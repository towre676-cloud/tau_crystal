$ErrorActionPreference = 'Stop'
$LAKE = "$HOME\.elan\bin\lake.exe"
if ($PSScriptRoot) { Set-Location -Path $PSScriptRoot }

function Assert($cond, $msg) {
  if (-not $cond) { throw "FAIL: $msg" } else { Write-Host "✔ $msg" -ForegroundColor Green }
}

function Normalize-Manifest([object]$m) {
  if (-not $m) { return $null }
  $o = [ordered]@{}
  $o.run_id = if ($m.PSObject.Properties.Match('run_id')) { $m.run_id } else { $m.runId }
  $o.audit  = [bool]$m.audit
  $tauRaw = $m.tau
  $o.tau = if ($tauRaw -is [double]) { $tauRaw } else { [double]::Parse("$tauRaw",[Globalization.CultureInfo]::InvariantCulture) }
  $q = @()
  foreach ($qv in @($m.q)) {
    if ($qv -is [double]) { $q += $qv }
    else { $q += [double]::Parse("$qv",[Globalization.CultureInfo]::InvariantCulture) }
  }
  $o.q = $q
  foreach ($k in 'count','sum_q','mean_q','scaled') { if ($m.PSObject.Properties.Match($k)) { $o[$k] = $m.$k } }
  return [pscustomobject]$o
}

function Run-One([string]$runId, [string]$outfile) {
  if (Test-Path $outfile) { Remove-Item -Force $outfile }
  try { & $LAKE update 2>$null | Out-Null } catch { }
  & $LAKE build
  $stdout = & $LAKE exe tau_crystal -- --tau 1.25 --q "0.0,0.5,1.0,2.0" --run-id $runId --out $outfile --audit true 2>&1
  if (-not (Test-Path $outfile)) { throw "No manifest written: $outfile`nSTDOUT:`n$stdout" }
  $jsonText = Get-Content -Raw $outfile
  $json = $jsonText | ConvertFrom-Json
  return @{ StdOut = $stdout; Manifest = (Normalize-Manifest $json); Raw = $jsonText }
}

Write-Host "== Building & running (pass 1) ==" -ForegroundColor Cyan
$r1 = Run-One -runId "assure-1" -outfile "manifest_assure1.json"
$m1 = $r1.Manifest

Assert ([math]::Abs([double]$m1.tau - 1.25) -lt 1e-9) "tau propagated (1.25)"
Assert ($m1.q.Count -eq 4 -and ($m1.q -join ',') -eq '0,0.5,1,2') "q propagated ([0,0.5,1,2])"
Assert ($m1.run_id -eq 'assure-1') "run_id recorded"
Assert ($m1.audit -eq $true) "audit flag recorded"

$obsFromCert = $null
if ($r1.StdOut -match 'cert:\s*{[^}]*obstructionDim\s*:=\s*([0-9]+)') { $obsFromCert = [int]$Matches[1] }
$obsFromPulse = $null
if ($r1.StdOut -match 'tau-pulse:\s*obs=([0-9]+)') { $obsFromPulse = [int]$Matches[1] }
if ($obsFromCert -ne $null -and $obsFromPulse -ne $null) {
  Assert ($obsFromCert -eq $obsFromPulse) "obs in cert equals obs in τ-pulse ($obsFromCert)"
}
if ($r1.StdOut -match 'auditor_ok:\s*true') { Write-Host "✔ auditor_ok true" -ForegroundColor Green }

$qsSeen = [System.Collections.Generic.HashSet[string]]::new()
$r1.StdOut -split "`r?`n" | ForEach-Object { if ($_ -match 'qCRO:\s*q=([0-9.]+)') { [void]$qsSeen.Add($Matches[1]) } }
if ($qsSeen.Count -gt 0) { Assert ($qsSeen.SetEquals(@('0','0.5','1','2'))) "qCRO reported for all q in request" }

Write-Host "== Re-running (pass 2) ==" -ForegroundColor Cyan
$r2 = Run-One -runId "assure-2" -outfile "manifest_assure2.json"
$m2 = $r2.Manifest

$m1cmp = $m1 | Select-Object * -ExcludeProperty run_id,out
$m2cmp = $m2 | Select-Object * -ExcludeProperty run_id,out
Assert ((($m1cmp | ConvertTo-Json -Compress -Depth 10) -eq ($m2cmp | ConvertTo-Json -Compress -Depth 10))) "deterministic manifest fields (except run_id/out)"

$h1 = (Get-FileHash -Algorithm SHA256 'manifest_assure1.json').Hash
$h2 = (Get-FileHash -Algorithm SHA256 'manifest_assure2.json').Hash
Write-Host "SHA256(manifest_assure1.json) = $h1"
Write-Host "SHA256(manifest_assure2.json) = $h2"

Write-Host "`nALL CHECKS PASSED." -ForegroundColor Green
