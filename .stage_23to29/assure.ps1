$ErrorActionPreference = "Stop"
$LAKE = "$HOME\.elan\bin\lake.exe"
if ($PSScriptRoot) { Set-Location -Path $PSScriptRoot }

function Assert($cond, $msg) {
  if (-not $cond) { throw "FAIL: $msg" } else { Write-Host "✔ $msg" -ForegroundColor Green }
}

function Normalize-Manifest([object]$m) {
  if (-not $m) { return $null }
  $o = [ordered]@{}
  $o.run_id = if ($m.PSObject.Properties.Match("run_id")) { $m.run_id } else { $m.runId }
  $o.audit  = [bool]$m.audit
  $tauRaw = $m.tau
  $o.tau = if ($tauRaw -is [double]) { $tauRaw } else { [double]::Parse("$tauRaw",[Globalization.CultureInfo]::InvariantCulture) }
  $q = @()
  foreach ($qv in @($m.q)) {
    if ($qv -is [double]) { $q += $qv } else { $q += [double]::Parse("$qv",[Globalization.CultureInfo]::InvariantCulture) }
  }
  $o.q = $q
  foreach ($k in "count","sum_q","mean_q","scaled") { if ($m.PSObject.Properties.Match($k)) { $o[$k] = $m.$k } }
  [pscustomobject]$o
}

function Sign-Manifest([string]$path) {
  $jsonText = Get-Content -Raw -Encoding UTF8 $path
  $bytes = [Text.Encoding]::UTF8.GetBytes($jsonText)

  $sha = [System.Security.Cryptography.SHA256]::Create()
  $hash = ($sha.ComputeHash($bytes) | ForEach-Object { $_.ToString("x2") }) -join ""

  $sigKey = $env:TAUCRYSTAL_SIG_KEY  # set in CI secrets or your local env
  $hmacHex = $null
  if ($sigKey -and $sigKey.Trim().Length -gt 0) {
    $keyBytes = [Text.Encoding]::UTF8.GetBytes($sigKey)
    $h = New-Object System.Security.Cryptography.HMACSHA256($keyBytes)
    $hmac = $h.ComputeHash($bytes)
    $hmacHex = ($hmac | ForEach-Object { $_.ToString("x2") }) -join ""
  }

  Set-Content -Encoding ASCII -Path ($path + ".sha256") -Value $hash
  if ($hmacHex) { Set-Content -Encoding ASCII -Path ($path + ".hmac") -Value $hmacHex }

  Write-Host "SHA256($path) = $hash"
  if ($hmacHex) { Write-Host "HMAC($path) = $hmacHex" }
  return @{ sha256 = $hash; hmac = $hmacHex }
}

function Require-RuntimeSignals([string]$stdout, [string[]]$expectedQ) {
  # cert with obstructionDim
  if ($stdout -notmatch 'cert:\s*{[^}]*obstructionDim\s*:=\s*([0-9]+)') {
    throw "No 'cert:{... obstructionDim := N}' line emitted."
  }
  $obsCert = [int]$Matches[1]

  # tau-pulse with obs=...
  if ($stdout -notmatch 'tau-pulse:\s*obs=([0-9]+)') {
    throw "No 'tau-pulse: obs=N' line emitted."
  }
  $obsPulse = [int]$Matches[1]

  Assert ($obsCert -eq $obsPulse) "obs in cert equals obs in τ-pulse ($obsCert)"

  # qCRO lines for each requested q
  $seen = [System.Collections.Generic.HashSet[string]]::new()
  $stdout -split "`r?`n" | ForEach-Object {
    if ($_ -match 'qCRO:\s*q=([0-9.]+)') { [void]$seen.Add($Matches[1]) }
  }
  if ($expectedQ.Count -gt 0) {
    $ok = $true
    foreach ($q in $expectedQ) { if (-not $seen.Contains($q)) { $ok = $false } }
    if (-not $ok) {
      throw "qCRO coverage incomplete. expected=[$($expectedQ -join ',')] seen=[$([string]::Join(',', $seen))]"
    }
    Write-Host "✔ qCRO reported for all q in request" -ForegroundColor Green
  }
}

function Run-One([string]$runId, [string]$outfile, [string[]]$expectedQ) {
  if (Test-Path $outfile) { Remove-Item -Force $outfile }
  try { & $LAKE update 2>$null | Out-Null } catch { }
  & $LAKE build
  $args = @("--tau","1.25","--q","0.0,0.5,1.0,2.0","--run-id",$runId,"--out",$outfile,"--audit","true")
  $stdout = & $LAKE exe tau_crystal -- @args 2>&1
  if (-not (Test-Path $outfile)) { throw "No manifest written: $outfile`nSTDOUT:`n$stdout" }
  Require-RuntimeSignals -stdout $stdout -expectedQ $expectedQ
  $jsonText = Get-Content -Raw $outfile
  $json = $jsonText | ConvertFrom-Json
  return @{ StdOut = $stdout; Manifest = (Normalize-Manifest $json); OutFile = $outfile }
}

$expectedQ = @("0","0.5","1","2")

Write-Host "== Building & running (pass 1) ==" -ForegroundColor Cyan
$r1 = Run-One -runId "assure-1" -outfile "manifest_assure1.json" -expectedQ $expectedQ
$m1 = $r1.Manifest

Assert ([math]::Abs([double]$m1.tau - 1.25) -lt 1e-9) "tau propagated (1.25)"
Assert ($m1.q.Count -eq 4 -and ($m1.q -join ",") -eq "0,0.5,1,2") "q propagated ([0,0.5,1,2])"
Assert ($m1.run_id -eq "assure-1") "run_id recorded"
Assert ($m1.audit -eq $true) "audit flag recorded"

if ($r1.StdOut -match "auditor_ok:\s*true") { Write-Host "✔ auditor_ok true" -ForegroundColor Green } else { throw "auditor_ok not reported as true" }

Write-Host "== Re-running (pass 2) ==" -ForegroundColor Cyan
$r2 = Run-One -runId "assure-2" -outfile "manifest_assure2.json" -expectedQ $expectedQ
$m2 = $r2.Manifest

# Determinism on normalized payload
$m1cmp = $m1 | Select-Object * -ExcludeProperty run_id,out
$m2cmp = $m2 | Select-Object * -ExcludeProperty run_id,out
Assert ((($m1cmp | ConvertTo-Json -Compress -Depth 10) -eq ($m2cmp | ConvertTo-Json -Compress -Depth 10))) "deterministic manifest fields (except run_id/out)"

# Sign both manifests (SHA256, and HMAC if TAUCRYSTAL_SIG_KEY is set)
$S1 = Sign-Manifest $r1.OutFile
$S2 = Sign-Manifest $r2.OutFile

Write-Host "`nALL CHECKS PASSED (mandatory attestation + signed manifests)." -ForegroundColor Green
