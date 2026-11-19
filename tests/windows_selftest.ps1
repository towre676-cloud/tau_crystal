# Moth Companion Windows QA — no network requests outside 127.0.0.1.
# Run after reviewing the commands. Requires PowerShell 5.1+, Windows 10/11.
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
$exe = Join-Path $root 'MothCompanion.exe'
$report = Join-Path $root 'tests\Moth-Windows-QA.json'
if (-not (Test-Path $exe)) { throw "MothCompanion.exe not found at $exe" }
$folder = Join-Path $env:TEMP ("Moth-QA-" + [guid]::NewGuid().ToString('N'))
New-Item -Path $folder -ItemType Directory -Force | Out-Null
$testState = Join-Path $folder 'nest'
$listener = [System.Net.Sockets.TcpListener]::new([Net.IPAddress]::Loopback, 0)
$listener.Start(); $port = $listener.LocalEndpoint.Port; $listener.Stop()
$base = "http://127.0.0.1:$port"
$headers = @{ 'X-Moth-Local' = '1' }
$passed = @()
$proc = $null
try {
  $proc = Start-Process -FilePath $exe -ArgumentList @('--no-browser', "--port=$port", "--data-dir=$testState") -PassThru -WindowStyle Hidden
  $status = $null
  for ($i=0; $i -lt 45; $i++) {
    try { $status = Invoke-RestMethod -Uri "$base/api/status" -TimeoutSec 1; break } catch { Start-Sleep -Milliseconds 250 }
  }
  if (-not $status) { throw 'Windows executable failed to start localhost server' }
  $passed += "Windows launch and loopback HTTP ($($status.version))"
  $m = Invoke-RestMethod -Method Post -Uri "$base/api/memory" -Headers $headers -ContentType 'application/json' -Body (@{text='Windows QA: pine forests'}|ConvertTo-Json)
  if (-not $m.id) { throw 'Memory POST failed' }
  $reply = Invoke-RestMethod -Method Post -Uri "$base/api/chat" -Headers $headers -ContentType 'application/json' -Body (@{message='What do you remember about me?'}|ConvertTo-Json)
  if ($reply.reply -notmatch 'pine forests') { throw 'Memory recall failed' }
  $passed += 'Persistent memory and recall'
  $task = Invoke-RestMethod -Method Post -Uri "$base/api/task" -Headers $headers -ContentType 'application/json' -Body (@{action='add';text='Review windows report'}|ConvertTo-Json)
  if ($task.tasks.Count -lt 1) { throw 'Task creation failed' }
  $passed += 'Daily tasks'
  $ledger = Invoke-RestMethod -Uri "$base/api/ledger/verify"
  if (-not $ledger.valid) { throw "Local chain verification failed: $($ledger.message)" }
  $passed += 'Signed event ledger'
  $quit = Invoke-RestMethod -Method Post -Uri "$base/api/quit" -Headers $headers -ContentType 'application/json' -Body '{}'
  if (-not $quit.ok) { throw 'Quit endpoint failed' }
  Start-Sleep -Seconds 1
  $nest = Get-Content -Raw (Join-Path $testState 'nest.json') | ConvertFrom-Json
  if ($nest.memories.Count -ne 1 -or $nest.tasks.Count -ne 1) { throw 'Saved state incomplete' }
  $passed += 'Graceful quit and disk persistence'
  $result = @{pass=$true;windows=[Environment]::OSVersion.VersionString;timestamp=(Get-Date).ToUniversalTime().ToString('o');version=$status.version;tests=$passed;binary_sha256=(Get-FileHash $exe -Algorithm SHA256).Hash.ToLowerInvariant()}
} catch {
  $result = @{pass=$false;windows=[Environment]::OSVersion.VersionString;timestamp=(Get-Date).ToUniversalTime().ToString('o');tests=$passed;error=$_.Exception.Message}
} finally {
  if ($proc -and -not $proc.HasExited) { try { $proc.Kill() } catch {} }
  $result | ConvertTo-Json -Depth 8 | Out-File -FilePath $report -Encoding utf8
  Write-Host "QA report: $report" -ForegroundColor Cyan
  if (-not $result.pass) { Write-Error $result.error }
}
