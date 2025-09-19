@echo off
setlocal
set "LAKE=%USERPROFILE%\.elan\bin\lake.exe"
cd /d "%~dp0"

"%LAKE%" update >nul
if errorlevel 1 goto :err
"%LAKE%" build
if errorlevel 1 goto :err

if "%~1"=="" (
  for /f "tokens=1-4 delims=/:. " %%a in ("%date% %time%") do set "TS=%%d%%b%%c_%%a%%~nT"
  set "RUN_ID=run-%TS%"
  "%LAKE%" exe tau_crystal -- --tau 1.25 --q "0.0,0.5,1.0,2.0" --run-id "%RUN_ID%" --out "manifest.json" --audit true
) else (
  "%LAKE%" exe tau_crystal -- %*
)

echo(
if exist "manifest.json" (
  echo Preview:
  more +0 "manifest.json"
) else (
  echo (no manifest.json found)
)
goto :eof

:err
echo Build or update failed. See messages above.
pause
endlocal
