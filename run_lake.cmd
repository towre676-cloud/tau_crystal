@echo off
setlocal
cd /d "C:\Users\Cody\Desktop\tau_crystal"
echo [lake update]
lake update || exit /b 1
echo [lake clean]
lake clean || exit /b 1
echo [lake build]
lake build || exit /b 1
echo [lake exe tau_crystal]
lake exe tau_crystal -- --tau 1.25 --q "0.0,0.5,1.0,2.0" --run-id "demo-run" --out "manifest.json" --audit true || exit /b 1
endlocal
