@echo off
setlocal EnableExtensions
cd /d "%~dp0"

if not exist "lakefile.toml" (
    echo ERROR: unpack this patch in the root of NavierStokesAndEuler, alongside lakefile.toml.
    exit /b 10
)
where lake >nul 2>&1
if errorlevel 1 (
    echo ERROR: lake.exe is not available on PATH.
    exit /b 11
)
if not exist "SSTFormal\ClockEndpoint.lean" (
    echo ERROR: SSTFormal\ClockEndpoint.lean missing.
    exit /b 12
)

set "LOG=sstformal_clockendpoint_build.log"
lake env lean SSTFormal\ClockEndpoint.lean > "%LOG%" 2>&1
set "RC=%ERRORLEVEL%"
type "%LOG%"
echo.
echo Lean exit code: %RC%
if not "%RC%"=="0" (
  echo FAIL: SST-FV02 is NOT verified. Inspect %LOG%.
  exit /b %RC%
)
echo PASS: Lean accepted SST-FV02 stage A. Check the printed axioms.
exit /b 0
