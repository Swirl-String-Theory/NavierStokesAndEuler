@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 20

if not exist "lakefile.toml" (
  echo ERROR: extract the package into NavierStokesAndEuler root, beside lakefile.toml.
  popd
  exit /b 21
)
if not exist "SSTFormal\ClockEndpoint.lean" (
  echo ERROR: SST-FV02 stage A source SSTFormal\ClockEndpoint.lean is required.
  popd
  exit /b 22
)
if not exist "SSTFormal\ClockIntegral.lean" (
  echo ERROR: SSTFormal\ClockIntegral.lean is missing.
  popd
  exit /b 23
)
where lake >nul 2>&1
if errorlevel 1 (
  echo ERROR: Lake executable not on PATH. Activate elan/Lean 4.34.0-rc2.
  popd
  exit /b 24
)

if not exist ".lake\build\lib\lean\SSTFormal" mkdir ".lake\build\lib\lean\SSTFormal"
set "LOG=sstformal_clockintegral_v0.3.0_build.log"
> "%LOG%" echo SST-FV02B v0.3.0 - Stage A dependency and Stage B proof check
>> "%LOG%" echo Building the imported Stage A module into an olean first...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockEndpoint.olean" "SSTFormal\ClockEndpoint.lean" >> "%LOG%" 2>&1
set "RC=%ERRORLEVEL%"
if not "%RC%"=="0" goto failed_stageA

>> "%LOG%" echo Checking Stage B: integral, monotonicity, inverse, correspondence...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockIntegral.olean" "SSTFormal\ClockIntegral.lean" >> "%LOG%" 2>&1
set "RC=%ERRORLEVEL%"
if not "%RC%"=="0" goto failed_stageB

type "%LOG%"
echo.
echo Lean exit code: 0
echo PASS: FV02-B accepted by local Lean. Inspect axiom lines above.
echo NOTE: This does NOT run Comparator, prove Euler C1/ENNReal bridge, or test active clock feedback.
popd
exit /b 0

:failed_stageA
type "%LOG%"
echo.
echo FAIL: Stage A prerequisite compilation returned exit code %RC%.
popd
exit /b %RC%

:failed_stageB
type "%LOG%"
echo.
echo FAIL: Stage B Lean compilation returned exit code %RC%.
popd
exit /b %RC%
