@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 20

if not exist "lakefile.toml" (
  echo ERROR: Extract into NavierStokesAndEuler root beside lakefile.toml.
  popd
  exit /b 21
)
for %%F in ("SSTFormal\ClockEndpoint.lean" "SSTFormal\ClockIntegral.lean" "SSTFormal\ClockEulerC1.lean" "SSTFormal\ClockEulerC1Limsup.lean") do (
  if not exist %%F (
    echo ERROR: Missing prerequisite/source file %%F
    popd
    exit /b 22
  )
)
where lake >nul 2>&1
if errorlevel 1 (
  echo ERROR: Lake is missing from PATH.
  popd
  exit /b 23
)

if not exist ".lake\build\lib\lean\SSTFormal" mkdir ".lake\build\lib\lean\SSTFormal"
set "LOG=sstformal_clockeulerc1limsup_v0.5.0_build.log"
> "%LOG%" echo SST-FV02-C2 v0.5.0 local Lean build and axiom audit

>> "%LOG%" echo Compiling Stage A...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockEndpoint.olean" "SSTFormal\ClockEndpoint.lean" >> "%LOG%" 2>&1
if errorlevel 1 goto fail

>> "%LOG%" echo Compiling Stage B...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockIntegral.olean" "SSTFormal\ClockIntegral.lean" >> "%LOG%" 2>&1
if errorlevel 1 goto fail

>> "%LOG%" echo Compiling Stage C1...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockEulerC1.olean" "SSTFormal\ClockEulerC1.lean" >> "%LOG%" 2>&1
if errorlevel 1 goto fail

>> "%LOG%" echo Compiling Stage C2...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockEulerC1Limsup.olean" "SSTFormal\ClockEulerC1Limsup.lean" >> "%LOG%" 2>&1
if errorlevel 1 goto fail

type "%LOG%"
echo.
echo PASS: FV02-C2 local Lean check exit code 0.
echo Verify printed axioms are exactly propext, Classical.choice, Quot.sound.
echo NOTE: No Comparator or sandbox verification was performed by this script.
popd
exit /b 0

:fail
set "RC=%ERRORLEVEL%"
type "%LOG%"
echo.
echo FAIL: Lean exit code %RC%.
popd
exit /b %RC%
