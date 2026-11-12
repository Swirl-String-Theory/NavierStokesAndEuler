@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 20

if not exist "lakefile.toml" (
  echo ERROR: Extract into NavierStokesAndEuler root beside lakefile.toml.
  popd
  exit /b 21
)
for %%F in ("SSTFormal\ClockEndpoint.lean" "SSTFormal\ClockIntegral.lean" "SSTFormal\ClockEulerC1.lean") do (
  if not exist %%F (
    echo ERROR: prerequisite or new proof file missing: %%F
    popd
    exit /b 22
  )
)
where lake >nul 2>&1
if errorlevel 1 (
  echo ERROR: Lake missing from PATH.
  popd
  exit /b 23
)

if not exist ".lake\build\lib\lean\SSTFormal" mkdir ".lake\build\lib\lean\SSTFormal"
set "LOG=sstformal_clockeulerc1_v0.4.0_build.log"
> "%LOG%" echo SST-FV02-C1 v0.4.0 local Lean check

>> "%LOG%" echo Compiling prior endpoint module...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockEndpoint.olean" "SSTFormal\ClockEndpoint.lean" >> "%LOG%" 2>&1
set "RC=%ERRORLEVEL%"
if not "%RC%"=="0" goto fail

>> "%LOG%" echo Compiling prior integral module...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockIntegral.olean" "SSTFormal\ClockIntegral.lean" >> "%LOG%" 2>&1
set "RC=%ERRORLEVEL%"
if not "%RC%"=="0" goto fail

>> "%LOG%" echo Compiling Euler C1 bridge...
lake env lean -o ".lake\build\lib\lean\SSTFormal\ClockEulerC1.olean" "SSTFormal\ClockEulerC1.lean" >> "%LOG%" 2>&1
set "RC=%ERRORLEVEL%"
if not "%RC%"=="0" goto fail

type "%LOG%"
echo.
echo Lean exit code: 0
echo PASS: FV02-C1 accepted locally. Check #print axioms and commit this exact version.
echo NOTE: This does not run Comparator, prove ENNReal Filter.limsup under clock, or test feedback.
popd
exit /b 0

:fail
type "%LOG%"
echo.
echo FAIL: Lean returned code %RC%.
popd
exit /b %RC%
