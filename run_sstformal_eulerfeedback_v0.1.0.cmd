@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 20

if not exist "lakefile.toml" (
  echo ERROR: Extract this package beside lakefile.toml in NavierStokesAndEuler.
  popd
  exit /b 21
)
for %%F in ("SSTFormal\EulerFeedback\StretchingBound.lean" "SSTFormal\EulerFeedback\VorticityBound.lean" "SSTFormal\EulerFeedback\EulerianTransfer.lean") do (
  if not exist %%F (
    echo ERROR: Missing required Lean source %%F
    popd
    exit /b 22
  )
)
where lake >nul 2>&1
if errorlevel 1 (
  echo ERROR: lake is not available on PATH.
  popd
  exit /b 23
)
where python >nul 2>&1
if errorlevel 1 (
  echo ERROR: python is required for the strict axiom/log audit.
  popd
  exit /b 24
)

set "LOG=sstformal_eulerfeedback_v0.1.0_build.log"
if exist "%LOG%" (
  echo ERROR: Existing log would be overwritten: %LOG%
  echo Rename/archive the old log before a new run.
  popd
  exit /b 25
)
if exist "VALIDATION_FV03A_LOCAL.json" (
  echo ERROR: Existing validation would be overwritten.
  popd
  exit /b 26
)

if not exist ".lake\build\lib\lean\SSTFormal\EulerFeedback" mkdir ".lake\build\lib\lean\SSTFormal\EulerFeedback"
> "%LOG%" echo SST-FV03A v0.1.0 local Lean proof build and axiom audit
>> "%LOG%" echo Source branch should be sst/formal-euler-feedback-v0.1.0
>> "%LOG%" echo Half-open interval [0,T): no endpoint smoothness is assumed
>> "%LOG%" echo.
>> "%LOG%" echo [1/3] Compiling integrating-factor stretching bounds...
lake env lean -o ".lake\build\lib\lean\SSTFormal\EulerFeedback\StretchingBound.olean" "SSTFormal\EulerFeedback\StretchingBound.lean" >> "%LOG%" 2>&1
if errorlevel 1 goto fail

>> "%LOG%" echo [2/3] Compiling vector-vorticity identities and conditional bound...
lake env lean -o ".lake\build\lib\lean\SSTFormal\EulerFeedback\VorticityBound.olean" "SSTFormal\EulerFeedback\VorticityBound.lean" >> "%LOG%" 2>&1
if errorlevel 1 goto fail

>> "%LOG%" echo [3/3] Compiling conditional Eulerian transfer...
lake env lean -o ".lake\build\lib\lean\SSTFormal\EulerFeedback\EulerianTransfer.olean" "SSTFormal\EulerFeedback\EulerianTransfer.lean" >> "%LOG%" 2>&1
if errorlevel 1 goto fail

python "tools\audit_fv03a.py" --log "%LOG%" --out "VALIDATION_FV03A_LOCAL.json"
if errorlevel 1 goto audit_fail

type "%LOG%"
echo.
echo PASS: FV03A Lean compilation and strict axiom audit succeeded.
echo STATUS: PASS_LOCAL_LEAN, independent rerun NOT EXECUTED.
echo Validation: VALIDATION_FV03A_LOCAL.json
popd
exit /b 0

:audit_fail
type "%LOG%"
echo FAIL: FV03A theorem/axiom audit failed. No PASS may be claimed.
popd
exit /b 29

:fail
set "RC=%ERRORLEVEL%"
type "%LOG%"
echo.
echo FAIL: Lean exited with code %RC%. No PASS may be claimed.
popd
exit /b %RC%
