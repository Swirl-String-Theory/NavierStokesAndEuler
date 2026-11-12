@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 20

if not exist "lakefile.toml" (
  echo ERROR: Run from NavierStokesAndEuler root.
  popd
  exit /b 21
)
where lake >nul 2>&1
if errorlevel 1 (
  echo ERROR: lake is not available on PATH.
  popd
  exit /b 23
)

set "LOG=euler_potential_flow_build.log"
if exist "%LOG%" (
  echo ERROR: Existing log would be overwritten: %LOG%
  echo Rename/archive the old log before a new run.
  popd
  exit /b 25
)

if not exist ".lake\build\lib\lean\Euler\PotentialFlow" mkdir ".lake\build\lib\lean\Euler\PotentialFlow"

> "%LOG%" echo Euler Potential Flow local Lean build
>> "%LOG%" echo Branch should be feature/euler-potential-flow
>> "%LOG%" echo.

set FAIL=0

call :build_one Definitions
if errorlevel 1 set FAIL=1
call :build_one GradientCurl
if errorlevel 1 set FAIL=1
call :build_one Laplace
if errorlevel 1 set FAIL=1
call :build_one Bernoulli
if errorlevel 1 set FAIL=1
call :build_one ExteriorDomain
if errorlevel 1 set FAIL=1
call :build_one Circulation
if errorlevel 1 set FAIL=1
call :build_one VortexCoreCoupling
if errorlevel 1 set FAIL=1

>> "%LOG%" echo.
>> "%LOG%" echo [aggregator] Euler/PotentialFlow.lean
lake env lean -o ".lake\build\lib\lean\Euler\PotentialFlow.olean" "Euler\PotentialFlow.lean" >> "%LOG%" 2>&1
if errorlevel 1 set FAIL=1

if "%FAIL%"=="1" (
  >> "%LOG%" echo.
  >> "%LOG%" echo RESULT: FAIL
  echo RESULT: FAIL — see %LOG%
  popd
  exit /b 1
)

>> "%LOG%" echo.
>> "%LOG%" echo RESULT: PASS
echo RESULT: PASS — see %LOG%
popd
exit /b 0

:build_one
>> "%LOG%" echo [module] Euler/PotentialFlow/%~1.lean
lake env lean -o ".lake\build\lib\lean\Euler\PotentialFlow\%~1.olean" "Euler\PotentialFlow\%~1.lean" >> "%LOG%" 2>&1
exit /b %ERRORLEVEL%
