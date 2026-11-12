@echo off
setlocal EnableExtensions DisableDelayedExpansion
pushd "%~dp0" || exit /b 20
if not exist "lakefile.toml" (
  echo ERROR: Install files into NavierStokesAndEuler repository root.
  popd
  exit /b 21
)
where python >nul 2>&1
if errorlevel 1 (
  echo ERROR: python required for sequential stage controller.
  popd
  exit /b 22
)
python tools\run_fv03b.py %*
set "RC=%ERRORLEVEL%"
popd
exit /b %RC%
