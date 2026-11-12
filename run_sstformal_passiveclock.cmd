@echo off
setlocal EnableExtensions
cd /d "%~dp0"

where lake >nul 2>&1
if errorlevel 1 (
    echo ERROR: lake.exe not found on PATH. Start an elan-enabled terminal.
    exit /b 10
)

if not exist "SSTFormal\PassiveClock.lean" (
    echo ERROR: SSTFormal\PassiveClock.lean not found.
    exit /b 11
)

set "LOG=sstformal_passiveclock_build.log"
echo Checking SST-FV01 with the repository's pinned Lean toolchain...
lake env lean SSTFormal\PassiveClock.lean > "%LOG%" 2>&1
set "RC=%ERRORLEVEL%"
type "%LOG%"
echo.
echo Lean exit code: %RC%
if not "%RC%"=="0" (
    echo FAIL: Do not mark SST-FV01 as PASS. Review %LOG%.
    exit /b %RC%
)
echo PASS: Lean accepted SST-FV01. Inspect printed axiom dependencies.
exit /b 0
