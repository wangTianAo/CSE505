@ECHO OFF
REM ECHO ----- SET VS ENVIRONMENT -----
REM call "C:\Program Files\Microsoft Visual Studio 9.0\VC\vcvarsall.bat" x86
REM call "C:\Program Files\Microsoft Visual Studio 9.0\VC\vcvarsall.bat" x86_amd64

IF NOT DEFINED LIB GOTO VisualSudio

ECHO ----- Read SWI-Prolog settings -----
SETLOCAL
FOR /F "usebackq delims=;" %%i IN (`swipl.exe --dump-runtime-variables`) DO SET %%i

IF NOT DEFINED PLBASE GOTO SwiplErr
IF NOT DEFINED PLLIB GOTO SwiplErr

:: Remove quotes
SET PLBASE=###%PLBASE%###
SET PLBASE=%PLBASE:"###=%
SET PLBASE=%PLBASE:###"=%
SET PLBASE=%PLBASE:###=%

SET PLLIB=###%PLLIB%###
SET PLLIB=%PLLIB:"###=%
SET PLLIB=%PLLIB:###"=%
SET PLLIB=%PLLIB:###=%

:: set ocal settings
SET SWILIB=%PLBASE%/lib
SET SWIINC=%PLBASE%/include
SET SOLVER_DIR=glucose-2.2
SET SOLVER_INTRF=pl-glucose
SET SOLVER_FILES=Solver
:: Visual Studio LIB path
SET LIB=%SWILIB%;%LIB%

ECHO ----- Copy SAT-Solver interface file -----
copy %SOLVER_INTRF%.cpp ..\%SOLVER_DIR%\core\%SOLVER_INTRF%.cc

ECHO ----- Compiling SAT-Solver files -----

FOR %%i IN (%SOLVER_FILES% %SOLVER_INTRF%) DO ^
cl.exe -c -O2 /MD /EHsc -D_REENTRANT -D__SWI_PROLOG__ ^
/Fotmp_%%i.obj ^
-I"%SWIINC%" ^
-I"../%SOLVER_DIR%" ^
../%SOLVER_DIR%/core/%%i.cc || GOTO CompileErr

ECHO ----- Linking SAT-Solver objects -----
link.exe /out:../%SOLVER_INTRF%.dll /dll /nologo ^
%PLLIB% ^
tmp_*.obj || GOTO LinkErr

ECHO ----- Cleanining -----
del *.obj
del ..\*.lib
del ..\*.dll.manifest
del ..\*.exp

ECHO -------------------------------------------------------------
ECHO SUCCEED: Compiling %SOLVER_INTRF% succeed !!!
ENDLOCAL

GOTO :EOF

:VisualSudio
echo
echo -------------------------------------------------------------
echo ERROR: Could not find LIB settings !!!
echo Executing of this command file should be
echo done from Visual Studio Command Prompt
echo or
echo A call to set up Visual Studio
echo environment was added to this file.
GOTO :EOF

:SwiplErr
echo
echo -------------------------------------------------------------
echo ERROR: Could not get SWI-Prolog runtime variables !!!
echo Please make sure swipl.exe is accessable from any folder.
GOTO :EOF

:CompileErr
echo
echo -------------------------------------------------------------
echo ERROR: while compiling files...
GOTO :EOF

:LinkErr
echo
echo -------------------------------------------------------------
echo ERROR: while linking files...
GOTO :EOF