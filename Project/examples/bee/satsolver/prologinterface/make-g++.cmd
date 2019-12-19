@ECHO OFF
copy pl-glucose.cpp ..\glucose-2.2\core\pl-glucose.cpp
if %errorlevel% neq 0 GOTO CopyErr
cd ..\glucose-2.2\core

echo Start Compiling ...
swipl-ld -O2 -fomit-frame-pointer -s -shared -fpic -o ..\..\pl-glucose.dll ^
pl-glucose.cpp ^
Solver.cc ^
-I".." ^
-D__STDC_LIMIT_MACROS -D__STDC_FORMAT_MACROS ^
-Wno-unused-result

if %errorlevel% neq 0 GOTO SwiplErr

echo Compilation of Glucose v2.2 is DONE !!!

GOTO DoneComp

:CopyErr
echo ERROR: Failed copy pl-glucose.cpp !!!
GOTO :EOF

:SwiplErr
echo ERROR: Compiling using swipl-ld failed !!!

:DoneComp
cd ..\..
