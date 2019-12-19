@echo off
echo =================================================
echo =====      Compile  PL-Minisat v2.0.2       =====
echo =================================================
echo Please make sure:
echo SWI-Prolog and MinGW (g++) are installed 
echo and accessable from every path.
echo =================================================
pause

echo ---- EXTRACT SOURCE ----
md ..\satsolver
TarTool plMiniSAT_src.tar.gz ../satsolver
TarTool plSATsolver.tar.gz ../satsolver
echo ---- COMPILE -----
(cd ..\satsolver\prologinterface & CMD /C make-g++.cmd & cd ..\..\satsolver_src)
echo ---- CLEAN SOURCE ----
rd /s /q ..\satsolver\minisat-2.0.2
rd /s /q ..\satsolver\prologinterface
echo ---- DONE -----
