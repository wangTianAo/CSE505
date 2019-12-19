@echo off
echo ==============================
echo ===== COMPILE  BumbleBEE =====
echo ==============================
cd ..
del BumbleBEE.exe /q
del BumbleSol.exe /q
swipl.exe -G0 -T0 -L0 -f none -F none -g true -t "consult(['beeSolver/bSolver.pl']),qsave_program('BumbleBEE.exe',[goal='bSolver',toplevel=prolog,init_file=none])"
swipl.exe -G0 -T0 -L0 -f none -F none -g true -t "consult(['beeSolver/bSolReader.pl']),qsave_program('BumbleSol.exe',[goal='bSolReader',toplevel=prolog,init_file=none])"
copy satsolver\pl-glucose4.dll .\pl-satsolver.dll
copy satsolver\libgcc_s_dw2-1.dll .\
copy "satsolver\libstdc++-6.dll" .\
echo ========================================================
echo =  BumbleBEE might required additional dlls to run:    =
echo =  Prolog files: swipl.dll, pthreadVC.dll              =
echo =  PL-SATsolver files: pl-satsolver.dll (*),           =
echo =                      libstdc++-6.dll,                =
echo =                      libgcc_s_dw2-1.dll              =
echo =  (*) pl-satsolver.dll can be any of the sat solver   =
echo =      dlls which implementing PL-SATsolver interface  =
echo ========================================================
echo ---- DONE -----
