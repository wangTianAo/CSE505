    \'''/ //       BumbleBEE       / \_/ \_/ \
   -(|||)(')      README file      \_/ \_/ \_/
     ^^^         by Amit Metodi    / \_/ \_/ \
-------------------------------------------------

BumbleBEE is a wrapper which enables to call the compiler in
conjunction with a SAT solver as an executable. It takes as
input a BEE model (FlatZinc-like syntax) and provides as output
a solution if one exists.

BumbleBEE requires a solving directive. The last line in a model
should be one of the following (where 'w' is an integer variable 
declared in the model):

    (a) solve satisfy       example ex_sat.bee / ex_unsat.bee
    (b) solve minimize w    example ex_sat_min.bee
    (c) solve maximize w


======
Usage:
======
After compile (see below) the executable have three modes: Solver, Checker, and Dimacs.

Solver Mode:
------------
Command: ./BumbleBEE file.bee
BumbleBEE will compile the BEE model into CNF, solve it with a SAT solver,
and return a satisfied assignment if exists.

For example: ./BumbleBEE beeSolver/bExamples/ex_sat.bee
%  \'''/ //      BumbleBEE       / \_/ \_/ \
% -(|||)(')     (??/??/????)     \_/ \_/ \_/
%   ^^^        by Amit Metodi    / \_/ \_/ \
%
%  reading BEE file ... done
%  load pl-satSolver ... % SWI-Prolog interface to Glucose v4.0 ... OK
%  encoding BEE model ... done
%  solving CNF (satisfy) ...
x = 0
y = -4
z = -4
w = 2
x1 = false
x2 = true
x3 = false
x4 = false
----------
==========


Checker Mode:
-------------
Command: ./BumbleBEE file.bee -check
BumbleBEE will do type checking for the BEE model.
It will alert when undefined (int) variables are used or 
when using the wrong type of variables.

For Example: ./BumbleBEE beeSolver/bExamples/checker_example.bee -check
%  \'''/ //      BumbleBEE       / \_/ \_/ \
% -(|||)(')     (??/??/????)     \_/ \_/ \_/
%   ^^^        by Amit Metodi    / \_/ \_/ \
%
%  reading BEE file ... done
%  Checking BEE model ...
Constraint #3: unknown constraint (int_ge).
Constraint #4: argument #3 is undefined.
Constraint #7: argument #2 is not an integer (bool).
7 constraints checked.


Dimacs Mode:
------------
Command: ./BumbleBEE file.bee -dimacs dimacs.cnf dimacs.map
BumbleBEE will compile the BEE model into CNF, write the compiled CNF
into a file in dimacs format and write the maping between output variables
in the BEE model and the literals in the dimacs into another file.

Once the dimacs is solver the output of the SAT solver and
the map file can be decoded using BumbleSol executable.
Command: ./BumbleSol dimacs.map dimacs.solution

For example: using BumbleBEE to write a DIMACS file and 
             solved it with a standalone MiniSAT:
./BumbleBEE problem.bee -dimacs dimacs.cnf dimacs.map
./minisat dimacs.cnf dimacs.sol
./BumbleSol dimacs.map dimacs.sol





Examples of BumbleBEE models can be found at ./beeSolver/bExamples/



========
Compile:
========

NOTE: Before compiling BumbleBEE, PL-SATsolver must be compiled
since BumbleBEE using PL-SATsolver.
Refer to README file at ./satsolver_src folder to learn more 
about how to compile PL-SATsolver.

Linux:
------
To compile BumbleBEE executable use the attached makefile as followed:
  > make

NOTE: Using older versions of SWI-Prolog such as 5.10.2 might cause the
      compiling of BumbleBEE to enter endless loop.

The makefile will compile BumbleBEE and place several files in the "root BEE" directory:
BumbleBEE - Main Linux executable
BumbleSol - Linux executable for reading DIMACS solution.
pl-satsolver.so - PL-SATsolver library which will be loaded by
                  BumbleBEE when execute (copied from ./satsolver folder).
                  By default the make file copies pl-glucose4.so.
                  To try different sat solver simply replace pl-satsolver.so file 
                  with so file of a different sat solver from ./satsolver folder.



Windows:
--------
To compile BumbleBEE execute the batch file: make-BEE.cmd.

NOTE: Using older versions of SWI-Prolog such as 5.10.2 might cause the
      compiling of BumbleBEE to enter endless loop.

The batch file will place several files in the "root BEE" directory:
BumbleBEE.exe - Main Windows executable
BumbleSol.exe - Windows executable for reading DIMACS solution.
pl-satsolver.dll - PL-SATsolver library which will be loaded by
                   BumbleBEE when execute (copied from ./satsolver folder).
                   By default the make file copies pl-glucose4.dll.
                   To try different sat solver simply replace pl-satsolver.dll file 
                   with dll file of a different sat solver from ./satsolver folder.

In addition it might be required to copy the following files from SWI-Prolog directory:
swipl.dll
pthreadVC.dll
readutil.dll