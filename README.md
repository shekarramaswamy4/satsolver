# satsolver
implementation of DPLL Algorithm in java.

How to use:
create executable of SATSolver.java and run, which will open a prompt.

Input specification:
Takes in a formula, which is represented by a list of clauses. One clause per line, and hit enter to start entering a new clause. For a given clause, input integers, negative or positive. Each literal in a clause are joined with "or", and each clause is joined with "and".
To finish inputting, CTRL-D. The program will then output two lines: the first being the list of true literals, second being the list of false literals.

Examples:
To evaluate (1 and -1):
1 [enter]
-1 [enter]
ctrl-d
------
UNSAT

To evaluate ((-1 or 2) and (2 or 3)):
-1 2 [enter]
2 3 [enter]
ctrl-d
------
2 3
-1

