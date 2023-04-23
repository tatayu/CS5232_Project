# CS5233 Project -  Formal Specification and Verification of LFU Algorithms with Dafny

## Software Prerequisites

- Dafny v3.13 is required.
- The Verification Time Limit is set to 600 seconds

In Visual Studio Code, you can check the Dafny version in the bottom-right
corner of the editor window when you have a `.dfy` file open.

If a different version is displayed (e.g., version 4), go to the Extensions
pane (Ctrl + Shift + X), search for the 'Dafny' extension, go to Extension
Settings, set 'Dafny: Version' to `3.13.1` and restart Visual Studio Code.

To set the time limit, got to the Extension Setting, set 'Dafny: Verification Time Limit' to 600 and restartd Visual Studio Code.

## LFU.dfy
This code contains the implementation and verification of the LFU algorithm with O(1) time complexity. To run the program, go to the command palette (Ctrl + Shift + P), search for 'Dafny: run' and click on it. The program should be verified within a ??? seconds. The expected output is shown as below: 

## LFUSimple.dfy
This code contains the implementation and verification of the LFU algorithm with O(N) time complexity. To run the program, go to the command palette (Ctrl + Shift + P), search for 'Dafny: run' and click on it. The program should be verified within a few seconds. The expected output is shown as below: 

Dafny program verifier finished with 8 verified, 0 errors <br>
Cache Capacity = 5 <br>
PUT (1, 1) - after put: map[1 := (1, 1)] <br>
PUT (2, 2) - after put: map[1 := (1, 1), 2 := (2, 1)] <br>
PUT (3, 3) - after put: map[1 := (1, 1), 2 := (2, 1), 3 := (3, 1)] <br>
GET (1) - after get: map[1 := (1, 2), 2 := (2, 1), 3 := (3, 1)] <br>
get(1) = 1 <br>
PUT (3, 5) - after put: map[1 := (1, 2), 2 := (2, 1), 3 := (5, 1)] <br>
GET (3) - after get: map[1 := (1, 2), 2 := (2, 1), 3 := (5, 2)] <br>
get(3) = 5 <br>
PUT (4, 6) - after put: map[1 := (1, 2), 2 := (2, 1), 3 := (5, 2), 4 := (6, 1)] <br>
PUT (5, 7) - after put: map[1 := (1, 2), 2 := (2, 1), 3 := (5, 2), 4 := (6, 1), 5 := (7, 1)] <br>
PUT (10, 100) - after put: map[1 := (1, 2), 3 := (5, 2), 4 := (6, 1), 5 := (7, 1), 10 := (100, 1)] <br>
GET (2) - after get: map[1 := (1, 2), 3 := (5, 2), 4 := (6, 1), 5 := (7, 1), 10 := (100, 1)] <br>
get(2) = -1 <br>
