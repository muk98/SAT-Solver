<<<<<<<=========== Files/folder Info ============>>>>>>>
1. sat.ipynb and sat.py contains the main code. One is jupyter notebook version of other.
2. status.txt contains the output from the run over different file in the edusat format
3. assignments.txt contains the files having the variable assignments (Only for SAT).




<<<<<<<<<<<========== Installation Guide =====>>>>>>>>
To run the code the machine should have ::

1. Python 3.6
2. Install the sortedcontainers using pip3 install sortedcontainers



<<<<<<<<<============== How to run ========>>>>>
The folder contains two files sat.ipynb and sat.py. One is jupyter notebook version of other.

a. How to run sat.ipynb

1. Load the file using jupyter noetbook
2. Run the code cell wise

b. How to run sat.py

Run the below command to run the code
1. python3 sat.py


<<<<<========== How to change the file in the code ======>>>>>>>>>>
In order to specify the file, change the name of the file in the  __main__ function at the end of the code.

For eg :: read_cnf("1.txt") or read_cnf("2.txt") where 1.txt and 2.txt are the file names
