
# coding: utf-8

# In[1]:


# SAT SOLVER Optmization Methods (CS 508)
# Author- Mukul Verma (160101044)


# In[2]:


# import the required packages
import os
import sys
import time
from enum import Enum,auto
from sortedcontainers import SortedDict, SortedSet


# In[3]:


def parse_args():
    nargs = len(sys.argv)
    if nargs<2:
        raise Exception("Input File is not provided.")

    return sys.argv[1]


# In[4]:


# ENUM CLASSES

# function override (of class Enum in python) to generate the automatic 
# enum value which is equal to the name of the enum
class AutoName(Enum):
    def _generate_next_value_(name, start, count, last_values):
        return name
    
# enum LitState
# This enum represents the state of the literal
# L_SAT ==> literal is satisfied that is literal is assigned true.
# L_UNSAT ==> literal is unsatisfied that is literal is assigned false
# L_UNASSIGNED ==> literal is unassigned
class LitState(AutoName):
    L_SAT = auto()
    L_UNSAT = auto()
    L_UNASSIGNED = auto()
    
# enum SolverState
# This enum represents the state of the SAT solver
# SAT ==> SAT formula is satisfied that is SAT formula has a true assignment 
#         and solver has reached to that state where it has found the satisfiable assignments
# UNSAT ==> SAT formula is unsatisfied that is SAT formula does not have any true assignment
#           and solver has reached to the state where it has found that the SAT formula is unsatisfiable
# CONFLICT ==> solver has encountered a conflict 
# UNDEF ==> Solver state is undefined that is solver cannot decide over the conflict or satisfiability
#           of the SAT formula.
class SolverState(AutoName):
    SAT = auto()
    UNSAT = auto()
    CONFLICT = auto()
    UNDEF = auto() 


# In[5]:



# Clause Class

# A class which contains a clause and its required attributes
class Clause:
    def __init__(self):
        super(Clause,self).__init__()
        self.c = []             # a list variable which holds the literals of a clause
        self.lw = None          # left watch literal of the clause
        self.rw = None          # right watch literal of the clause
    
    # The function returns the next non false literal as the new watch literal in the clause during BCP. 
    # Arguments :: 
    #     1. other_watch ==> the literal of the clause which is not being replaced during BCP of the clause. 
    #     2. S           ==> reference to the solver class (given below) to access its functions.
    # Description :: The function iterates over the literals of the clause and checks if any
    #                literal which is not false is present in the clause or not. If found, it return that 
    #                literal and if not it returns NULL which represents that no new watch literal is found.  
    def get_next_watch(self, other_watch, S):
        for i,lit in enumerate(self.c):
            
            # check if the literal is not false and literal is not the other watch literal, if both true,
            # we found out new watch literal.
            if S.get_lit_state(lit) != LitState.L_UNSAT and lit != other_watch:
                return lit
        return None
    


# In[6]:


# Solver Class

# A class which represents the SAT solver object and contains the SAT solver attributes.
class Solver:
    def __init__(self,nvars_,nclauses_):
        super(Solver,self).__init__()           

        # VARIABLES TO STORE THE CNF RELATED ATTRIBUTES

        self.nvars = nvars_                             # ==> variable to store the total number of variables in SAT formula                                                                                     
        self.nclauses = nclauses_                       # ==> variable to store the total number of clauses in the SAT formula (including unary clauses)
        self.nlits = 2*nvars_                           # ==> variable to store the total number of literals in the SAT formula
        self.cnf = []                                   # ==> list to hold the clause objects (excluding unary clauses)
        self.unit_c = []                                # ==> list to hold the unary clauses (only literal not the clause object as in self.cnf)
        
        
        #VARIABLES USED FOR BCP, CONFLICT ANALYSIS AND BACKPROPOGATION

        self.watches = {indx : [] for indx in range(-nvars_,nvars_+1)}  # ==>  watch list for each literal :: A dictionary with literal as the key and
                                                                        #      value as the list of indexes of clauses in which that literal is one of the
                                                                        #      watch literal. As literal can be negative hence dictionary is used instead 
                                                                        #      of a list of list. 
        
        
        
        self.lit_state = [0 for i in range(self.nvars+1)]                # ==> a list to store the state (0,1,-1) of the literal 
        self.lit_prev_state = [0 for i in range(self.nvars+1)]           # ==> a list to store the previous state of the literal (PHASE-SAVING) 
        self.BCP_stack = []                                              # ==> stack which contains the literals which should be propogated through BCP
                                                                         #     Stack is used here instead of a queue as , we are traversing in DFS manner.
        

        self.dl_var = [-1 for i in range(self.nvars+1)]                  # ==> A list to store the decision level at which a variable is assigned.
        self.dl = 0                                                      # ==> Variable to store the current level of the solver
        self.trail = {}                                                  # ==> A dictionary to store the sequence of the assignments of the literal. The key of
                                                                         #     the dictionary is the decision level and value is a list of the literals in the order 
                                                                         #     in which they were assigned in that particular decision level.
                                                                         #     The format can be shown as {<decision_level>: [l1,l2,l3,l4,...] } , l1,l2,.. are literals
                                                                         #     assigned in the decision level <decision_level> in the order l1,l2,l3,........

        self.antecedent = [-1 for i in range(self.nvars+1)]              # ==> a list to store the antecedent clause of the literal.(see the definition of 
                                                                         #     antecendent clause from the writeup)
        

        # VARIABLES USED FOR DECIDE ::

                                              
        self.var_score = [0 for i in range(self.nvars+1)]                # ==> list to store the scores of the variables based on VSIDS heuristics. Initial
                                                                         #     scores of each variable is the number of clauses in which it appears and value 
                                                                         #     is increased when that variable is involved in the learned clause (Clause Learning). 
        
        self.score_map = SortedDict()                                    # ==> A dictionary which maps the scores to the variable having that score. Key is score and 
                                                                         #     and value is a list of variables having that score. This is used to decrease the complexity
                                                                         #     of searching the highest score unassigned variable in decision.
        
        self.max_score = 0                                               # ==> A variable to store the current maximum score. Using this we can directly access the 
                                                                         #     the variable list using self.score_map. This reduces the access time in decision.
        
        self.score_map_r_it = self.score_map.__reversed__()              # ==> A reverse iterator to iterate from highest to lowest score in self.score_map 


        # VARIABLES USED FOR RESTART :: 

        self.LUBY_FACTOR = 100                                           # ==> Factor to be multiplied to the LUBY series which is used in Restart  
        self.inner = 0                                                   # ==> inner list pointer of the luby series
        self.outer = 0                                                   # ==> outer list pointer of the luby series
        self.u = 1                                                       # ==> heler variables u,v to generate the next number of luby series
        self.v = 1                                                       # ==> stores the current number in the luby series
        self.luby_list = [100]                                           # ==> list to store the luby series multiplied by LUBY_FACTOR
        self.nconflicts = 0                                              # ==> variable to store the number of conflicts seen so far from the last restart.
                                                                         #     If the number of conflicts reaches the value of inner series then restart is
                                                                         #     is done and this values is set to 0.
       
        self.restarts = 0                      #number of restarts
        self.learned_clause =0                 #number of learned clause
        self.decisions = 0                     # number of decisions
        self.implications = 0                  # number of implications
        
    
    # SOLVER FUNCTIONS :::::::::::

    # DESCRIPTION :: This function returns the state of the literal. A literal is unassigned (that is L_UNASSIGNED) if it's variable state is 0 and 
    #                it is satisfied (that is L_SAT) if it is negative literal and it's variable state is -1 (then literal has state 1) and
    #                if it postive literal and it's variable state is 1 (then literal has state 1). In all other cases the literal is unsatisfied. 
    # AEGUEMENTS :: lit ==> A literal whose state is required.
    def get_lit_state(self,lit):
        var = abs(lit)                                                  # calculate the respective variable of the literal
        state = self.lit_state[var]                                     # get the state of that variable
        if state == 0:                                                  # if state == 0, literal is unassigned
            return LitState.L_UNASSIGNED                            
        elif ((lit<0 and state == -1) or (lit>0 and state == 1)) == 1:  # if any one condition given before the function defintion for satisiability 
                                                                        #   of literal holds return satisfied
            return LitState.L_SAT
        else:
            return LitState.L_UNSAT                                     # otherwise return unsatisfied
    
    
    # DESCRIPTION :: This function sets the left and right watches of the clause as the literals present at postion l and r in the clause, inserts
    #                the clause in the watch list of the literals and add it to the cnf.
    # ARGUMENTS ::  C ==> Clause which is to be added
    #                l ==> Index of left watch literal
    #                r ==> Index of right watch literal
    def add_clause(self,C,l,r):
        C.lw = C.c[l]                                                   # set the left and write literals.
        C.rw = C.c[r]

        self.cnf.append(C)                                              # add the clause in the cnf formula
          
                                                                        # CLAUSE IS 0 INDEXED, LITERAL IS 1 INDEXED
        size = len(self.cnf)-1                                          # add the clause in the watch list of each literal.
        self.watches[C.lw].append(size)
        self.watches[C.rw].append(size)



    # DESCRIPTION :: This function add the unary clause. This function does not add unary clause into the cnf formula. Instead assign the value to
    #                the literal as true as this literal can only be true for the formula to be satisfiable and hence unit propogate it's negation.
    # ARGUMENTS ::  C ==> The unary clause object
    def add_unary_clause(self,C):
        cl = C.c                                                        # get the clause from the Clause object
        self.assert_unary(cl[0])                                        # assign the literal its required value,i.e 1 if positive literal and -1 otherwise
        self.BCP_stack.append(-1*(cl[0]))                               # add literal's negation in the BCP stack to propogate it through BCP
        self.unit_c.append(cl[0])                                       # add the literal into the unit clause list


   
    # HEURISTICS USED :: The heuristic used for BCP is based on two watched literal proposed in "Chaff: Engineering an Efficient SAT Solver" paper.
    #                    The explanation about heuristic is given in the writeup.
    # DESCRIPTION :: This function propogates the literals in the BCP stack, using Binary Constraint Propogation (BCP) and also updates the 
    #                watch list corresponding to the literal being propogated. As the unit propogated variable is assigned -1 (L_UNSAT state), 
    #                a new literal (which is not false) must replace this literal in the clauses in which this literal is a watch literal. 
    #                If a new literal is found, watch is updated. If not then if other watch literal of the clause if true then the clause is satisfied
    #                and we continue to the next clause in the watch list of the literal else if other watch literal is unassigned then the clause becomes unit
    #                as all other literals in that clause are false and then other watch literal is unit propogated and If the other watch literal is
    #                false then sovler is arrived at a conflict and conflict analysis and backtracking is done.
    def BCP(self):
        while len(self.BCP_stack)!=0:                                           
            lit = self.BCP_stack.pop()
            updated_watch_list = []                                     # ==> updated list of clauses in which literal is watch after unit propogation of literal
            conflict_cl_indx = None                                     # ==> a variable to store the conflicting clause (in which conflict is produced) index.

            for i,cl_indx in enumerate(self.watches[lit]):              # ==> iterate over the clauses in which literal is a watch literal
                cl_lw = self.cnf[cl_indx].lw                            # ==> get the left and right watch literal
                cl_rw = self.cnf[cl_indx].rw

                is_left_watch = 1                                       
                other_watch = cl_rw

                if lit == cl_rw:                                        # ==> if literal is right watch literal then other watch literal is left watch literal
                    is_left_watch = 0                                   #     hence set the other watch literal
                    other_watch = cl_lw

                new_watch = self.cnf[cl_indx].get_next_watch(other_watch,self)  # ==> get the next not false literal in the clause.

                                                                        # ==>  If new watch is not found then watch is not changed hence push the clause in 
                if new_watch == None:                                   #      the updated watch list of literal
                    updated_watch_list.append(cl_indx)

                if new_watch != None:                                   # ==> if new watch literal is found, update the watch accordingly. 
                    if is_left_watch == 1:
                        self.cnf[cl_indx].lw = new_watch
                    else:
                        self.cnf[cl_indx].rw = new_watch    
                    self.watches[new_watch].append(cl_indx)             # ==> push the clause in the watch list of the new watch literal
                
                
                else:                                                           # ==> else if new watch literal is not found    
                    if self.get_lit_state(other_watch) == LitState.L_UNSAT:     #     if the other watch literal state is unsatisfiable then 
                        if self.dl==0:                                          #     if decision literal is 0 then SAT is unsatifiable as we can backjump to 
                            return SolverState.UNSAT, None                      #     flip a variable. 
                        
                        self.BCP_stack.clear()                                  #     else if decision level != 0, clear the BCP stack as the backjump will reset the
                                                                                #     assigned state (to unassigned) of the literals in the BCP stack as BCP stack only
                                                                                #     contains the variables at the current decision literal.  
                        
                        conflict_cl_indx = cl_indx                              #     set the conflicting clause index 
                        for j in range(i+1,len(self.watches[lit])):             #     add all other clauses into the watch lits of the literal as no change in their watch literals.
                            updated_watch_list.append(self.watches[lit][j]) 
                        break                                                   #     break the loop to perform conflict analysis

                    elif self.get_lit_state(other_watch) == LitState.L_SAT:     # ==> else if other watch is satisfied then continue to next clause
                        continue
                    else:                                                       # ==> else the clause is unit as the other watch is the only unassigned
                                                                                #     literal of the clause
                        self.assert_lit(other_watch)                            #     Assign the literal its value (that is true)
                        self.BCP_stack.append(-1*(other_watch))                 #     Make the clause as antecedent of the other watch literal.  
                        self.antecedent[abs(other_watch)] = cl_indx

            self.watches[lit].clear()                                    # ==> Update the watch list of the literal. 
            self.watches[lit] = updated_watch_list  
            
            if conflict_cl_indx != None:                                 # ==> If there exists a conflict return the solver state as the conflict  and
                return SolverState.CONFLICT, conflict_cl_indx;           #     also return the conflicting clause index
            
        return SolverState.UNDEF, None                                   # ==> else solver is in undef state and a decision is taken next.

    
     
    # DESCRIPTION :: This function increases the score of the literal by 1 and updates the scores_map accordingly. 
    # ARGUEMENTS :: var ==> variable whose score is to be increased 
    def increase_score(self,var):
        old_score = self.var_score[var]                                 # ==> get the old score and calculate the new score
        score = self.var_score[var]+1

        self.var_score[var] = score                                     # ==> set the new score of the variable

        if self.score_map.get(old_score):                               # ==> Update the data structure holding the (scores,[literals_list]) key-value  
            self.score_map[old_score].discard(var)                      #     pair according to the changed score. That is delete the previous entry 
            if len(self.score_map[old_score])==0:                       
                del self.score_map[old_score]

        if not self.score_map.get(score):                   
            self.score_map[score] = SortedSet()
    
        self.score_map[score].add(var)                                  #     and add the new entry


    
    # HEURISTICS USED :: The confilct analysis is based on "CLAUSE LEARNING" using "IMPLICATION GRAPH" as by Zhang in "Efficient Conflict Driven Learning 
    #                    in a Boolean Satisfiability Solver" paper. Each literal maintains an antecedent clause which is the clause due to which the unit
    #                    propogation of that literal is happened when that clause bacame unit. The detailed explanation is written in writeup.
    
    # DESCRIPTION ::     This function learns the reason clause by performing resolution of current clause and antecedent clause. The implementation first
    #                    selects the current clause as the conflicting clause and adds the literals not in the conflicting level (at which conflict occurs) to the learned clause and mark
    #                    the literals of conflicting level in the current clause. Then, the literal which is last assigned literal is resoluted with its antecedent
    #                    clause. This resoluted clause is then made as the current clause and same procedure is continued till we reaches to a literal 
    #                    which is the only marked literal. This literal becomes the 1-UIP in the implication graph and its negation is added in the learned clause.
    #                    The second highest decision level of the literals in the learned clause is made as the backjump level. This is done because doing so
    #                    makes the learned clause as unit clause (reason in writup) and we get a new literal to propogate just after the backtracking.
    
    # ARGUEMENTS :: conflict_c ==> conflicting clause in which conflict is occured during BCP.
    def conflict_analysis(self,conflict_cl):
       
        current_cl = conflict_cl                                        # ==> make the conflicting clause as the current clause  
        confl_level_lit = 0                                             # ==> variables to hold the marked literals at the conflicting level,
        reason_cl = []                                                  #     to hold learned clause 
        bcktrack_l = 0                                                  #     to store backtrack level
        second_hl_lit = 0                                               #     to store one of the other watch literal of the learned clause
        trail_indx = len(self.trail[self.dl])-1                         #     reverse iterator to the trail
        visited = [0 for i in range(self.nvars+1)]                      #     visited array to mark the literals

        lit = None                                                      #     literal and variable to hold the 1-UIP
        var = None

        while True:
            for lit in current_cl:                                      # ==> iterate over the current clause
                var = abs(lit)                              
                var_level = self.dl_var[var]                            
                if var_level== self.dl and visited[var]==0:             # ==> if literal's decision level is conflicting level mark it and increas the counter
                    visited[var]=1                              
                    confl_level_lit +=1                                 
                elif var_level!= self.dl and (lit not in reason_cl):    #     else add it in the reason clause if it is not already present in it.
                    reason_cl.append(lit)
                    self.increase_score(abs(lit))                       #     ncrease the VSIDS score of literal as it is involved in conflict.  

                    if var_level > bcktrack_l:                          # ==> set the backrack level to the highest level in the learned clause which will
                        bcktrack_l = var_level                          #     beacome second highest when 1-UIP (belongs to conflicting level) is added  
                        second_hl_lit = len(reason_cl)-1

            while trail_indx >= 0:                                      # ==> get the last assigned literal in the trail which is marked by iterating in the
                lit = self.trail[self.dl][trail_indx]                   #     trail of the conflicting level in the reverse order.
                var = abs(lit)
                trail_indx -= 1
                if visited[var]==1:                                     #     if mark is true, we have found the last assigned literal                                     
                    break       

            visited[var] = 2
            confl_level_lit -= 1                                        # ==> decrease the counter as we will resolute one of the marked literal
            
            if confl_level_lit == 0:                                    # ==> if none other literal is marked else one then break the loop as we have found 
                break                                                   #     1-UIP
            
            ant = self.antecedent[var]                                  # ==> else calculate the antecendent of the last assigned literal
            current_cl = self.cnf[ant].c.copy()                         #     get the antecedent clause (use copy so that original clause do not get changed)
            current_cl.remove(lit)                                      #     remove the literal from the clause which is resolution of the last assigned literal
       
        UIP1 = -1*(lit)                                                 
        reason_cl.append(UIP1)                                          # ==> add the negation of the 1-UIP in the reason/learned clause

        self.increase_score(abs(UIP1))                                  # ==> Increase the VSIDS score of the UIP as it is involved in conflict

                                                                        # ==> add the uip in the BCP stack for the unit propogation as the clause will become 
                                                                        #     unit after backpropogation
        if len(reason_cl)==1:                                           
            self.BCP_stack.append(lit)                                  #     If it is unit ,add it into the unit clauses  
            self.unit_c.append(UIP1)
        else:
            self.BCP_stack.append(lit)                                  
            C = Clause()                        
            C.c = reason_cl                                     
            self.add_clause(C,second_hl_lit,len(reason_cl)-1)           # ==> else add it into the cnf with other clauses
        self.learned_clause +=1
        self.nconflicts+=1                                              # ==> increase the number of conflict which is be used for restart.
        return UIP1, bcktrack_l                                         # ==> return the UIP and backtrack level for backtracking
        
    
    
    # HEURISTICS USED :: The heuristics used for deciding the literal is to select the literal having maximum score. The scoring method is based on the 
    #                   "VSIDS" proposed in "Chaff: Engineering an Efficient SAT Solver" paper. The defualt score of each variable is the number in
    #                   which that variable appears and increased by 1 if that var occurs in conflict. 
    #                   The heuristics used for selecting the value of the decided variable is based on "PHASE SAVING", which involves setting the 
    #                   value of the variable as the last value it was assigned. 
    # DESCRIPTION ::    This function selects and assign value to a unassigned variable based on the above heuristic. If a vaiable is not found that is
    #                   all the varibles are assigned then it returns Solver State as SAT, otherwise it propogates the selected literal.
    def decide(self):
        
        best_var = None                                                 # ==> variable to store the decided variable
        while True:
            if self.score_map.get(self.max_score):                      # ==> iterate from the current max score of the unassigned variables
                for var in self.score_map[self.max_score]:              #     in the reverse order.   
                    # print("HAIIII ")
                    if self.lit_state[var] == 0:                        # ==> If a variable is found, break the loop
                        best_var = var 
                        break

            if best_var==None:                                          #     If variable is not found in the list of variables having max score, then
                hasNext = next(self.score_map_r_it,None)                
                if hasNext == None:                                     #     if the max score is the minimum score then break the loop as no variable
                    break                                               #     be decided.
                else:
                    self.max_score = hasNext                            #     else go the score which is just less than the current maxscore      
            else:
                break

        if best_var == None:                                            # ==> If no variable is decided, return SAT. 
            return SolverState.SAT
        
        self.decisions +=1
        best_lit = None                                                 # ==> select the literal based on the last assigned state of variable
        if self.lit_prev_state[best_var] == 1:                          # ==> If previous saved state was 1 then it must be positive literal corresponding 
            best_lit = best_var                                         #     to the variable, hence make decided literal as positive literal
        else:
            best_lit = -1*best_var                                      # ==> If it was unassigned or assigned -1, select negative literal.
                                                                        #     Selecting negative when uassigned is a good choice as in SAT assignments of
                                                                        #     variables in a cnf are mostly false.  
       
        self.dl = self.dl+1                                             # ==> increase the decision level of the solver
        self.assert_lit(best_lit)                                       # ==> assign the value to the literal and add it into the trail
        self.BCP_stack.append(-1*best_lit)                              # ==> do the BCP
        return SolverState.UNDEF


    # DESRIPTION :: This function assign the state to the variable based on the literal. As passed literal is assigned true, hence state of the 
    #               variable is made 1 if the literal is positive and -1 if it is negative. Literal is added to the trail at its decision level
    # ARGUMENT :: lit ==> literal to be assigned and added to the trail  
    def assert_lit(self,lit):
        self.implications +=1
        var = abs(lit)
        if lit<0:                                                       # ==> if lit is negative
            self.lit_state[var] = self.lit_prev_state[var] = -1         #     update previous state and current_state as -1
        else:
            self.lit_state[var] = self.lit_prev_state[var] = 1          #     else update to +1

        if not self.trail.get(self.dl):                                 # ==> if the current literal is the decision literal then a new level is added in the trail
            self.trail[self.dl] = []

        self.trail[self.dl].append(lit)                                 # ==> literal is added into the trail at its decision level.
        self.dl_var[var] = self.dl                                      # ==> set the decision level of the literal as the current level


    # DESRIPTION :: This function assign the state to the unary variable based on the unary literal. The logic of assignment is same as above function.
    #               This function donot add the literal to the trail as it is unary and the value of the literal is fixed (that is true) and saves the 
    #               time for reassigning after the backtrack or restart.
    def assert_unary(self,lit):
        self.implications +=1
        var = abs(lit)
        if lit<0:
            self.lit_state[var] = self.lit_prev_state[var] = -1
        else:
            self.lit_state[var] = self.lit_prev_state[var] = 1 
        self.dl_var[var] = 0    


    # DESCRIPTION :: This function performs "non chronological backtracking technique" and backtracks to a level calculated in the conflict anaysis. This function
    #                resets the literals decision level, states of their variables and the antecedent clauses of the literals for the level > backtrack level.
    #                This function also resets the max_score as new variables will become unassigned. After resetting the variables and the max_score, it assigns the
    #                value to the UIP calculated in the conflict analysis. This is done after resetting, otherwise backtracking will reset its value.

    # ARGUMENTNS ::  bcktrack_l ==> level till which backtracking it to be done
    #                UIP ==> UIP literal calculated from the conflct analysis. 
    def backtrack(self,bcktrack_l,UIP):
        level = bcktrack_l+1                                            # ==> set the starting resetting level and start resetting the variables from this level 

        for dl in range(level,self.dl+1):                                               # ==> iterate over the decision level to reset 
            if self.trail.get(dl):                                                      
                for lit in self.trail[dl]:                                              # ==> iterate over the trail of that decision level
                    self.lit_state[abs(lit)] = 0                                        # ==> reset the state, decision level and antecedents
                    self.dl_var[abs(lit)] = -1
                    self.antecedent[abs(lit)] = -1
                    self.max_score = max(self.max_score,self.var_score[abs(lit)])       # ==> update the max score 

        self.score_map_r_it = self.score_map.__reversed__()                             
        curr_sc = next(self.score_map_r_it,None)                                        
        
        while curr_sc != None and curr_sc!= self.max_score:                             # ==> reset the reverse iterator to the new position where
            curr_sc = next(self.score_map_r_it,None)                                    #     max score lies

        if curr_sc == None:                                                             # ==> reset if max_score is not longer valid that is not present
            self.score_map_r_it = self.score_map.__reversed__()                         #     (A check, condition may never becomes true)
            max_score = next(self.score_map_r_it)


        while level <= self.dl:                                                         # ==> erase the trail till the backtrack level
            if self.trail.get(level):
                del self.trail[level]
            level+=1
              
        var = abs(UIP)                                                              
        self.dl = bcktrack_l                                                            # ==> set the current level as the backtrack level
        if bcktrack_l == 0:                                                             # ==> if backtrack level ==0, the uip must be unary, as
            self.assert_unary(UIP)                                                      #     level 0 is the lowest level and hence only single literal will  
                                                                                        #     be present in the learned clause suring conflict analysis
        else:                                                                           # ==> else assign the state to the UIP variable and add it into the trail
            self.assert_lit(UIP)                    
            self.antecedent[var] = len(self.cnf)-1                                      # ==> set it's antecendent clause

    
    # DESCRIPTION :: This function return the next number in the luby series. THIS IMPLEMENTED FUNCTION IS TAKEN FROM THE SAT4J SAT SOLVER 
    #                http://www.sat4j.org/maven233/org.sat4j.core/xref/org/sat4j/minisat/restarts/LubyRestarts.html
    def get_next_luby(self):
        if (self.u & -1*self.u) == self.v:                # Luby series seqeunce is 1,1,2,1,1,2,4,1,1,2,1,1,2,4,8,1,1,2.......           
            self.u = self.u+1                             # where v gives the luby sequence and can be calculated from the method
            self.v = 1                                    # given in this function  
        else:
            self.v = self.v<<1
        return self.v


    # HEURISTICS ::  The restart is based on the iterative two nested luby series. The two series inner and outer are maintained.
    #                Whenever the number of conflicts become equal to the value of inner series, restart is done and inner series is incremented.
    #                Whenever inner series becomes equal to outer series, inner series is reset to starting value and outer series is incremented.
    #                More details are given in the writeup.
    # DESCRIPTION :: This funtion performs the restart and reset all the variables except the unit ones. It does not delete the learned clause. It is 
    #                to backtracking till level 0.    
    def restart(self):
        self.restarts +=1
        for i in range(1,self.nvars+1):                                 # ==> reset the variables 
            if i not in self.unit_c or -i not in self.unit_c:
                self.lit_state[i] = 0
                self.dl_var[i]= -1
                self.antecedent[i] = -1
            
        self.trail.clear()                                              # ==> clear the trail and bcp stack
        self.BCP_stack.clear()                                              
        self.nconflicts = 0                                             # ==> reset the number of conflicts
        self.score_map_r_it = self.score_map.__reversed__()             # ==> reset the max score
        self.max_score = next(self.score_map_r_it)                          
        self.dl=0                                                       # ==> set the decision level to 0

        if self.inner == self.outer:                                    # ==> if the inner luby series has reached to outer luby series,
            next_luby = self.get_next_luby()*self.LUBY_FACTOR           # ==> get the next luby number
            self.luby_list.append(next_luby)                            # ==> append in the luby list
            self.outer += 1                                             # ==> increment the outer luby series
            self.inner = 0                                              # ==> reset the inner luby series to initial value
        else:
            self.inner += 1                                             # ==> else increment the inner luby series 


# In[7]:


# MAIN FUNCTIONS ::::

# DESCRIPTION :: This function read the cnf file and build the solver class and calculates the initial scores of the variables
# ARGUMENT ::    file ==> name of the file to be read
def read_cnf(file):
    global S
    
    f = open(file,"r")                                                  # ==> open the file
    nclauses = 0
    nvars = 0

    line = f.readline()                                                 # ==> read the first line

    while True:                                                         # ==> skip all the comments lines
        if "C" in line or "c" in line.split(" "):
            line = f.readline()
        else:
            break
            

    if not "p cnf" in line:                                                                 # ==> check if the file format is valid or not
        raise Exception("[File Error]: Expected p cnf at the beginning of the file")    

    l = line.split(" ")                                                                     # ==> get the number of variables and clauses
    nvars = int(l[2])
    nclauses = int(l[3])

    if nvars <=0 or nclauses <=0:                                       # ==> check if the number of variables and clauses are > 0
        raise Exception("Expected non-zero variables or clauses")

    print("Vars: {} Clauses: {}".format(nvars,nclauses))    
    
    S = Solver(nvars,nclauses)                                          # ==> initialize the solver instance
    
    for line in f:                                                      # ==> read the file line by line

        C = Clause()                                                     
        C.c = list(map(int,line.split(" ")[:-1]))                       # ==> read a clause  

        if len(C.c) <1:                                                 # ==> check if clause length is > 0
            raise Exception("Empty clause is not allowed");    
        
        dict_var = dict()                                              
        new_cl = []
        for lit in C.c:                                                 # ==> iterate over the clause and remove duplicate literals from the clause
            if lit > S.nvars:
                raise Exception("[Invalid Literal]: index is more than expected")
            if not dict_var.get(lit):                                   # ==> if literal is not present then
                dict_var[lit] = 1   
                new_cl.append(lit)                                      #     add the literal into the clause
                S.increase_score(abs(lit))                              #     increment the VSIDS score of the variable
        
        C.c = (new_cl)                                                  # ==> update the clause which contains the removed duplicates
        
        if len(new_cl) ==1:                                             # ==> len ==1 the add the unary clause
            S.add_unary_clause(C)
        else:
            S.add_clause(C,0,1)                                         # ==> else add the clause with 0 and 1 position literals as watches

    f.close()                                                           # ==> close the file
    print("File Read Time: %.6f seconds "%(time.process_time()-start_time))
   


# In[8]:


# DESCRIPTION :: This function implements the outer loop of the CDCL algorithm and call the BCP, conflict analysis, backtrack and decide function.
#                The function first calls the BCP() and if the return state is UNSAT then it concludes that the formula is unsatisfiable. Otherwise,
#                if there is conflict it calls conflict analysis to learn a new clause and the backtrack level and then calls backtrack to jump to the
#                backtrack level learned from the conflict analysis. If there is no conflict and unsat then this function calls decide to select a new
#                literal to be assigned and then that variable is propogated through BCP. The procedure terminates with decide return SAT or bcp returning
#                unsat.
def solve_cdcl():
    global S

    while True:                                                         # ==> Iterates till sat (all variables are assigned) or unsat is returned
        state, conflict_cl_indx = S.BCP()                               # ==> call BCP for Unit propogation of literals in the BCP stack
        if state  == SolverState.UNSAT:                                 # ==> return unsat if solver state is unsat
            return state
        elif state == SolverState.CONFLICT:                                     # ==> if state is conflict
            UIP, bcktk_l  = S.conflict_analysis(S.cnf[conflict_cl_indx].c)      #     calls conflict analysis and get the backtrack level and uip

            if S.nconflicts >= S.luby_list[S.inner]:                            # ==> If number of conflicts are greater than the inner luby series value
                                                                                #     call the restart. Backtrack is not called as it is already reset to level 0
                S.restart()                     
            else:                                                               # ==> calls the backtrack till the level returned by conflict analysis
                S.backtrack(bcktk_l,UIP)
        else:                                                               
            state = S.decide()                                          # ==> calls decide only after BCP not after conflict anlaysis as learned clause becomes
                                                                        #     unit after backpropogation and we get a literal to perform BCP.
            if state == SolverState.SAT:                                # ==> If sat is return that is no other variable is unassigned, return sat.
                return state


# In[9]:


### HELPER FUNCTIONS :::::


# DESCRIPTION :: check if the assignments done by the solver are valid or not.
def validate():
    for i,cl in enumerate(S.cnf):                                       # ==> iterate over all the clauses
        found =0
        for lit in cl.c:                                                # ==> and all the literals of that clause
            if S.get_lit_state(lit) == LitState.L_SAT:                  # ==> if atleast one of the literal is satisfied, then the clause is satisfied
                found = 1                                                 
                break
        if found==0:                                                    # ==> else clause is unsatisfied and assignments are not correct.
            print("fail on ",i)
            return False
            break
    return True                                                         # return true if all the clauses are satisfied 


# In[10]:


# DESCRIPTION :: This function writes the assignments into the file
def write_assignments(assgn_file):
    for var, state in enumerate(S.lit_state):
        if var==0:
            continue
        
        if state == -1:
            assgn_file.write(str(var) +" :: False\n")
        else:
            assgn_file.write(str(var) +" :: True\n")
        
    
    assgn_file.close()


# In[11]:


## MAIN FUNCTION :::

if __name__== "__main__":
    start_time = time.process_time()                                #start the timer
    # file_name = parse_args()

    read_cnf("./final_test/bmc-3.cnf")                                # build the cnf and solver by reading the passed file as arguement
    S.score_map_r_it = S.score_map.__reversed__()                   # reset the iterator and max score 
    S.max_score = next(S.score_map_r_it)                        
    print(solve_cdcl())                                             # call cdcl function to solve the cnf
    print(validate())                                               # check the validity of assignemnts 
    end_time = time.process_time()                                  # print the time taken
    print(end_time-start_time)


# In[14]:


# # MAIN FUNCTION TO SOLVE ALL THE FILES FROM A FOLDER AND PRINT ASSIGNMENT AND TIME TAKEN INTO THE DEFINED FILES
# # uncomment to use 

# if __name__== "__main__":
#     test_folder = "./final_test/"
#     status_file = open("./status/status.txt","w+")
    
#     assign_folder = "./assignments/"
#     for file in os.listdir(test_folder):
#         print("File executing: ","./final_test/"+file)

        
#         start_time = time.process_time()
        
#         read_cnf("./final_test/"+file)
#         S.score_map_r_it = S.score_map.__reversed__()
#         S.max_score = next(S.score_map_r_it)
        
#         status = solve_cdcl()
#         status_assgn = validate()
        
#         print(status, status_assgn)
        
#         end_time = time.process_time()
#         print(end_time-start_time)
        
#         if status == SolverState.SAT and status_assgn == True:
# #             assgn_file = open(assign_folder + file[:-3]+"txt","w+")
#             status_file.write("Statistics :::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
#             status_file.write("CNF in "+file+" :: SATISFIABLE\n")
#             status_file.write("### Time " + str(end_time-start_time)+"\n")
#             status_file.write("### Restarts: "+str(S.restarts))
#             status_file.write("### Learned Clauses: "+str(S.learned_clause))
#             status_file.write("### Decisions: "+ str(S.decisions))
#             status_file.write("### Implications: "+ str(S.implications))
#             status_file.write("\n\n")
            

# #             write_assignments(assgn_file)
            
#         elif status == SolverState.UNSAT:
#             status_file.write("Statistics :::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::")
#             status_file.write("CNF in "+file+" :: UNSATISFIABLE\n")
#             status_file.write("### Time " + str(end_time-start_time)+"\n")
#             status_file.write("### Restarts: "+str(S.restarts))
#             status_file.write("### Learned Clauses: "+str(S.learned_clause))
#             status_file.write("### Decisions: "+ str(S.decisions))
#             status_file.write("### Implications: "+ str(S.implications))
#             status_file.write("\n\n")
#     status_file.close()

