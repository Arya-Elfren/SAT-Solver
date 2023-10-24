from array import array
from collections import Counter, deque 
from functools import reduce
from itertools import chain, takewhile
import numpy as np # only used for simple_sat_solve
from random import getrandbits
from typing import Deque, List, Optional, Set, Tuple


################################################################


def load_dimacs(path: str) -> List[List[int]]:
    """
    Given a fileName as a string it returns a clause set as a List of Lists of ints.
    """
    with open(path, 'r') as f:
        lines = (
            l.strip() # 4. remove extra whitespace
            for l in takewhile(
                lambda x: x[0] != "%", # 2. stop reading after reaching a line starting with `%`. A workaround for reading test files from https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
                f.readlines() # 1. read all the lines
            ) if l[0] != "c" and l[0] != "p" # 3. if it's a comment or the metadata line, ignore it
        )
        return [
            [
                int(y) # 10. convert them to int
                for y in x.strip() # 8. strip the whitespace
                    .split(" ") # 9. split the clause into literals
            ] for x in " ".join(lines) # 5. join the lines with a space, this makes multiline clauses just the same as all the other clauses
                .split(" 0") # 6. split on all separators
                [:-1] # 7. ignore last empty string from split
            ]


################################################################


def simple_sat_solve(clause_set: List[List[int]]) -> Optional[List[int]]:
    def truth_assig_gen():
        # the number of variables in the clause_set
        max_number_of_var = max(map(abs, chain.from_iterable(clause_set)))
        # + 1 so that indexing works easily 
        arr = np.full(max_number_of_var + 1, False)
        # binary numbers incrementing is equivalent to a truth table
        for i in range(2 ** max_number_of_var):
            # reset array to false
            arr.fill(False)
            # the inverted binary digits of `i` without the `0b` at the start
            digits = bin(i)[:1:-1]
            # list of digits as ints `[0] +` so that they index into arr correctly 
            digits = [0] + list(map(int, digits))
            # all indeces of digits that are non-zero
            idx_digits = np.array(digits).nonzero()
            # set all indeces that are 1 in digits to True in arr
            arr[idx_digits] = True
            yield arr


    def is_sat_from_arr(arr):
        # given a numpy arr from `truth_assig_gen` check if it satisfies `clause_set`
        new_clause_set = (
            [var for var in clause] # keep all variables
            for clause in clause_set # from all clauses where
            if not any( # there isn't any instance of it in arr
                # if var is negative we check for False at index abs(var)
                not arr[-var] if var < 0 else arr[var]
                for var in clause
            )
        )
        try:
            # try get the first clause
            next(new_clause_set)
            # if we succed then there's at least one unsat clause and we return False
            return False
        except StopIteration:
            # new_clause_set is empty so it's sat
            return True
    
    # filter all truth_assig_gen results for only those that are sat
    # it's lazy filtering from a generator so we only compute the first one
    all_sat_truth_assigs = filter(is_sat_from_arr, truth_assig_gen())
    try:
        # get the first sat truth assignment
        first_sat_truth_assig = next(all_sat_truth_assigs)
    except StopIteration:
        # if we get a StopIteration exception it's unsat
        return None
    # from [False, False, True] get [(0, False), (1, False), (2, True)]
    enum_first_sat_truth_assig = enumerate(first_sat_truth_assig)
    # depending on the truth value of the second value in the tuple either return
    # - the first value or + the first value
    first_sat_truth_assig_as_idxs = map(
        lambda x: x[0] if x[1] else -x[0],
        enum_first_sat_truth_assig
    )
    # turn to a list and ignore the truth value of idx 0 (added by `max_number_of_var + 1`) above
    return list(first_sat_truth_assig_as_idxs)[1:]


################################################################


def branching_sat_solve(clause_set: List[List[int]], partial_assignment: List[int]) -> Optional[List[int]]:
    def internal_branching_sat_solve(clause_set: List[List[int]], new_var: int):
        clause_set = [ # assign the new_var branching variable
                [var for var in clause if -var != new_var]
                for clause in clause_set
                if new_var not in clause
        ]

        if len(clause_set) == 0: # if SAT
            return [new_var]
        elif any(len(cl) == 0 for cl in clause_set): # if any clause UNSAT
            return None
        else:
            branch = clause_set[0][0] # branch on first variable

            left = internal_branching_sat_solve(clause_set, branch) # try left
            if left != None:
                return [new_var] + left

            right = internal_branching_sat_solve(clause_set, -branch) # try right
            if right != None:
                return [new_var] + right

            return None # dead end

    if len(partial_assignment) != 0: # if there is one, assign the partial assignment
        pas = set(partial_assignment)
        clause_set = [
            [var for var in clause if -var not in pas]
            for clause in clause_set
            if all(a not in clause for a in pas)
        ]

    res = internal_branching_sat_solve(clause_set, 0)
    return partial_assignment + res[1:] if res != None else None


################################################################


def unit_propagate(clause_set: List[List[int]]) -> List[List[int]]:
    units: Set[int] = set()
    while True:
        new_units = {u[0] for u in clause_set if len(u) == 1} # exctract all units
        if any(-u in units for u in new_units): # if any new_unit found has already been assigned its opposite
            return [[]] # UNSAT
        elif new_units.issubset(units): # if we've already discovered all those units
            return clause_set # finish
        units = units.union(new_units) # add the new units to our set
        clause_set = [ # propagate them by assigning them
            [var for var in clause if -var not in units]
            for clause in clause_set
            if all(var not in clause for var in units)
        ]
        if any(len(cl) == 0 for cl in clause_set): # if any clause UNSAT
            return [[]]


################################################################


"""
Below is an optimised version of DPLL that learns a clause at conflict points
(CDCL). If you make the first line of `learn_from_conflict`:
`data[1] -= 1; return` and remove the `while True` loop in `dpll_sat_solve` it
behaves as a normal DPLL algorithm.

By optimised I mean that it's much less readable than it used to be for
performance reasons. Classes and their method/property lookups are slow, so I
converted them into a list of function pointers. I also inlined all of my
functions.


The main idea is to split the clauses into the two watched literal format. In
this optimised implementation that means a tuple
`(watch_one, idx_of_watch_two, array_of_other_vars)`. Then have a mapping of
`parity_dependent_variable -> deque_of_clauses_watching_this_variable` which I
implement as a list of pointers where `watched_in[-var]` returns the deque of
clauses with a watch currently on `-var`. This means that unit propagation only
requires going through the deque of `watched_in[-unit]`, trying to find a new
not-false watch, and either appending it to the new queue or, upon failure to
do so, assign the new unit. This data structure is lazy and doesn't need any
re-setting upon backtracking.

The other idea is that during unit-propagation we remember which clause implied
the unit we're propagating so that if we reach a conflict we can backtrack
through the implication DAG to see what variables created this conflict and
then learn a new clause that means we don't conflict there again. To progress
faster we also backtrack to the decision level of the first variable in that
learned clause so we try something a bit different. This also means that our
UNSAT condition isn't finishing the recursion as our recursion is no longer
complete, but instead we raise UNSAT if we learn a conflict, or the conflict
happens at depth 0 (so without branching). This also lets us implement "random"
restarts, after a certain number of conflicts we restart the full recursion
tree at 0 which helps us avoid the long tail of DPLL. Due to a limitation of my
implementation we actually also restart completely whenever we learn a unit
clause.

My heuristic is a naive / greedy "most frequent variable" that doesn't get
updated by learned clauses. I implemented VSIDS (the state of the art CDCL
heuristic) but our clause sets are simply not big enough to benefit from that,
I don't learn enough clauses / reach enough conflicts.

My pre-processing removes duplicate literals and ignores trivially tautological
clauses (which helps tremendously on the "gt" instance that you can generate
with [6]). I tried implementing Bounded Variable Elimination but either my
implementation was too slow or our clause sets aren't big enough for it to be
worth while.

As I mentioned above, I implemented this with classes originally but after
inlining the methods I only had a bunch of state in the form of standard
library constructs to pass around to everything. I also kept having to do
method lookups when calling them. So instead I made a tuple of all of the
methods that my functions actually use and they index into that directly to
call the methods.


First, I found [0] when searching for efficient unit propagation strategies and
that led me to two watched literals [2][3]. I read and implemented the circular
approach described in [4]. All my other knowledge comes from the extremely
extensive and useful [1]. Chapters 3 and 4 are really good resources, I
recommend them to anyone interested in SAT-solving.

Amazing resources:
[0] Stack exchange answer that links to the relevant theory: https://cs.stackexchange.com/questions/150557/what-are-efficient-approaches-to-implement-unit-propagation-in-dpll-based-sat-so
[1] A. Biere, M. Heule, and H. van Maaren, Eds., Handbook of satisfiability, Second edition. Amsterdam ; Washington, DC: IOS Press, 2021.
[2] H. Zhang and M. Stickel, ‘An Efficient Algorithm for Unit Propagation’, Jan. 1996.
[3] M. Iser and T. Balyo, ‘Unit Propagation with Stable Watches’, 2021.
[4] I. P. Gent, ‘Optimal Implementation of Watched Literals and More General Techniques’, Journal of Artificial Intelligence Research, vol. 48, pp. 231–252, Oct. 2013, doi: 10.1613/jair.4016.
[5] ‘Hard formula generator (pysat.examples.genhard) — PySAT 0.1.8.dev1 documentation’. https://pysathq.github.io/docs/html/api/examples/genhard.html (accessed Mar. 16, 2023).
- ‘SATLIB - Benchmark Problems’. https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html (accessed Mar. 16, 2023).
- M. F. A. Platzer, ‘Lecture Notes on SAT Solvers & DPLL’.
- C. Sinz and T. Balyo, ‘Practical SAT Solving - Lecture 8’.
- M. Hořeňovský, ‘Modern SAT solvers: fast, neat and underused (part 3 of N)’, The Coding Nest, Apr. 16, 2019. http://codingnest.com/modern-sat-solvers-fast-neat-and-underused-part-3-of-n/ (accessed Mar. 16, 2023).

More relevant but too detailed resources:
- M. J. H. Heule, ‘Preprocessing Techniques’.
- G. Audemard and L. Simon, ‘Predicting Learnt Clauses Quality in Modern SAT Solvers’.
- M. Fleury, J. C. Blanchette, and P. Lammich, ‘A Verified SAT Solver with Watched Literals Using Imperative HOL’. Accessed: Mar. 16, 2023. [Online]. Available: https://matryoshka-project.github.io/matryoshka2018/slides/Matryoskha-2018-Fleury-A-Verified-SAT-Solver.pdf
- J. Liang, H. Govind, P. Poupart, K. Czarnecki, and V. Ganesh, ‘An Empirical Study of Branching Heuristics through the Lens of Global Learning Rate’.
- J. Jacobs, ‘Bounded clause elimination’.
- M. Ginsberg, ‘Branching Heuristics’. https://www.cs.cmu.edu/afs/cs/project/jair/pub/volume21/dixon04a-html/node8.html (accessed Mar. 16, 2023).
- N. Eén and A. Biere, ‘Effective Preprocessing in SAT Through Variable and Clause Elimination’, in Theory and Applications of Satisfiability Testing, vol. 3569, F. Bacchus and T. Walsh, Eds. Berlin, Heidelberg: Springer Berlin Heidelberg, 2005, pp. 61–75. doi: 10.1007/11499107_5.
- M. J. H. Heule, B. Kiesl, and A. Biere, ‘Encoding Redundancy for Satisfaction-Driven Clause Learning’, in Tools and Algorithms for the Construction and Analysis of Systems, vol. 11427, T. Vojnar and L. Zhang, Eds. Cham: Springer International Publishing, 2019, pp. 41–58. doi: 10.1007/978-3-030-17462-0_3.
- M. Järvisalo, M. J. H. Heule, and A. Biere, ‘Inprocessing Rules’, in Automated Reasoning, vol. 7364, B. Gramlich, D. Miller, and U. Sattler, Eds. Berlin, Heidelberg: Springer Berlin Heidelberg, 2012, pp. 355–370. doi: 10.1007/978-3-642-31365-3_28.
- M. G. Lagoudakis and M. L. Littman, ‘Learning to Select Branching Rules in the DPLL Procedure for Satisfiability’, Electronic Notes in Discrete Mathematics, vol. 9, pp. 344–359, Jun. 2001, doi: 10.1016/S1571-0653(04)00332-4.
- M. Kim, ‘SAT Solver Heuristics’. Accessed: Mar. 16, 2023. [Online]. Available: https://swtv.kaist.ac.kr/courses/cs453-fall09/model_checkin_2.pdf
- ‘Software Search - zbMATH Open’. https://zbmath.org/software/484 (accessed Mar. 16, 2023).
- J. H. Liang, V. Ganesh, E. Zulkoski, A. Zaman, and K. Czarnecki, ‘Understanding VSIDS Branching Heuristics in Conflict-Driven Clause-Learning SAT Solvers’, arXiv.org, Jun. 30, 2015. https://arxiv.org/abs/1506.08905v3 (accessed Mar. 16, 2023).

Less relevant things I looked at:
- O. Dubois and G. Dequen, ‘A backbone-search heuristic for efﬁcient solving of hard 3-SAT formulae£’.
- S. A. Cook, ‘A short proof of the pigeon hole principle using extended resolution’, SIGACT News, vol. 8, no. 4, pp. 28–32, Oct. 1976, doi: 10.1145/1008335.1008338.
- G. Dequen and O. Dubois, ‘An Efficient Approach to Solving Random k-sat Problems’, Journal of Automated Reasoning, vol. 37, no. 4, p. 261, 2006.
- T. Al-Yahya, M. E. B. A. Menai, and H. Mathkour, ‘Boosting the Performance of CDCL-Based SAT Solvers by Exploiting Backbones and Backdoors’, Algorithms, vol. 15, no. 9, p. 302, Aug. 2022, doi: 10.3390/a15090302.
- J. Chen, X. Shen, and T. Menzies, ‘Faster SAT Solving for Software with Repeated Structures (with Case Studies on Software Test Suite Minimization)’, arXiv.org, Jan. 08, 2021. https://arxiv.org/abs/2101.02817v1 (accessed Mar. 16, 2023).
- B. Chambers, P. Manolios, and D. Vroon, ‘Faster SAT solving with better CNF generation’, in Automation & Test in Europe Conference & Exhibition 2009 Design, Apr. 2009, pp. 1590–1595. doi: 10.1109/DATE.2009.5090918.
- G. Dequen and O. Dubois, ‘kcnfs: An Efficient Solver for Random k-SAT Formulae’, in Theory and Applications of Satisfiability Testing, vol. 2919, E. Giunchiglia and A. Tacchella, Eds. Berlin, Heidelberg: Springer Berlin Heidelberg, 2004, pp. 486–501. doi: 10.1007/978-3-540-24605-3_36.
- C. Cameron et al., ‘Monte Carlo Forest Search: UNSAT Solver Synthesis via Reinforcement learning’, arXiv.org, Nov. 22, 2022. https://arxiv.org/abs/2211.12581v1 (accessed Mar. 16, 2023).
- P. Liberatore, ‘On the complexity of choosing the branching literal in DPLL’, Artificial Intelligence, vol. 116, no. 1–2, pp. 315–326, Jan. 2000, doi: 10.1016/S0004-3702(99)00097-1.
- K. Claessen, N. Een, M. Sheeran, N. Sörensson, A. Voronov, and K. Åkesson, ‘SAT-Solving in Practice, with a Tutorial Example from Supervisory Control’, Discrete Event Dyn Syst, vol. 19, no. 4, pp. 495–524, Dec. 2009, doi: 10.1007/s10626-009-0081-8.
- J. E. Reeves and M. J. H. Heule, ‘The Impact of Bounded Variable Elimination on Solving Pigeonhole Formulas’.
- J. Lonlac and E. M. Nguifo, ‘Towards Learned Clauses Database Reduction Strategies Based on Dominance Relationship’.
- O. Tveretina and H. Zantema, ‘Transforming DPLL to Resolution’.
- Y. Wang, D. Ouyang, and L. Zhang, ‘Variable quality checking for backbone computation’, Electronics Letters, vol. 52, no. 21, pp. 1769–1771, 2016, doi: 10.1049/el.2016.1243.
- B. Ferris and J. Froehlich, ‘WalkSAT as an Informed Heuristic to DPLL in SAT Solving’.
"""


class SAT(Exception):
    """
    Used to bubble up the recursion stack without internal checks at each level.
    """
    pass


class UNSAT(Exception):
    """
    Used to bubble up the recursion stack without internal checks at each level.
    """
    pass


def learn_from_conflict(data, objects_and_functions, conflict) -> None:
    if data[1] == 0: # if the depth of the conflict is at 0 we have a conflict without branching hence UNSAT
        raise UNSAT

    c_abs = abs # caching builtin functions into local scope significantly speeds up python
    c_len = len
    assignment_order            = objects_and_functions[1]  # the assignement_order list
    learned_lits_add            = objects_and_functions[7]  # add a literal to the learned_lits set
    assignment_order_appendleft = objects_and_functions[11] # appendleft on the assignment_order deque
    assignment_set              = objects_and_functions[16] # set the value of an assignment
    antecedent_get              = objects_and_functions[17] # get the antecedent clause
    decision_depth_get          = objects_and_functions[19] # get the decision_depth
    watched_in_get              = objects_and_functions[8] # get the deque of clauses watching a var


    def partitioning_function(accumulator: Tuple[Set[int], Set[int], Set[int]], next_val: int):
        """
        Partition the variables in the conflicting clause into two sets, and keep track of all of them in
        a third.

        inspired by https://stackoverflow.com/a/4579086
        """
        if decision_depth_get(c_abs(next_val)) == data[1]: # if it was decided on this decision level add its complement to vars_to_analize
            accumulator[1].add(-next_val)
        else: # if it was decided earlier add it to the learned_clause
            accumulator[0].add(next_val)
        accumulator[2].add(c_abs(next_val)) # remember all the variables we look at, parity independent
        return accumulator

    vars_to_analize: Set[int]
    learned_clause, vars_to_analize, vars_analized = reduce(
        partitioning_function,
        chain([conflict[0]], conflict[2]),
        (set(), set(), set())
    )

    reversed_assignment_order = reversed(assignment_order) # go backwards through the assignment order

    learned_clause_add = learned_clause.add # cache the method
    while vars_to_analize: # as long as there are variables to analize
        var = next(reversed_assignment_order) # iterate backwards through our assignments
        if var not in vars_to_analize: # if it's not a variable we need to analize continue
            continue
        vars_to_analize.remove(var) # we're analizing it so we won't need to in the future

        if c_len(vars_to_analize) == 0: # No other vars to analyse => 1st unique implication point
            learned_clause_add(-var) # Learn -var
            break # end learning

        ante_of_var = antecedent_get(c_abs(var)) # Get its antecedent

        if ante_of_var == None: # If it's a decided variable
            learned_clause_add(-var) # Learn its complement
            continue

        # For each variable in the antecedent clause
        for ante_var in chain([ante_of_var[0]], ante_of_var[2]):
            if ante_var == var: # Don't learn the var we're anteceding
                continue
            elif decision_depth_get(c_abs(ante_var)) == data[1]: # If it was not decided at an earlier time
                if c_abs(ante_var) not in vars_analized: # And we're not already analysing it
                    vars_to_analize.add(-ante_var) # Analyse it
            else:
                learned_clause_add(ante_var) # Learn the antecedent's variable (not -var because it was already false)
            vars_analized.add(c_abs(ante_var))

    learned_clause = list(learned_clause)


    if c_len(learned_clause) == 0: # if the learned clause is empty we've deduced a contradiction
        raise UNSAT
    elif c_len(learned_clause) == 1: # if we learn a unit clause
        lit = learned_clause[0]
        assignment_set(lit, True) # assign it
        assignment_order_appendleft(lit)

        data[0] = 0 # restart the restart counter
        data[1] = -1 # restart our recursion

        learned_lits_add(lit)



        return
    
    learned_clause_c = [learned_clause[0], 0, learned_clause[1:]] # create the learned clause
    watched_in_get(learned_clause_c[0])[1](learned_clause_c) # and place it in the watched_in queue
    watched_in_get(learned_clause_c[2][learned_clause_c[1]])[1](learned_clause_c)

    if data[0] > 5: # restart after 5 conflicts
        data[0] = 0
        data[1] = -1
    else:
        # backtrack to the 2nd lowest decision level covered
        data[1] = sorted(map(decision_depth_get, map(c_abs, learned_clause)))[1]
        data[0] += 1


def unbranch(depth: int, data, objects_and_functions):
    if depth < data[1]: # if we're not backtracking from learn_from_conflict we backtrack by one here
        data[1] -= 1
    objects_and_functions[4]() # clear the unit_queue
    c_abs = abs # cache function
    assignment_order_not_empty  = objects_and_functions[12]
    assignment_order_get        = objects_and_functions[13]
    assignment_order_pop        = objects_and_functions[14]
    set_assignment              = objects_and_functions[16]
    set_antecedent              = objects_and_functions[18]
    get_decision_depth          = objects_and_functions[19]
    while assignment_order_not_empty():
        if data[1] != 0 and get_decision_depth(c_abs(assignment_order_get(-1))) <= data[1]:
            break

        last_decision_var = assignment_order_pop()
        set_assignment(last_decision_var, False)
        set_antecedent(c_abs(last_decision_var), None)
    

def internal_dpll_sat_solve(depth: int, data, objects_and_functions) -> None:
    c_len = len
    c_abs = abs
    learned_lits                = objects_and_functions[0]
    unit_queue_append           = objects_and_functions[3]
    unit_queue_popleft          = objects_and_functions[5]
    unit_queue_not_empty        = objects_and_functions[6]
    learned_lits_add            = objects_and_functions[7]
    assignment_order_append     = objects_and_functions[9]
    assignment_get              = objects_and_functions[15]
    assignment_set              = objects_and_functions[16]
    antecedent_set              = objects_and_functions[18]
    decision_depth_set          = objects_and_functions[20]
    watched_in_get              = objects_and_functions[8]


    # Assign all unit literals that we already know
    for lit in filter(lambda v: v not in objects_and_functions[1], learned_lits):
        unit_queue_append((lit, None)) # Has no antecedent, is implied without branching
    
    while unit_queue_not_empty(): # Unit propagate
        unit, clause = unit_queue_popleft()
        if assignment_get(unit): # already assigned, ignore
            continue
        elif assignment_get(-unit): # already assigned complement, conflict
            learn_from_conflict(data, objects_and_functions, clause)
            return
        if clause != None: # remember the clause that implied it (implication graph)
            antecedent_set(c_abs(unit), clause)


        # assign the unit at this depth
        assignment_set(unit, True)
        assignment_order_append(unit)
        decision_depth_set(c_abs(unit), data[1])

        neg_watched_in = watched_in_get(-unit) # cache pointer to this variable's watched_in pointer

        for _ in range(neg_watched_in[2]()): # for all the original watched_in clauses
            clause = neg_watched_in[0]() # pop first clause

            if clause[2][clause[1]] != -unit: # make sure that the changing pointer (watch_two) is the one we're assigning
                clause[0], clause[2][clause[1]] = clause[2][clause[1]], clause[0]
                

            if assignment_get(clause[0]): # already SAT
                neg_watched_in[1](clause)
                continue
            
            clause_len = c_len(clause[2])
            for idx in range(clause[1] + 1, clause[1] + clause_len): # iterate through other literals
                idx = idx % clause_len # circular buffer
                if not assignment_get(-clause[2][idx]): # if it's not False watch it
                    clause[1] = idx
                    watched_in_get(clause[2][idx])[1](clause)
                    break
            else:
                neg_watched_in[1](clause) # re append it to this watch queue
                if assignment_get(-clause[0]): # and watch_one is already false UNSAT
                    learn_from_conflict(data, objects_and_functions, clause)
                    return
                unit_queue_append((clause[0], clause)) # or append new unit


        if data[1] == 0: # any units learned at depth 0 will always be units, even on restart
            learned_lits_add(unit)




    if c_len(objects_and_functions[1]) == objects_and_functions[10]: # if all variables assigned successfully SAT
        raise SAT
    for var in objects_and_functions[2]: # for all variables, in frequency order
        if not assignment_get(var) and not assignment_get(-var): # not yet assigned
            var = var if bool(getrandbits(1)) else -var # randomise its parity
            break
    else: # they've all been assigned successfully
        raise SAT



    data[1] += 1 # increase depth
    unit_queue_append((var, None)) # assign variable
    internal_dpll_sat_solve(depth + 1, data, objects_and_functions) # recurse
    unbranch(depth, data, objects_and_functions) # reverse the branching process
    if depth > data[1]: # if we're exiting early leave now
        return


    # same again for -var
    data[1] += 1
    unit_queue_append((-var, None))
    internal_dpll_sat_solve(depth + 1, data, objects_and_functions)
    unbranch(depth, data, objects_and_functions)


def dpll_sat_solve(original_clauses: List[List[int]], partial_assignment: List[int]) -> Optional[List[int]]:
    variable_frequencies = Counter(map(abs, chain.from_iterable(original_clauses)))
    biggest_variable: int = max(variable_frequencies)
    parity_sensitive_list_len = (biggest_variable * 2) + 1
    parity_insensitive_list_len = biggest_variable + 1

    unit_queue: Deque[int] = deque()
    assignment = [False for _ in range(parity_sensitive_list_len)]
    antecedent = [None for _ in range(parity_insensitive_list_len)]
    decision_depth = [-1 for _ in range(parity_insensitive_list_len)]
    watched_in = list(map( # watched_in_fncalls -> (popleft, append, len)
            lambda dq: (dq.popleft, dq.append, dq.__len__),
            (deque() for _ in range(parity_sensitive_list_len))))
    learned_lits: Set[int] = set()
    assignment_order: Deque[int] = deque()

    data = [0, 0] # how many conflicst since last restart and dpll depth
    objects_and_functions = (
        learned_lits,                   #  0 -> set of all literals that we know the parity of for sure
        assignment_order,               #  1 -> deque of variables assigned, in order
        sorted(
            list(variable_frequencies.keys()), # sort variables
            key=lambda x: (variable_frequencies[x], x), # by frequency
            reverse=True # most frequent first
        ),                              #  2 -> list of variables sorted by initial frequency
        unit_queue.append,              #  3 -> unit_queue.append
        unit_queue.clear,               #  4 -> unit_queue.clear
        unit_queue.popleft,             #  5 -> unit_queue.popleft
        unit_queue.__bool__,            #  6 -> unit_queue__bool__
        learned_lits.add,               #  7 -> learned_lits.add
        watched_in.__getitem__,         #  8 -> watched_in.__getitem__
        assignment_order.append,        #  9 -> assignment_order.append
        biggest_variable,               # 10 -> the total number of variables
        assignment_order.appendleft,    # 11 -> assignment_order.appendleft
        assignment_order.__bool__,      # 12 -> assignment_order.__bool__
        assignment_order.__getitem__,   # 13 -> assignment_order.__getitem__
        assignment_order.pop,           # 14 -> assignment_order.pop
        assignment.__getitem__,         # 15 -> assignment.__getitem__
        assignment.__setitem__,         # 16 -> assignment.__setitem__
        antecedent.__getitem__,         # 17 -> antecedent.__getitem__
        antecedent.__setitem__,         # 18 -> antecedent.__setitem__
        decision_depth.__getitem__,     # 19 -> decision_depth.__getitem__
        decision_depth.__setitem__,     # 20 -> decision_depth.__setitem__
    )

    c_set = set
    c_len = len

    learned_lits_add = objects_and_functions[7]
    watched_in_get = objects_and_functions[8]

    for og_clause in original_clauses:
        s_clause = c_set(og_clause)
        for var in s_clause:
            if -var in s_clause:
                continue
        if c_len(og_clause) > 1: # transform all non-unit clauses and watch them
            clause = [og_clause[0], 0, array('i', og_clause[1:])]
            # don't need to set watches because all are sat to begin with.
            # also means watches are indices 0 and 1
            watched_in_get(og_clause[0])[1](clause)
            watched_in_get(og_clause[1])[1](clause)
        elif c_len(og_clause) == 1: # initially unit clauses
            learned_lits_add(og_clause[0])
        else:
            return None



    while True:
        data[1] = 0
        try:
            internal_dpll_sat_solve(0, data, objects_and_functions)
        except SAT:
            return list(objects_and_functions[1])
        except UNSAT:
            return None
