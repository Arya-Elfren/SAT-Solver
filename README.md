# SAT-Solver

This is a severly extended version (we were only tasked with DPLL, not CDCL or
2-watched literals) of a first year coursework. `Sat.py` runs some tests
against the instances in `./tests/`, `wvdg57.py` has my implementation, it
includes some simpler tasks, but the CDCL is the last part. Below I have
extracted my comment explaining what I did.

*During development I had a more readable version that I can't find anymore*

Highlighted resource:

> First, I found [0] when searching for efficient unit propagation strategies and
> that led me to two watched literals [2][3]. I read and implemented the circular
> approach described in [4]. All my other knowledge comes from the extremely
> extensive and useful [1]. Chapters 3 and 4 are really good resources, I
> recommend them to anyone interested in SAT-solving.

# Explanation

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

The other idea is that, during unit-propagation we remember which clause implied
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
with [5]). I tried implementing Bounded Variable Elimination but either my
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
- [0] Stack exchange answer that links to the relevant theory: https://cs.stackexchange.com/questions/150557/what-are-efficient-approaches-to-implement-unit-propagation-in-dpll-based-sat-so
- [1] A. Biere, M. Heule, and H. van Maaren, Eds., Handbook of satisfiability, Second edition. Amsterdam ; Washington, DC: IOS Press, 2021.
- [2] H. Zhang and M. Stickel, ‘An Efficient Algorithm for Unit Propagation’, Jan. 1996.
- [3] M. Iser and T. Balyo, ‘Unit Propagation with Stable Watches’, 2021.
- [4] I. P. Gent, ‘Optimal Implementation of Watched Literals and More General Techniques’, Journal of Artificial Intelligence Research, vol. 48, pp. 231–252, Oct. 2013, doi: 10.1613/jair.4016.
- [5] ‘Hard formula generator (pysat.examples.genhard) — PySAT 0.1.8.dev1 documentation’. https://pysathq.github.io/docs/html/api/examples/genhard.html (accessed Mar. 16, 2023).
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
