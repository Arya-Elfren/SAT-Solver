from itertools import chain
from os import listdir
import timeit

from typing import Set, List

from wvdg57 import load_dimacs, dpll_sat_solve, unit_propagate, simple_sat_solve, branching_sat_solve


def unit_propagate_check(clause_set, units):
    clause_set = [
        [var for var in clause if -var not in units]
        for clause in clause_set
        if all(var not in clause for var in units)
    ]
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


def runall():
    uf_twenty = map(lambda x: ("uf20/" + x[:-4], True), listdir("tests/uf20"))
    uf_fifty = map(lambda x: ("uf50/" + x[:-4], True), listdir("tests/uf50"))
    uuf_fifty = map(lambda x: ("uuf50/" + x[:-4], False), listdir("tests/uuf50"))
    sat_insts = [
        ("sat", True),
        ("unsat", False),
        ("8queens", True),
        ("W_2,3_ n=8", True),
        ("PHP-5-4", False), 
        ("LNP-6", False),
        ("php-k1-n5", False),
        ("par-n4", False),
        ("gt", False),  
        ("zebra", True),
    ]
    long_sat_insts = [
        ("cb", False),
        ("par", False),
        ("php-k1", False),
        #("php-k2", False),
        #("php-k3", False),
        #("php-k4", False),  
    ]
    for name, sat in chain(
        uf_twenty,
        sat_insts,
        uuf_fifty,
        uf_fifty,
        #long_sat_insts,
    ):
        sat_instance = load_dimacs(f"tests/{name}.cnf")
        print(name, end="                            ")
        sat_res = dpll_sat_solve(sat_instance, [])
        if sat:
            assert type(sat_res) == list
            assert len(unit_propagate_check(sat_instance, set(sat_res))) == 0
        else:
            assert sat_res == None, sat_res
        print("\r", end="")

for name in ["sat", "unsat"]:
    break
    sat_instance = load_dimacs(f"tests/{name}.cnf")
    print("unit_propagate", name, unit_propagate(sat_instance))
    print("simple_sat_solve", name, simple_sat_solve(sat_instance))
    print("branching_sat_solve", name, branching_sat_solve(sat_instance, []))
    print("dpll_sat_solve", name, dpll_sat_solve(sat_instance, []))

for name in ["W_2,3_ n=8"]:
    break
    sat_instance = load_dimacs(f"tests/{name}.cnf")
    print("simple_sat_solve", name, simple_sat_solve(sat_instance))
    print("branching_sat_solve", name, branching_sat_solve(sat_instance, []))
    print("dpll_sat_solve", name, dpll_sat_solve(sat_instance, []))

for name in ["8queens","PHP-5-4",  "LNP-6"]:
    break
    sat_instance = load_dimacs(f"tests/{name}.cnf")
    print("branching_sat_solve", name, branching_sat_solve(sat_instance, []))
    print("dpll_sat_solve", name, dpll_sat_solve(sat_instance, []))

runall()

