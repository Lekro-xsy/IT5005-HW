"""IT5005 Assignment 1: student implementation file.

Implement the functions marked below. Do not modify utils.py or logic_.py.
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB encoding this n x n Sudoku's constraints plus the given
    cells, as general clauses.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int]

    Returns
    -------
    PropKB
    """
    kb = PropKB()

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            choices = []
            for v in range(1, n + 1):
                choices.append(atom('Is', r, c, v))
            kb.tell(associate('|', choices))

            for v1 in range(1, n + 1):
                for v2 in range(v1 + 1, n + 1):
                    kb.tell(~atom('Is', r, c, v1) | ~atom('Is', r, c, v2))

    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n + 1):
                for c2 in range(c1 + 1, n + 1):
                    kb.tell(~atom('Is', r, c1, v) | ~atom('Is', r, c2, v))

    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n + 1):
                for r2 in range(r1 + 1, n + 1):
                    kb.tell(~atom('Is', r1, c, v) | ~atom('Is', r2, c, v))

    for first_r in range(1, n + 1, box_h):
        for first_c in range(1, n + 1, box_w):
            cells = []
            for r in range(first_r, first_r + box_h):
                for c in range(first_c, first_c + box_w):
                    cells.append((r, c))
            for v in range(1, n + 1):
                for i in range(len(cells)):
                    for j in range(i + 1, len(cells)):
                        r1, c1 = cells[i]
                        r2, c2 = cells[j]
                        kb.tell(~atom('Is', r1, c1, v) | ~atom('Is', r2, c2, v))

    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    return kb


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB encoding this n x n Sudoku's constraints plus
    the given cells, using elimination + last-candidate reasoning.

    Parameters
    ----------
    n, box_h, box_w : int
    givens : dict[(int, int), int] -- {(row, col): value}, 1-indexed

    Returns
    -------
    PropDefiniteKB
    """
    kb = PropDefiniteKB()

    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                for other in range(1, n + 1):
                    if other != v:
                        kb.tell(Expr('==>', atom('Is', r, c, v),
                                     atom('Not', r, c, other)))

    for r in range(1, n + 1):
        for v in range(1, n + 1):
            for c1 in range(1, n + 1):
                for c2 in range(1, n + 1):
                    if c1 != c2:
                        kb.tell(Expr('==>', atom('Is', r, c1, v),
                                     atom('Not', r, c2, v)))

    for c in range(1, n + 1):
        for v in range(1, n + 1):
            for r1 in range(1, n + 1):
                for r2 in range(1, n + 1):
                    if r1 != r2:
                        kb.tell(Expr('==>', atom('Is', r1, c, v),
                                     atom('Not', r2, c, v)))

    for first_r in range(1, n + 1, box_h):
        for first_c in range(1, n + 1, box_w):
            cells = []
            for r in range(first_r, first_r + box_h):
                for c in range(first_c, first_c + box_w):
                    cells.append((r, c))
            for v in range(1, n + 1):
                for r1, c1 in cells:
                    for r2, c2 in cells:
                        if (r1, c1) != (r2, c2):
                            kb.tell(Expr('==>', atom('Is', r1, c1, v),
                                         atom('Not', r2, c2, v)))

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                other_values = []
                for other in range(1, n + 1):
                    if other != v:
                        other_values.append(atom('Not', r, c, other))
                kb.tell(Expr('==>', associate('&', other_values),
                             atom('Is', r, c, v)))

    return kb


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    answer = {}

    lookup = {}
    for clause in kb.clauses:
        if clause.op == '==>':
            premises, conclusion = parse_definite_clause(clause)
            for premise in premises:
                if premise not in lookup:
                    lookup[premise] = []
                lookup[premise].append(clause)

    def find_rules(premise):
        return lookup.get(premise, [])

    kb.clauses_with_premise = find_rules

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in givens:
                answer[(r, c)] = givens[(r, c)]
                continue
            for v in range(1, n + 1):
                if pl_fc_entails(kb, atom('Is', r, c, v)):
                    answer[(r, c)] = v
                    break
            if (r, c) not in answer:
                raise ValueError('Could not solve cell ' + str((r, c)))

    return answer


def pl_bc_entails(kb, query):
    """Your own backward-chaining implementation.

    Parameters
    ----------
    kb : PropDefiniteKB
    query : Expr

    Returns
    -------
    bool
    """
    if not hasattr(kb, '_bc_rules'):
        facts = set()
        rules = {}

        for clause in kb.clauses:
            match clause.op:
                case '==>':
                    premises, conclusion = parse_definite_clause(clause)
                    if conclusion not in rules:
                        rules[conclusion] = []
                    rules[conclusion].append((premises, clause))
                case _:
                    facts.add(clause)

        kb._bc_rules = rules
        kb._bc_facts = facts
        kb._bc_known = set(facts)
        kb._bc_proof = {}

    goals = set()
    useful_rules = []
    todo = [query]

    while todo:
        goal = todo.pop()
        if goal in goals:
            continue
        goals.add(goal)

        for premises, clause in kb._bc_rules.get(goal, []):
            useful_rules.append((premises, goal, clause))
            for premise in premises:
                if premise not in goals:
                    todo.append(premise)

    changed = True
    while changed and query not in kb._bc_known:
        changed = False
        for premises, conclusion, clause in useful_rules:
            if conclusion in kb._bc_known:
                continue

            proved = True
            for premise in premises:
                if premise not in kb._bc_known:
                    proved = False
                    break

            if proved:
                kb._bc_known.add(conclusion)
                kb._bc_proof[conclusion] = (premises, clause)
                changed = True

    return query in kb._bc_known


def solve_full_grid_bc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + your own pl_bc_entails.

    For each cell, try each candidate value until pl_bc_entails confirms one
    -- the same per-cell strategy as solve_full_grid_fc, but backed by
    backward chaining instead of a single shared forward-chaining pass.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    answer = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in givens:
                answer[(r, c)] = givens[(r, c)]
                continue
            for v in range(1, n + 1):
                if pl_bc_entails(kb, atom('Is', r, c, v)):
                    answer[(r, c)] = v
                    break
            if (r, c) not in answer:
                raise ValueError('Could not solve cell ' + str((r, c)))

    return answer
