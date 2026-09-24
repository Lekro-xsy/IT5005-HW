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
    peers = {}
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            p = set()
            for x in range(1, n + 1):
                if x != c:
                    p.add((r, x))
                if x != r:
                    p.add((x, c))
            br = ((r - 1) // box_h) * box_h + 1
            bc = ((c - 1) // box_w) * box_w + 1
            for rr in range(br, br + box_h):
                for cc in range(bc, bc + box_w):
                    if (rr, cc) != (r, c):
                        p.add((rr, cc))
            peers[(r, c)] = p

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            values = [atom('Is', r, c, v) for v in range(1, n + 1)]
            kb.tell(associate('|', values))
            for i in range(n):
                for j in range(i + 1, n):
                    kb.tell(~values[i] | ~values[j])

    for (r, c), cell_peers in peers.items():
        for r2, c2 in cell_peers:
            if (r, c) >= (r2, c2):
                continue
            for v in range(1, n + 1):
                kb.tell(
                    ~atom('Is', r, c, v)
                    | ~atom('Is', r2, c2, v)
                )

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
    peers = {}
    for r in range(1, n + 1):
        for c in range(1, n + 1):
            p = set()
            for x in range(1, n + 1):
                if x != c:
                    p.add((r, x))
                if x != r:
                    p.add((x, c))
            br = ((r - 1) // box_h) * box_h + 1
            bc = ((c - 1) // box_w) * box_w + 1
            for rr in range(br, br + box_h):
                for cc in range(bc, bc + box_w):
                    if (rr, cc) != (r, c):
                        p.add((rr, cc))
            peers[(r, c)] = p

    for (r, c), v in givens.items():
        kb.tell(atom('Is', r, c, v))

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            for v in range(1, n + 1):
                is_value = atom('Is', r, c, v)

                for v2 in range(1, n + 1):
                    if v2 != v:
                        kb.tell(
                            Expr(
                                '==>',
                                is_value,
                                atom('Not', r, c, v2),
                            )
                        )

                for r2, c2 in peers[(r, c)]:
                    kb.tell(
                        Expr(
                            '==>',
                            is_value,
                            atom('Not', r2, c2, v),
                        )
                    )

                eliminated = [
                    atom('Not', r, c, v2)
                    for v2 in range(1, n + 1)
                    if v2 != v
                ]
                if eliminated:
                    kb.tell(
                        Expr(
                            '==>',
                            associate('&', eliminated),
                            is_value,
                        )
                    )
                else:
                    kb.tell(is_value)

    premise_index = {}
    for clause in kb.clauses:
        if clause.op == '==>':
            premises, _ = parse_definite_clause(clause)
            for premise in premises:
                premise_index.setdefault(premise, []).append(clause)
    kb._clauses_by_premise = premise_index
    kb.clauses_with_premise = (
        lambda premise, index=premise_index: index.get(premise, ())
    )

    return kb


def solve_full_grid_fc(n, box_h, box_w, givens):
    """Solve the whole puzzle using build_definite_kb + pl_fc_entails.

    Returns
    -------
    dict[(int, int), int] -- {(row, col): value} for every cell
    """
    kb = build_definite_kb(n, box_h, box_w, givens)
    solved = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in givens:
                solved[(r, c)] = givens[(r, c)]
                continue

            for value in range(1, n + 1):
                if pl_fc_entails(kb, atom('Is', r, c, value)):
                    solved[(r, c)] = value
                    break
            else:
                raise ValueError(
                    f'forward chaining could not solve cell ({r}, {c})'
                )

    return solved


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
    clause_count = len(kb.clauses)
    if getattr(kb, '_bc_index_clause_count', None) != clause_count:
        facts = set()
        rules_by_conclusion = {}
        for clause in kb.clauses:
            match clause.op:
                case '==>':
                    premises, conclusion = parse_definite_clause(clause)
                    rules_by_conclusion.setdefault(conclusion, []).append(
                        (tuple(premises), clause)
                    )
                case _:
                    facts.add(clause)
        kb._bc_facts = facts
        kb._bc_rules_by_conclusion = rules_by_conclusion
        kb._bc_index_clause_count = clause_count
        kb._bc_proven = set(facts)
        kb._bc_proof = {}

    facts = kb._bc_facts
    rules_by_conclusion = kb._bc_rules_by_conclusion
    known = kb._bc_proven
    proof = kb._bc_proof

    relevant_goals = set()
    relevant_rules = []

    pending = [query]
    while pending:
        goal = pending.pop()
        if goal in relevant_goals:
            continue
        relevant_goals.add(goal)
        if goal in known:
            continue
        for premises, clause in rules_by_conclusion.get(goal, ()):
            relevant_rules.append((premises, goal, clause))
            for premise in premises:
                if premise not in relevant_goals:
                    pending.append(premise)

    entailed_goals = {goal for goal in relevant_goals if goal in known}
    agenda = list(entailed_goals)
    remaining = {}
    rules_with_premise = {}

    for rule_id, (premises, _, _) in enumerate(relevant_rules):
        missing = [premise for premise in premises if premise not in entailed_goals]
        remaining[rule_id] = len(missing)
        for premise in missing:
            rules_with_premise.setdefault(premise, []).append(rule_id)

    for rule_id, count in remaining.items():
        if count != 0:
            continue
        premises, conclusion, clause = relevant_rules[rule_id]
        if conclusion not in entailed_goals:
            entailed_goals.add(conclusion)
            agenda.append(conclusion)
            proof[conclusion] = (premises, clause)

    while agenda:
        established = agenda.pop()
        for rule_id in rules_with_premise.get(established, ()):
            if remaining[rule_id] == 0:
                continue
            remaining[rule_id] -= 1
            if remaining[rule_id] == 0:
                premises, conclusion, clause = relevant_rules[rule_id]
                if conclusion not in entailed_goals:
                    entailed_goals.add(conclusion)
                    agenda.append(conclusion)
                    proof[conclusion] = (premises, clause)

    known.update(entailed_goals)
    entailed = query in entailed_goals

    return entailed


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
    solved = {}

    for r in range(1, n + 1):
        for c in range(1, n + 1):
            if (r, c) in givens:
                solved[(r, c)] = givens[(r, c)]
                continue

            for value in range(1, n + 1):
                if pl_bc_entails(kb, atom('Is', r, c, value)):
                    solved[(r, c)] = value
                    break
            else:
                raise ValueError(
                    f'backward chaining could not solve cell ({r}, {c})'
                )

    return solved
