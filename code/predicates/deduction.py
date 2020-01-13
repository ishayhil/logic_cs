# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/deduction.py

"""Useful proof manipulation maneuvers in predicate logic."""

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

m = {}


def remove_assumption(proof: Proof, assumption: Formula,
                      print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of some `conclusion` formula, an assumption of
    which is `assumption`, to a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Returns:
        A valid proof of ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()

    prover = Prover(proof.assumptions.difference({Schema(assumption)}), print_as_proof_forms)
    for ind, line in enumerate(proof.lines):
        if isinstance(line, Proof.AssumptionLine):
            last_step = handle_axiom(prover, ind, proof, assumption)
        elif isinstance(line, Proof.TautologyLine):
            last_step = handle_tautology(prover, ind, proof, assumption)
        elif isinstance(line, Proof.MPLine):
            last_step = handle_mp(prover, ind, proof, assumption)
        else:  # UG
            last_step = handle_ug(prover, ind, proof, assumption)
        m[ind] = last_step

    return prover.qed()


def handle_axiom(prover: Prover, line_number: int, proof: Proof, assumption: Formula) -> int:
    formula = proof.lines[line_number].formula
    mapping = proof.lines[line_number].instantiation_map
    assumption_old = proof.lines[line_number].assumption
    if formula == assumption:
        step1 = prover.add_tautology(Formula('->', assumption, assumption))
        return step1

    step1 = prover.add_instantiated_assumption(formula, assumption_old, mapping)
    step2 = prover.add_tautological_implication(Formula('->', assumption, formula), {step1})
    # step2 = prover.add_tautology(Formula('->', formula, Formula('->', assumption, formula)))
    # step3 = prover.add_mp(Formula('->', assumption, formula), step1, step2)
    return step2


def handle_tautology(prover: Prover, line_number: int, proof: Proof, assumption: Formula) -> int:
    formula = proof.lines[line_number].formula
    step1 = prover.add_tautology(formula)
    step2 = prover.add_tautology(Formula('->', assumption, formula))
    return step2


def handle_mp(prover: Prover, line_number: int, proof: Proof, assumption: Formula) -> int:
    formula = proof.lines[line_number].formula
    new_antecedent_line_num, new_conditional_line_num = find_mp_dependencies(prover, line_number, proof, assumption)
    step1 = prover.add_tautological_implication(Formula('->', assumption, formula),
                                                {new_conditional_line_num, new_antecedent_line_num})

    return step1


def find_mp_dependencies(prover: Prover, old_line_number: int, proof: Proof, assumption: Formula) -> Tuple[
    int, int]:
    new_conditional = Formula('->', assumption,
                              proof.lines[proof.lines[old_line_number].conditional_line_number].formula)
    new_antecedent = Formula('->', assumption, proof.lines[proof.lines[old_line_number].antecedent_line_number].formula)

    new_antecedent_line_num = -1
    new_conditional_line_num = -1
    for ind, line in enumerate(prover._lines):
        if repr(line.formula) == repr(new_antecedent):
            new_antecedent_line_num = ind
            break
    for ind, line in enumerate(prover._lines):
        if repr(line.formula) == repr(new_conditional):
            new_conditional_line_num = ind
            break

    assert new_antecedent_line_num > -1, f"cant find matching formula for antecedent {repr(new_antecedent)}. old line {proof.lines[old_line_number].antecedent_line_number}, new_line {m[proof.lines[old_line_number].antecedent_line_number]}"
    assert new_conditional_line_num > -1, f"cant find matching formula for conditional {repr(new_conditional)}. old line {old_line_number}"
    return new_antecedent_line_num, new_conditional_line_num


def handle_ug(prover, ind, proof, assumption) -> int:
    new_predicate_line_number = find_ug_dependency(prover, ind, proof, assumption)
    new_predicate: Formula = prover._lines[new_predicate_line_number].formula
    var = proof.lines[ind].formula.variable
    formula = Formula('A', var, new_predicate)
    step1 = prover.add_ug(formula, new_predicate_line_number)
    mapping = {
        'Q': new_predicate.first,
        'R': new_predicate.second.substitute({var: Term('_')}),
        'x': var
    }
    us = Prover.US.instantiate(mapping)
    step2 = prover.add_instantiated_assumption(us, Prover.US, mapping)
    step3 = prover.add_mp(us.second, step1, step2)
    return step3

    # todo add us here


def find_ug_dependency(prover: Prover, old_line_number: int, proof: Proof, assumption: Formula):
    new_predicate = Formula('->', assumption, proof.lines[proof.lines[old_line_number].predicate_line_number].formula)
    for ind, line in enumerate(prover._lines):
        if line.formula == new_predicate:
            return ind

    raise RuntimeError("cant get here! UG")


def proof_by_way_of_contradiction(proof: Proof, assumption: Formula,
                                  print_as_proof_forms: bool = False) -> Proof:
    """Converts the given proof of a contradiction, an assumption of which is
    `assumption`, to a proof of ``'~``\ `assumption`\ ``'`` from the same
    assumptions except `assumption`.

    Parameters:
        proof: valid proof of a contradiction (i.e., a formula whose negation is
            a tautology) to convert, from assumptions/axioms that include
            `~predicates.prover.Prover.AXIOMS`.
        assumption: formula that is a simple assumption (i.e., without any
            templates) of the given proof, such that no line of the given proof
            is a UG line over a variable that is free in this assumption.

    Return:
        A valid proof of ``'~``\ `assumption`\ ``'`` from the same
        assumptions/axioms as the given proof except `assumption`.
    """
    assert proof.is_valid()
    assert Schema(assumption) in proof.assumptions
    assert proof.assumptions.issuperset(Prover.AXIOMS)
    for line in proof.lines:
        if isinstance(line, Proof.UGLine):
            assert line.formula.variable not in assumption.free_variables()
    prover = Prover(proof.assumptions.difference({Schema(assumption)}), print_as_proof_forms)
    # prover.add_proof(proof.conclusion, proof)
    remove_asm = remove_assumption(proof, assumption, False)
    step1 = prover.add_proof(remove_asm.conclusion, remove_asm)
    step2 = prover.add_tautological_implication(Formula('~', assumption), {step1})
    return prover.qed()
