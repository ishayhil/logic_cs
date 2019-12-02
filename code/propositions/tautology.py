# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/tautology.py

"""The Tautology Theorem and its implications."""

from typing import List, Union

from logic_utils import frozendict

from propositions.syntax import *
from propositions.proofs import *
from propositions.deduction import *
from propositions.semantics import *
from propositions.operators import *
from propositions.axiomatic_systems import *
import functools


def formulae_capturing_model(model: Model) -> List[Formula]:
    """Computes the formulae that capture the given model: ``'``\ `x`\ ``'``
    for each variable `x` that is assigned the value ``True`` in the given
    model, and ``'~``\ `x`\ ``'`` for each variable x that is assigned the value
    ``False``.

    Parameters:
        model: model to construct the formulae for.

    Returns:
        A list of the constructed formulae, ordered alphabetically by variable
        name.

    Examples:
        >>> formulae_capturing_model({'p2': False, 'p1': True, 'q': True})
        [p1, ~p2, q]
    """
    assert is_model(model)
    return [Formula(var) if b else Formula.parse(f'~{var}') for var, b in sorted(model.items(), key=lambda x: repr(x))]


def prove_in_model(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert formula.operators().issubset({'->', '~'})
    assert is_model(model)

    assignments = formulae_capturing_model(model)
    return prove_in_model_helper(formula, model, assignments)


def prove_in_model_helper(formula: Formula, model: Model, assignments) -> Proof:
    if is_variable(formula.root):
        if not model[formula.root]:
            formula = Formula('~', formula)
        return Proof(InferenceRule(assignments, formula), AXIOMATIC_SYSTEM, [Proof.Line(formula)])
    elif is_binary(formula.root):
        if not evaluate(formula, model):  # p true, q false
            proof1 = prove_in_model_helper(formula.first, model, assignments)
            proof2 = prove_in_model_helper(Formula('~', formula.second), model, assignments)
            return combine_proofs(proof1, proof2, Formula('~', formula), NI)
        else:
            if not evaluate(formula.first, model):
                proof1 = prove_in_model_helper(Formula('~', formula.first), model, assignments)
                return prove_corollary(proof1, formula, I2)
            else:
                proof2 = prove_in_model_helper(formula.second, model, assignments)
                return prove_corollary(proof2, formula, I1)
    else:  # ~p
        proof1 = prove_in_model_helper(formula.first, model, assignments)
        if evaluate(formula, model):
            return proof1
        else:
            return prove_corollary(proof1, Formula('~', formula), NN)


def reduce_assumption(proof_from_affirmation: Proof,
                      proof_from_negation: Proof) -> Proof:
    """Combines the given two proofs, both of the same formula `conclusion` and
    from the same assumptions except that the last assumption of the latter is
    the negation of that of the former, into a single proof of `conclusion` from
    only the common assumptions.

    Parameters:
        proof_from_affirmation: valid proof of `conclusion` from one or more
            assumptions, the last of which is an assumption `assumption`.
        proof_of_negation: valid proof of `conclusion` from the same assumptions
            and inference rules of `proof_from_affirmation`, but with the last
            assumption being ``'~``\ `assumption` ``'`` instead of `assumption`.

    Returns:
        A valid proof of `conclusion` from only the assumptions common to the
        given proofs (i.e., without the last assumption of each), via the same
        inference rules of the given proofs and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.R`.

    Examples:
        If the two given proofs are of ``['p', 'q'] ==> '(q->p)'`` and of
        ``['p', '~q'] ==> ('q'->'p')``, then the returned proof is of
        ``['p'] ==> '(q->p)'``.
    """
    assert proof_from_affirmation.is_valid()
    assert proof_from_negation.is_valid()
    assert proof_from_affirmation.statement.conclusion == \
           proof_from_negation.statement.conclusion
    assert len(proof_from_affirmation.statement.assumptions) > 0
    assert len(proof_from_negation.statement.assumptions) > 0
    assert proof_from_affirmation.statement.assumptions[:-1] == \
           proof_from_negation.statement.assumptions[:-1]
    assert Formula('~', proof_from_affirmation.statement.assumptions[-1]) == \
           proof_from_negation.statement.assumptions[-1]
    assert proof_from_affirmation.rules == proof_from_negation.rules

    proof1 = remove_assumption(proof_from_affirmation)
    proof2 = remove_assumption(proof_from_negation)
    return combine_proofs(proof1, proof2, proof_from_negation.statement.conclusion, R)


def prove_tautology(tautology: Formula, model: Model = frozendict()) -> Proof:
    """Proves the given tautology from the formulae that capture the given
    model.

    Parameters:
        tautology: tautology that contains no constants or operators beyond
            ``'->'`` and ``'~'``, to prove.
        model: model over a (possibly empty) prefix (with respect to the
            alphabetical order) of the variables of `tautology`, from whose
            formulae to prove.

    Returns:
        A valid proof of the given tautology from the formulae that capture the
        given model, in the order returned by
        `formulae_capturing_model`\ ``(``\ `model`\ ``)``, via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.

    Examples:
        If the given model is the empty dictionary, then the returned proof is
        of the given tautology from no assumptions.
    """
    assert is_tautology(tautology)
    assert tautology.operators().issubset({'->', '~'})
    assert is_model(model)
    assert sorted(tautology.variables())[:len(model)] == sorted(model.keys())

    v = sorted(tautology.variables())
    t_model, f_model = dict(model), dict(model)
    if len(v) == len(model):
        return prove_in_model(tautology, model)
    else:
        for var in v:
            if var not in model:
                f_model[var] = False
                t_model[var] = True
                break
        return reduce_assumption(prove_tautology(tautology, t_model), prove_tautology(tautology, f_model))


def proof_or_counterexample(formula: Formula) -> Union[Proof, Model]:
    """Either proves the given formula or finds a model in which it does not
    hold.

    Parameters:
        formula: formula that contains no constants or operators beyond ``'->'``
            and ``'~'``, to either prove or find a counterexample for.

    Returns:
        If the given formula is a tautology, then an assumptionless proof of the
        formula via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`,
        otherwise a model in which the given formula does not hold.
    """
    assert formula.operators().issubset({'->', '~'})

    for model in all_models(list(formula.variables())):
        if not evaluate(formula, model):
            return model
    return prove_tautology(formula)


def encode_as_formula(rule: InferenceRule) -> Formula:
    """Encodes the given inference rule as a formula consisting of a chain of
    implications.

    Parameters:
        rule: inference rule to encode.

    Returns:
        The formula encoding the given rule.

    Examples:
        >>> encode_as_formula(InferenceRule([Formula('p1'), Formula('p2'),
        ...                                  Formula('p3'), Formula('p4')],
        ...                                 Formula('q')))
        (p1->(p2->(p3->(p4->q))))
        >>> encode_as_formula(InferenceRule([], Formula('q')))
        q
    """
    return encode_as_formula_recursive(rule, 0)


def encode_as_formula_recursive(rule: InferenceRule, ind):
    if ind == len(rule.assumptions):
        return rule.conclusion
    return Formula('->', rule.assumptions[ind], encode_as_formula_recursive(rule, ind + 1))


def prove_sound_inference(rule: InferenceRule) -> Proof:
    """Proves the given sound inference rule.

    Parameters:
        rule: sound inference rule whose assumptions and conclusion that contain
            no constants or operators beyond ``'->'`` and ``'~'``, to prove.

    Returns:
        A valid assumptionless proof of the given sound inference rule via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    assert is_sound_inference(rule)
    for formula in rule.assumptions + (rule.conclusion,):
        assert formula.operators().issubset({'->', '~'})

    proof1 = prove_tautology(encode_as_formula(rule))
    proof_head_lines = [
        *[Proof.Line(f) for f in rule.assumptions],
        *[Proof.Line(line.formula, line.rule,
                     [n + len(rule.assumptions) for n in line.assumptions] if not line.is_assumption() else None) for
          line in proof1.lines],
    ]

    new_tail_lines = []
    for i in range(len(rule.assumptions)):
        if i == 0:
            line = Proof.Line(proof_head_lines[-1].formula.second, MP, [0, len(proof_head_lines) - 1])
        else:
            line = Proof.Line(new_tail_lines[-1].formula.second, MP,
                              [i, len(proof_head_lines) + len(new_tail_lines) - 1])
        new_tail_lines.append(line)

    return Proof(rule, AXIOMATIC_SYSTEM, [*proof_head_lines, *new_tail_lines])


def model_or_inconsistency(formulas: List[Formula]) -> Union[Model, Proof]:
    """Either finds a model in which all the given formulae hold, or proves
    ``'~(p->p)'`` from these formula.

    Parameters:
        formulas: formulae that use only the operators ``'->'`` and ``'~'``, to
            either find a model for or prove ``'~(p->p)'`` from.

    Returns:
        A model in which all of the given formulae hold if such exists,
        otherwise a proof of '~(p->p)' from the given formulae via
        `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM`.
    """
    for formula in formulas:
        assert formula.operators().issubset({'->', '~'})

    all_vars = []
    for f in formulas:
        all_vars.extend(list(f.variables()))

    for model in all_models(list(all_vars)):
        if all(evaluate(formula, model) if formula.variables().issubset(model) else False for formula in formulas):
            return model

    # if formulas are inconsistent, then then we can prove anything from them, so ~(p->p) is sound.
    return prove_sound_inference(InferenceRule([f for f in formulas], Formula.parse('~(p->p)')))


def prove_in_model_full(formula: Formula, model: Model) -> Proof:
    """Either proves the given formula or proves its negation, from the formulae
    that capture the given model.

    Parameters:
        formula: formula that contains no operators beyond ``'->'``, ``'~'``,
            ``'&'``, and ``'|'``, whose affirmation or negation is to prove.
        model: model from whose formulae to prove.

    Returns:
        If the given formula evaluates to ``True`` in the given model, then
        a proof of the formula, otherwise a proof of ``'~``\ `formula`\ ``'``.
        The returned proof is from the formulae that capture the given model, in
        the order returned by `formulae_capturing_model`\ ``(``\ `model`\ ``)``,
        via `~propositions.axiomatic_systems.AXIOMATIC_SYSTEM_FULL`.
    """
    assert formula.operators().issubset({'T', 'F', '->', '~', '&', '|'})
    assert is_model(model)
    # Optional Task 6.6
