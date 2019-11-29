# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/deduction.py

"""Useful proof manipulation maneuvers in propositional logic."""

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *


def prove_corollary(antecedent_proof: Proof, consequent: Formula,
                    conditional: InferenceRule) -> Proof:
    """Converts the given proof of a formula `antecedent` into a proof of the
    given formula `consequent` by using the given assumptionless inference rule
    of which ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
    specialization.

    Parameters:
        antecedent_proof: valid proof of `antecedent`.
        consequent: formula to prove.
        conditional: assumptionless inference rule of which the assumptionless
            inference rule with conclusion
            ``'(``\ `antecedent`\ ``->``\ `consequent`\ ``)'`` is a
            specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proof, via the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent_proof.is_valid()
    assert InferenceRule([],
                         Formula('->', antecedent_proof.statement.conclusion,
                                 consequent)).is_specialization_of(conditional)

    first_map = InferenceRule.formula_specialization_map(conditional.conclusion.first,
                                                         antecedent_proof.lines[-1].formula)
    second_map = InferenceRule.formula_specialization_map(conditional.conclusion.second, consequent)
    s_map = InferenceRule.merge_specialization_maps(first_map, second_map)

    new_rules = antecedent_proof.rules.union({conditional})
    new_lines = [
        Proof.Line(conditional.conclusion.substitute_variables(s_map), rule=conditional, assumptions=[]),
        Proof.Line(consequent, rule=MP,
                   assumptions=[len(antecedent_proof.lines) - 1, len(antecedent_proof.lines)])
    ]
    statement = InferenceRule(antecedent_proof.statement.assumptions, consequent)

    return Proof(statement, new_rules, [*antecedent_proof.lines, *new_lines])


def combine_proofs(antecedent1_proof: Proof, antecedent2_proof: Proof,
                   consequent: Formula, double_conditional: InferenceRule) -> \
        Proof:
    """Combines the given proofs of two formulae `antecedent1` and `antecedent2`
    into a proof of the given formula `consequent` by using the given
    assumptionless inference rule of which
    ``('``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
    is a specialization.

    Parameters:
        antecedent1_proof: valid proof of `antecedent1`.
        antecedent2_proof: valid proof of `antecedent2` from the same
            assumptions and inference rules as `antecedent1_proof`.
        consequent: formula to prove.
        double_conditional: assumptionless inference rule of which the
            assumptionless inference rule with conclusion
            ``'(``\ `antecedent1`\ ``->(``\ `antecedent2`\ ``->``\ `consequent`\ ``))'``
            is a specialization.

    Returns:
        A valid proof of `consequent` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and `conditional`.
    """
    assert antecedent1_proof.is_valid()
    assert antecedent2_proof.is_valid()
    assert antecedent1_proof.statement.assumptions == \
           antecedent2_proof.statement.assumptions
    assert antecedent1_proof.rules == antecedent2_proof.rules
    assert InferenceRule(
        [], Formula('->', antecedent1_proof.statement.conclusion,
                    Formula('->', antecedent2_proof.statement.conclusion, consequent))
    ).is_specialization_of(double_conditional)

    # all: (a1->(a2->p))
    # proof1 proves (a2->p)
    proof1 = prove_corollary(antecedent1_proof, Formula('->', antecedent2_proof.statement.conclusion, consequent),
                             double_conditional)

    external_lines = [
        *[Proof.Line(formula=line.formula, rule=line.rule,
                     assumptions=[n + len(proof1.lines) for n in
                                  range(len(line.assumptions))] if not line.is_assumption() else None) for line in
          antecedent2_proof.lines],
        Proof.Line(formula=consequent, rule=MP,
                   assumptions=[len(proof1.lines) + len(antecedent2_proof.lines) - 1, len(proof1.lines) - 1])
    ]

    proof = Proof(
        statement=InferenceRule(antecedent1_proof.statement.assumptions, consequent),
        rules=proof1.rules.union(antecedent2_proof.rules),
        lines=[*proof1.lines, *external_lines]
    )
    return proof


def remove_assumption(proof: Proof) -> Proof:
    """Converts a proof of some `conclusion` formula, the last assumption of
    which is an assumption `assumption`, into a proof of
    ``'(``\ `assumption`\ ``->``\ `conclusion`\ ``)'`` from the same assumptions
    except `assumption`.

    Parameters:
        proof: valid proof to convert, with at least one assumption, via some
            set of inference rules all of which have no assumptions except
            perhaps `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of ``'(``\ `assumptions`\ ``->``\ `conclusion`\ ``)'``
        from the same assumptions as the given proof except the last one, via
        the same inference rules as the given proof and in addition
        `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`, and
        `~propositions.axiomatic_systems.D`.
    """
    assert proof.is_valid()
    assert len(proof.statement.assumptions) > 0
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    the_assumptions = proof.statement.assumptions[-1]
    new_assumptions = [p for p in proof.statement.assumptions if p != the_assumptions]
    new_formulas = generate_new_formulas(proof.lines, the_assumptions)

    new_lines = []
    line_cnt = 0
    for new_formula, line in zip(new_formulas, proof.lines):
        if line.formula == the_assumptions:
            external_lines = handle_same(new_formula)
        elif line.formula in new_assumptions:
            external_lines = handle_assumptions(new_formula, line_cnt)
        else:  # has to be axiom
            external_lines = handle_axiom(new_formula, line_cnt, line, new_lines, new_formulas, proof.rules)

        line_cnt += len(external_lines)
        new_lines.extend(external_lines)

    return Proof(
        InferenceRule(new_assumptions, new_formulas[-1]),
        {*proof.rules, MP, I0, I1, D},
        lines=new_lines
    )


def handle_axiom(new_formula: Formula, line_cnt: int, old_line: Proof.Line, new_lines_so_far, new_formulas, rules) -> \
        List[Proof.Line]:
    if not old_line.assumptions:
        axiom = find_matching_inference_rule(new_formula.second, rules)
        return handle_axiom_not_mp(new_formula, line_cnt, axiom)
    else:
        return handle_axiom_mp(old_line, new_lines_so_far, new_formulas, new_formula, line_cnt)


def handle_axiom_mp(old_line: Proof.Line, new_lines_so_far, new_formulas, new_formula, line_cnt):
    indexes = get_mp_matching_lines(old_line, new_lines_so_far, new_formulas)

    d_formula = Formula('->', new_lines_so_far[indexes[1]].formula,
                        Formula('->', new_lines_so_far[indexes[0]].formula, new_formula))
    d_map = get_s_map(D, Formula('->', new_lines_so_far[indexes[1]].formula,
                                 Formula('->', new_lines_so_far[indexes[0]].formula, new_formula)))

    return [
        Proof.Line(D.conclusion.substitute_variables(d_map), D, []),
        Proof.Line(d_formula.second, MP, [indexes[1], line_cnt]),
        Proof.Line(new_formula, MP, [indexes[0], line_cnt + 1]),
    ]


def handle_axiom_not_mp(new_formula: Formula, line_cnt, axiom: InferenceRule) -> List[Proof.Line]:
    return handle_assumptions_or_not_mp(new_formula, line_cnt, axiom=axiom)


def find_matching_inference_rule(f: Formula, rules) -> InferenceRule:
    for r in rules:
        if InferenceRule([], f).is_specialization_of(r):
            return r

    raise RuntimeError


def handle_assumptions(new_formula: Formula, line_cnt: int) -> List[Proof.Line]:
    return handle_assumptions_or_not_mp(new_formula, line_cnt, axiom=None)


def handle_assumptions_or_not_mp(new_formula: Formula, line_cnt: int, axiom: Union[None, InferenceRule]) -> List[
    Proof.Line]:
    i1_map = get_s_map(I1, Formula("->", first=new_formula.second, second=new_formula))  # (old -> (new -> old))
    if axiom is None:
        first_line = Proof.Line(new_formula.second, None)
    else:
        first_line = Proof.Line(new_formula.second, axiom, [])

    return [
        first_line,
        Proof.Line(I1.conclusion.substitute_variables(i1_map), I1, []),
        Proof.Line(new_formula, MP, [line_cnt, line_cnt + 1])
    ]


def get_mp_matching_lines(old_line: Proof.Line, new_lines_so_far, new_formulas):
    indexes = []
    for asmp in old_line.assumptions:
        formula = new_formulas[asmp]
        for ind, line in enumerate(new_lines_so_far):
            if line.formula == formula:
                indexes.append(ind)
                break
    return indexes


def get_s_map(axiom: InferenceRule, formula: Formula):
    return InferenceRule.formula_specialization_map(axiom.conclusion, formula)


def handle_same(new_formula: Formula) -> List[Proof.Line]:
    return [Proof.Line(new_formula, rule=I0, assumptions=[])]


def generate_new_formulas(lines: Tuple[Proof.Line], f: Formula) -> List[Formula]:
    return [Formula('->', f, line.formula) for line in lines]


def merge_proofs(proof1: Proof, proof2: Proof) -> Proof:
    proof_2_lines = [
        Proof.Line(line.formula, line.rule,
                   [n + len(proof1.lines) for n in line.assumptions] if not line.is_assumption() else None) for line in
        proof2.lines
    ]

    lines = [*proof1.lines, *proof_2_lines]
    statement = InferenceRule(proof1.statement.assumptions, proof2.statement.conclusion)
    rules = proof1.rules.union(proof2.rules)

    return Proof(statement, rules, lines)


def proof_from_inconsistency(proof_of_affirmation: Proof,
                             proof_of_negation: Proof, conclusion: Formula) -> \
        Proof:
    """Combines the given proofs of a formula `affirmation` and its negation
    ``'~``\ `affirmation`\ ``'`` into a proof of the given formula.

    Parameters:
        proof_of_affirmation: valid proof of `affirmation`.
        proof_of_negation: valid proof of ``'~``\ `affirmation`\ ``'`` from the
            same assumptions and inference rules of `proof_of_affirmation`.

    Returns:
        A valid proof of `conclusion` from the same assumptions as the given
        proofs, via the same inference rules as the given proofs and in addition
        `~propositions.axiomatic_systems.MP` and
        `~propositions.axiomatic_systems.I2`.
    """
    assert proof_of_affirmation.is_valid()
    assert proof_of_negation.is_valid()
    assert proof_of_affirmation.statement.assumptions == \
           proof_of_negation.statement.assumptions
    assert Formula('~', proof_of_affirmation.statement.conclusion) == \
           proof_of_negation.statement.conclusion
    assert proof_of_affirmation.rules == proof_of_negation.rules

    merged_proofs = merge_proofs(proof_of_affirmation, proof_of_negation)
    i2_formula = Formula('->', merged_proofs.statement.conclusion,
                         Formula('->', proof_of_affirmation.statement.conclusion, conclusion))
    new_lines = [
        Proof.Line(i2_formula, I2, []),
        Proof.Line(i2_formula.second, MP,
                   [len(merged_proofs.lines) - 1, len(merged_proofs.lines)]),
        Proof.Line(i2_formula.second.second, MP, [len(proof_of_affirmation.lines) - 1, len(merged_proofs.lines) + 1])
    ]
    statement = InferenceRule(merged_proofs.statement.assumptions, conclusion)
    return Proof(statement, merged_proofs.rules.union({I2}), [*merged_proofs.lines, *new_lines])


def prove_by_contradiction(proof: Proof) -> Proof:
    """Converts the given proof of ``'~(p->p)'``, the last assumption of which
    is an assumption ``'~``\ `formula`\ ``'``, into a proof of `formula` from
    the same assumptions except ``'~``\ `formula`\ ``'``.

    Parameters:
        proof: valid proof of ``'~(p->p)'`` to convert, the last assumption of
            which is of the form ``'~``\ `formula`\ ``'``, via some set of
            inference rules all of which have no assumptions except perhaps
            `~propositions.axiomatic_systems.MP`.

    Return:
        A valid proof of `formula` from the same assumptions as the given proof
        except the last one, via the same inference rules as the given proof and
        in addition `~propositions.axiomatic_systems.MP`,
        `~propositions.axiomatic_systems.I0`,
        `~propositions.axiomatic_systems.I1`,
        `~propositions.axiomatic_systems.D`, and
        `~propositions.axiomatic_systems.N`.
    """
    assert proof.is_valid()
    assert proof.statement.conclusion == Formula.parse('~(p->p)')
    assert len(proof.statement.assumptions) > 0
    assert proof.statement.assumptions[-1].root == '~'
    for rule in proof.rules:
        assert rule == MP or len(rule.assumptions) == 0

    # (~q->~p)->(p->q) = N
    proof1 = remove_assumption(proof)
    s_map = {
        'p': proof.statement.conclusion.first,
        # conclusion without ~
        'q': proof.statement.assumptions[-1].first
    }

    n_formula = N.conclusion.substitute_variables(s_map)
    new_lines = [
        Proof.Line(n_formula, N, []),
        Proof.Line(n_formula.second, MP, [len(proof1.lines) - 1, len(proof1.lines)]),  # ((p->p)->q)
        Proof.Line(proof.statement.conclusion.first, I0, []),  # (p->p)
        Proof.Line(n_formula.second.second, MP, [len(proof1.lines) + 2, len(proof1.lines) + 1]),
    ]
    statement = InferenceRule(proof1.statement.assumptions, n_formula.second.second)
    lines = [*proof1.lines, *new_lines]
    rules = proof1.rules.union({N})
    a = Proof(statement, rules, lines)
    print(a)
    return a
