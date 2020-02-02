# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/prenex.py

"""Conversion of predicate-logic formulas into prenex normal form."""

from typing import Tuple

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *

#: Additional axioms of quantification for first-order predicate logic.
ADDITIONAL_QUANTIFICATION_AXIOMS = (
    Schema(Formula.parse('((~Ax[R(x)]->Ex[~R(x)])&(Ex[~R(x)]->~Ax[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('((~Ex[R(x)]->Ax[~R(x)])&(Ax[~R(x)]->~Ex[R(x)]))'),
           {'x', 'R'}),
    Schema(Formula.parse('(((Ax[R(x)]&Q())->Ax[(R(x)&Q())])&'
                         '(Ax[(R(x)&Q())]->(Ax[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]&Q())->Ex[(R(x)&Q())])&'
                         '(Ex[(R(x)&Q())]->(Ex[R(x)]&Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ax[R(x)])->Ax[(Q()&R(x))])&'
                         '(Ax[(Q()&R(x))]->(Q()&Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()&Ex[R(x)])->Ex[(Q()&R(x))])&'
                         '(Ex[(Q()&R(x))]->(Q()&Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]|Q())->Ax[(R(x)|Q())])&'
                         '(Ax[(R(x)|Q())]->(Ax[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]|Q())->Ex[(R(x)|Q())])&'
                         '(Ex[(R(x)|Q())]->(Ex[R(x)]|Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ax[R(x)])->Ax[(Q()|R(x))])&'
                         '(Ax[(Q()|R(x))]->(Q()|Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()|Ex[R(x)])->Ex[(Q()|R(x))])&'
                         '(Ex[(Q()|R(x))]->(Q()|Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ax[R(x)]->Q())->Ex[(R(x)->Q())])&'
                         '(Ex[(R(x)->Q())]->(Ax[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Ex[R(x)]->Q())->Ax[(R(x)->Q())])&'
                         '(Ax[(R(x)->Q())]->(Ex[R(x)]->Q())))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ax[R(x)])->Ax[(Q()->R(x))])&'
                         '(Ax[(Q()->R(x))]->(Q()->Ax[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((Q()->Ex[R(x)])->Ex[(Q()->R(x))])&'
                         '(Ex[(Q()->R(x))]->(Q()->Ex[R(x)])))'), {'x', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ax[R(x)]->Ay[Q(y)])&(Ay[Q(y)]->Ax[R(x)])))'),
           {'x', 'y', 'R', 'Q'}),
    Schema(Formula.parse('(((R(x)->Q(x))&(Q(x)->R(x)))->'
                         '((Ex[R(x)]->Ey[Q(y)])&(Ey[Q(y)]->Ex[R(x)])))'),
           {'x', 'y', 'R', 'Q'}))


def is_quantifier_free(formula: Formula) -> bool:
    """Checks if the given formula contains any quantifiers.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if the given formula contains any quantifiers, ``True``
        otherwise.
    """
    if is_equality(formula.root) or is_relation(formula.root):
        return True
    elif is_binary(formula.root):
        return is_quantifier_free(formula.first) and is_quantifier_free(formula.second)
    elif is_unary(formula.root):
        return is_quantifier_free(formula.first)
    else:
        return False


def is_in_prenex_normal_form(formula: Formula) -> bool:
    """Checks if the given formula is in prenex normal form.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula in prenex normal form, ``False``
        otherwise.
    """
    if is_quantifier(formula.root):
        return is_in_prenex_normal_form(formula.predicate)
    else:
        return is_quantifier_free(formula)


def equivalence_of(formula1: Formula, formula2: Formula) -> Formula:
    """States the equivalence of the two given formulas as a formula.

    Parameters:
        formula1: first of the formulas the equivalence of which is to be
            stated.
        formula2: second of the formulas the equivalence of which is to be
            stated.

    Returns:
        The formula ``'((``\ `formula1`\ ``->``\ `formula2`\ ``)&(``\ `formula2`\ ``->``\ `formula1`\ ``))'``.
    """
    return Formula('&', Formula('->', formula1, formula2),
                   Formula('->', formula2, formula1))


def has_uniquely_named_variables(formula: Formula) -> bool:
    """Checks if the given formula has uniquely named variables.

    Parameters:
        formula: formula to check.

    Returns:
        ``False`` if in the given formula some variable name has both quantified
        and free occurrences or is quantified by more than one quantifier,
        ``True`` otherwise.
    """
    forbidden_variables = set(formula.free_variables())

    def has_uniquely_named_variables_helper(formula: Formula) -> bool:
        if is_unary(formula.root):
            return has_uniquely_named_variables_helper(formula.first)
        elif is_binary(formula.root):
            return has_uniquely_named_variables_helper(formula.first) and \
                   has_uniquely_named_variables_helper(formula.second)
        elif is_quantifier(formula.root):
            if formula.variable in forbidden_variables:
                return False
            forbidden_variables.add(formula.variable)
            return has_uniquely_named_variables_helper(formula.predicate)
        else:
            assert is_relation(formula.root) or is_equality(formula.root)
            return True

    return has_uniquely_named_variables_helper(formula)


def uniquely_rename_quantified_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula with uniquely named
    variables, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, with the exact same structure but with the additional
        property of having uniquely named variables, obtained by consistently
        replacing each variable name that is bound in the given formula with a
        new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``. The
        second element of the pair is a proof of the equivalence of the given
        formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.5
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS))
    if is_quantifier_free(formula):
        # print(equivalence_of(formula, formula))
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    elif is_unary(formula.root):
        inner_formula, proof = uniquely_rename_quantified_variables(formula.first)
        new_formula = Formula(formula.root, inner_formula)
        step0 = prover.add_proof(proof.conclusion, proof)
        prover.add_tautological_implication(equivalence_of(formula, new_formula), {step0})
        return new_formula, prover.qed()

    elif is_binary(formula.root):
        first_formula, first_proof = uniquely_rename_quantified_variables(formula.first)
        second_formula, second_proof = uniquely_rename_quantified_variables(formula.second)
        step0 = prover.add_proof(first_proof.conclusion, first_proof)
        step1 = prover.add_proof(second_proof.conclusion, second_proof)
        new_formula = Formula(formula.root, first_formula, second_formula)
        step3 = prover.add_tautological_implication(equivalence_of(formula, new_formula), {step0, step1})
        return new_formula, prover.qed()
    else:  # quantifier
        substituted_predicate, substituted_predicate_proof = uniquely_rename_quantified_variables(formula.predicate)
        new_var = next(fresh_variable_name_generator)

        instantiation_map = {'x': formula.variable, 'y': new_var,
                             'R': formula.predicate.substitute({formula.variable: Term('_')}),
                             'Q': substituted_predicate.substitute({formula.variable: Term('_')})}

        ax = ADDITIONAL_QUANTIFICATION_AXIOMS[14] if formula.root == 'A' else ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        step0 = prover.add_proof(substituted_predicate_proof.conclusion, substituted_predicate_proof)
        step1 = prover.add_instantiated_assumption(ax.instantiate(instantiation_map), ax, instantiation_map)
        new_formula = Formula(formula.root, new_var,
                              substituted_predicate.substitute({formula.variable: Term(new_var)}))
        step3 = prover.add_mp(equivalence_of(formula, new_formula), step0, step1)
        return new_formula, prover.qed()


def pull_out_quantifications_across_negation(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``,
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, whose root is a negation, i.e., which is of
            the form
            ``'~``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_formula`\ ``]``...\ ``]]'``
            where `n`>=0, each `Qi` is a quantifier, each `xi` is a variable
            name, and `inner_formula` does not start with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[~``\ `inner_formula`\ ``]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the `xi` variable names and
        `inner_formula` are the same as in the given formula. The second element
        of the pair is a proof of the equivalence of the given formula and the
        returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('~Ax[Ey[R(x,y)]]')
        >>> returned_formula, proof = pull_out_quantifications_across_negation(
        ...     formula)
        >>> returned_formula
        Ex[Ay[~R(x,y)]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert is_unary(formula.root)
    # Task 11.6
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS), False)

    if not is_quantifier(formula.first.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    quantifier = formula.first
    not_predicate = Formula('~', quantifier.predicate)
    new_predicate, neg_predicate_proof = pull_out_quantifications_across_negation(not_predicate)
    new_root = "A" if quantifier.root == "E" else "E"
    new_formula = Formula(new_root, quantifier.variable, new_predicate)
    conversion_mapping = {'x': quantifier.variable,
                          'R': quantifier.predicate.substitute({quantifier.variable: Term('_')})}
    bind_mapping = {'x': quantifier.variable, 'y': quantifier.variable,
                    'Q': new_predicate.substitute({quantifier.variable: Term('_')}),
                    'R': not_predicate.substitute({quantifier.variable: Term('_')})}
    if quantifier.root == "A":
        bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        conversion_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[0]
    else:
        bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        conversion_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[1]

    step0 = prover.add_proof(neg_predicate_proof.conclusion, neg_predicate_proof)
    step1 = prover.add_instantiated_assumption(bind_axiom.instantiate(bind_mapping), bind_axiom, bind_mapping)
    step2 = prover.add_mp(prover._lines[step1].formula.second, step0, step1)
    step3 = prover.add_instantiated_assumption(conversion_axiom.instantiate(conversion_mapping), conversion_axiom,
                                               conversion_mapping)
    step4 = prover.add_tautological_implication(equivalence_of(formula, new_formula), {step2, step3})
    return new_formula, prover.qed()


def pull_out_quantifications_from_left_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `second`\ ``)'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_first` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `inner_first`\ `*`\ `second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `inner_first`, and `second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]&Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_left_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ax[Ey[(R(x,y)&Ez[P(1,z)])]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.1
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS), False)
    if not is_quantifier(formula.first.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    quantifier = formula.first
    predicate_and_second = Formula(formula.root, quantifier.predicate, formula.second)
    new_predicate, new_predicate_proof = \
        pull_out_quantifications_from_left_across_binary_operator(predicate_and_second)
    root = quantifier.root if formula.root != '->' else ('A' if quantifier.root == 'E' else 'E')
    new_formula = Formula(root, quantifier.variable, new_predicate)
    conversion_mapping = {'x': quantifier.variable,
                          'R': quantifier.predicate.substitute({quantifier.variable: Term('_')}),
                          'Q': formula.second.substitute({quantifier.variable: Term('_')})}
    bind_mapping = {'x': quantifier.variable, 'y': quantifier.variable,
                    'Q': new_predicate.substitute({quantifier.variable: Term('_')}),
                    'R': predicate_and_second.substitute({quantifier.variable: Term('_')})}

    if quantifier.root == 'A':
        bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14] if formula.root != '->' else ADDITIONAL_QUANTIFICATION_AXIOMS[
            15]
        conversion_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[{'&': 2, '|': 6, '->': 10}[formula.root]]
    else:
        bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15] if formula.root != '->' else ADDITIONAL_QUANTIFICATION_AXIOMS[
            14]
        conversion_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[{'&': 3, '|': 7, '->': 11}[formula.root]]

    step0 = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
    step1 = prover.add_instantiated_assumption(bind_axiom.instantiate(bind_mapping), bind_axiom, bind_mapping)
    step2 = prover.add_mp(prover._lines[step1].formula.second, step0, step1)
    step3 = prover.add_instantiated_assumption(conversion_axiom.instantiate(conversion_mapping), conversion_axiom,
                                               conversion_mapping)
    prover.add_tautological_implication(equivalence_of(formula, new_formula), {step2, step3})
    return new_formula, prover.qed()


def pull_out_quantifications_from_right_across_binary_operator(formula:
Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `first`\ `*`\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, each `Qi` is a quantifier,
            each `xi` is a variable name, and `inner_second` does not start with
            a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[(``\ `first`\ `*`\ `inner_second`\ ``)]``...\ ``]]'``
        where each `Q'i` is a quantifier, and where the operator `*`, the `xi`
        variable names, `first`, and `inner_second` are the same as in the given
        formula. The second element of the pair is a proof of the equivalence of
        the given formula and the returned formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]|Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_from_right_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ez[(Ax[Ey[R(x,y)]]|P(1,z))]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.7.2
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS), False)
    if not is_quantifier(formula.second.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    quantifier = formula.second
    first_and_predicate = Formula(formula.root, formula.first, quantifier.predicate)
    new_predicate, new_predicate_proof = pull_out_quantifications_from_right_across_binary_operator(first_and_predicate)
    new_formula = Formula(quantifier.root, quantifier.variable, new_predicate)
    conversion_mapping = {'x': quantifier.variable,
                          'R': quantifier.predicate.substitute({quantifier.variable: Term('_')}),
                          'Q': formula.first.substitute({quantifier.variable: Term('_')})}
    bind_mapping = {'x': quantifier.variable, 'y': quantifier.variable,
                    'Q': new_predicate.substitute({quantifier.variable: Term('_')}),
                    'R': first_and_predicate.substitute({quantifier.variable: Term('_')})}

    if quantifier.root == 'A':
        bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        conversion_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[{'&': 4, '|': 8, '->': 12}[formula.root]]
    else:
        bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        conversion_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[{'&': 5, '|': 9, '->': 13}[formula.root]]

    step0 = prover.add_proof(new_predicate_proof.conclusion, new_predicate_proof)
    step1 = prover.add_instantiated_assumption(bind_axiom.instantiate(bind_mapping), bind_axiom, bind_mapping)
    step2 = prover.add_mp(prover._lines[step1].formula.second, step0, step1)
    step3 = prover.add_instantiated_assumption(conversion_axiom.instantiate(conversion_mapping), conversion_axiom,
                                               conversion_mapping)
    prover.add_tautological_implication(equivalence_of(formula, new_formula), {step2, step3})
    return new_formula, prover.qed()


def pull_out_quantifications_across_binary_operator(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables of the form
    ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
    to an equivalent formula of the form
    ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
    and proves the equivalence of these two formulas.

    Parameters:
        formula: formula with uniquely named variables to convert, whose root
            is a binary operator, i.e., which is of the form
            ``'(``\ `Q1`\ `x1`\ ``[``\ `Q2`\ `x2`\ ``[``...\ `Qn`\ `xn`\ ``[``\ `inner_first`\ ``]``...\ ``]]``\ `*`\ `P1`\ `y1`\ ``[``\ `P2`\ `y2`\ ``[``...\ `Pm`\ `ym`\ ``[``\ `inner_second`\ ``]``...\ ``]])'``
            where `*` is a binary operator, `n`>=0, `m`>=0, each `Qi` and `Pi`
            is a quantifier, each `xi` and `yi` is a variable name, and neither
            `inner_first` nor `inner_second` starts with a quantifier.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but of the form
        ``'``\ `Q'1`\ `x1`\ ``[``\ `Q'2`\ `x2`\ ``[``...\ `Q'n`\ `xn`\ ``[``\ `P'1`\ `y1`\ ``[``\ `P'2`\ `y2`\ ``[``...\ `P'm`\ `ym`\ ``[(``\ `inner_first`\ `*`\ `inner_second`\ ``)]``...\ ``]]]``...\ ``]]'``
        where each `Q'i` and `P'i` is a quantifier, and where the operator `*`,
        the `xi` and `yi` variable names, `inner_first`, and `inner_second` are
        the same as in the given formula. The second element of the pair is a
        proof of the equivalence of the given formula and the returned formula
        (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(Ax[Ey[R(x,y)]]->Ez[P(1,z)])')
        >>> returned_formula, proof = pull_out_quantifications_across_binary_operator(
        ...     formula)
        >>> returned_formula
        Ex[Ay[Ez[(R(x,y)->P(1,z))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """
    assert has_uniquely_named_variables(formula)
    assert is_binary(formula.root)
    # Task 11.8
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS), False)
    if not is_quantifier(formula.first.root) and not is_quantifier(formula.second.root):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    l_formula, l_proof = pull_out_quantifications_from_left_across_binary_operator(formula)
    quantifiers = []
    while is_quantifier(l_formula.root):
        quantifiers.append((l_formula.root, l_formula.variable))
        l_formula = l_formula.predicate
    pulled_right_formula, pulled_right_proof = pull_out_quantifications_from_right_across_binary_operator(l_formula)

    step_i = prover.add_proof(pulled_right_proof.conclusion, pulled_right_proof)
    old_formula, new_formula = l_formula, pulled_right_formula
    for i in range(len(quantifiers)):
        q = quantifiers[-1 - i]
        if q[0] == 'A':
            bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        else:
            bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        bind_mapping = {'x': q[1], 'y': q[1], 'Q': new_formula.substitute({q[1]: Term('_')}),
                        'R': old_formula.substitute({q[1]: Term('_')})}
        step1 = prover.add_instantiated_assumption(bind_axiom.instantiate(bind_mapping), bind_axiom, bind_mapping)
        step_i = prover.add_mp(prover._lines[step1].formula.second, step_i, step1)
        derivation = prover._lines[step_i].formula.first
        old_formula, new_formula = derivation.first, derivation.second

    step3 = prover.add_proof(l_proof.conclusion, l_proof)
    prover.add_tautological_implication(equivalence_of(formula, new_formula), {step_i, step3})
    return new_formula, prover.qed()


def to_prenex_normal_form_from_uniquely_named_variables(formula: Formula) -> \
        Tuple[Formula, Proof]:
    """Converts the given formula with uniquely named variables to an equivalent
    formula in prenex normal form, and proves the equivalence of these two
    formulas.

    Parameters:
        formula: formula with uniquely named variables to convert.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.

    Examples:
        >>> formula = Formula.parse('(~(Ax[Ey[R(x,y)]]->Ez[P(1,z)])|S(w))')
        >>> returned_formula, proof = to_prenex_normal_form_from_uniquely_named_variables(
        ...     formula)
        >>> returned_formula
        Ax[Ey[Az[(~(R(x,y)->P(1,z))|S(w))]]]
        >>> proof.is_valid()
        True
        >>> proof.conclusion == equivalence_of(formula, returned_formula)
        True
        >>> proof.assumptions == Prover.AXIOMS.union(
        ...     ADDITIONAL_QUANTIFICATION_AXIOMS)
        True
    """

    assert has_uniquely_named_variables(formula)
    # Task 11.9
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS), False)
    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()

    if is_unary(formula.root):
        f, p = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        prenex_f, prenex_p = pull_out_quantifications_across_negation(Formula('~', f))
        f0, f = p.conclusion.first.first, p.conclusion.first.second
        step0 = prover.add_proof(p.conclusion, p)
        step1 = prover.add_tautological_implication(equivalence_of(Formula('~', f0), Formula('~', f)), {step0})
        step2 = prover.add_proof(prenex_p.conclusion, prenex_p)
        step3 = prover.add_tautological_implication(equivalence_of(formula, prenex_f), {step1, step2})
        return prenex_f, prover.qed()

    if is_binary(formula.root):
        f0, p0 = to_prenex_normal_form_from_uniquely_named_variables(formula.first)
        f, p1 = to_prenex_normal_form_from_uniquely_named_variables(formula.second)
        f = Formula(formula.root, f0, f)
        prenex_f, prenex_p = pull_out_quantifications_across_binary_operator(f)
        step0 = prover.add_proof(p0.conclusion, p0)
        step1 = prover.add_proof(p1.conclusion, p1)
        step2 = prover.add_tautological_implication(equivalence_of(formula, f), {step0, step1})
        step3 = prover.add_proof(prenex_p.conclusion, prenex_p)
        step4 = prover.add_tautological_implication(equivalence_of(prenex_f, formula), {step2, step3})
        return prenex_f, prover.qed()
    else:
        assert is_quantifier(formula.root)
        f, p = to_prenex_normal_form_from_uniquely_named_variables(formula.predicate)
        if formula.root == 'A':
            bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[14]
        else:
            bind_axiom = ADDITIONAL_QUANTIFICATION_AXIOMS[15]
        mapping = {'x': formula.variable, 'y': formula.variable, 'R': f.substitute({formula.variable: Term('_')}),
                   'Q': formula.predicate.substitute({formula.variable: Term('_')})}
        step0 = prover.add_proof(p.conclusion, p)
        step1 = prover.add_instantiated_assumption(bind_axiom.instantiate(mapping), bind_axiom, mapping)
        p_form = Formula(formula.root, formula.variable, f)
        step2 = prover.add_tautological_implication(equivalence_of(formula, p_form), {step0, step1})
        return p_form, prover.qed()


def to_prenex_normal_form(formula: Formula) -> Tuple[Formula, Proof]:
    """Converts the given formula to an equivalent formula in prenex normal
    form, and proves the equivalence of these two formulas.

    Parameters:
        formula: formula to convert, which contains no variable names starting
            with ``z``.

    Returns:
        A pair. The first element of the pair is a formula equivalent to the
        given formula, but in prenex normal form. The second element of the pair
        is a proof of the equivalence of the given formula and the returned
        formula (i.e., a proof of
        `equivalence_of`\ ``(``\ `formula`\ ``,``\ `returned_formula`\ ``)``)
        via `~predicates.prover.Prover.AXIOMS` and
        `ADDITIONAL_QUANTIFICATION_AXIOMS`.
    """
    # Task 11.10
    prover = Prover(Prover.AXIOMS.union(ADDITIONAL_QUANTIFICATION_AXIOMS), False)
    if is_quantifier_free(formula):
        prover.add_tautology(equivalence_of(formula, formula))
        return formula, prover.qed()
    renamed_formula, rename_proof = uniquely_rename_quantified_variables(formula)
    p_formula, p_proof = to_prenex_normal_form_from_uniquely_named_variables(renamed_formula)
    step0 = prover.add_proof(rename_proof.conclusion, rename_proof)
    step1 = prover.add_proof(p_proof.conclusion, p_proof)
    step2 = prover.add_tautological_implication(equivalence_of(formula, p_formula), {step0, step1})
    return p_formula, prover.qed()
