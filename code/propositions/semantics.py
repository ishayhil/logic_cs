# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Iterator, List, Mapping

from propositions.syntax import *
from propositions.proofs import *
from itertools import product, combinations
from functools import reduce

Model = Mapping[str, bool]


def is_model(model: Model) -> bool:
    """Checks if the given dictionary a model over some set of variables.

    Parameters:
        model: dictionary to check.

    Returns:
        ``True`` if the given dictionary is a model over some set of variables,
        ``False`` otherwise.
    """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True


def variables(model: Model) -> AbstractSet[str]:
    """Finds all variables over which the given model is defined.

    Parameters:
        model: model to check.

    Returns:
        A set of all variables over which the given model is defined.
    """
    assert is_model(model)
    return model.keys()


def evaluate(formula: Formula, model: Model) -> bool:
    """Calculates the truth value of the given formula in the given model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: model over (possibly a superset of) the variables of the formula,
            to calculate the truth value in.

    Returns:
        The truth value of the given formula in the given model.
    """
    assert is_model(model)
    assert formula.variables().issubset(variables(model))

    if is_constant(formula.root):
        return formula.root == 'T'
    elif is_variable(formula.root):
        return model[formula.root]
    elif is_unary(formula.root):
        return not evaluate(formula.first, model)
    elif is_binary(formula.root):
        return evaluate_binary(formula.root, formula.first, formula.second, model)


def evaluate_binary(quantifier: str, first: Formula, second: Formula, model: Model):
    if quantifier == "&":
        return evaluate(first, model) and evaluate(second, model)
    elif quantifier == "-&":  # nand
        return not (evaluate(first, model) and evaluate(second, model))
    elif quantifier == "|":
        return evaluate(first, model) or evaluate(second, model)
    elif quantifier == "-|":  # nor
        return not (evaluate(first, model) or evaluate(second, model))
    elif quantifier == "+":  # xor
        return (evaluate(first, model) and not evaluate(second, model)) or (
                not evaluate(first, model) and evaluate(second, model))
    elif quantifier == "<->":  # iff
        return (not evaluate(first, model) or evaluate(second, model)) and (
                evaluate(first, model) or not evaluate(second, model))
    else:  # ->
        return not evaluate(first, model) or evaluate(second, model)


def all_models(variables: List[str]) -> Iterable[Model]:
    """Calculates all possible models over the given variables.

    Parameters:
        variables: list of variables over which to calculate the models.

    Returns:
        An iterable over all possible models over the given variables. The order
        of the models is lexicographic according to the order of the given
        variables, where False precedes True.

    Examples:
        >>> list(all_models(['p', 'q']))
        [{'p': False, 'q': False}, {'p': False, 'q': True}, {'p': True, 'q': False}, {'p': True, 'q': True}]
    """
    for v in variables:
        assert is_variable(v)

    _product = product(variables, [False, True], repeat=1)
    all_combs = combinations(_product, len(variables))

    for t in all_combs:
        temp_dic = {s[0]: s[1] for s in t}
        if len(temp_dic) == len(set(variables)):  # check if there are no repeats
            yield temp_dic


def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    """Calculates the truth value of the given formula in each of the given
    model.

    Parameters:
        formula: formula to calculate the truth value of.
        model: iterable over models to calculate the truth value in.

    Returns:
        An iterable over the respective truth values of the given formula in
        each of the given models, in the order of the given models.
    """
    for model in models:
        yield evaluate(formula, model)


def print_truth_table(formula: Formula) -> None:
    """Prints the truth table of the given formula, with variable-name columns
    sorted alphabetically.

    Parameters:
        formula: formula to print the truth table of.

    Examples:
        >>> print_truth_table(Formula.parse('~(p&q76)'))
        | p | q76 | ~(p&q76) |
        |---|-----|----------|
        | F | F   | T        |
        | F | T   | T        |
        | T | F   | T        |
        | T | T   | F        |
    """

    _vars = sorted(list(formula.variables()))

    vars_with_formula = _vars + [str(formula)]
    models = list(all_models(_vars))
    truth_vals = list(truth_values(formula, models))

    # header
    print('| ' + reduce(lambda a, b: a + ' | ' + b, vars_with_formula) + " |")

    spaces = lambda x: len(x) + 2
    # dashes
    print("".join(f"|{spaces(var) * '-'}" for var in vars_with_formula) + '|')

    # truth values
    for model, truth_val in zip(models, truth_vals):
        head = "| " + "| ".join(("T" if model[var] else "F") + (len(var) * " ") for var in _vars)
        tail = '| ' + ("T" if truth_val else "F") + (len(str(formula)) * " " + "|")
        print(head + tail)


def is_tautology(formula: Formula) -> bool:
    """Checks if the given formula is a tautology.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a tautology, ``False`` otherwise.
    """
    models = all_models(list(formula.variables()))
    return reduce(lambda a, b: a and b, truth_values(formula, models))


def is_contradiction(formula: Formula) -> bool:
    """Checks if the given formula is a contradiction.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is a contradiction, ``False`` otherwise.
    """
    models = all_models(list(formula.variables()))
    return not reduce(lambda a, b: a or b, truth_values(formula, models))


def is_satisfiable(formula: Formula) -> bool:
    """Checks if the given formula is satisfiable.

    Parameters:
        formula: formula to check.

    Returns:
        ``True`` if the given formula is satisfiable, ``False`` otherwise.
    """
    return not is_contradiction(formula)


def synthesize_for_model(model: Model) -> Formula:
    """Synthesizes a propositional formula in the form of a single clause that
      evaluates to ``True`` in the given model, and to ``False`` in any other
      model over the same variables.

    Parameters:
        model: model in which the synthesized formula is to hold.

    Returns:
        The synthesized formula.
    """
    assert is_model(model)

    _vars = [var if model[var] else '~' + var for var in model.keys()]
    s = reduce(lambda a, b: f"({a}&{b})", _vars)  # for recursive str structure

    return Formula.parse(s)


def synthesize(variables: List[str], values: Iterable[bool]) -> Formula:
    """Synthesizes a propositional formula in DNF over the given variables, from
    the given specification of which value the formula should have on each
    possible model over these variables.

    Parameters:
        variables: the set of variables for the synthesize formula.
        values: iterable over truth values for the synthesized formula in every
            possible model over the given variables, in the order returned by
            `all_models`\ ``(``\ `~synthesize.variables`\ ``)``.

    Returns:
        The synthesized formula.

    Examples:
        >>> formula = synthesize(['p', 'q'], [True, True, True, False])
        >>> for model in all_models(['p', 'q']):
        ...     evaluate(formula, model)
        True
        True
        True
        False
    """
    assert len(variables) > 0

    models = list(all_models(variables))

    s = ""
    for model, b in zip(models, values):
        f = str(synthesize_for_model(model))
        if b:
            s = f"({s}|{f})" if s else f
    if not s:  # all false
        for var in variables:
            t = f"({var}&~{var})"
            s = f"({s}|{t})" if s else t

    return Formula.parse(s)


def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    """Checks if the given inference rule holds in the given model.

    Parameters:
        rule: inference rule to check.
        model: model to check in.

    Returns:
        ``True`` if the given inference rule holds in the given model, ``False``
        otherwise.
    """
    assert is_model(model)
    # Task 4.2


def is_sound_inference(rule: InferenceRule) -> bool:
    """Checks if the given inference rule is sound, i.e., whether its
    conclusion is a semantically correct implication of its assumptions.

    Parameters:
        rule: inference rule to check.

    Returns:
        ``True`` if the given inference rule is sound, ``False`` otherwise.
    """
    # Task 4.3
