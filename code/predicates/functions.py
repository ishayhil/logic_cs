# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/functions.py

"""Syntactic conversion of first-order formulas to not use functions and
equality."""

from typing import AbstractSet, List, Set

from logic_utils import fresh_variable_name_generator

from predicates.syntax import *
from predicates.semantics import *


def function_name_to_relation_name(function: str) -> str:
    """Converts the given function name to a canonically corresponding relation
    name.

    Parameters:
        function: function name to convert.

    Returns:
        A relation name that is the same as the given function name, except that
        its first letter is capitalized.
    """
    assert is_function(function)
    return function[0].upper() + function[1:]


def relation_name_to_function_name(relation: str) -> str:
    """Converts the given relation name to a canonically corresponding function
    name.

    Parameters:
        relation: relation name to convert.

    Returns:
        A function name `function` such that
        `function_name_to_relation_name`\ ``(``\ `function`\ ``)`` is the given
        relation name.
    """
    assert is_relation(relation)
    return relation[0].lower() + relation[1:]


def replace_functions_with_relations_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a canonically corresponding model without any
    function meanings, replacing each function meaning with a canonically
    corresponding relation meaning.

    Parameters:
        model: model to convert, such that there exist no canonically
            corresponding function name and relation name that both have
            meanings in this model.

    Return:
        A model obtained from the given model by replacing every function
        meaning of a function name with a relation meaning of the canonically
        corresponding relation name, such that the relation meaning contains
        any tuple ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)``  if and only if `x1`
        is the output of the function meaning for the arguments
        ``(``\ `x2`\ ``,``...\ ``,``\ `xn`\ ``)``.
    """
    for function in model.function_meanings:
        assert function_name_to_relation_name(function) not in \
               model.relation_meanings

    new_relation_meanings: dict[str, Set[Tuple[T, ...]]] = dict()
    for func_name, func_mapping in model.function_meanings.items():
        relation_name = function_name_to_relation_name(func_name)
        new_relation_meanings[relation_name] = set()
        for args, res in func_mapping.items():
            new_relation_meanings[relation_name].add((res, *args))
    return Model(model.universe, model.constant_meanings, {**new_relation_meanings, **model.relation_meanings})


def replace_relations_with_functions_in_model(model: Model[T],
                                              original_functions:
                                              AbstractSet[str]) -> \
        Union[Model[T], None]:
    """Converts the given model with no function meanings to a canonically
    corresponding model with meanings for the given function names, having each
    new function meaning replace a canonically corresponding relation meaning.

    Parameters:
        model: model to convert, that contains no function meanings.
        original_functions: function names for the model to convert to,
            such that no relation name that canonically corresponds to any of
            these function names has a meaning in the given model.

    Returns:
        A model `model` with the given function names such that
        `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``
        is the given model, or ``None`` if no such model exists.
    """
    for function in original_functions:
        assert is_function(function)
        assert function not in model.function_meanings
        assert function_name_to_relation_name(function) in \
               model.relation_meanings

    new_functions_meaning: dict[str, dict[Tuple[T, ...], T]] = dict()
    for func in original_functions:
        relation_name = function_name_to_relation_name(func)
        new_functions_meaning[func] = dict()
        tuples = model.relation_meanings[relation_name]
        for t in tuples:
            if t[1:] in new_functions_meaning[func]:
                return None  # function cant returns diff values for same args
            new_functions_meaning[func][t[1:]] = t[0]

    for func in new_functions_meaning:
        # if the function doesnt have all the possible combinations of elements from the universe
        if len(new_functions_meaning[func]) != len(model.universe) ** len(list(new_functions_meaning[func].keys())[0]):
            return None

    new_relation_meanings = {k: v for k, v in model.relation_meanings.items() if
                             relation_name_to_function_name(k) not in original_functions}

    return Model(model.universe, model.constant_meanings, new_relation_meanings, new_functions_meaning)


def compile_term(term: Term) -> List[Formula]:
    """Syntactically compiles the given term into a list of single-function
    invocation steps.

    Parameters:
        term: term to compile, whose root is a function invocation, and that
            contains no variable names starting with ``z``.

    Returns:
        A list of steps, each of which is a formula of the form
        ``'``\ `y`\ ``=``\ `f`\ ``(``\ `x1`\ ``,``...\ ``,``\ `xn`\ ``)'``,
        where `y` is a new variable name obtained by calling
        `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``, `f`
        is a function name, and each of the `x`\ `i` is either a constant name
        or a variable name. If `x`\ `i` is a new variable name, then it is also
        the left-hand side of a previous step, where all of the steps "leading
        up to" `x1` precede those "leading up" to `x2`, etc. If all the returned
        steps hold in any model, then the left-hand-side variable of the last
        returned step evaluates in that model to the value of the given term.
    """
    assert is_function(term.root)

    overall = []
    args = []
    for t in term.arguments:
        if is_function(t.root):
            new_args = compile_term(t)
            overall.extend(new_args)
            args.append(new_args[-1].arguments[0])
        else:
            args.append(t)
    a = [*overall, Formula('=', [Term(next(fresh_variable_name_generator)), Term(term.root, args)])]
    return a


def generate_implies_rec(step: List[Formula], i: int, final_formula: Formula):
    R = function_name_to_relation_name(step[i].arguments[1].root)
    z = step[i].arguments[0]
    args = [z, *step[i].arguments[1].arguments]

    left_side = Formula(root=R, arguments_or_first_or_variable=args)

    if i == len(step) - 1:
        return Formula(root='A', arguments_or_first_or_variable=z.root,
                       second_or_predicate=Formula('->', left_side, final_formula))

    return Formula(root='A', arguments_or_first_or_variable=z.root,
                   second_or_predicate=Formula('->', left_side,
                                               generate_implies_rec(step, i + 1, final_formula)))


def replace_functions_with_relations_in_formula(formula: Formula) -> Formula:
    """Syntactically converts the given formula to a formula that does not
    contain any function invocations, and is "one-way equivalent" in the sense
    that the former holds in a model if and only if the latter holds in the
    canonically corresponding model with no function meanings.

    Parameters:
        formula: formula to convert, that contains no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in this
            formula.

    Returns:
        A formula such that the given formula holds in any model `model` if and
        only if the returned formula holds in
        `replace_function_with_relations_in_model`\ ``(``\ `model`\ ``)``.
    """
    assert len({function_name_to_relation_name(function) for
                function, arity in formula.functions()}.intersection(
        {relation for relation, arity in formula.relations()})) == 0
    for variable in formula.variables():
        assert variable[0] != 'z'

    if is_binary(formula.root):
        return Formula(formula.root, replace_functions_with_relations_in_formula(formula.first),
                       replace_functions_with_relations_in_formula(formula.second))
    if is_unary(formula.root):
        return Formula('~', replace_functions_with_relations_in_formula(formula.first))
    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_functions_with_relations_in_formula(formula.predicate))
    if is_relation(formula.root):
        steps: List[Formula] = []
        final_args: List[Term] = []
        for arg in formula.arguments:
            if is_function(arg.root):
                this_step = compile_term(arg)
                final_args.append(this_step[-1].arguments[0])
                steps.extend(this_step)
            else:
                final_args.append(arg)

        final_relation = Formula(formula.root, arguments_or_first_or_variable=final_args)
        return generate_implies_rec(steps, 0, final_relation) if steps else formula
    else:  # equality
        left = formula.arguments[0]
        right = formula.arguments[1]

        first_steps = compile_term(left) if is_function(left.root) else []
        second_steps = compile_term(right) if is_function(right.root) else []

        z1 = first_steps[-1].arguments[0] if first_steps else left
        z2 = second_steps[-1].arguments[0] if second_steps else right
        steps = [*first_steps, *second_steps]
        final_formula = Formula('=', arguments_or_first_or_variable=[z1, z2])
        return generate_implies_rec(steps, 0, final_formula) if steps else formula


def replace_functions_with_relations_in_formulas(formulas:
AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a set of formulas
    that do not contain any function invocations, and is "two-way
    equivalent" in the sense that:

    1. The former holds in a model if and only if the latter holds in the
       canonically corresponding model with no function meanings.
    2. The latter holds in a model if and only if that model has a
       canonically corresponding model with meanings for the functions of the
       former, and the former holds in that model.

    Parameters:
        formulas: formulas to convert, that contain no variable names starting
            with ``z``, and such that there exist no canonically corresponding
            function name and relation name that are both invoked in these
            formulas.

    Returns:
        A set of formulas, one for each given formula as well as one additional
        formula for each relation name that replaces a function name from the
        given formulas, such that:

        1. The given formulas holds in a model `model` if and only if the
           returned formulas holds in
           `replace_functions_with_relations_in_model`\ ``(``\ `model`\ ``)``.
        2. The returned formulas holds in a model `model` if and only if
           `replace_relations_with_functions_in_model`\ ``(``\ `model`\ ``,``\ `original_functions`\ ``)``,
           where `original_functions` are all the function names in the given
           formulas, is a model and the given formulas hold in it.
    """
    assert len(set.union(*[{function_name_to_relation_name(function) for
                            function, arity in formula.functions()}
                           for formula in formulas]).intersection(
        set.union(*[{relation for relation, arity in
                     formula.relations()} for
                    formula in formulas]))) == 0
    for formula in formulas:
        for variable in formula.variables():
            assert variable[0] != 'z'

    new_formulas = {replace_functions_with_relations_in_formula(f) for f in formulas}

    for f in formulas:
        for func in f.functions():
            first_rule = generate_first_rule(func, [])
            second_rule = generate_second_rule(func, [])
            new_formulas = new_formulas.union({first_rule, second_rule})

    return new_formulas


def generate_first_rule(function: Tuple[str, int], args_so_far: List[Term]):
    z = next(fresh_variable_name_generator)
    if len(args_so_far) == function[1]:
        r_name = function_name_to_relation_name(function[0])
        relation = Formula(r_name, arguments_or_first_or_variable=[Term(z), *args_so_far])
        return Formula('E', z, relation)

    args_so_far.append(Term(z))
    return Formula('A', z, generate_first_rule(function, args_so_far))


def generate_second_rule(function: Tuple[str, int], args_so_far: List[Term]):
    if len(args_so_far) == function[1] + 2:
        r_name = function_name_to_relation_name(function[0])
        relation1 = Formula(r_name, arguments_or_first_or_variable=[args_so_far[0], *args_so_far[2:]])
        relation2 = Formula(r_name, arguments_or_first_or_variable=[args_so_far[1], *args_so_far[2:]])
        r_and = Formula('&', relation1, relation2)
        equals = Formula('=', arguments_or_first_or_variable=args_so_far[:2])
        return Formula('->', r_and, equals)

    z = next(fresh_variable_name_generator)
    args_so_far.append(Term(z))
    return Formula('A', z, generate_second_rule(function, args_so_far))


def replace_equality_with_SAME_in_formulas(formulas: AbstractSet[Formula]) -> \
        Set[Formula]:
    """Syntactically converts the given set of formulas to a canonically
    corresponding set of formulas that do not contain any equalities, consisting
    of the following formulas:

    1. A formula for each of the given formulas, where each equality is
       replaced with a matching invocation of the relation name ``'SAME'``.
    2. Formula(s) that ensure that in any model for the returned formulas,
       the meaning of the relation name ``'SAME'`` is reflexive, symmetric, and
       transitive.
    3. For each relation name from the given formulas, formula(s) that ensure
       that in any model for the returned formulas, the meaning of this
       relation name respects the meaning of the relation name ``'SAME'``.

    Parameters:
        formulas: formulas to convert, that contain no function names and do not
            contain the relation name ``'SAME'``.

    Returns:
        The converted set of formulas.
    """
    for formula in formulas:
        assert len(formula.functions()) == 0
        assert 'SAME' not in \
               {relation for relation, arity in formula.relations()}

    new_formulas = {replace_equals_with_same_in_formula(f) for f in formulas}

    z1 = next(fresh_variable_name_generator)
    z2 = next(fresh_variable_name_generator)
    z3 = next(fresh_variable_name_generator)
    reflexivity = get_reflexivity(z1)
    symmetry = get_symmetry(z1, z2)
    transitivity = get_transitivity(z1, z2, z3)
    new_formulas.update({reflexivity, symmetry, transitivity})

    for formula in formulas:
        for relation in formula.relations():
            new_formulas.add(get_relation_same_rule(relation, []))

    return new_formulas


def replace_equals_with_same_in_formula(formula: Formula):
    if is_relation(formula.root):
        return formula
    if is_quantifier(formula.root):
        return Formula(formula.root, formula.variable, replace_equals_with_same_in_formula(formula.predicate))
    if is_binary(formula.root):
        return Formula(formula.root, replace_equals_with_same_in_formula(formula.first),
                       replace_equals_with_same_in_formula(formula.second))
    if is_unary(formula.root):
        return Formula(formula.root, replace_equals_with_same_in_formula(formula.first))
    else:  # equality
        return Formula('SAME', arguments_or_first_or_variable=formula.arguments)


def get_reflexivity(z1) -> Formula:
    return Formula('A', z1, Formula('SAME', [Term(z1), Term(z1)]))


def get_symmetry(z1, z2) -> Formula:
    implies1 = Formula('->', Formula('SAME', [Term(z1), Term(z2)]), Formula('SAME', [Term(z2), Term(z1)]))
    implies2 = Formula('->', Formula('SAME', [Term(z2), Term(z1)]), Formula('SAME', [Term(z1), Term(z2)]))
    _and = Formula('&', implies1, implies2)
    return Formula('A', z1, Formula('A', z2, _and))


def get_transitivity(z1, z2, z3) -> Formula:
    same1 = Formula('SAME', [Term(z1), Term(z2)])
    same2 = Formula('SAME', [Term(z2), Term(z3)])
    same3 = Formula('SAME', [Term(z1), Term(z3)])
    _and = Formula('&', same1, same2)
    implies = Formula('->', _and, same3)
    return Formula('A', z1, Formula('A', z2, Formula('A', z3, implies)))


def get_relation_same_rule(relation: Tuple[str, int], tuples_so_far: List[Tuple[str, str]]):
    if len(tuples_so_far) == relation[1]:
        same_tuples = generate_same_tuples(tuples_so_far)
        relation_assignments = generate_relation_assignments(relation, tuples_so_far)
        return Formula('->', same_tuples, relation_assignments)

    z1 = next(fresh_variable_name_generator)
    z2 = next(fresh_variable_name_generator)
    tuples_so_far.append((z1, z2))
    return Formula('A', z1, Formula('A', z2, get_relation_same_rule(relation, tuples_so_far)))


def generate_same_tuples(tuples_so_far: List[Tuple[str, str]], i: int = 0):
    same = Formula('SAME', arguments_or_first_or_variable=[Term(tuples_so_far[i][0]), Term(tuples_so_far[i][1])])
    if i == len(tuples_so_far) - 1:
        return same

    return Formula('&', same, generate_same_tuples(tuples_so_far, i + 1))


def generate_relation_assignments(relation: Tuple[str, int], tuples_so_far: List[Tuple[str, str]]):
    first_args = [Term(t[0]) for t in tuples_so_far]
    second_args = [Term(t[1]) for t in tuples_so_far]

    r1 = Formula(relation[0], arguments_or_first_or_variable=first_args)
    r2 = Formula(relation[0], arguments_or_first_or_variable=second_args)
    return Formula("->", r1, r2)


def add_SAME_as_equality_in_model(model: Model[T]) -> Model[T]:
    """Adds a meaning for the relation name ``'SAME'`` in the given model, that
    canonically corresponds to equality in the given model.

    Parameters:
        model: model that has no meaning for the relation name ``'SAME'``, to
            add the meaning to.

    Return:
        A model obtained from the given model by adding a meaning for the
        relation name ``'SAME'``, that contains precisely all pairs
        ``(``\ `x`\ ``,``\ `x`\ ``)`` for every element `x` of the universe of
        the given model.
    """
    assert 'SAME' not in model.relation_meanings
    # Task 8.7


def make_equality_as_SAME_in_model(model: Model[T]) -> Model[T]:
    """Converts the given model to a model where equality coincides with the
    meaning of ``'SAME'`` in the given model, in the sense that any set of
    formulas holds in the returned model if and only if its canonically
    corresponding set of formulas that do not contain equality holds in the
    given model.

    Parameters:
        model: model to convert, that contains no function meanings, and
            contains a meaning for the relation name ``'SAME'`` that is
            reflexive, symmetric, transitive, and respected by the meanings
            of all other relation names.

    Returns:
        A model that is a model for any set `formulas` if and only if
        the given model is a model for
        `replace_equality_with_SAME`\ ``(``\ `formulas`\ ``)``. The universe of
        the returned model corresponds to the equivalence classes of the
        ``'SAME'`` relation in the given model.
    """
    assert 'SAME' in model.relation_meanings and \
           model.relation_arities['SAME'] == 2
    assert len(model.function_meanings) == 0
    # Task 8.8
