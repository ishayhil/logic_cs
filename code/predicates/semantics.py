# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/semantics.py

"""Semantic analysis of first-order logic constructs."""

from typing import AbstractSet, FrozenSet, Generic, Mapping, Tuple, TypeVar

from logic_utils import frozen, frozendict

from predicates.syntax import *

#: A generic type for a universe element in a model.
T = TypeVar('T')


@frozen
class Model(Generic[T]):
    """An immutable model for first-order logic constructs.

    Attributes:
        universe (`~typing.FrozenSet`\\[`T`]): the set of elements to which
            terms can be evaluated and over which quantifications are defined.
        constant_meanings (`~typing.Mapping`\\[`str`, `T`]): mapping from each
            constant name to the universe element to which it evaluates.
        relation_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each relation name to the arity of the relation, or to ``-1`` if the
            relation is the empty relation.
        relation_meanings (`~typing.Mapping`\\[`str`, `~typing.AbstractSet`\\[`~typing.Tuple`\\[`T`, ...]]]):
            mapping from each n-ary relation name to argument n-tuples (of
            universe elements) for which the relation is true.
        function_arities (`~typing.Mapping`\\[`str`, `int`]): mapping from
            each function name to the arity of the function.
        function_meanings (`~typing.Mapping`\\[`str`, `~typing.Mapping`\\[`~typing.Tuple`\\[`T`, ...], `T`]]):
            mapping from each n-ary function name to the mapping from each
            argument n-tuple (of universe elements) to the universe element that
            the function outputs given these arguments.
    """
    universe: FrozenSet[T]
    constant_meanings: Mapping[str, T]
    relation_arities: Mapping[str, int]
    relation_meanings: Mapping[str, AbstractSet[Tuple[T, ...]]]
    function_arities: Mapping[str, int]
    function_meanings: Mapping[str, Mapping[Tuple[T, ...], T]]

    def __init__(self, universe: AbstractSet[T],
                 constant_meanings: Mapping[str, T],
                 relation_meanings: Mapping[str, AbstractSet[Tuple[T, ...]]],
                 function_meanings: Mapping[str, Mapping[Tuple[T, ...], T]] =
                 frozendict()) -> None:
        """Initializes a `Model` from its universe and constant, relation, and
        function meanings.

        Parameters:
            universe: the set of elements to which terms are to be evaluated
                and over which quantifications are to be defined.
            constant_meanings: mapping from each constant name to a universe
                element to which it is to be evaluated.
            relation_meanings: mapping from each relation name that is to
                be the name of an n-ary relation, to the argument n-tuples (of
                universe elements) for which the relation is to be true.
            function_meanings: mapping from each function name that is to
                be the name of an n-ary function, to a mapping from each
                argument n-tuple (of universe elements) to a universe element
                that the function is to output given these arguments.
        """
        self.universe = frozenset(universe)

        for constant in constant_meanings:
            assert is_constant(constant)
            assert constant_meanings[constant] in universe
        self.constant_meanings = frozendict(constant_meanings)

        relation_arities = {}
        for relation in relation_meanings:
            assert is_relation(relation)
            relation_meaning = relation_meanings[relation]
            if len(relation_meaning) == 0:
                arity = -1  # any
            else:
                some_arguments = next(iter(relation_meaning))
                arity = len(some_arguments)
                for arguments in relation_meaning:
                    assert len(arguments) == arity
                    for argument in arguments:
                        assert argument in universe
            relation_arities[relation] = arity
        self.relation_meanings = \
            frozendict({relation: frozenset(relation_meanings[relation]) for
                        relation in relation_meanings})
        self.relation_arities = frozendict(relation_arities)

        function_arities = {}
        for function in function_meanings:
            assert is_function(function)
            function_meaning = function_meanings[function]
            assert len(function_meaning) > 0
            some_argument = next(iter(function_meaning))
            arity = len(some_argument)
            assert arity > 0
            assert len(function_meaning) == len(universe) ** arity
            for arguments in function_meaning:
                assert len(arguments) == arity
                for argument in arguments:
                    assert argument in universe
                assert function_meaning[arguments] in universe
            function_arities[function] = arity
        self.function_meanings = \
            frozendict({function: frozendict(function_meanings[function]) for
                        function in function_meanings})
        self.function_arities = frozendict(function_arities)

    def __repr__(self) -> str:
        """Computes a string representation of the current model.

        Returns:
            A string representation of the current model.
        """
        return 'Universe=' + str(self.universe) + '; Constant Meanings=' + \
               str(self.constant_meanings) + '; Relation Meanings=' + \
               str(self.relation_meanings) + \
               ('; Function Meanings=' + str(self.function_meanings)
                if len(self.function_meanings) > 0 else '')

    def evaluate_term(self, term: Term,
                      assignment: Mapping[str, T] = frozendict()) -> T:
        """Calculates the value of the given term in the current model, for the
        given assignment of values to variables names.

        Parameters:
            term: term to calculate the value of, for the constants and
                functions of which the current model has meanings.
            assignment: mapping from each variable name in the given term to a
                universe element to which it is to be evaluated.

        Returns:
            The value (in the universe of the current model) of the given
            term in the current model, for the given assignment of values to
            variable names.
        """
        assert term.constants().issubset(self.constant_meanings.keys())
        assert term.variables().issubset(assignment.keys())
        for function, arity in term.functions():
            assert function in self.function_meanings and \
                   self.function_arities[function] == arity

        if is_constant(term.root):
            return self.constant_meanings[term.root]
        if is_variable(term.root):
            return assignment[term.root]
        else:  # func
            return self.function_meanings[term.root][
                tuple(self.evaluate_term(arg, assignment) for arg in term.arguments)]

    def evaluate_formula(self, formula: Formula,
                         assignment: Mapping[str, T] = frozendict()) -> bool:
        """Calculates the truth value of the given formula in the current model,
        for the given assignment of values to free occurrences of variables
        names.

        Parameters:
            formula: formula to calculate the truth value of, for the constants,
                functions, and relations of which the current model has
                meanings.
            assignment: mapping from each variable name that has a free
                occurrence in the given formula to a universe element to which
                it is to be evaluated.

        Returns:
            The truth value of the given formula in the current model, for the
            given assignment of values to free occurrences of variable names.
        """
        assert formula.constants().issubset(self.constant_meanings.keys())
        assert formula.free_variables().issubset(assignment.keys())
        for function, arity in formula.functions():
            assert function in self.function_meanings and \
                   self.function_arities[function] == arity
        for relation, arity in formula.relations():
            assert relation in self.relation_meanings and \
                   self.relation_arities[relation] in {-1, arity}

        if is_unary(formula.root):
            return not self.evaluate_formula(formula.first, assignment)
        elif is_binary(formula.root):
            first = self.evaluate_formula(formula.first, assignment)
            second = self.evaluate_formula(formula.second, assignment)
            if formula.root == '&':
                return first and second
            elif formula.root == '|':
                return first or second
            else:  # ->
                return (not first) or second
        elif is_relation(formula.root):
            return tuple(self.evaluate_term(term, assignment) for term in formula.arguments) in \
                   self.relation_meanings[formula.root]
        elif is_equality(formula.root):
            return self.evaluate_term(formula.arguments[0], assignment) == \
                   self.evaluate_term(formula.arguments[1], assignment)
        else:  # quantifier
            new_assignment = dict(assignment).pop(formula.variable) if formula.variable in assignment \
                else dict(assignment)
            if formula.root == 'A':
                return all(self.evaluate_formula(formula.predicate, {**new_assignment, **{formula.variable: e}})
                           for e in self.universe)
            else:
                return any(self.evaluate_formula(formula.predicate, {**new_assignment, **{formula.variable: e}})
                           for e in self.universe)

    def all_possible_assignments_for_model(self, arr, n, r, index, data, i, all_arrays):
        if index == r:
            all_arrays.append(data)
            return

        if i >= n:
            return

        data[index] = arr[i]
        self.all_possible_assignments_for_model(arr, n, r, index + 1, data, i + 1, all_arrays)

        self.all_possible_assignments_for_model(arr, n, r, index, data, i + 1, all_arrays)

    def is_model_of(self, formulas: AbstractSet[Formula]) -> bool:
        """Checks if the current model is a model for the given formulas.

        Returns:
            ``True`` if each of the given formulas evaluates to true in the
            current model for any assignment of elements from the universe of
            the current model to the free occurrences of variables in that
            formula, ``False`` otherwise.
        """
        for formula in formulas:
            assert formula.constants().issubset(self.constant_meanings.keys())
            for function, arity in formula.functions():
                assert function in self.function_meanings and \
                       self.function_arities[function] == arity
            for relation, arity in formula.relations():
                assert relation in self.relation_meanings and \
                       self.relation_arities[relation] in {-1, arity}
        import itertools

        all_free_vars = reduce(lambda a, b: a.union(b), [formula.free_variables() for formula in formulas])
        products = itertools.product(self.universe, repeat=len(self.universe))
        all_asm = set()
        for prod in products:
            all_asm.add(DictWrapper({free_var: e for free_var, e in zip(all_free_vars, prod)}))
        return all(self.evaluate_formula(formula, asm) for asm in all_asm for formula in formulas)


class DictWrapper(dict):
    def __hash__(self):
        return hash(tuple(sorted(self.items())))
