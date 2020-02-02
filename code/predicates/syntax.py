# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/syntax.py

"""Syntactic handling of first-order formulas and terms."""

from __future__ import annotations
from typing import AbstractSet, Mapping, Optional, Sequence, Set, Tuple, Union, Dict
from functools import reduce

from logic_utils import fresh_variable_name_generator, frozen

from propositions.syntax import Formula as PropositionalFormula, \
    is_variable as is_propositional_variable
import re


def get_nested_str(s: str, opn: str = "(", close: str = ")") -> str:
    cnt = 1
    temp = ""
    for c in s[1:]:
        if c == opn:
            cnt += 1
        if c == close:
            cnt -= 1
        if cnt == 0:
            break
        temp += c
    return temp


def split_without_nested_args(s: str) -> list:
    lst = []
    current = ""
    i = 0
    while i < len(s):
        if s[i] == ',':
            lst.append(current) if current else None
            current = ""
            i += 1
        elif s[i] == '(':
            nested = get_nested_str(s[i:])
            current += "(" + nested + ")"
            i += len(nested) + 2
            lst.append(current)
            current = ""
        else:
            current += s[i]
            i += 1
    if current:
        lst.append(current)
    return lst


def find_main_operator(s: str) -> tuple:
    if s[1] in ['(', 'A', 'E'] or s[1:3] in ['~A', '~E', '~(']:  # there is nested braces or predicate Ax[...]
        if s[1] == '(':
            nested_braces = get_nested_str(s[1:])
        elif s[1:3] == '~(':
            nested_braces = '~' + get_nested_str(s[2:])
        else:
            pre_exp = re.findall(r"~?[AE][u-z]+", s)[0]
            var = re.findall(r"[u-z]+", pre_exp)[0]
            nested_braces = pre_exp[:-len(var)] + var + get_nested_str(s[len(pre_exp) + 1:], '[', ']')

        offset = 1 + len(nested_braces) + 2
        s = s[offset:]
        cg = [(m.start(0) + offset, m.end(0) + offset) for m in re.finditer(r'&|->|\|', s)]
    else:
        cg = [(m.start(0), m.end(0)) for m in re.finditer(r'&|->|\|', s)]

    return cg[0]


class ForbiddenVariableError(Exception):
    """Raised by `Term.substitute` and `Formula.substitute` when a substituted
    term contains a variable name that is forbidden in that context."""

    def __init__(self, variable_name: str) -> None:
        """Initializes a `ForbiddenVariableError` from its offending variable
        name.

        Parameters:
            variable_name: variable name that is forbidden in the context in
                which a term containing it was to be substituted.
        """
        assert is_variable(variable_name)
        self.variable_name = variable_name


def is_constant(s: str) -> bool:
    """Checks if the given string is a constant name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a constant name, ``False`` otherwise.
    """
    return (((s[0] >= '0' and s[0] <= '9') or (s[0] >= 'a' and s[0] <= 'd'))
            and s.isalnum()) or s == '_'


def is_variable(s: str) -> bool:
    """Checks if the given string is a variable name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a variable name, ``False`` otherwise.
    """
    return s[0] >= 'u' and s[0] <= 'z' and s.isalnum()


def is_function(s: str) -> bool:
    """Checks if the given string is a function name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a function name, ``False`` otherwise.
    """
    return s[0] >= 'f' and s[0] <= 't' and s.isalnum()


@frozen
class Term:
    """An immutable first-order term in tree representation, composed from
    variable names and constant names, and function names applied to them.

    Attributes:
        root (`str`): the constant name, variable name, or function name at the
            root of the term tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a function name.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]

    def __init__(self, root: str,
                 arguments: Optional[Sequence[Term]] = None) -> None:
        """Initializes a `Term` from its root and root arguments.

        Parameters:
            root: the root for the formula tree.
            arguments: the arguments to the root, if the root is a function
                name.
        """
        if is_constant(root) or is_variable(root):
            assert arguments is None
            self.root = root
        else:
            assert is_function(root)
            assert arguments is not None
            self.root = root
            self.arguments = tuple(arguments)
            assert len(self.arguments) > 0

    def __repr__(self) -> str:
        """Computes the string representation of the current term.

        Returns:
            The standard string representation of the current term.
        """
        if is_constant(self.root) or is_variable(self.root):
            return self.root
        else:
            return self.root + "(" + ','.join([repr(arg) for arg in self.arguments]) + ")"

    def __eq__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Term` object that equals the
            current term, ``False`` otherwise.
        """
        return isinstance(other, Term) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current term with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Term` object or does not
            equal the current term, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Term, str]:
        """Parses a prefix of the given string into a term.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a term.

        Returns:
            A pair of the parsed term and the unparsed suffix of the string. If
            the given string has as a prefix a constant name (e.g., ``'c12'``)
            or a variable name (e.g., ``'x12'``), then the parsed prefix will be
            that entire name (and not just a part of it, such as ``'x1'``).
        """
        if is_constant(s[0]) or is_variable(s[0]):
            the_var = re.findall(r'[a-z0-9]+|_', s)[0]
            tail = s[len(the_var):] if len(the_var) < len(s) else ""
            return Term(the_var), tail
        else:  # function
            func_name = re.findall(r'[a-zA-Z0-9]+', s)[0]
            nested_str = get_nested_str(s[len(func_name):])
            terms = tuple(Term.parse_prefix(prefix)[0] for prefix in split_without_nested_args(nested_str))
            tail = s[len(func_name + nested_str) + 2:] if len(func_name + nested_str) + 2 < len(s) else ""
            return Term(func_name, terms), tail

    @staticmethod
    def parse(s: str) -> Term:
        """Parses the given valid string representation into a term.

        Parameters:
            s: string to parse.

        Returns:
            A term whose standard string representation is the given string.
        """
        return Term.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current term.

        Returns:
            A set of all constant names used in the current term.
        """
        if is_constant(self.root):
            return {self.root}
        elif is_function(self.root):
            return reduce(lambda a, b: a.union(b), [arg.constants() for arg in self.arguments])  #
        else:
            return set()

    def variables(self) -> Set[str]:
        """Finds all variable names in the current term.

        Returns:
            A set of all variable names used in the current term.
        """
        if is_variable(self.root):
            return {self.root}
        elif is_function(self.root):
            return reduce(lambda a, b: a.union(b), [arg.variables() for arg in self.arguments])  #
        else:
            return set()

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current term, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current term.
        """
        if is_variable(self.root):
            return set()
        elif is_function(self.root):
            return {(self.root, len(self.arguments))}.union(
                reduce(lambda a, b: a.union(b), [arg.functions() for arg in self.arguments]))
        else:
            return set()

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Term:
        """Substitutes in the current term, each constant name `name` or
        variable name `name` that is a key in `substitution_map` with the term
        `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The term resulting from performing all substitutions. Only
            constant names and variable names originating in the current term
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`.

        Examples:
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'y'})
            f(c,plus(d,x))
            >>> Term.parse('f(x,c)').substitute(
            ...     {'c': Term.parse('plus(d,y)')}, {'y'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)

        if is_constant(self.root) or is_variable(self.root):
            # if self.root in forbidden_variables then it is bound var, so don't replace either
            if self.root in substitution_map and self.root not in forbidden_variables:
                replacement = substitution_map[self.root]
                legality = replacement.check_if_legal_replacement(forbidden_variables)
                if legality is not None:
                    raise ForbiddenVariableError(legality.root)
                else:
                    return replacement
            else:
                return self
        else:  # function
            args = []
            for arg in self.arguments:
                args.append(arg.substitute(substitution_map, forbidden_variables))
            return Term(self.root, args)

    def check_if_legal_replacement(self, forbidden_variables: AbstractSet[str]) -> Union[Term, None]:
        if is_constant(self.root) or is_variable(self.root):
            if self.root in forbidden_variables:
                return self
            else:
                return None
        else:
            for arg in self.arguments:
                current = arg.check_if_legal_replacement(forbidden_variables)
                if current is not None:
                    return current
            return None


def is_equality(s: str) -> bool:
    """Checks if the given string is the equality relation.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is the equality relation, ``False``
        otherwise.
    """
    return s == '='


def is_relation(s: str) -> bool:
    """Checks if the given string is a relation name.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a relation name, ``False`` otherwise.
    """
    return s[0] >= 'F' and s[0] <= 'T' and s.isalnum()


def is_unary(s: str) -> bool:
    """Checks if the given string is a unary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a unary operator, ``False`` otherwise.
    """
    return s == '~'


def is_binary(s: str) -> bool:
    """Checks if the given string is a binary operator.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a binary operator, ``False`` otherwise.
    """
    return s == '&' or s == '|' or s == '->'


def is_quantifier(s: str) -> bool:
    """Checks if the given string is a quantifier.

    Parameters:
        s: string to check.

    Returns:
        ``True`` if the given string is a quantifier, ``False`` otherwise.
    """
    return s == 'A' or s == 'E'


@frozen
class Formula:
    """An immutable first-order formula in tree representation, composed from
    relation names applied to first-order terms, and operators and
    quantifications applied to them.

    Attributes:
        root (`str`): the relation name, equality relation, operator, or
            quantifier at the root of the formula tree.
        arguments (`~typing.Optional`\\[`~typing.Tuple`\\[`Term`, ...]]): the
            arguments to the root, if the root is a relation name or the
            equality relation.
        first (`~typing.Optional`\\[`Formula`]): the first operand to the root,
            if the root is a unary or binary operator.
        second (`~typing.Optional`\\[`Formula`]): the second
            operand to the root, if the root is a binary operator.
        variable (`~typing.Optional`\\[`str`]): the variable name quantified by
            the root, if the root is a quantification.
        predicate (`~typing.Optional`\\[`Formula`]): the predicate quantified by
            the root, if the root is a quantification.
    """
    root: str
    arguments: Optional[Tuple[Term, ...]]
    first: Optional[Formula]
    second: Optional[Formula]
    variable: Optional[str]
    predicate: Optional[Formula]

    def __init__(self, root: str,
                 arguments_or_first_or_variable: Union[Sequence[Term],
                                                       Formula, str],
                 second_or_predicate: Optional[Formula] = None) -> None:
        """Initializes a `Formula` from its root and root arguments, root
        operands, or root quantified variable and predicate.

        Parameters:
            root: the root for the formula tree.
            arguments_or_first_or_variable: the arguments to the the root, if
                the root is a relation name or the equality relation; the first
                operand to the root, if the root is a unary or binary operator;
                the variable name quantified by the root, if the root is a
                quantification.
            second_or_predicate: the second operand to the root, if the root is
                a binary operator; the predicate quantified by the root, if the
                root is a quantification.
        """
        if is_equality(root) or is_relation(root):
            # Populate self.root and self.arguments
            assert second_or_predicate is None
            assert isinstance(arguments_or_first_or_variable, Sequence) and \
                   not isinstance(arguments_or_first_or_variable, str)
            self.root, self.arguments = \
                root, tuple(arguments_or_first_or_variable)
            if is_equality(root):
                assert len(self.arguments) == 2
        elif is_unary(root):
            # Populate self.first
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is None
            self.root, self.first = root, arguments_or_first_or_variable
        elif is_binary(root):
            # Populate self.first and self.second
            assert isinstance(arguments_or_first_or_variable, Formula) and \
                   second_or_predicate is not None
            self.root, self.first, self.second = \
                root, arguments_or_first_or_variable, second_or_predicate
        else:
            assert is_quantifier(root)
            # Populate self.variable and self.predicate
            assert isinstance(arguments_or_first_or_variable, str) and \
                   is_variable(arguments_or_first_or_variable) and \
                   second_or_predicate is not None
            self.root, self.variable, self.predicate = \
                root, arguments_or_first_or_variable, second_or_predicate

    def __repr__(self) -> str:
        """Computes the string representation of the current formula.

        Returns:
            The standard string representation of the current formula.
        """
        if is_equality(self.root):
            return repr(self.arguments[0]) + self.root + repr(self.arguments[1])
        if is_relation(self.root):
            return self.root + "(" + ','.join([repr(arg) for arg in self.arguments]) + ")"
        if is_unary(self.root):
            return self.root + repr(self.first)
        if is_binary(self.root):
            return '(' + repr(self.first) + self.root + repr(self.second) + ')'
        else:
            return self.root + self.variable + '[' + repr(self.predicate) + ']'

    def __eq__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is a `Formula` object that equals the
            current formula, ``False`` otherwise.
        """
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        """Compares the current formula with the given one.

        Parameters:
            other: object to compare to.

        Returns:
            ``True`` if the given object is not a `Formula` object or does not
            equal the current formula, ``False`` otherwise.
        """
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @staticmethod
    def parse_prefix(s: str) -> Tuple[Formula, str]:
        """Parses a prefix of the given string into a formula.

        Parameters:
            s: string to parse, which has a prefix that is a valid
                representation of a formula.

        Returns:
            A pair of the parsed formula and the unparsed suffix of the string.
            If the given string has as a prefix a term followed by an equality
            followed by a constant name (e.g., ``'c12'``) or by a variable name
            (e.g., ``'x12'``), then the parsed prefix will include that entire
            name (and not just a part of it, such as ``'x1'``).
        """
        if is_unary(s[0]):
            first, tail = Formula.parse_prefix(s[1:])
            return Formula(s[0], first), tail
        if is_relation(s[0]):
            relation_name = re.findall(r"[a-zA-Z0-9]+", s)[0]
            nested_args = get_nested_str(s[len(relation_name):])
            tail = s[len(relation_name) + len(nested_args) + 2:] if len(relation_name) + len(nested_args) + 2 < len(
                s) else ""
            return Formula(relation_name,
                           [Term.parse(arg) for arg in split_without_nested_args(nested_args)]), tail
        if s[0] == '(':  # binary
            head = "(" + get_nested_str(s) + ")"
            tail = s[len(head):] if len(head) < len(s) else ""
            t = find_main_operator(head)
            return Formula(
                s[t[0]:t[1]],
                Formula.parse_prefix(head[1:t[0]])[0],
                Formula.parse_prefix(head[t[1]:len(head) - 1])[0],
            ), tail
        if is_quantifier(s[0]):
            quantifier = s[0]
            variable = re.findall(r'[a-z0-9]+|_]', s[1:])[0]
            predicate = get_nested_str(s[len(variable) + 1:], '[', ']')
            tail = s[len(quantifier) + len(variable) + len(predicate) + 2:]
            return Formula(quantifier, variable, Formula.parse_prefix(predicate)[0]), tail
        else:  # equality
            equal_ind = s.find("=")
            first_term = s[:equal_ind]
            second_term = s[equal_ind + 1:]
            first_arg = Term.parse_prefix(first_term)[0]
            second_arg, tail = Term.parse_prefix(second_term)
            return Formula('=', [first_arg, second_arg]), tail

    @staticmethod
    def parse(s: str) -> Formula:
        """Parses the given valid string representation into a formula.

        Parameters:
            s: string to parse.

        Returns:
            A formula whose standard string representation is the given string.
        """
        # Task 7.4.2
        return Formula.parse_prefix(s)[0]

    def constants(self) -> Set[str]:
        """Finds all constant names in the current formula.

        Returns:
            A set of all constant names used in the current formula.
        """
        if is_unary(self.root):
            return self.first.constants()
        if is_relation(self.root):
            return reduce(lambda a, b: a.union(b),
                          [arg.constants() for arg in self.arguments]) if self.arguments else set()
        if is_binary(self.root):
            return self.first.constants().union(self.second.constants())
        if is_quantifier(self.root):
            return self.predicate.constants()
        else:  # equality
            return reduce(lambda a, b: a.union(b),
                          [arg.constants() for arg in self.arguments]) if self.arguments else set()

    def variables(self) -> Set[str]:
        """Finds all variable names in the current formula.

        Returns:
            A set of all variable names used in the current formula.
        """
        if is_unary(self.root):
            return self.first.variables()
        if is_relation(self.root):
            return reduce(lambda a, b: a.union(b),
                          [arg.variables() for arg in self.arguments]) if self.arguments else set()
        if is_binary(self.root):
            return self.first.variables().union(self.second.variables())
        if is_quantifier(self.root):
            return {self.variable}.union(self.predicate.variables())
        else:  # equality
            return reduce(lambda a, b: a.union(b),
                          [arg.variables() for arg in self.arguments]) if self.arguments else set()

    def free_variables(self) -> Set[str]:
        """Finds all variable names that are free in the current formula.

        Returns:
            A set of all variable names used in the current formula not only
            within a scope of a quantification on those variable names.
        """
        if is_unary(self.root):
            return self.first.free_variables()
        if is_relation(self.root):
            return reduce(lambda a, b: a.union(b),
                          [arg.variables() for arg in self.arguments]) if self.arguments else set()
        if is_binary(self.root):
            return self.first.free_variables().union(self.second.free_variables())
        if is_quantifier(self.root):
            return self.predicate.free_variables().difference({self.variable})
        else:  # equality
            return reduce(lambda a, b: a.union(b), [arg.variables() for arg in self.arguments])

    def functions(self) -> Set[Tuple[str, int]]:
        """Finds all function names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of function name and arity (number of arguments) for
            all function names used in the current formula.
        """
        if is_unary(self.root):
            return self.first.functions()
        if is_relation(self.root):
            return reduce(lambda a, b: a.union(b),
                          [arg.functions() for arg in self.arguments]) if self.arguments else set()
        if is_binary(self.root):
            return self.first.functions().union(self.second.functions())
        if is_quantifier(self.root):
            return self.predicate.functions()
        else:  # equality
            return reduce(lambda a, b: a.union(b), [arg.functions() for arg in self.arguments])

    def relations(self) -> Set[Tuple[str, int]]:
        """Finds all relation names in the current formula, along with their
        arities.

        Returns:
            A set of pairs of relation name and arity (number of arguments) for
            all relation names used in the current formula.
        """
        if is_unary(self.root):
            return self.first.relations()
        if is_relation(self.root):
            return {(self.root, len(self.arguments))}
        if is_binary(self.root):
            return self.first.relations().union(self.second.relations())
        if is_quantifier(self.root):
            return self.predicate.relations()
        else:  # equality
            return set()

    def substitute(self, substitution_map: Mapping[str, Term],
                   forbidden_variables: AbstractSet[str] = frozenset()) -> Formula:
        """Substitutes in the current formula, each constant name `name` or free
        occurrence of variable name `name` that is a key in `substitution_map`
        with the term `substitution_map[name]`.

        Parameters:
            substitution_map: mapping defining the substitutions to be
                performed.
            forbidden_variables: variables not allowed in substitution terms.

        Returns:
            The formula resulting from performing all substitutions. Only
            constant names and variable names originating in the current formula
            are substituted (i.e., those originating in one of the specified
            substitutions are not subjected to additional substitutions).

        Raises:
            ForbiddenVariableError: If a term that is used in the requested
                substitution contains a variable from `forbidden_variables`
                or a variable occurrence that becomes bound when that term is
                substituted into the current formula.

        Examples:
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,x)'), 'x': Term.parse('c')}, {'z'})
            Ay[c=plus(d,x)]
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,z)')}, {'z'})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: z
            >>> Formula.parse('Ay[x=c]').substitute(
            ...     {'c': Term.parse('plus(d,y)')})
            Traceback (most recent call last):
              ...
            predicates.syntax.ForbiddenVariableError: y
        """
        for element_name in substitution_map:
            assert is_constant(element_name) or is_variable(element_name)
        for variable in forbidden_variables:
            assert is_variable(variable)

        if is_unary(self.root):
            return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables))
        elif is_binary(self.root):
            return Formula(self.root, self.first.substitute(substitution_map, forbidden_variables),
                           self.second.substitute(substitution_map, forbidden_variables))
        elif is_quantifier(self.root):
            # if self.variable in substitution_map:
            #     raise ForbiddenVariableError(self.variable)
            return Formula(self.root, self.variable,
                           self.predicate.substitute(substitution_map, {*forbidden_variables, self.variable}))
        elif is_equality(self.root):
            left = self.arguments[0]
            right = self.arguments[1]
            return Formula(self.root,
                           arguments_or_first_or_variable=[
                               left.substitute(substitution_map, forbidden_variables),
                               right.substitute(substitution_map, forbidden_variables)
                           ])
        else:  # relation
            args = []
            for arg in self.arguments:
                args.append(arg.substitute(substitution_map, forbidden_variables))
            return Formula(self.root, args)

    def propositional_skeleton(self) -> Tuple[PropositionalFormula,
                                              Mapping[str, Formula]]:
        """Computes a propositional skeleton of the current formula.

        Returns:
            A pair. The first element of the pair is a propositional formula
            obtained from the current formula by substituting every (outermost)
            subformula that has a relation or quantifier at its root with an
            atomic propositional formula, consistently such that multiple equal
            such (outermost) subformulas are substituted with the same atomic
            propositional formula. The atomic propositional formulas used for
            substitution are obtained, from left to right, by calling
            `next`\ ``(``\ `~logic_utils.fresh_variable_name_generator`\ ``)``.
            The second element of the pair is a map from each atomic
            propositional formula to the subformula for which it was
            substituted.
        """

        return self._propositional_skeleton_helper(dict())

    def _propositional_skeleton_helper(self, mapping: Dict[str, Formula]) -> Tuple[PropositionalFormula,
                                                                                   Mapping[str, Formula]]:

        for k in mapping:
            if mapping[k] == self:
                return PropositionalFormula(k), mapping
        if is_quantifier(self.root) or is_relation(self.root) or is_equality(self.root):
            z1 = next(fresh_variable_name_generator)
            mapping[z1] = self
            return PropositionalFormula(z1), mapping
        elif is_unary(self.root):
            formula, dic = self.first._propositional_skeleton_helper(mapping)
            return PropositionalFormula(self.root, formula), {**mapping, **dic}
        elif is_binary(self.root):
            formula1, dic1 = self.first._propositional_skeleton_helper(mapping)
            mapping = {**dic1, **mapping}
            formula2, dic2 = self.second._propositional_skeleton_helper(mapping)
            mapping = {**dic2, **mapping}
            return PropositionalFormula(self.root, formula1, formula2), mapping

    @staticmethod
    def from_propositional_skeleton(skeleton: PropositionalFormula,
                                    substitution_map: Mapping[str, Formula]) -> \
            Formula:
        """Computes a first-order formula from a propositional skeleton and a
        substitution map.

        Arguments:
            skeleton: propositional skeleton for the formula to compute.
            substitution_map: a map from each atomic propositional subformula
                of the given skeleton to a first-order formula.

        Returns:
            A first-order formula obtained from the given propositional skeleton
            by substituting each atomic propositional subformula with the formula
            mapped to it by the given map.
        """
        for key in substitution_map:
            assert is_propositional_variable(key)

        if is_unary(skeleton.root):
            return Formula(skeleton.root, Formula.from_propositional_skeleton(skeleton.first, substitution_map))
        elif is_binary(skeleton.root):
            return Formula(skeleton.root, Formula.from_propositional_skeleton(skeleton.first, substitution_map),
                           Formula.from_propositional_skeleton(skeleton.second, substitution_map))
        else:  # var
            return substitution_map[skeleton.root]
