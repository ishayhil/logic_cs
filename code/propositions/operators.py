# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulae to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *


class NotAndOr:
    def __init__(self):
        pass

    implies_map = {
        '->': Formula.parse("(~p|q)"),
    }

    and_or_not = {
        '+': Formula.parse("((~p&q)|(p&~q))"),
        '-&': Formula.parse("~(p&q)"),
        '-|': Formula.parse("~(p|q)"),
        **implies_map,
        '<->': Formula.parse("((p->q)&(q->p))"),
        'F': Formula.parse("(~p&p)"),
        'T': Formula.parse("(~p|p)"),
    }


or_to_and_not = {
    '|': Formula.parse("~(~p&~q)")
}


def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """

    return formula.substitute_operators(
        {k: v.substitute_operators(NotAndOr.implies_map) for k, v in NotAndOr.and_or_not.items()}
    )


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """

    this_map = {
        **{k: v.substitute_operators(NotAndOr.implies_map).substitute_operators(or_to_and_not) for k, v in
           NotAndOr.and_or_not.items()},
        **or_to_and_not
    }
    return formula.substitute_operators(this_map)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    not_map = {
        '~': Formula.parse("(p-&p)"),
    }

    and_map = {
        '&': Formula.parse("~(p-&q)").substitute_operators(not_map),
    }

    or_map = {
        '|': Formula.parse("(p|q)").substitute_operators(or_to_and_not).substitute_operators(
            and_map).substitute_operators(not_map),
    }

    implies_map = {
        '->': NotAndOr.and_or_not['->'].substitute_operators(not_map).substitute_operators(or_map)
    }

    nor_map = {
        '-|': NotAndOr.and_or_not['-|'].substitute_operators(and_map).substitute_operators(
            or_map).substitute_operators(not_map)
    }

    xor_map = {
        '+': NotAndOr.and_or_not['+'].substitute_operators(and_map).substitute_operators(
            or_map).substitute_operators(not_map)
    }

    iff_map = {
        '<->': NotAndOr.and_or_not['<->'].substitute_operators(implies_map).substitute_operators(and_map),
    }

    nand_map = {
        **or_map,
        **not_map,
        **and_map,
        **xor_map,
        **nor_map,
        **implies_map,
        **iff_map,
        'T': NotAndOr.and_or_not['T'].substitute_operators(or_map).substitute_operators(and_map).substitute_operators(
            not_map),
        'F': NotAndOr.and_or_not['F'].substitute_operators(or_map).substitute_operators(and_map).substitute_operators(
            not_map),
    }

    return formula.substitute_operators(nand_map)


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    and_map = {
        '&': Formula.parse("~(p->~q)")
    }

    or_map = {
        '|': Formula.parse('(p|q)').substitute_operators(or_to_and_not).substitute_operators(and_map)
    }

    nor_map = {
        '-|': Formula('~', or_map['|'])
    }

    xor_map = {
        '+': NotAndOr.and_or_not['+'].substitute_operators(and_map).substitute_operators(or_map)
    }

    nand_map = {
        '-&': Formula('~', and_map['&'])
    }

    iff_map = {
        '<->': NotAndOr.and_or_not['<->'].substitute_operators(NotAndOr.implies_map).substitute_operators(
            and_map).substitute_operators(or_map)
    }

    implies_not_map = {
        **and_map,
        **or_map,
        **nor_map,
        **nand_map,
        **xor_map,
        **iff_map,
        'F': NotAndOr.and_or_not['F'].substitute_operators(and_map),
        'T': NotAndOr.and_or_not['T'].substitute_operators(or_map)
    }

    return formula.substitute_operators(implies_not_map)


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Return:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    and_map = {
        '&': Formula.parse('((q->(p->F))->F)')
    }

    not_map = {
        '~': Formula.parse('(p->F)')
    }

    or_map = {
        '|': Formula.parse('(p|q)').substitute_operators(or_to_and_not).substitute_operators(
            and_map).substitute_operators(not_map)
    }

    nor_map = {
        '-|': NotAndOr.and_or_not['-|'].substitute_operators(or_map).substitute_operators(and_map).substitute_operators(
            not_map)
    }

    xor_map = {
        '+': NotAndOr.and_or_not['+'].substitute_operators(and_map).substitute_operators(or_map).substitute_operators(
            not_map)
    }

    nand_map = {
        '-&': NotAndOr.and_or_not['-&'].substitute_operators(and_map).substitute_operators(or_map).substitute_operators(
            not_map)
    }

    iff_map = {
        '<->': NotAndOr.and_or_not['<->'].substitute_operators(NotAndOr.implies_map).substitute_operators(
            and_map).substitute_operators(or_map).substitute_operators(not_map)
    }

    implies_false_map = {
        **and_map,
        **not_map,
        **or_map,
        **nor_map,
        **nand_map,
        **xor_map,
        **iff_map,
        'T': Formula.parse('(F->p)')
    }

    return formula.substitute_operators(implies_false_map)
