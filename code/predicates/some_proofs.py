# (c) This file is part of the course
# Mathematical Logic through Programming
# by Gonczarowski and Nisan.
# File name: predicates/some_proofs.py

from predicates.syntax import *
from predicates.proofs import *
from predicates.prover import *


# from predicates.deduction import *
# from predicates.prenex import equivalence_of

def syllogism_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_instantiated_assumption(
        '(Ax[(Man(x)->Mortal(x))]->(Man(aristotle)->Mortal(aristotle)))',
        Prover.UI, {'R': '(Man(_)->Mortal(_))', 'c': 'aristotle'})
    step3 = prover.add_mp('(Man(aristotle)->Mortal(aristotle))', step1, step2)
    step4 = prover.add_assumption('Man(aristotle)')
    step5 = prover.add_mp('Mortal(aristotle)', step4, step3)
    return prover.qed()


def syllogism_proof_with_universal_instantiation(print_as_proof_forms: bool =
                                                 False) -> Proof:
    """Using the method `~predicates.prover.Prover.add_universal_instantiation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Aristotle is a man (``'Man(aristotle)'``)

    the conclusion: Aristotle is mortal (``'Mortal(aristotle)'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_universal_instantiation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Man(aristotle)'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_universal_instantiation(
        '(Man(aristotle)->Mortal(aristotle))', step1, 'aristotle')
    step3 = prover.add_assumption('Man(aristotle)')
    step4 = prover.add_mp('Mortal(aristotle)', step3, step2)
    return prover.qed()


def syllogism_all_all_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautology(
        '((Greek(x)->Human(x))->((Human(x)->Mortal(x))->(Greek(x)->Mortal(x))))')
    step6 = prover.add_mp(
        '((Human(x)->Mortal(x))->(Greek(x)->Mortal(x)))', step2, step5)
    step7 = prover.add_mp('(Greek(x)->Mortal(x))', step4, step6)
    step8 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step7)
    return prover.qed()


def syllogism_all_all_proof_with_tautological_implication(print_as_proof_forms:
bool = False) -> \
        Proof:
    """Using the method
    `~predicates.prover.Prover.add_tautological_implication`, proves from the
    assumptions:

    1. All Greeks are human (``'Ax[(Greek(x)->Human(x))]'``), and
    2. All humans are mortal (``'Ax[(Human(x)->Mortal(x))]'``)

    the conclusion: All Greeks are mortal (``'Ax[(Greek(x)->Mortal(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_tautological_implication`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Greek(x)->Human(x))]', 'Ax[(Human(x)->Mortal(x))]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Greek(x)->Human(x))]')
    step2 = prover.add_universal_instantiation(
        '(Greek(x)->Human(x))', step1, 'x')
    step3 = prover.add_assumption('Ax[(Human(x)->Mortal(x))]')
    step4 = prover.add_universal_instantiation(
        '(Human(x)->Mortal(x))', step3, 'x')
    step5 = prover.add_tautological_implication(
        '(Greek(x)->Mortal(x))', {step2, step4})
    step6 = prover.add_ug('Ax[(Greek(x)->Mortal(x))]', step5)
    return prover.qed()


def syllogism_all_exists_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI,
        {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_ug('Ax[(Man(x)->Ex[Mortal(x)])]', step5)
    step7 = prover.add_instantiated_assumption(
        '((Ax[(Man(x)->Ex[Mortal(x)])]&Ex[Man(x)])->Ex[Mortal(x)])', Prover.ES,
        {'R': 'Man(_)', 'Q': 'Ex[Mortal(x)]'})
    step8 = prover.add_tautological_implication(
        'Ex[Mortal(x)]', {step2, step6, step7})
    return prover.qed()


def syllogism_all_exists_proof_with_existential_derivation(print_as_proof_forms:
bool = False) -> \
        Proof:
    """Using the method `~predicates.prover.Prover.add_existential_derivation`,
    proves from the assumptions:

    1. All men are mortal (``'Ax[(Man(x)->Mortal(x))]'``), and
    2. Some men exist (``'Ex[Man(x)]'``)
    
    the conclusion: Some mortals exist (``'Ex[Mortal(x)]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof, constructed using the method
        `~predicates.prover.Prover.add_existential_derivation`, of the above
        inference via `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[(Man(x)->Mortal(x))]', 'Ex[Man(x)]'},
                    print_as_proof_forms)
    step1 = prover.add_assumption('Ax[(Man(x)->Mortal(x))]')
    step2 = prover.add_assumption('Ex[Man(x)]')
    step3 = prover.add_universal_instantiation(
        '(Man(x)->Mortal(x))', step1, 'x')
    step4 = prover.add_instantiated_assumption(
        '(Mortal(x)->Ex[Mortal(x)])', Prover.EI, {'R': 'Mortal(_)', 'c': 'x'})
    step5 = prover.add_tautological_implication(
        '(Man(x)->Ex[Mortal(x)])', {step3, step4})
    step6 = prover.add_existential_derivation('Ex[Mortal(x)]', step2, step5)
    return prover.qed()


def lovers_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. Everybody loves somebody (``'Ax[Ey[Loves(x,y)]]'``), and
    2. Everybody loves a lover (``'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'``)
    
    the conclusion: Everybody loves everybody (``'Ax[Az[Loves(z,x)]]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'Ax[Ey[Loves(x,y)]]',
                     'Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]'},
                    print_as_proof_forms)
    # Task 10.4
    # Ey[Loves(x,y)]
    step1 = prover.add_assumption('Ax[Ey[Loves(x,y)]]')
    step2 = prover.add_universal_instantiation('Ey[Loves(x,y)]', step1, 'x')
    # (Loves(x,y)->Loves(z,x))
    step3 = prover.add_assumption('Ax[Az[Ay[(Loves(x,y)->Loves(z,x))]]]')
    step4 = prover.add_universal_instantiation('Az[Ay[(Loves(x,y)->Loves(z,x))]]', step3, 'x')
    step5 = prover.add_universal_instantiation('Ay[(Loves(x,y)->Loves(z,x))]', step4, 'z')
    step6 = prover.add_universal_instantiation('(Loves(x,y)->Loves(z,x))', step5, 'y')

    # Loves(z,x)
    step7 = prover.add_existential_derivation('Loves(z,x)', step2, step6)
    # AxAzLoves(z,x)
    step8 = prover.add_ug(Formula('A', 'z', Formula.parse('Loves(z,x)')), step7)
    step9 = prover.add_ug(Formula('A', 'x', Formula('A', 'z', Formula.parse('Loves(z,x)'))), step8)
    return prover.qed()


def homework_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the assumptions:

    1. No homework is fun (``'~Ex[(Homework(x)&Fun(x))]'``), and
    2. Some reading is homework (``'Ex[(Homework(x)&Reading(x))]'``)
    
    the conclusion: Some reading is not fun (``'Ex[(Reading(x)&~Fun(x))]'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({'~Ex[(Homework(x)&Fun(x))]',
                     'Ex[(Homework(x)&Reading(x))]'}, print_as_proof_forms)
    # Task 10.5
    # p -> q
    p_q_formula = Formula.parse('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])')
    step1 = prover.add_instantiated_assumption('((Homework(x)&Fun(x))->Ex[(Homework(x)&Fun(x))])',
                                               Prover.EI,
                                               {
                                                   'c': Term('x'),
                                                   'R': Formula('&', Formula('Homework', [Term('_')]),
                                                                Formula('Fun', [Term('_')]))
                                               })
    # ~q -> ~p
    consequent = Formula.parse('~(Homework(x)&Fun(x))')
    not_q_p_formula = Formula('->', Formula.parse('~Ex[(Homework(x)&Fun(x))]'), consequent)
    step2 = prover.add_tautology(Formula('->', p_q_formula, not_q_p_formula))
    step3 = prover.add_mp(not_q_p_formula, step1, step2)
    # add assumption
    step4 = prover.add_assumption('~Ex[(Homework(x)&Fun(x))]')
    step5 = prover.add_mp(consequent, step4, step3)

    # implication
    step6 = prover.add_instantiated_assumption(Formula.parse('((Reading(x)&~Fun(x))->Ex[(Reading(x)&~Fun(x))])'),
                                               Prover.EI,
                                               {
                                                   'c': Term('x'),
                                                   'R': Formula.parse('(Reading(_)&~Fun(_))')
                                               })
    # ((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])
    step7 = prover.add_tautological_implication('((Homework(x)&Reading(x))->Ex[(Reading(x)&~Fun(x))])',
                                                {step5, step6})

    # second assumption
    step8 = prover.add_assumption('Ex[(Homework(x)&Reading(x))]')
    # derive final conclusion
    prover.add_existential_derivation('Ex[(Reading(x)&~Fun(x))]',
                                      step8, step7)

    return prover.qed()


#: The three group axioms
GROUP_AXIOMS = frozenset({'plus(0,x)=x', 'plus(minus(x),x)=0',
                          'plus(plus(x,y),z)=plus(x,plus(y,z))'})


def right_neutral_proof(stop_before_flipped_equality: bool,
                        stop_before_free_instantiation: bool,
                        stop_before_substituted_equality: bool,
                        stop_before_chained_equality: bool,
                        print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms that x+0=x (``'plus(x,0)=x'``).

    Parameters:
        stop_before_flipped_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_flipped_equality` and to return the
            prefix of the proof constructed up to that point.
        stop_before_free_instantiation: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_free_instantiation` and to return the
            prefix of the proof constructed up to that point.
        stop_before_substituted_equality: flag specifying stop proving just
            before the first call to
            `~predicates.prover.Prover.add_substituted_equality` and to return
            the prefix of the proof constructed up to that point.
        stop_before_chained_equality: flag specifying to stop proving just
            before the first call to
            `~predicates.prover.Prover.add_chained_equality` and to return the
            prefix of the proof constructed up to that point.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(GROUP_AXIOMS, print_as_proof_forms)
    zero = prover.add_assumption('plus(0,x)=x')
    negation = prover.add_assumption('plus(minus(x),x)=0')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    if stop_before_flipped_equality:
        return prover.qed()
    flipped_zero = prover.add_flipped_equality('x=plus(0,x)', zero)
    flipped_negation = prover.add_flipped_equality(
        '0=plus(minus(x),x)', negation)
    flipped_associativity = prover.add_flipped_equality(
        'plus(x,plus(y,z))=plus(plus(x,y),z)', associativity)
    if stop_before_free_instantiation:
        return prover.qed()
    step7 = prover.add_free_instantiation(
        '0=plus(minus(minus(x)),minus(x))', flipped_negation, {'x': 'minus(x)'})
    step8 = prover.add_flipped_equality(
        'plus(minus(minus(x)),minus(x))=0', step7)
    step9 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),minus(x)),x)='
        'plus(minus(minus(x)),plus(minus(x),x))',
        associativity, {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step10 = prover.add_free_instantiation('plus(0,0)=0', zero, {'x': '0'})
    step11 = prover.add_free_instantiation(
        'plus(x,0)=plus(0,plus(x,0))', flipped_zero, {'x': 'plus(x,0)'})
    step12 = prover.add_free_instantiation(
        'plus(0,plus(x,0))=plus(plus(0,x),0)', flipped_associativity,
        {'x': '0', 'y': 'x', 'z': '0'})
    if stop_before_substituted_equality:
        return prover.qed()
    step13 = prover.add_substituted_equality(
        'plus(plus(0,x),0)=plus(plus(plus(minus(minus(x)),minus(x)),x),0)',
        step7, 'plus(plus(_,x),0)')
    step14 = prover.add_substituted_equality(
        'plus(plus(plus(minus(minus(x)),minus(x)),x),0)='
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)',
        step9, 'plus(_,0)')
    step15 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),plus(minus(x),x)),0)='
        'plus(plus(minus(minus(x)),0),0)',
        negation, 'plus(plus(minus(minus(x)),_),0)')
    step16 = prover.add_free_instantiation(
        'plus(plus(minus(minus(x)),0),0)=plus(minus(minus(x)),plus(0,0))',
        associativity, {'x': 'minus(minus(x))', 'y': '0', 'z': '0'})
    step17 = prover.add_substituted_equality(
        'plus(minus(minus(x)),plus(0,0))=plus(minus(minus(x)),0)',
        step10, 'plus(minus(minus(x)),_)')
    step18 = prover.add_substituted_equality(
        'plus(minus(minus(x)),0)=plus(minus(minus(x)),plus(minus(x),x))',
        flipped_negation, 'plus(minus(minus(x)),_)')
    step19 = prover.add_free_instantiation(
        'plus(minus(minus(x)),plus(minus(x),x))='
        'plus(plus(minus(minus(x)),minus(x)),x)', flipped_associativity,
        {'x': 'minus(minus(x))', 'y': 'minus(x)', 'z': 'x'})
    step20 = prover.add_substituted_equality(
        'plus(plus(minus(minus(x)),minus(x)),x)=plus(0,x)', step8, 'plus(_,x)')
    if stop_before_chained_equality:
        return prover.qed()
    step21 = prover.add_chained_equality(
        'plus(x,0)=x',
        [step11, step12, step13, step14, step15, step16, step17, step18, step19,
         step20, zero])
    return prover.qed()


def unique_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the group axioms and from the assumption a+c=a
    (``'plus(a,c)=a'``) that c=0 (``'c=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    # Task 10.10
    # a+c=a
    # 0+c=0
    # c=
    # 0+a=a
    # a+c=0+a
    # -a+a+c=-a+0+a
    # 0+c=0+-a+a
    # c = 0
    prover = Prover(GROUP_AXIOMS.union({'plus(a,c)=a'}), print_as_proof_forms)
    step1 = prover.add_assumption('plus(0,x)=x')
    step2 = prover.add_assumption('plus(a,c)=a')
    step3 = prover.add_free_instantiation('plus(0,a)=a', step1, {'x': 'a'})
    step4 = prover.add_flipped_equality("a=plus(0,a)", step3)
    step5 = prover.add_chained_equality('plus(a,c)=plus(0,a)', [step2, step4])
    step6 = prover.add_substituted_equality('plus(minus(a),plus(a,c))=plus(minus(a),plus(0,a))', step5,
                                            'plus(minus(a),_)')
    step7 = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    step8 = prover.add_free_instantiation('plus(plus(minus(a),a),c)=plus(minus(a),plus(a,c))',
                                          step7,
                                          {'x': 'minus(a)', 'y': 'a', 'z': 'c'}
                                          )
    ##
    step9 = prover.add_chained_equality('plus(plus(minus(a),a),c)=plus(minus(a),plus(0,a))', [step8, step6])
    ##
    step10 = prover.add_assumption("plus(minus(x),x)=0")
    step11 = prover.add_free_instantiation('plus(minus(a),a)=0', step10, {"x": "a"})
    step12 = prover.add_substituted_equality('plus(plus(minus(a),a),c)=plus(0,c)', step11, 'plus(_,c)')
    step13 = prover.add_free_instantiation('plus(0,c)=c', step1, {"x": "c"})
    step14 = prover.add_chained_equality('plus(plus(minus(a),a),c)=c', [step12, step13])
    ##
    step15 = prover.add_flipped_equality('c=plus(plus(minus(a),a),c)', step14)
    ##
    step16 = prover.add_substituted_equality("plus(minus(a),plus(0,a))=plus(minus(a),a)", step3, 'plus(minus(a),_)')
    step17 = prover.add_chained_equality('plus(minus(a),plus(0,a))=0', [step16, step11])
    step17 = prover.add_chained_equality('c=0', [step15, step9, step17])
    return prover.qed()


#: The six field axioms
FIELD_AXIOMS = frozenset(GROUP_AXIOMS.union(
    {'plus(x,y)=plus(y,x)', 'times(x,1)=x', 'times(x,y)=times(y,x)',
     'times(times(x,y),z)=times(x,times(y,z))', '(~x=0->Ey[times(y,x)=1])',
     'times(x,plus(y,z))=plus(times(x,y),times(x,z))'}))


def multiply_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the field axioms that 0*x=0 (``'times(0,x)=0'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    # 0+x=x
    # 0(0+x)=0*x
    # 0*0+0*x=0*x
    # 0*0 = 0*x-0*x
    # 0*0 = x(0-0)
    # 0*0 = x*0

    # 0*x-0*x = 0

    # 0+0=0
    # 0*0+0*0=0*0
    # 0*0=0
    # 0*0
    prover = Prover(FIELD_AXIOMS, print_as_proof_forms)
    # Task 10.11
    zero_axiom = prover.add_assumption('plus(0,x)=x')
    associativity = prover.add_assumption('plus(plus(x,y),z)=plus(x,plus(y,z))')
    neg = prover.add_assumption('plus(minus(x),x)=0')
    dist = prover.add_assumption('times(x,plus(y,z))=plus(times(x,y),times(x,z))')
    comm = prover.add_assumption('times(x,y)=times(y,x)')

    # 0 + 0 = 0
    step1 = prover.add_free_instantiation('plus(0,0)=0',
                                          zero_axiom,
                                          {'x': '0'})
    # x(0+0) = x*0
    step2 = prover.add_substituted_equality('times(x,plus(0,0))=times(x,0)',
                                            step1,
                                            'times(x,_)')
    # -x*0+x*0 = 0
    step3 = prover.add_free_instantiation('plus(minus(times(x,0)),times(x,0))=0',
                                          neg,
                                          {'x': 'times(x,0)'})
    # x*(0+0) = x*0 + x*0
    step4 = prover.add_free_instantiation('times(x,plus(0,0))=plus(times(x,0),times(x,0))',
                                          dist,
                                          {
                                              'x': 'x',
                                              'y': '0',
                                              'z': '0'
                                          })
    # x*0 + x*0 = x(0+0)
    step5 = prover.add_flipped_equality('plus(times(x,0),times(x,0))=times(x,plus(0,0))',
                                        step4)
    # x0+x0 = x0
    step6 = prover.add_chained_equality('plus(times(x,0),times(x,0))=times(x,0)',
                                        [step5, step2])
    # -x*0 + (x*0+x*0) = -x*0 + x*0
    step7 = prover.add_substituted_equality(
        'plus(minus(times(x,0)),plus(times(x,0),times(x,0)))=plus(minus(times(x,0)),times(x,0))',
        step6,
        'plus(minus(times(x,0)),_)')
    # (-x*0+x0) + x*0 = -x*0 + (x*0 + x*0)
    step8 = prover.add_free_instantiation(
        'plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(minus(times(x,0)),plus(times(x,0),times(x,0)))',
        associativity,
        {
            'x': 'minus(times(x,0))',
            'y': 'times(x,0)',
            'z': 'times(x,0)'
        })
    # (-*x0+x*0)+x0 = 0+x*0
    step9 = prover.add_substituted_equality('plus(plus(minus(times(x,0)),times(x,0)),times(x,0))=plus(0,times(x,0))',
                                            step3,
                                            'plus(_,times(x,0))')
    # flip to obtain 0+x*0 = (-x*0+x*0)+x*0
    step10 = prover.add_flipped_equality('plus(0,times(x,0))=plus(plus(minus(times(x,0)),times(x,0)),times(x,0)))',
                                         step9)
    # 0 + x*0 = x*0
    step11 = prover.add_free_instantiation('plus(0,times(x,0))=times(x,0)',
                                           zero_axiom,
                                           {'x': 'times(x,0)'})
    # flip to obtain x*0 = 0+x*0
    step12 = prover.add_flipped_equality('times(x,0)=plus(0,times(x,0))',
                                         step11)
    # 0x = x*0
    step13 = prover.add_free_instantiation('times(0,x)=times(x,0)',
                                           comm,
                                           {'x': '0', 'y': 'x'})
    step14 = prover.add_chained_equality('times(0,x)=0', [step13, step12, step10, step8, step7, step3])
    return prover.qed()


#: The induction axiom
INDUCTION_AXIOM = Schema(
    Formula.parse('((R(0)&Ax[(R(x)->R(s(x)))])->Ax[R(x)])'), {'R'})
#: The six axioms of Peano arithmetic
PEANO_AXIOMS = frozenset({'(s(x)=s(y)->x=y)', '(~x=0->Ey[s(y)=x])', '~s(x)=0',
                          'plus(x,0)=x', 'plus(x,s(y))=s(plus(x,y))',
                          'times(x,0)=0', 'times(x,s(y))=plus(times(x,y),x)',
                          INDUCTION_AXIOM})


def peano_zero_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms of Peano arithmetic that 0+x=x
    (``'plus(0,x)=x'``).

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover(PEANO_AXIOMS, print_as_proof_forms)
    # Task 10.12
    step1 = prover.add_assumption('plus(x,0)=x')  # Axiom 4
    # 0+0=0
    step2 = prover.add_free_instantiation('plus(0,0)=0', step1, {'x': '0'})
    # 0+x=x -> (s(0+x)=s(0+x) -> s(0+x) = s(x))
    step3 = prover.add_instantiated_assumption('(plus(0,x)=x->(s(plus(0,x))=s(plus(0,x))->s(plus(0,x))=s(x))',
                                               Prover.ME,
                                               {'c': 'plus(0,x)',
                                                'd': 'x',
                                                'R': 's(plus(0,x))=s(_)'})
    # s(0+x) = s(0+x)
    step4 = prover.add_instantiated_assumption('s(plus(0,x))=s(plus(0,x))',
                                               Prover.RX,
                                               {'c': 's(plus(0,x))'})
    # get 0+x=x -> s(0+x)=s(x)
    step5 = prover.add_tautological_implication('(plus(0,x)=x->s(plus(0,x))=s(x))',
                                                {step3, step4})
    # x+s(y) = s(x+y)
    step6 = prover.add_assumption('plus(x,s(y))=s(plus(x,y))')
    # axiom 5: 0 + s(x) = s(0+x)
    step7 = prover.add_free_instantiation('plus(0,s(x))=s(plus(0,x))',
                                          step6,
                                          {'x': '0', 'y': 'x'})
    # s(0+x)=s(x)->(0+s(x)=s(0+x)->0+s(x)=s(x)), ME
    step8 = prover.add_instantiated_assumption('(s(plus(0,x))=s(x)->(plus(0,s(x))=s(plus(0,x))->plus(0,s(x))=s(x)))',
                                               Prover.ME,
                                               {'c': 's(plus(0,x))',
                                                'd': 's(x)',
                                                'R': 'plus(0,s(x))=_'})
    # 0+x=x->0+s(x)=s(x)
    step9 = prover.add_tautological_implication('(plus(0,x)=x->plus(0,s(x))=s(x))',
                                                {step5, step7, step8})
    # Ax[0+x=x->0+s(x)=s(x)]
    step10 = prover.add_ug('Ax[(plus(0,x)=x->plus(0,s(x))=s(x))]', step9)
    # induction
    step11 = prover.add_instantiated_assumption('((plus(0,0)=0&Ax[(plus(0,x)=x->plus(0,s(x))=s(x))])->Ax[plus(0,x)=x])',
                                                INDUCTION_AXIOM,
                                                {'R': 'plus(0,_)=_'})
    # Ax[0+x=x]
    step12 = prover.add_tautological_implication('Ax[plus(0,x)=x]',
                                                 {step11, step10, step2})
    # 0+x=x
    step13 = prover.add_universal_instantiation('plus(0,x)=x', step12, Term('x'))
    return prover.qed()


#: The axiom schema of (unrestricted) comprehension
COMPREHENSION_AXIOM = Schema(
    Formula.parse('Ey[Ax[((In(x,y)->R(x))&(R(x)->In(x,y)))]]'), {'R'})


def russell_paradox_proof(print_as_proof_forms: bool = False) -> Proof:
    """Proves from the axioms schema of unrestricted comprehension the
    contradiction ``'(z=z&~z=z)'``.

    Parameters:
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    prover = Prover({COMPREHENSION_AXIOM}, print_as_proof_forms)
    # Task 10.13
    # hint
    step1 = prover.add_instantiated_assumption('Ey[Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]]',
                                               COMPREHENSION_AXIOM,
                                               {'R': '~In(_,_)'})
    mapping = {'R': Formula.parse('((In(_,y)->~In(_,_))&(~In(_,_)->In(_,y)))'),
               'x': 'x',
               'c': Term('y')}
    form = Prover.UI.instantiate(mapping)
    step2 = prover.add_instantiated_assumption(form,
                                               Prover.UI,
                                               mapping)
    step3 = prover.add_tautology('(((In(y,y)->~In(y,y))&(~In(y,y)->In(y,y)))->(z=z&~z=z))')
    step5 = prover.add_tautological_implication('(Ax[((In(x,y)->~In(x,x))&(~In(x,x)->In(x,y)))]->'
                                                '(z=z&~z=z))', {step2, step3})
    step6 = prover.add_existential_derivation('(z=z&~z=z)', step1, step5)
    return prover.qed()


def not_exists_not_implies_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(~E``\ `variable`\ ``[~``\ `formula`\ ``]->A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.1


def exists_not_implies_not_all_proof(formula: Formula, variable: str,
                                     print_as_proof_forms: bool = False) -> \
        Proof:
    """Proves that
    ``'(E``\ `variable`\ ``[~``\ `formula`\ ``]->~A``\ `variable`\ ``[``\ `formula`\ ``])'``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.2


def not_all_iff_exists_not_proof(formula: Formula, variable: str,
                                 print_as_proof_forms: bool = False) -> Proof:
    """Proves that
    `equivalence_of`\ ``('(~A``\ `variable`\ ``[``\ `formula`\ ``]', 'E``\ `variable`\ ``[~``\ `formula`\ ``]')``.

    Parameters:
        formula: predicate for the universal quantification in the formula to be
            proven.
        variable: variable name for the quantifications in the formula to be
            proven.
        print_as_proof_forms: flag specifying whether the proof is to be printed
            in real time as it is being constructed.

    Returns:
        A valid proof of the above inference via
        `~predicates.prover.Prover.AXIOMS`.
    """
    assert is_variable(variable)
    # Optional Task 11.4.3
