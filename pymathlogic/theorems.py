from .formula import Formula


def axiom_A1(num: int, F: Formula, G: Formula):
    """
    A1 axiom schema applied to formula F and G

    :param num: sequence number of new formula in inference seq
    :param F: Formula
    :param G: Formula
    :return:  Formula obj, formula annotation string
    """
    formula = F.imp(G.imp(F))
    formula.is_axiom = True
    formula.axiom_num = 1
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Axiom A1 applied to: F: {F}, G: {G}\n"
    return formula, annotation.format(num=num, formula=formula, F=F, G=G)


def axiom_A2(num: int, F: Formula, G, H):
    """
    A1 axiom schema applied to formula F and G

    :param num: sequence number of new formula in inference seq
    :param F:   Formula
    :param G:   Formula
    :param H:   Formula
    :return:    Formula obj, formula annotation string
    """
    left = F.imp(G.imp(H))
    right = (F.imp(G)).imp(F.imp(H))
    formula = left.imp(right)
    formula.is_axiom = True
    formula.axiom_num = 2
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Axiom A2 applied to: F: {F}, G: {G}, H: {H}\n"
    return formula, annotation.format(num=num, formula=formula, F=F, G=G, H=H)


def axiom_A3(num: int, F: Formula, G: Formula):
    """
    A1 axiom schema applied to formula F and G

    :param num: sequence number of new formula in inference seq
    :param F:   Formula
    :param G:   Formula
    :return:    Formula obj, formula annotation string
    """
    left = G.neg().imp(F.neg())
    right = (G.neg().imp(F)).imp(G)
    formula = left.imp(right)
    formula.is_axiom = True
    formula.axiom_num = 3
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Axiom A3 applied to: F: {F}, G: {G}\n"
    return formula, annotation.format(formula=formula, num=num, F=F, G=G)


def from_hypothesis(num: int, F: Formula):
    """
    Adds formula 'from hypothesis set' which means it changes it sequence number and
    additionally generates annotation string

    :param num: sequence number of new formula in inference seq
    :param F: Formula
    :return: Formula obj, formula annotation string
    """
    annotation = "F_{num}: {formula} - Hypothesis\n"
    G = Formula.copy(F)
    G.seq_num = num
    return G, annotation.format(num=num, formula=G)


def MP(num: int, F: Formula, G: Formula):
    """
    Modus Ponens rule applied to formulas F =  A; G = A -> B

    :param num: sequence number of new formula in inference seq
    :param F:   formula "A"
    :param G:   formula "A -> B"
    :return:    Formula obj, formula annotation string
    """
    assert G.operation == "IMP", 'Incorrect MP application'
    assert G.successors[0].str_val == F.str_val
    formula = G.successors[1]
    formula.derived_by_mp_from = [F, G]
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Modus ponens rule applied to F_{fNum} and F_{gNum}\n"
    return formula, annotation.format(num=num, formula=formula, fNum=F.seq_num, gNum=G.seq_num)


def theorem_el(num: int, F: Formula):
    """
    Theorem L implementation. Build logical inference for formula F -> F
    |- F -> F

    :param F: Formula
    :param num: last used index in inference sequence
    :return:   tuple (formula objects list, annotation string list, increment of row amount (len formula lst))
    """
    lc = num + 1    # local counter
    f1, ann1 = axiom_A2(lc, F, F.imp(F), F)
    f2, ann2 = axiom_A1(f1.seq_num + 1, F, F.imp(F))
    f3, ann3 = MP(f2.seq_num + 1, f2, f1)
    f4, ann4 = axiom_A1(f3.seq_num + 1, F, F)
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)
    fs = (f1, f2, f3, f4, f5)
    anns = (ann1, ann2, ann3, ann4, ann5)
    return fs, anns, len(anns)


def _find_inference_index_for(inferred: list, F: Formula, A: Formula):
    """
    Seeks from tail to head in inference sequence for F -> A formula number

    :param inferred: inference list
    :return: index in list if occurrence was found, -1 otherwise
    """
    cmp_str = F.imp(A).str_val
    for i in range(len(inferred) - 1, -1, -1):
        if cmp_str == inferred[i].str_val:
            return i
    return -1


def deduction_theorem(num: int, hypothesis: list, inference_seq: list, F: Formula):
    """
    Deduction theorem implementation
    For given inference, derived formula H, and another formula F (which is supposed to be part of hypothesis list
    while derivation) rebuild inference such as given
    {Hypothesis set} + F |- H       becomes
    {Hypothesis set}     |- F -> H

    :param num: sequence number of new formula in inference seq
    :param hypothesis: list of formulas used as hypothesis set while derivation
    :param inference_seq: inference sequence
    :param F:          Formula
    :return: tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    res = []
    annotations = []
    local_counter = num
    for i, fi in enumerate(inference_seq):
        if fi == F:
            if res and res[-1].seq_num != local_counter:
                local_counter = res[-1].seq_num
            fs, anns, inc = theorem_el(local_counter, F)
            res.extend(fs)
            annotations.extend(anns)
            local_counter += inc + 1
        elif fi in hypothesis or fi.is_axiom:
            if fi in hypothesis:                        # if hypothesis -- add in inference row
                f, ann = from_hypothesis(local_counter, fi)
                res.append(f)
                annotations.append(ann)
                local_counter += 1
            else:
                f = Formula.copy(fi)
                f.seq_num = local_counter

                res.append(f)                          # if axiom -- add itself to new inference first of all
                annotations.append("F_{}: {} Axiom  A{} from previous inference\n".format(local_counter, f.str_val, fi.axiom_num))
                local_counter += 1
            g, an = axiom_A1(local_counter, f, F)      # then add another one axiom and derive needed
            res.append(g)
            annotations.append(an)
            h, an2 = MP(local_counter + 1, f, g)     # and derive needed
            local_counter += 1
            res.append(h)
            annotations.append(an2)
            local_counter += 1
        else:                               # derived by MP from some of the previous
            A, B = fi.derived_by_mp_from    # A = A, B = A -> fi - bigger one (ensured by extension order - line 57)
            f, ans = axiom_A2(local_counter, F, A, fi)
            res.append(f)
            annotations.append(ans)
            j1 = _find_inference_index_for(res, F, A)   # by induction assumption we were supposed to derive it somewhere before
            j2 = _find_inference_index_for(res, F, B)
            assert j1 != -1 and j2 != -1, "supposed to be derived formula was not found in inference list\n"
            FA = res[j1]
            FB = res[j2]
            f2, anns2 = MP(local_counter + 1, FB, f)
            f3, anns3 = MP(local_counter + 2, FA, f2)
            res.extend((f2, f3))
            annotations.extend((anns2, anns3))
            local_counter += 3
    return res, annotations, len(annotations)


def theorem_t3(num, F, G):
    """
    Builds inference list for T3 theorem
    |- (!f -> (f -> g))

    :param num: last used index in inference sequence
    :param F:   formula F
    :param G:   formula G
    :return:    tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F)                           # a
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F.neg())         # !a
    f3, ann3 = axiom_A1(f2.seq_num + 1, F, G.neg())             # a -> (!b -> a)
    f4, ann4 = MP(f3.seq_num + 1, F, f3)                        # !b -> a
    f5, ann5 = axiom_A1(f4.seq_num + 1, f2, G.neg())            # !a -> (!b -> !a)
    f6, ann6 = MP(f5.seq_num + 1, f2, f5)                       # !b -> !a
    f7, ann7 = axiom_A3(f6.seq_num + 1, F, G)                   # (!b -> !a) -> ((!b -> a) -> b)
    f8, ann8 = MP(f7.seq_num + 1, f6, f7)                       # (!b -> a) -> b
    f9, ann9 = MP(f8.seq_num + 1, f4, f8)                       # b
    fs = [f1, f2, f3, f4, f5, f6, f7, f8, f9]
    hyp = [f2,]                                                                  # first hypothesis
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num, hyp, fs, F)
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num + 1, [], deducted_fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)       # formulas, annotations, increment


def silogism_s1(num, F, G):
    """
    Builds inference list for silogism S1
    a -> b, b -> c |- a -> c

    :param num: last used index in inference sequence
    :param F:   F = a - > b
    :param G:   G = b -> c
    :return: tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F.successors[0]) # a
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F)           # a->b
    f3, ann3 = from_hypothesis(f2.seq_num + 1, G)           # b->c
    f4, ann4 = MP(f3.seq_num + 1, f1, f2)                   # b
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)                   # c
    fs = [f1, f2, f3, f4, f5]
    hyp = [f2, f3]
    deducted_fs, deducted_ann, inc = deduction_theorem(num, hyp, fs, f1)
    return deducted_fs, deducted_ann, len(deducted_ann)


def silogism_s2(num, F, G):
    """
    Builds inference list for silogism s2
    a -> (b -> c), b |- (a -> c)

    :param num: last used index in inference sequence
    :param F: F = a -> (b -> c)
    :param G: G = b
    :return: tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """

    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F.successors[0])             # a
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F)               # a->(b->c)
    f3, ann3 = from_hypothesis(f2.seq_num + 1, G)               # b
    f4, ann4 = MP(f3.seq_num + 1, f1, f2)                       # b->c
    f5, ann5 = MP(f4.seq_num + 1, f3, f4)                       # c
    fs = [f1, f2, f3, f4, f5]
    hyp = [f2, f3]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, hyp, fs, f1)
    return deducted_fs, deducted_anns, len(deducted_anns)


def theorem_t1(num, F):
    """
    Builds inference list for theorem T1
    |- !!f -> f

    :param num: last used index in inference sequence
    :param F: F
    :return:    tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F.neg(), F)
    f2s, ann2s, inc = theorem_el(f1.seq_num, F.neg())       # f2s - derivation of F->F formula
    f2 = f2s[-1]                                            # F->F extraction
    f3s, ann3s, inc = silogism_s2(f2.seq_num, f1, f2)
    f3 = f3s[-1]
    f4, ann4 = axiom_A1(f3.seq_num + 1, F.neg().neg(), F.neg())
    f5s, ann5s, inc = silogism_s1(f4.seq_num, f4, f3)
    inference = [f1] + list(f2s) + list(f3s) + [f4] + list(f5s)
    annotations = [ann1] + list(ann2s) + list(ann3s) + [ann4] + list(ann5s)
    return inference, annotations, len(annotations)


def theorem_t2(num, F):
    """
    Builds inference list for theorem T2
    |- f -> !!f

    :param num: last used index in inference sequence
    :param F: F
    :return:    tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F, F.neg().neg())
    f2s, ann2s, inc = theorem_t1(f1.seq_num, F.neg())
    f2 = f2s[-1]
    f3, ann3 = MP(f2.seq_num + 1, f2, f1)
    f4, ann4 = axiom_A1(f3.seq_num + 1, F, F.neg().neg().neg())
    f5s, ann5s, inc = silogism_s1(f4.seq_num, f4, f3)
    inference = [f1] + list(f2s) + [f3] + [f4] + list(f5s)
    annotations = [ann1] + list(ann2s) + [ann3] + [ann4] + list(ann5s)
    return inference, annotations, len(annotations)


def theorem_t4(num, F, G):
    """
    Builds inference list for theorem T4
    (!G -> !F) -> (F -> G)

    :param num: last used index in inference sequence
    :param F: Formula
    :param G: Formula
    :return:  tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F, G)                                               # (!G -> !F) -> ((!G -> F) -> G)
    f2, ann2 = from_hypothesis(f1.seq_num + 1, G.neg().imp(F.neg()))            # (!G -> !F)
    f3, ann3 = MP(f2.seq_num + 1, f2, f1)                                       # (!G -> F) -> G
    f4, ann4 = axiom_A1(f3.seq_num + 1, F, G.neg())                             # F -> (!G -> F)
    f5s, ann5s, inc = silogism_s1(f4.seq_num, f4, f3)                           # F -> G
    lc += inc
    fs = [f1, f2, f3, f4] + list(f5s)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, [], fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)


def theorem_t5(num, F, G):
    """
    Builds inference list for theorem T5
    (F -> G) -> (!G -> !F)

    :param num: last used index in inference sequence
    :param F: Formula
    :param G: Formula
    :return:  tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, G.neg(), F.neg())       # (!!f -> !!g) -> ((!!f -> !g) -> !f)
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F.imp(G))    # f->g
    f3s, ann3s, inc = theorem_t2(f2.seq_num, G)         # g->!!g
    f3 = f3s[-1]
    f4s, ann4s, inc = silogism_s1(f3.seq_num, f2, f3)       # f -> !!g
    f4 = f4s[-1]
    f5s, ann5s, inc = theorem_t1(f4.seq_num, F)             # !!f->f
    f5 = f5s[-1]
    f6s, ann6s, inc = silogism_s1(f5.seq_num, f5, f4)       # !!f -> !!g
    f6 = f6s[-1]
    f7, ann7 = MP(f6.seq_num + 1, f6, f1)                   # (!!f -> !g) -> !f
    f8, ann8 = axiom_A1(f7.seq_num + 1, G.neg(), F.neg().neg())     # (!g -> (!!f -> !g))
    f9s, ann9s, inc = silogism_s1(f8.seq_num, f8, f7)
    f9 = f9s[-1]                                             # !g -> !f
    fs = [f1, f2] + list(f3s) + list(f4s) + list(f5s) + list(f6s) + [f7, f8] + list(f9s)

    deducted_fs, deducted_anns, inc = deduction_theorem(num, [], fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)


def _lemma_t6(num, F, G):
    """
    Builds inference list for
    F |- (F -> G) -> G

    :param num: last used index in inference sequence
    :param F: Formula
    :param G: Formula
    :return:  tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F)
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F.imp(G))
    f3, ann3 = MP(f2.seq_num + 1, f1, f2)                   # G

    fs = [f1, f2, f3]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, [f1,], fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)


def theorem_t6(num, F, G):
    """
    Builds inference list for theorem T6
    F -> (!G -> !(F -> G))

    :param num: last used index in inference sequence
    :param F: Formula
    :param G: Formula
    :return:  tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F)                   # F
    f2s, ann2s, inc = theorem_t5(f1.seq_num, F.imp(G), G)       # ((F -> G) -> G) -> (!G -> !(F -> G))
    f2 = f2s[-1]
    f3s, ann3s, inc = _lemma_t6(f2.seq_num, F, G)               # (F -> G) -> G
    f3 = f3s[-1]
    f4, ann4 = MP(f3.seq_num + 1, f3, f2)                           # (!G -> !(F -> G))
    f5, ann5 = from_hypothesis(f4.seq_num + 1, G.neg())             # !G
    f6, ann5 = MP(f5.seq_num + 1, f5, f4)                           # !(F -> G)

    fs = [f1] + list(f2s) + list(f3s) + [f4] + [f5] + [f6]
    deducted_fs, deducted_anns, inc = deduction_theorem(num + 1, [f1, ], fs, f5)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, [], deducted_fs, f1)
    return deducted_fs, deducted_anns, len(deducted_anns)


def _lemma_t7(num, F, G):
    """
    Builds intermediate theorem inference:
    !F -> G, F |- (!F -> G) -> (!F -> !!G)

    :param num: last used index in inference sequence
    :param F: Formula
    :param G: Formula
    :return:  tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F.neg().imp(G))  # !F -> G
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F.neg())     # !F
    f3s, ann3s, inc = theorem_t2(f2.seq_num, G)         # G -> !!G
    f3 = f3s[-1]
    f4, ann4 = MP(f3.seq_num + 1, f2, f1)                       # G
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)

    fs = [f1] + [f2] + list(f3s) + [f4] + [f5]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, [f1,], fs, f2)
    deducted_fs, deducted_anns, inc = deduction_theorem(num + 1, [], deducted_fs, f1)
    return deducted_fs, deducted_anns, len(deducted_anns)


def theorem_t7(num, F, G):
    """
    Builds inference for theorem T7
    (F -> G) -> ((!F -> G) -> G)

    :param num: last used index in inference sequence
    :param F: Formula
    :param G: Formula
    :return:  tuple(inference sequence, annotation sequence, amount of formulas in inference sequence)
    """
    lc = num
    f1s, ann1s, inc = theorem_t5(lc, F, G)
    f1 = f1s[-1]
    f2, ann2 = axiom_A3(f1.seq_num + 1, F, G)
    f3s, ann3s, inc = silogism_s1(f2.seq_num, f1, f2)
    f3 = f3s[-1]                                                # (F -> G) -> ((!G -> F) -> G)
    f4, ann4 = from_hypothesis(f3.seq_num + 1, F.imp(G))
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)                       # (!G -> F) -> G
    f6s, ann6s, inc = theorem_t4(f5.seq_num, G.neg(), F)        # (!F -> !!G) -> (!G -> F)
    f6 = f6s[-1]
    f7s, ann7s, inc = _lemma_t7(f6.seq_num, F, G)               # (!F -> G) -> (!F -> !!G)
    f7 = f7s[-1]
    f8s, ann8s, inc = silogism_s1(f7.seq_num, f7, f6)           # (!F -> G) -> (!G -> F)
    f8 = f8s[-1]
    f9s, ann9s, inc = silogism_s1(f8.seq_num, f8, f5)           # (!F -> G) -> G
    f9 = f9s[-1]
    f10, ann10 = from_hypothesis(f9.seq_num + 1, F.neg().imp(G))    # (!F -> G)
    f11, ann11 = MP(f10.seq_num + 1, f10, f9)                    # G

    fs = list(f1s) + [f2] + list(f3s) + [f4] + [f5] + list(f6s) + list(f7s) + list(f8s) + list(f9s) + [f10] + [f11]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, [f4, ], fs, f10)
    deducted_fs, deducted_anns, inc = deduction_theorem(num + 1, [], deducted_fs, f4)
    return deducted_fs, deducted_anns, len(deducted_anns)
