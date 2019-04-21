"""

"""
# from .formula import Formula


import formula


Formula = formula.Formula


def axiom_A1(num, F, G):
    """

    :param num:
    :param F:
    :param G:
    :return:
    """
    formula = F.imp(G.imp(F))
    formula.is_axiom = True
    formula.axiom_num = 1
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Axiom A1 applied to: F: {F}, G: {G}\n"
    return formula, annotation.format(num=num, formula=formula, F=F, G=G)


def axiom_A2(num, F, G, H):
    """

    :param num:
    :param F:
    :param G:
    :param H:
    :return:
    """
    left = F.imp(G.imp(H))
    right = (F.imp(G)).imp(F.imp(H))
    formula = left.imp(right)
    formula.is_axiom = True
    formula.axiom_num = 2
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Axiom A2 applied to: F: {F}, G: {G}, H: {H}\n"
    return formula, annotation.format(num=num, formula=formula, F=F, G=G, H=H)


def axiom_A3(num, F, G):
    """

    :param num:
    :param F:
    :param G:
    :return:
    """
    left = G.neg().imp(F.neg())
    right = (G.neg().imp(F)).imp(G)
    formula = left.imp(right)
    formula.is_axiom = True
    formula.axiom_num = 3
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Axiom A3 applied to: F: {F}, G: {G}\n"
    return formula, annotation.format(formula=formula, num=num, F=F, G=G)


def from_hypothesis(num, F):
    annotation = "F_{num}: {formula} - Hypothesis\n"
    F.seq_num = num
    return F, annotation.format(num=num, formula=F)


def MP(num, F, G):
    """
    Modus Ponens rule application to formulas F: A, G: A -> B

    :param num: last formula num in sequence of logically inferred statements
    :param F:   formula "A"
    :param G:   formula "A -> B"
    :return:
    """
    assert G.operation == "IMP", 'Incorrect MP application'
    assert G.successors[0].str_val == F.str_val
    formula = G.successors[1]
    formula.derived_by_mp_from = [F, G]
    formula.seq_num = num
    annotation = "F_{num}: {formula} - Modus ponens rule applied to F_{fNum} and F_{gNum}\n"
    return formula, annotation.format(num=num, formula=formula, fNum=F.seq_num, gNum=G.seq_num)


def theorem_el(num, F):
    """
    Theorem L implementation
    |- F -> F

    :param F: ^
    :param num: last used index in inference sequence
    :return:   tuple (formula objects list, annotation string list, increment of row amount (len formula lst))
    """
    lc = num + 1    # local counter
    f1, ann1 = axiom_A2(lc, F, F.imp(F), F)
    f2, ann2 = axiom_A1(lc + 1, F, F.imp(F))
    f3, ann3 = MP(lc + 2, f2, f1)
    f4, ann4 = axiom_A1(lc + 3, F, F)
    f5, ann5 = MP(lc + 4, f4, f3)
    fs = (f1, f2, f3, f4, f5)
    anns = (ann1, ann2, ann3, ann4, ann5)
    return fs, anns, 5


def _find_inference_index_for(inferred, F, A):
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


def deduction_theorem(num, hypothesis, inference_seq, F: Formula):
    res = []
    annotations = []
    local_counter = num
    for i, fi in enumerate(inference_seq):
        if fi == F:
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
                f = fi
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
    return tuple(res), annotations, local_counter - num


def theorem_t3(num, formula_f, neg_formula_f, formula_g):
    """

    :param num:         last used index inference sequence
    :param formula_f:
    :param neg_formula_f:
    :param formula_g:
    :return:
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, formula_f)                           # a
    f2, ann2 = from_hypothesis(lc + 1, neg_formula_f)                   # !a
    f3, ann3 = axiom_A1(lc + 2, formula_f, formula_g.neg())             # a -> (!b -> a)
    f4, ann4 = MP(lc + 3, formula_f, f3)                                # !b -> a
    f5, ann5 = axiom_A1(lc + 4, neg_formula_f, formula_g.neg())         # !a -> (!b -> !a)
    f6, ann6 = MP(lc + 5, neg_formula_f, f5)                            # !b -> !a
    f7, ann7 = axiom_A3(lc + 6, formula_f, formula_g)                   # (!b -> !a) -> ((!b -> a) -> b)
    f8, ann8 = MP(lc + 7, f6, f7)                                       # (!b -> a) -> b
    f9, ann9 = MP(lc + 8, f4, f8)                                       # b
    fs = (f1, f2, f3, f4, f5, f6, f7, f8, f9)
    hyp = (neg_formula_f,)                                                                  # first hypothesis
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num, hyp, fs, formula_f)
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num + 1, (), deducted_fs, neg_formula_f)
    return deducted_fs, deducted_anns, deducted_num    # formulas, annotations, last used index


def silogism_s1(num, F, G):
    """

    :param num:
    :param F:   f = a - > b
    :param G:   g = b -> c
    :return: derives a -> c
    """
    # a, b = f.successors
    # c = g.successors[1]
    # return _silogism_s1(num, a, b, c)
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F.successors[0]) # a
    f2, ann2 = from_hypothesis(lc + 1, F)           # a->b
    f3, ann3 = from_hypothesis(lc + 2, G)           # b->c
    f4, ann4 = MP(lc + 3, f1, f2)                   # b
    f5, ann5 = MP(lc + 4, f4, f3)                   # c
    fs = (f1, f2, f3, f4, f5)
    hyp = (f2, f3)
    deducted_fs, deducted_ann, inc = deduction_theorem(lc + 4, hyp, fs, f1)
    return deducted_fs, deducted_ann, inc


def silogism_s2(num, F, G):
    """

    :param num:
    :param F: f = a -> (b -> c)
    :param G: g = b
    :return: derives a -> c
    """

    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F.successors[0])     # a
    f2, ann2 = from_hypothesis(lc + 1, F)               # a->(b->c)
    f3, ann3 = from_hypothesis(lc + 2, G)               # b
    f4, ann4 = MP(lc + 3, f1, f2)                       # b->c
    f5, ann5 = MP(lc + 4, f3, f4)                       # c
    fs = (f1, f2, f3, f4, f5)
    hyp = (f2, f3)
    deducted_fs, deducted_anns, inc = deduction_theorem(lc + 4, hyp, fs, f1)
    return deducted_fs, deducted_anns, inc


def theorem_t1(num, F):
    """
    |- !!f -> f

    :param num: relative number in inference sequence
    :param F: f
    :return:
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F.neg(), F)
    f2s, ann2s, inc = theorem_el(lc, F.neg())     # f2s - derivation of F->F formula
    f2 = f2s[-1]                                            # F->F extraction
    lc += inc                                               # local counter += increment
    f3s, ann3s, inc = silogism_s2(lc, f1, f2)
    f3 = f3s[-1]
    lc += inc
    f4, ann4 = axiom_A1(lc, F.neg().neg(), F.neg())
    f5s, ann5s, inc = silogism_s1(lc + 1, f4, f3)
    lc += inc
    inference = [f1] + list(f2s) + list(f3s) + [f4] + list(f5s)
    annotations = [ann1] + list(ann2s) + list(ann3s) + [ann4] + list(ann5s)
    return inference, annotations, lc - num


def theorem_t2(num, F):
    """
    |- f -> !!f

    :param num:
    :param F:
    :return:
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F, F.neg().neg())
    f2s, ann2s, inc = theorem_t1(lc, F.neg())
    lc += inc
    f2 = f2s[-1]
    f3, ann3 = MP(lc + 1, f2, f1)
    f4, ann4 = axiom_A1(lc + 2, F, F.neg().neg().neg())
    f5s, ann5s, inc = silogism_s1(lc + 2, f4, f3)
    inference = [f1] + list(f2s) + [f3] + [f4] + list(f5s)
    annotations = [ann1] + list(ann2s) + [ann3] + [ann4] + list(ann5s)
    return inference, annotations, inc


def theorem_t4(num, F, G):
    """
    (!G -> !F) -> (F -> G)

    :param num:
    :param F: f
    :param G: g
    :return:
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F, G)                                       # (!G -> !F) -> ((!G -> F) -> G)
    f2, ann2 = from_hypothesis(lc + 1, G.neg().imp(F.neg()))            # (!G -> !F)
    f3, ann3 = MP(lc + 2, f2, f1)                                       # (!G -> F) -> G
    f4, ann4 = axiom_A1(lc + 3, F, G.neg())                             # F -> (!G -> F)
    f5s, ann5s, inc = silogism_s1(lc + 4, f4, f3)                       # F -> G
    lc += inc
    fs = [f1, f2, f3, f4] + list(f5s)
    deducted_fs, deducted_anns, inc = deduction_theorem(num + 1, (), fs, f2)
    return deducted_fs, deducted_anns, inc


def theorem_t5(num, F, G):
    """
    (F -> G) -> (!G -> !F)

    :param num:
    :param F: F
    :param G: G
    :return:
    """
    lc = num + 1
    f1s, ann1s, inc = theorem_t4(lc, G.neg(), F.neg())
    lc += inc
    f1 = f1s[-1]                                    # (!!f -> !!g) -> (!g -> !f)
    f2, ann2 = from_hypothesis(lc, F.imp(G))        # f -> g
    f3s, ann3s, inc = theorem_t2(lc, G)
    lc += inc
    f3 = f3s[-1]                                    # g -> !!g
    f4s, ann4s, inc = silogism_s1(lc, f2, f3)
    lc += inc
    f4 = f4s[-1]                                    # f -> !!g
    f5s, ann5s, inc = theorem_t1(lc, F)             # !!f -> f
    lc += inc
    f5 = f5s[-1]
    f6s, ann6s, inc = silogism_s1(lc, f5, f4)       # !!f -> !!g
    lc += inc
    f6 = f6s[-1]
    f7, ann7 = MP(lc + 1, f6, f1)                   # !g -> !f
    fs = list(f1s) + [f2] + list(f3s) + list(f4s) + list(f5s) + list(f6s) + [f7]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (), fs, f2)
    return deducted_fs, deducted_anns, inc


def _lemma_t6(num, F, G):
    """
    F |- (F -> G) -> G

    :param num:
    :param F:
    :param G:
    :return:
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F)
    f2, ann2 = from_hypothesis(lc + 1, F.imp(G))
    f3, ann3 = MP(lc + 2, f1, f2)                   # G

    fs = (f1, f2, f3)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (f1,), fs, f2)
    return deducted_fs, deducted_anns, inc


def theorem_t6(num, F, G):
    """
    F -> (!G -> !(F -> G))

    :param num:
    :param F:
    :param G:
    :return:
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F)                   # F
    f2s, ann2s, inc = theorem_t5(lc, F.imp(G), G)       # ((F -> G) -> G) -> (!G -> !(F -> G))
    lc += inc
    f2 = f2s[-1]
    f3s, ann3s, inc = _lemma_t6(lc, F, G)               # (F -> G) -> G
    lc += inc
    f3 = f3s[-1]
    f4, ann4 = MP(lc, f3, f2)                           # (!G -> !(F -> G))
    f5, ann5 = from_hypothesis(lc + 1, G.neg())         # !G
    f6, ann5 = MP(lc, f5, f4)                           # !(F -> G)

    fs = [f1] + list(f2s) + list(f3s) + [f4] + [f5] + [f6]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (f1, ), fs, f5)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (), deducted_fs, f1)
    return deducted_fs, deducted_anns, inc


def _lemma_t7(num, F, G):
    """
    (!F -> G) -> (!F -> !!G)

    :param num:
    :param F:
    :param G:
    :return:
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F.neg().imp(G))  # !F -> G
    f2, ann2 = from_hypothesis(lc + 1, F.neg())     # !F
    f3s, ann3s, inc = theorem_t2(lc + 2, G)         # G -> !!G
    lc += inc
    f3 = f3s[-1]
    f4, ann4 = MP(lc, f2, f1)                       # G
    f5, ann5 = MP(lc + 1, f4, f3)

    fs = [f1] + [f2] + list(f3s) + [f4] + [f5]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (f1,), fs, f2)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (), deducted_fs, f1)
    return deducted_fs, deducted_anns, inc


def theorem_t7(num, F, G):
    """
    (F -> G) -> ((!F -> G) -> G)

    :param num:
    :param F:
    :param G:
    :return:
    """
    lc = num + 1
    f1s, ann1s, inc = theorem_t5(lc, F, G)
    lc += inc
    f1 = f1s[-1]
    f2, ann2 = axiom_A3(lc, F, G)
    f3s, ann3s, inc = silogism_s1(lc + 1, f1, f2)
    lc += inc
    f3 = f3s[-1]                                        # (F -> G) -> ((!G -> F) -> G)
    f4, ann4 = from_hypothesis(lc, F.imp(G))
    f5, ann5 = MP(lc + 1, f4, f3)                       # (!G -> F) -> G
    f6s, ann6s, inc = theorem_t4(lc + 1, G.neg(), F)    # (!F -> !!G) -> (!G -> F)
    lc += inc
    f6 = f6s[-1]
    f7s, ann7s, inc = _lemma_t7(lc, F, G)               # (!F -> G) -> (!F -> !!G)
    lc += inc
    f7 = f7s[-1]
    f8s, ann8s, inc = silogism_s1(lc, f7, f6)           # (!F -> G) -> (!G -> F)
    lc += inc
    f8 = f8s[-1]
    f9s, ann9s, inc = silogism_s1(lc, f8, f5)           # (!F -> G) -> G
    lc += inc
    f9 = f9s[-1]
    f10, ann10 = from_hypothesis(lc + 1, F.neg().imp(G))    # (!F -> G)
    f11, ann11 = MP(lc + 2, f10, f9)                    # G

    fs = list(f1s) + [f2] + list(f3s) + [f4] + [f5] + list(f6s) + list(f7s) + list(f8s) + list(f9s) + [f10] + [f11]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (f4, ), fs, f10)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (), deducted_fs, f4)
    return deducted_fs, deducted_anns, inc





if __name__ == '__main__':
    F = Formula("(F)")
    F.seq_num = 1
    F.is_complete = True
    F.operation = None
    F.type = "var"

    G = Formula("(G)")
    G.seq_num = 2
    G.is_complete = True
    G.operation = None
    G.type = "var"

    fs, anns, num = theorem_t6(2, F, G)
    for an in anns:
        print(an, end='')

    # fs2, anns2, inc = theorem_el(5, A)
    # pass
    # fs, anns, num = theorem_t3(i, A, neg_A, B)
    # for an in anns:
    #     print(an)