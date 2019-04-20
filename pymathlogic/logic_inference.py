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
    formula.derived_by_mp_from.extend([F, G])
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


def theorem_t3(num, formula_a, neg_formula_a, formula_b):
    """

    :param num:         last used index inference sequence
    :param formula_a:
    :param neg_formula_a:
    :param formula_b:
    :param num_a:       formula a index
    :param num_neg_a:   negation of formula a index
    :param num_b:       formula b index
    :return:
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, formula_a)                           # a
    f2, ann2 = from_hypothesis(lc + 1, neg_formula_a)                   # !a
    f3, ann3 = axiom_A1(lc + 2, formula_a, formula_b.neg())             # a -> (!b -> a)
    f4, ann4 = MP(lc + 3, formula_a, f3)                                # !b -> a
    f5, ann5 = axiom_A1(lc + 4, neg_formula_a, formula_b.neg())         # !a -> (!b -> !a)
    f6, ann6 = MP(lc + 5, neg_formula_a, f5)                            # !b -> !a
    f7, ann7 = axiom_A3(lc + 6, formula_a, formula_b)                   # (!b -> !a) -> ((!b -> a) -> b)
    f8, ann8 = MP(lc + 7, f6, f7)                                       # (!b -> a) -> b
    f9, ann9 = MP(lc + 8, f4, f8)                                       # b
    fs = (f1, f2, f3, f4, f5, f6, f7, f8, f9)
    hyp = (neg_formula_a,)                                                                  # first hypothesis
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num, hyp, fs, formula_a)
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num + 1, (), deducted_fs, neg_formula_a)
    return deducted_fs, deducted_anns, deducted_num    # formulas, annotations, last used index


def silogism_s1(num, formula_a:Formula, formula_b:Formula, formula_c:Formula):
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, formula_a)
    f2, ann2 = from_hypothesis(lc + 1, formula_a.imp(formula_b))
    f3, ann3 = from_hypothesis(lc+ 2, formula_b.imp(formula_c))
    f4, ann4 = MP(lc + 3, f1, f2)    # B
    f5, ann5 = MP(lc + 4, f4, f3)    # C
    fs = (f1, f2, f3, f4, f5)
    hyp = (f2, f3)
    deducted_fs, deducted_ann, inc = deduction_theorem(num, hyp, fs, f1)
    return deducted_fs, deducted_ann, inc


def silogism_s2(num, formula_a, formula_b, formula_c):
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, formula_a.imp(formula_b.imp(formula_c)))     # a -> (b -> c)
    f2, ann2 = from_hypothesis(lc + 1, formula_a)                               # a
    f3, ann3 = from_hypothesis(lc + 2, formula_b)                               # b
    f4, ann4 = MP(lc + 3, f2, f1)                                               # b -> c
    f5, ann5 = MP(lc + 5, f3, f4)                                               # c

    fs = (f1, f2, f3, f4, f5)
    hyp = (f1, f3)
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num , hyp, fs, f2)
    return deducted_fs, deducted_anns, deducted_num



if __name__ == '__main__':
    A = Formula("(A)")
    A.seq_num = 1
    A.is_complete = True
    A.operation = None
    A.type = "var"

    B = Formula("(B)")
    B.seq_num = 2
    B.is_complete = True
    B.operation = None
    B.type = "var"

    C = Formula("(C)")
    C.is_complete = True
    C.seq_num = 3
    C.operation = None
    C.type = "var"

    # fs, anns, num = theorem_t3(0, A, A.neg(), B)
    # for a in anns:
    #     print(a, end='')
    fs, anns, num = silogism_s2(0, A, B, C)
    for an in anns:
        print(an, end='')

    # fs2, anns2, inc = theorem_el(5, A)
    # pass
    # fs, anns, num = theorem_t3(i, A, neg_A, B)
    # for an in anns:
    #     print(an)