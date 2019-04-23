"""

"""
from .formula import Formula

# import formula


# Formula = formula.Formula


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
    # F.seq_num = num
    G = Formula(F.str_val)      # REFACTOR ME TO ALTERNATIVE CLASS CONSTRUCTOR
    G.seq_num = num
    G.is_complete = F.is_complete
    G.is_axiom = F.is_axiom
    G.axiom_num = F.axiom_num
    G.derived_by_mp_from = F.derived_by_mp_from[:]
    G.operation = F.operation
    G.type = F.type
    G.successors = F.successors[:]
    return G, annotation.format(num=num, formula=G)


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
    f2, ann2 = axiom_A1(f1.seq_num + 1, F, F.imp(F))
    f3, ann3 = MP(f2.seq_num + 1, f2, f1)
    f4, ann4 = axiom_A1(f3.seq_num + 1, F, F)
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)
    fs = (f1, f2, f3, f4, f5)
    anns = (ann1, ann2, ann3, ann4, ann5)
    return fs, anns, len(anns)


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
                f = Formula(fi.str_val)
                f.seq_num = local_counter
                f.is_complete = fi.is_complete
                f.is_axiom = fi.is_axiom
                f.axiom_num = fi.axiom_num
                f.derived_by_mp_from = fi.derived_by_mp_from[:]
                f.operation = fi.operation
                f.type = fi.type
                f.successors = fi.successors[:]

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


def theorem_t3(num, F, G):
    """

    :param num:         last used index inference sequence
    :param F:
    :param G:
    :return:
    """
    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F)                           # a
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F.neg())                   # !a
    f3, ann3 = axiom_A1(f2.seq_num + 1, F, G.neg())             # a -> (!b -> a)
    f4, ann4 = MP(f3.seq_num + 1, F, f3)                                # !b -> a
    f5, ann5 = axiom_A1(f4.seq_num + 1, f2, G.neg())         # !a -> (!b -> !a)
    f6, ann6 = MP(f5.seq_num + 1, f2, f5)                            # !b -> !a
    f7, ann7 = axiom_A3(f6.seq_num + 1, F, G)                   # (!b -> !a) -> ((!b -> a) -> b)
    f8, ann8 = MP(f7.seq_num + 1, f6, f7)                                       # (!b -> a) -> b
    f9, ann9 = MP(f8.seq_num + 1, f4, f8)                                       # b
    fs = (f1, f2, f3, f4, f5, f6, f7, f8, f9)
    hyp = (f2,)                                                                  # first hypothesis
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num, hyp, fs, F)
    deducted_fs, deducted_anns, deducted_num = deduction_theorem(num + 1, (), deducted_fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)    # formulas, annotations, increment


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
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F)           # a->b
    f3, ann3 = from_hypothesis(f2.seq_num + 1, G)           # b->c
    f4, ann4 = MP(f3.seq_num + 1, f1, f2)                   # b
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)                   # c
    fs = (f1, f2, f3, f4, f5)
    hyp = (f2, f3)
    deducted_fs, deducted_ann, inc = deduction_theorem(num, hyp, fs, f1)
    return deducted_fs, deducted_ann, len(deducted_ann)


def silogism_s2(num, F, G):
    """

    :param num:
    :param F: f = a -> (b -> c)
    :param G: g = b
    :return: derives a -> c
    """

    lc = num + 1
    f1, ann1 = from_hypothesis(lc, F.successors[0])     # a
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F)               # a->(b->c)
    f3, ann3 = from_hypothesis(f2.seq_num + 1, G)               # b
    f4, ann4 = MP(f3.seq_num + 1, f1, f2)                       # b->c
    f5, ann5 = MP(f4.seq_num + 1, f3, f4)                       # c
    fs = (f1, f2, f3, f4, f5)
    hyp = (f2, f3)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, hyp, fs, f1)
    return deducted_fs, deducted_anns, len(deducted_anns)


def theorem_t1(num, F):
    """
    |- !!f -> f

    :param num: relative number in inference sequence
    :param F: f
    :return:
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F.neg(), F)
    f2s, ann2s, inc = theorem_el(f1.seq_num, F.neg())     # f2s - derivation of F->F formula
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
    |- f -> !!f

    :param num:
    :param F:
    :return:
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
    (!G -> !F) -> (F -> G)

    :param num:
    :param F: f
    :param G: g
    :return:
    """
    lc = num + 1
    f1, ann1 = axiom_A3(lc, F, G)                                       # (!G -> !F) -> ((!G -> F) -> G)
    f2, ann2 = from_hypothesis(f1.seq_num + 1, G.neg().imp(F.neg()))            # (!G -> !F)
    f3, ann3 = MP(f2.seq_num + 1, f2, f1)                                       # (!G -> F) -> G
    f4, ann4 = axiom_A1(f3.seq_num + 1, F, G.neg())                             # F -> (!G -> F)
    f5s, ann5s, inc = silogism_s1(f4.seq_num, f4, f3)                       # F -> G
    lc += inc
    fs = [f1, f2, f3, f4] + list(f5s)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (), fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)


def theorem_t5(num, F, G):
    """
    (F -> G) -> (!G -> !F)

    :param num:
    :param F: F
    :param G: G
    :return:
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

    deducted_fs, deducted_anns, inc = deduction_theorem(num, (), fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)


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
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F.imp(G))
    f3, ann3 = MP(f2.seq_num + 1, f1, f2)                   # G

    fs = (f1, f2, f3)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (f1,), fs, f2)
    return deducted_fs, deducted_anns, len(deducted_anns)


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
    f2s, ann2s, inc = theorem_t5(f1.seq_num, F.imp(G), G)       # ((F -> G) -> G) -> (!G -> !(F -> G))
    f2 = f2s[-1]
    f3s, ann3s, inc = _lemma_t6(f2.seq_num, F, G)               # (F -> G) -> G
    f3 = f3s[-1]
    f4, ann4 = MP(f3.seq_num + 1, f3, f2)                           # (!G -> !(F -> G))
    f5, ann5 = from_hypothesis(f4.seq_num + 1, G.neg())             # !G
    f6, ann5 = MP(f5.seq_num + 1, f5, f4)                           # !(F -> G)

    fs = [f1] + list(f2s) + list(f3s) + [f4] + [f5] + [f6]
    deducted_fs, deducted_anns, inc = deduction_theorem(num + 1, (f1, ), fs, f5)
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (), deducted_fs, f1)
    return deducted_fs, deducted_anns, len(deducted_anns)


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
    f2, ann2 = from_hypothesis(f1.seq_num + 1, F.neg())     # !F
    f3s, ann3s, inc = theorem_t2(f2.seq_num, G)         # G -> !!G
    f3 = f3s[-1]
    f4, ann4 = MP(f3.seq_num + 1, f2, f1)                       # G
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)

    fs = [f1] + [f2] + list(f3s) + [f4] + [f5]
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (f1,), fs, f2)
    deducted_fs, deducted_anns, inc = deduction_theorem(num + 1, (), deducted_fs, f1)
    return deducted_fs, deducted_anns, len(deducted_anns)


def theorem_t7(num, F, G):
    """
    (F -> G) -> ((!F -> G) -> G)

    :param num:
    :param F:
    :param G:
    :return:
    """
    lc = num
    f1s, ann1s, inc = theorem_t5(lc, F, G)
    f1 = f1s[-1]
    f2, ann2 = axiom_A3(f1.seq_num + 1, F, G)
    f3s, ann3s, inc = silogism_s1(f2.seq_num, f1, f2)
    f3 = f3s[-1]                                        # (F -> G) -> ((!G -> F) -> G)
    f4, ann4 = from_hypothesis(f3.seq_num + 1, F.imp(G))
    f5, ann5 = MP(f4.seq_num + 1, f4, f3)                       # (!G -> F) -> G
    f6s, ann6s, inc = theorem_t4(f5.seq_num, G.neg(), F)    # (!F -> !!G) -> (!G -> F)
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
    deducted_fs, deducted_anns, inc = deduction_theorem(num, (f4, ), fs, f10)
    deducted_fs, deducted_anns, inc = deduction_theorem(num + 1, (), deducted_fs, f4)
    return deducted_fs, deducted_anns, inc


def _build_hypothesis(F: Formula, vector: dict) -> tuple:
    """
    Helper function for kalmar theorem. Implements xi^(alpha_i) hypothesis sequence

    :param F: Formula
    :param vector: dict - boolean vector represented as {'var_name': value} where value in {0; 1}
    :return: tuple xi^(alpha_i)
    """
    var_names = F.get_vars()
    assert var_names == set(vector.keys()), 'Incorrect input vector for given formula'
    hyp = []
    temp = "({})"
    for i, var in enumerate(var_names):
        f = Formula(temp.format(var))
        f.is_complete = True
        f.type = 'var'
        if f(**vector) == 0:
            f = f.neg()
        f.seq_num = i + 1
        hyp.append(f)
    return tuple(hyp)


def _get_formula_from(F: Formula, inf_list: list):
    for g in inf_list:
        if F == g:
            return g
    return None


def _kalmar_helper(F: Formula, hypothesis: tuple, inf_list: list, ann_list: list, vector: dict, num: int):
    """

    :param F: formula - current formula (current node in syntax tree)
    :param hypothesis: tuple - logical inference hypothesis
    :param inf_list: list - global inference list
    :param ann_list: list - global inference list annotation
    :param vector:  dict - given boolean vector
    :return: index increment (amount of performed operations on current node)
    """
    if F in hypothesis:
        if not inf_list:
            index = 1
        else:
            index = inf_list[-1].seq_num + 1
        f, ann = from_hypothesis(index, F)
        inf_list.append(f)
        ann_list.append(ann)
        return
    if F.type == "var":
        if inf_list:
            f, ann = from_hypothesis(inf_list[-1].seq_num + 1, F.pow_alpha(vector)) # inference list supposed to be non-empty
        else:
            f, ann = from_hypothesis(num + 1, F.pow_alpha(vector))
        inf_list.append(f)
        ann_list.append(ann)
        return
    else:
        op = F.operation
        if op == "NOT":
            # if F(**vector) == 1:
                # by induction assumption already derived
            G = F.successors[0]
            _kalmar_helper(G, hypothesis, inf_list, ann_list, vector, num)
            if F(**vector) == 0:
                f1s, ann1s, inc = theorem_t2(inf_list[-1].seq_num, G)            # G -> !!G
                f1 = f1s[-1]
                f2 = _get_formula_from(G, inf_list)                                # G
                f3, ann3 = MP(f1.seq_num + 1, f2, f1)                            # !!G
                fs = list(f1s) + [f3]
                anns = ann1s + [ann3]
                inf_list.extend(fs)
                ann_list.extend(anns)
                return
        elif op == "IMP":
            G, H = F.successors # F = G -> H
            _kalmar_helper(G, hypothesis, inf_list, ann_list, vector, num)
            _kalmar_helper(H, hypothesis, inf_list, ann_list, vector, num)
            if G(**vector) == 0:
                f1s, ann1s, inc = theorem_t3(inf_list[-1].seq_num, G, H)   # !G -> (G - > H)
                f1 = f1s[-1]
                f2 = _get_formula_from(G.neg(), inf_list)   # ... |- !G
                f3, ann3 = MP(f1.seq_num + 1, f2, f1)       # ... |- (G -> H)
                fs = list(f1s) + [f3]
                anns = list(ann1s) + [ann3]
                inf_list.extend(fs)
                ann_list.extend(anns)
                return
            elif H(**vector) == 1:
                f1, ann1 = axiom_A1(inf_list[-1].seq_num + 1, H, G)  # H -> (G -> H)
                f2 = _get_formula_from(H.pow_alpha(vector), inf_list)    # ... |- H
                f3, ann3 = MP(f1.seq_num + 1, f2, f1)      # (G -> H)
                fs = [f1, f3]
                anns = [ann1, ann3]
                inf_list.extend(fs)
                ann_list.extend(anns)
                return
            elif G(**vector) == 1 and H(**vector) == 0:
                f1 = _get_formula_from(G.pow_alpha(vector), inf_list)   # ... |- G
                f2 = _get_formula_from(H.pow_alpha(vector), inf_list)   # ... |- !H
                f3s, ann3s, inc = theorem_t6(inf_list[-1].seq_num, G, H)     # G -> (!H -> !(G -> H))
                f3, ann3 = f3s[-1], ann3s[-1]
                f4, ann4 = MP(f3.seq_num + 1, f1, f3)          # !H -> !(G -> H)
                f5, ann5 = MP(f4.seq_num + 1, f2, f4)              # !(g -> h)
                fs = list(f3s) + [f4, f5]
                anns = list(ann3s) + [ann4, ann5]
                inf_list.extend(fs)
                ann_list.extend(anns)
                return


def kalmar_theorem(num: int, F: Formula, vector: dict):
    """
    Kalmar theorem implementation


    :param num:     int - last used index in inference sequence
    :param F:       Formula - formula - F to be derived
    :param vector:  dict - boolean vector represented as {'var_name': value} where value in {0; 1}
    :return:        logical inference of formula F from it's variables xi^(alpha_i)
                    where xi^(alpha_i) = xi if alpha_i = 1 else !xi
    """
    print(f'Kalmar called on vector: {tuple(vector.values())}')
    hyp = _build_hypothesis(F, vector)
    inf_list = []
    ann_list = []
    vector_copy = {k: v for k, v in vector.items()}
    _kalmar_helper(F, hyp, inf_list, ann_list, vector_copy, num)
    return inf_list, ann_list, len(ann_list)


def _inference_union(xn: Formula, hypothesis: tuple, inf1: list, inf2: list, F: Formula):
    """
    For given x1^(a1), ..., x(n-1)^(a(n-1)),  xn |- F
              x1^(a1), ..., x(n-1)^(a(n-1)), !xn |- F  builds x1^(a1), ..., x(n-1)^(a(n-1)) |- F

    :param xn:              Formula - variable (xn) to be thrown away
    :param hypothesis:      tuple - x1^(a1), ..., x(n-1)^(a(n-1))
    :param inf1:            list - first inference sequence     (last variable normal)
    :param inf2:            list - second inference sequence    (last variable inverted)
    :param F:               Formula
    :return:                tuple - inference sequence, annotations, increment
    """

    deducted_f1, deducted_a1, inc1 = deduction_theorem(0, hypothesis, inf1, xn.neg())                   # !xn -> F
    f1 = deducted_f1[-1]
    deducted_f2, deducted_a2, inc2 = deduction_theorem(deducted_f1[-1].seq_num, hypothesis, inf2, xn)   # xn -> F
    f2 = deducted_f2[-1]
    f3s, ann3s, inc3 = theorem_t7(deducted_f2[-1].seq_num, xn, F)                       # (xn -> F) -> ((!xn -> F) -> F)
    f3 = f3s[-1]
    f4, ann4 = MP(f3s[-1].seq_num + 1, f2, f3)                        # ((!xn -> F) -> F)
    f5, ann5 = MP(f4.seq_num + 1, f1, f4)                                  # F

    inference = list(deducted_f1) + list(deducted_f2) + list(f3s) + [f4, f5]
    annotations = deducted_a1 + deducted_a2 + ann3s + [ann4, ann5]
    return inference, annotations, len(annotations)


def _formula_from_variable(str_val: str):
    wrap = "({})"
    f = Formula(wrap.format(str_val))
    f.type = 'variable'
    f.is_complete = True
    return f



def _adequacy_recursive_helper(num: int, F: Formula, vector: dict):
    """
    Recursive helper for adequacy theorem function

    :param num:     int - last used index in inference sequence
    :param F:       Formula - tautology formula to be logically inferred thus proven to be a theorem
    :param vector:  dict - boolean vector represented as {'var_name': value} where value in {0; 1}
    :return:
    """
    if not any([v is None for v in vector.values()]):                                       # if vector already formed
        inference, annotations, inc = kalmar_theorem(num, F, vector)
        return inference, annotations, inc
    else:
        for xi, v in vector.items():
            if v is None:                                                                   # i-th coord is unfilled
                new_vector = {k: v for k, v in vector.items()}             # copy of filled part
                hyp = [_formula_from_variable(F) if val else _formula_from_variable(F).neg() for F, val in new_vector.items() if not val is None]
                new_vector[xi] = 0                                                          # fill as True
                f1s, ann1s, inc1 = _adequacy_recursive_helper(num, F, new_vector)           # recursive call left
                new_vector[xi] = 1                                                          # fill as False
                f2s, ann2s, inc2 = _adequacy_recursive_helper(num + inc1, F, new_vector)    # recursive call right
                fs, anns, inc = _inference_union(_formula_from_variable(xi), tuple(hyp), f1s, f2s, F)
                return fs, anns, inc
                                                                              # build hypothesis in prior


def adequacy_theorem(F: Formula):
    """
    Adequacy theorem implementation. If formula F is tautology it can be inferred as
    a theorem, formally     |=  F <-> |- F. If formula F is tautology - builds logical inference
    otherwise None

    :param F:
    :return:
    """
    if F.is_tautology():
        amt = len(F.get_vars())
        variables = tuple(sorted(F.get_vars()))
        vector = {v: None for v in variables}
        return _adequacy_recursive_helper(amt, F, vector)
    else:
        return None, None, None


if __name__ == '__main__':
    F = Formula("(F)")
    F.seq_num = 1
    F.is_complete = True
    F.type = "var"

    G = Formula("(G)")
    G.seq_num = 2
    G.is_complete = True
    G.type = "var"

    H = Formula("(H)")
    H.seq_num = 3
    H.is_complete = True
    H.type = "var"

    f1 = F.imp(F.neg().neg())
    f2 = F.neg().neg().imp(F)
    f3 = F.imp(F.neg().imp(G))
    f4 = F.imp(G).imp(G.neg().imp(F.neg()))
    # print(f1.is_tautology())

    f5 = F.imp(G).imp(F).imp(F)

    fs, anns, num = adequacy_theorem(f5)
    for an in anns:
        print(an, end='')