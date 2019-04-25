"""

"""
from .formula import Formula
from .theorems import *


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
    """
    helper function to search through inference list for a given formula and
    to retrieve it back

    :param F: Formula
    :param inf_list: list - inference list
    :return: Formula object/None
    """
    for g in inf_list:
        if F == g:
            return g
    return None


def _kalmar_helper(F: Formula, hypothesis: tuple, inf_list: list, ann_list: list, vector: dict, num: int):
    """
    Recursive helper function for Kalmar theorem

    :param F: formula - current formula
    :param hypothesis: tuple - logical inference hypothesis
    :param inf_list: list - global inference list
    :param ann_list: list - global inference list annotation
    :param vector:  dict - given boolean vector
    :return: None
    """
    if F in hypothesis:
        index = 1 if not inf_list else inf_list[-1].seq_num + 1
        f, ann = from_hypothesis(index, F)
        inf_list.append(f)
        ann_list.append(ann)
        return
    if F.type == "var":
        if inf_list:
            f, ann = from_hypothesis(inf_list[-1].seq_num + 1, F.pow_alpha(vector))
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
                f2 = _get_formula_from(G, inf_list)                              # G
                f3, ann3 = MP(f1.seq_num + 1, f2, f1)                            # !!G
                fs = list(f1s) + [f3]
                anns = ann1s + [ann3]
                inf_list.extend(fs)
                ann_list.extend(anns)
                return
        elif op == "IMP":
            G, H = F.successors                                                  # F = G -> H
            _kalmar_helper(G, hypothesis, inf_list, ann_list, vector, num)
            _kalmar_helper(H, hypothesis, inf_list, ann_list, vector, num)
            if G(**vector) == 0:
                f1s, ann1s, inc = theorem_t3(inf_list[-1].seq_num, G, H)         # !G -> (G - > H)
                f1 = f1s[-1]
                f2 = _get_formula_from(G.neg(), inf_list)                        # ... |- !G
                f3, ann3 = MP(f1.seq_num + 1, f2, f1)                            # ... |- (G -> H)
                fs = list(f1s) + [f3]
                anns = list(ann1s) + [ann3]
                inf_list.extend(fs)
                ann_list.extend(anns)
                return
            elif H(**vector) == 1:
                f1, ann1 = axiom_A1(inf_list[-1].seq_num + 1, H, G)              # H -> (G -> H)
                f2 = _get_formula_from(H.pow_alpha(vector), inf_list)            # ... |- H
                f3, ann3 = MP(f1.seq_num + 1, f2, f1)                            # (G -> H)
                fs = [f1, f3]
                anns = [ann1, ann3]
                inf_list.extend(fs)
                ann_list.extend(anns)
                return
            elif G(**vector) == 1 and H(**vector) == 0:
                f1 = _get_formula_from(G.pow_alpha(vector), inf_list)            # ... |- G
                f2 = _get_formula_from(H.pow_alpha(vector), inf_list)            # ... |- !H
                f3s, ann3s, inc = theorem_t6(inf_list[-1].seq_num, G, H)         # G -> (!H -> !(G -> H))
                f3, ann3 = f3s[-1], ann3s[-1]
                f4, ann4 = MP(f3.seq_num + 1, f1, f3)                            # !H -> !(G -> H)
                f5, ann5 = MP(f4.seq_num + 1, f2, f4)                            # !(g -> h)
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


def _inference_union(xn: Formula, hypothesis: list, inf1: list, inf2: list, F: Formula):
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
    f3s, ann3s, inc3 = theorem_t7(f2.seq_num, xn, F)                                    # (xn -> F) -> ((!xn -> F) -> F)
    f3 = f3s[-1]
    f4, ann4 = MP(f3s[-1].seq_num + 1, f2, f3)                                          # ((!xn -> F) -> F)
    f5, ann5 = MP(f4.seq_num + 1, f1, f4)                                               # F

    inference = list(deducted_f1) + list(deducted_f2) + list(f3s) + [f4, f5]
    annotations = deducted_a1 + deducted_a2 + ann3s + [ann4, ann5]
    return inference, annotations, len(annotations)


def _formula_from_variable(str_val: str):
    """
    Transforms a variable name string into a standalone formula object

    :param str_val: variable name
    :return: Formula
    """
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
                new_vector = {k: v for k, v in vector.items()}                              # copy a filled part
                # for each variable X used in formula and given vector V of values assigned to ths variables if
                # corresponding variable == 1 - add X, otherwise add !X and avoid adding unfilled coordinates which
                # are supposed to be filled recursively
                hyp = [_formula_from_variable(F) if val else _formula_from_variable(F).neg()\
                       for F, val in new_vector.items() if not val is None]
                new_vector[xi] = 0                                                          # fill as True
                f1s, ann1s, inc1 = _adequacy_recursive_helper(num, F, new_vector)           # recursive call left
                new_vector[xi] = 1                                                          # fill as False
                f2s, ann2s, inc2 = _adequacy_recursive_helper(num + inc1, F, new_vector)    # recursive call right
                fs, anns, inc = _inference_union(_formula_from_variable(xi), hyp, f1s, f2s, F)
                return fs, anns, inc


def adequacy_theorem(F: Formula):
    """
    Adequacy theorem implementation. If formula F is tautology it can be inferred as
    a theorem, formally     |=  F <-> |- F. If formula F is tautology - builds logical inference
    otherwise returns None

    :param F: Formula
    :return:
    """
    if F.is_tautology():
        amt = len(F.get_vars())
        variables = tuple(sorted(F.get_vars()))     # get_vars returns unordered set, we'll sort it to restore order
        vector = {v: None for v in variables}       # vector skeleton "xi": val_i
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

    fs, anns, num = adequacy_theorem(f1)
    for an in anns:
        print(an, end='')
