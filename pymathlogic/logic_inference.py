"""

"""
# from .formula import Formula

import formula

Formula = formula.Formula

def axiom_A1(num, F, G):
    formula = F.imp(G.imp(F))
    annotation = "F_{num}: {formula} - Axiom A1 applied to: F: {F}, G: {G}\n"
    return formula, annotation.format(num=num, formula=formula, F=F, G=G)


def axiom_A2(num, F, G, H):
    left = F.imp(G.imp(H))
    right = (F.imp(G)).imp(F.imp(H))
    formula = left.imp(right)
    annotation = "F_{num}: {formula} - Axiom A2 applied to: F: {F}, G: {G}, H: {H}\n"
    return formula, annotation.format(num=num, formula=formula, F=F, G=G, H=H)


def axiom_A3(num, F, G):
    left = G.neg().imp(F.neg())
    right = (G.neg().imp(F)).imp(G)
    formula = left.imp(right)
    annotation = "F_{num}: {formula} - Axiom A3 applied to: F: {F}, G: {G}\n"
    return formula, annotation.format(num=num, F=F, G=G)


def MP(num, F, G, fNum, gNum):
    """

    :param num: start num
    :param F:   formula "A"
    :param G:   formula "A -> B:
    :param fNum: formula F global num
    :param gNum: formula G global num
    :return:
    """
    assert G.operation == "IMP", 'Incorrect MP application'
    assert G.successors[0].str_val == F.str_val
    formula = G.successors[1]
    annotation = "F_{num}: {formula} - Modus ponens rule applied to F_{fNum} and F_{gNum}\n"
    return formula, annotation.format(num=num, formula=formula, fNum=fNum, gNum=gNum)


def theorem_el(F, cur_num):
    f1, ann1 = axiom_A2(cur_num, F, F.imp(F), F)
    f2, ann2 = axiom_A1(cur_num+1, F, F.imp(F))
    f3, ann3 = MP(cur_num+2, f2, f1, cur_num, cur_num+1)
    f4, ann4 = axiom_A1(cur_num+3, F, F)
    f5, ann5 = MP(cur_num+4, f4, f3, cur_num+2, cur_num+3)
    fs = (f1, f2, f3, f4, f5)
    anns = (ann1, ann2, ann3, ann4, ann5)
    return fs, anns, cur_num+5






if __name__ == '__main__':
    # num = 1
    # A = "A"
    # B = "A -> B"
    # f, ann = MP(num, A, B, 1, 2)
    # print(f)
    # print(ann)
    F = Formula("(F)")
    F.is_complete = True
    F.operation = None
    F.type = "var"
    fs, anns, cur_num = theorem_el(F, 1)
    for f in anns:
        print(f, end='')
