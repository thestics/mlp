from pymathlogic import *


if __name__ == '__main__':
    # vals = {'x1': 0, 'x2': 0, 'x3': 1}
    f1 = "((x1) IMP ((x2) IMP (x1)))"
    f2 = "(((F) -> ((G) -> (H))) -> (((F) -> (G)) -> ((F) -> (H))))"
    f2 = f2.replace('->', 'IMP')
    f3 = "(((G) -> (!(F))) -> (((!(G)) -> (F)) -> (G)))"
    f3 = f3.replace('!', 'NOT')
    f3 = f3.replace('->', 'IMP')
    # f2 = "(((F) IMP ((G) IMP (H)) IMP (((F) IMP (G)) IMP ((F) IMP (H))))"
    p = parse_formula(f3).parse()
    print(p.is_tautology())
    # p = parse_formula("((((NOT (x2)) IMP (x3)) IMP (x1)) IMP ((x1) IMP (x1)))").parse()
    # vals = {'x1': 1, 'x2': 1, 'x3': 0}
    # print(p.get_vars())