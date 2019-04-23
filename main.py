from pymathlogic import *


if __name__ == '__main__':
    # tests
    f1 = "((f) -> ((!(f)) -> (g)))"
    f2 = "((f) -> (!(!(f))))"
    f3 = "((!(!(f))) -> (f))"
    f4 = "(((f) -> (g)) -> ((!(g)) -> (!(f))))"
    f5 = "(((!(g)) -> (!(f))) -> ((f) -> (g)))"

    p1 = parse_formula(f2).parse()
    fs, anns, inc = adequacy_theorem(p1)
    with open('output.txt', 'w') as f:   # formula f4 fully derived took 200k formulas and 500mb to be written in file
        f.writelines(anns)
    # for an in anns:
    #     print(an, end='')
