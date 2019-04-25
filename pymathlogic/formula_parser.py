from .formula import Formula
import re


class FormulaParser:

    def __init__(self, string):
        self.root = None
        self._raw = string
        self._remove_extra_spaces()

    def _remove_extra_spaces(self):
        self._raw = self._raw.strip()           # extra spaces before-after
        p1 = ' +'
        p2 = '\( +'
        p3 = ' +\)'
        self._raw = re.sub(p1, ' ', self._raw)  # multiple spaces in a row -> one space
        self._raw = re.sub(p2, '(', self._raw)  # spaces between parentheses - remove at all
        self._raw = re.sub(p3, ')', self._raw)

    def _find_main_operation(self, string):
        """
        Helper function for main operation token search in string

        :param string: raw string
        :return: None
        """
        layer = 0
        for i in range(len(string)):  # skip 1st open bracket
            if string[i] == '(':
                layer += 1
            elif string[i] == ')':
                layer -= 1
            if i > 0 and layer == 1:
                j1 = string.find("->", i, i + 4)    # spaces before-after operator is to be considered
                j2 = string.find("!", i, i + 3)
                if j1 == -1 and j2 == -1:
                    return i, None                  # it is a simple variable
                if j1 != -1:
                    return j1, "IMP"
                if j2 != -1:
                    return j2, "NOT"

    def parse(self):
        """
        Main parsing method

        :return: parser formula object
        """
        cur = Formula(self._raw)
        self.root = cur
        self._parse(cur)
        self.root.is_complete = True
        return self.root

    def _parse(self, cur_formula):
        """
        Parser helper method

        :param cur_formula: current formula object
        :return: None
        """
        i, token = self._find_main_operation(cur_formula.str_val)
        if token is None:                   # formula is a variable (base case)
            cur_formula.set_type("var")
            return
        elif token == "IMP":
            cur_formula.set_type("formula")
            cur_formula.set_operation("IMP")
            left_str_val = cur_formula.str_val[1:i - 1]           # avoid start '('
            # avoid inconsistency in spaces before and after operation
            right_start = cur_formula.str_val.find("(", i + 1)
            right_str_val = cur_formula.str_val[right_start:-1]     # avoid end ')'
            left_form = Formula(left_str_val)
            right_form = Formula(right_str_val)
            cur_formula.add_successor(left_form)
            cur_formula.add_successor(right_form)
            self._parse(left_form)
            self._parse(right_form)
            return
        elif token == "NOT":
            cur_formula.set_type("formula")
            cur_formula.set_operation("NOT")
            right_start = cur_formula.str_val.find("(", i + 1)
            right_str_val = cur_formula.str_val[right_start:-1]
            right_form = Formula(right_str_val)
            cur_formula.add_successor(right_form)
            self._parse(right_form)
            return


if __name__ == '__main__':
    # vals = {'x1': 0, 'x2': 0, 'x3': 1}
    f1 = "((x1) -> ((x2) -> (x1)))"
    f2 = "(((F) -> ((G) -> (H))) -> (((F) -> (G)) -> ((F) -> (H))))"
    # f2 = f2.replace('->', 'IMP')
    f3 = "(((!(G)) -> (!(F))) -> (((!(G)) -> (F)) -> (G)))"
    # f3 = f3.replace('!', 'NOT')
    # f3 = f3.replace('->', 'IMP')
    # f2 = "(((F) IMP ((G) IMP (H)) IMP (((F) IMP (G)) IMP ((F) IMP (H))))"
    p = FormulaParser(f1).parse()
    print(p.is_tautology())
    # p = parse_formula("((((NOT (x2)) IMP (x3)) IMP (x1)) IMP ((x1) IMP (x1)))").parse()
    # vals = {'x1': 1, 'x2': 1, 'x3': 0}
    # print(p.get_vars())
