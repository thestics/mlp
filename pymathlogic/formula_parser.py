# from . import formula
import formula


Formula = formula.Formula


class parse_formula:

    def __init__(self, string):
        self.root = None
        self._raw = string
        self._remove_extra_spaces()

    def _remove_extra_spaces(self):     # attempt to make it more efficient than straightforward while true s.replace('  ', ' ')
        cpy = ''
        space_layer = 0                 # amt of spaces already encountered
        last_char_parent = False
        for c in self._raw.strip():
            if c != ' ':                # non-space -- free to add
                if space_layer != 0:
                    space_layer = 0
                if c in '()':           # avoid '( ( ( ( (...'
                    last_char_parent = True
                else:
                    last_char_parent = False
                cpy += c
            if c == ' ' and space_layer == 0 and not last_char_parent:   # space and no spaces in current sequence of spaces -- free to add
                space_layer += 1
                cpy += c
            if c == ' ' and space_layer > 0:    # if at least one space was already added in a row -- skip
                space_layer += 1
        self._raw = cpy

    def _find_main_operation(self, string):
        layer = 0
        for i in range(len(string)):  # skip 1st open parentheses
            if string[i] == '(':
                layer += 1
            elif string[i] == ')':
                layer -= 1
            if i > 0 and layer == 1:
                j1 = string.find("IMP", i, i + 6)    # )_IMP_ with/without spaces <= 6 chars, redundant spaces is to be removed
                j2 = string.find("NOT", i, i + 6)
                if j1 == -1 and j2 == -1:
                    return i, None  # simple variable
                if j1 != -1:
                    return j1, "IMP"
                if j2 != -1:
                    return j2, "NOT"

    def parse(self):
        cur = Formula(self._raw)
        self.root = cur
        self._parse(cur)
        return self.root

    def _parse(self, cur_formula):
        i, token = self._find_main_operation(cur_formula.str_val)
        if token is None:                   # formula is a variable (base case)
            cur_formula.set_type("var")
            return
        elif token == "IMP":
            cur_formula.set_type("formula")
            cur_formula.set_operation("IMP")
            left_str_val = cur_formula.str_val[1:i]           # avoid start '('
            right_start = cur_formula.str_val.find("(", i + 1)  # avoid inconsistency in spaces before and after operation
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
