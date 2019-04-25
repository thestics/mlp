"""
-> - implies
! - negation

formula is supposed to be wrapped in a parentheses
(xi) - formula
F formula => (! F) - formula
F, G formula => (F -> G) - formula

((x1) -> (x2))
((!(x1)) -> (x2)) -- main operation 'implication'
(!((x1) -> (x2))) -- main operation 'negation'

"""
imp = lambda a, b: int(not a or b)
neg = lambda a: int(not a)


class FormulaBase:
    """
    Base class for formula
    """

    __slots__ = ('str_val', 'operation', 'type', 'successors', 'is_complete', 'is_axiom', 'derived_by_mp_from', 'axiom_num', 'seq_num')

    def __init__(self, content):
        self.str_val = content        # string representation of formula
        self.is_complete = False      # is it totally packed?
        # stuff for more convenient implementation of deduction theorem                            -----
        self.is_axiom = False         # is it axiom                                                    |
        self.axiom_num = None         # if it is, which form (A1-A3) it meets?                         |
        self.seq_num = -1             # number in inference sequence                                   |
        self.derived_by_mp_from = []  # if we got this formula using Modus Ponens - from which exactly--
        self.operation = None         # 'IMP' 'NOT' - main operation
        self.type = None              # var/formula
        self.successors = []          # sub-formulas

    def __str__(self):
        return self.str_val

    def __repr__(self):
        return f"Formula({self.str_val})"

    def get_var_name(self):
        """
        Returns variable name if formula is variable

        :return: str
        """
        if self.type == 'var':
            return self.str_val[1:-1]
        else:
            return ''

    def set_type(self, type: str):
        self.type = type

    def set_operation(self, operation: str):
        self.operation = operation

    def add_successor(self, f):
        self.successors.append(f)

    def get_vars(self)-> set:
        """
        Collect a set of all variables present in formula

        :return:
        """
        if self.type == "var":
            return {self.str_val[1:-1],  }
        else:
            if self.operation == "IMP":
                left, right = self.successors
                lVars = left.get_vars()
                rVars = right.get_vars()
                return lVars.union(rVars)
            elif self.operation == "NOT":
                return self.successors[0].get_vars()

    def get_vars_as_formulas(self):
        """
        Collect a set of all variables present in formula and recast them
        to formulas

        :return:
        """
        data = self.get_vars()
        hyp = []
        temp = "({})"
        for i, var in enumerate(data):
            f = Formula(temp.format(var))
            f.is_complete = True
            f.type = 'var'
            f.seq_num = i + 1
            hyp.append(f)
        return hyp

    def __call__(self, **kwargs):
        if self.type == 'var':
            vName = self.get_var_name()
            assert vName, 'incorrect value'
            return kwargs[vName]
        else:
            if self.operation == "NOT":
                son = self.successors[0]
                return neg(son(**kwargs))
            elif self.operation == "IMP":
                left, right = self.successors
                return imp(left(**kwargs), right(**kwargs))

    def __eq__(self, other):
        if isinstance(other, Formula):
            return self.str_val == other.str_val


class Formula(FormulaBase):

    def __init__(self, content):
        super().__init__(content)

    def imp(self, f):
        """
        For another formula build self -> f formula

        :param f: Formula
        :return: Formula
        """
        content = "({} -> {})".format(self.str_val, f.str_val)
        new = Formula(content)
        new.operation = "IMP"
        new.successors = [self, f]
        new.type = "formula"
        new.is_complete = True
        return new

    def neg(self):
        """
        Builds !self formula

        :return:
        """
        content = "(!{})".format(self.str_val)
        new = Formula(content)
        new.operation = "NOT"
        new.successors = [self]
        new.type = "formula"
        new.is_complete = True
        return new

    @classmethod
    def copy(cls, F):
        """
        Copy constructor

        :param F: Formula
        :return: Formula object with all field copied
        """
        res = cls(F.str_val)
        res.is_complete = F.is_complete
        res.is_axiom = F.is_axiom
        res.axiom_num = F.axiom_num
        res.seq_num = F.seq_num
        res.derived_by_mp_from = F.derived_by_mp_from[:]
        res.operation = F.operation
        res.type = F.type
        res.successors = F.successors[:]
        return res

    def pow_alpha(self, vector):
        if self(**vector):
            return self
        else:
            return self.neg()

    def is_tautology(self):
        var = tuple(sorted(self.get_vars()))
        amt = len(var)
        for mask in range(1 << amt):
            strMask = '{0:0>{1}}'.format(bin(mask)[2:], amt)
            intMask = map(int, strMask)
            state = dict(zip(var, intMask))
            if not self(**state):
                return False
        return True
