"""
IMP - implies
NOT - negation

formula is supposed to be wrapped in a parentheses
(xi) - formula
F formula => (NOT F) - formula
F, G formula => (F IMP G) - formula

((((NOT (x2)) IMP (x3)) IMP (x1)) IMP ((x1) IMP (x1))) -- pay attention to spaces and ()

((x1) IMP (x2))
((NOT (x1)) IMP (x2)) -- main operation 'implication'
(NOT ((x1) IMP (x2))) -- main operation 'negation'


"""
imp = lambda a, b: int(not a or b)
neg = lambda a: int(not a)


class Formula:

    def __init__(self, content):
        self.str_val = content
        self.operation = None
        self.type = None
        self.successors = []

    def __str__(self):
        return self.str_val

    def get_var_name(self):
        if self.type == 'var':
            return self.str_val[1:-1]
        else:
            return ''

    def set_type(self, type: str):
        self.type = type

    def set_operation(self, oper: str):
        self.operation = oper

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
