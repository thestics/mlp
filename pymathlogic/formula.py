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


class Formula:

    def __init__(self, content):
        self.str_val = content
        self.operation = None
        self.type = None
        self.successors = []

    def __str__(self):
        return self.str_val

    def set_type(self, type: str):
        self.type = type

    def set_operation(self, oper: str):
        self.operation = oper

    def add_successor(self, f):
        self.successors.append(f)



