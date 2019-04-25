"""
Mathematical logic package, whose main purpose for now is to build logical inference to any tautology formula
from propositional calculus. Also implemented few helper theorems.
"""


from .formula_parser import FormulaParser
from .formula import Formula
from .logic_inference import adequacy_theorem


__all__ = ['Formula', 'FormulaParser', 'adequacy_theorem']
