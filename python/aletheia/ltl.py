"""LTL DSL for temporal properties"""

from typing import Any, Dict, Optional


class LTL:
    """Linear Temporal Logic formula builder"""
    
    @staticmethod
    def always(formula: Any) -> 'LTLFormula':
        """Always/Globally operator (G φ)"""
        return LTLFormula('always', formula)
    
    @staticmethod
    def eventually(formula: Any, within: Optional[float] = None) -> 'LTLFormula':
        """Eventually/Finally operator (F φ), optionally bounded"""
        if within is not None:
            return LTLFormula('eventually_within', formula, within)
        return LTLFormula('eventually', formula)
    
    @staticmethod
    def next(formula: Any) -> 'LTLFormula':
        """Next operator (X φ)"""
        return LTLFormula('next', formula)
    
    @staticmethod
    def never(formula: Any) -> 'LTLFormula':
        """Never (¬F φ)"""
        return LTLFormula('never', formula)
    
    @staticmethod
    def implies(antecedent: Any, consequent: Any) -> 'LTLFormula':
        """Implication (φ → ψ)"""
        return LTLFormula('implies', antecedent, consequent)
    
    @staticmethod
    def both(left: Any, right: Any) -> 'LTLFormula':
        """Conjunction (φ ∧ ψ)"""
        return LTLFormula('and', left, right)
    
    @staticmethod
    def either(left: Any, right: Any) -> 'LTLFormula':
        """Disjunction (φ ∨ ψ)"""
        return LTLFormula('or', left, right)
    
    @staticmethod
    def until(left: Any, right: Any) -> 'LTLFormula':
        """Until operator (φ U ψ)"""
        return LTLFormula('until', left, right)
    
    @staticmethod
    def before(event: Any, must_have: Any) -> 'LTLFormula':
        """Before pattern: must_have must occur before event"""
        return LTL.until(LTL.never(event), must_have)


class LTLFormula:
    """LTL formula representation"""
    
    def __init__(self, operator: str, *args: Any):
        self.operator = operator
        self.args = args
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        result: Dict[str, Any] = {'operator': self.operator}
        
        if self.args:
            result['args'] = [
                arg.to_dict() if hasattr(arg, 'to_dict') else arg
                for arg in self.args
            ]
        
        return result
