import PrimalitySheafVerification.Mock2
import PrimalitySheafVerification.Mock2_Advanced
import PrimalitySheafVerification.Mock2_FunctionalAnalysis

/-!
# Integrated Mock2 functional-analysis interface

This module is intentionally a thin integration boundary. It re-exports the
checked-in elementary, advanced, and functional-analysis developments without
adding assumptions, axioms, or replacement declarations. Downstream modules,
including `QYM`, can import one stable dependency after all three component
modules have compiled directly from their checked-in sources.
-/
