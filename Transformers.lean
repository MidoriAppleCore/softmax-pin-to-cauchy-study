/-
Library root for Lake only: pulls in every local module so sibling `.olean` files
are built before the `Main` executable target.

(`lean_exe` alone may schedule `Main` before local imports are compiled.)
-/
import CauchyTheory
import AxiomAudit
import Part5_GeodesicConjecture
import GeodesicIntegration
