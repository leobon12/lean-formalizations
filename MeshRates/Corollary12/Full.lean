import MeshRates.Corollary12.AssumptionD
import MeshRates.Corollary12.HarmonicMeasure
import MeshRates.Corollary12.StoppedWalk

/-!
# MR Corollary 1.2 in full

Assumption D from the mesh hypothesis alone (MR §7), the harmonic-measure conclusion of BRG
Proposition 4.2 and the stopped-walk conclusion of BRG Theorem 4.1, without alternatives (I)–(III).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace BouRabeeGwynne.MeshRates

/-- MR Corollary 1.2. -/
theorem corollary12_full : MeshRatesCorollary12Statement :=
  ⟨corollary12_assumptionD, corollary12_harmonicMeasure, corollary12_stoppedWalk⟩

end BouRabeeGwynne.MeshRates
