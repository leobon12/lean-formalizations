import BouRabeeGwynne.TheoremAProcessLaws
import MeshRates.Corollary12.UniformStoppedWalkConvergence
import MeshRates.Statement.Corollary12

/-! MR Corollary 1.2, stopped-walk part (BRG Theorem 4.1 / Theorem A without
alternatives (I)–(III)). Assembled exactly as `BouRabeeGwynne.theoremA_proved`
(TheoremAProved.lean:13), with `PaperRegularity G` replaced by the
`BallDirichletInput G` supplied by the mesh-only Theorem 1.1. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace BouRabeeGwynne.MeshRates

theorem corollary12_stoppedWalk : MeshRatesCorollary12StoppedWalkStatement := by
  intro d hd2 G N U hU hUb hUD happrox
  have hd : 1 ≤ d := by omega
  have hD : BallDirichletInput G :=
    ballDirichletInput_of_meshConverges hd2 (N.mesh_tendsto_zero happrox)
  obtain ⟨μ, hμ, hBrownian⟩ :=
    exists_standardBrownianLaw_with_stopped_laws hd hU.isDomain.1 hUb
  obtain ⟨walkLaw, hwalk⟩ := N.exists_eventually_stoppedWalkLaws hd U hUb hUD happrox
  refine ⟨μ, hμ, hBrownian, walkLaw, ?_, ?_⟩
  · filter_upwards [hwalk] with n hn
    intro z _
    exact hn z
  · intro η hη
    filter_upwards [hwalk, eventually_stoppedWalkLaw_levyProkhorov_le_of_ballDirichlet hd N
      hU.isDomain.1 hU.hasLipschitzBoundary hUb hUD happrox hD hμ hη] with n hn hconv
    intro z hz
    exact hconv z hz (walkLaw n z) (hn z)

end BouRabeeGwynne.MeshRates
