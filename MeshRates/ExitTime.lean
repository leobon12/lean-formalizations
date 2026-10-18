import MeshRates.Section3Heat

/-!
# Survival probability and expected exit time of the killed chain (MR §3, §6)

The process of MR (27) (rates `a(v,w)/m_v`) on a finite region `R`, absorbed on leaving
`S ⊆ R`, is the existing Poissonized uniformized chain `poissonizedUniformizedLaw` of `MeshOnly`.
`P_x(τ_S > t)` is the time-`t` law of that chain charged on `S`, as in `prop31_onDiagonal_and_survival`.
There is no path-space process with stopping times in the libraries, so the expected exit time is
defined by the layer-cake formula `E_x τ_S = ∫_0^∞ P_x(τ_S > t) dt`, valued in `[0, ∞]` (no junk
value from non-integrability).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal
open MeasureTheory

namespace BouRabeeGwynne.MeshRates

variable {d : ℕ}

open Classical in
/-- `P_x(τ_S > t)`: the probability that the chain with generator MR (27) on the finite region `R`,
started at `x` and absorbed on leaving `S`, is still in `S` at time `t`. -/
noncomputable def survivalProb (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    [MeasurableSpace R] (S : Set R) (x : R) (t : ℝ≥0) : ℝ :=
  ((T.finiteNetwork R).poissonizedUniformizedLaw (fun v : R => (T.cell v).volume.toReal)
    (fun v => cellVolume_toReal_pos T v) S x t S).toReal

/-- `E_x τ_S = ∫_0^∞ P_x(τ_S > t) dt` (layer-cake formula for the exit time of MR Lemma 6.1). -/
noncomputable def expectedExitTime (T : OrthogonalTiling d) (R : Set T.V) [Fintype R]
    [MeasurableSpace R] (S : Set R) (x : R) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (survivalProb T R S x t.toNNReal)

end BouRabeeGwynne.MeshRates
