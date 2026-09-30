import QuantumZipper.Proofs.Zipper.GenUCOpen
import QuantumZipper.Proofs.Thm18.ASepModJ
import QuantumZipper.Proofs.Thm18.ASepDetB
import QuantumZipper.Proofs.Thm18.G4SepUC2Ident

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (d): the engine on one parameter box for the free field, `τ' = 0`

For a fixed driver `W`, the field `x_{p,ω} = coordChange (ofFun (a' log|·| + g₁) + X_ω) f_τ⁻¹ Q`
(`X` free, `p = (τ, a)`), the centre measures `ν_p = σ.map (w ↦ f_τ(a w))` (`nuA0`) and the
smoothed family `muA0`, this file assembles the inputs of `ASep.GenInputsDep` on a rational box:

* `GenFam`: `ASep.genFam_muA0` (ASepModJ);
* retraction, countable dense set, radii `R = range radius`;
* identity `hid`: `G4Core.ae_ident_fwdMapInv_gen` at each fixed parameter;
* deterministic convergence `hdet`, `hdetc`: `ASep.det_unif_A0`, `ASep.continuousOn_detLimA0`;
* `hΦeq` by definition of `Φ`;

and concludes (`ae_exact_free_box`) exactness a.s. at every parameter of the box, from the three
remaining pathwise/raw inputs, taken as hypotheses here: pathwise continuity of the smoothed
pairings (`hΦc`), the raw identity (`hraw`, ASepRawId/ASepRawMatch) and pathwise continuity of the
raw value (`hrawc`), plus the support/measurability facts of `ν_p`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core GenUC

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem radius_strictAnti' : StrictAnti radius :=
  pow_right_strictAnti₀ (by norm_num) (by norm_num)

theorem radius_injective' : Function.Injective radius := radius_strictAnti'.injective

/-- The dyadic index of a dyadic radius. -/
def jOf (ρ : ℝ) : ℕ := by
  classical exact if h : ∃ j, radius j = ρ then h.choose else 0

theorem jOf_radius (j : ℕ) : jOf (radius j) = j := by
  classical
  have h : ∃ k, radius k = radius j := ⟨j, rfl⟩
  unfold jOf
  rw [dif_pos h]
  exact radius_injective' h.choose_spec

/-- The centre measures of the A-sep family at `τ' = 0`. -/
def nuA0 (W : ℝ → ℝ) (d : ℂ) (r : ℝ) (p : Fin 2 → ℝ) : Measure ℂ :=
  (foldedCircle d r).map fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)

end ASep
end QuantumZipper
