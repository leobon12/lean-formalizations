import QuantumZipper.Proofs.Thm18.ASepRawMatch
import QuantumZipper.Proofs.Thm18.ASepFreeBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP: the raw identity input `hraw` of `ASep.ae_exact_free_box` at a fixed parameter

`x_p(ν_p) = X(μ_p(0)) + detLimA0 p` a.s. (`ae_hraw_A0`), from the raw value at `τ' = 0`
(`ASep.ae_raw_A0`), the identification of its deterministic term with the engine limit
(`ASep.detLimA0_eq_raw`) and `ν_p = σ.map (a ψ)` on the image of the re-zipping map
(`ASep.mul_revMapInv_revDrv0_eq`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- `ν_p` is the A-sep pushed circle `σ.map (a ψ)`. -/
theorem nuA0_eq_map_psi {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ} {r : ℝ}
    {p : Fin 2 → ℝ} (hτ : 0 ≤ p 0) (ha : 0 < p 1)
    (hgd : ∀ᵐ w ∂foldedCircle d r, 0 < w.im ∧
      w ∈ revMap (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 '' H) :
    nuA0 W d r p = (foldedCircle d r).map fun w =>
      (p 1 : ℂ) * revMapInv (backDrv W (p 0) 0 (p 1)).2 (backDrv W (p 0) 0 (p 1)).1 w := by
  unfold nuA0
  refine Measure.map_congr ?_
  filter_upwards [hgd] with w hw
  exact (mul_revMapInv_revDrv0_eq hW hW0 hτ ha hw.2 hw.1).symm

end ASep
end QuantumZipper
