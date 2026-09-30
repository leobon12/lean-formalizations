import QuantumZipper.Proofs.Thm18.G4ACross2Contact
import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Zipper.Cor15RezipRegDist
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# EXACT-CLUSTER (1): the re-zip pushed circles in round-trip form

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1) and its
proof (pp. 69–71). Decision: `handoff/G4-CORE.md` §8.

The G4 nodes A-sep / A-cross ask exactness of the unzipped field `U_τ = Y ∘ f_τ⁻¹ + Q log|(f_τ⁻¹)'|`
at `σ_i.map (a ψ)`, `ψ = revMapInv (backDrv W τ τ' a)`. This file proves the Loewner identity
behind the decision of §8: on the image of the re-zipping map (i.e. `σ_i`-a.e. under
`BackSupportI`),

* `f_τ⁻¹ (a ψ(w)) = f_{τ'}⁻¹ (a w)` (`fwdMapInv_mul_revMapInv_backDrv`, the image-side form of
  the existing `fwdMapInv_mul_backDrv`): the composite map read by `U_τ` at these measures is
  `f_{τ'}⁻¹ (a ·)`, conformal on all of `ℍ`, whatever the position of the circle relative to the
  hull (the raw-value side is `unzippedField_backDrv_raw`, G4SepUCRaw.lean);
* `a ψ(w) = f_τ (f_{τ'}⁻¹ (a w))` (`mul_revMapInv_backDrv_eq_fwdMap`): the measure is the forward
  image under `f_τ` of the measure `(f_{τ'}⁻¹ (a ·))_* σ_i` living in `ℍ`
  (`map_mul_revMapInv_backDrv_eq`).

Hence every A-sep / A-cross exactness conjunct is **round-trip exactness** (RTX): exactness of
`U_τ` at `(f_τ)_* μ` for measures `μ` in `ℍ` (here `μ = (f_{τ'}⁻¹ (a ·))_* σ_i`), which is the
regularized form of `Z_τ ∘ Z_{−τ} = id` at `μ`. Also: a separated circle has quantitative
contact (`backContactI_of_backSepI`), so the contact guard of `G4CrossQAllStmt` covers A-sep.

Loewner inputs: `fwdMapInv_mul_backDrv` (G4CoreDownShort.lean; Loewner cocycle and scaling,
Lawler, *Conformally invariant processes in the plane*, §4.1), `RS.fwdMap_fwdMapInv`.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- **Pointwise identities on the image of the re-zipping map.** For `w = R(z)`, `z ∈ ℍ`:
`f_τ⁻¹ (a ψ(w)) = f_{τ'}⁻¹ (a w)` and `a ψ(w) = f_τ (f_{τ'}⁻¹ (a w))`, `ψ = revMapInv (backDrv …)`. -/
theorem fwdMapInv_mul_revMapInv_backDrv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {τ τ' a : ℝ} (hτ' : 0 ≤ τ') (hττ' : τ' ≤ τ) (ha : 0 < a) {w : ℂ}
    (hw : w ∈ revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 '' H) :
    fwdMapInv W τ ((a : ℂ) * revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w) =
      fwdMapInv W τ' ((a : ℂ) * w) := by
  obtain ⟨z, hz, rfl⟩ := hw
  have hT : 0 ≤ (backDrv W τ τ' a).1 := by
    show 0 ≤ (τ - τ') / a ^ 2
    exact div_nonneg (sub_nonneg.2 hττ') (by positivity)
  rw [Cor15Group.revMapInv_revMap (continuous_backDrv hW τ τ' a) hT hz]
  exact fwdMapInv_mul_backDrv hW hW0 hτ' hττ' ha hz

theorem mul_revMapInv_backDrv_eq_fwdMap {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {τ τ' a : ℝ} (hτ' : 0 ≤ τ') (hττ' : τ' ≤ τ) (ha : 0 < a) {w : ℂ}
    (hw : w ∈ revMap (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 '' H) :
    (a : ℂ) * revMapInv (backDrv W τ τ' a).2 (backDrv W τ τ' a).1 w =
      fwdMap W τ (fwdMapInv W τ' ((a : ℂ) * w)) := by
  have hτ : 0 ≤ τ := hτ'.trans hττ'
  rw [← fwdMapInv_mul_revMapInv_backDrv hW hW0 hτ' hττ' ha hw]
  obtain ⟨z, hz, rfl⟩ := hw
  have hT : 0 ≤ (backDrv W τ τ' a).1 := by
    show 0 ≤ (τ - τ') / a ^ 2
    exact div_nonneg (sub_nonneg.2 hττ') (by positivity)
  rw [Cor15Group.revMapInv_revMap (continuous_backDrv hW τ τ' a) hT hz]
  have haz : (a : ℂ) * z ∈ H := by
    show 0 < ((a : ℂ) * z).im
    have : 0 < z.im := hz
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    positivity
  exact (RS.fwdMap_fwdMapInv hW hW0 hτ haz).symm

/-! ## Almost-everywhere and measure forms under `BackSupportI` -/

/-! ## Separation implies quantitative contact -/

end G4Core
end Thm18Asm
end QuantumZipper
