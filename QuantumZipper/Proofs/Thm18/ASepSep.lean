import QuantumZipper.Proofs.Thm18.G4WeldRem

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP: the separation `BackSepI` at `τ' = 0` in forward coordinates

At `τ' = 0`, `backDrv W τ 0 a = revDrv W τ a` (`G4Core.backDrv_zero`) and the reverse hull of this rescaled time reversal
is the dilated forward hull: `revHull (revDrv W τ a) = {w ∈ ℍ : a w ∈ K_τ}`
(`revHull_revDrv_eq`; the inclusion `⊆` is `Thm18Asm.revHull_revDrv_subset`, the inclusion `⊇`
is proved here from `Thm18Asm.revMap_revDrv` and `Cor15Group.revHull_vrev_eq_fwdHull`). Hence the
separation hypothesis `BackSepI` of A-sep at `τ' = 0` says that the circle is at positive distance
from `a⁻¹ K_τ`, the form used by the parameter set `ASep.ParGood`. Loewner scaling and time
reversal (Lawler, *Conformally invariant processes in the plane*, §4.1); own bookkeeping.
-/

noncomputable section

open MeasureTheory Set

namespace QuantumZipper
namespace ASep

open Thm18Asm

/-- `{w ∈ ℍ : a w ∈ K_τ} ⊆ revHull (revDrv W τ a)`. -/
theorem subset_revHull_revDrv {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ a : ℝ}
    (hτ : 0 < τ) (ha : 0 < a) :
    {w : ℂ | w ∈ H ∧ (a : ℂ) * w ∈ fwdHull W τ} ⊆ revHull (revDrv W τ a).2 (revDrv W τ a).1 := by
  rintro w ⟨hwH, hwK⟩
  refine ⟨hwH, fun ⟨y, hy, hyw⟩ => ?_⟩
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [← Cor15Group.revHull_vrev_eq_fwdHull hW hW0 hτ] at hwK
  refine hwK.2 ⟨(a : ℂ) * y, ?_, ?_⟩
  · show 0 < ((a : ℂ) * y).im
    have : 0 < y.im := hy
    simpa using mul_pos ha this
  · rw [← hyw, revMap_revDrv hW hτ.le ha hy, mul_div_cancel₀ _ haC]

/-- **The reverse hull at `τ' = 0` is the dilated forward hull.** -/
theorem revHull_revDrv_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {τ a : ℝ}
    (hτ : 0 < τ) (ha : 0 < a) :
    revHull (revDrv W τ a).2 (revDrv W τ a).1 = {w : ℂ | w ∈ H ∧ (a : ℂ) * w ∈ fwdHull W τ} := by
  refine subset_antisymm (fun w hw => ⟨hw.1, ?_⟩) (subset_revHull_revDrv hW hW0 hτ ha)
  obtain ⟨z, hz, rfl⟩ := revHull_revDrv_subset hW hW0 hτ ha hw
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [← mul_assoc, mul_inv_cancel₀ haC, one_mul]
  exact hz

end ASep
end QuantumZipper
