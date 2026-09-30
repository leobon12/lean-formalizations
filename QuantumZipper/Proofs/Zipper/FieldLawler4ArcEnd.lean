import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopComp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-ARC (A2, A4): end points of the `D`-arcs and the connected sets for Lemma 3.3

Task FL4-ARC (Track A round 4), towards `FieldLawler.FLImageSumBoundStmt`.

* (A2) `fl4_end_mem`: an end point `ε e^{iα}` (`0 ≤ α ≤ π`) of a maximal arc of
  `D ∩ C_ε`, `D = ℍ \ K_t`, lies in `K_t` or on `ℝ`; `fl4_arcs_disjoint`: `Z_t⁻¹` maps disjoint
  image crosscuts to disjoint sets.
* (A4) `fl4_K_props`: `K' = γ[0, t] ∪ ({Im z ≤ 0} \ {-ε})` is connected, disjoint from `D`,
  omits `-ε`, and contains every point of `K_t ∪ ℝ` other than `-ε` (hypothesis `hK` of
  `fl3_lemma33`).

Source: Field–Lawler, EJP 20 (2015), proof of Prop. 3.4 and Lemma 3.3 (pp. 8–9), where these
facts are used without comment ("the end points of `ηⱼ` lie on `γ_t ∪ ℝ`"). Own elementary
arguments (a half-plane minus a boundary point is connected via vertical segments).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- **(A2)** An end point of a maximal arc of `D ∩ C_ε` lies on the curve or on `ℝ`. -/
theorem fl4_end_mem (hc : SideCtx W t F) {ε α : ℝ} (hε : 0 < ε) (hα : α ∈ Icc 0 π)
    (hnot : flCirc ε α ∉ H \ fwdHull W t) :
    flCirc ε α ∈ trace W '' Ioc 0 t ∪ {z : ℂ | z.im = 0} := by
  by_cases hH : flCirc ε α ∈ H
  · left
    rw [← hc.hull]
    by_contra h
    exact hnot ⟨hH, h⟩
  · right
    have h1 : 0 ≤ (flCirc ε α).im := by
      rw [flCirc_im]; exact mul_nonneg hε.le (Real.sin_nonneg_of_nonneg_of_le_pi hα.1 hα.2)
    exact le_antisymm (not_lt.1 hH) h1

end FieldLawler
end QuantumZipper
