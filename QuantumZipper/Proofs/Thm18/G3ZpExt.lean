import QuantumZipper.Proofs.Thm18.G3ZpLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Z-PARTNER (5): the local maps of a good path extend continuously to the boundary

The locality lemmas of G3ZpLoc (`g3zoomLawM_eventually_iff_ball`, `g3zoomLawM_bump_iff`) ask
that the local map `g3mapP Ψ left (y, a, 1, x)` agree on `H` near `0` with a map continuous on
`closedBall 0 ρ ∩ Hbar`, mapping it into `Hbar` and fixing `0`. `g3mapP_ext` supplies this at every
point `x` of the side half-line when the side map has a Schwarz reflection across the side
half-line (`SideReflGood`, the a.s. property of `G1SideReflStmt`) and maps `H` into `H`
(`PsiGood`, from any measurable selection).

The extension is `w ↦ Ψ̃(w + Φ⁻¹(x)) − x` with `Ψ̃` the reflected map. Own elementary proof
(AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zp

open G3Z2b2 G1ZZ1

/-- **Continuous boundary extension of the local map at a side point.** -/
theorem g3mapP_ext {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} {left : Bool} {a : ℝ≥0 → ℝ}
    (hψH : MapsTo (Ψ left a) H H) {Φ : ℝ ≃o ℝ} (hR : SideReflGood left (Ψ left a) Φ) {x : ℝ}
    (hx : x ∈ g1SideHalf left) (y : FieldSample) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ Φ₁ : ℂ → ℂ, ContinuousOn Φ₁ (closedBall 0 ρ ∩ Hbar) ∧
      MapsTo Φ₁ (closedBall 0 ρ ∩ Hbar) Hbar ∧
      EqOn (g3mapP Ψ left (y, a, 1, x)) Φ₁ (closedBall 0 ρ ∩ H) ∧ Φ₁ 0 = 0 := by
  set B : ℝ := Φ.symm x with hBdef
  have hB : B ∈ g1SideHalf left := (mem_half_symm_iff hR.1 left x).2 hx
  have hΦB : Φ B = x := Φ.apply_symm_apply x
  have hpre : g3bpre Ψ left a x = B := g3bpre_eq hR hx
  have hB0 : B ≠ 0 := by
    cases left <;> simp only [g1SideHalf, Bool.false_eq_true, if_false, if_true, mem_Ioi,
      mem_Iio] at hB <;> linarith
  set δ : ℝ := |B| / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hIcc : Icc (B - δ) (B + δ) ⊆ g1SideHalf left := by
    intro t ht
    cases left <;> simp only [g1SideHalf, Bool.false_eq_true, if_false, if_true, mem_Ioi,
      mem_Iio] at hB ⊢
    · rw [abs_of_pos hB] at hδ; linarith [ht.1]
    · rw [abs_of_neg hB] at hδ; linarith [ht.2]
  obtain ⟨U, Ψt, hUo, hmemU, hdiff, hΦeq, -, heqH⟩ :=
    hR.2 (B - δ) (B + δ) (by linarith) hIcc
  have hBU : (B : ℂ) ∈ U := hmemU B ⟨by linarith, by linarith⟩
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hUo _ hBU
  set ρ : ℝ := min ε δ / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    have := min_le_left ε δ; rw [hρ]; linarith
  have hρδ : ρ ≤ δ := by
    have := min_le_right ε δ; rw [hρ]; linarith
  have hmapsU : ∀ w ∈ closedBall (0 : ℂ) ρ, w + (B : ℂ) ∈ U := fun w hw => hεU (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
    exact lt_of_le_of_lt (by simpa using hw) hρε)
  refine ⟨ρ, hρ0, fun w => Ψt (w + (B : ℂ)) - (x : ℂ), ?_, ?_, ?_, ?_⟩
  · refine ContinuousOn.sub ?_ continuousOn_const
    exact hdiff.continuousOn.comp (continuousOn_id.add continuousOn_const)
      (fun w hw => hmapsU w hw.1)
  · intro w hw
    rcases lt_or_eq_of_le (show (0 : ℝ) ≤ w.im from hw.2) with him | him
    · have hwH : w + (B : ℂ) ∈ H := by show 0 < (w + (B : ℂ)).im; simpa using him
      show 0 ≤ (Ψt (w + (B : ℂ)) - (x : ℂ)).im
      rw [← heqH hwH]
      have : 0 < (Ψ left a (w + (B : ℂ))).im := hψH hwH
      simp only [sub_im, ofReal_im, sub_zero]; exact this.le
    · have hw' : w = ((w.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [← him]
      have hre : |w.re| ≤ ρ := by
        have := hw.1; rw [mem_closedBall, dist_zero_right] at this
        exact (Complex.abs_re_le_norm w).trans this
      have ht : w.re + B ∈ Icc (B - δ) (B + δ) := by
        rw [abs_le] at hre; constructor <;> linarith
      have e : w + (B : ℂ) = ((w.re + B : ℝ) : ℂ) := by
        rw [hw']; push_cast; simp
      show 0 ≤ (Ψt (w + (B : ℂ)) - (x : ℂ)).im
      rw [e, hΦeq _ ht]
      simp
  · intro w hw
    have hwH : w + (B : ℂ) ∈ H := by
      show 0 < (w + (B : ℂ)).im; simpa using (show 0 < w.im from hw.2)
    simp only [g3mapP, g3mapB, g3locM, div_one, ofReal_one, one_mul, hpre]
    rw [heqH hwH]
  · show Ψt (0 + (B : ℂ)) - (x : ℂ) = 0
    rw [zero_add, show (B : ℂ) = ((B : ℝ) : ℂ) from rfl, hΦeq B ⟨by linarith, by linarith⟩, hΦB,
      sub_self]

end G3Zp
end Thm18Asm
end QuantumZipper
