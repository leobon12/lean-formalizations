import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcNormA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-EXCLOWER, normalized case: `ℰ(η, [0, ∞)) ≥ c (diam η ∧ 1)`

`flExcNorm_holds : FLExcNormStmt`. For a crosscut `η` of `ℍ` from `−1` to `a ≤ −1` of any
diameter `d`, with `m = d ∧ 1`, the argument of the repository's proof of the lower half of the
key estimate of Lawler–Werness (Ann. Probab. 41 (2013), proof of Lemma 4.3, p. 24;
`lw43KeyLower_holds`, LWExc3Key.lean) runs verbatim with `r ∈ {m/5, m/40}`: `lw3_circle` and
`lw3_outer` give `h(z) ≥ c₀ r Im z/|z + 1|²` for `z ∈ H_η` with `|z + 1| > r`; the points
`x + iy`, `x ≥ 0`, `0 < y` small, lie in `H_η` by the strip lemma `flSub_strip_mem`; hence
`∂_y h(x) ≥ (c₀/160) m/(x + 1)²` (`flSub_yDer_ge`) and `∫_0^∞ ∂_y h ≥ (c₀/160) m`.
This is the normalized form of Field–Lawler, EJP 20 (2015), Cor. 5.2 as used in the proof of
Prop. 3.1 (p. 7). Own elementary argument (extension of the repository's LW 4.3 proof).
-/

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- **Normalized lower bound**: `ℰ(η, [0, ∞)) ≥ (c₀/160) (diam η ∧ 1)` for a crosscut from `−1`
to `a ≤ −1`. -/
theorem flExcNorm_holds : FLExcNormStmt := by
  have hc0 := lw3c0_pos
  refine ⟨lw3c0 / 160, by positivity, ?_⟩
  intro η a h hη h0 h1 ha hm
  set d := Metric.diam (arcH η) with hddef
  have hdpos : 0 < d := lwExc_diam_pos hη
  set m := min d 1 with hmdef
  have hmpos : 0 < m := lt_min hdpos one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hmd : m ≤ d := min_le_left _ _
  obtain ⟨r, hr, hr1, hr2, hra⟩ : ∃ r : ℝ, 0 < r ∧ m / 40 ≤ r ∧ r ≤ m / 5 ∧
      (‖(a : ℂ) + 1‖ < r / 2 ∨ 2 * r < ‖(a : ℂ) + 1‖) := by
    by_cases hA : ‖(a : ℂ) + 1‖ < m / 10
    · exact ⟨m / 5, by positivity, by linarith, le_rfl, Or.inl (by linarith)⟩
    · push Not at hA
      exact ⟨m / 40, by positivity, le_rfl, by linarith, Or.inr (by linarith)⟩
  have hfar : ∃ p ∈ arcH η, 2 * r < ‖p + 1‖ := by
    by_contra hno
    push Not at hno
    have hsub : arcH η ⊆ closedBall (-1 : ℂ) (2 * r) := fun p hp => by
      rw [mem_closedBall, dist_eq_norm, sub_neg_eq_add]; exact hno p hp
    have := Metric.diam_le_of_subset_closedBall (by positivity) hsub
    linarith
  have hcirc : ∀ q ∈ hullComp η, ‖q + 1‖ = r → lw3c0 * (q.im / r) ≤ h q :=
    fun q hq hqr => lw3_circle hη h0 h1 hm hr hfar hra hq hqr
  have hout := lw3_outer hη hm hr hcirc
  obtain ⟨ε, hε, hstr⟩ := flSub_strip hη h0 h1 ha
  set ρ := min ε (1 / 4) with hρdef
  have hρ : 0 < ρ := lt_min hε (by norm_num)
  have hρε : ρ ≤ ε := min_le_left _ _
  have hρ4 : ρ ≤ 1 / 4 := min_le_right _ _
  have hpt : ∀ x ∈ Ici (0 : ℝ), lw3c0 / 160 * m / (x + 1) ^ 2 ≤ yDer h x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hball : ∀ w ∈ ball (x : ℂ) ρ, x - ρ < w.re ∧ |w.im| < ρ := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw
      have h2 : (w - (x : ℂ)).re = w.re - x := by simp
      have h3 := (Complex.abs_im_le_norm (w - x)).trans_lt hw
      have h4 : (w - (x : ℂ)).im = w.im := by simp
      rw [h4] at h3
      have h5 := (abs_lt.1 ((Complex.abs_re_le_norm (w - x)).trans_lt hw)).1
      rw [h2] at h5
      exact ⟨by linarith, h3⟩
    refine flSub_yDer_ge hm hρ ?_ ?_ ?_
    · rintro w ⟨hwH, hwB⟩
      obtain ⟨hre, him⟩ := hball w hwB
      have hwim : 0 < w.im := hwH
      exact flSub_strip_mem hε hstr (by linarith) hwim
        (lt_of_lt_of_le (lt_of_le_of_lt (le_abs_self _) him) hρε)
    · intro w hwB hw0 hwc
      obtain ⟨hre, -⟩ := hball w hwB
      have := hstr w hwc (by linarith)
      linarith
    · intro y hy hyρ
      set z : ℂ := (x : ℂ) + (y : ℂ) * I with hz
      have hzre : z.re = x := by simp [hz]
      have hzim : z.im = y := by simp [hz]
      have hzU : z ∈ hullComp η :=
        flSub_strip_mem hε hstr (by rw [hzre]; linarith) (by rw [hzim]; exact hy)
          (by rw [hzim]; linarith)
      have hz1 : x + 1 ≤ ‖z + 1‖ := by
        have := Complex.re_le_norm (z + 1)
        have e : (z + 1).re = x + 1 := by simp [hz]
        linarith
      have hz2 : ‖z + 1‖ ≤ 2 * (x + 1) := by
        have : ‖z + 1‖ ≤ ‖((x + 1 : ℝ) : ℂ)‖ + ‖(y : ℂ) * I‖ := by
          have e : z + 1 = ((x + 1 : ℝ) : ℂ) + (y : ℂ) * I := by
            simp [hz]; ring
          rw [e]; exact norm_add_le _ _
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul,
          Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy] at this
        linarith
      have hrz : r < ‖z + 1‖ := by linarith
      have hk := hout z hzU hrz
      rw [hzim] at hk
      have hx1 : 0 < x + 1 := by linarith
      have hnpos : 0 < ‖z + 1‖ := by linarith
      have hq : ‖z + 1‖ ^ 2 ≤ 4 * (x + 1) ^ 2 := by nlinarith
      calc y * (lw3c0 / 160 * m / (x + 1) ^ 2)
          = lw3c0 * (m / 40) * y / (4 * (x + 1) ^ 2) := by field_simp; ring
        _ ≤ lw3c0 * r * y / (4 * (x + 1) ^ 2) := by gcongr
        _ ≤ lw3c0 * r * y / ‖z + 1‖ ^ 2 := by gcongr
        _ ≤ h z := hk
  calc ENNReal.ofReal (lw3c0 / 160 * m)
      = ∫⁻ x in Ici (0 : ℝ), ENNReal.ofReal (lw3c0 / 160 * m / (x + 1) ^ 2) :=
        (lwExc_lintegral_inv_sq (by positivity)).symm
    _ ≤ excR h (Ici 0) :=
        setLIntegral_mono' measurableSet_Ici fun x hx => ENNReal.ofReal_le_ofReal (hpt x hx)

end FieldLawler
end QuantumZipper
