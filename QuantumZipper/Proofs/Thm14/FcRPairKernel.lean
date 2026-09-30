import QuantumZipper.Proofs.Loewner.TwoPointEnergy
import QuantumZipper.Statements.CouplingFields

/-!
# FCR-PAIR, part 4: a pointwise bound for the pushed-forward Neumann kernel

For `W` continuous, `T ≥ 0`, `f = revMap W T` and `z, w ∈ ℍ` in a bounded set,

  `|neumannH (f z) (f w)| ≤ C + 2 |log ‖z − w‖| + |log Im z| + |log Im w|`

(`abs_neumannH_revMap_le`). This is the domination used for the energy convergence of the
semicircle approximations. Own elementary proof from the two-point lower bound
`TwoPoint.twoPoint_lower` (`‖f z − f w‖ ≥ ‖z − w‖ √(Im z Im w / (Im f z Im f w))`), the bound
`‖f‖ ≤ B` on bounded sets, and `‖x − ȳ‖ ≥ ‖x − y‖` for `x, y ∈ ℍ`.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm14WDG

/-- `‖x − y‖ ≤ ‖x − ȳ‖` for `x, y` in the closed upper half-plane. -/
theorem norm_sub_le_norm_sub_conj {x y : ℂ} (hx : 0 ≤ x.im) (hy : 0 ≤ y.im) :
    ‖x - y‖ ≤ ‖x - conj y‖ := by
  have h : ‖x - y‖ ^ 2 ≤ ‖x - conj y‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [sub_re, sub_im, conj_re, conj_im]
    nlinarith [mul_nonneg hx hy]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- **Pointwise domination of the pushed-forward Neumann kernel.** -/
theorem abs_neumannH_revMap_le {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    ∃ C : ℝ, ∀ z w : ℂ, z ∈ H → w ∈ H → ‖z‖ ≤ R → ‖w‖ ≤ R → z ≠ w →
      |neumannH (revMap W T z) (revMap W T w)| ≤
        C + 2 * |Real.log ‖z - w‖| + |Real.log z.im| + |Real.log w.im| := by
  obtain ⟨B₀, -, hB₀⟩ := TwoPoint.exists_norm_revMap_le hW hT R
  set B := max B₀ 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  refine ⟨2 * |Real.log B| + 2 * |Real.log (2 * B)|, fun z w hz hw hzR hwR hzw => ?_⟩
  set x := revMap W T z
  set y := revMap W T w
  have hxi : 0 < x.im := TwoPoint.im_revMap_pos hW hz hT
  have hyi : 0 < y.im := TwoPoint.im_revMap_pos hW hw hT
  have hxB : ‖x‖ ≤ B := (hB₀ z hzR).trans (le_max_left _ _)
  have hyB : ‖y‖ ≤ B := (hB₀ w hwR).trans (le_max_left _ _)
  have hxiB : x.im ≤ B := (Complex.im_le_norm x).trans hxB
  have hyiB : y.im ≤ B := (Complex.im_le_norm y).trans hyB
  have hxy : x ≠ y := fun h => hzw (injOn_revMap W hW hT hz hw h)
  set a := ‖x - y‖ with ha_def
  set b := ‖x - conj y‖ with hb_def
  have ha : 0 < a := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hab : a ≤ b := norm_sub_le_norm_sub_conj hxi.le hyi.le
  have hb : 0 < b := ha.trans_le hab
  have hb2 : b ≤ 2 * B := by
    calc b ≤ ‖x‖ + ‖conj y‖ := norm_sub_le _ _
      _ ≤ 2 * B := by rw [Complex.norm_conj]; linarith
  have ha2 : a ≤ 2 * B := hab.trans hb2
  have hzwpos : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw)
  have hzi : 0 < z.im := hz
  have hwi : 0 < w.im := hw
  -- the two-point lower bound, in logarithmic form
  set q := z.im * w.im / (x.im * y.im) with hq
  have hq0 : 0 < q := by positivity
  have hlow : ‖z - w‖ * Real.sqrt q ≤ a := TwoPoint.twoPoint_lower hW hz hw hT
  have hlog1 : Real.log ‖z - w‖ + Real.log q / 2 ≤ Real.log a := by
    have := Real.log_le_log (by positivity) hlow
    rwa [Real.log_mul hzwpos.ne' (Real.sqrt_pos.2 hq0).ne', Real.log_sqrt hq0.le] at this
  have hlogq : Real.log z.im + Real.log w.im - 2 * Real.log B ≤ Real.log q := by
    rw [hq, Real.log_div (by positivity) (by positivity), Real.log_mul hzi.ne' hwi.ne',
      Real.log_mul hxi.ne' hyi.ne']
    have h1 := Real.log_le_log hxi hxiB
    have h2 := Real.log_le_log hyi hyiB
    linarith
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log ha hab
  have hlb2 : Real.log b ≤ Real.log (2 * B) := Real.log_le_log hb hb2
  have hla2 : Real.log a ≤ Real.log (2 * B) := Real.log_le_log ha ha2
  have hN : neumannH x y = -Real.log a - Real.log b := rfl
  rw [hN, abs_le]
  constructor
  · -- lower bound: `neumannH ≥ −2 log (2B)`
    have := le_abs_self (Real.log (2 * B))
    nlinarith [abs_nonneg (Real.log B), abs_nonneg (Real.log ‖z - w‖),
      abs_nonneg (Real.log z.im), abs_nonneg (Real.log w.im)]
  · -- upper bound: `neumannH ≤ −2 log a`
    have e1 := neg_abs_le (Real.log ‖z - w‖)
    have e2 := neg_abs_le (Real.log z.im)
    have e3 := neg_abs_le (Real.log w.im)
    have e4 := le_abs_self (Real.log B)
    nlinarith [abs_nonneg (Real.log (2 * B))]

/-- **Pointwise bound for `𝔥_T`.** On bounded subsets of `ℍ`,
`|𝔥_T(z)| ≤ C + C' |log Im z|` (from `Im f z ≥ Im z`, `‖f‖ ≤ B` and
`TwoPoint.abs_log_norm_deriv_revMap_le`). -/
theorem abs_hTrev_le (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    ∃ C C' : ℝ, ∀ z : ℂ, z ∈ H → ‖z‖ ≤ R → |hTrev κ W T z| ≤ C + C' * |Real.log z.im| := by
  obtain ⟨B₀, -, hB₀⟩ := TwoPoint.exists_norm_revMap_le hW hT R
  set B := max B₀ 1 with hBdef
  have hB1 : 1 ≤ B := le_max_right _ _
  refine ⟨|2 / Real.sqrt κ| * |Real.log B| +
      |Qc (Real.sqrt κ)| * |Real.log (Real.sqrt (R ^ 2 + 4 * T))|,
    |2 / Real.sqrt κ| + |Qc (Real.sqrt κ)|, fun z hz hzR => ?_⟩
  have hzi : 0 < z.im := hz
  have hxi : z.im ≤ (revMap W T z).im := im_le_im_revMap W hW z hz hT
  have hxB : ‖revMap W T z‖ ≤ B := (hB₀ z hzR).trans (le_max_left _ _)
  have hxn : z.im ≤ ‖revMap W T z‖ := hxi.trans (Complex.im_le_norm _)
  have hl1 : |Real.log ‖revMap W T z‖| ≤ |Real.log B| + |Real.log z.im| := by
    have h1 := Real.log_le_log hzi hxn
    have h2 := Real.log_le_log (hzi.trans_le hxn) hxB
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log z.im), abs_nonneg (Real.log B)]
    · linarith [le_abs_self (Real.log B), abs_nonneg (Real.log z.im)]
  have hl2 := TwoPoint.abs_log_norm_deriv_revMap_le hW hT hz
    (show z.im ≤ R from (Complex.im_le_norm z).trans hzR)
  show |2 / Real.sqrt κ * Real.log ‖revMap W T z‖ +
    Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W T) z‖| ≤ _
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have e1 := mul_le_mul_of_nonneg_left hl1 (abs_nonneg (2 / Real.sqrt κ))
  have e2 := mul_le_mul_of_nonneg_left hl2 (abs_nonneg (Qc (Real.sqrt κ)))
  nlinarith

end Thm14WDG
end QuantumZipper
