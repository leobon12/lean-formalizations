import QuantumZipper.Proofs.Zipper.B5LocF1Assembly
import QuantumZipper.Proofs.Zipper.F1Side3

/-!
# B5 locality for F1, input (R2): the side images are small at small times

`sideSmallStmt` proves `SideSmallStmt` of `B5LocF1Assembly.lean`: if `W` is continuous,
`W 0 = 0`, `|W| ≤ M` on `[0,t]` and every real `x ≠ 0` is alive at time `t`, then
`|O^±_t| ≤ 3M + 3√t`.

For a real starting point `x < 0` the centered forward solution `φ` is real and negative, and
`v = φ + W` (the uncentered `g_s(x)`) is decreasing with `v' = 2/φ`. As long as `v ≥ -(2M + √t)`
the bound is immediate; after the first time `v` reaches `-(2M + √t)`, `φ ≤ -√t`, so `v` loses at
most `(2/√t)·t = 2√t`. Hence `φ_t ≥ -(3M + 3√t)`; letting `x → 0⁻` gives `O⁻_t ∈ [-(3M+3√t), 0]`
(the limit exists by `F1.exists_tendsto_sideImages_of_alive`). The side `x > 0` follows by the
symmetry `W ↦ -W`, `φ ↦ -φ` (`RS.isForwardSol_neg`).

This is the real-line case of the standard estimate `|g_t(z) - z| ≤ C(‖W‖_{∞,[0,t]} + √t)`
(Lawler, *Conformally Invariant Processes in the Plane*, Lemma 4.12, p. 80 is the analogous bound
for the reverse flow); the one-line barrier argument above is our own elementary proof.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace B5

/-- A forward solution from a real point, as a real integral equation. -/
theorem real_eq_of_isForwardSol {W : ℝ → ℝ} {t y : ℝ} {f : ℝ → ℂ}
    (hf : IsForwardSol W (y : ℂ) t f) :
    ContinuousOn (fun q => (f q).re) (Icc 0 t) ∧ (∀ q ∈ Icc 0 t, (f q).re ≠ 0) ∧
      ∀ q ∈ Icc 0 t, (f q).re = y - W q + ∫ p in (0 : ℝ)..q, 2 / (f p).re := by
  set φ : ℝ → ℝ := fun q => (f q).re with hφ
  have him : ∀ q ∈ Icc 0 t, f q = (φ q : ℂ) := fun q hq => by
    apply Complex.ext
    · simp [φ]
    · simp [φ, F1.im_eq_zero_of_isForwardSol_ofReal hf hq]
  have hφne : ∀ q ∈ Icc 0 t, φ q ≠ 0 := fun q hq h =>
    (hf.2 q hq).1 (by rw [him q hq, h, Complex.ofReal_zero])
  refine ⟨Complex.continuous_re.comp_continuousOn hf.1, hφne, fun q hq => ?_⟩
  have h := (hf.2 q hq).2
  have hI : ∫ p in (0 : ℝ)..q, 2 / f p = ((∫ p in (0 : ℝ)..q, 2 / φ p : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun p hp => ?_
    rw [uIcc_of_le hq.1] at hp
    simp only [him p ⟨hp.1, hp.2.trans hq.2⟩, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [hI] at h
  have h2 := congrArg Complex.re h
  simpa [φ] using h2

/-- **Barrier bound, left side.** A forward solution from a real `y ∈ [-(2M+√t), 0)` stays
negative and ends above `-(3M + 3√t)`. -/
theorem neg_le_re_of_isForwardSol_neg {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t y M : ℝ} (ht : 0 < t) (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) (hy : y < 0)
    (hyL : -(2 * M + Real.sqrt t) ≤ y) {f : ℝ → ℂ} (hf : IsForwardSol W (y : ℂ) t f) :
    -(3 * M + 3 * Real.sqrt t) ≤ (f t).re ∧ (f t).re < 0 := by
  obtain ⟨hφc, hφne, heq⟩ := real_eq_of_isForwardSol hf
  set φ : ℝ → ℝ := fun q => (f q).re with hφdef
  have ht0 : (t : ℝ) ∈ Icc 0 t := ⟨ht.le, le_rfl⟩
  have h00 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht.le⟩
  have hφ0 : φ 0 = y := by
    have := heq 0 h00
    rw [hW0, intervalIntegral.integral_same] at this
    linarith
  have hneg : ∀ q ∈ Icc 0 t, φ q < 0 := by
    intro q hq
    by_contra hcon
    push Not at hcon
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hq.1 (hφc.mono (Icc_subset_Icc_right hq.2))
      (show (0 : ℝ) ∈ Icc (φ 0) (φ q) from ⟨by rw [hφ0]; exact hy.le, hcon⟩)
    exact hφne c ⟨hc.1, hc.2.trans hq.2⟩ hc0
  have hc2 : ContinuousOn (fun q => 2 / φ q) (Icc 0 t) := continuousOn_const.div hφc hφne
  have hint : ∀ p q, p ∈ Icc 0 t → q ∈ Icc 0 t →
      IntervalIntegrable (fun q => 2 / φ q) volume p q := fun p q hp hq =>
    (hc2.mono (uIcc_subset_Icc hp hq)).intervalIntegrable
  set v : ℝ → ℝ := fun q => φ q + W q with hvdef
  have hv : ∀ q ∈ Icc 0 t, v q = y + ∫ p in (0 : ℝ)..q, 2 / φ p := by
    intro q hq
    have h := heq q hq
    change (f q).re + W q = y + ∫ p in (0 : ℝ)..q, 2 / (f p).re
    rw [h]
    ring
  have hdiff : ∀ p q, p ∈ Icc 0 t → q ∈ Icc 0 t → v q - v p = ∫ r in p..q, 2 / φ r := by
    intro p q hp hq
    rw [hv q hq, hv p hp]
    have := intervalIntegral.integral_interval_sub_left (hint 0 q h00 hq) (hint 0 p h00 hp)
    linarith
  have hanti : ∀ p q, p ∈ Icc 0 t → q ∈ Icc 0 t → p ≤ q → v q ≤ v p := by
    intro p q hp hq hpq
    have h1 := intervalIntegral.integral_mono_on hpq (hint p q hp hq)
      (intervalIntegrable_const (c := (0 : ℝ)))
      (fun x hx => (div_neg_of_pos_of_neg two_pos
        (hneg x ⟨hp.1.trans hx.1, hx.2.trans hq.2⟩)).le)
    rw [intervalIntegral.integral_const, smul_zero] at h1
    linarith [hdiff p q hp hq]
  refine ⟨?_, hneg t ht0⟩
  have hWt := abs_le.1 (hM t ht0)
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 h00)
  have hvt : φ t = v t - W t := by simp [hvdef]
  by_cases hcase : -(2 * M + Real.sqrt t) ≤ v t
  · show -(3 * M + 3 * Real.sqrt t) ≤ φ t
    linarith
  push Not at hcase
  have hvc : ContinuousOn v (Icc 0 t) := hφc.add hW.continuousOn
  have hv0 : v 0 = y := by simp [hvdef, hφ0, hW0]
  obtain ⟨τ, hτ, hvτ⟩ := intermediate_value_Icc' ht.le hvc
    (show -(2 * M + Real.sqrt t) ∈ Icc (v t) (v 0) from ⟨hcase.le, by rw [hv0]; exact hyL⟩)
  have hφle : ∀ r ∈ Icc τ t, -(2 / Real.sqrt t) ≤ 2 / φ r := by
    intro r hr
    have hr' : r ∈ Icc 0 t := ⟨hτ.1.trans hr.1, hr.2⟩
    have h1 := hanti τ r hτ hr' hr.1
    have h2 := abs_le.1 (hM r hr')
    have h3 : φ r ≤ -Real.sqrt t := by
      have : φ r = v r - W r := by simp [hvdef]
      linarith
    have h4 : 2 / (-φ r) ≤ 2 / Real.sqrt t :=
      div_le_div_of_nonneg_left (by norm_num) hsq (by linarith)
    have h5 : 2 / φ r = -(2 / (-φ r)) := by rw [div_neg, neg_neg]
    rw [h5]
    linarith
  have hI := intervalIntegral.integral_mono_on hτ.2 (intervalIntegrable_const (c := -(2 / Real.sqrt t)))
    (hint τ t hτ ht0) hφle
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI
  have e : 2 / Real.sqrt t * t = 2 * Real.sqrt t := by
    rw [div_mul_eq_mul_div, div_eq_iff hsq.ne', mul_assoc, Real.mul_self_sqrt ht.le]
  have hpos : 0 < 2 / Real.sqrt t := by positivity
  have key : -(2 * Real.sqrt t) ≤ (t - τ) * -(2 / Real.sqrt t) := by
    nlinarith [mul_nonneg hpos.le hτ.1]
  have hd := hdiff τ t hτ ht0
  show -(3 * M + 3 * Real.sqrt t) ≤ φ t
  linarith

/-- **Barrier bound, right side** (by `W ↦ -W`). -/
theorem re_le_of_isForwardSol_pos {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t y M : ℝ} (ht : 0 < t) (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) (hy : 0 < y)
    (hyL : y ≤ 2 * M + Real.sqrt t) {f : ℝ → ℂ} (hf : IsForwardSol W (y : ℂ) t f) :
    (f t).re ≤ 3 * M + 3 * Real.sqrt t ∧ 0 < (f t).re := by
  have hf' := RS.isForwardSol_neg hf
  have e : -(y : ℂ) = ((-y : ℝ) : ℂ) := by push_cast; ring
  rw [e] at hf'
  have h := neg_le_re_of_isForwardSol_neg (W := fun r => -W r) hW.neg (by simp [hW0]) ht
    (fun r hr => by rw [abs_neg]; exact hM r hr) (by linarith) (by linarith) hf'
  simp only [Complex.neg_re] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **(R2) proved**: `SideSmallStmt`, with `M = a/12`, `t₀ = (a/12)²`. -/
theorem sideSmallStmt : SideSmallStmt := by
  intro a ha
  refine ⟨a / 12, by positivity, (a / 12) ^ 2, by positivity, ?_⟩
  intro W hW hW0 t ht halive hM
  have hsq0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hsq : Real.sqrt t ≤ a / 12 :=
    (Real.sqrt_le_sqrt ht.2).trans (Real.sqrt_sq (by positivity)).le
  obtain ⟨o₁, o₂, h₁, h₂⟩ := F1.exists_tendsto_sideImages_of_alive ht.1.le halive
  have e₁ : (sideImages W t).1 = o₁ := h₁.limUnder_eq
  have e₂ : (sideImages W t).2 = o₂ := h₂.limUnder_eq
  have hb₁ : ∀ᶠ x : ℝ in 𝓝[<] (0 : ℝ), -(3 * (a / 12) + 3 * Real.sqrt t) ≤ (fwdMap W t (x : ℂ)).re ∧
      (fwdMap W t (x : ℂ)).re ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT (show -Real.sqrt t < 0 by linarith)] with x hx
    obtain ⟨f, hf⟩ := halive x hx.2.ne
    rw [F1.fwdMap_eq_of_isForwardSol hf ⟨ht.1.le, le_rfl⟩]
    have := neg_le_re_of_isForwardSol_neg hW hW0 ht.1 hM hx.2
      (by linarith [hx.1, ha]) hf
    exact ⟨this.1, this.2.le⟩
  have hb₂ : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ (fwdMap W t (x : ℂ)).re ∧
      (fwdMap W t (x : ℂ)).re ≤ 3 * (a / 12) + 3 * Real.sqrt t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.sqrt t by linarith)] with x hx
    obtain ⟨f, hf⟩ := halive x hx.1.ne'
    rw [F1.fwdMap_eq_of_isForwardSol hf ⟨ht.1.le, le_rfl⟩]
    have := re_le_of_isForwardSol_pos hW hW0 ht.1 hM hx.1
      (by linarith [hx.2, ha]) hf
    exact ⟨this.2.le, this.1⟩
  have l₁ := ge_of_tendsto h₁ (hb₁.mono fun x hx => hx.1)
  have u₁ := le_of_tendsto h₁ (hb₁.mono fun x hx => hx.2)
  have l₂ := ge_of_tendsto h₂ (hb₂.mono fun x hx => hx.1)
  have u₂ := le_of_tendsto h₂ (hb₂.mono fun x hx => hx.2)
  rw [e₁, e₂]
  refine ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩

end B5
end QuantumZipper
