/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.Uniqueness
import InteractingSLE.Spec.Sec2.GirsanovSLE

/-!
# Lemma 5.10: the pathwise core

Packet PROVE-SEC5-B (specification §5.2, proof of Lemma 5.10, `source/spec/p097-144.md` L929–L959, and the
corrected crossing lemma, `source/spec/p433-480.md` §2.2).

A deterministic statement about one path of the evolution after the change of measure. Under `ℚ`, the
Brownian motion is `β = B + ∫₀^· φ`, where the Girsanov integrand `φ` (`crossIntegrand`) removes

* the bounded drift `U` of the force points other than the first right one (`|U| ≤ C` before
  `τ ∧ 1`, so the clamp at `C/√κ` is inactive there), and
* after a fixed time `s`, the one-force drift `ρ/(W − V)` while the gap `V − W` is at least `g/2`.

Then on `[0, s]` the pair `(W, V)` is a one-force evolution driven by `β`: its gap `G = V − W` satisfies
`G/√κ = x/√κ − β + ((2+ρ)/κ) ∫ √κ/G`, which dominates the zero-start Bessel path `Y` of the smaller coefficient
`c_* ≤ (2+ρ)/κ` (`Bessel.le_of_sub_eq_integral`). Hence `|W_u| ≤ √κ|β_u| + |ρ| ∫₀ᵘ 1/G ≤ √κ a₁ + ρ_max b₁/(c_*√κ)`
when `sup_{[0,s]} |β| ≤ a₁` and `c_* ∫₀ˢ 1/Y = Y_s + β_s ≤ b₁`, and `G_s ≥ √κ Y_s ≥ √κ g_Y`. After `s`,
`W − W_s = √κ(β − β_s)` as long as the gap stays above `g/2`, which it does when `√κ |β − β_s| ≤ g/4`
(the force point is nondecreasing). So `|W| ≤ 3/8` up to time `1` and, by a first-exit argument, the evolution
lives through time `1` (`crossing_path`).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

/-! ### Clamps, the domain `t ≤ τ ∧ 1`, and the integrand -/

/-- The clamp of `y` to `[−K, K]`. -/
def clampAbs (K y : ℝ) : ℝ := max (-K) (min K y)

theorem clampAbs_of_abs_le {K y : ℝ} (h : |y| ≤ K) : clampAbs K y = y := by
  rw [clampAbs, min_eq_right (abs_le.1 h).2, max_eq_right (abs_le.1 h).1]

theorem abs_clampAbs_le {K : ℝ} (hK : 0 ≤ K) (y : ℝ) : |clampAbs K y| ≤ K := by
  rw [clampAbs, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem continuous_clampAbs (K : ℝ) : Continuous (clampAbs K) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- `t ≤ τ ∧ 1` for `τ = inf {t : |W_t| ≥ 1}`. -/
def InDom (w : ℝ≥0 → ℝ) (t : ℝ≥0) : Prop := t ≤ 1 ∧ ∀ u < t, |w u| < 1

theorem InDom.mono {w : ℝ≥0 → ℝ} {t u : ℝ≥0} (h : InDom w t) (hut : u ≤ t) : InDom w u :=
  ⟨hut.trans h.1, fun r hr => h.2 r (hr.trans_le hut)⟩

/-- The Girsanov integrand of the proof of Lemma 5.10: the clamped other drift `U/√κ`, plus, from time `s`
on, the one-force drift `ρ/(√κ(W − V))` cut at gap `g/2`. -/
def crossIntegrand (κ C ρ g : ℝ) (s t : ℝ≥0) (w v o : ℝ) : ℝ :=
  clampAbs (C / Real.sqrt κ) (o / Real.sqrt κ) +
    if s ≤ t then ρ / Real.sqrt κ * Girsanov.recipCut (g / 2) (w - v) else 0

theorem abs_crossIntegrand_le {κ C ρ g : ℝ} (hC : 0 ≤ C) (hg : 0 < g) (s t : ℝ≥0) (w v o : ℝ) :
    |crossIntegrand κ C ρ g s t w v o| ≤ C / Real.sqrt κ + |ρ / Real.sqrt κ| * (g / 2)⁻¹ := by
  rw [crossIntegrand]
  refine (abs_add_le _ _).trans (add_le_add (abs_clampAbs_le (div_nonneg hC (Real.sqrt_nonneg _)) _) ?_)
  split_ifs
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Girsanov.abs_recipCut_le (half_pos hg) _) (abs_nonneg _)
  · simp only [abs_zero]
    positivity

/-! ### The pathwise argument -/

section Path

variable {κ C ρ ρmax cl x a₁ b₁ gY a₂ : ℝ} {s : ℝ≥0} {w v o b bq y : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The one-force part of `crossIntegrand`, scaled by `√κ`. -/
def oneForceCut (ρ g : ℝ) (s : ℝ≥0) (w v : ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  if s ≤ r.toNNReal then ρ * Girsanov.recipCut (g / 2) (w r.toNNReal - v r.toNNReal) else 0

theorem toNNReal_le_of_mem_uIoc {t : ℝ≥0} {r : ℝ} (hr : r ∈ Set.uIoc 0 (t : ℝ)) : r.toNNReal ≤ t := by
  rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hr
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1.le]
  exact hr.2

theorem continuousOn_comp_toNNReal {f : ℝ≥0 → ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < ζ}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : ContinuousOn (fun r : ℝ => f r.toNNReal) (Set.uIcc 0 (t : ℝ)) := by
  refine hf.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
  rw [Set.uIcc_of_le (NNReal.coe_nonneg t)] at hr
  refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) ht
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
  exact hr.2

theorem intervalIntegrable_oneForceCut (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ}) {g : ℝ} (hg : 0 < g) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : IntervalIntegrable (oneForceCut ρ g s w v) volume 0 t := by
  have hh : ContinuousOn (fun r : ℝ => ρ * Girsanov.recipCut (g / 2) (w r.toNNReal - v r.toNNReal))
      (Set.uIcc 0 (t : ℝ)) :=
    continuousOn_const.mul ((Girsanov.continuous_recipCut (half_pos hg)).comp_continuousOn
      ((continuousOn_comp_toNNReal hwc ht).sub (continuousOn_comp_toNNReal hvc ht)))
  have hS : MeasurableSet {r : ℝ | s ≤ r.toNNReal} := measurable_real_toNNReal measurableSet_Ici
  have he : oneForceCut ρ g s w v = Set.indicator {r : ℝ | s ≤ r.toNNReal}
      (fun r : ℝ => ρ * Girsanov.recipCut (g / 2) (w r.toNNReal - v r.toNNReal)) := by
    funext r
    simp only [oneForceCut, Set.indicator, Set.mem_ofPred_eq]
  rw [he]
  have hi : IntervalIntegrable (fun r : ℝ => ρ * Girsanov.recipCut (g / 2)
      (w r.toNNReal - v r.toNNReal)) volume 0 t := hh.intervalIntegrable
  exact ⟨hi.1.indicator hS, hi.2.indicator hS⟩

/-- **The equation after the change of measure** (before `τ ∧ 1`):
`W_t = √κ β_t + ∫₀ᵗ ρ/(W − V) − ∫₀ᵗ 1{s ≤ r} ρ r_{g/2}(W − V)`. -/
theorem w_eq_of_inDom (hκ : 0 < κ) (hg : 0 < gY)
    (hlife : ∀ t, InDom w t → (t : ℝ≥0∞) < ζ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hinto : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => o r.toNNReal) volume 0 t)
    (hweq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = Real.sqrt κ * b t
      + (∫ r in (0 : ℝ)..t, ρ / (w r.toNNReal - v r.toNNReal)) + ∫ r in (0 : ℝ)..t, o r.toNNReal)
    (ho : ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → InDom w r.toNNReal → |o r.toNNReal| ≤ C)
    (hgir : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min 1 ζ → bq t = b t + ∫ r in (0 : ℝ)..t,
      crossIntegrand κ C ρ (Real.sqrt κ * gY) s r.toNNReal (w r.toNNReal) (v r.toNNReal)
        (o r.toNNReal))
    {t : ℝ≥0} (ht : InDom w t) :
    w t = Real.sqrt κ * bq t + (∫ r in (0 : ℝ)..t, ρ / (w r.toNNReal - v r.toNNReal))
      - ∫ r in (0 : ℝ)..t, oneForceCut ρ (Real.sqrt κ * gY) s w v r := by
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have htζ := hlife t ht
  have htm : (t : ℝ≥0∞) ≤ min 1 ζ := le_min (by exact_mod_cast ht.1) htζ.le
  have hclamp : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.uIoc 0 (t : ℝ) →
      clampAbs (C / Real.sqrt κ) (o r.toNNReal / Real.sqrt κ) = o r.toNNReal / Real.sqrt κ := by
    filter_upwards [ho] with r hr hrI
    have hr0 : 0 ≤ r := by
      rw [Set.uIoc_of_le (NNReal.coe_nonneg t)] at hrI; exact hrI.1.le
    refine clampAbs_of_abs_le ?_
    rw [abs_div, abs_of_pos hsk]
    exact div_le_div_of_nonneg_right (hr hr0 (ht.mono (toNNReal_le_of_mem_uIoc hrI))) hsk.le
  have hI1 : IntervalIntegrable (fun r : ℝ => clampAbs (C / Real.sqrt κ)
      (o r.toNNReal / Real.sqrt κ)) volume 0 t :=
    ((hinto t htζ).div_const _).congr_ae ((ae_restrict_iff' measurableSet_uIoc).2 (by
      filter_upwards [hclamp] with r hr hrI using (hr hrI).symm))
  have hI2 := intervalIntegrable_oneForceCut (ρ := ρ) (s := s) hwc hvc (mul_pos hsk hg) htζ
  have hsplit : (fun r : ℝ => crossIntegrand κ C ρ (Real.sqrt κ * gY) s r.toNNReal (w r.toNNReal)
      (v r.toNNReal) (o r.toNNReal)) = fun r => clampAbs (C / Real.sqrt κ)
        (o r.toNNReal / Real.sqrt κ) + (Real.sqrt κ)⁻¹ * oneForceCut ρ (Real.sqrt κ * gY) s w v r := by
    funext r
    simp only [crossIntegrand, oneForceCut]
    split_ifs
    · ring
    · ring
  have hg1 := hgir t htm
  rw [hsplit, intervalIntegral.integral_add hI1 (hI2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_congr_ae (by
      filter_upwards [hclamp] with r hr hrI using hr hrI), intervalIntegral.integral_div] at hg1
  have hw := hweq t htζ
  have : Real.sqrt κ * bq t = Real.sqrt κ * b t + (∫ r in (0 : ℝ)..t, o r.toNNReal)
      + ∫ r in (0 : ℝ)..t, oneForceCut ρ (Real.sqrt κ * gY) s w v r := by
    rw [hg1]
    field_simp
    ring
  linarith

theorem integral_oneForceCut_eq_zero {g : ℝ} {r : ℝ≥0} (hrs : r ≤ s) :
    ∫ q in (0 : ℝ)..r, oneForceCut ρ g s w v q = 0 := by
  refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans (by simp)
  filter_upwards [Girsanov.ae_ne_real (s : ℝ)] with q hqs hq
  have hqr := toNNReal_le_of_mem_uIoc hq
  rw [Set.uIoc_of_le (NNReal.coe_nonneg r)] at hq
  have hlt : q.toNNReal < s := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq.1.le]
    exact lt_of_le_of_ne (hq.2.trans (by exact_mod_cast hrs)) hqs
  simp [oneForceCut, not_le.2 hlt]

/-- `w ≤ v` gives `(v − w)⁻¹ ≥ 0`; the reciprocal gap is integrable. -/
theorem intervalIntegrable_inv_gap
    (hint : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 t)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun r : ℝ => (v r.toNNReal - w r.toNNReal)⁻¹) volume 0 t := by
  refine ((hint t ht).neg).congr fun r _ => ?_
  simp only [Pi.neg_apply, ← inv_neg, neg_sub]

/-- **Phase one** (`t ≤ s`): the gap dominates the Bessel path and `|W| ≤ 1/4`. -/
theorem phase_one (hκ : 0 < κ) (hg : 0 < gY) (hρ : |ρ| ≤ ρmax) (hcl : 0 < cl)
    (hclc : cl ≤ (2 + ρ) / κ) (hx : 0 ≤ x) (hw0 : w 0 = 0)
    (hlife : ∀ t, InDom w t → (t : ℝ≥0∞) < ζ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hwv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t ≤ v t)
    (hint : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 t)
    (hinto : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => o r.toNNReal) volume 0 t)
    (hweq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = Real.sqrt κ * b t
      + (∫ r in (0 : ℝ)..t, ρ / (w r.toNNReal - v r.toNNReal)) + ∫ r in (0 : ℝ)..t, o r.toNNReal)
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      v t = x + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal))
    (hcoll : volume {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < ζ ∧ w r.toNNReal = v r.toNNReal} = 0)
    (ho : ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → InDom w r.toNNReal → |o r.toNNReal| ≤ C)
    (hgir : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min 1 ζ → bq t = b t + ∫ r in (0 : ℝ)..t,
      crossIntegrand κ C ρ (Real.sqrt κ * gY) s r.toNNReal (w r.toNNReal) (v r.toNNReal)
        (o r.toNNReal))
    (hy : Bessel.IsBesselPath cl 0 (fun t => -bq t) y)
    (hE1 : ∀ t ≤ s, |bq t| ≤ a₁) (hE2 : y s + bq s ≤ b₁)
    (ha₁ : Real.sqrt κ * a₁ + ρmax * b₁ / (cl * Real.sqrt κ) ≤ 1 / 4)
    {u : ℝ≥0} (hu : InDom w u) (hus : u ≤ s) :
    Real.sqrt κ * y u ≤ v u - w u ∧ |w u| ≤ 1 / 4 := by
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have huζ := hlife u hu
  -- the one-force equation on `[0, u]`
  have hW : ∀ r : ℝ≥0, r ≤ u → w r = Real.sqrt κ * bq r
      + ∫ q in (0 : ℝ)..r, ρ / (w q.toNNReal - v q.toNNReal) := fun r hr => by
    have := w_eq_of_inDom hκ hg hlife hwc hvc hinto hweq ho hgir (hu.mono hr)
    rw [integral_oneForceCut_eq_zero (hr.trans hus), sub_zero] at this
    exact this
  have hζr : ∀ r : ℝ≥0, r ≤ u → (r : ℝ≥0∞) < ζ := fun r hr => hlife r (hu.mono hr)
  -- `β_0 = 0`, so `Y_0 = 0`
  have h0dom : InDom w 0 := hu.mono bot_le
  have hb0 : b 0 = 0 := by
    have := hweq 0 (hlife 0 h0dom)
    simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero, hw0] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hsk.ne'
    · exact h
  have hbq0 : bq 0 = 0 := by
    have := hgir 0 (by simp)
    simpa [hb0] using this
  have hy0 : y 0 = 0 := by
    have := hy.2.2.2.2 0
    simpa [hbq0] using this
  have hv0 : v 0 = x := by
    have := hveq 0 (hlife 0 h0dom)
    simpa using this
  -- comparison on `[0, u]`
  set c : ℝ := (2 + ρ) / κ with hc
  set X : ℝ → ℝ := fun r => (v r.toNNReal - w r.toNNReal) / Real.sqrt κ with hX
  set Y : ℝ → ℝ := fun r => y r.toNNReal with hY
  have hcont : ∀ f : ℝ≥0 → ℝ, ContinuousOn f {t | (t : ℝ≥0∞) < ζ} →
      ContinuousOn (fun r : ℝ => f r.toNNReal) (Set.Icc 0 (u : ℝ)) := fun f hf => by
    have := continuousOn_comp_toNNReal hf huζ
    rwa [Set.uIcc_of_le (NNReal.coe_nonneg u)] at this
  have hXc : ContinuousOn X (Set.Icc 0 (u : ℝ)) := ((hcont v hvc).sub (hcont w hwc)).div_const _
  have hYc : ContinuousOn Y (Set.Icc 0 (u : ℝ)) := hy.continuous_real.continuousOn
  have hgapI : IntervalIntegrable (fun r : ℝ => (v r.toNNReal - w r.toNNReal)⁻¹) volume 0 u :=
    intervalIntegrable_inv_gap hint huζ
  have hcX : ∀ r, c / X r = c * Real.sqrt κ * (v r.toNNReal - w r.toNNReal)⁻¹ := fun r => by
    rw [hX]
    simp only
    rw [div_div_eq_mul_div]
    ring
  have hXint : IntervalIntegrable (fun r => c / X r) volume 0 u := by
    simp only [hcX]
    exact hgapI.const_mul _
  have hYint : IntervalIntegrable (fun r => cl / Y r) volume 0 u := hy.intervalIntegrable_div u
  -- the pointwise identity `2/(v−w) − ρ/(w−v) = √κ · c/X`
  have hpt : ∀ r, 2 / (v r.toNNReal - w r.toNNReal) - ρ / (w r.toNNReal - v r.toNNReal)
      = Real.sqrt κ * (c / X r) := fun r => by
    rw [hcX]
    have hκs : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ.le
    rw [hc, ← neg_sub (v r.toNNReal) (w r.toNNReal), div_neg]
    by_cases hd : v r.toNNReal - w r.toNNReal = 0
    · simp [hd]
    · field_simp
      rw [Real.sq_sqrt hκ.le]
      ring
  have hXeq : ∀ r ∈ Set.Icc (0 : ℝ) u, X r = x / Real.sqrt κ - bq r.toNNReal
      + ∫ q in (0 : ℝ)..r, c / X q := fun r hr => by
    have hr' : r.toNNReal ≤ u := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]; exact hr.2
    have hrr : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.1
    have hv := hveq r.toNNReal (hζr _ hr')
    have hw := hW r.toNNReal hr'
    rw [hrr] at hv hw
    have hgapr : IntervalIntegrable (fun q : ℝ => (v q.toNNReal - w q.toNNReal)⁻¹) volume 0 r :=
      hgapI.mono_set (by
        rw [Set.uIcc_of_le hr.1, Set.uIcc_of_le (NNReal.coe_nonneg u)]
        exact Set.Icc_subset_Icc_right hr.2)
    have hi1 : IntervalIntegrable (fun q : ℝ => 2 / (v q.toNNReal - w q.toNNReal)) volume 0 r := by
      simpa [div_eq_mul_inv] using hgapr.const_mul 2
    have hi2 : IntervalIntegrable (fun q : ℝ => ρ / (w q.toNNReal - v q.toNNReal)) volume 0 r := by
      have := (hgapr.const_mul (-ρ))
      refine this.congr fun q _ => ?_
      simp only [div_eq_mul_inv, ← neg_sub (v q.toNNReal) (w q.toNNReal), inv_neg]
      ring
    have hsub := intervalIntegral.integral_sub hi1 hi2
    simp only [hpt, intervalIntegral.integral_const_mul] at hsub
    rw [show X r = (v r.toNNReal - w r.toNNReal) / Real.sqrt κ from rfl, hv, hw,
      div_eq_iff hsk.ne']
    have e : (x / Real.sqrt κ - bq r.toNNReal + ∫ q in (0 : ℝ)..r, c / X q) * Real.sqrt κ
        = x - Real.sqrt κ * bq r.toNNReal + Real.sqrt κ * ∫ q in (0 : ℝ)..r, c / X q := by
      field_simp
    rw [e]
    linarith
  have hYeq : ∀ r ∈ Set.Icc (0 : ℝ) u, Y r = -bq r.toNNReal + ∫ q in (0 : ℝ)..r, cl / Y q :=
    fun r hr => by
      have := hy.2.2.2.2 r.toNNReal
      rw [Real.coe_toNNReal _ hr.1] at this
      simpa [hY] using this
  have hXpos : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.Icc (0 : ℝ) u → 0 < X r := by
    have h := measure_eq_zero_iff_ae_notMem.1 hcoll
    filter_upwards [h] with r hr hrI
    have hr' : r.toNNReal ≤ u := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hrI.1]; exact hrI.2
    have hle := hwv _ (hζr _ hr')
    have hne : w r.toNNReal ≠ v r.toNNReal := fun h => hr ⟨hrI.1, hζr _ hr', h⟩
    exact div_pos (sub_pos.2 (lt_of_le_of_ne hle hne)) hsk
  have hsubI : ∀ r ∈ Set.Icc (0 : ℝ) u, Set.uIcc 0 r ⊆ Set.uIcc 0 (u : ℝ) := fun r hr => by
    rw [Set.uIcc_of_le hr.1, Set.uIcc_of_le (NNReal.coe_nonneg u)]
    exact Set.Icc_subset_Icc_right hr.2
  have hcmp := Bessel.le_of_sub_eq_integral (X := Y) (Y := X) (f := fun r => cl / Y r)
    (h := fun r => c / X r) hYc hXc hYint hXint (by
      simp only [hY, hX, Real.toNNReal_zero, hy0, hv0, hw0, sub_zero]
      exact div_nonneg hx hsk.le) (fun r hr => by
      rw [hYeq r hr, hXeq r hr, hYeq 0 ⟨le_rfl, NNReal.coe_nonneg u⟩,
        hXeq 0 ⟨le_rfl, NNReal.coe_nonneg u⟩, intervalIntegral.integral_sub
          (hYint.mono_set (hsubI r hr)) (hXint.mono_set (hsubI r hr))]
      simp only [Real.toNNReal_zero, hbq0, intervalIntegral.integral_same]
      ring) (by
      filter_upwards [hXpos] with r hr hrI hlt
      have hX0 := hr hrI
      calc cl / Y r ≤ cl / X r := div_le_div_of_nonneg_left hcl.le hX0 hlt.le
        _ ≤ c / X r := div_le_div_of_nonneg_right hclc hX0.le)
  have hYX : ∀ r ∈ Set.Icc (0 : ℝ) u, Y r ≤ X r := hcmp
  refine ⟨?_, ?_⟩
  · have := hYX u ⟨NNReal.coe_nonneg u, le_rfl⟩
    simp only [hY, hX, Real.toNNReal_coe] at this
    rw [le_div_iff₀ hsk] at this
    linarith
  · -- `∫₀ᵘ 1/(v − w) ≤ (1/√κ) ∫₀ˢ 1/Y ≤ b₁/(c_* √κ)`
    have hYpos := hy.ae_pos
    have hint1 : ∫ q in (0 : ℝ)..u, (v q.toNNReal - w q.toNNReal)⁻¹
        ≤ ∫ q in (0 : ℝ)..u, (Real.sqrt κ)⁻¹ * (Y q)⁻¹ := by
      refine intervalIntegral.integral_mono_ae_restrict (NNReal.coe_nonneg u) hgapI
        ((hy.2.2.2.1 u).const_mul _) ((ae_restrict_iff' measurableSet_Icc).2 ?_)
      filter_upwards [hXpos, hYpos] with q hq hq' hqI'
      have hX0 := hq hqI'
      have hY0 := hq' hqI'.1
      have hle := hYX q hqI'
      have : (v q.toNNReal - w q.toNNReal)⁻¹ = (Real.sqrt κ)⁻¹ * (X q)⁻¹ := by
        simp only [hX]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hX0 hY0).2 hle) (inv_nonneg.2 hsk.le)
    have hint2 : ∫ q in (0 : ℝ)..u, (Y q)⁻¹ ≤ ∫ q in (0 : ℝ)..s, (Y q)⁻¹ :=
      intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg u) (by exact_mod_cast hus)
        (ae_of_all _ fun q => inv_nonneg.2 (hy.2.1 _)) (hy.2.2.2.1 s)
    have hint3 : cl * ∫ q in (0 : ℝ)..s, (Y q)⁻¹ = y s + bq s := by
      have := hy.2.2.2.2 s
      rw [← intervalIntegral.integral_const_mul]
      simp only [hY, ← div_eq_mul_inv] at this ⊢
      linarith
    have hIs : ∫ q in (0 : ℝ)..s, (Y q)⁻¹ ≤ b₁ / cl := by
      rw [le_div_iff₀ hcl, mul_comm, hint3]; exact hE2
    have hgap0 : 0 ≤ ∫ q in (0 : ℝ)..u, (v q.toNNReal - w q.toNNReal)⁻¹ :=
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg u) fun q hq => by
        have hq' : q.toNNReal ≤ u := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq.1]; exact hq.2
        exact inv_nonneg.2 (sub_nonneg.2 (hwv _ (hζr _ hq')))
    have hrho : ∫ q in (0 : ℝ)..u, ρ / (w q.toNNReal - v q.toNNReal)
        = -ρ * ∫ q in (0 : ℝ)..u, (v q.toNNReal - w q.toNNReal)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun q _ => ?_
      simp only [div_eq_mul_inv, ← neg_sub (v q.toNNReal) (w q.toNNReal), inv_neg]
      ring
    have hwu := hW u le_rfl
    rw [hrho] at hwu
    have hbqu := hE1 u hus
    have hI : ∫ q in (0 : ℝ)..u, (v q.toNNReal - w q.toNNReal)⁻¹ ≤ b₁ / (cl * Real.sqrt κ) := by
      calc _ ≤ ∫ q in (0 : ℝ)..u, (Real.sqrt κ)⁻¹ * (Y q)⁻¹ := hint1
        _ = (Real.sqrt κ)⁻¹ * ∫ q in (0 : ℝ)..u, (Y q)⁻¹ := intervalIntegral.integral_const_mul _ _
        _ ≤ (Real.sqrt κ)⁻¹ * (b₁ / cl) :=
            mul_le_mul_of_nonneg_left (hint2.trans hIs) (inv_nonneg.2 hsk.le)
        _ = b₁ / (cl * Real.sqrt κ) := by field_simp
    have hρ0 : 0 ≤ ρmax := (abs_nonneg ρ).trans hρ
    calc |w u| = |Real.sqrt κ * bq u + -ρ * (∫ q in (0 : ℝ)..u, (v q.toNNReal - w q.toNNReal)⁻¹)| := by
          rw [hwu]
      _ ≤ Real.sqrt κ * |bq u| + |ρ| * (∫ q in (0 : ℝ)..u, (v q.toNNReal - w q.toNNReal)⁻¹) := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_of_pos hsk, abs_neg, abs_of_nonneg hgap0]
      _ ≤ Real.sqrt κ * a₁ + ρmax * (b₁ / (cl * Real.sqrt κ)) := by
          gcongr
      _ ≤ 1 / 4 := by rw [← mul_div_assoc]; exact ha₁

/-- **Phase two** (`s ≤ t`): while the gap stays above `g/2` the driver moves like `√κ β`; the gap does
stay above `g/2` when `√κ |β − β_s| ≤ g/4`, so `|W_t − W_s| ≤ 1/8`. -/
theorem phase_two (hκ : 0 < κ) (hg : 0 < gY)
    (hlife : ∀ t, InDom w t → (t : ℝ≥0∞) < ζ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hwv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t ≤ v t)
    (hint : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 t)
    (hinto : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => o r.toNNReal) volume 0 t)
    (hweq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = Real.sqrt κ * b t
      + (∫ r in (0 : ℝ)..t, ρ / (w r.toNNReal - v r.toNNReal)) + ∫ r in (0 : ℝ)..t, o r.toNNReal)
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      v t = x + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal))
    (ho : ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → InDom w r.toNNReal → |o r.toNNReal| ≤ C)
    (hgir : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min 1 ζ → bq t = b t + ∫ r in (0 : ℝ)..t,
      crossIntegrand κ C ρ (Real.sqrt κ * gY) s r.toNNReal (w r.toNNReal) (v r.toNNReal)
        (o r.toNNReal))
    (hF : ∀ u ≤ 1 - s, |bq (s + u) - bq s| ≤ a₂)
    (ha₂ : Real.sqrt κ * a₂ ≤ min (1 / 8) (Real.sqrt κ * gY / 4))
    (hGs : Real.sqrt κ * gY ≤ v s - w s) {t : ℝ≥0} (ht : InDom w t) (hst : s ≤ t) :
    |w t - w s| ≤ 1 / 8 := by
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  set g : ℝ := Real.sqrt κ * gY with hgdef
  have hg0 : 0 < g := mul_pos hsk hg
  -- the driver moves like `√κ β` while the gap stays above `g/2`
  have key : ∀ u : ℝ≥0, InDom w u → s ≤ u →
      (∀ r : ℝ≥0, s ≤ r → r < u → g / 2 ≤ v r - w r) → |w u - w s| ≤ min (1 / 8) (g / 4) := by
    intro u hu hsu hgap
    have huζ := hlife u hu
    have hsζ := hlife s (hu.mono hsu)
    have h1 := w_eq_of_inDom hκ hg hlife hwc hvc hinto hweq ho hgir hu
    have h2 := w_eq_of_inDom hκ hg hlife hwc hvc hinto hweq ho hgir (hu.mono hsu)
    have hf : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → IntervalIntegrable
        (fun r : ℝ => ρ / (w r.toNNReal - v r.toNNReal)) volume 0 t := fun t ht =>
      ((hint t ht).const_mul ρ).congr fun r _ => by simp only [div_eq_mul_inv]
    have hO : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
        IntervalIntegrable (oneForceCut ρ g s w v) volume 0 t := fun t ht =>
      intervalIntegrable_oneForceCut hwc hvc hg0 ht
    have e1 := intervalIntegral.integral_interval_sub_left (hf u huζ) (hf s hsζ)
    have e2 := intervalIntegral.integral_interval_sub_left (hO u huζ) (hO s hsζ)
    have hfi : IntervalIntegrable (fun r : ℝ => ρ / (w r.toNNReal - v r.toNNReal)) volume s u :=
      (hf s hsζ).symm.trans (hf u huζ)
    have hOi : IntervalIntegrable (oneForceCut ρ g s w v) volume s u :=
      (hO s hsζ).symm.trans (hO u huζ)
    have hzero : ∫ r in (s : ℝ)..u, (ρ / (w r.toNNReal - v r.toNNReal) - oneForceCut ρ g s w v r)
        = 0 := by
      refine (intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_).trans (by simp)
      filter_upwards [Girsanov.ae_ne_real (u : ℝ)] with r hru hr
      rw [Set.uIoc_of_le (by exact_mod_cast hsu)] at hr
      have hr0 : 0 ≤ r := (NNReal.coe_nonneg s).trans hr.1.le
      have hsr : s ≤ r.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hr.1.le
      have hru' : r.toNNReal < u := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact lt_of_le_of_ne hr.2 hru
      have hG := hgap _ hsr hru'
      have habs : g / 2 ≤ |w r.toNNReal - v r.toNNReal| := by
        rw [abs_sub_comm]; exact hG.trans (le_abs_self _)
      have hO' : oneForceCut ρ g s w v r = ρ * (w r.toNNReal - v r.toNNReal)⁻¹ := by
        simp only [oneForceCut, hsr, ↓reduceIte, Girsanov.recipCut_of_le (half_pos hg0) habs]
      rw [hO', div_eq_mul_inv, sub_self]
    rw [intervalIntegral.integral_sub hfi hOi] at hzero
    have hdiff : w u - w s = Real.sqrt κ * (bq u - bq s) := by
      have : (∫ r in (0 : ℝ)..u, ρ / (w r.toNNReal - v r.toNNReal))
          - (∫ r in (0 : ℝ)..s, ρ / (w r.toNNReal - v r.toNNReal))
          - ((∫ r in (0 : ℝ)..u, oneForceCut ρ g s w v r)
            - ∫ r in (0 : ℝ)..s, oneForceCut ρ g s w v r) = 0 := by
        rw [e1, e2]; linarith
      rw [h1, h2]
      linarith
    have hus1 : u - s ≤ 1 - s := tsub_le_tsub_right hu.1 s
    have hbq := hF (u - s) hus1
    rw [add_tsub_cancel_of_le hsu] at hbq
    rw [hdiff, abs_mul, abs_of_pos hsk]
    exact (mul_le_mul_of_nonneg_left hbq hsk.le).trans ha₂
  -- the gap stays above `g/2` on `[s, t]` (first exit)
  have hvmono : ∀ r₁ r₂ : ℝ≥0, r₁ ≤ r₂ → (r₂ : ℝ≥0∞) < ζ → v r₁ ≤ v r₂ := by
    intro r₁ r₂ h12 h2
    have h1ζ : (r₁ : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 h12) h2
    have hI : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → IntervalIntegrable
        (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 t := fun t ht => by
      simpa [div_eq_mul_inv] using (intervalIntegrable_inv_gap hint ht).const_mul 2
    have e := intervalIntegral.integral_interval_sub_left (hI r₂ h2) (hI r₁ h1ζ)
    rw [hveq r₂ h2, hveq r₁ h1ζ]
    have : 0 ≤ ∫ r in (r₁ : ℝ)..r₂, 2 / (v r.toNNReal - w r.toNNReal) :=
      intervalIntegral.integral_nonneg (by exact_mod_cast h12) fun r hr => by
        have hr0 : 0 ≤ r := (NNReal.coe_nonneg r₁).trans hr.1
        have hr' : r.toNNReal ≤ r₂ := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]; exact hr.2
        exact div_nonneg zero_le_two (sub_nonneg.2 (hwv _
          (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr') h2)))
    linarith
  have htζ := hlife t ht
  have hGc : ContinuousOn (fun r => v r - w r) (Set.Icc s t) :=
    (hvc.sub hwc).mono fun r hr => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr.2) htζ
  have hgap : ∀ r : ℝ≥0, s ≤ r → r ≤ t → g / 2 < v r - w r := by
    by_contra hcon
    push Not at hcon
    set S : Set ℝ≥0 := Set.Icc s t ∩ {r | v r - w r ≤ g / 2} with hS
    have hSne : S.Nonempty := by
      obtain ⟨r, h1, h2, h3⟩ := hcon
      exact ⟨r, ⟨h1, h2⟩, h3⟩
    have hSc : IsClosed S := hGc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSb : BddBelow S := ⟨s, fun r hr => hr.1.1⟩
    set u₀ := sInf S
    have hu₀ : u₀ ∈ S := hSc.csInf_mem hSne hSb
    have hsu₀ : s ≤ u₀ := hu₀.1.1
    have hu₀dom : InDom w u₀ := ht.mono hu₀.1.2
    have hbelow : ∀ r : ℝ≥0, s ≤ r → r < u₀ → g / 2 ≤ v r - w r := fun r hsr hru => by
      by_contra hlt
      push Not at hlt
      have hrS : r ∈ S := ⟨⟨hsr, (hru.le.trans hu₀.1.2)⟩, hlt.le⟩
      exact absurd (csInf_le hSb hrS) (not_le.2 hru)
    have hk := key u₀ hu₀dom hsu₀ hbelow
    have hvle := hvmono s u₀ hsu₀ (hlife u₀ hu₀dom)
    have h3 := hu₀.2
    simp only [Set.mem_ofPred_eq] at h3
    have := (abs_le.1 (hk.trans (min_le_right _ _))).2
    linarith
  exact (key t ht hst fun r hsr hrt => (hgap r hsr hrt.le).le).trans (min_le_left _ _)

/-- **The pathwise core of Lemma 5.10.** On the event where the changed-measure Brownian motion `β` satisfies
`sup_{[0,s]} |β| ≤ a₁`, `Y_s + β_s ≤ b₁`, `Y_s ≥ g_Y` (for the zero-start Bessel path `Y` of coefficient
`c_* ≤ (2 + ρ)/κ` driven by `−β`) and `√κ |β_{s+u} − β_s| ≤ √κ a₂` for `u ≤ 1 − s`, the evolution lives through
time `1` and `|W_t| ≤ 3/8` for every `t ≤ 1`; in particular `τ ≥ 1`. -/
theorem crossing_path (hκ : 0 < κ) (hg : 0 < gY) (hρ : |ρ| ≤ ρmax) (hcl : 0 < cl)
    (hclc : cl ≤ (2 + ρ) / κ) (hx : 0 ≤ x) (hw0 : w 0 = 0)
    (hlife : ∀ t, InDom w t → (t : ℝ≥0∞) < ζ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hwv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t ≤ v t)
    (hint : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 t)
    (hinto : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => o r.toNNReal) volume 0 t)
    (hweq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → w t = Real.sqrt κ * b t
      + (∫ r in (0 : ℝ)..t, ρ / (w r.toNNReal - v r.toNNReal)) + ∫ r in (0 : ℝ)..t, o r.toNNReal)
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      v t = x + ∫ r in (0 : ℝ)..t, 2 / (v r.toNNReal - w r.toNNReal))
    (hcoll : volume {r : ℝ | 0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < ζ ∧ w r.toNNReal = v r.toNNReal} = 0)
    (ho : ∀ᵐ r ∂(volume : Measure ℝ), 0 ≤ r → InDom w r.toNNReal → |o r.toNNReal| ≤ C)
    (hgir : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min 1 ζ → bq t = b t + ∫ r in (0 : ℝ)..t,
      crossIntegrand κ C ρ (Real.sqrt κ * gY) s r.toNNReal (w r.toNNReal) (v r.toNNReal)
        (o r.toNNReal))
    (hy : Bessel.IsBesselPath cl 0 (fun t => -bq t) y)
    (hE1 : ∀ t ≤ s, |bq t| ≤ a₁) (hE2 : y s + bq s ≤ b₁) (hE3 : gY ≤ y s)
    (hF : ∀ u ≤ 1 - s, |bq (s + u) - bq s| ≤ a₂)
    (ha₁ : Real.sqrt κ * a₁ + ρmax * b₁ / (cl * Real.sqrt κ) ≤ 1 / 4)
    (ha₂ : Real.sqrt κ * a₂ ≤ min (1 / 8) (Real.sqrt κ * gY / 4)) :
    ∀ t : ℝ≥0, t ≤ 1 → (t : ℝ≥0∞) < ζ ∧ |w t| ≤ 3 / 8 := by
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hbound : ∀ t, InDom w t → |w t| ≤ 3 / 8 := by
    intro t ht
    by_cases hts : t ≤ s
    · have := (phase_one hκ hg hρ hcl hclc hx hw0 hlife hwc hvc hwv hint hinto hweq hveq hcoll ho
        hgir hy hE1 hE2 ha₁ ht hts).2
      linarith
    · have hst : s ≤ t := (not_le.1 hts).le
      have p1 := phase_one hκ hg hρ hcl hclc hx hw0 hlife hwc hvc hwv hint hinto hweq hveq hcoll ho
        hgir hy hE1 hE2 ha₁ (ht.mono hst) le_rfl
      have hGs : Real.sqrt κ * gY ≤ v s - w s :=
        (mul_le_mul_of_nonneg_left hE3 hsk.le).trans p1.1
      have p2 := phase_two hκ hg hlife hwc hvc hwv hint hinto hweq hveq ho hgir hF ha₂ hGs ht hst
      calc |w t| = |(w t - w s) + w s| := by ring_nf
        _ ≤ |w t - w s| + |w s| := abs_add_le _ _
        _ ≤ 1 / 8 + 1 / 4 := add_le_add p2 p1.2
        _ ≤ 3 / 8 := by norm_num
  have hall : ∀ t : ℝ≥0, t ≤ 1 → InDom w t := by
    intro t ht1
    refine ⟨ht1, ?_⟩
    by_contra hcon
    push Not at hcon
    set S : Set ℝ≥0 := {u | u < t ∧ 1 ≤ |w u|} with hS
    have hSne : S.Nonempty := by
      obtain ⟨u, h1, h2⟩ := hcon
      exact ⟨u, h1, h2⟩
    set u₀ := sInf S
    obtain ⟨u₁, hu₁⟩ := hSne
    have hu₀t : u₀ ≤ t := (csInf_le (OrderBot.bddBelow S) hu₁).trans hu₁.1.le
    have hu₀dom : InDom w u₀ := by
      refine ⟨hu₀t.trans ht1, fun r hr => ?_⟩
      by_contra hr1
      push Not at hr1
      exact absurd (csInf_le (OrderBot.bddBelow S) ⟨hr.trans_le hu₀t, hr1⟩) (not_le.2 hr)
    have hu₀ζ := hlife u₀ hu₀dom
    have hcu : ContinuousAt w u₀ :=
      hwc.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hu₀ζ)
    obtain ⟨δ, hδ, hδw⟩ := Metric.continuousAt_iff.1 hcu (1 / 2) (by norm_num)
    have hlt : u₀ < u₀ + (δ / 2).toNNReal := lt_add_of_pos_right _ (Real.toNNReal_pos.2 (half_pos hδ))
    obtain ⟨r, hrS, hr⟩ := exists_lt_of_csInf_lt ⟨u₁, hu₁⟩ hlt
    have hu₀r : u₀ ≤ r := csInf_le (OrderBot.bddBelow S) hrS
    have hd : dist r u₀ < δ := by
      rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hu₀r))]
      have : (r : ℝ) < u₀ + δ / 2 := by
        have := (NNReal.coe_lt_coe.2 hr)
        rwa [NNReal.coe_add, Real.coe_toNNReal _ (half_pos hδ).le] at this
      linarith
    have h1 := hδw hd
    rw [Real.dist_eq] at h1
    have h2 := hbound u₀ hu₀dom
    have h3 := hrS.2
    have : |w r| < 1 := by
      calc |w r| = |(w r - w u₀) + w u₀| := by ring_nf
        _ ≤ |w r - w u₀| + |w u₀| := abs_add_le _ _
        _ < 1 / 2 + 3 / 8 := by linarith
        _ ≤ 1 := by norm_num
    linarith
  exact fun t ht => ⟨hlife t (hall t ht), hbound t (hall t ht)⟩

end Path

end Sec5

end InteractingSLE
