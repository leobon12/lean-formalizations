/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux104Calc
import InteractingSLE.Spec.Sec7.ContinuityProbGaps
import InteractingSLE.Spec.Sec7.ContinuityProb4Band
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Aux. lemma 104: the pathwise part

Packet PROVE-STRIPSYS3. One realization of the hypotheses of Aux. lemma 104 (`source/spec/p337-384.md` L308–L313):
the integrated system (IN1) with one left and one right mark at the seed `0`, an extra drift `e` bounded by `C`,
nonnegative gaps with null zero sets and integrable reciprocals, all before the lifetime `T`
(`IsSeedEntrance`). The coordinates `Λ = (L − √κ b, D)` (`L = w − v^L`, `D = v^R − v^L`) are the integrals of
the density `dens` (`coord_eq`); (IN2) `D_t² ≥ 16 t` (`sixteen_mul_le_sq`); and up to a time `σ ≤ T` before which
`D ≤ d` the density is integrable (also when `σ = T`: the reciprocal-gap integrals are bounded by `D ≤ d`,
`intervalIntegrable_dens`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux104

/-- **The hypotheses of Aux. lemma 104 along one path** before the lifetime `T`: (IN1) with `V^L_0 = V^R_0 = 0`,
`W_0 = √κ b_0`, an extra drift `e` with `|e| ≤ C`, ordered marks, integrable reciprocal gaps and null collision
sets. -/
structure IsSeedEntrance (κ ρL ρR C : ℝ) (w vL vR b e : ℝ≥0 → ℝ) (T : ℝ≥0∞) : Prop where
  vL_le_w : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vL t ≤ w t
  w_le_vR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t ≤ vR t
  integrable_gapL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL s.toNNReal)⁻¹) volume 0 t
  integrable_gapR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
    IntervalIntegrable (fun s : ℝ => (vR s.toNNReal - w s.toNNReal)⁻¹) volume 0 t
  integrable_e : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → IntervalIntegrable (fun s : ℝ => e s.toNNReal) volume 0 t
  abs_e_le : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → |e t| ≤ C
  w_eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t = Real.sqrt κ * b t +
    ∫ s in (0 : ℝ)..t, (ρL / (w s.toNNReal - vL s.toNNReal) + ρR / (w s.toNNReal - vR s.toNNReal) + e s.toNNReal)
  vL_eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vL t = ∫ s in (0 : ℝ)..t, 2 / (vL s.toNNReal - w s.toNNReal)
  vR_eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vR t = ∫ s in (0 : ℝ)..t, 2 / (vR s.toNNReal - w s.toNNReal)
  volume_collisionL : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = vL s.toNNReal} = 0
  volume_collisionR : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = vR s.toNNReal} = 0

/-- The density of the coordinates `(L − √κ b, D)` before `T` (`0` afterwards):
`(a/L − ρ_R/R + e, 2/L + 2/R)` with `a = ρ_L + 2`. -/
def dens (ρL ρR : ℝ) (w vL vR e : ℝ≥0 → ℝ) (T : ℝ≥0∞) (s : ℝ) : ℝ × ℝ :=
  if (s.toNNReal : ℝ≥0∞) < T then
    ((ρL + 2) / (w s.toNNReal - vL s.toNNReal) - ρR / (vR s.toNNReal - w s.toNNReal) + e s.toNNReal,
      2 / (w s.toNNReal - vL s.toNNReal) + 2 / (vR s.toNNReal - w s.toNNReal))
  else 0

/-- The coordinates: the integral of the density. -/
def coord (ρL ρR : ℝ) (w vL vR e : ℝ≥0 → ℝ) (T : ℝ≥0∞) (t : ℝ≥0) : ℝ × ℝ :=
  ∫ s in (0 : ℝ)..t, dens ρL ρR w vL vR e T s

variable {κ ρL ρR C : ℝ} {w vL vR b e : ℝ≥0 → ℝ} {T : ℝ≥0∞}

theorem toNNReal_lt_of_mem_Icc {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    (s.toNNReal : ℝ≥0∞) < T :=
  lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht

theorem eqOn_dens {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    EqOn (dens ρL ρR w vL vR e T) (fun s =>
      ((ρL + 2) / (w s.toNNReal - vL s.toNNReal) - ρR / (vR s.toNNReal - w s.toNNReal) + e s.toNNReal,
        2 / (w s.toNNReal - vL s.toNNReal) + 2 / (vR s.toNNReal - w s.toNNReal))) (uIcc 0 t) := by
  intro s hs
  rw [uIcc_of_le t.coe_nonneg] at hs
  simp only [dens, toNNReal_lt_of_mem_Icc ht hs, ↓reduceIte]

/-- The first density component is integrable before `T`. -/
theorem IsSeedEntrance.intervalIntegrable_fst (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : IntervalIntegrable (fun s : ℝ =>
      (ρL + 2) / (w s.toNNReal - vL s.toNNReal) - ρR / (vR s.toNNReal - w s.toNNReal) + e s.toNNReal) volume 0 t := by
  simp only [div_eq_mul_inv]
  exact (((h.integrable_gapL t ht).const_mul _).sub ((h.integrable_gapR t ht).const_mul _)).add (h.integrable_e t ht)

/-- The second density component is integrable before `T`. -/
theorem IsSeedEntrance.intervalIntegrable_snd (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : IntervalIntegrable (fun s : ℝ =>
      2 / (w s.toNNReal - vL s.toNNReal) + 2 / (vR s.toNNReal - w s.toNNReal)) volume 0 t := by
  simp only [div_eq_mul_inv]
  exact ((h.integrable_gapL t ht).const_mul _).add ((h.integrable_gapR t ht).const_mul _)

/-- An interval integral of a pair is the pair of interval integrals. -/
theorem intervalIntegral_pair {f g : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hf : IntervalIntegrable f volume 0 t)
    (hg : IntervalIntegrable g volume 0 t) :
    ∫ s in (0 : ℝ)..t, (f s, g s) = (∫ s in (0 : ℝ)..t, f s, ∫ s in (0 : ℝ)..t, g s) := by
  rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le ht]
  exact integral_pair ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hf)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1 hg)

/-- The density is integrable before `T`. -/
theorem IsSeedEntrance.intervalIntegrable_dens_of_lt (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : IntervalIntegrable (dens ρL ρR w vL vR e T) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
  refine IntegrableOn.congr_fun (((intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).1
    (h.intervalIntegrable_fst ht)).prodMk ((intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).1
      (h.intervalIntegrable_snd ht))) ?_ measurableSet_Ioc
  refine ((eqOn_dens ht).symm.mono ?_)
  rw [uIcc_of_le t.coe_nonneg]; exact Ioc_subset_Icc_self

/-- **The coordinates before `T`**: `∫₀ᵗ dens = (w_t − √κ b_t − v^L_t, v^R_t − v^L_t)`. -/
theorem IsSeedEntrance.coord_eq (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    coord ρL ρR w vL vR e T t = (w t - Real.sqrt κ * b t - vL t, vR t - vL t) := by
  unfold coord
  rw [intervalIntegral.integral_congr (eqOn_dens ht),
    intervalIntegral_pair t.coe_nonneg (h.intervalIntegrable_fst ht) (h.intervalIntegrable_snd ht)]
  have hL := h.integrable_gapL t ht
  have hR := h.integrable_gapR t ht
  have hE := h.integrable_e t ht
  have hgw : IntervalIntegrable (fun s : ℝ => ρL / (w s.toNNReal - vL s.toNNReal) +
      ρR / (w s.toNNReal - vR s.toNNReal) + e s.toNNReal) volume 0 t := by
    have e1 : (fun s : ℝ => ρL / (w s.toNNReal - vL s.toNNReal) + ρR / (w s.toNNReal - vR s.toNNReal) +
        e s.toNNReal) = fun s => ρL * (w s.toNNReal - vL s.toNNReal)⁻¹ +
          (-ρR) * (vR s.toNNReal - w s.toNNReal)⁻¹ + e s.toNNReal := by
      funext s; rw [← neg_sub (vR s.toNNReal), div_neg]; ring
    rw [e1]; exact ((hL.const_mul _).add (hR.const_mul _)).add hE
  have hgL : IntervalIntegrable (fun s : ℝ => 2 / (vL s.toNNReal - w s.toNNReal)) volume 0 t := by
    have e1 : (fun s : ℝ => 2 / (vL s.toNNReal - w s.toNNReal)) =
        fun s => (-2) * (w s.toNNReal - vL s.toNNReal)⁻¹ := by
      funext s; rw [← neg_sub (w s.toNNReal), div_neg]; ring
    rw [e1]; exact hL.const_mul _
  have hgR : IntervalIntegrable (fun s : ℝ => 2 / (vR s.toNNReal - w s.toNNReal)) volume 0 t := by
    simp only [div_eq_mul_inv]; exact hR.const_mul _
  congr 1
  · rw [h.w_eq t ht, h.vL_eq t ht, add_sub_cancel_left, ← intervalIntegral.integral_sub hgw hgL]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← neg_sub (w s.toNNReal) (vL s.toNNReal), ← neg_sub (w s.toNNReal) (vR s.toNNReal), div_neg, div_neg]
    ring
  · rw [h.vR_eq t ht, h.vL_eq t ht, ← intervalIntegral.integral_sub hgR hgL]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← neg_sub (w s.toNNReal) (vL s.toNNReal), div_neg]
    ring

/-- The cross-gap is the integral of `2/L + 2/R` before `T`. -/
theorem IsSeedEntrance.crossGap_eq (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    vR t - vL t = ∫ s in (0 : ℝ)..t, (2 / (w s.toNNReal - vL s.toNNReal) + 2 / (vR s.toNNReal - w s.toNNReal)) := by
  have e : (coord ρL ρR w vL vR e T t).2 = vR t - vL t := by rw [h.coord_eq ht]
  rw [← e]
  unfold coord
  rw [intervalIntegral.integral_congr (eqOn_dens ht),
    intervalIntegral_pair t.coe_nonneg (h.intervalIntegrable_fst ht) (h.intervalIntegrable_snd ht)]

/-- Almost every time before `T` has positive gaps (the collision sets are null). -/
theorem IsSeedEntrance.ae_gap_pos (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) :
    ∀ᵐ s : ℝ, 0 ≤ s → (s.toNNReal : ℝ≥0∞) < T →
      0 < w s.toNNReal - vL s.toNNReal ∧ 0 < vR s.toNNReal - w s.toNNReal := by
  have h1 := measure_eq_zero_iff_ae_notMem.1 h.volume_collisionL
  have h2 := measure_eq_zero_iff_ae_notMem.1 h.volume_collisionR
  filter_upwards [h1, h2] with s hs1 hs2 hs0 hsT
  exact ⟨sub_pos.2 (lt_of_le_of_ne (h.vL_le_w _ hsT) fun he => hs1 ⟨hs0, hsT, he.symm⟩),
    sub_pos.2 (lt_of_le_of_ne (h.w_le_vR _ hsT) fun he => hs2 ⟨hs0, hsT, he⟩)⟩

/-- **(IN2)**: `D_t² ≥ 16 t` before `T`. -/
theorem IsSeedEntrance.sixteen_mul_le_sq (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : 16 * (t : ℝ) ≤ (vR t - vL t) ^ 2 := by
  set g : ℝ → ℝ := fun s => 2 / (w s.toNNReal - vL s.toNNReal) + 2 / (vR s.toNNReal - w s.toNNReal) with hgdef
  set Y : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, g s with hYdef
  have hg : IntervalIntegrable g volume 0 t := h.intervalIntegrable_snd ht
  have hY0 : Y 0 = 0 := intervalIntegral.integral_same
  have hYc : ContinuousOn Y (Icc 0 t) := by
    have := intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc
    rwa [uIcc_of_le t.coe_nonneg] at this
  have hYeq : ∀ r ∈ Icc (0 : ℝ) t, Y r = vR r.toNNReal - vL r.toNNReal := fun r hr => by
    rw [h.crossGap_eq (toNNReal_lt_of_mem_Icc ht hr), Real.coe_toNNReal _ hr.1]
  have hbd : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) t → 0 < Y s ∧ 8 / Y s ≤ g s := by
    filter_upwards [h.ae_gap_pos] with s hs hsI
    obtain ⟨hL, hR⟩ := hs hsI.1 (toNNReal_lt_of_mem_Icc ht hsI)
    rw [hYeq s hsI]
    have e : vR s.toNNReal - vL s.toNNReal = (w s.toNNReal - vL s.toNNReal) + (vR s.toNNReal - w s.toNNReal) := by
      ring
    refine ⟨by rw [e]; exact add_pos hL hR, ?_⟩
    rw [e, hgdef]
    have := eight_div_add_le hL hR
    linarith
  have key := sq_add_le_sq_of_eq_integral t.coe_nonneg hYc (le_of_eq hY0.symm) hg
    (fun r _ => by rw [hY0, zero_add]) hbd
  rw [hY0, hYeq t ⟨t.coe_nonneg, le_rfl⟩, Real.toNNReal_coe] at key
  linarith

/-- The density is bounded by a multiple of `2/L + 2/R` plus `C`. -/
theorem IsSeedEntrance.norm_dens_le (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {s : ℝ}
    (hsT : (s.toNNReal : ℝ≥0∞) < T) :
    ‖dens ρL ρR w vL vR e T s‖ ≤ (|ρL + 2| + |ρR| + 2) / 2 *
      (2 / (w s.toNNReal - vL s.toNNReal) + 2 / (vR s.toNNReal - w s.toNNReal)) + C := by
  simp only [dens, hsT, ↓reduceIte]
  set L := w s.toNNReal - vL s.toNNReal with hLdef
  set R := vR s.toNNReal - w s.toNNReal with hRdef
  have hL : 0 ≤ L := sub_nonneg.2 (h.vL_le_w _ hsT)
  have hR : 0 ≤ R := sub_nonneg.2 (h.w_le_vR _ hsT)
  have he := h.abs_e_le _ hsT
  have hC : 0 ≤ C := (abs_nonneg _).trans he
  have hiL : 0 ≤ 1 / L := by positivity
  have hiR : 0 ≤ 1 / R := by positivity
  have hx : |(ρL + 2) / L - ρR / R + e s.toNNReal| ≤ |ρL + 2| * (1 / L) + |ρR| * (1 / R) + C := by
    have h1 : |(ρL + 2) / L| = |ρL + 2| * (1 / L) := by
      rw [abs_div, abs_of_nonneg hL]; ring
    have h2 : |ρR / R| = |ρR| * (1 / R) := by
      rw [abs_div, abs_of_nonneg hR]; ring
    calc |(ρL + 2) / L - ρR / R + e s.toNNReal| ≤ |(ρL + 2) / L - ρR / R| + |e s.toNNReal| := abs_add_le _ _
      _ ≤ |(ρL + 2) / L| + |ρR / R| + |e s.toNNReal| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by rw [h1, h2]; linarith
  have hy : 0 ≤ 2 / L + 2 / R := by positivity
  rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy]
  have ha := abs_nonneg (ρL + 2)
  have hb := abs_nonneg ρR
  have e2 : (|ρL + 2| + |ρR| + 2) / 2 * (2 / L + 2 / R) =
      (|ρL + 2| + |ρR|) * (1 / L + 1 / R) + (2 / L + 2 / R) := by ring
  rw [e2]
  constructor
  · have : |ρL + 2| * (1 / L) + |ρR| * (1 / R) ≤ (|ρL + 2| + |ρR|) * (1 / L + 1 / R) := by nlinarith
    linarith
  · nlinarith [mul_nonneg (add_nonneg ha hb) (add_nonneg hiL hiR)]

/-- **An improper bound gives integrability up to the endpoint.** -/
theorem intervalIntegrable_of_forall_lt {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {σ I : ℝ} (hσ : 0 ≤ σ)
    (hI0 : 0 ≤ I) (hf : ∀ t, 0 ≤ t → t < σ → IntervalIntegrable f volume 0 t)
    (hI : ∀ t, 0 ≤ t → t < σ → ∫ x in (0 : ℝ)..t, ‖f x‖ ≤ I) :
    IntervalIntegrable f volume 0 σ ∧ ∫ x in (0 : ℝ)..σ, ‖f x‖ ≤ I := by
  rcases hσ.eq_or_lt with h0 | hpos
  · subst h0; exact ⟨IntervalIntegrable.refl, by rw [intervalIntegral.integral_same]; exact hI0⟩
  set bs : ℕ → ℝ := fun i => σ * (1 - 1 / ((i : ℝ) + 2)) with hbs
  have hb0 : ∀ i, 0 ≤ bs i := fun i => by
    have : 1 / ((i : ℝ) + 2) ≤ 1 := by rw [div_le_one (by positivity)]; linarith [i.cast_nonneg (α := ℝ)]
    exact mul_nonneg hσ (by linarith)
  have hbσ : ∀ i, bs i < σ := fun i => by
    have : 0 < 1 / ((i : ℝ) + 2) := by positivity
    simp only [hbs]; nlinarith
  have hlim : Tendsto bs atTop (𝓝 σ) := by
    have h1 : Tendsto (fun i : ℕ => 1 / ((i : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1) |>.congr fun i => by
        simp only [Function.comp, Nat.cast_add, Nat.cast_one]; ring_nf
    have h2 := (h1.const_sub 1).const_mul σ
    simp only [sub_zero, mul_one] at h2
    exact h2
  have hint : IntegrableOn f (Ioc 0 σ) := by
    refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_right (I := I) (fun i => ?_) hlim
      (Eventually.of_forall fun i => ?_)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (hb0 i)).1 (hf _ (hb0 i) (hbσ i))
    · rw [← intervalIntegral.integral_of_le (hb0 i)]; exact hI _ (hb0 i) (hbσ i)
  have hfi : IntervalIntegrable f volume 0 σ := (intervalIntegrable_iff_integrableOn_Ioc_of_le hσ).2 hint
  refine ⟨hfi, ?_⟩
  have hc := intervalIntegral.continuousOn_primitive_interval' hfi.norm left_mem_uIcc
  rw [uIcc_of_le hσ] at hc
  have ht : Tendsto (fun i => ∫ x in (0 : ℝ)..bs i, ‖f x‖) atTop (𝓝 (∫ x in (0 : ℝ)..σ, ‖f x‖)) :=
    (hc σ ⟨hσ, le_rfl⟩).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i =>
      ⟨hb0 i, (hbσ i).le⟩⟩)
  exact le_of_tendsto ht (Eventually.of_forall fun i => hI _ (hb0 i) (hbσ i))

/-- **The density is integrable up to a time `σ ≤ T` before which `D ≤ d`**, with total variation at most
`K d + C σ`. -/
theorem IsSeedEntrance.intervalIntegrable_dens (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) (hC : 0 ≤ C)
    {σ : ℝ≥0} (hσT : (σ : ℝ≥0∞) ≤ T) {d : ℝ} (hd0 : 0 ≤ d) (hd : ∀ t : ℝ≥0, t < σ → vR t - vL t ≤ d) :
    IntervalIntegrable (dens ρL ρR w vL vR e T) volume 0 σ ∧
      ∫ s in (0 : ℝ)..σ, ‖dens ρL ρR w vL vR e T s‖ ≤ (|ρL + 2| + |ρR| + 2) / 2 * d + C * σ := by
  have hK : 0 ≤ (|ρL + 2| + |ρR| + 2) / 2 := by positivity
  refine intervalIntegrable_of_forall_lt σ.coe_nonneg (by positivity) (fun t ht0 htσ => ?_) (fun t ht0 htσ => ?_)
  · have : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
      lt_of_lt_of_le (by exact_mod_cast (Real.toNNReal_lt_iff_lt_coe ht0).2 htσ |>.trans_le le_rfl) hσT
    have hi := h.intervalIntegrable_dens_of_lt this
    rwa [Real.coe_toNNReal _ ht0] at hi
  · have htT : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
      lt_of_lt_of_le (by exact_mod_cast (Real.toNNReal_lt_iff_lt_coe ht0).2 htσ) hσT
    have hi := h.intervalIntegrable_dens_of_lt htT
    have hs := h.intervalIntegrable_snd htT
    rw [Real.coe_toNNReal _ ht0] at hi hs
    calc ∫ x in (0 : ℝ)..t, ‖dens ρL ρR w vL vR e T x‖
        ≤ ∫ x in (0 : ℝ)..t, ((|ρL + 2| + |ρR| + 2) / 2 *
          (2 / (w x.toNNReal - vL x.toNNReal) + 2 / (vR x.toNNReal - w x.toNNReal)) + C) := by
          refine intervalIntegral.integral_mono_on ht0 hi.norm ((hs.const_mul _).add intervalIntegrable_const)
            fun x hx => h.norm_dens_le (toNNReal_lt_of_mem_Icc htT (by rwa [Real.coe_toNNReal _ ht0]))
      _ = (|ρL + 2| + |ρR| + 2) / 2 * (vR t.toNNReal - vL t.toNNReal) + C * t := by
          rw [intervalIntegral.integral_add (hs.const_mul _) intervalIntegrable_const,
            intervalIntegral.integral_const_mul, ← Real.coe_toNNReal _ ht0, ← h.crossGap_eq htT,
            intervalIntegral.integral_const, smul_eq_mul, sub_zero, Real.coe_toNNReal _ ht0, mul_comm C]
      _ ≤ (|ρL + 2| + |ρR| + 2) / 2 * d + C * σ := by
          gcongr
          exact hd _ ((Real.toNNReal_lt_iff_lt_coe ht0).2 htσ)

/-! ### Continuity of the cross-gap and hitting times -/

/-- The cross-gap `D` is continuous before `T`. -/
theorem IsSeedEntrance.continuousOn_crossGap (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) :
    ContinuousOn (fun t : ℝ≥0 => vR t - vL t) {t | (t : ℝ≥0∞) < T} := by
  intro t₀ ht₀
  obtain ⟨t₁, ht₀₁, ht₁T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (show (t₀ : ℝ≥0∞) < T from ht₀)
  have ht₀₁' : t₀ < t₁ := by exact_mod_cast ht₀₁
  set g : ℝ → ℝ := fun s => 2 / (w s.toNNReal - vL s.toNNReal) + 2 / (vR s.toNNReal - w s.toNNReal)
  have hF := intervalIntegral.continuousOn_primitive_interval' (h.intervalIntegrable_snd ht₁T) left_mem_uIcc
  rw [uIcc_of_le t₁.coe_nonneg] at hF
  have hc : ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..(t : ℝ), g s) (Iic t₁) :=
    hF.comp NNReal.continuous_coe.continuousOn fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  have heq : (fun t : ℝ≥0 => vR t - vL t) =ᶠ[𝓝 t₀] fun t : ℝ≥0 => ∫ s in (0 : ℝ)..(t : ℝ), g s := by
    filter_upwards [Iic_mem_nhds ht₀₁'] with t ht
    exact h.crossGap_eq (lt_of_le_of_lt (by exact_mod_cast ht) ht₁T)
  exact ((hc.continuousAt (Iic_mem_nhds ht₀₁')).congr heq.symm).continuousWithinAt

/-- Before a rational hitting time of `{d < f}` (and before `T`), a function continuous before `T` is `≤ d`. -/
theorem le_of_lt_hitTime {f : ℝ≥0 → ℝ} {d : ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < T}) {t : ℝ≥0}
    (htT : (t : ℝ≥0∞) < T) (ht : (t : ℝ≥0∞) < Band.hitTime (fun s => d < f s) T) : f t ≤ d := by
  by_contra hlt
  push Not at hlt
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < T} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hnhds : {s : ℝ≥0 | d < f s ∧ (s : ℝ≥0∞) < T} ∈ 𝓝 t := by
    have h1 := (hf.continuousAt (hopen.mem_nhds htT)).eventually (lt_mem_nhds hlt)
    filter_upwards [h1, hopen.mem_nhds htT] with s hs1 hs2 using ⟨hs1, hs2⟩
  obtain ⟨u, htu, hu⟩ := exists_Ico_subset_of_mem_nhds hnhds (exists_gt t)
  obtain ⟨q, hq0, htq, hqu⟩ := ENNReal.lt_iff_exists_rat_btwn.1
    (show (t : ℝ≥0∞) < min (u : ℝ≥0∞) (Band.hitTime (fun s => d < f s) T) from lt_min (by exact_mod_cast htu) ht)
  have hqI : Real.toNNReal q ∈ Ico t u :=
    ⟨by exact_mod_cast htq.le, by exact_mod_cast lt_of_lt_of_le hqu (min_le_left _ _)⟩
  obtain ⟨hdq, hqT⟩ := hu hqI
  have := Band.hitTime_le (p := fun s => d < f s) hqT hdq
  exact absurd (lt_of_lt_of_le hqu (min_le_right _ _)) (not_lt.2 this)

/-- At a rational hitting time of `{d < f}` strictly before `T`, a function continuous before `T` is `≥ d`. -/
theorem le_of_hitTime_eq {f : ℝ≥0 → ℝ} {d : ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < T}) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) = Band.hitTime (fun s => d < f s) T) (hτT : (τ : ℝ≥0∞) < T) : d ≤ f τ := by
  by_contra hlt
  push Not at hlt
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < T} := isOpen_lt ENNReal.continuous_coe continuous_const
  have h1 := (hf.continuousAt (hopen.mem_nhds hτT)).eventually (gt_mem_nhds hlt)
  obtain ⟨u, hτu, hu⟩ := exists_Ico_subset_of_mem_nhds h1 (exists_gt τ)
  have hlt' : Band.hitTime (fun s => d < f s) T < (u : ℝ≥0∞) := by rw [← hτ]; exact_mod_cast hτu
  obtain ⟨r, hru, hrT, hdr⟩ := Band.hitTime_lt_iff.1 hlt'
  have hτr : τ ≤ Real.toNNReal r := by
    have := Band.hitTime_le (p := fun s => d < f s) hrT hdr
    rw [← hτ] at this; exact_mod_cast this
  exact absurd (hu ⟨hτr, by exact_mod_cast hru⟩) (not_lt.2 hdr.le)

/-! ### The generator along a path and bounds on the test function -/

/-- **The generator is nonnegative along the path** at a time before `T` with positive gaps and `D ≤ d`. -/
theorem IsSeedEntrance.itoGen_nonneg (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) {m d α β n : ℝ} (hα : 0 < α)
    (hαβ : α < β) (hm : 0 < m) (ha : m ≤ ρL + 2) (hb : m ≤ -(ρR + 2)) (hCd : C * d ≤ 2 * m)
    (hβn : Real.log β + n ≤ 0) {s : ℝ} (hsT : (s.toNNReal : ℝ≥0∞) < T) (hL : 0 < w s.toNNReal - vL s.toNNReal)
    (hR : 0 < vR s.toNNReal - w s.toNNReal) (hDd : vR s.toNNReal - vL s.toNNReal ≤ d) :
    0 ≤ Ito.itoGen (phi κ (m / 4) α β n) (coord ρL ρR w vL vR e T s.toNNReal, b s.toNNReal)
      (dens ρL ρR w vL vR e T s) := by
  rw [h.coord_eq hsT]
  simp only [dens, hsT, ↓reduceIte]
  have e1 : vR s.toNNReal - vL s.toNNReal = (w s.toNNReal - vL s.toNNReal) + (vR s.toNNReal - w s.toNNReal) := by
    ring
  rw [e1] at hDd ⊢
  exact itoGen_phi_nonneg hα hαβ hm ha hb (h.abs_e_le _ hsT) hCd hL hR hDd hβn (by ring)

/-- The lower cutoff level `α_n = e^{−(n+1)}`. -/
def alpha (n : ℕ) : ℝ := Real.exp (-((n : ℝ) + 1))

/-- The upper cutoff level `β_n = e^{−n}`. -/
def beta (n : ℕ) : ℝ := Real.exp (-(n : ℝ))

theorem alpha_pos (n : ℕ) : 0 < alpha n := Real.exp_pos _

theorem alpha_lt_beta (n : ℕ) : alpha n < beta n := Real.exp_lt_exp.2 (by linarith)

theorem log_beta_add (n : ℕ) : Real.log (beta n) + n = 0 := by rw [beta, Real.log_exp]; ring

theorem g1_mul_mem {α β : ℝ} {L D : ℝ} (hL : 0 ≤ L) (hLD : L ≤ D) :
    0 ≤ g1 α β D * L ∧ g1 α β D * L ≤ 1 := by
  rcases le_or_gt D 0 with hD | hD
  · have : L = 0 := le_antisymm (hLD.trans hD) hL
    simp [this]
  · have h1 : g1 α β D * L = cut α β D * (L / D) := by unfold g1; ring
    have h2 : L / D ≤ 1 := (div_le_one hD).2 hLD
    have h3 : 0 ≤ L / D := div_nonneg hL hD.le
    rw [h1]
    exact ⟨mul_nonneg (cut_nonneg _) h3, by nlinarith [cut_nonneg (α := α) (β := β) D, cut_le_one (α := α) (β := β) D]⟩

theorem neg_one_le_g2 (n : ℕ) (D : ℝ) : -1 ≤ g2 (alpha n) (beta n) n D := by
  unfold g2
  rcases le_or_gt D (alpha n) with hD | hD
  · rw [cut_eq_zero (alpha_lt_beta n) hD]; norm_num
  · have hlog : -((n : ℝ) + 1) < Real.log D := by
      rw [← Real.log_exp (-((n : ℝ) + 1))]
      exact Real.log_lt_log (alpha_pos n) hD
    have := cut_nonneg (α := alpha n) (β := beta n) D
    have := cut_le_one (α := alpha n) (β := beta n) D
    nlinarith

theorem g2_le (n : ℕ) {d D : ℝ} (hD : D ≤ d) : g2 (alpha n) (beta n) n D ≤ max 0 (Real.log d + n) := by
  unfold g2
  rcases le_or_gt D (alpha n) with hDα | hDα
  · rw [cut_eq_zero (alpha_lt_beta n) hDα, zero_mul]; exact le_max_left _ _
  · have hD0 : 0 < D := (alpha_pos n).trans hDα
    have hlog : Real.log D ≤ Real.log d := Real.log_le_log hD0 hD
    have h0 := cut_nonneg (α := alpha n) (β := beta n) D
    have h1 := cut_le_one (α := alpha n) (β := beta n) D
    rcases le_or_gt 0 (Real.log D + n) with hx | hx
    · calc cut (alpha n) (beta n) D * (Real.log D + n) ≤ 1 * (Real.log D + n) := by gcongr
        _ ≤ max 0 (Real.log d + n) := by rw [one_mul]; exact le_max_of_le_right (by linarith)
    · exact (mul_nonpos_of_nonneg_of_nonpos h0 hx.le).trans (le_max_left _ _)

/-- `Φ ≤ 1 + c` at an ordered state `0 ≤ L ≤ D`. -/
theorem phi_le_one_add (n : ℕ) {c l D x : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ l + Real.sqrt κ * x)
    (hLD : l + Real.sqrt κ * x ≤ D) : phi κ c (alpha n) (beta n) n ((l, D), x) ≤ 1 + c := by
  unfold phi
  have h1 := (g1_mul_mem (α := alpha n) (β := beta n) hL hLD).2
  have h2 := neg_one_le_g2 n D
  simp only
  nlinarith

/-- `Φ ≥ −c max(0, log d + n)` at an ordered state with `D ≤ d`. -/
theorem le_phi (n : ℕ) {c d l D x : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ l + Real.sqrt κ * x)
    (hLD : l + Real.sqrt κ * x ≤ D) (hD : D ≤ d) :
    -(c * max 0 (Real.log d + n)) ≤ phi κ c (alpha n) (beta n) n ((l, D), x) := by
  unfold phi
  have h1 := (g1_mul_mem (α := alpha n) (β := beta n) hL hLD).1
  have h2 := g2_le n hD
  simp only
  nlinarith

/-- **On the success event** (`D ≥ d ≥ e^{−n}`): `Φ ≤ 1 − c (log d + n)`. -/
theorem phi_le_of_le (n : ℕ) {c d l D x : ℝ} (hc : 0 ≤ c) (hβd : beta n ≤ d) (hdD : d ≤ D)
    (hLD : l + Real.sqrt κ * x ≤ D) :
    phi κ c (alpha n) (beta n) n ((l, D), x) ≤ 1 - c * (Real.log d + n) := by
  have hd0 : 0 < d := (Real.exp_pos _).trans_le hβd
  have hD0 : 0 < D := hd0.trans_le hdD
  have hcut : cut (alpha n) (beta n) D = 1 := cut_eq_one (alpha_lt_beta n) (hβd.trans hdD)
  unfold phi g1 g2
  simp only [hcut, one_mul]
  have h1 : 1 / D * (l + Real.sqrt κ * x) ≤ 1 := by
    rw [one_div_mul_eq_div, div_le_one hD0]; exact hLD
  have h2 : Real.log d ≤ Real.log D := Real.log_le_log hd0 hdD
  nlinarith

/-! ### The state up to the stop -/

/-- The closed set of states `0 ≤ L ≤ D ≤ d`, `|x| ≤ R`, with `L = l + √κ x`. -/
def stateSet (κ d R : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 ≤ p.1.1 + Real.sqrt κ * p.2 ∧ p.1.1 + Real.sqrt κ * p.2 ≤ p.1.2 ∧ p.1.2 ≤ d ∧ |p.2| ≤ R}

theorem isClosed_stateSet (κ d R : ℝ) : IsClosed (stateSet κ d R) := by
  have h1 : Continuous fun p : (ℝ × ℝ) × ℝ => p.1.1 + Real.sqrt κ * p.2 :=
    (continuous_fst.comp continuous_fst).add (continuous_const.mul continuous_snd)
  have h2 : Continuous fun p : (ℝ × ℝ) × ℝ => p.1.2 := continuous_snd.comp continuous_fst
  have e : stateSet κ d R = ({p | 0 ≤ p.1.1 + Real.sqrt κ * p.2} ∩ {p | p.1.1 + Real.sqrt κ * p.2 ≤ p.1.2}) ∩
      ({p | p.1.2 ≤ d} ∩ {p | |p.2| ≤ R}) := by
    ext p
    exact ⟨fun ⟨a, b, c, d⟩ => ⟨⟨a, b⟩, c, d⟩, fun ⟨⟨a, b⟩, c, d⟩ => ⟨a, b, c, d⟩⟩
  rw [e]
  exact ((isClosed_le continuous_const h1).inter (isClosed_le h1 h2)).inter
    ((isClosed_le h2 continuous_const).inter (isClosed_le (continuous_abs.comp continuous_snd) continuous_const))

/-- The state set is inside a compact box. -/
theorem stateSet_subset (κ d R : ℝ) (hd : 0 ≤ d) :
    stateSet κ d R ⊆ (Icc (-(d + Real.sqrt κ * R)) (d + Real.sqrt κ * R) ×ˢ Icc 0 d) ×ˢ Icc (-R) R := by
  rintro ⟨⟨l, D⟩, x⟩ ⟨h1, h2, h3, h4⟩
  simp only at h1 h2 h3 h4
  have hs := Real.sqrt_nonneg κ
  have hx := abs_le.1 h4
  refine ⟨⟨⟨?_, ?_⟩, ⟨by linarith, h3⟩⟩, hx⟩
  · nlinarith
  · nlinarith

/-- **The state stays in the state set up to the stop** `σ ≤ min(T, τ_d, τ_R)`, endpoint included. -/
theorem IsSeedEntrance.mem_stateSet (h : IsSeedEntrance κ ρL ρR C w vL vR b e T) (hC : 0 ≤ C)
    (hbc : Continuous b) (hb0 : b 0 = 0) {d R : ℝ} (hd : 0 ≤ d) (hR0 : 0 ≤ R) {σ : ℝ≥0} (hσT : (σ : ℝ≥0∞) ≤ T)
    (hσd : (σ : ℝ≥0∞) ≤ Band.hitTime (fun s => d < vR s - vL s) T)
    (hσR : (σ : ℝ≥0∞) ≤ Band.hitTime (fun s => R < |b s|) ⊤) {t : ℝ≥0} (ht : t ≤ σ) :
    (coord ρL ρR w vL vR e T t, b t) ∈ stateSet κ d R := by
  -- strictly before the stop
  have hlt : ∀ t : ℝ≥0, t < σ → (coord ρL ρR w vL vR e T t, b t) ∈ stateSet κ d R := by
    intro t htσ
    have htT : (t : ℝ≥0∞) < T := lt_of_lt_of_le (by exact_mod_cast htσ) hσT
    have hDd : vR t - vL t ≤ d := le_of_lt_hitTime h.continuousOn_crossGap htT
      (lt_of_lt_of_le (by exact_mod_cast htσ) hσd)
    have hbR : |b t| ≤ R := le_of_lt_hitTime (T := ⊤) (f := fun s => |b s|)
      (continuous_abs.comp hbc).continuousOn ENNReal.coe_lt_top (lt_of_lt_of_le (by exact_mod_cast htσ) hσR)
    rw [h.coord_eq htT]
    have h1 := h.vL_le_w t htT
    have h2 := h.w_le_vR t htT
    refine ⟨?_, ?_, hDd, hbR⟩ <;> simp only <;> linarith
  rcases ht.lt_or_eq with ht | ht
  · exact hlt t ht
  rw [ht]
  rcases (zero_le : (0 : ℝ≥0) ≤ σ).lt_or_eq with hσ0 | hσ0
  · -- the endpoint: a limit from the left
    have hdd : ∀ t : ℝ≥0, t < σ → vR t - vL t ≤ d := fun t htσ =>
      le_of_lt_hitTime h.continuousOn_crossGap (lt_of_lt_of_le (by exact_mod_cast htσ) hσT)
        (lt_of_lt_of_le (by exact_mod_cast htσ) hσd)
    have hint := (h.intervalIntegrable_dens hC hσT hd hdd).1
    have hF := intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
    rw [uIcc_of_le σ.coe_nonneg] at hF
    have hc : ContinuousOn (fun t : ℝ≥0 => (coord ρL ρR w vL vR e T t, b t)) (Iic σ) :=
      (hF.comp NNReal.continuous_coe.continuousOn fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht⟩).prodMk
        hbc.continuousOn
    have hmem : σ ∈ closure (Iio σ) := by
      rw [closure_Iio' (a := σ) ⟨0, hσ0⟩]; exact mem_Iic.2 le_rfl
    have := (hc σ (mem_Iic.2 le_rfl)).mono Iio_subset_Iic_self
    exact (isClosed_stateSet κ d R).closure_subset (this.mem_closure hmem fun t ht => hlt t ht)
  · subst hσ0
    have e0 : coord ρL ρR w vL vR e T 0 = 0 := by simp [coord]
    rw [e0, hb0]
    exact ⟨by simp, by simp, by simpa using hd, by simpa using hR0⟩

end Aux104

end Sec7

end InteractingSLE
