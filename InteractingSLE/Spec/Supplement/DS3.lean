/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2

/-!
# Lemma DS3 (including the double-seed entrance): the statement, and the cross-gap growth `D_t ≥ 4√t`

Packet PROVE-T14-TIP2. Specification supplement §12, **Lemma DS3** (`source/spec/p529-576.md` L597–L611, p. 554):

> Suppose the limiting initial state has two admissible seed groups at the driver, all other initial groups are
> separated from it, and the uniform inner partial-sum bound (DS1.1) holds. Then the conclusion of DS2 also holds from
> time zero. In particular it permits arbitrary admissible original-boundary and old-angle mergers after the initial
> time and before the far-buffer exit. The application below varies weights at fixed initial positions; no assertion
> about arbitrary changing initial coincidence patterns is needed.

* `DS3Statement`: the lemma in DS2's open-set form, at fixed initial positions with both nearest labels at the driver
  (no cross-gap hypothesis).
* **`sq_crossGap_ge`**, **`four_mul_sqrt_le_crossGap`** (proved, deterministic): the proof's estimate "Its geometric
  cross gap `D_t = V^{1,R}_t − V^{1,L}_t = X₁(t) + Y₁(t)` is continuous, nondecreasing and strictly positive for every
  `t > 0`. More quantitatively, its integrated equation and capacity-null collision sets give
  `(D_t²)' = 4D_t(X₁⁻¹ + Y₁⁻¹) ≥ 16` almost everywhere, `D_t ≥ 4√t`", along every integrated path:
  `D_t² ≥ D_0² + 16 t` before the lifetime. The proof uses no derivative of `D²`: `D_v (D_v − D_u) ≥ 8(v − u)`
  (`crossGap_mul_sub_ge`, from `(2/X + 2/Y)(X + Y) ≥ 8` a.e.) is summed over fine partitions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DS3

open DS2

/-- **Named statement: Lemma DS3** (p. 554), in DS2's open-set form. Fixed initial positions with both nearest labels
at the driver (two seed groups) and every other label `η`-separated from it, weights converging with (DS1.1) uniform;
any integrated evolutions of the words and of the limiting word: for every horizon `T` and every open set `U` of
continuous state paths on `[0, T]` inside the far buffer,
`P₀(alive through T, path ∈ U) ≤ liminf_m P_m(alive through T, path ∈ U)`. -/
def DS3Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ {nL nR : ℕ} (hnL : 0 < nL) (hnR : 0 < nR) (mL mR : ℕ) (Rw ε g η : ℝ),
    0 < ε → 0 < g → 0 < η →
    ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : ℕ → Fin nL → ℝ) (ρR : ℕ → Fin nR → ℝ) (ρL₀ : Fin nL → ℝ)
      (ρR₀ : Fin nR → ℝ),
      -- two seed groups at the driver, every other group separated from it
      xL ⟨0, hnL⟩ = 0 → xR ⟨0, hnR⟩ = 0 → (∀ i, xL i ≠ 0 → xL i ≤ -η) → (∀ j, xR j ≠ 0 → η ≤ xR j) →
      (∀ m, IsDS1Word mL mR Rw ε xL xR (ρL m) (ρR m)) → IsDS1Word mL mR Rw ε xL xR ρL₀ ρR₀ →
      Tendsto ρL atTop (𝓝 ρL₀) → Tendsto ρR atTop (𝓝 ρR₀) →
      ∀ (Ω : ℕ → Type u) [mΩ : ∀ m, MeasurableSpace (Ω m)] (P : ∀ m, Measure (Ω m))
        (𝓕 : ∀ m, Filtration ℝ≥0 (mΩ m)) (W : ∀ m, ℝ≥0 → Ω m → ℝ) (VL : ∀ m, Fin nL → ℝ≥0 → Ω m → ℝ)
        (VR : ∀ m, Fin nR → ℝ≥0 → Ω m → ℝ) (B : ∀ m, ℝ≥0 → Ω m → ℝ) (ζ : ∀ m, Ω m → ℝ≥0∞),
        (∀ m, IsIntegratedSLEEvolution κ xL xR (ρL m) (ρR m) (P m) (𝓕 m) (W m) (VL m) (VR m) (B m) (ζ m)) →
      ∀ {Ω₀ : Type u} {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) (𝓕₀ : Filtration ℝ≥0 mΩ₀)
        (W₀ : ℝ≥0 → Ω₀ → ℝ) (VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ)
        (B₀ : ℝ≥0 → Ω₀ → ℝ) (ζ₀ : Ω₀ → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL xR ρL₀ ρR₀ P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ →
      ∀ (T : ℝ≥0) (U : Set C(Set.Icc (0 : ℝ≥0) T, ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))), IsOpen U →
        (∀ f ∈ U, ∀ t, InFarBuffer mL mR g (f t)) →
        P₀ (pathEvent T U W₀ VL₀ VR₀ ζ₀) ≤
          liminf (fun m => P m (pathEvent T U (W m) (VL m) (VR m) (ζ m))) atTop

/-! ### The cross gap -/

section CrossGap

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The cross gap `D = V^{1,R} − V^{1,L}` of the two nearest labels. -/
def crossGap (hnL : 0 < nL) (hnR : 0 < nR) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  vR ⟨0, hnR⟩ t - vL ⟨0, hnL⟩ t

variable (hnL : 0 < nL) (hnR : 0 < nR) (hp : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ)
include hp

theorem crossGap_nonneg {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : 0 ≤ crossGap hnL hnR vL vR t := by
  have h1 := hp.vL_le_w ht ⟨0, hnL⟩
  have h2 := hp.w_le_vR ht ⟨0, hnR⟩
  unfold crossGap; linarith

theorem crossGap_mono {u v : ℝ≥0} (huv : u ≤ v) (hv : (v : ℝ≥0∞) < ζ) :
    crossGap hnL hnR vL vR u ≤ crossGap hnL hnR vL vR v := by
  have h1 := hp.vL_le_of_le huv hv ⟨0, hnL⟩
  have h2 := hp.le_vR_of_le huv hv ⟨0, hnR⟩
  unfold crossGap; linarith

/-- **`D_v (D_v − D_u) ≥ 8 (v − u)`** before the lifetime: `D_v − D_u = ∫ᵤᵛ (2/X₁ + 2/Y₁)` and, off the null collision
sets, `(2/X₁ + 2/Y₁) D_v ≥ (2/X₁ + 2/Y₁)(X₁ + Y₁) ≥ 8`. -/
theorem crossGap_mul_sub_ge {u v : ℝ≥0} (huv : u ≤ v) (hv : (v : ℝ≥0∞) < ζ) :
    8 * ((v : ℝ) - u) ≤ crossGap hnL hnR vL vR v * (crossGap hnL hnR vL vR v - crossGap hnL hnR vL vR u) := by
  set i₀ : Fin nL := ⟨0, hnL⟩
  set j₀ : Fin nR := ⟨0, hnR⟩
  set Dv := crossGap hnL hnR vL vR v
  have huv' : (u : ℝ) ≤ v := by exact_mod_cast huv
  set f : ℝ → ℝ := fun r => 2 / (vR j₀ r.toNNReal - w r.toNNReal) - 2 / (vL i₀ r.toNNReal - w r.toNNReal) with hf
  have hsub : Set.uIcc (u : ℝ) v ⊆ Set.uIcc 0 (v : ℝ) := by
    rw [Set.uIcc_of_le huv', Set.uIcc_of_le (NNReal.coe_nonneg v)]
    exact Set.Icc_subset_Icc (NNReal.coe_nonneg u) le_rfl
  have hfi : IntervalIntegrable f volume u v :=
    ((hp.intervalIntegrable_forceR hv j₀).sub (hp.intervalIntegrable_forceL hv i₀)).mono_set hsub
  have hD : Dv - crossGap hnL hnR vL vR u = ∫ r in (u : ℝ)..v, f r := by
    simp only [Dv, crossGap, hf]
    rw [intervalIntegral.integral_sub ((hp.intervalIntegrable_forceR hv j₀).mono_set hsub)
      ((hp.intervalIntegrable_forceL hv i₀).mono_set hsub), ← hp.vR_sub huv hv j₀, ← hp.vL_sub huv hv i₀]
    ring
  have hlt : ∀ r : ℝ, r ∈ Set.Icc (u : ℝ) v → (r.toNNReal : ℝ≥0∞) < ζ := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) hv
  have hae : ∀ᵐ r ∂volume.restrict (Set.Icc (u : ℝ) v), 8 ≤ Dv * f r := by
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hp.volume_collisionL i₀),
      measure_eq_zero_iff_ae_notMem.1 (hp.volume_collisionR j₀)] with r hrL hrR hr
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg u).trans hr.1
    have hζ := hlt r hr
    have hX : 0 < w r.toNNReal - vL i₀ r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (hp.vL_le_w hζ i₀) fun he => hrL ⟨hr0, hζ, he.symm⟩)
    have hY : 0 < vR j₀ r.toNNReal - w r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (hp.w_le_vR hζ j₀) fun he => hrR ⟨hr0, hζ, he⟩)
    set X := w r.toNNReal - vL i₀ r.toNNReal
    set Y := vR j₀ r.toNNReal - w r.toNNReal
    have hfr : f r = 2 / Y + 2 / X := by
      simp only [hf]
      rw [show vL i₀ r.toNNReal - w r.toNNReal = -X by simp only [X]; ring, div_neg]
      ring
    have hDr : crossGap hnL hnR vL vR r.toNNReal = X + Y := by simp only [crossGap, X, Y]; ring
    have hrv : r.toNNReal ≤ v := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hmono : X + Y ≤ Dv := hDr ▸ crossGap_mono hnL hnR hp hrv hv
    have hpos : 0 ≤ f r := by rw [hfr]; positivity
    have key : 8 ≤ (X + Y) * f r := by
      rw [hfr]
      have : (X + Y) * (2 / Y + 2 / X) = 4 + 2 * (X / Y) + 2 * (Y / X) := by field_simp; ring
      rw [this]
      have h1 : 0 < X / Y := div_pos hX hY
      have h2 : X / Y * (Y / X) = 1 := by field_simp
      nlinarith [sq_nonneg (X / Y - Y / X), sq_nonneg (X / Y - 1)]
    calc (8 : ℝ) ≤ (X + Y) * f r := key
      _ ≤ Dv * f r := mul_le_mul_of_nonneg_right hmono hpos
  have hint := intervalIntegral.integral_mono_ae_restrict huv' intervalIntegrable_const (hfi.const_mul Dv) hae
  rw [intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul, ← hD] at hint
  linarith

/-- One step: `D_v² − D_u² ≥ 8(v − u)(1 + D_u/D_v)` when `D_u > 0`. -/
theorem sq_crossGap_sub_ge {u v : ℝ≥0} (huv : u ≤ v) (hv : (v : ℝ≥0∞) < ζ) (hu : 0 < crossGap hnL hnR vL vR u) :
    16 * ((v : ℝ) - u) - 8 * ((v : ℝ) - u) * (crossGap hnL hnR vL vR v - crossGap hnL hnR vL vR u) /
        crossGap hnL hnR vL vR u ≤
      crossGap hnL hnR vL vR v ^ 2 - crossGap hnL hnR vL vR u ^ 2 := by
  set a := crossGap hnL hnR vL vR u
  set b := crossGap hnL hnR vL vR v
  have h1 := crossGap_mul_sub_ge hnL hnR hp huv hv
  have hab : a ≤ b := crossGap_mono hnL hnR hp huv hv
  have hb : 0 < b := hu.trans_le hab
  have hΔ : 0 ≤ (v : ℝ) - u := sub_nonneg.2 (by exact_mod_cast huv)
  set Δ := (v : ℝ) - u
  -- `b − a ≥ 8Δ/b`, so `b² − a² ≥ 8Δ(1 + a/b) = 16Δ − 8Δ(b − a)/b ≥ 16Δ − 8Δ(b − a)/a`
  have h2 : 8 * Δ / b ≤ b - a := by rw [div_le_iff₀ hb]; linarith
  have h3 : 8 * Δ * (b - a) / b ≤ 8 * Δ * (b - a) / a :=
    div_le_div_of_nonneg_left (mul_nonneg (by positivity) (sub_nonneg.2 hab)) hu hab
  have h4 : 16 * Δ - 8 * Δ * (b - a) / b ≤ b ^ 2 - a ^ 2 := by
    have e : 16 * Δ - 8 * Δ * (b - a) / b = 8 * Δ / b * (b + a) := by field_simp; ring
    rw [e, show b ^ 2 - a ^ 2 = (b - a) * (b + a) by ring]
    exact mul_le_mul_of_nonneg_right h2 (by linarith)
  linarith

/-- **`D_t² ≥ D_s² + 16 (t − s)`** for `s ≤ t < ζ` when `D_s > 0`: sum the one-step bound over the partition of
`[s, t]` into `N` equal pieces, `D_t² − D_s² ≥ 16(t − s) − 8 (t − s)(D_t − D_s)/(N D_s)`, and let `N → ∞`. -/
theorem sq_crossGap_ge_of_pos {s t : ℝ≥0} (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) (hs : 0 < crossGap hnL hnR vL vR s) :
    crossGap hnL hnR vL vR s ^ 2 + 16 * ((t : ℝ) - s) ≤ crossGap hnL hnR vL vR t ^ 2 := by
  set D := crossGap hnL hnR vL vR
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hN : ∀ N : ℕ, 0 < N → 16 * ((t : ℝ) - s) - 8 * ((t : ℝ) - s) * (D t - D s) / (N * D s) ≤
      D t ^ 2 - D s ^ 2 := by
    intro N hN0
    set Δ : ℝ≥0 := (t - s) / N with hΔ
    set p : ℕ → ℝ≥0 := fun k => s + k * Δ with hp'
    have hpN : p N = t := by
      simp only [hp', hΔ]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hN0.ne'), add_tsub_cancel_of_le hst]
    have hpmono : ∀ k, p k ≤ p (k + 1) := fun k => by
      simp only [hp']; push_cast; gcongr; exact le_add_of_nonneg_right zero_le_one
    have hple : ∀ k, k ≤ N → p k ≤ t := fun k hk => by
      rw [← hpN]; simp only [hp']; gcongr
    have hpge : ∀ k, s ≤ p k := fun k => le_add_of_nonneg_right zero_le
    have hlt : ∀ k, k ≤ N → (p k : ℝ≥0∞) < ζ := fun k hk => lt_of_le_of_lt (by exact_mod_cast hple k hk) ht
    have hDpos : ∀ k, k ≤ N → 0 < D (p k) := fun k hk =>
      hs.trans_le (crossGap_mono hnL hnR hp (hpge k) (hlt k hk))
    have hΔr : ∀ k, ((p (k + 1) : ℝ≥0) : ℝ) - p k = (Δ : ℝ) := fun k => by
      simp only [hp']; push_cast; ring
    -- each step, with `D_{p k} ≥ D_s` in the error term
    have hstep : ∀ k ∈ range N, 16 * (Δ : ℝ) - 8 * (Δ : ℝ) * (D (p (k + 1)) - D (p k)) / D s ≤
        D (p (k + 1)) ^ 2 - D (p k) ^ 2 := by
      intro k hk
      have hk' : k + 1 ≤ N := mem_range.1 hk
      have h := sq_crossGap_sub_ge hnL hnR hp (hpmono k) (hlt (k + 1) hk') (hDpos k (by omega))
      rw [hΔr k] at h
      have hdiff : 0 ≤ D (p (k + 1)) - D (p k) :=
        sub_nonneg.2 (crossGap_mono hnL hnR hp (hpmono k) (hlt (k + 1) hk'))
      have hsk : D s ≤ D (p k) := crossGap_mono hnL hnR hp (hpge k) (hlt k (by omega))
      have : 8 * (Δ : ℝ) * (D (p (k + 1)) - D (p k)) / D (p k) ≤
          8 * (Δ : ℝ) * (D (p (k + 1)) - D (p k)) / D s :=
        div_le_div_of_nonneg_left (mul_nonneg (by positivity) hdiff) hs hsk
      linarith
    have hsum := sum_le_sum hstep
    rw [sum_range_sub (fun k => D (p k) ^ 2), sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsum
    have htel : ∑ k ∈ range N, 8 * (Δ : ℝ) * (D (p (k + 1)) - D (p k)) / D s =
        8 * (Δ : ℝ) * (D t - D s) / D s := by
      rw [← sum_div, ← mul_sum, sum_range_sub (fun k => D (p k)), hpN]
      simp only [hp', CharP.cast_eq_zero, zero_mul, add_zero]
    rw [htel, hpN] at hsum
    have hp0 : p 0 = s := by simp only [hp', CharP.cast_eq_zero, zero_mul, add_zero]
    rw [hp0] at hsum
    have hΔe : (N : ℝ) * (Δ : ℝ) = (t : ℝ) - s := by
      simp only [hΔ]; push_cast
      rw [NNReal.coe_sub hst]; field_simp
    have e2 : 8 * (Δ : ℝ) * (D t - D s) / D s = 8 * ((t : ℝ) - s) * (D t - D s) / (N * D s) := by
      rw [← hΔe]; field_simp
    rw [e2] at hsum
    have h16 : (N : ℝ) * (16 * (Δ : ℝ)) = 16 * ((t : ℝ) - s) := by rw [← hΔe]; ring
    linarith
  -- let `N → ∞`
  by_contra hcon
  push Not at hcon
  have hC : 0 ≤ 8 * ((t : ℝ) - s) * (D t - D s) / D s :=
    div_nonneg (mul_nonneg (by linarith) (sub_nonneg.2 (crossGap_mono hnL hnR hp hst ht))) hs.le
  set gap := D s ^ 2 + 16 * ((t : ℝ) - s) - D t ^ 2 with hgap
  have hgap0 : 0 < gap := by linarith
  obtain ⟨N, hN'⟩ := exists_nat_gt (8 * ((t : ℝ) - s) * (D t - D s) / D s / gap)
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hC hgap0.le) hN'
    exact_mod_cast this
  have h := hN N hN0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have e : 8 * ((t : ℝ) - s) * (D t - D s) / (N * D s) = 8 * ((t : ℝ) - s) * (D t - D s) / D s / N := by
    field_simp
  rw [e] at h
  have : 8 * ((t : ℝ) - s) * (D t - D s) / D s / N < gap := by
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hgap0] at hN'
    linarith
  linarith

/-- **The cross-gap growth of DS3** (p. 554): `D_t² ≥ D_0² + 16 t` before the lifetime; in particular `D_t ≥ 4√t` from
a double seed. -/
theorem sq_crossGap_ge {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    crossGap hnL hnR vL vR 0 ^ 2 + 16 * (t : ℝ) ≤ crossGap hnL hnR vL vR t ^ 2 := by
  rcases (crossGap_nonneg hnL hnR hp (lt_of_le_of_lt (by exact_mod_cast zero_le) ht)).lt_or_eq with h0 | h0
  · simpa using sq_crossGap_ge_of_pos hnL hnR hp zero_le ht h0
  -- `D_0 = 0`: `D_s² ≥ 8 s > 0` for `s > 0`, then the positive case on `[s, t]` and `s → 0`
  rw [← h0]
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht0
  · rw [← ht0]
    push_cast
    nlinarith [sq_nonneg (crossGap hnL hnR vL vR 0)]
  set s : ℝ≥0 := min t ⟨ε / 32, by positivity⟩ with hs
  have hs0 : 0 < s := lt_min ht0 (by show (0 : ℝ) < ε / 32; positivity)
  have hst : s ≤ t := min_le_left _ _
  have hsζ : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  have h1 := crossGap_mul_sub_ge hnL hnR hp (zero_le : (0 : ℝ≥0) ≤ s) hsζ
  rw [← h0] at h1
  simp only [NNReal.coe_zero, sub_zero] at h1
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  have hDs : 0 < crossGap hnL hnR vL vR s := by
    nlinarith [crossGap_nonneg hnL hnR hp hsζ]
  have h2 := sq_crossGap_ge_of_pos hnL hnR hp hst ht hDs
  have hsε : (s : ℝ) ≤ ε / 32 := by
    have : s ≤ ⟨ε / 32, by positivity⟩ := min_le_right _ _
    exact_mod_cast this
  nlinarith [sq_nonneg (crossGap hnL hnR vL vR s)]

/-- `D_t ≥ 4√t` before the lifetime, from a double seed at the driver (`D_0 = 0`), or any start. -/
theorem four_mul_sqrt_le_crossGap {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    4 * Real.sqrt t ≤ crossGap hnL hnR vL vR t := by
  have h := sq_crossGap_ge hnL hnR hp ht
  have hn := crossGap_nonneg hnL hnR hp ht
  have h16 : (4 * Real.sqrt t) ^ 2 ≤ crossGap hnL hnR vL vR t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg t)]
    nlinarith [sq_nonneg (crossGap hnL hnR vL vR 0)]
  exact (pow_le_pow_iff_left₀ (by positivity) hn (by norm_num)).1 h16

end CrossGap

end DS3

end Supp12

end InteractingSLE
