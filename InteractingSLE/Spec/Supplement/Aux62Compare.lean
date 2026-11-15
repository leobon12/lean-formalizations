/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux62Setup

/-!
# Aux. lemma 62, probabilistic layer: the Girsanov comparison

Packet PROVE-GB7A2. Source: proof of Aux. lemma 62 (`source/spec/p241-288.md`, pp. 262–263) and Aux. lemma 5
(repulsion). From a deterministic restart time `q` on, the weights `ρ` of the marks are changed to comparison weights
`ρ'` by Girsanov's theorem (cut at the separation time `sepTime` of the monitored marks). Under the changed measure
`Q` the gap `Y = U_k − W` of the repelled mark solves `dY = −√κ dB̃ + β dt` with
`β = 2/Y − ∑ⱼ ρ'ⱼ/(W − Uⱼ) ≥ κ/(2Y)` (`CmpPath.decomp`), so by the localized repulsion criterion
(`measure_hit_le_stop`) it reaches `ε'` with `Q`-probability at most `F(ℓ)/F(ε)`. The energy transfer
(`measureReal_le_of_quadInt_le`) brings this back to the original law on the event of bounded drift energy
(`measure_quad_hit_le`). Letting the separation level `δ → 0`, then `ε → 0` and the transfer parameter `λ → ∞`
shows (`measure_eq_zero_of_cmp`): **almost surely, the repelled mark does not collide with the driver at a time `T`
before which, after `q`, all monitored marks stay away from the driver with bounded drift energy.**

This is the field-free form of the comparison of Aux. lemmas 61–62 ("the original and weighted laws, and hence their
stopped path marginals, are mutually absolutely continuous", p. 263): the energy bound replaces the uniform
integrability of the Cameron–Martin density (the deterministic identity `Aux61Ident.srcDrift_eq_markDrift`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

open Girsanov Sec2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : ℕ}

/-- **The pathwise input of the comparison**: before `ζ`, every reciprocal gap is integrable, the driver solves
`w = √κ b + ∑ⱼ ∫ ρⱼ/(w − uⱼ)`, every mark solves `uⱼ = uⱼ(0) + ∫ 2/(uⱼ − w)`, and at a finite positive lifetime some
mark of nonzero weight collides with the driver (the continuation threshold). -/
structure CmpPath (κ : ℝ) (ρ : Fin m → ℝ) (w b : ℝ≥0 → ℝ) (u : Fin m → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop where
  integrable : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ j,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - u j s.toNNReal)⁻¹) volume 0 t
  w_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
    w t = Real.sqrt κ * b t + ∑ j, ∫ s in (0 : ℝ)..t, ρ j / (w s.toNNReal - u j s.toNNReal)
  u_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ j,
    u j t = u j 0 + ∫ s in (0 : ℝ)..t, 2 / (u j s.toNNReal - w s.toNNReal)
  threshold : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ →
    ∃ j, ρ j ≠ 0 ∧ Tendsto (fun t => w t - u j t) (𝓝[<] T) (𝓝 0)

/-- The drift of the repelled gap `u_k − w` under the comparison weights `ρ'`. -/
def cmpBeta (ρ' : Fin m → ℝ) (k : Fin m) (w : ℝ≥0 → ℝ) (u : Fin m → ℝ≥0 → ℝ) (r : ℝ≥0) : ℝ :=
  2 / (u k r - w r) - ∑ j, ρ' j / (w r - u j r)

variable {κ : ℝ} {ρ ρ' : Fin m → ℝ}

/-- **The decomposition of the repelled gap under the changed measure** (pathwise): if `b̃ = b + ∫ θ` with `θ` the
cut weight-change drift, and the changed marks stay `δ`-away from the driver on `(q, t)`, then
`(u_k − w)(t) = (u_k − w)(q) − √κ (b̃_t − b̃_q) + ∫_q^t β`. -/
theorem CmpPath.decomp (hκ : 0 < κ) {w b bt : ℝ≥0 → ℝ} {u : Fin m → ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞}
    (hp : CmpPath κ ρ w b u ζ₀) {q t : ℝ≥0} (hqt : q ≤ t) (ht : (t : ℝ≥0∞) < ζ₀) (k : Fin m)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ r : ℝ, (q : ℝ) < r → r < t → ∀ j, ρ' j - ρ j ≠ 0 → δ ≤ |w r.toNNReal - u j r.toNNReal|)
    (hbt : bt t - bt q = b t - b q +
      ∫ s in (q : ℝ)..t, shiftIntegrand κ 1 δ (fun j => ρ' j - ρ j) (w s.toNNReal) (fun j => u j s.toNNReal)) :
    IntervalIntegrable (fun r : ℝ => cmpBeta ρ' k w u r.toNNReal) volume q t ∧
    u k t - w t = u k q - w q + (-Real.sqrt κ) * (bt t - bt q) +
      ∫ r in (q : ℝ)..t, cmpBeta ρ' k w u r.toNNReal := by
  have hq : (q : ℝ≥0∞) < ζ₀ := lt_of_le_of_lt (by exact_mod_cast hqt) ht
  set g : Fin m → ℝ → ℝ := fun j r => (w r.toNNReal - u j r.toNNReal)⁻¹ with hg
  have hgt : ∀ j, IntervalIntegrable (g j) volume 0 t := fun j => hp.integrable ht j
  have hgq : ∀ j, IntervalIntegrable (g j) volume 0 q := fun j => hp.integrable hq j
  have hgqt : ∀ j, IntervalIntegrable (g j) volume q t := fun j => (hgq j).symm.trans (hgt j)
  have hsub : ∀ j, (∫ r in (0 : ℝ)..t, g j r) - ∫ r in (0 : ℝ)..q, g j r = ∫ r in (q : ℝ)..t, g j r :=
    fun j => intervalIntegral.integral_interval_sub_left (hgt j) (hgq j)
  have e2 : ∀ j (s : ℝ), 2 / (u j s.toNNReal - w s.toNNReal) = (-2) * g j s := fun j s => by
    simp only [hg]
    rw [div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  have eρ : ∀ (c : Fin m → ℝ) j (s : ℝ), c j / (w s.toNNReal - u j s.toNNReal) = c j * g j s :=
    fun c j s => div_eq_mul_inv _ _
  -- the repelled mark
  have huk : u k t - u k q = (-2) * ∫ r in (q : ℝ)..t, g k r := by
    rw [hp.u_eq ht k, hp.u_eq hq k]
    simp only [e2, intervalIntegral.integral_const_mul]
    rw [← hsub k]
    ring
  -- the driver
  have hw : w t - w q = Real.sqrt κ * (b t - b q) + ∑ j, ρ j * ∫ r in (q : ℝ)..t, g j r := by
    rw [hp.w_eq ht, hp.w_eq hq]
    simp only [eρ ρ, intervalIntegral.integral_const_mul, ← hsub, mul_sub, Finset.sum_sub_distrib]
    ring
  -- the drift of the tilted Brownian motion
  have hF : ∫ s in (q : ℝ)..t, shiftIntegrand κ 1 δ (fun j => ρ' j - ρ j) (w s.toNNReal)
      (fun j => u j s.toNNReal) = -(1 / Real.sqrt κ) * ∑ j, (ρ' j - ρ j) * ∫ r in (q : ℝ)..t, g j r := by
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc (q : ℝ) t →
        shiftIntegrand κ 1 δ (fun j => ρ' j - ρ j) (w s.toNNReal) (fun j => u j s.toNNReal) =
          -(1 / Real.sqrt κ) * ∑ j, (ρ' j - ρ j) * g j s := by
      filter_upwards [ae_ne_real (t : ℝ)] with s hst hs
      rw [uIoc_of_le (by exact_mod_cast hqt)] at hs
      simp only [shiftIntegrand, addedDriftCut]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : ρ' j - ρ j = 0
      · simp only [hj, zero_mul]
      · rw [recipCut_of_le hδ (hgap s hs.1 (lt_of_le_of_ne hs.2 hst) j hj)]
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun j _ => (hgqt j).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  -- the drift `β` of the gap
  have hβ : (fun r : ℝ => cmpBeta ρ' k w u r.toNNReal) =
      fun r => (-2) * g k r - ∑ j, ρ' j * g j r := by
    funext r
    simp only [cmpBeta]
    rw [e2 k r]
    simp only [eρ ρ']
  have hsumi : IntervalIntegrable (fun r => ∑ j, ρ' j * g j r) volume q t := by
    have e : (fun r => ∑ j, ρ' j * g j r) = ∑ j ∈ Finset.univ, (fun r => ρ' j * g j r) := by
      funext r
      simp only [Finset.sum_apply]
    rw [e]
    exact IntervalIntegrable.sum Finset.univ (fun j _ => (hgqt j).const_mul (ρ' j))
  have hβi : IntervalIntegrable (fun r => (-2) * g k r - ∑ j, ρ' j * g j r) volume q t :=
    ((hgqt k).const_mul _).sub hsumi
  refine ⟨by rw [hβ]; exact hβi, ?_⟩
  rw [hβ, intervalIntegral.integral_sub ((hgqt k).const_mul _) hsumi, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun j _ => (hgqt j).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [hF] at hbt
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hS : ∑ j, (ρ' j - ρ j) * ∫ r in (q : ℝ)..t, g j r =
      ∑ j, ρ' j * (∫ r in (q : ℝ)..t, g j r) - ∑ j, ρ j * ∫ r in (q : ℝ)..t, g j r := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hS] at hbt
  have hbt' : Real.sqrt κ * (bt t - bt q) = Real.sqrt κ * (b t - b q) -
      (∑ j, ρ' j * (∫ r in (q : ℝ)..t, g j r) - ∑ j, ρ j * ∫ r in (q : ℝ)..t, g j r) := by
    have h1 : Real.sqrt κ * (1 / Real.sqrt κ) = 1 := mul_one_div_cancel hs
    rw [hbt]
    linear_combination (-(∑ j, ρ' j * (∫ r in (q : ℝ)..t, g j r) - ∑ j, ρ j * ∫ r in (q : ℝ)..t, g j r)) * h1
  linear_combination huk - hw + hbt'

/-! ### The repulsion path under the changed measure -/

/-- The gap of the repelled mark, killed at the lifetime. -/
def killedGap (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (U : Fin m → ℝ≥0 → Ω → ℝ) (k : Fin m) (t : ℝ≥0) (ω : Ω) :
    ℝ := killed ζ (U k) t ω - killed ζ W t ω

/-- The domination constant of the gap drift before the separation time. -/
def cmpK (ρ' : Fin m → ℝ) (δ : ℝ) : ℝ := (2 + ∑ j, |ρ' j|) / δ

/-- The stopping time of the repulsion argument: the separation time, floored by `q`. -/
def cmpStop (ρ ρ' : Fin m → ℝ) (k : Fin m) (q : ℝ≥0) (δ : ℝ) (W : ℝ≥0 → Ω → ℝ) (U : Fin m → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (T₀ : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  max q (sepTime ρ ρ' k q δ W U ζ T₀ ω).toNNReal

variable {𝓖 : Filtration ℝ≥0 mΩ} {P' : Measure Ω} {B W : ℝ≥0 → Ω → ℝ} {U : Fin m → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {k : Fin m} {q T₀ : ℝ≥0} {δ : ℝ}

/-- The separation time comes strictly before the lifetime, while alive at `q` (continuation threshold). -/
theorem sepTime_lt_lifetime (hδ : 0 < δ) {ω : Ω}
    (hp : CmpPath κ ρ (W · ω) (B · ω) (fun j t => U j t ω) (ζ ω)) (hqζ : (q : ℝ≥0∞) < ζ ω) :
    sepTime ρ ρ' k q δ W U ζ T₀ ω < ζ ω := by
  by_cases htop : ζ ω = ⊤
  · rw [htop]
    exact (sepTime_le_horizon ω).trans_lt ENNReal.coe_lt_top
  · set Tζ := (ζ ω).toNNReal with hTζ
    have hcoe : (Tζ : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal htop
    have hqT' : q < Tζ := by
      rw [← ENNReal.coe_lt_coe, hcoe]
      exact hqζ
    obtain ⟨j, hj, hlim⟩ := hp.threshold Tζ (lt_of_le_of_lt bot_le hqT') hcoe
    rw [← hcoe]
    exact sepTime_lt_of_tendsto hδ hqT' hcoe.le (Or.inl hj) hlim

theorem coe_cmpStop (hqT : q ≤ T₀) {ω : Ω} (hqζ : (q : ℝ≥0∞) < ζ ω) :
    ((cmpStop ρ ρ' k q δ W U ζ T₀ ω : ℝ≥0) : ℝ≥0∞) = sepTime ρ ρ' k q δ W U ζ T₀ ω := by
  have h1 := le_sepTime (ρ := ρ) (ρ' := ρ') (k := k) (δ := δ) (W := W) (U := U) hqT hqζ
  have h2 := sepTime_ne_top (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (δ := δ) (W := W) (U := U) (ζ := ζ)
    (T₀ := T₀) ω
  have hq : q ≤ (sepTime ρ ρ' k q δ W U ζ T₀ ω).toNNReal := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h2]
    exact h1
  rw [cmpStop, max_eq_right hq, ENNReal.coe_toNNReal h2]

/-- **The gap of the repelled mark is a repulsion path under the changed measure** (pathwise, while alive at `q`). -/
theorem isRepulsionPath_cmp (hκ : 0 < κ) (hδ : 0 < δ) (hqT : q ≤ T₀) (hW : AdaptedBefore 𝓖 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j)) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j ω, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω}) {ω : Ω}
    (hp : CmpPath κ ρ (W · ω) (B · ω) (fun j t => U j t ω) (ζ ω))
    (hd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ j, IsMon ρ ρ' k j → W t ω ≠ U j t ω) →
      0 < U k t ω - W t ω ∧ κ / (2 * (U k t ω - W t ω)) ≤ cmpBeta ρ' k (W · ω) (fun j t => U j t ω) t)
    (hBc : Continuous (B · ω)) (hqζ : (q : ℝ≥0∞) < ζ ω) (a : ℝ) :
    Sec4.Repulsion.IsRepulsionPath (-Real.sqrt κ) a 0 q (cmpStop ρ ρ' k q δ W U ζ T₀ ω)
      (killedGap ζ W U k · ω)
      (girsanovProcess B (cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U) · ω)
      (cmpBeta ρ' k (W · ω) (fun j t => U j t ω)) (fun r => cmpK ρ' δ * r) := by
  set ρs := cmpStop ρ ρ' k q δ W U ζ T₀ ω with hρs
  have hτ := measurableSet_sepTime_le (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (T₀ := T₀) hδ.le hW hU hWc hUc
  have hτζ := sepTime_le_lifetime (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (W := W) (U := U) (ζ := ζ)
    (T₀ := T₀) hδ.le
  have hθ := isStronglyProgressive_cmpDrift (κ := κ) (σ := fun j => ρ' j - ρ j) (q := q) hδ hW hU hτ
  have hθb := abs_cmpDrift_le (κ := κ) (σ := fun j => ρ' j - ρ j) (τ := (sepTime ρ ρ' k q δ W U ζ T₀)) (ζ := ζ)
    (q := q) (W := W)
    (U := U) hδ
  have hρτ : (ρs : ℝ≥0∞) = sepTime ρ ρ' k q δ W U ζ T₀ ω := coe_cmpStop hqT hqζ
  have hτζ' : sepTime ρ ρ' k q δ W U ζ T₀ ω < ζ ω := sepTime_lt_lifetime hδ hp hqζ
  have hqρ : q ≤ ρs := le_max_left _ _
  -- every time of `[q, ρ]` is alive
  have halive : ∀ r : ℝ≥0, r ≤ ρs → (r : ℝ≥0∞) < ζ ω := fun r hr =>
    lt_of_le_of_lt (by rw [← hρτ]; exact_mod_cast hr) hτζ'
  have hkill : ∀ r : ℝ≥0, r ≤ ρs → killedGap ζ W U k r ω = U k r ω - W r ω := fun r hr => by
    rw [killedGap, killed_of_lt (halive r hr), killed_of_lt (halive r hr)]
  -- before `ρ`, the monitored gaps exceed `δ`
  have hsep : ∀ r : ℝ, (q : ℝ) ≤ r → r < ρs → (r.toNNReal : ℝ≥0∞) < ζ ω ∧
      ∀ j, IsMon ρ ρ' k j → δ < |W r.toNNReal ω - U j r.toNNReal ω| := fun r hqr hrρ => by
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg q).trans hqr
    refine lt_of_lt_sepTime (T₀ := T₀) (q := q) hδ.le ?_ ?_
    · rw [← hρτ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
      exact hrρ
    · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
      exact hqr
  have hmon : ∀ j, ρ' j - ρ j ≠ 0 → IsMon ρ ρ' k j := fun j hj => by
    by_contra h
    simp only [IsMon, not_or, not_not] at h
    exact hj (by rw [h.1, h.2.1, sub_zero])
  refine ⟨?_, ?_, ?_, fun u hu _ => ?_⟩
  · refine ((hUc k ω).sub (hWc ω)).mono (fun r hr => halive r hr.2) |>.congr fun r hr => ?_
    exact hkill r hr.2
  · exact (hBc.add (continuous_drift hθ hθb ω)).continuousOn
  · exact (continuous_const.mul NNReal.continuous_coe).continuousOn
  -- the decomposition on `[q, u]`
  have huζ := halive u hu.2
  have hbt : girsanovProcess B (cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U) u ω -
      girsanovProcess B (cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U) q ω = B u ω - B q ω +
      ∫ s in (q : ℝ)..u, shiftIntegrand κ 1 δ (fun j => ρ' j - ρ j) (W s.toNNReal ω)
        (fun j => U j s.toNNReal ω) := by
    rw [girsanovProcess, girsanovProcess, ← drift_sub_drift_cmpDrift hδ hW hU hτ (hτζ ω) (hWc ω)
      (fun j => hUc j ω) hu.1 (by rw [← hρτ]; exact_mod_cast hu.2)]
    ring
  have hgap : ∀ r : ℝ, (q : ℝ) < r → r < u → ∀ j, ρ' j - ρ j ≠ 0 →
      δ ≤ |W r.toNNReal ω - U j r.toNNReal ω| := fun r hqr hru j hj =>
    ((hsep r hqr.le (lt_of_lt_of_le hru (by exact_mod_cast hu.2))).2 j (hmon j hj)).le
  obtain ⟨hint, hdec⟩ := hp.decomp (bt := fun t => girsanovProcess B
    (cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U) t ω) hκ hu.1 huζ k hδ hgap hbt
  refine ⟨hint, ?_, ?_, ?_⟩
  · show killedGap ζ W U k u ω = killedGap ζ W U k q ω + _ + _
    rw [hkill u hu.2, hkill q hqρ]
    exact hdec
  · -- domination
    have hab : (q : ℝ) ≤ u := by exact_mod_cast hu.1
    calc (∫ r in (q : ℝ)..u, |cmpBeta ρ' k (W · ω) (fun j t => U j t ω) r.toNNReal|)
        ≤ ∫ r in (q : ℝ)..u, cmpK ρ' δ := by
          refine intervalIntegral.integral_mono_ae_restrict hab hint.abs intervalIntegrable_const ?_
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
          filter_upwards [ae_ne_real (u : ℝ)] with r hru hr
          have hs := hsep r hr.1 (lt_of_lt_of_le (lt_of_le_of_ne hr.2 hru) (by exact_mod_cast hu.2))
          have hk := hs.2 k (Or.inr (Or.inr rfl))
          have hkpos : 0 < |W r.toNNReal ω - U k r.toNNReal ω| := hδ.trans hk
          simp only [cmpBeta, cmpK]
          refine (abs_sub _ _).trans ?_
          rw [add_div]
          refine add_le_add ?_ ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
          · rw [abs_div, abs_two, ← abs_neg, neg_sub]
            exact div_le_div_of_nonneg_left zero_le_two hδ hk.le
          · rw [Finset.sum_div]
            refine Finset.sum_le_sum fun j _ => ?_
            by_cases hj : ρ' j = 0
            · simp [hj]
            · have hj' := hs.2 j (Or.inr (Or.inl hj))
              rw [abs_div]
              exact div_le_div_of_nonneg_left (abs_nonneg _) hδ hj'.le
      _ = cmpK ρ' δ * u - cmpK ρ' δ * q := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  · -- the drift inequality
    filter_upwards [ae_ne_real (u : ℝ)] with r hru hr
    have hs := hsep r hr.1 (lt_of_lt_of_le (lt_of_le_of_ne hr.2 hru) (by exact_mod_cast hu.2))
    have hne : ∀ j, IsMon ρ ρ' k j → W r.toNNReal ω ≠ U j r.toNNReal ω := fun j hj h => by
      have := hs.2 j hj
      rw [h, sub_self, abs_zero] at this
      exact absurd this (not_lt.2 hδ.le)
    obtain ⟨-, hdr⟩ := hd r.toNNReal hs.1 hne
    have hr0 : r.toNNReal ≤ ρs := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg q).trans hr.1)]
      exact hr.2.trans (by exact_mod_cast hu.2)
    rw [hkill _ hr0, neg_sq, Real.sq_sqrt hκ.le, sub_zero]
    exact hdr

/-! ### The bound for a fixed separation level -/

/-- The start event of the repulsion argument: alive at `q` with `ℓ ≤ Y_q < a`. -/
def cmpStart (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (U : Fin m → ℝ≥0 → Ω → ℝ) (k : Fin m) (q : ℝ≥0) (ℓ a : ℝ) :
    Set Ω :=
  {ω | (q : ℝ≥0∞) < ζ ω ∧ ℓ ≤ killedGap ζ W U k q ω ∧ killedGap ζ W U k q ω < a}

/-- The hitting event of the repulsion argument: started, and `Y ≤ ε'` before the stopping time while `Y < a`. -/
def cmpHit (ρ ρ' : Fin m → ℝ) (k : Fin m) (q : ℝ≥0) (δ : ℝ) (W : ℝ≥0 → Ω → ℝ) (U : Fin m → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (T₀ : ℝ≥0) (ℓ a ε' : ℝ) : Set Ω :=
  {ω | ω ∈ cmpStart ζ W U k q ℓ a ∧
    (∀ r ∈ Icc q (cmpStop ρ ρ' k q δ W U ζ T₀ ω), cmpK ρ' δ * (r : ℝ) - cmpK ρ' δ * (q : ℝ) <
      cmpK ρ' δ * (T₀ : ℝ) + 1) ∧
    ∃ u ∈ Icc q (cmpStop ρ ρ' k q δ W U ζ T₀ ω), killedGap ζ W U k u ω ≤ ε' ∧
      ∀ r ∈ Icc q u, killedGap ζ W U k r ω < a}

theorem cmpK_pos (hδ : 0 < δ) : 0 < cmpK ρ' δ :=
  div_pos (add_pos_of_pos_of_nonneg two_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _)) hδ

/-- **The bound for a fixed separation level**: on the event of drift energy `≤ C`, the original probability that
the repelled gap falls from `[ℓ, a)` at `q` to `ε'` before the separation time is at most
`λ F(ℓ)/(2 F(ε)) + e^C/(2λ)`. -/
theorem measure_quad_hit_le [IsProbabilityMeasure P'] (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓖 B P')
    (hW : AdaptedBefore 𝓖 ζ W) (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j))
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j ω, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hpath : ∀ᵐ ω ∂P', CmpPath κ ρ (W · ω) (B · ω) (fun j t => U j t ω) (ζ ω))
    (hdrift : ∀ᵐ ω ∂P', ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ j, IsMon ρ ρ' k j → W t ω ≠ U j t ω) →
      0 < U k t ω - W t ω ∧ κ / (2 * (U k t ω - W t ω)) ≤ cmpBeta ρ' k (W · ω) (fun j t => U j t ω) t)
    (hδ : 0 < δ) (hqT : q ≤ T₀) {ℓ a ε ε' : ℝ} (hε : 0 < ε) (hε' : ε' < ε) (hεℓ : ε < ℓ) (hℓa : ℓ < a)
    {C lam : ℝ} (hlam : 0 < lam) :
    P' ({ω | quadInt (cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U) (T₀ + 1) ω
        ≤ C} ∩ cmpHit ρ ρ' k q δ W U ζ T₀ ℓ a ε') ≤
      ENNReal.ofReal (lam / 2 * (Sec4.Repulsion.repulsionInt 0 a ℓ / Sec4.Repulsion.repulsionInt 0 a ε) +
        Real.exp C / (2 * lam)) := by
  have hBP := isFilteredPreBrownian_of_isFilteredBrownianReal hB
  have hτ := measurableSet_sepTime_le (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (T₀ := T₀) hδ.le hW hU hWc hUc
  have hτζ := sepTime_le_lifetime (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (W := W) (U := U) (ζ := ζ)
    (T₀ := T₀) hδ.le
  have hτT := sepTime_le_horizon (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (δ := δ) (W := W) (U := U) (ζ := ζ)
    (T₀ := T₀)
  have hcont : ∀ᵐ ω ∂P', ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω} :=
    ae_of_all _ fun ω => ⟨hWc ω, fun j => hUc j ω⟩
  set θ := cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U with hθdef
  have hθ : IsStronglyProgressive 𝓖 θ := isStronglyProgressive_cmpDrift hδ hW hU hτ
  have hθb : ∀ t ω, |θ t ω| ≤ cmpBound κ δ (fun j => ρ' j - ρ j) := abs_cmpDrift_le hδ
  have hθreg : IsRiemannRegular P' θ := isRiemannRegular_cmpDrift hδ hτζ hcont
  have hθT : ∀ t ω, T₀ + 1 ≤ t → θ t ω = 0 := cmpDrift_eq_zero_of_horizon_le hτT
  set Q := girsanovMeasure P' 𝓖 B θ (T₀ + 1) with hQdef
  have hQeq : MathFin.IsEquivProbMeasure P' Q :=
    isEquivProbMeasure_girsanovMeasure (B := B) hθ.stronglyAdapted hθb hθreg _
  have hQprob : IsProbabilityMeasure Q :=
    isProbabilityMeasure_girsanovMeasure (B := B) hθ.stronglyAdapted hθb hθreg _
  have hBt : IsFilteredBrownianReal 𝓖 (girsanovProcess B θ) Q :=
    isFilteredBrownianReal_girsanov hB hθ hθb hθreg hθT
  have hBtP := isFilteredPreBrownian_of_isFilteredBrownianReal hBt
  -- the repulsion estimate under `Q`
  have hY : ∀ u, Measurable[𝓖 u] (killedGap ζ W U k u) := fun u =>
    (measurable_killed (hU k) u).sub (measurable_killed hW u)
  have hAs : MeasurableSet[𝓖 q] (cmpStart ζ W U k q ℓ a) := by
    have hlife : MeasurableSet[𝓖 q] {ω | (q : ℝ≥0∞) < ζ ω} := by
      simpa using hW q univ MeasurableSet.univ
    exact hlife.inter ((measurableSet_le measurable_const (hY q)).inter
      (measurableSet_lt (hY q) measurable_const))
  have hρ : IsStoppingTime 𝓖 fun ω => ((cmpStop ρ ρ' k q δ W U ζ T₀ ω : ℝ≥0) : WithTop ℝ≥0) := by
    intro i
    have e : {ω | ((cmpStop ρ ρ' k q δ W U ζ T₀ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (i : WithTop ℝ≥0)} =
        {_ω | q ≤ i} ∩ {ω | sepTime ρ ρ' k q δ W U ζ T₀ ω ≤ i} := by
      ext ω
      have hx : ∀ x : ℝ≥0∞, x ≠ ⊤ → (x.toNNReal ≤ i ↔ x ≤ i) := fun x hx => by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hx]
      simp only [Set.mem_ofPred_eq, mem_inter_iff, WithTop.coe_le_coe, cmpStop, max_le_iff,
        hx _ (sepTime_ne_top ω)]
    rw [e]
    refine MeasurableSet.inter ?_ (hτ i)
    by_cases h : q ≤ i
    · simp only [h, ofPred_true, MeasurableSet.univ]
    · simp only [h, ofPred_false, MeasurableSet.empty]
  have hρt : ∀ ω, cmpStop ρ ρ' k q δ W U ζ T₀ ω ≤ T₀ := fun ω => by
    refine max_le hqT ?_
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (sepTime_ne_top ω)]
    exact hτT ω
  have hpathQ : ∀ᵐ ω ∂Q, ω ∈ cmpStart ζ W U k q ℓ a →
      Sec4.Repulsion.IsRepulsionPath (-Real.sqrt κ) a 0 q (cmpStop ρ ρ' k q δ W U ζ T₀ ω)
        (killedGap ζ W U k · ω) (girsanovProcess B θ · ω)
        ((fun r ω => cmpBeta ρ' k (W · ω) (fun j t => U j t ω) r) · ω)
        ((fun (r : ℝ≥0) (_ : Ω) => cmpK ρ' δ * (r : ℝ)) · ω) := by
    refine hQeq.ac.ae_le ?_
    filter_upwards [hpath, hdrift, hB.1.cont] with ω hp hd hBc hω
    exact isRepulsionPath_cmp hκ hδ hqT hW hU hWc hUc hp hd hBc hω.1 a
  have hσ : -Real.sqrt κ ≠ 0 := neg_ne_zero.2 (Real.sqrt_pos.2 hκ).ne'
  have hN : (0 : ℝ) ≤ cmpK ρ' δ * (T₀ : ℝ) + 1 :=
    add_nonneg (mul_nonneg (cmpK_pos hδ).le (NNReal.coe_nonneg _)) zero_le_one
  have hrep := measure_hit_le_stop (P := Q) (B := girsanovProcess B θ) (Y := killedGap ζ W U k)
    (ψ := fun (r : ℝ≥0) (_ : Ω) => cmpK ρ' δ * (r : ℝ)) (A := cmpStart ζ W U k q ℓ a)
    (ρ := cmpStop ρ ρ' k q δ W U ζ T₀) (β := fun r ω => cmpBeta ρ' k (W · ω) (fun j t => U j t ω) r)
    (σ := -Real.sqrt κ) (C := 0) (𝓕 := 𝓖) hBtP hσ le_rfl hε hε' hεℓ hℓa hN hqT hY
    (fun _ => measurable_const) hAs hρ (fun ω => le_max_left _ _) hρt (fun ω hω => hω.2) hpathQ
  rw [mul_zero, zero_div] at hrep
  -- the energy transfer
  set H := cmpHit ρ ρ' k q δ W U ζ T₀ ℓ a ε' with hHdef
  have hHrep : Q H ≤ ENNReal.ofReal (Sec4.Repulsion.repulsionInt 0 a ℓ / Sec4.Repulsion.repulsionInt 0 a ε) :=
    hrep
  have hqm : Measurable (quadInt θ (T₀ + 1)) :=
    ((stronglyMeasurable_integral_comp hθ (measurable_id.pow_const 2) (T₀ + 1)).measurable).mono
      (𝓖.le _) le_rfl
  set D := {ω | quadInt θ (T₀ + 1) ω ≤ C} ∩ toMeasurable Q H with hDdef
  have hDm : MeasurableSet D := (measurableSet_le hqm measurable_const).inter (measurableSet_toMeasurable Q H)
  have hkey := measureReal_le_of_quadInt_le hBP hθ hθb hθreg (T₀ + 1) hDm (fun ω hω => hω.1) hlam
  have hFℓ : 0 ≤ Sec4.Repulsion.repulsionInt 0 a ℓ :=
    Sec4.Repulsion.repulsionInt_nonneg (hε.trans hεℓ) hℓa.le
  have hFε : 0 ≤ Sec4.Repulsion.repulsionInt 0 a ε :=
    Sec4.Repulsion.repulsionInt_nonneg hε (hεℓ.trans hℓa).le
  have hQD : Q.real D ≤ Sec4.Repulsion.repulsionInt 0 a ℓ / Sec4.Repulsion.repulsionInt 0 a ε := by
    refine (measureReal_mono inter_subset_right).trans ?_
    rw [measureReal_def, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hFℓ hFε) hHrep
  calc P' ({ω | quadInt θ (T₀ + 1) ω ≤ C} ∩ H) ≤ P' D :=
        measure_mono (inter_subset_inter_right _ (subset_toMeasurable Q H))
    _ = ENNReal.ofReal (P'.real D) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal (hkey.trans ?_)
        gcongr

/-! ### Letting the separation level tend to `0` -/

/-- The pathwise event of the comparison for fixed bounds: after `q` and before a time `T ≤ T₀ ∧ ζ`, the monitored
marks stay away from the driver, the drift energy is `≤ C` and the repelled gap stays `< a`; the gap is `≥ ℓ` at `q`
and tends to `0` at `T`. -/
def cmpSet (ρ ρ' : Fin m → ℝ) (k : Fin m) (q : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (U : Fin m → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (T₀ : ℝ≥0) (ℓ a C : ℝ) : Set Ω :=
  {ω | ∃ T : ℝ≥0, q < T ∧ T ≤ T₀ ∧ (T : ℝ≥0∞) ≤ ζ ω ∧
    (∀ t : ℝ≥0, q ≤ t → t < T → (∀ j, IsMon ρ ρ' k j → W t ω ≠ U j t ω) ∧
      (∫ s in (q : ℝ)..t, (∑ j, (ρ' j - ρ j) / (W s.toNNReal ω - U j s.toNNReal ω)) ^ 2) ≤ C ∧
      U k t ω - W t ω < a) ∧
    ℓ ≤ U k q ω - W q ω ∧ Tendsto (fun t => U k t ω - W t ω) (𝓝[<] T) (𝓝 0)}

/-- The event of the fixed-level bound. -/
def cmpGood (κ : ℝ) (ρ ρ' : Fin m → ℝ) (k : Fin m) (q : ℝ≥0) (δ : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T₀ : ℝ≥0) (ℓ a ε' C : ℝ) : Set Ω :=
  {ω | quadInt (cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U) (T₀ + 1) ω ≤ C} ∩
    cmpHit ρ ρ' k q δ W U ζ T₀ ℓ a ε'

/-- `ζ`-alive times where the monitored gaps exceed `δ` see the uncut drift. -/
theorem shiftIntegrand_sq_eq (hκ : 0 < κ) (hδ : 0 < δ) {w : ℝ} {u : Fin m → ℝ}
    (hg : ∀ j, ρ' j - ρ j ≠ 0 → δ ≤ |w - u j|) :
    shiftIntegrand κ 1 δ (fun j => ρ' j - ρ j) w u ^ 2 = (∑ j, (ρ' j - ρ j) / (w - u j)) ^ 2 / κ := by
  have e : shiftIntegrand κ 1 δ (fun j => ρ' j - ρ j) w u = -(1 / Real.sqrt κ) * ∑ j, (ρ' j - ρ j) / (w - u j) := by
    simp only [shiftIntegrand, addedDriftCut]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ρ' j - ρ j = 0
    · simp only [hj, zero_mul, zero_div]
    · rw [recipCut_of_le hδ (hg j hj), div_eq_mul_inv]
  rw [e, mul_pow, neg_sq, div_pow, one_pow, Real.sq_sqrt hκ.le]
  ring

/-- **Almost every separation level detects the hit**: on the pathwise event, for all small `δ = 1/(N+1)`, the
drift energy is `≤ C/κ` and the repelled gap reaches `ε'` before the separation time. -/
theorem eventually_mem_cmpGood (hκ : 0 < κ) (hW : AdaptedBefore 𝓖 ζ W) (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j))
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j ω, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hqT : q ≤ T₀) {ℓ a ε' C : ℝ}
    (hε' : 0 < ε') {ω : Ω} (hω : ω ∈ cmpSet ρ ρ' k q W U ζ T₀ ℓ a C) :
    ∀ᶠ N : ℕ in atTop, ω ∈ cmpGood κ ρ ρ' k q (1 / ((N : ℝ) + 1)) W U ζ T₀ ℓ a ε' (C / κ) := by
  obtain ⟨T, hqT', hTT₀, hTζ, hall, hℓY, hlim⟩ := hω
  have hqζ : (q : ℝ≥0∞) < ζ ω := (show (q : ℝ≥0∞) < T by exact_mod_cast hqT').trans_le hTζ
  -- a time `u ∈ (q, T)` with `Y_u < ε'`
  have hNe : (𝓝[<] T).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' ⟨q, hqT'⟩]
    exact Set.mem_Iic.2 le_rfl
  obtain ⟨u, hu1, hu2, hu3⟩ := ((hlim.eventually (gt_mem_nhds hε')).and
    ((Filter.eventually_of_mem (Ioo_mem_nhdsLT hqT') fun t ht => ht.1).and self_mem_nhdsWithin)).exists
  have huT : u < T := hu3
  have hlive : ∀ t : ℝ≥0, t ≤ u → (t : ℝ≥0∞) < ζ ω := fun t ht =>
    lt_of_lt_of_le (by exact_mod_cast ht.trans_lt huT) hTζ
  -- a positive lower bound of the monitored gaps on `[q, u]`
  have hmj : ∀ j, ∃ mj : ℝ, 0 < mj ∧ ∀ t ∈ Icc q u, IsMon ρ ρ' k j → mj ≤ |W t ω - U j t ω| := by
    intro j
    by_cases hj : IsMon ρ ρ' k j
    · have hc : ContinuousOn (fun t => |W t ω - U j t ω|) (Icc q u) :=
        (continuous_abs.comp_continuousOn ((hWc ω).sub (hUc j ω))).mono fun t ht => hlive t ht.2
      obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hu2.le) hc
      refine ⟨|W t₀ ω - U j t₀ ω|, abs_pos.2 (sub_ne_zero.2 ((hall t₀ ht₀.1 (ht₀.2.trans_lt huT)).1 j hj)),
        fun t ht _ => hmin ht⟩
    · exact ⟨1, one_pos, fun t _ h => absurd h hj⟩
  choose mj hmj0 hmj using hmj
  set m₀ := Finset.univ.inf' ⟨k, Finset.mem_univ k⟩ mj with hm₀
  have hm₀pos : 0 < m₀ := (Finset.lt_inf'_iff _).2 fun j _ => hmj0 j
  have hm₀le : ∀ j, m₀ ≤ mj j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hm₀pos
  filter_upwards [eventually_ge_atTop n] with N hN
  set δ : ℝ := 1 / ((N : ℝ) + 1) with hδdef
  have hδ : 0 < δ := Nat.one_div_pos_of_nat
  have hδm : δ < m₀ := lt_of_le_of_lt (Nat.one_div_le_one_div hN) hn
  -- `u` comes before the separation time, which comes before `T`
  have huτ : (u : ℝ≥0∞) ≤ sepTime ρ ρ' k q δ W U ζ T₀ ω := by
    refine le_min (le_iInf₂ fun t ht => ?_) (by exact_mod_cast huT.le.trans hTT₀)
    by_contra htu
    rw [not_le] at htu
    have htu' : t < u := by exact_mod_cast htu
    obtain ⟨j, hj⟩ := ht.2
    rw [killedF, killed_of_lt (hlive t htu'.le), monGap] at hj
    by_cases htq : q ≤ t
    · split_ifs at hj with hmon
      · have := (hmj j t ⟨htq, htu'.le⟩ hmon)
        linarith [le_max_left |W t ω - U j t ω| (δ + ((q : ℝ) - t)), hm₀le j]
      · linarith [le_max_left (δ + 1) (δ + ((q : ℝ) - t))]
    · rw [not_le] at htq
      have : (t : ℝ) < q := htq
      have h2 := (le_max_right _ _).trans hj
      linarith
  have hτT : sepTime ρ ρ' k q δ W U ζ T₀ ω < T := by
    refine sepTime_lt_of_tendsto hδ hqT' hTζ (j := k) (Or.inr (Or.inr rfl)) ?_
    have := hlim.neg
    rw [neg_zero] at this
    exact this.congr fun t => by ring
  have hqτ : (q : ℝ≥0∞) ≤ sepTime ρ ρ' k q δ W U ζ T₀ ω := le_sepTime hqT hqζ
  have hτtop := sepTime_ne_top (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (δ := δ) (W := W) (U := U) (ζ := ζ)
    (T₀ := T₀) ω
  have hstopT : cmpStop ρ ρ' k q δ W U ζ T₀ ω ≤ T₀ := by
    refine max_le hqT ?_
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hτtop]
    exact sepTime_le_horizon ω
  have hustop : u ≤ cmpStop ρ ρ' k q δ W U ζ T₀ ω := by
    refine le_trans ?_ (le_max_right _ _)
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hτtop]
    exact huτ
  have hkill : ∀ t : ℝ≥0, t ≤ u → killedGap ζ W U k t ω = U k t ω - W t ω := fun t ht => by
    rw [killedGap, killed_of_lt (hlive t ht), killed_of_lt (hlive t ht)]
  refine ⟨?_, ⟨hqζ, ?_, ?_⟩, ?_, u, ⟨hu2.le, hustop⟩, ?_, ?_⟩
  · -- the energy
    have hτζ := sepTime_le_lifetime (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (W := W) (U := U) (ζ := ζ)
      (T₀ := T₀) hδ.le
    have hτm := measurableSet_sepTime_le (𝓖 := 𝓖) (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (T₀ := T₀) hδ.le
      hW hU hWc hUc
    show quadInt _ (T₀ + 1) ω ≤ C / κ
    rw [quadInt_cmpDrift_eq hδ hW hU hτm sepTime_le_horizon (hτζ ω) (hWc ω) (fun j => hUc j ω) hqτ]
    set τr := (sepTime ρ ρ' k q δ W U ζ T₀ ω).toReal with hτr
    have hqτr : (q : ℝ) ≤ τr := by
      rw [hτr, ← ENNReal.coe_toReal]
      exact ENNReal.toReal_mono hτtop hqτ
    have hτrT : τr < T := by
      rw [hτr, ← ENNReal.coe_toReal]
      exact (ENNReal.toReal_lt_toReal hτtop ENNReal.coe_ne_top).2 hτT
    have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc (q : ℝ) τr →
        shiftIntegrand κ 1 δ (fun j => ρ' j - ρ j) (W s.toNNReal ω) (fun j => U j s.toNNReal ω) ^ 2 =
          (∑ j, (ρ' j - ρ j) / (W s.toNNReal ω - U j s.toNNReal ω)) ^ 2 / κ := by
      filter_upwards [ae_ne_real τr] with s hsτ hs
      rw [uIoc_of_le hqτr] at hs
      have hs0 : 0 ≤ s := (NNReal.coe_nonneg q).trans hs.1.le
      have hlt : (s.toNNReal : ℝ≥0∞) < sepTime ρ ρ' k q δ W U ζ T₀ ω :=
        (toNNReal_lt_iff hτtop hs0).2 (lt_of_le_of_ne hs.2 hsτ)
      have hqs : q ≤ s.toNNReal := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]
        exact hs.1.le
      have hsep := (lt_of_lt_sepTime hδ.le hlt hqs).2
      refine shiftIntegrand_sq_eq hκ hδ fun j hj => (hsep j ?_).le
      by_contra h
      simp only [IsMon, not_or, not_not] at h
      exact hj (by rw [h.1, h.2.1, sub_zero])
    rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_div]
    have hτn : q ≤ τr.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg q).trans hqτr)]
      exact hqτr
    have hτn' : τr.toNNReal < T := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ((NNReal.coe_nonneg q).trans hqτr)]
      exact hτrT
    have hE := (hall τr.toNNReal hτn hτn').2.1
    rw [Real.coe_toNNReal _ ((NNReal.coe_nonneg q).trans hqτr)] at hE
    exact div_le_div_of_nonneg_right hE hκ.le
  · rw [hkill q hu2.le]
    exact hℓY
  · rw [hkill q hu2.le]
    exact (hall q le_rfl hqT').2.2
  · intro r hr
    have hK := (cmpK_pos (ρ' := ρ') hδ).le
    have h1 : (r : ℝ) ≤ T₀ := by exact_mod_cast hr.2.trans hstopT
    nlinarith [NNReal.coe_nonneg q]
  · rw [hkill u le_rfl]
    exact hu1.le
  · intro r hr
    rw [hkill r hr.2]
    exact (hall r hr.1 (hr.2.trans_lt huT)).2.2

/-- **The comparison for fixed bounds**: the pathwise event `cmpSet` is null. -/
theorem measure_cmpSet_eq_zero [IsProbabilityMeasure P'] (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓖 B P')
    (hW : AdaptedBefore 𝓖 ζ W) (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j))
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j ω, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hpath : ∀ᵐ ω ∂P', CmpPath κ ρ (W · ω) (B · ω) (fun j t => U j t ω) (ζ ω))
    (hdrift : ∀ᵐ ω ∂P', ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ j, IsMon ρ ρ' k j → W t ω ≠ U j t ω) →
      0 < U k t ω - W t ω ∧ κ / (2 * (U k t ω - W t ω)) ≤ cmpBeta ρ' k (W · ω) (fun j t => U j t ω) t)
    {ℓ a C : ℝ} (hℓ : 0 < ℓ) (hℓa : ℓ < a) :
    P' (cmpSet ρ ρ' k q W U ζ T₀ ℓ a C) = 0 := by
  by_cases hqT : q ≤ T₀
  swap
  · convert measure_empty (μ := P')
    refine eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    obtain ⟨T, hqT', hTT₀, -⟩ := hω
    exact hqT (hqT'.le.trans hTT₀)
  set S := cmpSet ρ ρ' k q W U ζ T₀ ℓ a C with hSdef
  -- the bound for every transfer parameter `λ` and repulsion level `ε`
  have hbound : ∀ lam : ℝ, 0 < lam → ∀ ε : ℝ, 0 < ε → ε < ℓ →
      P' S ≤ ENNReal.ofReal (lam / 2 * (Sec4.Repulsion.repulsionInt 0 a ℓ /
        Sec4.Repulsion.repulsionInt 0 a ε) + Real.exp (C / κ) / (2 * lam)) := by
    intro lam hlam ε hε hεℓ
    set G : ℕ → Set Ω := fun N =>
      cmpGood κ ρ ρ' k q (1 / ((N : ℝ) + 1)) W U ζ T₀ ℓ a (ε / 2) (C / κ) with hG
    have hsub : S ⊆ ⋃ M : ℕ, ⋂ N ∈ Ici M, G N := fun ω hω => by
      obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_mem_cmpGood (𝓖 := 𝓖) hκ hW hU hWc hUc hqT
        (half_pos hε) hω)
      exact mem_iUnion.2 ⟨M, mem_iInter₂.2 fun N hN => hM N hN⟩
    have hmono : Monotone fun M : ℕ => ⋂ N ∈ Ici M, G N := fun M M' hMM' =>
      biInter_mono (Ici_subset_Ici.2 hMM') fun _ _ => le_rfl
    refine (measure_mono hsub).trans ?_
    rw [hmono.measure_iUnion]
    refine iSup_le fun M => (measure_mono (biInter_subset_of_mem (Set.mem_Ici.2 (le_refl M)))).trans ?_
    exact measure_quad_hit_le hκ hB hW hU hWc hUc hpath hdrift Nat.one_div_pos_of_nat hqT hε
      (half_lt_self hε) hεℓ hℓa hlam
  -- conclusion
  by_contra hne
  have hfin : P' S ≠ ⊤ := measure_ne_top _ _
  set x := (P' S).toReal with hx
  have hxpos : 0 < x := ENNReal.toReal_pos hne hfin
  set c := x / 2 with hc
  have hcpos : 0 < c := half_pos hxpos
  set lam := Real.exp (C / κ) / c with hlam
  have hlampos : 0 < lam := div_pos (Real.exp_pos _) hcpos
  set Fℓ := Sec4.Repulsion.repulsionInt 0 a ℓ with hFℓ
  have hFℓ0 : 0 ≤ Fℓ := Sec4.Repulsion.repulsionInt_nonneg hℓ hℓa.le
  obtain ⟨ε₀, hε₀, hε₀a, hε₀F⟩ := Sec4.Repulsion.exists_le_repulsionInt (η := 0) le_rfl (hℓ.trans hℓa)
    (lam * Fℓ / c + 1)
  set ε := min ε₀ (ℓ / 2) with hε
  have hεpos : 0 < ε := lt_min hε₀ (half_pos hℓ)
  have hεℓ : ε < ℓ := (min_le_right _ _).trans_lt (half_lt_self hℓ)
  have hFε := hε₀F ε hεpos (min_le_left _ _)
  have hFεpos : 0 < Sec4.Repulsion.repulsionInt 0 a ε :=
    lt_of_lt_of_le (by positivity) hFε
  have h1 : lam / 2 * (Fℓ / Sec4.Repulsion.repulsionInt 0 a ε) ≤ c / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have : lam * Fℓ ≤ c * Sec4.Repulsion.repulsionInt 0 a ε := by
      have h2 : c * (lam * Fℓ / c + 1) ≤ c * Sec4.Repulsion.repulsionInt 0 a ε :=
        mul_le_mul_of_nonneg_left hFε hcpos.le
      rw [mul_add, mul_div_cancel₀ _ hcpos.ne', mul_one] at h2
      linarith
    nlinarith
  have h2 : Real.exp (C / κ) / (2 * lam) = c / 2 := by
    rw [hlam]
    field_simp
  have h3 := hbound lam hlampos ε hεpos hεℓ
  have h4 : P' S ≤ ENNReal.ofReal c := h3.trans (ENNReal.ofReal_le_ofReal (by rw [h2]; linarith))
  have h5 := ENNReal.toReal_le_of_le_ofReal hcpos.le h4
  rw [← hx] at h5
  linarith

/-- **The Girsanov comparison of Aux. lemma 62** (generic form). Let `(W, U)` be a driver and marks with
weights `ρ` (`CmpPath`), adapted before the lifetime and continuous on `[0, ζ)` for every `ω`, and let `ρ'` be
comparison weights under which the gap of the mark `k` is repelled: `β = 2/(U_k − W) − ∑ ρ'ⱼ/(W − Uⱼ) ≥ κ/(2(U_k − W))`
while the monitored marks are off the driver. Then almost surely there is no time `T > q` such that, on `[q, T)`, the
monitored marks stay off the driver with bounded energy `∫_q^t (∑ (ρ'ⱼ − ρⱼ)/(W − Uⱼ))²`, and the repelled gap
tends to `0` at `T`. -/
theorem measure_eq_zero_of_cmp [IsProbabilityMeasure P'] (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓖 B P')
    (hW : AdaptedBefore 𝓖 ζ W) (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j))
    (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j ω, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hpath : ∀ᵐ ω ∂P', CmpPath κ ρ (W · ω) (B · ω) (fun j t => U j t ω) (ζ ω))
    (hdrift : ∀ᵐ ω ∂P', ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ j, IsMon ρ ρ' k j → W t ω ≠ U j t ω) →
      0 < U k t ω - W t ω ∧ κ / (2 * (U k t ω - W t ω)) ≤ cmpBeta ρ' k (W · ω) (fun j t => U j t ω) t)
    (q : ℝ≥0) {A : Set Ω}
    (hA : ∀ ω ∈ A, ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ ω ∧
      (∀ t : ℝ≥0, q ≤ t → t < T → ∀ j, IsMon ρ ρ' k j → W t ω ≠ U j t ω) ∧
      (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
        (∫ s in (q : ℝ)..t, (∑ j, (ρ' j - ρ j) / (W s.toNNReal ω - U j s.toNNReal ω)) ^ 2) ≤ C) ∧
      Tendsto (fun t => U k t ω - W t ω) (𝓝[<] T) (𝓝 0)) :
    P' A = 0 := by
  have key : ∀ᵐ ω ∂P', ω ∈ A → ω ∈ ⋃ (i : ℕ) (n : ℕ) (c : ℕ) (nT : ℕ),
      cmpSet ρ ρ' k q W U ζ (nT : ℝ≥0) (1 / ((i : ℝ) + 1)) ((n : ℝ) + 2) (c : ℝ) := by
    filter_upwards [hdrift] with ω hd hωA
    obtain ⟨T, hqT, hTζ, hgap, ⟨C, hC⟩, hlim⟩ := hA ω hωA
    have hlive : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ ω := fun t ht =>
      lt_of_lt_of_le (by exact_mod_cast ht) hTζ
    have hYq : 0 < U k q ω - W q ω := (hd q (hlive q hqT) (hgap q le_rfl hqT)).1
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hYq
    -- the gap is bounded above on `[q, T)`
    have hbdd : ∃ M : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T → U k t ω - W t ω ≤ M := by
      have hev : {t | U k t ω - W t ω < 1} ∈ 𝓝[<] T := hlim (Iio_mem_nhds one_pos)
      obtain ⟨l, hl, hlsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hqT).1 hev
      set t₂ := max l q with ht₂
      have ht₂T : t₂ < T := max_lt hl hqT
      have hc : ContinuousOn (fun t => U k t ω - W t ω) (Icc q t₂) :=
        ((hUc k ω).sub (hWc ω)).mono fun t ht => hlive t (ht.2.trans_lt ht₂T)
      obtain ⟨M₁, hM₁⟩ := (isCompact_Icc.image_of_continuousOn hc).bddAbove
      refine ⟨max M₁ 1, fun t hqt htT => ?_⟩
      by_cases ht : t ≤ t₂
      · exact (hM₁ ⟨t, ⟨hqt, ht⟩, rfl⟩).trans (le_max_left _ _)
      · rw [not_le] at ht
        exact ((hlsub ⟨(le_max_left l q).trans_lt ht, htT⟩ : U k t ω - W t ω < 1).le).trans
          (le_max_right _ _)
    obtain ⟨M, hM⟩ := hbdd
    refine mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨⌈M⌉₊, mem_iUnion.2 ⟨⌈C⌉₊, mem_iUnion.2 ⟨⌈(T : ℝ)⌉₊, ?_⟩⟩⟩⟩
    refine ⟨T, hqT, ?_, hTζ, fun t hqt htT => ⟨hgap t hqt htT, (hC t hqt htT).trans (Nat.le_ceil _), ?_⟩,
      hi.le, hlim⟩
    · rw [← NNReal.coe_le_coe, NNReal.coe_natCast]
      exact Nat.le_ceil _
    · have := hM t hqt htT
      have := Nat.le_ceil M
      linarith
  refine measure_mono_null_ae key ?_
  refine measure_iUnion_null fun i => measure_iUnion_null fun n => measure_iUnion_null fun c =>
    measure_iUnion_null fun nT => ?_
  refine measure_cmpSet_eq_zero hκ hB hW hU hWc hUc hpath hdrift Nat.one_div_pos_of_nat ?_
  have h1 : 1 / ((i : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  linarith [Nat.cast_nonneg (α := ℝ) n]

end GB7a

end InteractingSLE
