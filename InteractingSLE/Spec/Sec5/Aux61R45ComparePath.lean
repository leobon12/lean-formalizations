/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux62Compare
import InteractingSLE.Spec.Coupling.SafeFamily

/-!
# Aux. 62 comparison strictly before an announced stop

The algebra and estimates are the landed `Aux62Compare` proofs, generalized
only at their use of maximality. `CmpEquations` omits the continuation-threshold
clause. The repulsion stop is additionally cut at an announcing time; every
point of its closed interval is therefore strictly before the lifetime.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
namespace InteractingSLE.Sec5.Aux61R45
open GB7a Girsanov Sec2
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {m : ℕ}

/-- Local integrated equations, without a maximal-lifetime assertion. -/
structure CmpEquations (κ : ℝ) (ρ : Fin m → ℝ) (w b : ℝ≥0 → ℝ) (u : Fin m → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop where
  integrable : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ j,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - u j s.toNNReal)⁻¹) volume 0 t
  w_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
    w t = Real.sqrt κ * b t + ∑ j, ∫ s in (0 : ℝ)..t, ρ j / (w s.toNNReal - u j s.toNNReal)
  u_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ j,
    u j t = u j 0 + ∫ s in (0 : ℝ)..t, 2 / (u j s.toNNReal - w s.toNNReal)
variable {κ : ℝ} {ρ ρ' : Fin m → ℝ}

/-- **The decomposition of the repelled gap under the changed measure** (pathwise): if `b̃ = b + ∫ θ` with `θ` the
cut weight-change drift, and the changed marks stay `δ`-away from the driver on `(q, t)`, then
`(u_k − w)(t) = (u_k − w)(q) − √κ (b̃_t − b̃_q) + ∫_q^t β`. -/
theorem CmpEquations.decomp (hκ : 0 < κ) {w b bt : ℝ≥0 → ℝ} {u : Fin m → ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞}
    (hp : CmpEquations κ ρ w b u ζ₀) {q t : ℝ≥0} (hqt : q ≤ t) (ht : (t : ℝ≥0∞) < ζ₀) (k : Fin m)
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


variable {𝓖 : Filtration ℝ≥0 mΩ} {P' : Measure Ω}
  {B W : ℝ≥0 → Ω → ℝ} {U : Fin m → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {k : Fin m} {q T₀ : ℝ≥0} {δ : ℝ}

/-- The separation stop cut at one announcing time, and floored at the restart. -/
def annStop (ρ ρ' : Fin m → ℝ) (k : Fin m) (q : ℝ≥0) (δ : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (U : Fin m → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (T₀ : ℝ≥0) (R : Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  max q (min (R ω) (cmpStop ρ ρ' k q δ W U ζ T₀ ω))

theorem annStop_le_cmpStop {R : Ω → ℝ≥0} (ω : Ω) :
    annStop ρ ρ' k q δ W U ζ T₀ R ω ≤ cmpStop ρ ρ' k q δ W U ζ T₀ ω :=
  max_le (le_max_left _ _) (min_le_right _ _)

theorem annStop_lt_lifetime {R : Ω → ℝ≥0} {ω : Ω}
    (hR : (R ω : ℝ≥0∞) < ζ ω) (hq : (q : ℝ≥0∞) < ζ ω) :
    (annStop ρ ρ' k q δ W U ζ T₀ R ω : ℝ≥0∞) < ζ ω := by
  rw [annStop, ENNReal.coe_max]
  exact max_lt hq (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_left _ _)) hR)

theorem isRepulsionPath_annStop (hκ : 0 < κ) (hδ : 0 < δ) (hqT : q ≤ T₀) (hW : AdaptedBefore 𝓖 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓖 ζ (U j)) (hWc : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hUc : ∀ j ω, ContinuousOn (U j · ω) {t | (t : ℝ≥0∞) < ζ ω}) {ω : Ω}
    (hp : CmpEquations κ ρ (W · ω) (B · ω) (fun j t => U j t ω) (ζ ω))
    (hd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → (∀ j, IsMon ρ ρ' k j → W t ω ≠ U j t ω) →
      0 < U k t ω - W t ω ∧ κ / (2 * (U k t ω - W t ω)) ≤ cmpBeta ρ' k (W · ω) (fun j t => U j t ω) t)
    {R : Ω → ℝ≥0} (hR : (R ω : ℝ≥0∞) < ζ ω)
    (hBc : Continuous (B · ω)) (hqζ : (q : ℝ≥0∞) < ζ ω) (a : ℝ) :
    Sec4.Repulsion.IsRepulsionPath (-Real.sqrt κ) a 0 q (annStop ρ ρ' k q δ W U ζ T₀ R ω)
      (killedGap ζ W U k · ω)
      (girsanovProcess B (cmpDrift κ δ (fun j => ρ' j - ρ j) (sepTime ρ ρ' k q δ W U ζ T₀) ζ q W U) · ω)
      (cmpBeta ρ' k (W · ω) (fun j t => U j t ω)) (fun r => cmpK ρ' δ * r) := by
  set ρs := annStop ρ ρ' k q δ W U ζ T₀ R ω with hρs
  have hτ := measurableSet_sepTime_le (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (T₀ := T₀) hδ.le hW hU hWc hUc
  have hτζ := sepTime_le_lifetime (ρ := ρ) (ρ' := ρ') (k := k) (q := q) (W := W) (U := U) (ζ := ζ)
    (T₀ := T₀) hδ.le
  have hθ := isStronglyProgressive_cmpDrift (κ := κ) (σ := fun j => ρ' j - ρ j) (q := q) hδ hW hU hτ
  have hθb := abs_cmpDrift_le (κ := κ) (σ := fun j => ρ' j - ρ j) (τ := (sepTime ρ ρ' k q δ W U ζ T₀)) (ζ := ζ)
    (q := q) (W := W)
    (U := U) hδ
  have hρτ : (ρs : ℝ≥0∞) ≤ sepTime ρ ρ' k q δ W U ζ T₀ ω := by
    rw [← coe_cmpStop hqT hqζ]
    exact ENNReal.coe_le_coe.2 (annStop_le_cmpStop _)
  have hρζ : (ρs : ℝ≥0∞) < ζ ω := annStop_lt_lifetime hR hqζ
  have hqρ : q ≤ ρs := le_max_left _ _
  -- every time of `[q, ρ]` is alive
  have halive : ∀ r : ℝ≥0, r ≤ ρs → (r : ℝ≥0∞) < ζ ω := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr) hρζ
  have hkill : ∀ r : ℝ≥0, r ≤ ρs → killedGap ζ W U k r ω = U k r ω - W r ω := fun r hr => by
    rw [killedGap, killed_of_lt (halive r hr), killed_of_lt (halive r hr)]
  -- before `ρ`, the monitored gaps exceed `δ`
  have hsep : ∀ r : ℝ, (q : ℝ) ≤ r → r < ρs → (r.toNNReal : ℝ≥0∞) < ζ ω ∧
      ∀ j, IsMon ρ ρ' k j → δ < |W r.toNNReal ω - U j r.toNNReal ω| := fun r hqr hrρ => by
    have hr0 : 0 ≤ r := (NNReal.coe_nonneg q).trans hqr
    refine lt_of_lt_sepTime (T₀ := T₀) (q := q) hδ.le ?_ ?_
    · apply lt_of_lt_of_le _ hρτ
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]
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
      (fun j => hUc j ω) hu.1 ((ENNReal.coe_le_coe.2 hu.2).trans hρτ)]
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


end InteractingSLE.Sec5.Aux61R45
