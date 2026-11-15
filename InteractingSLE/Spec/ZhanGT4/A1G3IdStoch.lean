/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3IdRec
import InteractingSLE.Spec.Sec2.AddMarksInverse

/-!
# Zhan's A.1 (G3): two facts for the Doléans identification

Packet PROVE-A1-G3ROW2.

* **`stochIntegral_ae_eq_of_eq_off`**: two bounded adapted Riemann-regular integrands that agree at every time except
  one random time `τ(ω)` have almost surely equal Itô integrals (the dyadic Riemann sums differ by at most one term,
  a bounded multiple of a Brownian increment over one cell, which tends to `0` by uniform continuity of the paths).
  This is needed because the cut drift of Girsanov's theorem (`cutDrift`) and the stopped coefficient of the
  logarithmic Itô formula (`Ito.stopCoef`) may differ at the stopping time itself.
* **`sub_eq_mul_exp_of_force`**: two force points `v_x`, `v_y` of a driver `w`, off the driver on `[0, S]`, satisfy
  `v_x − v_y = (x − y) exp(−∫₀ᵗ 2/((v_x − w)(v_y − w)))` there (the linear ODE
  `(v_x − v_y)' = −2(v_x − v_y)/((v_x − w)(v_y − w))`); in particular they never meet.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Id

open Girsanov

/-! ### Itô integrals of integrands that differ at one random time -/

section OnePoint

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {B θ θ' : ℝ≥0 → Ω → ℝ}

theorem grid_injective (n : ℕ) : Function.Injective (grid n) := by
  intro i j h
  have h' := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  simp only [coe_grid] at h'
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [div_left_inj' h2] at h'
  exact_mod_cast h'

/-- **The Riemann sums of integrands agreeing off one time differ by at most one term.** -/
theorem abs_riemannSum_sub_le {C C' : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθb' : ∀ t ω, |θ' t ω| ≤ C')
    {τ : Ω → ℝ≥0} (heq : ∀ ω t, t ≠ τ ω → θ t ω = θ' t ω) (n : ℕ) (d : ℝ≥0) (ω : Ω) {M : ℝ}
    (hM : ∀ i, |B (min (grid n (i + 1)) d) ω - B (min (grid n i) d) ω| ≤ M) :
    |riemannSum B θ n d ω - riemannSum B θ' n d ω| ≤ (C + C') * M := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hθb 0 ω)
  have hC' : 0 ≤ C' := (abs_nonneg _).trans (hθb' 0 ω)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  unfold riemannSum
  rw [← Finset.sum_sub_distrib]
  by_cases h : ∃ i ∈ Finset.range (cells n), grid n i = τ ω
  · obtain ⟨i₀, hi₀, hg⟩ := h
    rw [Finset.sum_eq_single_of_mem i₀ hi₀ fun j _ hj => by
      have hne : grid n j ≠ τ ω := fun h' => hj (grid_injective n (h'.trans hg.symm))
      rw [heq ω _ hne]
      ring]
    rw [← sub_mul, abs_mul]
    refine mul_le_mul ((abs_sub _ _).trans (add_le_add (hθb _ ω) (hθb' _ ω))) (hM i₀) (abs_nonneg _)
      (by positivity)
  · push Not at h
    rw [Finset.sum_eq_zero fun j hj => by rw [heq ω _ (h j hj)]; ring, abs_zero]
    positivity

/-- **The Riemann sums of integrands agreeing off one time have the same limit along a continuous path.** -/
theorem tendsto_riemannSum_sub {C C' : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθb' : ∀ t ω, |θ' t ω| ≤ C')
    {τ : Ω → ℝ≥0} (heq : ∀ ω t, t ≠ τ ω → θ t ω = θ' t ω) (d : ℝ≥0) {ω : Ω} (hBc : Continuous (B · ω)) :
    Tendsto (fun n => riemannSum B θ n d ω - riemannSum B θ' n d ω) atTop (𝓝 0) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hθb 0 ω)
  have hC' : 0 ≤ C' := (abs_nonneg _).trans (hθb' 0 ω)
  have huc : UniformContinuousOn (B · ω) (Icc 0 d) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hBc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (C + C' + 1) with hε'
  have hε'pos : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨η, hη, hcont⟩ := huc ε' hε'pos
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hη (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  have hM : ∀ i, |B (min (grid n (i + 1)) d) ω - B (min (grid n i) d) ω| ≤ ε' := by
    intro i
    have ha : min (grid n (i + 1)) d ∈ Icc 0 d := ⟨bot_le, min_le_right _ _⟩
    have hb : min (grid n i) d ∈ Icc 0 d := ⟨bot_le, min_le_right _ _⟩
    have hdist : dist (min (grid n (i + 1)) d) (min (grid n i) d) < η := by
      rw [NNReal.dist_eq, NNReal.coe_min, NNReal.coe_min]
      refine (abs_min_sub_min_le_max _ _ _ _).trans_lt ?_
      rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), coe_grid, coe_grid]
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      have e : ((↑(i + 1) : ℝ) / 2 ^ n - (i : ℝ) / 2 ^ n) = (1 / 2) ^ n := by
        rw [one_div_pow, ← sub_div]
        push_cast
        ring
      rw [e, abs_of_pos (by positivity)]
      exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn).trans_lt hN
    have := hcont _ ha _ hb hdist
    rw [Real.dist_eq] at this
    exact this.le
  have hb := abs_riemannSum_sub_le (B := B) hθb hθb' heq n d ω hM
  rw [Real.dist_eq, sub_zero]
  refine hb.trans_lt ?_
  rw [hε']
  have hCC : 0 < C + C' + 1 := by positivity
  calc (C + C') * (ε / (C + C' + 1)) < (C + C' + 1) * (ε / (C + C' + 1)) :=
        mul_lt_mul_of_pos_right (by linarith) (div_pos hε hCC)
    _ = ε := by field_simp

/-- **Itô integrals of integrands that agree off one random time agree almost surely** (continuous Brownian paths). -/
theorem stochIntegral_ae_eq_of_eq_off [IsProbabilityMeasure P] (hB : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ ω, Continuous (B · ω)) (hθm : StronglyAdapted 𝓕 θ) (hθm' : StronglyAdapted 𝓕 θ') {C C' : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθb' : ∀ t ω, |θ' t ω| ≤ C') (hθreg : IsRiemannRegular P θ)
    (hθreg' : IsRiemannRegular P θ') {τ : Ω → ℝ≥0} (heq : ∀ ω t, t ≠ τ ω → θ t ω = θ' t ω) (d : ℝ≥0) :
    stochIntegral P 𝓕 B θ d =ᵐ[P] stochIntegral P 𝓕 B θ' d := by
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_riemannSum hB hθm hθb hθreg d).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae'⟩ := ((tendstoInMeasure_riemannSum hB hθm' hθb' hθreg' d).comp
    hns.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hae, hae'] with ω h1 h2
  have h1' : Tendsto (fun i => riemannSum B θ (ns (ms i)) d ω) atTop
      (𝓝 (stochIntegral P 𝓕 B θ d ω)) := h1.comp hms.tendsto_atTop
  have hdiff := ((tendsto_riemannSum_sub (B := B) hθb hθb' heq d (hBc ω)).comp hns.tendsto_atTop).comp
    hms.tendsto_atTop
  have h2' : Tendsto (fun i => riemannSum B θ (ns (ms i)) d ω) atTop
      (𝓝 (stochIntegral P 𝓕 B θ' d ω)) := by
    have := h2.add hdiff
    rw [add_zero] at this
    refine this.congr fun i => ?_
    simp only [Function.comp_apply]
    ring
  exact tendsto_nhds_unique h1' h2'

end OnePoint

/-! ### Two force points of one driver never meet -/

section Force

/-- **Two force points of one driver, off the driver on `[0, S]`, satisfy the linear ODE of their difference**:
`v_x t − v_y t = (x − y) exp(−∫₀ᵗ 2/((v_x − w)(v_y − w)))` for `t ≤ S`. -/
theorem sub_eq_mul_exp_of_force {w vx vy : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {x y : ℝ}
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hxc : ContinuousOn vx {t | (t : ℝ≥0∞) < ζ})
    (hyc : ContinuousOn vy {t | (t : ℝ≥0∞) < ζ})
    (hx : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vx t = x + ∫ s in (0 : ℝ)..t, 2 / (vx s.toNNReal - w s.toNNReal))
    (hy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vy t = y + ∫ s in (0 : ℝ)..t, 2 / (vy s.toNNReal - w s.toNNReal))
    {S : ℝ≥0} (hS : (S : ℝ≥0∞) < ζ) (hgx : ∀ r ≤ S, vx r ≠ w r) (hgy : ∀ r ≤ S, vy r ≠ w r) {t : ℝ≥0}
    (ht : t ≤ S) :
    vx t - vy t = (x - y) *
      Real.exp (-∫ s in (0 : ℝ)..t, 2 / ((vx s.toNNReal - w s.toNNReal) * (vy s.toNNReal - w s.toNNReal))) := by
  have hSE : ENNReal.ofReal (S : ℝ) < ζ := by rw [ENNReal.ofReal_coe_nnreal]; exact hS
  have cW : ContinuousOn (Strip.extPath w) (Icc 0 (S : ℝ)) := A1Ref.continuousOn_extPath_Icc hwc hSE
  have cX : ContinuousOn (Strip.extPath vx) (Icc 0 (S : ℝ)) := A1Ref.continuousOn_extPath_Icc hxc hSE
  have cY : ContinuousOn (Strip.extPath vy) (Icc 0 (S : ℝ)) := A1Ref.continuousOn_extPath_Icc hyc hSE
  have hle : ∀ u ∈ Icc (0 : ℝ) S, u.toNNReal ≤ S := fun u hu => Real.toNNReal_le_iff_le_coe.2 hu.2
  have nX : ∀ u ∈ Icc (0 : ℝ) S, Strip.extPath vx u - Strip.extPath w u ≠ 0 := fun u hu =>
    sub_ne_zero.2 (hgx _ (hle u hu))
  have nY : ∀ u ∈ Icc (0 : ℝ) S, Strip.extPath vy u - Strip.extPath w u ≠ 0 := fun u hu =>
    sub_ne_zero.2 (hgy _ (hle u hu))
  set a : ℝ → ℝ := fun s => 2 / ((Strip.extPath vx s - Strip.extPath w s) * (Strip.extPath vy s - Strip.extPath w s))
    with ha
  have ca : ContinuousOn a (Icc 0 (S : ℝ)) :=
    continuousOn_const.div ((cX.sub cW).mul (cY.sub cW)) fun u hu => mul_ne_zero (nX u hu) (nY u hu)
  have gX : ContinuousOn (fun s => 2 / (Strip.extPath vx s - Strip.extPath w s)) (Icc 0 (S : ℝ)) :=
    continuousOn_const.div (cX.sub cW) nX
  have gY : ContinuousOn (fun s => 2 / (Strip.extPath vy s - Strip.extPath w s)) (Icc 0 (S : ℝ)) :=
    continuousOn_const.div (cY.sub cW) nY
  -- the force points on `[0, S]`
  have eX : ∀ u ∈ Icc (0 : ℝ) S, Strip.extPath vx u = x + ∫ s in (0 : ℝ)..u, 2 / (Strip.extPath vx s -
      Strip.extPath w s) := fun u hu => by
    simp only [Strip.extPath]
    rw [hx _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hle u hu)) hS), Real.coe_toNNReal _ hu.1]
  have eY : ∀ u ∈ Icc (0 : ℝ) S, Strip.extPath vy u = y + ∫ s in (0 : ℝ)..u, 2 / (Strip.extPath vy s -
      Strip.extPath w s) := fun u hu => by
    simp only [Strip.extPath]
    rw [hy _ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hle u hu)) hS), Real.coe_toNNReal _ hu.1]
  have dX : ∀ u ∈ Icc (0 : ℝ) S, HasDerivWithinAt (Strip.extPath vx)
      (2 / (Strip.extPath vx u - Strip.extPath w u)) (Icc 0 (S : ℝ)) u := fun u hu =>
    ((hasDerivWithinAt_integral_base_real gX hu).const_add x).congr (fun v hv => eX v hv) (eX u hu)
  have dY : ∀ u ∈ Icc (0 : ℝ) S, HasDerivWithinAt (Strip.extPath vy)
      (2 / (Strip.extPath vy u - Strip.extPath w u)) (Icc 0 (S : ℝ)) u := fun u hu =>
    ((hasDerivWithinAt_integral_base_real gY hu).const_add y).congr (fun v hv => eY v hv) (eY u hu)
  set f : ℝ → ℝ := fun u => (Strip.extPath vx u - Strip.extPath vy u) * Real.exp (∫ s in (0 : ℝ)..u, a s) with hf
  have df : ∀ u ∈ Icc (0 : ℝ) S, HasDerivWithinAt f 0 (Icc 0 (S : ℝ)) u := by
    intro u hu
    have hA := (hasDerivWithinAt_integral_base_real ca hu).exp
    have h : HasDerivWithinAt (fun v => (Strip.extPath vx v - Strip.extPath vy v) * Real.exp (∫ s in (0 : ℝ)..v, a s))
        ((2 / (Strip.extPath vx u - Strip.extPath w u) - 2 / (Strip.extPath vy u - Strip.extPath w u)) *
            Real.exp (∫ s in (0 : ℝ)..u, a s) +
          (Strip.extPath vx u - Strip.extPath vy u) * (Real.exp (∫ s in (0 : ℝ)..u, a s) * a u))
        (Icc 0 (S : ℝ)) u := ((dX u hu).sub (dY u hu)).mul hA
    refine h.congr_deriv ?_
    have h1 := nX u hu
    have h2 := nY u hu
    rw [ha]
    dsimp only
    field_simp
    ring
  have hfc : ContinuousOn f (Icc 0 (S : ℝ)) := fun u hu => (df u hu).continuousWithinAt
  have hderiv : ∀ u ∈ Ico (0 : ℝ) S, HasDerivWithinAt f 0 (Ici u) u := fun u hu =>
    (df u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
      (mem_of_superset (Icc_mem_nhdsGE hu.2) (Icc_subset_Icc_left hu.1))
  have hconst : ∀ u ∈ Ico (0 : ℝ) S, HasDerivWithinAt (fun _ : ℝ => x - y) 0 (Ici u) u := fun _ _ =>
    hasDerivWithinAt_const _ _ _
  have h0 : f 0 = x - y := by
    have e0 := eX 0 ⟨le_rfl, S.coe_nonneg⟩
    have e0' := eY 0 ⟨le_rfl, S.coe_nonneg⟩
    simp only [intervalIntegral.integral_same, add_zero] at e0 e0'
    simp only [hf, e0, e0', intervalIntegral.integral_same, Real.exp_zero, mul_one]
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) S := ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  have key := eq_of_has_deriv_right_eq hderiv hconst hfc continuousOn_const h0 t htI
  simp only [hf, Strip.extPath, Real.toNNReal_coe] at key
  have hint : (∫ s in (0 : ℝ)..t, a s) =
      ∫ s in (0 : ℝ)..t, 2 / ((vx s.toNNReal - w s.toNNReal) * (vy s.toNNReal - w s.toNNReal)) := rfl
  rw [hint] at key
  rw [Real.exp_neg, ← key]
  field_simp

end Force

end InteractingSLE.ZhanGT4.A1G3Id
