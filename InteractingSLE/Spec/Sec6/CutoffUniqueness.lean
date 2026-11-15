/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.CutoffEnergy
import InteractingSLE.Spec.Sec6.CutoffPairing
import InteractingSLE.Spec.Sec6.TraceDisk
import InteractingSLE.Spec.Sec6.ConformalDirichlet
import InteractingSLE.Spec.Sec6.FiniteExceptionUniqueness

/-!
# Aux. lemma 29: uniqueness with finitely many exceptional physical points

Packet PROVE-SEC6-A2 (specification §6.1, `source/spec/p145-192.md`, `#aux-29`, pp. 164–166).

**Aux. lemma 29 (first part).** Let `O` be a bounded simply connected domain with locally
connected boundary, `f : 𝔻 → O` conformal (and also its continuous extension to the closed disk),
`P ⊆ ∂O` finite. If `u` is harmonic in `𝔻`, `u ∈ L²(𝔻)`, and `u` has continuous boundary value
zero at every point of `∂𝔻 \ f⁻¹(P)`, then `u = 0`. There is no assumption that `f⁻¹(P)` is finite.

## Lean statements

* `aux29_eqOn_zero_disk`: the disk statement. The map is any `f` holomorphic and injective on the
  open disk, continuous on the closed disk, with `f(𝔻) ∩ P = ∅`.
* `aux29_eqOn_zero`: the source's form, for `f` a conformal bijection of `𝔻` onto an open `O`
  that is continuous on the closed disk, and `P ⊆ ∂O` finite.

The hypotheses "bounded, simply connected, locally connected boundary" of the source serve only to
provide the continuous extension of `f` to the closed disk ("Here `f` denotes also its continuous
extension"); the Lean statements take the extension itself as the hypothesis `ContinuousOn f
(closedBall 0 1)` and drop the three conditions on `O`.

## Proof (as in the source, with smooth cutoffs)

Write `u = Re F`, `c_n` its harmonic coefficients, `T(ψ) = ∑ c_n ψ̂(−n)` the boundary distribution;
(PU4) gives `S = ∑ |c_n|²/(|n|+1) < ∞`. For `r → 0`, the cutoffs `b_r` (`capCutoff`, `= 1` within
`r` of `P`) have energy `→ 0`, and `v_r = b_r ∘ f → 0` in `L²(𝔻)` by dominated convergence (the
points `f(ζ)`, `ζ ∈ 𝔻`, are not in `P`). By uniform continuity of `f` on the closed disk, for
`R < 1` close to `1` the boundary function `ψ_r(t) = v_r(R e^{it})` equals `1` on an open
neighbourhood `U` of `E = ∂𝔻 ∩ f⁻¹(P)`, and by the trace estimate (PU1) and conformal invariance
`‖ψ_r‖²_{H^{1/2}} ≤ 8 (‖v_r‖²_{L²} + ∫ |∇b_r|²) → 0` (PU2–PU3). For the mode `e_m = e^{−imt}`:
`T(e_m) = c_m`, `T(e_m(1 − ψ_r)) = 0` (support), and
`|T(e_m ψ_r)| ≤ (ε/2) S + (2ε)⁻¹ (1 + |m|) ‖ψ_r‖²_{H^{1/2}}`. Hence `c_m = 0` for all `m`, `u = 0`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace InteractingSLE.Sec6

/-! ## The cutoffs as `r → 0` -/

theorem continuous_capCutoff {P : Finset ℂ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (capCutoff P r) :=
  continuous_iff_continuousAt.2 fun z => (hasFDerivAt_capCutoff hr0 hr1 z).continuousAt

/-- The energy of the multi-point cutoffs tends to zero (the source's
`∫ |∇b_r|² ≤ 2πN / log(R/r) → 0`). -/
theorem tendsto_energy_capCutoff (P : Finset ℂ) :
    Tendsto (fun r => ∫⁻ z, ENNReal.ofReal (‖capCutoffDeriv P r z‖ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨D, -, hD⟩ := exists_bound_deriv_cutProfile
  have h1 : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h2 : Tendsto (fun r : ℝ => (P.card : ℝ) ^ 2 * (18 * π * D ^ 2 / -Real.log r)) (𝓝[>] 0)
      (𝓝 ((P.card : ℝ) ^ 2 * 0)) :=
    (tendsto_const_nhds.div_atTop h1).const_mul _
  rw [mul_zero] at h2
  have h3 := ENNReal.tendsto_ofReal h2
  rw [ENNReal.ofReal_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h3
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact lintegral_capCutoffDeriv_le hD hr.1 hr.2

/-- `v_r = b_r ∘ f → 0` in `L²(𝔻)` when `f(𝔻)` avoids `P` (dominated convergence). -/
theorem tendsto_lintegral_capCutoff_comp {f : ℂ → ℂ} (hfc : ContinuousOn f (ball 0 1))
    {P : Finset ℂ} (hPf : ∀ ζ ∈ ball (0 : ℂ) 1, f ζ ∉ P) :
    Tendsto (fun r => ∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (capCutoff P r (f ζ) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  set G : ℝ → ℂ → ℝ≥0∞ := fun r =>
    (ball (0 : ℂ) 1).indicator fun ζ => ENNReal.ofReal (capCutoff P r (f ζ) ^ 2)
  have hGeq : ∀ r, ∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (capCutoff P r (f ζ) ^ 2) =
      ∫⁻ ζ, G r ζ := fun r => (lintegral_indicator measurableSet_ball _).symm
  simp_rw [hGeq]
  have hmeas : ∀ᶠ r in 𝓝[>] (0 : ℝ), Measurable (G r) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with r hr
    have hc : ContinuousOn (fun ζ => ENNReal.ofReal (capCutoff P r (f ζ) ^ 2)) (ball 0 1) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (((continuous_capCutoff hr.1 hr.2).comp_continuousOn hfc).pow 2)
    have := hc.measurable_piecewise (g := fun _ => (0 : ℝ≥0∞)) continuousOn_const
      measurableSet_ball
    convert this using 1
    funext ζ; simp only [G, Set.indicator, Set.piecewise]
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ᵐ ζ ∂(volume : Measure ℂ),
      G r ζ ≤ (ball (0 : ℂ) 1).indicator 1 ζ := by
    refine Eventually.of_forall fun r => Eventually.of_forall fun ζ => ?_
    refine Set.indicator_le_indicator ?_
    simp only [Pi.one_apply]
    refine ENNReal.ofReal_le_one.2 ?_
    have h0 := capCutoff_nonneg (P := P) (r := r) (f ζ)
    have h1 := capCutoff_le_one (P := P) (r := r) (f ζ)
    nlinarith
  have hfin : ∫⁻ ζ, (ball (0 : ℂ) 1).indicator 1 ζ ≠ ⊤ := by
    rw [lintegral_indicator_one measurableSet_ball]; exact measure_ball_lt_top.ne
  have hlim : ∀ᵐ ζ ∂(volume : Measure ℂ), Tendsto (fun r => G r ζ) (𝓝[>] 0) (𝓝 0) := by
    refine Eventually.of_forall fun ζ => ?_
    by_cases hζ : ζ ∈ ball (0 : ℂ) 1
    · simp only [G, indicator_of_mem hζ]
      have h := ((tendsto_capCutoff_zero (hPf ζ hζ)).pow 2)
      rw [zero_pow two_ne_zero] at h
      simpa using ENNReal.tendsto_ofReal h
    · simp only [G, indicator_of_notMem hζ]
      exact tendsto_const_nhds
  have := tendsto_lintegral_filter_of_dominated_convergence _ hmeas hbound hfin hlim
  simpa using this

/-! ## The coefficient bound from a test function -/

/-- **The pairing estimate** (proof of Aux. lemma 29: "`⟨T, a⟩ = ⟨T, a ψ̃_r⟩`,
`|⟨T, a ψ̃_r⟩| ≤ ‖T‖_{H^{−1/2}} ‖a ψ̃_r‖_{H^{1/2}}`", for the Fourier mode `a = e^{−imt}`). If `ψ`
is an `H^{1/2}` boundary function equal to `1` at the angles of an open set `U`, and `u → 0` at
every point of the circle outside `U`, then
`|c_m| ≤ (ε/2) ∑ |c_n|²/(|n|+1) + (2ε)⁻¹ (1 + |m|) ∑ (1 + |n|) |ψ̂(n)|²`. -/
theorem norm_diskCoeff_le_of_test {F : ℂ → ℂ} {u : ℂ → ℝ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hu : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z)
    (hc : Summable fun n : ℤ => ‖diskCoeff F n‖ ^ 2 / (|(n : ℝ)| + 1))
    {U : Set ℂ} (hU : IsOpen U)
    (hbd : ∀ q : ℂ, ‖q‖ = 1 → q ∉ U → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0))
    {ψ : ℝ → ℂ} (hψ : Continuous ψ)
    (hψs : Summable fun n : ℤ => (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2)
    (hψ1 : ∀ t : ℝ, exp (t * I) ∈ U → ψ t = 1) (m : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ‖diskCoeff F m‖ ≤ ε / 2 * ∑' n : ℤ, ‖diskCoeff F n‖ ^ 2 / (|(n : ℝ)| + 1) +
      (2 * ε)⁻¹ * ((1 + |(m : ℝ)|) * ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2) := by
  set e : ℝ → ℂ := fun t => exp (-((m : ℂ) * t * I)) with he_def
  have he := isC1Loop_exp_neg m
  have hec : Continuous e := he.continuous
  set φ : ℝ → ℂ := fun t => e t * ψ t with hφ_def
  have hφc : Continuous φ := hec.mul hψ
  have hφcoeff : ∀ n : ℤ, circCoeff φ (-n) = circCoeff ψ (-n + m) := fun n =>
    circCoeff_exp_neg_mul m ψ (-n)
  obtain ⟨hsh, hshle⟩ := summable_shift hψs m
  have hpair := summable_norm_mul_of_L2 hc hsh hε
  have hφs : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff φ (-n)‖ := by
    simp_rw [hφcoeff]; exact hpair.1
  have hes : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff e (-n)‖ :=
    (summable_norm_mul_of_L2 hc (summable_sobolev_neg (summable_sobolev_of_isC1Loop he))
      one_pos).1
  have hdiff : Summable fun n => ‖diskCoeff F n‖ * ‖circCoeff (fun t => e t - φ t) (-n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hes.add hφs)
    rw [circCoeff_sub hec hφc, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  have hzero : bdryPair F (fun t => e t - φ t) = 0 :=
    bdryPair_eq_zero_of_vanish_on hF hu hU hbd (hec.sub hφc) hdiff fun t ht => by
      simp only [φ, hψ1 t ht, mul_one, sub_self]
  have hTe : bdryPair F e = diskCoeff F m := by
    unfold bdryPair
    have : ∀ n : ℤ, diskCoeff F n * circCoeff e (-n) = if n = m then diskCoeff F m else 0 := by
      intro n
      rw [he_def, circCoeff_exp_neg]
      split_ifs with h
      · rw [h, mul_one]
      · rw [mul_zero]
    simp_rw [this]
    exact tsum_ite_eq m _
  have hsub := bdryPair_sub hec hφc hes hφs
  rw [hzero] at hsub
  have hTφ : bdryPair F φ = diskCoeff F m := by
    rw [← hTe]; exact (sub_eq_zero.1 hsub.symm).symm
  rw [← hTφ]
  refine (norm_bdryPair_le hφs).trans ?_
  simp_rw [hφcoeff]
  refine hpair.2.trans ?_
  have : (0 : ℝ) ≤ (2 * ε)⁻¹ := by positivity
  gcongr

/-! ## The test functions `ψ_r = (b_r ∘ f)(R e^{it})` -/

/-- **(PU2)–(PU3).** For a fixed cutoff radius `r`, there are an open neighbourhood `U` of
`E = ∂𝔻 ∩ f⁻¹(P)` and a `C¹` boundary function `ψ` (the cutoff `b_r ∘ f` on a circle of radius
`R < 1` close to `1`) equal to `1` at the angles of `U`, with
`‖ψ‖²_{H^{1/2}} ≤ 8 (‖b_r ∘ f‖²_{L²(𝔻)} + ∫_ℂ |∇b_r|²)`. -/
theorem exists_test_capCutoff {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f (ball 0 1))
    (hfi : InjOn f (ball 0 1)) (hfc : ContinuousOn f (closedBall 0 1)) (P : Finset ℂ)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ q ∈ sphere (0 : ℂ) 1, f q ∈ P → q ∈ U) ∧
      ∃ ψ : ℝ → ℂ, Continuous ψ ∧
        Summable (fun n : ℤ => (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2) ∧
        (∀ t : ℝ, exp (t * I) ∈ U → ψ t = 1) ∧
        ENNReal.ofReal (∑' n : ℤ, (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2) ≤
          8 * ((∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (capCutoff P r (f ζ) ^ 2)) +
            ∫⁻ z, ENNReal.ofReal (‖capCutoffDeriv P r z‖ ^ 2)) := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hfc) r hr0
  set R : ℝ := max (1 / 2) (1 - δ / 4)
  have hR1 : R < 1 := max_lt (by norm_num) (by linarith)
  have hR2 : 1 / 2 ≤ R := le_max_left _ _
  have hRδ : 1 - R < δ / 2 := by have := le_max_right (1 / 2 : ℝ) (1 - δ / 4); linarith
  have hR0 : 0 < R := by linarith
  have hRabs : |R| < 1 := by rw [abs_of_pos hR0]; exact hR1
  set v : ℂ → ℝ := fun ζ => capCutoff P r (f ζ)
  set Dv : ℂ → ℂ →L[ℝ] ℝ := fun ζ => (capCutoffDeriv P r (f ζ)).comp (realDeriv (deriv f ζ))
  have hv : ∀ ζ ∈ ball (0 : ℂ) 1, HasFDerivAt v (Dv ζ) ζ := fun ζ hζ =>
    (hasFDerivAt_capCutoff hr0 hr1 (f ζ)).comp ζ
      (hasFDerivAt_realDeriv (hfd.differentiableAt (isOpen_ball.mem_nhds hζ)))
  have hDv : ContinuousOn Dv (ball 0 1) := by
    have h1 : ContinuousOn (fun ζ => capCutoffDeriv P r (f ζ)) (ball 0 1) :=
      (continuous_capCutoffDeriv hr0 hr1).comp_continuousOn hfd.continuousOn
    have h2 : ContinuousOn (fun ζ => realDeriv (deriv f ζ)) (ball 0 1) :=
      (by unfold realDeriv; fun_prop : Continuous realDeriv).comp_continuousOn
        (hfd.deriv isOpen_ball).continuousOn
    exact h1.clm_comp h2
  set ψ : ℝ → ℂ := fun t => (v (polarPt R t) : ℂ)
  have hψ : IsC1Loop ψ fun t => ((Dv (polarPt R t)) ((R : ℂ) * (I * exp (t * I))) : ℂ) :=
    ⟨fun t => (hasDerivAt_v_polar_angle hv hRabs t).ofReal_comp,
      Complex.continuous_ofReal.comp (continuous_Dv_polar hDv hRabs _ (by fun_prop)),
      by simp only [ψ]; rw [polarPt_two_pi]⟩
  set U : Set ℂ := ⋃ q ∈ {q ∈ sphere (0 : ℂ) 1 | f q ∈ P}, ball q (δ / 2)
  have hψs := summable_sobolev_of_isC1Loop hψ
  refine ⟨U, isOpen_biUnion fun q _ => isOpen_ball,
    fun q hq hqP => mem_biUnion (x := q) ⟨hq, hqP⟩ (mem_ball_self (by linarith)), ψ,
    hψ.continuous, hψs, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, ⟨hq, hqP⟩, hqt⟩ := mem_iUnion₂.1 ht
    have hpt : polarPt R t ∈ closedBall (0 : ℂ) 1 :=
      ball_subset_closedBall (polarPt_mem_ball hR0.le hR1 t)
    have hqc : q ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hq
    have hdist : dist (polarPt R t) q < δ := by
      rw [mem_ball] at hqt
      have h1 : dist (polarPt R t) (exp (t * I)) = 1 - R := by
        rw [dist_eq_norm, polarPt,
          show (R : ℂ) * exp (t * I) - exp (t * I) = ((R - 1 : ℝ) : ℂ) * exp (t * I) by
            push_cast; ring,
          norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_neg (by linarith)]
        ring
      calc dist (polarPt R t) q ≤ dist (polarPt R t) (exp (t * I)) + dist (exp (t * I)) q :=
            dist_triangle _ _ _
        _ < δ / 2 + δ / 2 := by rw [h1]; exact add_lt_add hRδ hqt
        _ = δ := by ring
    have h := hδf _ hpt _ hqc hdist
    rw [dist_eq_norm] at h
    simp only [ψ, v]
    rw [capCutoff_eq_one hr0 hr1 hqP h.le, Complex.ofReal_one]
  · set A := ∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (capCutoff P r (f ζ) ^ 2)
    set B := ∫⁻ z, ENNReal.ofReal (‖capCutoffDeriv P r z‖ ^ 2)
    have htr := trace_estimate hv hDv hR2 hR1
    have hconf := lintegral_norm_comp_sq_le hfd hfi (capCutoffDeriv P r)
    have hS : ∀ S : Finset ℤ, ENNReal.ofReal (∑ n ∈ S, (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2) ≤
        8 * (A + B) := fun S => (htr S).trans (mul_le_mul' le_rfl (add_le_add le_rfl hconf))
    by_cases htop : 8 * (A + B) = ⊤
    · rw [htop]; exact le_top
    · have hle : ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2 ≤ (8 * (A + B)).toReal :=
        Real.tsum_le_of_sum_le (fun n => by positivity) fun S =>
          (ENNReal.ofReal_le_iff_le_toReal htop).1 (hS S)
      exact (ENNReal.ofReal_le_ofReal hle).trans (ENNReal.ofReal_toReal htop).le

/-! ## Aux. lemma 29 -/

/-- **Aux. lemma 29** (first part), disk form. Let `f` be holomorphic and injective on the unit
disk and continuous on the closed disk, and let `P` be a finite set with `f(𝔻) ∩ P = ∅`. If `u` is
harmonic in `𝔻`, square integrable on `𝔻`, and has continuous boundary value zero at every point
of `∂𝔻 \ f⁻¹(P)`, then `u = 0`. (No finiteness of `∂𝔻 ∩ f⁻¹(P)` is assumed.) -/
theorem aux29_eqOn_zero_disk {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f (ball 0 1))
    (hfi : InjOn f (ball 0 1)) (hfc : ContinuousOn f (closedBall 0 1)) {P : Set ℂ}
    (hP : P.Finite) (hPf : ∀ ζ ∈ ball (0 : ℂ) 1, f ζ ∉ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
    (hL2 : ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (u z ^ 2) ≠ ⊤)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, f q ∉ P → Tendsto u (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, u z = 0 := by
  obtain ⟨F, hFa, hFeq⟩ := hu.exists_analyticOnNhd_ball_re_eq
  have hF : DifferentiableOn ℂ F (ball 0 1) := hFa.differentiableOn
  have hu' : ∀ z ∈ ball (0 : ℂ) 1, (F z).re = u z := fun z hz => hFeq hz
  have hucont : ContinuousOn u (ball 0 1) :=
    (Complex.continuous_re.comp_continuousOn hF.continuousOn).congr fun z hz => (hu' z hz).symm
  have hc := summable_sq_diskCoeff_div hF hu' hucont hL2
  set S := ∑' n : ℤ, ‖diskCoeff F n‖ ^ 2 / (|(n : ℝ)| + 1)
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by positivity
  set P' : Finset ℂ := hP.toFinset
  have hPf' : ∀ ζ ∈ ball (0 : ℂ) 1, f ζ ∉ P' := fun ζ hζ h => hPf ζ hζ (hP.mem_toFinset.1 h)
  have hA := tendsto_lintegral_capCutoff_comp (hfc.mono ball_subset_closedBall) hPf'
  have hB := tendsto_energy_capCutoff P'
  have hAB : Tendsto (fun r => 8 * ((∫⁻ ζ in ball (0 : ℂ) 1,
      ENNReal.ofReal (capCutoff P' r (f ζ) ^ 2)) +
        ∫⁻ z, ENNReal.ofReal (‖capCutoffDeriv P' r z‖ ^ 2))) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (hA.add hB) (Or.inr (by norm_num : (8 : ℝ≥0∞) ≠ ⊤))
    simpa using this
  have hcoeff : ∀ m : ℤ, diskCoeff F m = 0 := by
    intro m
    have hmain : ∀ η > 0, ∀ ε > 0,
        ‖diskCoeff F m‖ ≤ ε / 2 * S + (2 * ε)⁻¹ * ((1 + |(m : ℝ)|) * η) := by
      intro η hη ε hε
      obtain ⟨r, hr, hr01⟩ := ((hAB.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hη))).and
        (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))).exists
      obtain ⟨U, hU, hEU, ψ, hψc, hψs, hψ1, htr⟩ :=
        exists_test_capCutoff hfd hfi hfc P' hr01.1 hr01.2
      have hbd' : ∀ q : ℂ, ‖q‖ = 1 → q ∉ U → Tendsto u (𝓝[ball (0 : ℂ) 1] q) (𝓝 0) :=
        fun q hq hqU => hbd q (mem_sphere_zero_iff_norm.2 hq) fun hqP =>
          hqU (hEU q (mem_sphere_zero_iff_norm.2 hq) (hP.mem_toFinset.2 hqP))
      have h1 := norm_diskCoeff_le_of_test hF hu' hc hU hbd' hψc hψs hψ1 m hε
      have h2 : ∑' n : ℤ, (1 + |(n : ℝ)|) * ‖circCoeff ψ n‖ ^ 2 ≤ η :=
        (ENNReal.ofReal_le_ofReal_iff hη.le).1 (htr.trans hr.le)
      refine h1.trans ?_
      have : (0 : ℝ) ≤ (2 * ε)⁻¹ := by positivity
      gcongr
    by_contra hne
    have ha : 0 < ‖diskCoeff F m‖ := norm_pos_iff.2 hne
    set a := ‖diskCoeff F m‖
    set ε := a / (S + 1)
    have hε : 0 < ε := by positivity
    set M := 1 + |(m : ℝ)|
    have hM : 0 < M := by positivity
    set η := a * ε / (2 * M)
    have hη : 0 < η := by positivity
    have h := hmain η hη ε hε
    have h1 : ε / 2 * S = a / 2 * (S / (S + 1)) := by simp only [ε]; field_simp
    have h2 : S / (S + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have h3 : (2 * ε)⁻¹ * (M * η) = a / 4 := by simp only [η]; field_simp; ring
    have h4 : a / 2 * (S / (S + 1)) < a / 2 * 1 := mul_lt_mul_of_pos_left h2 (by positivity)
    linarith
  intro z hz
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hzp : polarPt ‖z‖ (Complex.arg z) = z := Complex.norm_mul_exp_arg_mul_I z
  have h := hasSum_diskCoeff hF (norm_nonneg z) hz1 (Complex.arg z)
  rw [hzp, hu' z hz] at h
  simp only [hcoeff, zero_mul] at h
  exact_mod_cast (hasSum_zero.unique h).symm

/-- **Aux. lemma 29** (first part). Let `f` be a conformal map of the unit disk onto an open set
`O`, continuous on the closed disk (its continuous extension), and `P ⊆ ∂O` finite. If `u` is
harmonic in `𝔻`, `u ∈ L²(𝔻)`, and `u` has continuous boundary value zero at every point of
`∂𝔻 \ f⁻¹(P)`, then `u = 0`. -/
theorem aux29_eqOn_zero {O : Set ℂ} (hOo : IsOpen O) {f : ℂ → ℂ}
    (hf : SupercriticalConformalCovariance.IsConformalBijection f (ball 0 1) O)
    (hfc : ContinuousOn f (closedBall 0 1)) {P : Set ℂ} (hP : P.Finite) (hPO : P ⊆ frontier O)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1))
    (hL2 : ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (u z ^ 2) ≠ ⊤)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, f q ∉ P → Tendsto u (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, u z = 0 := by
  refine aux29_eqOn_zero_disk hf.1 hf.2.injOn hfc hP (fun ζ hζ hfP => ?_) hu hL2 hbd
  have h1 : f ζ ∈ O := hf.2.mapsTo hζ
  have h2 : f ζ ∈ O ∩ frontier O := ⟨h1, hPO hfP⟩
  rw [hOo.inter_frontier_eq] at h2
  exact h2

/-! ## The final assertion of Aux. lemma 29 -/

open QuantumZipper.CA.Koebe SupercriticalConformalCovariance in
/-- The bounds of the proof of Aux. lemma 28 (as used in Aux. lemma 29: "the Koebe quarter theorem
and derivative distortion estimate used in Aux. lemma 28 give … `H ∘ f = O((1 − |ζ|)^{−2ε})` …
The logarithmic derivative estimate in that same lemma gives `F ∘ f = O(1 + log(1/(1 − |ζ|)))`"):
`(H − F) ∘ f` is harmonic on the disk and `O((1 − |ζ|)^{−1/4})`. -/
theorem harmonicOnNhd_and_growth_comp {C : Set ℂ} (hCo : IsOpen C) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {Hh : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd Hh C)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ z ∈ C,
      |Hh z| ≤ Cε * (1 + infDist z (frontier C) ^ (-ε)))
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ C {w : ℂ | 0 < w.im})
    {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g {w : ℂ | 0 < w.im})
    (hgb : ∃ M, ∀ w : ℂ, 0 < w.im → |g w| ≤ M) (χ : ℝ) {A : ℂ → ℝ} (hAc : ContinuousOn A C)
    (hA : ∀ z ∈ C, deriv φ z = ‖deriv φ z‖ * exp (A z * I)) :
    InnerProductSpace.HarmonicOnNhd (fun ζ => Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))) (ball 0 1) ∧
      ∃ C' : ℝ, ∀ ζ ∈ ball (0 : ℂ) 1,
        |Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))| ≤ C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨hfd, hfb⟩ := hf
  have hfinj := hfb.injOn
  have hfim : f '' ball 0 1 = C := hfb.image_eq
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  -- the derivative lifts
  have hL := isDerivLog_of_arg_branch hCo hφ hAc hA
  set L := fun z => (Real.log ‖deriv φ z‖ : ℂ) + (A z : ℂ) * I
  obtain ⟨ℓf, hℓf⟩ := exists_isDerivLog isOpen_ball isSimplyConnected_unitBall hfd
    (fun ζ hζ => QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hζ)
  have hLm := IsDerivLog.comp isOpen_ball hCo hφ.1 hfd hfb.mapsTo hL hℓf
  have hmd : DifferentiableOn ℂ (φ ∘ f) (ball 0 1) := hφ.1.comp hfd hfb.mapsTo
  have hminj : InjOn (φ ∘ f) (ball 0 1) := hφ.2.injOn.comp hfinj hfb.mapsTo
  -- `A ∘ f = Im (L_m − ℓ_f)`
  have hAf : ∀ ζ ∈ ball (0 : ℂ) 1, A (f ζ) = (L (f ζ) + ℓf ζ - ℓf ζ).im := by
    intro ζ _
    simp [L]
  -- growth of `A ∘ f`
  set K₀ := ‖(L (f 0) + ℓf 0) - ℓf 0‖
  have hAgrowth : ∀ ζ ∈ ball (0 : ℂ) 1,
      |A (f ζ)| ≤ K₀ + 2 * koebeDistExp * (-Real.log (1 - ‖ζ‖)) := by
    intro ζ hζ
    have h1 := norm_derivLog_sub_le hmd hminj hLm hζ
    have h2 := norm_derivLog_sub_le hfd hfinj hℓf hζ
    rw [hAf ζ hζ]
    refine (Complex.abs_im_le_norm _).trans ?_
    calc ‖L (f ζ) + ℓf ζ - ℓf ζ‖
        = ‖((L (f ζ) + ℓf ζ) - (L (f 0) + ℓf 0)) - (ℓf ζ - ℓf 0) +
            ((L (f 0) + ℓf 0) - ℓf 0)‖ := by ring_nf
      _ ≤ ‖(L (f ζ) + ℓf ζ) - (L (f 0) + ℓf 0)‖ + ‖ℓf ζ - ℓf 0‖ + K₀ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ _ := by simp only [L] at h1 ⊢; linarith
  -- Koebe: distance to the boundary
  have hCne : C.Nonempty := ⟨f 0, hfb.mapsTo hball0⟩
  have hCuniv : C ≠ univ := hfim ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos hfd hfinj
  set κ := koebeCovConst * ‖deriv f 0‖
  have hκ : 0 < κ := mul_pos koebeCovConst_pos
    (norm_pos_iff.2 (QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hball0))
  have hdist : ∀ ζ ∈ ball (0 : ℂ) 1,
      κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp) ≤ infDist (f ζ) (frontier C) := by
    intro ζ hζ
    have := koebe_mul_pow_le_infDist hfd hfinj hζ
    rw [hfim] at this
    exact this.trans (infDist_compl_le_infDist_frontier hCo hCne hCuniv _)
  -- the subpower bound for `H ∘ f`
  set ε₀ : ℝ := 1 / (4 * (1 + koebeDistExp))
  have hε₀ : 0 < ε₀ := by have := koebeDistExp_pos; positivity
  obtain ⟨Cε, hCε⟩ := hgrowth ε₀ hε₀
  have hHgrowth : ∀ ζ ∈ ball (0 : ℂ) 1,
      |Hh (f ζ)| ≤ |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
    intro ζ hζ
    have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hpow0 : 0 < κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp) := by positivity
    have hd := hdist ζ hζ
    have h1 : infDist (f ζ) (frontier C) ^ (-ε₀) ≤ (κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp)) ^ (-ε₀) :=
      Real.rpow_le_rpow_of_nonpos hpow0 hd (by linarith)
    have h2 : (κ * (1 - ‖ζ‖) ^ (1 + koebeDistExp)) ^ (-ε₀) =
        κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.mul_rpow hκ.le (by positivity), ← Real.rpow_mul hr.le]
      congr 2
      simp only [ε₀]
      have := koebeDistExp_pos
      field_simp
    have h3 : 1 ≤ (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
    have hfz : f ζ ∈ C := hfb.mapsTo hζ
    have h4 := hCε (f ζ) hfz
    have hκp : 0 ≤ κ ^ (-ε₀) := by positivity
    calc |Hh (f ζ)| ≤ Cε * (1 + infDist (f ζ) (frontier C) ^ (-ε₀)) := h4
      _ ≤ |Cε| * (1 + infDist (f ζ) (frontier C) ^ (-ε₀)) := by
          have : 0 ≤ 1 + infDist (f ζ) (frontier C) ^ (-ε₀) := by
            have := Real.rpow_nonneg (infDist_nonneg (x := f ζ) (s := frontier C)) (-ε₀)
            linarith
          exact mul_le_mul_of_nonneg_right (le_abs_self _) this
      _ ≤ |Cε| * (1 + κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
          gcongr; rw [← h2]; exact h1
      _ ≤ |Cε| * ((1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) + κ ^ (-ε₀) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
          gcongr
      _ = |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by ring
  -- the total bound
  obtain ⟨M, hM⟩ := hgb
  set u : ℂ → ℝ := fun ζ => Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))
  set C' := |Cε| * (1 + κ ^ (-ε₀)) + |M| + |χ| * (K₀ + 8 * koebeDistExp)
  have hugrowth : ∀ ζ ∈ ball (0 : ℂ) 1, |u ζ| ≤ C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
    intro ζ hζ
    have hr : 0 < 1 - ‖ζ‖ := by have := mem_ball_zero_iff.1 hζ; linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hP : 1 ≤ (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
    have hlog := neg_log_le_four_mul_rpow hr
    have hgz : |g (φ (f ζ))| ≤ M := hM _ (hφ.2.mapsTo (hfb.mapsTo hζ))
    have hAz := hAgrowth ζ hζ
    have hH := hHgrowth ζ hζ
    have hK₀ : 0 ≤ K₀ := norm_nonneg _
    have hC2 := koebeDistExp_pos
    have hA' : |A (f ζ)| ≤ (K₀ + 8 * koebeDistExp) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by
      calc |A (f ζ)| ≤ K₀ + 2 * koebeDistExp * (-Real.log (1 - ‖ζ‖)) := hAz
        _ ≤ K₀ * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) +
            2 * koebeDistExp * (4 * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) := by
            gcongr
            · nlinarith
        _ = _ := by ring
    simp only [u]
    calc |Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))|
        ≤ |Hh (f ζ)| + (|g (φ (f ζ))| + |χ| * |A (f ζ)|) := by
          rw [← abs_mul]
          exact (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ ≤ |Cε| * (1 + κ ^ (-ε₀)) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) +
          (|M| * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) +
            |χ| * ((K₀ + 8 * koebeDistExp) * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)))) := by
          gcongr
          · exact hgz.trans ((le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg _) hP))
      _ = C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ)) := by simp only [C']; ring
  -- harmonicity of `u`
  have hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1) := by
    intro ζ hζ
    have hfa : AnalyticAt ℂ f ζ := hfd.analyticAt (isOpen_ball.mem_nhds hζ)
    have hfz : f ζ ∈ C := hfb.mapsTo hζ
    have hφa : AnalyticAt ℂ φ (f ζ) := hφ.1.analyticAt (hCo.mem_nhds hfz)
    have h1 : InnerProductSpace.HarmonicAt (Hh ∘ f) ζ :=
      QuantumZipper.FieldLawler.fl_harmonicAt_comp hfa (hH _ hfz)
    have h2 : InnerProductSpace.HarmonicAt (g ∘ (φ ∘ f)) ζ :=
      QuantumZipper.FieldLawler.fl_harmonicAt_comp (hφa.comp hfa) (hg _ (hφ.2.mapsTo hfz))
    have h3 : InnerProductSpace.HarmonicAt (fun ζ => (L (f ζ) + ℓf ζ - ℓf ζ).im) ζ := by
      have : AnalyticAt ℂ (fun ζ => L (f ζ) + ℓf ζ - ℓf ζ) ζ :=
        (hLm.1.sub hℓf.1).analyticAt (isOpen_ball.mem_nhds hζ)
      exact this.harmonicAt_im
    have h3' : InnerProductSpace.HarmonicAt (fun ζ => χ * A (f ζ)) ζ := by
      have h := h3.const_smul (c := χ)
      refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h
      filter_upwards [isOpen_ball.mem_nhds hζ] with w hw
      simp only [Pi.smul_apply, smul_eq_mul, hAf w hw]
    exact h1.sub (h2.sub h3')
  exact ⟨hu, C', hugrowth⟩

/-- `(1 − |ζ|)^{−1/2}` is integrable on the disk ("Both bounds are square integrable against disk
area near the unit circle"). -/
theorem lintegral_ball_rpow_ne_top :
    ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal ((1 - ‖z‖) ^ (-(1 / 2 : ℝ))) ≠ ⊤ := by
  have hm : Measurable fun z : ℂ => ENNReal.ofReal ((1 - ‖z‖) ^ (-(1 / 2 : ℝ))) :=
    ((measurable_const.sub measurable_norm).pow_const _).ennreal_ofReal
  rw [lintegral_ball_eq_polar hm]
  have hin : ∀ ρ ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal ρ * ∫⁻ t in Ioo (-π) π,
      ENNReal.ofReal ((1 - ‖polarPt ρ t‖) ^ (-(1 / 2 : ℝ))) ≤
        ENNReal.ofReal (2 * π) * ENNReal.ofReal ((1 - ρ) ^ (-(1 / 2 : ℝ))) := by
    intro ρ hρ
    have hc : ∀ t : ℝ, ENNReal.ofReal ((1 - ‖polarPt ρ t‖) ^ (-(1 / 2 : ℝ))) =
        ENNReal.ofReal ((1 - ρ) ^ (-(1 / 2 : ℝ))) := fun t => by rw [norm_polarPt hρ.1.le]
    simp_rw [hc]
    rw [setLIntegral_const, Real.volume_Ioo, show π - -π = 2 * π by ring]
    calc ENNReal.ofReal ρ * (ENNReal.ofReal ((1 - ρ) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (2 * π))
        ≤ 1 * (ENNReal.ofReal ((1 - ρ) ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal (2 * π)) :=
          mul_le_mul' (ENNReal.ofReal_le_one.2 hρ.2.le) le_rfl
      _ = _ := by rw [one_mul, mul_comm]
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioo hin)
  rw [lintegral_const_mul _ (show Measurable fun x : ℝ => ENNReal.ofReal ((1 - x) ^ (-(1 / 2 : ℝ)))
    from ((measurable_const.sub measurable_id).pow_const _).ennreal_ofReal)]
  refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 1 0 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 := h1.comp_sub_left 1
  simp only [sub_self, sub_zero] at h2
  have h3 := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 h2
  exact (Integrable.lintegral_lt_top h3).ne

/-- A harmonic function on the disk with `|u| ≤ C (1 − |ζ|)^{−1/4}` is in `L²(𝔻)`. -/
theorem lintegral_sq_ne_top_of_growth {u : ℂ → ℝ} {C' : ℝ}
    (hg : ∀ ζ ∈ ball (0 : ℂ) 1, |u ζ| ≤ C' * (1 - ‖ζ‖) ^ (-(1 / 4 : ℝ))) :
    ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (u z ^ 2) ≠ ⊤ := by
  have hle : ∀ z ∈ ball (0 : ℂ) 1, ENNReal.ofReal (u z ^ 2) ≤
      ENNReal.ofReal (C' ^ 2) * ENNReal.ofReal ((1 - ‖z‖) ^ (-(1 / 2 : ℝ))) := by
    intro z hz
    have hr : 0 < 1 - ‖z‖ := by have := mem_ball_zero_iff.1 hz; linarith
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hg z hz
    have h0 : 0 ≤ C' * (1 - ‖z‖) ^ (-(1 / 4 : ℝ)) := (abs_nonneg _).trans h
    have hsq : u z ^ 2 ≤ (C' * (1 - ‖z‖) ^ (-(1 / 4 : ℝ))) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hpow : ((1 - ‖z‖) ^ (-(1 / 4 : ℝ))) ^ 2 = (1 - ‖z‖) ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; norm_num
    calc u z ^ 2 ≤ (C' * (1 - ‖z‖) ^ (-(1 / 4 : ℝ))) ^ 2 := hsq
      _ = C' ^ 2 * (1 - ‖z‖) ^ (-(1 / 2 : ℝ)) := by rw [mul_pow, hpow]
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_ball hle)
  rw [lintegral_const_mul _ (show Measurable fun z : ℂ => ENNReal.ofReal ((1 - ‖z‖) ^ (-(1 / 2 : ℝ)))
    from ((measurable_const.sub measurable_norm).pow_const _).ennreal_ofReal)]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top lintegral_ball_rpow_ne_top

open SupercriticalConformalCovariance in
/-- **Aux. lemma 29** (final assertion). Let `f` be a conformal map of the unit disk onto an open
set `O`, continuous on the closed disk, and `P ⊆ ∂O` finite. Let `H` be harmonic in `O` with
`|H(z)| ≤ C_ε (1 + dist(z, ∂O)^{−ε})` for every `ε > 0`, `φ : O → ℍ` conformal, `g` bounded
harmonic in `ℍ`, `χ` real, and `A` a continuous branch of `arg φ'` on `O`; put
`F = g ∘ φ − χ A`. If `(H − F) ∘ f` has continuous boundary value zero at every point of
`∂𝔻 \ f⁻¹(P)`, then `H = F` on `O`. (There is no assumption that the number of prime ends over a
point of `P` is finite.) -/
theorem aux29_eqOn_of_tendsto {O : Set ℂ} (hOo : IsOpen O) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) O) (hfc : ContinuousOn f (closedBall 0 1))
    {P : Set ℂ} (hP : P.Finite) (hPO : P ⊆ frontier O) {Hh : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd Hh O)
    (hgrowth : ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, ∀ z ∈ O,
      |Hh z| ≤ Cε * (1 + infDist z (frontier O) ^ (-ε)))
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ O {w : ℂ | 0 < w.im})
    {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g {w : ℂ | 0 < w.im})
    (hgb : ∃ M, ∀ w : ℂ, 0 < w.im → |g w| ≤ M) (χ : ℝ) {A : ℂ → ℝ} (hAc : ContinuousOn A O)
    (hA : ∀ z ∈ O, deriv φ z = ‖deriv φ z‖ * exp (A z * I))
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, f q ∉ P →
      Tendsto (fun ζ => Hh (f ζ) - (g (φ (f ζ)) - χ * A (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) :
    ∀ z ∈ O, Hh z = g (φ z) - χ * A z := by
  obtain ⟨hu, C', hC'⟩ := harmonicOnNhd_and_growth_comp hOo hf hH hgrowth hφ hg hgb χ hAc hA
  have h0 := aux29_eqOn_zero hOo hf hfc hP hPO hu (lintegral_sq_ne_top_of_growth hC') hbd
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hf.2.surjOn hz
  have := h0 ζ hζ
  linarith

end InteractingSLE.Sec6
