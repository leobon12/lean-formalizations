import QuantumZipper.Proofs.RS.OnePointFinal
import QuantumZipper.Proofs.RS.GenerationCor

/-!
# The one-point estimate (DU6) for ordinary chordal SLE_κ, `0 < κ < 8`

Specification, Aux. lemma 14 and its proof (`source/spec/p049-096.md`, lines 794–848, p. 86–88):
for `z ∈ ℍ` and `0 < r < Im z / 4`,

`P[dist(z, γ) < r] ≤ C_κ (r / Im z)^{β_κ}`   (DU6).

The specification derives (DU6) from the angle diffusion of `arg (g_t(z) − W_t)` in the
conformal-radius clock ((DU1)–(DU5)) and the observation that an approach of the trace to `z` is
detected before `z` is swallowed, also for non-simple traces. QuantumZipper already proves the
conformal-radius tail bound for every `0 < κ < 8` (`QuantumZipper.RS.prob_logCR_lt_unif`, the
upper bound of Lawler–Zhou, arXiv:1006.4936, Prop. 2.3, whose proof runs the same angle diffusion
through a barrier function): with `Υ_t = Im g_t(z) / |g_t'(z)|`,

`P[∃ t, z ∉ K_t ∧ Υ_t < r] ≤ C (r / Im z)^{1 − κ/8} (Im z / |z|)^{8/κ − 1}`,

so (DU1)–(DU5) are not reproved here: (DU6) holds with the exponent `β_κ = 1 − κ/8`
(`onePointExponent`). This file proves

* `exists_notMem_fwdHull_dist_trace_lt` — the deterministic "approach before swallowing" step
  (spec. p. 88): if the continuous trace generates the hulls and comes within distance `r ≤ Im z`
  of `z` at some time, then it does so at a time before `z` is swallowed. If `z` is swallowed at
  `σ` while `γ[0, σ]` stays at distance `≥ r`, the disc `B(z, r)` is trace-free, hence lies in the
  bounded part `K_σ`, and every later trace point is a limit of points of `ℍ \ K_t ⊆ ℍ \ K_σ`;
* `prob_infDist_sleTrace_lt` — (DU6) for every `r > 0` (the range `r ≥ c Im z` is trivial after
  enlarging the constant), from the step above, the half-plane Koebe estimate
  `c₀ Υ_t ≤ dist(z, γ(t))` (`QuantumZipper.RS.koebe_logCR_le_dist`) and the tail bound.
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Dimension

open QuantumZipper QuantumZipper.RS

/-- **Approach before swallowing** (specification p. 88, proof of Aux. lemma 14). For a continuous
driving function whose trace is continuous and is the locally uniform radial limit, if the trace
comes within distance `r ≤ Im z` of `z ∈ ℍ`, then it does so at a time `t` at which `z` is not yet
swallowed. -/
theorem exists_notMem_fwdHull_dist_trace_lt {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hcont : ContinuousOn (trace W) (Ici 0))
    (hunif : ∀ t : ℝ, 0 ≤ t → TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * Complex.I))
      (trace W) (𝓝[>] 0) (Icc 0 t))
    {z : ℂ} (hz : z ∈ H) {r : ℝ} (hrz : r ≤ z.im) {s : ℝ} (hs : 0 ≤ s)
    (hzs : dist z (trace W s) < r) :
    ∃ t : ℝ, 0 ≤ t ∧ z ∉ fwdHull W t ∧ dist z (trace W t) < r := by
  by_contra hcon
  push Not at hcon
  have hzim : 0 < z.im := hz
  have hr0 : 0 < r := lt_of_le_of_lt dist_nonneg hzs
  -- `z` is swallowed by time `s`
  have hzK : z ∈ fwdHull W s := by
    by_contra h
    exact absurd (hcon s hs h) (not_le.2 hzs)
  have hTle : swallowTime W z ≤ ENNReal.ofReal s := hzK.2
  have hTne : swallowTime W z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hTle
  set σ : ℝ := (swallowTime W z).toReal with hσdef
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  have hσs : σ ≤ s := ENNReal.toReal_le_of_le_ofReal hs hTle
  have hTσ : swallowTime W z = ENNReal.ofReal σ := (ENNReal.ofReal_toReal hTne).symm
  have hzKσ : z ∈ fwdHull W σ := ⟨hz, hTσ.le⟩
  have hσpos : 0 < σ := by
    have h := swallowTime_pos (z := z) hW hzim
    rw [hTσ] at h
    exact ENNReal.ofReal_pos.1 h
  -- before `σ`, `z` is not swallowed, so the trace stays at distance `≥ r`
  have hbefore : ∀ t ∈ Ico 0 σ, r ≤ dist z (trace W t) := by
    rintro t ⟨ht0, htσ⟩
    refine hcon t ht0 fun hmem => ?_
    have h1 : ENNReal.ofReal σ ≤ ENNReal.ofReal t := hTσ ▸ hmem.2
    exact absurd ((ENNReal.ofReal_le_ofReal_iff ht0).1 h1) (not_le.2 htσ)
  -- by continuity also at `σ`
  have hatσ : r ≤ dist z (trace W σ) := by
    have hcw : ContinuousWithinAt (fun t => dist z (trace W t)) (Ico 0 σ) σ :=
      (continuous_const.dist continuous_id).continuousAt.comp_continuousWithinAt
        ((hcont σ hσ0).mono Ico_subset_Ici_self)
    have hcl : σ ∈ closure (Ico 0 σ) := by
      rw [closure_Ico hσpos.ne]
      exact ⟨hσ0, le_rfl⟩
    exact ContinuousWithinAt.closure_le hcl continuousWithinAt_const hcw hbefore
  have hupto : ∀ t ∈ Icc 0 σ, r ≤ dist z (trace W t) := by
    rintro t ⟨ht0, htσ⟩
    rcases htσ.lt_or_eq with h | h
    · exact hbefore t ⟨ht0, h⟩
    · exact h ▸ hatσ
  -- the disc `B(z, r)` lies in `K_σ`
  have hballH : ball z r ⊆ H := by
    intro w hw
    have h1 : |w.im - z.im| < r := by
      calc |w.im - z.im| = |(w - z).im| := by rw [Complex.sub_im]
        _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
        _ = dist w z := (dist_eq_norm w z).symm
        _ < r := hw
    show 0 < w.im
    have := (abs_lt.1 h1).1
    linarith
  have hball_tr : ball z r ⊆ H \ trace W '' Icc 0 σ := by
    intro w hw
    refine ⟨hballH hw, ?_⟩
    rintro ⟨t, ht, rfl⟩
    have h1 := hupto t ht
    rw [mem_ball, dist_comm] at hw
    exact absurd hw (not_lt.2 h1)
  have hball : ball z r ⊆ fwdHull W σ := by
    intro w hw
    by_contra hwK
    have hcc := compl_fwdHull_eq_connectedComponentIn hW hW0 hσ0 (hunif σ hσ0)
      (hcont.mono Icc_subset_Ici_self) (x := w) ⟨hballH hw, hwK⟩
    have hsub : ball z r ⊆ connectedComponentIn (H \ trace W '' Icc 0 σ) w :=
      isPreconnected_ball.subset_connectedComponentIn hw hball_tr
    have hzc : z ∈ H \ fwdHull W σ := hcc ▸ hsub (mem_ball_self hr0)
    exact hzc.2 hzKσ
  -- after `σ`, the trace is a limit of points of `ℍ \ K_t ⊆ ℍ \ K_σ`
  have hafter : r ≤ dist z (trace W s) := by
    have hlim : Tendsto (fun y : ℝ => fwdMapInv W s (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (trace W s)) := (hunif s hs).tendsto_at ⟨hs, le_rfl⟩
    have hev : ∀ᶠ y : ℝ in 𝓝[>] 0, r ≤ dist z (fwdMapInv W s (y * Complex.I)) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyH : (y : ℂ) * Complex.I ∈ H := by
        show 0 < ((y : ℂ) * Complex.I).im
        simpa using (hy : (0 : ℝ) < y)
      have hmem : fwdMapInv W s (y * Complex.I) ∈ H \ fwdHull W s := by
        rw [← image_fwdMapInv_H hW hW0 hs]
        exact mem_image_of_mem _ hyH
      have hnot : fwdMapInv W s (y * Complex.I) ∉ fwdHull W σ := fun h =>
        hmem.2 (fwdHull_mono.1 hσs h)
      by_contra hlt
      push Not at hlt
      exact hnot (hball (by rw [mem_ball, dist_comm]; exact hlt))
    exact ge_of_tendsto (tendsto_const_nhds.dist hlim) hev
  exact absurd hzs (not_lt.2 hafter)

/-- The exponent `β_κ = 1 − κ/8` of the one-point estimate (DU6). -/
def onePointExponent (κ : ℝ) : ℝ := 1 - κ / 8

theorem onePointExponent_pos {κ : ℝ} (hκ8 : κ < 8) : 0 < onePointExponent κ := by
  unfold onePointExponent; linarith

theorem onePointExponent_le_one {κ : ℝ} (hκ : 0 < κ) : onePointExponent κ ≤ 1 := by
  unfold onePointExponent; linarith

/-- On the almost sure event of `QuantumZipper.RS.ae_sleTrace_good`, the radial convergence is
uniform on every compact time interval. -/
theorem tendstoUniformlyOn_of_rpow_bound {W : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hb : ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t (y * Complex.I) - trace W t‖ ≤ C * y ^ δ) (t : ℝ) :
    TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * Complex.I)) (trace W)
      (𝓝[>] 0) (Icc 0 t) := by
  obtain ⟨C, hC⟩ := hb ⌈t⌉₊
  exact tendstoUniformlyOn_fwdMapInv_mul_I_of_bound hδ fun s hs y hy =>
    hC s ⟨hs.1, hs.2.trans (Nat.le_ceil t)⟩ y hy

/-- **(DU6), the one-point estimate for ordinary chordal SLE_κ, `0 < κ < 8`** (specification p. 88).
There is `C` depending only on `κ` such that for every Brownian motion `B`, every `z ∈ ℍ` and every
`r > 0`, `P[dist(z, γ) < r] ≤ C (r / Im z)^{β_κ}`, with `γ = sleTrace κ B` and `β_κ = 1 − κ/8`.
The set need not be measurable; `P` is the outer measure. -/
theorem prob_infDist_sleTrace_lt {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ z ∈ H, ∀ r : ℝ, 0 < r →
        P {ω | infDist z (sleTrace κ B ω '' Ici 0) < r}
          ≤ ENNReal.ofReal (C * (r / z.im) ^ onePointExponent κ) := by
  obtain ⟨C₀, hC₀⟩ := prob_logCR_lt_unif hκ hκ8
  set β := onePointExponent κ with hβ
  have hβ0 : 0 < β := onePointExponent_pos hκ8
  set c := CA.Koebe.koebeCovConst with hc
  have hc0 : 0 < c := CA.Koebe.koebeCovConst_pos
  set c₁ := c / 2 with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  refine ⟨max C₀ 0 * (c ^ β)⁻¹ + (c₁ ^ β)⁻¹, by positivity, ?_⟩
  intro Ω _ P _ B hB z hz r hr
  have hzim : 0 < z.im := hz
  have hrz0 : 0 < r / z.im := div_pos hr hzim
  have hpow0 : 0 ≤ (r / z.im) ^ β := Real.rpow_nonneg hrz0.le _
  rcases le_or_gt r (c₁ * z.im) with hsmall | hlarge
  · -- the main case `r ≤ c₁ Im z`
    obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good hB hκ hκ8
    have hrc : 0 < r / c := div_pos hr hc0
    have hrcz : r / c ≤ z.im / 2 := by
      rw [div_le_iff₀ hc0]
      calc r ≤ c₁ * z.im := hsmall
        _ = z.im / 2 * c := by rw [hc₁]; ring
    have h := hC₀ P B hB z hz (r / c) hrc hrcz
    have hsub : {ω | infDist z (sleTrace κ B ω '' Ici 0) < r} ≤ᵐ[P]
        {ω | ∃ t ≥ (0 : ℝ), z ∉ fwdHull (drive κ B ω) t ∧
          Real.exp (FwdClock.fwdLogCR (drive κ B ω) t z) < r / c} := by
      filter_upwards [hgood, hB.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero]
        with ω hω hcontB h0
      intro hω'
      set W := drive κ B ω with hWdef
      have hW : Continuous W := drive_continuous hcontB
      have hW0 : W 0 = 0 := drive_zero h0
      have hne : (sleTrace κ B ω '' Ici 0).Nonempty := ⟨_, mem_image_of_mem _ (mem_Ici.2 le_rfl)⟩
      obtain ⟨q, ⟨s, hs, rfl⟩, hq⟩ := (infDist_lt_iff hne).1 hω'
      have hunif := tendstoUniformlyOn_of_rpow_bound hδ hω.2.2
      have hrz : r ≤ z.im := by
        have : c₁ ≤ 1 := by rw [hc₁, hc]; unfold CA.Koebe.koebeCovConst; norm_num
        nlinarith
      obtain ⟨t, ht0, htK, htd⟩ := exists_notMem_fwdHull_dist_trace_lt hW hW0 hω.2.1 (fun t _ => hunif t)
        hz hrz (s := s) hs hq
      have hlim : Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0)
          (𝓝 (trace W t)) := (hunif t).tendsto_at ⟨ht0, le_rfl⟩
      have hk := koebe_logCR_le_dist hW hW0 ht0 hlim ⟨hz, htK⟩
      refine ⟨t, ht0, htK, ?_⟩
      rw [lt_div_iff₀ hc0, mul_comm]
      exact lt_of_le_of_lt hk htd
    refine (measure_mono_ae hsub).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
    -- `C₀ (r/(c Im z))^β (Im z/|z|)^p ≤ max C₀ 0 · c^{-β} (r/Im z)^β`
    have hp0 : 0 ≤ 8 / κ - 1 := by
      rw [sub_nonneg, le_div_iff₀ hκ]; linarith
    have hq0 : 0 ≤ z.im / ‖z‖ := div_nonneg hzim.le (norm_nonneg z)
    have hq1 : z.im / ‖z‖ ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le hzim (Complex.im_le_norm z))]
      exact Complex.im_le_norm z
    have hqp0 : 0 ≤ (z.im / ‖z‖) ^ (8 / κ - 1) := Real.rpow_nonneg hq0 _
    have hqp1 : (z.im / ‖z‖) ^ (8 / κ - 1) ≤ 1 := Real.rpow_le_one hq0 hq1 hp0
    have hsplit : (r / c / z.im) ^ (1 - κ / 8) = (c ^ β)⁻¹ * (r / z.im) ^ β := by
      rw [show r / c / z.im = (r / z.im) / c by ring, Real.div_rpow hrz0.le hc0.le]
      rw [hβ, onePointExponent]; ring
    rw [hsplit]
    have hcβ : 0 ≤ (c ^ β)⁻¹ := by positivity
    have hA : 0 ≤ (c ^ β)⁻¹ * (r / z.im) ^ β := mul_nonneg hcβ hpow0
    calc C₀ * ((c ^ β)⁻¹ * (r / z.im) ^ β) * (z.im / ‖z‖) ^ (8 / κ - 1)
        ≤ max C₀ 0 * ((c ^ β)⁻¹ * (r / z.im) ^ β) * 1 := by
          have h1 : C₀ * ((c ^ β)⁻¹ * (r / z.im) ^ β) ≤ max C₀ 0 * ((c ^ β)⁻¹ * (r / z.im) ^ β) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hA
          have h2 : 0 ≤ max C₀ 0 * ((c ^ β)⁻¹ * (r / z.im) ^ β) :=
            mul_nonneg (le_max_right _ _) hA
          calc C₀ * ((c ^ β)⁻¹ * (r / z.im) ^ β) * (z.im / ‖z‖) ^ (8 / κ - 1)
              ≤ max C₀ 0 * ((c ^ β)⁻¹ * (r / z.im) ^ β) * (z.im / ‖z‖) ^ (8 / κ - 1) :=
                mul_le_mul_of_nonneg_right h1 hqp0
            _ ≤ max C₀ 0 * ((c ^ β)⁻¹ * (r / z.im) ^ β) * 1 :=
                mul_le_mul_of_nonneg_left hqp1 h2
      _ ≤ (max C₀ 0 * (c ^ β)⁻¹ + (c₁ ^ β)⁻¹) * (r / z.im) ^ β := by
          have : 0 ≤ (c₁ ^ β)⁻¹ * (r / z.im) ^ β := mul_nonneg (by positivity) hpow0
          nlinarith
  · -- the trivial case `r > c₁ Im z`: the right side is at least `1`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hc₁z : c₁ < r / z.im := by rw [lt_div_iff₀ hzim]; exact hlarge
    have h1 : c₁ ^ β ≤ (r / z.im) ^ β := Real.rpow_le_rpow hc₁0.le hc₁z.le hβ0.le
    have h2 : 0 < c₁ ^ β := Real.rpow_pos_of_pos hc₁0 _
    have h3 : 1 ≤ (c₁ ^ β)⁻¹ * (r / z.im) ^ β := by
      rw [← div_eq_inv_mul, one_le_div h2]; exact h1
    have h4 : 0 ≤ max C₀ 0 * (c ^ β)⁻¹ * (r / z.im) ^ β := by positivity
    nlinarith

end InteractingSLE.Dimension
