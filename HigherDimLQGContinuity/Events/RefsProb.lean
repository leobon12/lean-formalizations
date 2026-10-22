import HigherDimLQGContinuity.Events.Profile
import HigherDimLQGContinuity.Witness.Refs
import HigherDimLQGMetric.Config.Tight
import HigherDimLQGMetric.Config.Geometry

/-!
# Lemma `a:lem-refs-prob`: the references have high probability (packet P5b)

Packet P5b, target `refs_prob`. Source: blueprint Part A, Lemma `a:lem-refs-prob` ([C] p. 6, l. 267), Definition
`a:def-refs`; planning audit NA1, item 20; interface audit IA1, N-7 (the producer supplies the ranges
`0 < σ₀ < 1 < β₀`, `0 < m < M`, `1 ≤ H₀` of the reference constants). Consumed interface: I1, `UniformEstimates d ξ̄ s`
(Lemma 2.1, taken as a hypothesis; its producer is the Appendix-A chain).

**Statement.** If `UniformEstimates d ξ̄ s` holds (`d ≥ 2`, `s > 0`), then for every `p > 0` there are reference
constants `(H₀, σ₀, β₀, m, M)` with `0 < σ₀ < 1 < β₀`, `0 < m < M`, `1 ≤ H₀` such that
`𝐏ₛ(PairRefs(D, E; 𝓡)ᶜ) ≤ p` for all `ξ, η ∈ (0, ξ̄]` and all `D`, `E` strong at `(ξ, Q(ξ))`, `(η, Q(η))`.

**Proof** (blueprint, with explicit constants). For one metric, with `ε = p/2` and `ε' = ε/4`:
* (lower), (upper): the envelope (E1) at `R = 2` gives `H` with `∫ H^{p₁} ≤ C 3^A`; on `{H ≤ t₀}`,
  `t₀ = max(1, (C 3^A/ε')^{1/p₁})`, the lower bound holds with `H₀ = 2 t₀` (`ρ_A ≥ ρ ≥ H⁻¹|x - y|^β`), and the upper bound
  at close points (`|x - y| ≤ 1/64`) holds with `H₀` via the ball `B_{2r}(x) ⊆ A`, `r = 2|x - y|`
  (`ρ_A(x, y) ≤ diam_{B_{2r}(x)} B_r(x) ≤ H r^σ ≤ 2 t₀ |x - y|^σ`); Markov: `𝐏ₛ(H > t₀) ≤ ε'`.
* (cross): (E2) with `q = 1` and `setDistIn ρ A ≥ setDistIn ρ ℝ^d`; Markov on the inverse crossing with
  `m = ε'/max(K₁, 1)`.
* (diam), (diamK): (E3) with `U = A` (open, bounded, connected for `d ≥ 2`) and `K_c = ∂B₁`, `K`; Markov with
  `M = max(m + 1, (max(K₂, K₃, 1)/ε')^{1/p₊})`.
Union bound over the four failures of each metric: `𝐏ₛ(PairRefsᶜ) ≤ 2 · 4 ε' = p`.

The integrands of (E2), (E3) are a.e.-measurable because `ρ^D_g` is almost surely a length metric
(`internal_univ_of_isLength`, `aemeasurable_diamIn_of_ae_length`); Markov's inequality is applied to them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Markov's inequality in the form used here -/

/-- Markov's inequality with real bounds. -/
theorem p5b_markov {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {I c : ℝ} (hc : 0 < c) (hI : ∫⁻ x, f x ∂μ ≤ ENNReal.ofReal I) :
    μ {x | ENNReal.ofReal c ≤ f x} ≤ ENNReal.ofReal (I / c) := by
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 hc).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact (mul_meas_ge_le_lintegral₀ hf _).trans hI

/-! ## Geometry -/

theorem p5b_annCl_subset_closedBall_two : annCl (0 : Rd d) (5 / 8) (3 / 2) ⊆ closedBall (0 : Rd d) 2 := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have := hx.2
  rw [sub_zero] at this
  linarith

/-- For `x ∈ annCl 0 (5/8) (3/2)` and `ρ ≤ 1/16`, the ball `B_ρ(x)` lies in `A`. -/
theorem p5b_ball_subset_annA {x : Rd d} (hx : x ∈ annCl (0 : Rd d) (5 / 8) (3 / 2)) {ρ : ℝ}
    (hρ : ρ ≤ 1 / 16) : ball x ρ ⊆ annA d := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  have hx1 : 5 / 8 ≤ ‖x‖ := by simpa using hx.1
  have hx2 : ‖x‖ ≤ 3 / 2 := by simpa using hx.2
  have h1 : ‖x‖ ≤ ‖w‖ + ‖w - x‖ := by
    calc ‖x‖ = ‖w - (w - x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖w‖ + ‖w - x‖ := norm_sub_le _ _
  have h2 : ‖w‖ ≤ ‖x‖ + ‖w - x‖ := by
    calc ‖w‖ = ‖x + (w - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖w - x‖ := norm_add_le _ _
  rw [mem_annA_iff]
  constructor <;> linarith

theorem p5b_sphere_one_subset_annA : sphere (0 : Rd d) 1 ⊆ annA d := by
  intro x hx
  rw [mem_annA_iff, mem_sphere_zero_iff_norm.1 hx]
  norm_num

theorem p5b_isCompact_annK : IsCompact (annK d) := by
  refine isCompact_of_isClosed_isBounded (isClosed_annCl _ _ _) ?_
  refine (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : Rd d) 1)).subset ?_
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  simpa using hx.2

theorem p5b_isBounded_annA : Bornology.IsBounded (annA d) := by
  refine (isBounded_ball : Bornology.IsBounded (ball (0 : Rd d) (7 / 2))).subset ?_
  intro x hx
  rw [mem_ball, dist_zero_right]
  exact (mem_annA_iff.1 hx).2

theorem p5b_isConnected_annA (hd : 2 ≤ d) : IsConnected (annA d) :=
  config_isConnected_ann hd 0 (by norm_num) (by norm_num)

/-- The global crossing is at most the `A`-internal crossing. -/
theorem p5b_setDistIn_univ_le (G : ContMetric d) (V S T : Set (Rd d)) :
    setDistIn G univ S T ≤ setDistIn G V S T := by
  unfold setDistIn
  exact iInf₂_mono fun u _ => iInf₂_mono fun v _ => G.internal_anti (subset_univ V) u v

/-! ## The deterministic step -/

/-- The references from the envelope bounds at `R = 2`, the crossing and the two diameters. -/
theorem p5b_localRefs_of_bounds {G : ContMetric d} {Hg t₀ σ β m M : ℝ} (hHg : 1 ≤ Hg) (hHt : Hg ≤ t₀)
    (hσ : 0 < σ) (hσ1 : σ < 1)
    (hup : ∀ z ∈ closedBall (0 : Rd d) 2, ∀ r ∈ Ioc (0 : ℝ) 1,
      diamIn G (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (Hg * r ^ σ))
    (hlow : ∀ x ∈ closedBall (0 : Rd d) 2, ∀ y ∈ closedBall (0 : Rd d) 2, Hg⁻¹ * ‖x - y‖ ^ β ≤ G.1 (x, y))
    (hcross : ENNReal.ofReal m ≤ setDistIn G univ (sphere 0 (3 / 4)) (sphere 0 1))
    (hdiam : diamIn G (annA d) (sphere 0 1) ≤ ENNReal.ofReal M)
    (hdiamK : diamIn G (annA d) (annK d) ≤ ENNReal.ofReal M) :
    LocalRefs G (2 * t₀) σ β m M := by
  have hHpos : 0 < Hg := lt_of_lt_of_le one_pos hHg
  have ht₀ : 0 < t₀ := lt_of_lt_of_le hHpos hHt
  refine ⟨fun x hx y hy => ?_, fun x hx y hy hxy => ?_, ?_, hdiam, hdiamK⟩
  · -- lower reference
    have hb := hlow x (p5b_annCl_subset_closedBall_two hx) y (p5b_annCl_subset_closedBall_two hy)
    have hinv : (2 * t₀)⁻¹ ≤ Hg⁻¹ := inv_anti₀ hHpos (by linarith)
    have h1 : (2 * t₀)⁻¹ * ‖x - y‖ ^ β ≤ G.1 (x, y) :=
      le_trans (mul_le_mul_of_nonneg_right hinv (Real.rpow_nonneg (norm_nonneg _) _)) hb
    exact (ENNReal.ofReal_le_ofReal h1).trans (G.ofReal_le_internal _ _ _)
  · -- upper reference at close points
    have hxA : x ∈ annA d := annCl_subset_annA hx
    rcases eq_or_ne x y with rfl | hne
    · rw [G.internal_self hxA]
      exact zero_le
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    set r : ℝ := 2 * ‖x - y‖ with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by linarith
    have hsub : ball x (2 * r) ⊆ annA d := p5b_ball_subset_annA hx (by linarith)
    have hxball : x ∈ ball x r := mem_ball_self hr0
    have hyball : y ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, norm_sub_rev]
      linarith
    have h1 : G.internal (annA d) x y ≤ diamIn G (ball x (2 * r)) (ball x r) := by
      refine (G.internal_anti hsub x y).trans ?_
      unfold diamIn
      exact le_iSup₂_of_le x hxball (le_iSup₂_of_le y hyball le_rfl)
    have h2 := hup x (p5b_annCl_subset_closedBall_two hx) r ⟨hr0, hr1⟩
    refine h1.trans (h2.trans (ENNReal.ofReal_le_ofReal ?_))
    have hpow : r ^ σ = 2 ^ σ * ‖x - y‖ ^ σ := by
      rw [hr, Real.mul_rpow (by norm_num) (norm_nonneg _)]
    have h2σ : (2 : ℝ) ^ σ ≤ 2 := by
      calc (2 : ℝ) ^ σ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1.le
        _ = 2 := Real.rpow_one 2
    have hn : 0 ≤ ‖x - y‖ ^ σ := Real.rpow_nonneg (norm_nonneg _) _
    rw [hpow]
    calc Hg * (2 ^ σ * ‖x - y‖ ^ σ) = (Hg * 2 ^ σ) * ‖x - y‖ ^ σ := by ring
      _ ≤ (t₀ * 2) * ‖x - y‖ ^ σ := by
          refine mul_le_mul_of_nonneg_right ?_ hn
          exact mul_le_mul hHt h2σ (by positivity) ht₀.le
      _ = 2 * t₀ * ‖x - y‖ ^ σ := by ring
  · exact hcross.trans (p5b_setDistIn_univ_le G _ _ _)

/-! ## Measurability of the integrands -/

/-- The global crossing of two spheres is a.e.-measurable when `ρ^D_g` is a.s. a length metric. -/
theorem p5b_aemeasurable_setDistIn_univ {D : DistRd d → ContMetric d} (hD : Measurable D)
    (μ : Measure (DistRd d)) (hl : ∀ᵐ g ∂μ, (rho D g).IsLength) (S T : Set (Rd d)) :
    AEMeasurable (fun g => setDistIn (rho D g) univ S T) μ := by
  have hm : Measurable fun g : DistRd d => ⨅ p ∈ S ×ˢ T, ENNReal.ofReal ((rho D g).1 p) :=
    LQGMetric.measurable_biInf_of_continuous
      (f := fun (g : DistRd d) (p : Rd d × Rd d) => ENNReal.ofReal ((rho D g).1 p))
      (fun g => ENNReal.continuous_ofReal.comp (rho D g).1.continuous)
      (fun p => ENNReal.measurable_ofReal.comp (p2_measurable_contMetric_apply (measurable_rho hD) p))
      (S ×ˢ T)
  refine hm.aemeasurable.congr ?_
  filter_upwards [hl] with g hg
  unfold setDistIn
  rw [biInf_prod]
  simp only [(rho D g).internal_univ_of_isLength hg]

/-! ## One metric -/

/-- **`a:lem-refs-prob` for one metric**: from `UniformEstimates d ξ̄ s`, for every `ε > 0` there are reference
constants such that `𝐏ₛ(¬ LocalRefs ρ^D) ≤ ε` for all `ξ ∈ (0, ξ̄]` and `D` strong. -/
theorem p5b_refs_prob_one (hd : 2 ≤ d) {ξbar s : ℝ} (hs : 0 < s) (hU : UniformEstimates d ξbar s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ σ₀ β₀ m M : ℝ, 0 < σ₀ ∧ σ₀ < 1 ∧ 1 < β₀ ∧ 0 < m ∧ m < M ∧ 1 ≤ H₀ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
          pinLaw d s {g | ¬ LocalRefs (rho D g) H₀ σ₀ β₀ m M} ≤ ENNReal.ofReal ε := by
  obtain ⟨p₁, σ, β, C, A, hp₁, hσ, hσ1, hβ, hC, hA, henv⟩ := hU.envelope
  obtain ⟨K₁, hK₁⟩ := hU.cross 0 (3 / 4) 1 1 (by norm_num) (by norm_num) one_pos
  obtain ⟨pp, hpp, hdiam⟩ := hU.diam
  obtain ⟨K₂, hK₂⟩ := hdiam (annA d) (sphere 0 1) isOpen_annA p5b_isBounded_annA (p5b_isConnected_annA hd)
    (isCompact_sphere 0 1) p5b_sphere_one_subset_annA
  obtain ⟨K₃, hK₃⟩ := hdiam (annA d) (annK d) isOpen_annA p5b_isBounded_annA (p5b_isConnected_annA hd)
    p5b_isCompact_annK annK_subset_annA
  set ε' : ℝ := ε / 4 with hε'
  have hε'0 : 0 < ε' := by positivity
  -- the constants
  set c₀ : ℝ := C * (1 + 2) ^ A with hc₀
  set t₀ : ℝ := max 1 ((c₀ / ε') ^ p₁⁻¹) with ht₀
  set K₁' : ℝ := max K₁ 1 with hK₁'
  set m : ℝ := ε' / K₁' with hm
  set K' : ℝ := max (max K₂ K₃) 1 with hK'
  set M : ℝ := max (m + 1) ((K' / ε') ^ pp⁻¹) with hM
  have hc₀0 : 0 < c₀ := by positivity
  have ht₀1 : 1 ≤ t₀ := le_max_left _ _
  have ht₀0 : 0 < t₀ := lt_of_lt_of_le one_pos ht₀1
  have hK₁'1 : 1 ≤ K₁' := le_max_right _ _
  have hm0 : 0 < m := div_pos hε'0 (lt_of_lt_of_le one_pos hK₁'1)
  have hK'1 : 1 ≤ K' := le_max_right _ _
  have hmM : m < M := lt_of_lt_of_le (lt_add_one m) (le_max_left _ _)
  have hM0 : 0 < M := hm0.trans hmM
  refine ⟨2 * t₀, σ, β, m, M, hσ, hσ1, hβ, hm0, hmM, by linarith, ?_⟩
  intro ξ hξ D hD
  have := isProbabilityMeasure_pinLaw hd s
  have hl := p5b_ae_isLength_rho hd hD hs
  obtain ⟨H, hHm, hH1, hHint, hHae⟩ := henv ξ hξ D hD 2 (by norm_num)
  -- the four bad events
  set B₁ : Set (DistRd d) := {g | ENNReal.ofReal (t₀ ^ p₁) ≤ ENNReal.ofReal (H g ^ p₁)} with hB₁
  set B₂ : Set (DistRd d) := {g | ENNReal.ofReal m⁻¹ ≤
    (setDistIn (rho D g) univ (sphere 0 (3 / 4)) (sphere 0 1))⁻¹ ^ (1 : ℝ)} with hB₂
  set B₃ : Set (DistRd d) := {g | ENNReal.ofReal (M ^ pp) ≤ diamIn (rho D g) (annA d) (sphere 0 1) ^ pp}
    with hB₃
  set B₄ : Set (DistRd d) := {g | ENNReal.ofReal (M ^ pp) ≤ diamIn (rho D g) (annA d) (annK d) ^ pp}
    with hB₄
  set N : Set (DistRd d) := {g | ¬ ((∀ z ∈ closedBall (0 : Rd d) 2, ∀ r ∈ Ioc (0 : ℝ) 1,
      diamIn (rho D g) (ball z (2 * r)) (ball z r) ≤ ENNReal.ofReal (H g * r ^ σ)) ∧
      (∀ x ∈ closedBall (0 : Rd d) 2, ∀ y ∈ closedBall (0 : Rd d) 2,
        (H g)⁻¹ * ‖x - y‖ ^ β ≤ (rho D g).1 (x, y)))} with hN
  have hN0 : pinLaw d s N = 0 := ae_iff.1 hHae
  -- inclusion of the failure event
  have hsub : {g | ¬ LocalRefs (rho D g) (2 * t₀) σ β m M} ⊆ N ∪ B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    intro g hg
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨hgN, hg1⟩, hg2⟩, hg3⟩, hg4⟩ := hcon
    have hgN' := not_not.1 hgN
    -- `H g ≤ t₀`
    have hHt : H g ≤ t₀ := by
      by_contra hlt
      push Not at hlt
      exact hg1 (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ht₀0.le hlt.le hp₁.le))
    -- the crossing
    have hcr : ENNReal.ofReal m ≤ setDistIn (rho D g) univ (sphere 0 (3 / 4)) (sphere 0 1) := by
      by_contra hlt
      push Not at hlt
      apply hg2
      change ENNReal.ofReal m⁻¹ ≤ (setDistIn (rho D g) univ (sphere 0 (3 / 4)) (sphere 0 1))⁻¹ ^ (1 : ℝ)
      rw [ENNReal.rpow_one, ENNReal.ofReal_inv_of_pos hm0]
      exact ENNReal.inv_le_inv.2 hlt.le
    -- the diameters
    have hdi (S : Set (Rd d)) (hS : ¬ ENNReal.ofReal (M ^ pp) ≤ diamIn (rho D g) (annA d) S ^ pp) :
        diamIn (rho D g) (annA d) S ≤ ENNReal.ofReal M := by
      by_contra hlt
      push Not at hlt
      apply hS
      rw [← ENNReal.ofReal_rpow_of_nonneg hM0.le hpp.le]
      exact ENNReal.rpow_le_rpow hlt.le hpp.le
    exact hg (p5b_localRefs_of_bounds (hH1 g) hHt hσ hσ1 hgN'.1 hgN'.2 hcr (hdi _ hg3) (hdi _ hg4))
  -- the four Markov bounds
  have hP₁ : pinLaw d s B₁ ≤ ENNReal.ofReal ε' := by
    have hmk := p5b_markov (μ := pinLaw d s)
      (f := fun g => ENNReal.ofReal (H g ^ p₁))
      (ENNReal.measurable_ofReal.comp (hHm.pow_const p₁)).aemeasurable
      (Real.rpow_pos_of_pos ht₀0 p₁) hHint
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    have hpow : c₀ / ε' ≤ t₀ ^ p₁ := by
      calc c₀ / ε' = ((c₀ / ε') ^ p₁⁻¹) ^ p₁ := (Real.rpow_inv_rpow (by positivity) hp₁.ne').symm
        _ ≤ t₀ ^ p₁ := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hp₁.le
    rw [div_le_iff₀ (Real.rpow_pos_of_pos ht₀0 p₁)]
    rw [div_le_iff₀ hε'0] at hpow
    linarith
  have hP₂ : pinLaw d s B₂ ≤ ENNReal.ofReal ε' := by
    have hX := p5b_aemeasurable_setDistIn_univ hD.measurable (pinLaw d s) hl (sphere 0 (3 / 4)) (sphere 0 1)
    have hmk := p5b_markov (μ := pinLaw d s)
      (f := fun g => (setDistIn (rho D g) univ (sphere 0 (3 / 4)) (sphere 0 1))⁻¹ ^ (1 : ℝ))
      (hX.inv.pow_const 1) (inv_pos.2 hm0) (hK₁ ξ hξ D hD)
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_inv_eq_mul]
    calc K₁ * m ≤ K₁' * m := mul_le_mul_of_nonneg_right (le_max_left _ _) hm0.le
      _ = ε' := by rw [hm]; field_simp
  have hMpow : K' / ε' ≤ M ^ pp := by
    calc K' / ε' = ((K' / ε') ^ pp⁻¹) ^ pp := (Real.rpow_inv_rpow (by positivity) hpp.ne').symm
      _ ≤ M ^ pp := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hpp.le
  have hMpos : 0 < M ^ pp := Real.rpow_pos_of_pos hM0 pp
  have hdiamP (S : Set (Rd d)) (hSA : S ⊆ annA d) {K : ℝ} (hKK : K ≤ K')
      (hKint : ∫⁻ g, diamIn (rho D g) (annA d) S ^ pp ∂(pinLaw d s) ≤ ENNReal.ofReal K) :
      pinLaw d s {g | ENNReal.ofReal (M ^ pp) ≤ diamIn (rho D g) (annA d) S ^ pp} ≤ ENNReal.ofReal ε' := by
    have hY := aemeasurable_diamIn_of_ae_length (pinLaw d s) (rho D) (measurable_rho hD.measurable) hl
      isOpen_annA hSA
    have hmk := p5b_markov (μ := pinLaw d s) (f := fun g => diamIn (rho D g) (annA d) S ^ pp)
      (hY.pow_const pp) hMpos hKint
    refine hmk.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [div_le_iff₀ hMpos]
    rw [div_le_iff₀ hε'0] at hMpow
    linarith
  have hP₃ : pinLaw d s B₃ ≤ ENNReal.ofReal ε' :=
    hdiamP _ p5b_sphere_one_subset_annA (le_trans (le_max_left _ _) (le_max_left _ _)) (hK₂ ξ hξ D hD)
  have hP₄ : pinLaw d s B₄ ≤ ENNReal.ofReal ε' :=
    hdiamP _ annK_subset_annA (le_trans (le_max_right _ _) (le_max_left _ _)) (hK₃ ξ hξ D hD)
  -- union bound
  calc pinLaw d s {g | ¬ LocalRefs (rho D g) (2 * t₀) σ β m M}
      ≤ pinLaw d s (N ∪ B₁ ∪ B₂ ∪ B₃ ∪ B₄) := measure_mono hsub
    _ ≤ pinLaw d s N + pinLaw d s B₁ + pinLaw d s B₂ + pinLaw d s B₃ + pinLaw d s B₄ := by
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        exact measure_union_le _ _
    _ ≤ 0 + ENNReal.ofReal ε' + ENNReal.ofReal ε' + ENNReal.ofReal ε' + ENNReal.ofReal ε' := by
        rw [hN0]
        gcongr
    _ = ENNReal.ofReal ε := by
        rw [zero_add, ← ENNReal.ofReal_add hε'0.le hε'0.le, ← ENNReal.ofReal_add (by positivity) hε'0.le,
          ← ENNReal.ofReal_add (by positivity) hε'0.le]
        congr 1
        rw [hε']
        ring

/-! ## Lemma `a:lem-refs-prob` -/

/-- **Lemma `a:lem-refs-prob`** (blueprint Part A; [C] p. 6, l. 267): from Lemma 2.1 at the pin `s`
(`UniformEstimates d ξ̄ s`, interface I1), for every `p > 0` there are reference constants
`(H₀, σ₀, β₀, m, M)`, `0 < σ₀ < 1 < β₀`, `0 < m < M`, `1 ≤ H₀`, such that the pair references fail with
`𝐏ₛ`-probability at most `p` for all `ξ, η ∈ (0, ξ̄]` and all `D`, `E` strong. -/
theorem refs_prob (hd : 2 ≤ d) {ξbar s : ℝ} (hs : 0 < s) (hU : UniformEstimates d ξbar s)
    {p : ℝ} (hp : 0 < p) :
    ∃ H₀ σ₀ β₀ m M : ℝ, 0 < σ₀ ∧ σ₀ < 1 ∧ 1 < β₀ ∧ 0 < m ∧ m < M ∧ 1 ≤ H₀ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ η ∈ Ioc (0 : ℝ) ξbar, ∀ D E : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
          pinLaw d s (PairRefs D E H₀ σ₀ β₀ m M)ᶜ ≤ ENNReal.ofReal p := by
  obtain ⟨H₀, σ₀, β₀, m, M, hσ₀, hσ₀1, hβ₀, hm, hmM, hH₀, hone⟩ :=
    p5b_refs_prob_one hd hs hU (ε := p / 2) (by positivity)
  refine ⟨H₀, σ₀, β₀, m, M, hσ₀, hσ₀1, hβ₀, hm, hmM, hH₀, fun ξ hξ η hη D E hD hE => ?_⟩
  have hsub : (PairRefs D E H₀ σ₀ β₀ m M)ᶜ ⊆
      {g | ¬ LocalRefs (rho D g) H₀ σ₀ β₀ m M} ∪ {g | ¬ LocalRefs (rho E g) H₀ σ₀ β₀ m M} := by
    intro g hg
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
    exact hg ⟨hcon.1, hcon.2⟩
  calc pinLaw d s (PairRefs D E H₀ σ₀ β₀ m M)ᶜ
      ≤ pinLaw d s {g | ¬ LocalRefs (rho D g) H₀ σ₀ β₀ m M} +
          pinLaw d s {g | ¬ LocalRefs (rho E g) H₀ σ₀ β₀ m M} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (p / 2) + ENNReal.ofReal (p / 2) := add_le_add (hone ξ hξ D hD) (hone η hη E hE)
    _ = ENNReal.ofReal p := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end HigherDimLQGContinuity
