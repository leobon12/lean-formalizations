/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTailGirsanov
import BrownianMotion.Gaussian.BrownianMotion

/-!
# The strip endpoint theorem (ii) from the constant-drift endpoint theorem

Packet PROVE-ZHAN-A4, item 4. Astra, *Formalization proofs* L1554–L1569 ("The strip endpoint theorem"): under (3.3)
the strip driver is `ξ_t = √κ B̃_t + σ t + ∫₀ᵗ e`, `|σ| < 1`, with an exponentially decaying error `e`; the
whole-tail Girsanov step transfers the actual endpoint of the constant-drift reference to the original trace.

This file assembles the conditional theorem

  `stripEndpointStatement_of_constDrift : ConstDriftEndpointStatement κ → StripEndpointStatement κ`  (`0 < κ`),

a **conditional helper** whose single hypothesis is the named source theorem "constant drift `|σ| < 1`: the actual
trace converges to a point of the upper line" (Astra L1420–L1499, `ConstDriftEndpointStatement`, strip-driver form).
Proof, almost surely:

* clauses (1)–(2) of `HasStripEndpoint` are PROVE-ZHAN-A3's (`ae_hasStripEndpoint_of_convergence`);
* the strip driver is `√κ B̃ + σ t + ∫ e` (`StripGood.stripDriver_eq`, with PROVE-ZHAN-A2's strip Brownian motion
  `stripBM` of the strip filtration `stripFilt`), every lower gap grows linearly (`StripGood.exists_linear_escape`,
  with the Brownian strong law), so `|e| ≤ 1` and `∫ e² ≤ M` after some integer `n` (`exists_stripErr_bound`);
* for every `(n, M)` the whole-tail Girsanov step (`Tail.exists_tail_reference`, with the adapted error
  `errOfState ∘ stateAt`) gives a Brownian motion `β` under an equivalent measure with
  `ξ_{n+1+t} − ξ_{n+1} = √κ β_t + σ t` on the no-cutoff event, so the restart at strip time `n + 1` has the
  constant-drift strip driver (`HasStripDriver.rs`) and the named input applies to it;
* the pullback through the finite prefix (`IsStripPath.stripConv_of_rs`) gives clause (3).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

open Strip

variable {nL nR : ℕ} {κ : ℝ} {pL : Fin nL → ℝ} {pR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {τm : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The initial strip state of a strip word lies in the strip martingale region. -/
theorem stripInit_mem_region_word (pL : Fin nL → ℝ) (pR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (τm κ : ℝ) :
    stripInit (Strip.wordXL pL) (Strip.wordXR pR) ∈
      stripMartRegion κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR := by
  refine stripInit_mem_region κ _ _ _ _ (by simp) (wordXL_last_lt pL) fun j => ?_
  simp only [Strip.wordXL_last, Strip.wordXR]
  linarith [Real.exp_pos (pR j)]

/-- **The driving identity for PROVE-ZHAN-A2's strip Brownian motion** on the good event (the identity of
`exists_stripBrownian`, for the explicit `stripBM`). -/
theorem stripDriver_eq_stripBM (hκ : 0 < κ)
    (hgood : ∀ ω ∈ G, IsGoodStrip κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR W VL VR B ζ ω)
    {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL (Fin.last nL) · ω)) t =
      Real.sqrt κ * stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B t ω
      - (∑ i : Fin nL, ρL i / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
          (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VL i.castSucc · ω)) t - pL i))
      - (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
          (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VR j · ω)) t - pR j))
      + (τm - Strip.tauPlus κ ρL ρR τm) / 2 * t := by
  have hg := hgood ω hω
  have hs0 : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hBM : Real.sqrt κ * stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B t ω =
      stripMartObs κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR
        (stripCoordAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (chordT (W · ω)
          (VL (Fin.last nL) · ω) t), B (chordT (W · ω) (VL (Fin.last nL) · ω) t) ω) -
      stripMartObs κ (Strip.wordXL pL) (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR
        (stripInit (Strip.wordXL pL) (Strip.wordXR pR)) := by
    simp only [stripBM, phiS, chordS, coordS, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
    field_simp
  rw [hBM, stripMartObs_chordT_eq (vL := fun i t => VL i t ω) (b := (B · ω)) hg.1 hg.2.2.2 t,
    stripMartObs_stripInit_word]
  simp only [Strip.wordRhoL_castSucc, Strip.wordRhoL_last, Strip.tauPlus]
  have e1 : ∑ i : Fin nL, ρL i / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
      (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VL i.castSucc · ω)) t - pL i) =
      (∑ i : Fin nL, ρL i / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
        (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VL i.castSucc · ω)) t - t)) +
      (∑ i : Fin nL, ρL i / 2) * t - ∑ i, ρL i / 2 * pL i := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
      (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VR j · ω)) t - pR j) =
      (∑ j, ρR j / 2 * (Strip.stripPoint (Strip.extPath (W · ω))
        (Strip.extPath (VL (Fin.last nL) · ω)) (Strip.extPath (VR j · ω)) t - t)) +
      (∑ j, ρR j / 2) * t - ∑ j, ρR j / 2 * pR j := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : (∑ i : Fin nL, ρL i / 2) = (∑ i, ρL i) / 2 := by rw [Finset.sum_div]
  have e4 : (∑ j, ρR j / 2) = (∑ j, ρR j) / 2 := by rw [Finset.sum_div]
  rw [e1, e2, e3, e4]
  ring

/-- **Sublinearity from the strong law**: a continuous path with `f(t)/t → 0` satisfies
`|c f(u)| ≤ C + ε u` on `[0, ∞)` for every `ε > 0`. -/
theorem sublinear_of_tendsto {f : ℝ≥0 → ℝ} (hc : Continuous f)
    (hf : Tendsto (fun t : ℝ≥0 => f t / (t : ℝ)) atTop (𝓝 0)) (c : ℝ) :
    ∀ ε > 0, ∃ C, ∀ u : ℝ, 0 ≤ u → |c * f u.toNNReal| ≤ C + ε * u := by
  intro ε hε
  set δ := ε / (|c| + 1) with hδ
  have hδ0 : 0 < δ := div_pos hε (by positivity)
  obtain ⟨T₀, hT₀⟩ := (Metric.tendsto_atTop.1 hf) δ hδ0
  set T₁ : ℝ≥0 := max T₀ 1 with hT₁
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T₁)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|c| * max C₀ 0, fun u hu => ?_⟩
  rw [abs_mul]
  rcases le_or_gt u.toNNReal T₁ with h1 | h1
  · have := hC₀ u.toNNReal ⟨bot_le, h1⟩
    rw [Real.norm_eq_abs] at this
    have h2 : |c| * |f u.toNNReal| ≤ |c| * max C₀ 0 :=
      mul_le_mul_of_nonneg_left (this.trans (le_max_left _ _)) (abs_nonneg c)
    nlinarith
  · have hT : T₀ ≤ u.toNNReal := (le_max_left _ _).trans h1.le
    have hpos : (0 : ℝ) < u.toNNReal := lt_of_lt_of_le (by norm_num) (NNReal.coe_le_coe.2
      ((le_max_right T₀ 1).trans h1.le))
    have h3 := hT₀ u.toNNReal hT
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hpos, div_lt_iff₀ hpos] at h3
    rw [Real.coe_toNNReal _ hu] at h3 hpos
    have h4 : |c| * |f u.toNNReal| ≤ |c| * (δ * u) := mul_le_mul_of_nonneg_left h3.le (abs_nonneg c)
    have h5 : |c| * (δ * u) ≤ ε * u := by
      have hfrac : |c| * δ ≤ ε := by
        rw [hδ, mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg c]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hfrac hu
    have h6 : 0 ≤ |c| * max C₀ 0 := mul_nonneg (abs_nonneg c) (le_max_right _ _)
    linarith

/-- The side sums of a strip word with lower prefix sums `≥ κ/2 − 2` are `> −2`. -/
theorem one_add_sum_div_two_nonneg {n : ℕ} {ρ : Fin n → ℝ} (hκ : 0 < κ)
    (hpre : ∀ j : Fin n, κ / 2 - 2 ≤ ∑ i ∈ Finset.Iic j, ρ i) : 0 ≤ 1 + (∑ i, ρ i) / 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have h := hpre (Fin.last k)
    rw [← Fin.top_eq_last, Finset.Iic_top] at h
    linarith

/-- `|σ| < 1` for the strip drift `σ = (q₋ − q₊)/2`. -/
theorem abs_stripDrift_lt_one (hq : |chargePlus κ ρL ρR τm - chargeMinus ρL τm| < 2) :
    |(τm - tauPlus κ ρL ρR τm) / 2 + (∑ i, ρL i) / 2 - (∑ j, ρR j) / 2| < 1 := by
  have e : (τm - tauPlus κ ρL ρR τm) / 2 + (∑ i, ρL i) / 2 - (∑ j, ρR j) / 2 =
      -((chargePlus κ ρL ρR τm - chargeMinus ρL τm) / 2) := by
    simp only [chargePlus, chargeMinus]; ring
  rw [e, abs_neg, abs_div, abs_two]
  linarith

/-- **Zhan's strip endpoint theorem (ii) from the constant-drift endpoint theorem** (conditional helper; Astra
L1554–L1569, the whole-tail Girsanov step). For every `κ > 0`, the named input `ConstDriftEndpointStatement κ`
(constant drift `|σ| < 1`: the actual trace converges to a point of the upper line) implies
`StripEndpointStatement κ`. -/
theorem stripEndpointStatement_of_constDrift (hκ : 0 < κ) (h : ConstDriftEndpointStatement.{u} κ) :
    StripEndpointStatement.{u} κ := by
  intro nL nR pL pR ρL ρR τm Ω mΩ P 𝓕 W VL VR B ζ hsep hpre hq hE
  classical
  have hP : IsProbabilityMeasure P :=
    hE.isFilteredBrownianReal.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  refine ae_hasStripEndpoint_of_convergence hκ hsep hpre hE ?_
  -- PROVE-ZHAN-A2's strip filtration and strip Brownian motion
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good_strip hE (ae_hasUnboundedStripClock hκ hsep hpre hE)
  have h0 := stripInit_mem_region_word pL pR ρL ρR τm κ
  have hB' : IsFilteredBrownianReal (stripFilt hE hGm hGc hgood)
      (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B) P :=
    isFilteredBrownianReal_stripBM hE hGm hGc hgood h0 hκ
  have hB'c : ∀ ω, Continuous (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B · ω) :=
    continuous_stripBM hgood h0
  -- noncollision on a measurable full set
  have hnc := ae_stripLife_noncollision hκ hsep hpre hE
  set S : Set Ω := (toMeasurable P {ω | ¬ ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
    (∀ i : Fin nL, VL i.castSucc s ω < W s ω) ∧ ∀ j : Fin nR, W s ω < VR j s ω})ᶜ with hSdef
  have hSm : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSc : P Sᶜ = 0 := by rw [hSdef, compl_compl, measure_toMeasurable]; exact ae_iff.1 hnc
  have hSnc : ∀ ω ∈ S, ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last nL) · ω) (ζ ω) s →
      (∀ i : Fin nL, VL i.castSucc s ω < W s ω) ∧ ∀ j : Fin nR, W s ω < VR j s ω := fun ω hω => by
    by_contra hcon
    exact hω (subset_toMeasurable _ _ hcon)
  set G' : Set Ω := G ∩ S with hG'def
  have hG'm : MeasurableSet G' := hGm.inter hSm
  have hG'c : P G'ᶜ = 0 := by rw [hG'def, compl_inter]; exact measure_union_null hGc hSc
  have hgd : ∀ ω ∈ G', StripGood κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) := fun ω hω =>
    ⟨(hgood ω hω.1).1, (hgood ω hω.1).2.2.2, hSnc ω hω.2⟩
  -- the adapted, continuous drift error
  set e : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G' then errOfState κ (Strip.wordXL pL) (Strip.wordXR pR)
    (Strip.wordRhoL ρL τm) ρR ρL ρR (stateAt pL (Strip.wordXR pR) G W VL VR B t ω) else 0 with hedef
  have heq : ∀ ω ∈ G', ∀ t, e t ω = stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t :=
    fun ω hω t => by
      show (if ω ∈ G' then _ else _) = _
      simp only [hω, ite_true]
      exact errOfState_stateAt hgood hω.1 ρL ρR t
  have hG'H : ∀ t, MeasurableSet[stripFilt hE hGm hGc hgood t] G' := fun t => by
    have h1 : MeasurableSet[usualAugmentation 𝓕 P 0] G' := by
      have := (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hG'm.compl hG'c 0).compl
      rwa [compl_compl] at this
    exact (isStoppingTime_chordS hE hGm hGc hgood t).le_measurableSpace_of_const_le (i := 0)
      (fun ω => WithTop.coe_le_coe.2 (by positivity)) _ h1
  have he : ∀ t, Measurable[stripFilt hE hGm hGc hgood t] (e t) := fun t => by
    show Measurable[stripFilt hE hGm hGc hgood t] fun ω => if ω ∈ G' then errOfState κ (Strip.wordXL pL)
      (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR ρL ρR (stateAt pL (Strip.wordXR pR) G W VL VR B t ω) else 0
    exact Measurable.ite (hG'H t) ((measurable_errOfState κ (Strip.wordXL pL) (Strip.wordXR pR)
      (Strip.wordRhoL ρL τm) ρR ρL ρR).comp (measurable_stateAt hE hGm hGc hgood t)) measurable_const
  have hec : ∀ ω, Continuous (e · ω) := by
    intro ω
    by_cases hω : ω ∈ G'
    · have e1 : (e · ω) = fun t : ℝ≥0 =>
          stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) t := funext fun t => heq ω hω t
      rw [e1]
      exact ((hgd ω hω).continuousOn_stripErr_Ici ρL ρR).comp_continuous NNReal.continuous_coe
        fun t => NNReal.coe_nonneg t
    · have e1 : (e · ω) = fun _ => (0 : ℝ) := funext fun t => by
        show (if ω ∈ G' then _ else _) = _
        simp only [hω, ite_false]
      rw [e1]
      exact continuous_const
  -- the drift and the side sums
  set σ := (τm - tauPlus κ ρL ρR τm) / 2 + (∑ i, ρL i) / 2 - (∑ j, ρR j) / 2 with hσdef
  have hσ : |σ| < 1 := abs_stripDrift_lt_one hq
  have hsl := one_add_sum_div_two_nonneg hκ hpre.1
  have hsr := one_add_sum_div_two_nonneg hκ hpre.2
  -- every `(n, M)`: the reference tail and the named input, almost surely
  have hnm : ∀ n M : ℕ, ∀ᵐ ω ∂P, ∃ β : ℝ≥0 → ℝ,
      ((∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1) →
        (∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M) →
        ∀ t : ℝ≥0, Real.sqrt κ * β t =
          Real.sqrt κ * (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B
              ((n : ℝ≥0) + 1 + t) ω -
            stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B ((n : ℝ≥0) + 1) ω) +
            ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω) ∧
      ∀ (w v : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), HasStripDriver w v ζ' (fun t => Real.sqrt κ * β t + σ * t) →
        HasStripEndpoint w v ζ' := by
    intro n M
    obtain ⟨Q, 𝓗', β, hQ, hβ, hid⟩ := Tail.exists_tail_reference hκ hB' hB'c he hec n M
    filter_upwards [hQ.ac'.ae_le (h σ hσ Q 𝓗' β hβ)] with ω hω
    exact ⟨(β · ω), hid ω, hω⟩
  have hnm' : ∀ᵐ ω ∂P, ∀ n M : ℕ, ∃ β : ℝ≥0 → ℝ,
      ((∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1) →
        (∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M) →
        ∀ t : ℝ≥0, Real.sqrt κ * β t =
          Real.sqrt κ * (stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B
              ((n : ℝ≥0) + 1 + t) ω -
            stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B ((n : ℝ≥0) + 1) ω) +
            ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω) ∧
      ∀ (w v : ℝ≥0 → ℝ) (ζ' : ℝ≥0∞), HasStripDriver w v ζ' (fun t => Real.sqrt κ * β t + σ * t) →
        HasStripEndpoint w v ζ' := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; exact hnm n
  have hlaw := ProbabilityTheory.IsBrownianReal.tendsto_div_id_atTop hB'.1
  have hG'ae : ∀ᵐ ω ∂P, ω ∈ G' := by rw [ae_iff]; exact hG'c
  filter_upwards [hnm', hlaw, hG'ae] with ω hω hsub hωG
  have hg := hgd ω hωG
  set B' := stripBM κ pL (Strip.wordXR pR) (Strip.wordRhoL ρL τm) ρR G W VL VR B with hB'def
  -- the strip driver as constant drift plus error
  have hξ0 : ∀ t : ℝ≥0, stripDriver (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) t =
      Real.sqrt κ * B' t ω + σ * t +
        ∫ r in (0 : ℝ)..t, stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r :=
    fun t => hg.stripDriver_eq (N := fun t => Real.sqrt κ * B' t ω)
      (fun t => stripDriver_eq_stripBM hκ hgood hωG.1 t) t
  have hξ : ∀ u : ℝ, 0 ≤ u → stripDriver (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) u =
      Real.sqrt κ * B' u.toNNReal ω + σ * u +
        ∫ r in (0 : ℝ)..u, stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r :=
    fun u hu => by
      have := hξ0 u.toNNReal
      rwa [Real.coe_toNNReal _ hu] at this
  have hN := sublinear_of_tendsto (hB'c ω) hsub (Real.sqrt κ)
  obtain ⟨α, hα, T, hT⟩ := hg.exists_linear_escape (N := fun u => Real.sqrt κ * B' u.toNNReal ω) hξ hN
    hsl hsr hσ
  obtain ⟨T', hT'0, M', hbd⟩ := hg.exists_stripErr_bound (ρl := ρL) (ρr := ρR) hα hT
  set n := ⌈T'⌉₊ with hn
  set M := ⌈M'⌉₊ with hM
  have hnT : T' ≤ (n : ℝ) := Nat.le_ceil T'
  have hMM : M' ≤ (M : ℝ) := Nat.le_ceil M'
  have hcut1 : ∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → |e u ω| ≤ 1 := fun u hu => by
    rw [heq ω hωG u]
    exact (hbd u (hnT.trans (by exact_mod_cast hu))).1
  have hcut2 : ∀ u : ℝ≥0, (n : ℝ≥0) ≤ u → ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 ≤ M := fun u hu => by
    have hnu : (n : ℝ) ≤ u := by exact_mod_cast hu
    have hcongr : ∫ r in (n : ℝ)..(u : ℝ), e r.toNNReal ω ^ 2 =
        ∫ r in (n : ℝ)..(u : ℝ), stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r ^ 2 := by
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le hnu] at hr
      have hr0 : 0 ≤ r := (Nat.cast_nonneg n).trans hr.1
      simp only [heq ω hωG, Real.coe_toNNReal _ hr0]
    have hc2 := (hg.continuousOn_stripErr_Ici ρL ρR).pow 2
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := T') (b := (n : ℝ))
      (c := (u : ℝ)) (f := fun r => stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r ^ 2)
      ((hc2.mono (by rw [uIcc_of_le hnT]; exact fun r hr => hT'0.trans hr.1)).intervalIntegrable)
      ((hc2.mono (by rw [uIcc_of_le hnu]; exact fun r hr => (hT'0.trans hnT).trans hr.1)).intervalIntegrable)
    have hnn : 0 ≤ ∫ r in T'..(n : ℝ),
        stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r ^ 2 :=
      intervalIntegral.integral_nonneg hnT fun r _ => sq_nonneg _
    have := (hbd u (hnT.trans hnu)).2
    rw [hcongr]
    linarith
  obtain ⟨β, hid, hbase⟩ := hω n M
  have hid' := hid hcut1 hcut2
  -- the restart at strip time `n + 1` has the constant-drift strip driver
  have hSD : HasStripDriver (W · ω) (VL (Fin.last nL) · ω) (ζ ω)
      (fun t => stripDriver (extPath (W · ω)) (extPath (VL (Fin.last nL) · ω)) t) :=
    ⟨hg.isStripPath, fun t => rfl⟩
  have hR := hSD.rs ((n : ℝ≥0) + 1)
  have hR' : HasStripDriver (rsW (W · ω) (VL (Fin.last nL) · ω) ((n : ℝ≥0) + 1))
      (rsV (W · ω) (VL (Fin.last nL) · ω) ((n : ℝ≥0) + 1))
      (rsZ (W · ω) (VL (Fin.last nL) · ω) (ζ ω) ((n : ℝ≥0) + 1)) (fun t => Real.sqrt κ * β t + σ * t) := by
    refine ⟨hR.1, fun t => ?_⟩
    rw [hR.2 t]
    have h1 := hξ0 ((n : ℝ≥0) + 1 + t)
    have h2 := hξ0 ((n : ℝ≥0) + 1)
    have hint := intervalIntegral.integral_interval_sub_left (μ := volume)
      (hg.intervalIntegrable_stripErr ρL ρR le_rfl (NNReal.coe_nonneg ((n : ℝ≥0) + 1 + t)))
      (hg.intervalIntegrable_stripErr ρL ρR le_rfl (NNReal.coe_nonneg ((n : ℝ≥0) + 1)))
    have hcongr : ∫ r in (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ)..(((n : ℝ≥0) + 1 + t : ℝ≥0) : ℝ),
        stripErr ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) r =
        ∫ r in ((n : ℝ) + 1)..((n : ℝ) + 1 + t), e r.toNNReal ω := by
      push_cast
      refine intervalIntegral.integral_congr fun r hr => ?_
      rw [uIcc_of_le (by linarith [NNReal.coe_nonneg t])] at hr
      have hr0 : 0 ≤ r := by linarith [hr.1, Nat.cast_nonneg (α := ℝ) n]
      simp only [heq ω hωG, Real.coe_toNNReal _ hr0]
    have hβt := hid' t
    simp only at h1 h2 ⊢
    rw [h1, h2]
    have hc : ((((n : ℝ≥0) + 1 + t : ℝ≥0)) : ℝ) = (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) + t := by push_cast; ring
    have hσc : σ * ((((n : ℝ≥0) + 1 + t : ℝ≥0)) : ℝ) = σ * (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) + σ * t := by
      rw [hc]; ring
    linarith
  exact hg.isStripPath.stripConv_of_rs ((n : ℝ≥0) + 1) (hbase _ _ _ hR')

end Zhan

end InteractingSLE
