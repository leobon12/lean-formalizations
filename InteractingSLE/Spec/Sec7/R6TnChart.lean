/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TnBoundary
import InteractingSLE.Spec.Sec7.R6FcMixedInf

/-!
# Boundary models of actual outer current charts

PROVE-R6-TWO. These adapters reuse the landed `chart_facts` and
`chart_factsInf`, for arbitrary driven traversals with an interior tip.
Neither adapter assumes a reverse visit order on an outer arm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Tn

open PocketTraversal Lemma71C PocketStop PocketStopField R6Fc
open WangWu (chartAL chartAR)

abbrev leftSeed {Ω : Type*} (γ : Ω → ℝ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  geomLW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXL) 0 q ω - segDriver (γ ω) q

abbrev rightSeed {Ω : Type*} (γ : Ω → ℝ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  geomRW (fun t ω => segDriver (γ ω) t) (fun _ => LP.twoSeedXR) 0 q ω - segDriver (γ ω) q

/-- Package the landed Loewner boundary correspondence in a physical
initial coordinate. `hdetect` is the Jordan boundary collar theorem. -/
theorem boundaryChart_of_loewner {C P : Set ℂ} {ψ E₀ : ℂ → ℂ} {O : Chart}
    (hO : O.IsConformal) (hCP : C ⊆ P) (hψc : ContinuousOn ψ P) (hψH : MapsTo ψ C H)
    (hE₀m : MapsTo E₀ Hbar P) (hcomp : ∀ z ∈ Hbar, ψ (E₀ z) = z)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {q : ℝ} (hq : 0 < q) (hgap : chartAL W q < chartAR W q)
    (hdom : (O.dom : Set ℂ) = C ∩ ψ ⁻¹' (H \ fwdHull W q))
    (hE : EqOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) O.2.1 H)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q) z)) Hbar)
    (hdetect : ∀ p ∈ P, ∀ r > 0,
      C ∩ ball p r ⊆ C ∩ ψ ⁻¹' (H \ fwdHull W q) → ψ p ∉ closure (fwdHull W q)) :
    Nonempty (BoundaryChart C P O (chartAL W q) (chartAR W q)) := by
  obtain ⟨hFc, hFeq, hFm⟩ := extendFrom_props hη hW hW0 hq.le
  refine ⟨{
    coord := ψ, hull := fwdHull W q,
    inverse := fun z => E₀ (extendFrom H (fwdMapInv W q) z),
    conformal := hO, dom_eq := hdom, inv_eq := hE, inv_cont := hEc,
    inv_maps := hE₀m.comp hFm, mem_boundary := hCP, coord_mem := hψH,
    coord_cont := hψc, classify := ?_, detect := hdetect, norm_bound := ?_ }⟩
  · intro x
    rw [hcomp _ (hFm (real_mem_Hbar x))]
    constructor
    · intro h
      by_contra hx
      apply alive_of_not_mem_Icc hη hW hW0 hq.le _ h
      simpa only [mem_Icc, not_and_or, not_le] using hx
    · exact dead_of_mem_Icc hη hW hW0 hq hgap
  · obtain ⟨B, hB⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hq.le
    refine ⟨B, fun w hw => ?_⟩
    let z := O.1 w
    have hzH : z ∈ H := hO.fwd_mem hw
    have hψw : ψ w = fwdMapInv W q z := by
      rw [← hO.inv_fwd hw, ← hE hzH, hcomp _ (hFm (QuantumZipper.H_subset_Hbar hzH)), hFeq hzH]
    have hb := hB z hzH
    rw [← hψw] at hb
    have hn := norm_sub_norm_le z (ψ w)
    rw [norm_sub_rev] at hn
    change ‖z‖ ≤ ‖ψ w‖ + B
    linarith

section Actual

variable {Ω : Type*} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
  {n : Ω → ℤ} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- Boundary model and strict seed signs at an interior tip, finite
outgoing pole. All hypotheses are ordinary one-pocket facts. -/
theorem boundaryChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψc : ∀ ω ∈ A, SupercriticalConformalCovariance.IsConformalBijection (ψ ω) (C ω) H)
    (hCb : Bornology.IsBounded (C ω)) {x₀ y₀ : ℂ} (hx₀ : x₀ ∉ C ω)
    (hJ : Sec6.IsJordanCoord (C ω) x₀ y₀ (ψ ω)) (hω : ω ∈ A) (hγ : IsDrivenCurve (γ ω))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (htip : capTrace (γ ω) q ∈ H) :
    ∃ _M : BoundaryChart (C ω) (closure (C ω) \ {x₀})
      (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω)
      (leftSeed γ q ω) (rightSeed γ q ω), leftSeed γ q ω < 0 ∧ 0 < rightSeed γ q ω := by
  obtain ⟨t, hqt, ht⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt' : q < t := by exact_mod_cast hqt
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, W, hW, hW0, hWeq, η, hη, hηeq, hfacts⟩ :=
    chart_facts (n := n) hCo hCH hψc hCb hx₀ hJ hω hγ ht
  obtain ⟨hO, hdom, -, hE, hEc⟩ := hfacts q hqt'
  have hWq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (γ ω) s.toNNReal = W s :=
    fun s hs => hWeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt'.le)⟩
  have hL : leftSeed γ q ω = chartAL W q := seedL_eq hW hWq
  have hR : rightSeed γ q ω = chartAR W q := seedR_eq hW hWq
  have htip' : extendFrom H (fwdMapInv W q) ((0 : ℝ) : ℂ) ∈ H := by
    have hlim := hη.tendsto_fwdMapInv_tip hW hW0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at hlim
    rw [extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar 0) hlim,
      hηeq q q.coe_nonneg (by exact_mod_cast hqt'.le)]
    exact htip
  have hAL := chartAL_neg_of_tip hη hW hW0 q.coe_nonneg htip'
  have hAR := chartAR_pos_of_tip hη hW hW0 q.coe_nonneg htip'
  obtain ⟨M⟩ := boundaryChart_of_loewner (P := closure (C ω) \ {x₀}) hO
    (fun z hz => ⟨subset_closure hz, fun he => hx₀ (he ▸ hz)⟩) hJ.1 (hψc ω hω).2.mapsTo hE₀m
    (fun z hz => jordan_comp_ext hJ hE₀ hE₀c hE₀m hz) hη hW hW0
    (show (0 : ℝ) < q by exact_mod_cast hq0) (hAL.trans hAR) hdom hE hEc
    (fun p hp r hr hsub => notMem_closure_of_ball_subset hJ hCb hx₀ (fun z hz => hz.1) hp hr hsub)
  rw [hL, hR]
  exact ⟨M, hAL, hAR⟩

/-- The same one-chart adapter when the outgoing pole is infinity. -/
theorem boundaryChartInf (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψc : ∀ ω ∈ A, SupercriticalConformalCovariance.IsConformalBijection (ψ ω) (C ω) H)
    {y₀ : ℂ} (hJ : Sec6.IsJordanCoordInf (C ω) y₀ (ψ ω)) (hω : ω ∈ A) (hγ : IsDrivenCurve (γ ω))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (htip : capTrace (γ ω) q ∈ H) :
    ∃ _M : BoundaryChart (C ω) (closure (C ω))
      (relChart (fun ω => shiftChart (pChart A C ψ ω) (n ω)) γ q ω)
      (leftSeed γ q ω) (rightSeed γ q ω), leftSeed γ q ω < 0 ∧ 0 < rightSeed γ q ω := by
  obtain ⟨t, hqt, ht⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt' : q < t := by exact_mod_cast hqt
  obtain ⟨E₀, hE₀, hE₀c, hE₀m, W, hW, hW0, hWeq, η, hη, hηeq, hfacts⟩ :=
    chart_factsInf (n := n) hCo hCH hψc hJ hω hγ ht
  obtain ⟨hO, hdom, -, hE, hEc⟩ := hfacts q hqt'
  have hWq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (γ ω) s.toNNReal = W s :=
    fun s hs => hWeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt'.le)⟩
  have hL : leftSeed γ q ω = chartAL W q := seedL_eq hW hWq
  have hR : rightSeed γ q ω = chartAR W q := seedR_eq hW hWq
  have htip' : extendFrom H (fwdMapInv W q) ((0 : ℝ) : ℂ) ∈ H := by
    have hlim := hη.tendsto_fwdMapInv_tip hW hW0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at hlim
    rw [extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar 0) hlim,
      hηeq q q.coe_nonneg (by exact_mod_cast hqt'.le)]
    exact htip
  have hAL := chartAL_neg_of_tip hη hW hW0 q.coe_nonneg htip'
  have hAR := chartAR_pos_of_tip hη hW hW0 q.coe_nonneg htip'
  obtain ⟨M⟩ := boundaryChart_of_loewner hO subset_closure hJ.1 (hψc ω hω).2.mapsTo hE₀m
    (fun z hz => jordan_comp_extInf hJ hE₀ hE₀c hE₀m hz) hη hW hW0
    (show (0 : ℝ) < q by exact_mod_cast hq0) (hAL.trans hAR) hdom hE hEc
    (fun p hp r hr hsub => notMem_closure_of_ball_subsetInf hJ (fun z hz => hz.1) hp hr hsub)
  rw [hL, hR]
  exact ⟨M, hAL, hAR⟩

end Actual

/-- Interior tips persist in a right neighbourhood of a live capacity
time. This discharges the seed-sign side condition for nearby inner levels. -/
theorem exists_right_capTrace_mem_H {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife γ) (htip : capTrace γ q ∈ H) :
    ∃ ε > 0, ∀ q' : ℝ≥0, q < q' → (q' : ℝ) < q + ε → capTrace γ q' ∈ H := by
  have he : ∀ᶠ q' in 𝓝 q, capTrace γ q' ∈ H :=
    (hγ.continuousAt_capTrace hq) (QuantumZipper.isOpen_H.mem_nhds htip)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 he
  refine ⟨ε, hε, fun q' hlo hhi => hsub ?_⟩
  have hd : (0 : ℝ) < (q' : ℝ) - q := sub_pos.2 (by exact_mod_cast hlo)
  rw [mem_ball, NNReal.dist_eq, abs_of_pos hd]
  linarith

end InteractingSLE.Sec7.R6Tn
