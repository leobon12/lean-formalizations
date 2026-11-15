/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofChart
import InteractingSLE.Spec.Restart.RetPlumbProofKernel

/-!
# Retained Gaussian laws from the physical measurability obligations

Packet PROVE-RETPLUMB. The filtration, stop-line chart, capped versions, and line
kernels are discharged here. The remaining clock and line-safe measurability
obligations are explicit premises of the conditional helper below. This does not
assert Lemma 7.6 or discharge stopped K2.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F DomainMarkov DomainMarkov.Aux79 K2

universe v

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {η₁' η₂' : Ω → ℝ≥0 → ℂ} {G : ℝ≥0 → Set Ω}
    {u r : ℝ≥0} {F : Set Ω} {c₀ : BoundaryWord}

/-- Every live later line before the boundary stop is a disjoint pair of the
original paths, not merely of their measurable versions. -/
theorem ae_retPairAt (hκ : 0 < κ) (hκ4 : κ < 4)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u
      (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ F →
      (retClock G η₁' η₂' ζ₂ u r t ω : ℝ≥0∞) < retLife G η₁' η₂' ζ₂ u r ω →
      Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) (r + t) := by
  filter_upwards [ha₁, ha₂,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂]
    with ω e₁ e₂ hp₁ hp₂ hωF hlt
  obtain ⟨hp, hGr⟩ := hF ω hωF
  have hp₁' := Supp7.IsPathGood.congr hp₁ e₁
  have hp₂' := Supp7.IsPathGood.congr hp₂ e₂
  have hp' : Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) (r + t) := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | ht
    · subst h0
      simpa only [add_zero] using hp
    · have htL := lt_retLifeP_of_retClock_lt hd hGr hp₂' hp hlt
      exact isDisjointPair_of_lt_contStop hp₁' hp₂' hp
        (lt_add_of_pos_right r ht) (coe_add_lt_iff.1 htL)
  exact (isDisjointPair_congr
    (fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hp'.1.le))
    (fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht).trans hp'.2.1.le)) Iff.rfl Iff.rfl).1 hp'

omit mΩ in
/-- The complement of the filled line set is exactly its retained domain. -/
theorem H_diff_retLineSet (G : ℝ≥0 → Set Ω) (η₁' η₂' : Ω → ℝ≥0 → ℂ)
    (u r t : ℝ≥0) (ω : Ω) :
    H \ retLineSet G η₁' η₂' u r t ω = (retFam G η₁' η₂' u (r + t)).D ω :=
  sdiff_sdiff_cancel_left (fun _ hz => hz.1)

/-- K2's (S), with the chart and all line kernels proved, conditional only on
the remaining physical clock and line-safe-event measurability obligations
(and the given typed live event). -/
theorem hasSafeLaw_ret_of_physical_measurability
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : ∀ r', (retFam G η₁' η₂' u r').IsMeasGood)
    (hG : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω →
      (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r')
    (hGsub : G r ⊆ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω})
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (hc₀J : c₀.jumps = jumps)
    (hc₀b : ∀ y ∉ jumps, c₀.fn y = b y)
    (hF : ∀ ω ∈ F, Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u
      (η₂' ω) (ζ₂ ω) r ∧ ω ∈ G r)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (htype : ∀ ω ∈ F, FCDet.IsFlowType κ θ₂
      (retWordAt G η₁' η₂' u κ θ₁ θ₂ c₀ r ω) (xL ω) (xR ω) ρL ρR)
    (hFm : MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0] F)
    (hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
      (retClock G η₁' η₂' ζ₂ u r t))
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t]
        (lineSafe (retClock G η₁' η₂' ζ₂ u r)
          (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
          (retLife G η₁' η₂' ζ₂ u r) (tsupport ψ) t)) :
    HasSafeLaw κ ρL ρR P
      (timeChange (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) (retClock G η₁' η₂' ζ₂ u r) hQa)
      F (retLife G η₁' η₂' ζ₂ u r) (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀)
      (PocketTraversal.geomLW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xL)
      (PocketTraversal.geomRW (retDrv G η₁' η₂' ζ₁ ζ₂ u r κ θ₁ θ₂ c₀) xR)
      fun ω => Chart.chartTransport ((hd r).isConformal_chart ω) 1
        (θ₂ * QuantumZipper.chiC κ) (QuantumZipper.chiC κ) (h ω) := by
  classical
  have hag : ∀ s : ℝ≥0, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω →
      (s : ℝ≥0∞) < ζ₂ ω → ω ∈ G s ∧
        (∀ t ≤ u, η₁' ω t = η₁ ω t) ∧ ∀ t ≤ s, η₂' ω t = η₂ ω t := by
    intro s
    filter_upwards [hG s, ha₁, ha₂] with ω hGω e₁ e₂ hu hs
    exact ⟨hGω hu hs, fun t ht => e₁ t ((ENNReal.coe_le_coe.2 ht).trans hu.le),
      fun t ht => e₂ t ((ENNReal.coe_le_coe.2 ht).trans hs.le)⟩
  choose ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ h0₁ h0₂ hag₁ hag₂ hg hker using
    fun t : ℝ≥0 => exists_retDomain_kernel hL75 hκ hκ4 hb hh hη₁ hη₂
      (hd (r + t)) (hag (r + t)) hu₀
  obtain ⟨α₁, α₂, hcα₁, hcα₂, hmα₁, hmα₂, h0α₁, h0α₂, haα₁, haα₂, _, _, _⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement
      hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR u r) u r
  obtain ⟨hdom, hfwd, hlift⟩ := chart_measurability_retSigma76 (hd r)
    (measurable_lifetime_of_isFlowLine hη₁) (measurable_lifetime_of_isFlowLine hη₂)
    hGsub (hag r) hcα₁ hcα₂ hmα₁ hmα₂ h0α₁ h0α₂ haα₁ haα₂
  have hdom0 : ∀ z, MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom} := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hdom
  have hfwd0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁' η₂' u r).chart ω).1 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hfwd
  have hlift0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r 0]
      ({ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁' η₂' u r).chart ω).2.2 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hlift
  apply hasSafeLaw_ret_of_plumbing hL75 hκ hκ4 hb hx hh hη₁ hη₂ ha₁ ha₂ hd hG
    hu₀ hc₀ hc₀J hc₀b hF htype ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    hFm hdom0 hfwd0 hlift0 hQa hS
    (fun t => retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ (ηc₁ t) (ηc₂ t) u (r + t))
    (fun t => retPhysFiltration_le_retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ (ηc₁ t) (ηc₂ t) u r t)
    (fun t => retLineSigma_le hh.1 u₀ η₁ η₂ (measurable_lifetime_of_isFlowLine hη₁)
      (measurable_lifetime_of_isFlowLine hη₂) (hc₁ t) (hc₂ t) (hm₁ t) (hm₂ t) u (r + t))
  intro t φ
  filter_upwards [hker t φ, ae_retPairAt hκ hκ4 hη₁ hη₂ ha₁ ha₂ (hd r) hF t,
    ae_retLineSet_eq hκ hκ4 hx hη₁ hη₂ ha₁ ha₂ hd hG hc₀ hF t]
    with ω hkerω hpair hD hωF hlt hsupp
  have hDeq := (H_diff_retLineSet G η₁' η₂' u r t ω).symm.trans (hD hωF hlt)
  rw [← hDeq] at hsupp ⊢
  exact hkerω (hpair hωF hlt) hsupp

end InteractingSLE.Restart.RetAux79
