/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76FR1
import InteractingSLE.Spec.Sec7.Lemma78MeanAssembly

/-!
# Lemma 7.6: the mean identification at a disjoint pair from its chart boundary values

Packet PROVE-T15-CLOSE1 (2). Proof of Lemma 7.6, pp. 268–269: the conditional mean in the retained chart is
`𝔤_β ∘ φ − χ arg φ′` once its boundary values are known (the canonical seed, the new-slit germs, the sides of the
first path, the untouched real boundary), by the uniqueness statement of Aux. lemmas 28–29 in bounded coordinates.
This is PROVE-PRIMEEND2's assembly (`Restart.isBoxPointwiseMean_of_chartBoundaryLimit`, first-contact chart) in G7's
retained chart at a disjoint pair:

* `isLocalSet_cstUnion_of_isFlowLine`: the stopped union of **any** pair of capped versions is a local set of the
  centred field;
* **`IsRetChartBoundaryLimit`**: the boundary values of the union mean in the retained chart (outside a finite set of
  real chart points, `(v + 𝔥₀ + χ arg φ′) ∘ ψ` tends to the word datum);
* **`isRetMeanIdent_of_chartBoundaryLimit`**: `IsRetChartBoundaryLimit` and the sortedness of `β` give the mean
  identification `IsRetMeanIdent`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)

universe u

namespace InteractingSLE

namespace Sec7

namespace Lemma76F

open Supp7 Restart Sec6 LocalSets LQGMetric

section Local

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The stopped union of any pair of capped versions is a local set** of the centred field (Lemma 6.2 at
deterministic stops with killing records; inputs Lemma 7.5 and Aux. lemma 56 at first entrances). -/
theorem isLocalSet_cstUnion_of_isFlowLine (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m s t : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) :
    IsLocalSet (cstUnion ηc₁ ηc₂ s t) (WholeField.centredField h u₀) P := by
  obtain ⟨ηs₁, hc₁, hm₁, h0₁, -, hs₁, hdet₁, hdetζ₁⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηs₂, hc₂, hm₂, h0₂, -, hs₂, hdet₂, hdetζ₂⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hloc₁ := WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m
    ηs₁ hc₁ hm₁ hs₁
  have hloc₂ := WholeField.retainedRangeEntranceStatement κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m
    ηs₂ hc₂ hm₂ hs₂
  have hζm₁ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζm₂ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₂)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hloc := isLocalSet_cstUnion (x₁ := (x₁ : ℂ)) (x₂ := (x₂ : ℂ)) (u := s) (r := t) hh0.measurable hc₁ hc₂
    (fun ω => by rw [h0₁ ω]) (fun ω => by rw [h0₂ ω]) hm₁ hm₂ hζm₁ hζm₂ hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hh0
  refine Sec7.IsLocalSet.congr_ae hloc ?_
  filter_upwards [hag₁, hag₂, hs₁, hs₂] with ω ha₁ ha₂ hb₁ hb₂
  have e₁ : ηc₁ ω = ηs₁ ω := funext fun t => (ha₁ t).trans (hb₁ t).symm
  have e₂ : ηc₂ ω = ηs₂ ω := funext fun t => (ha₂ t).trans (hb₂ t).symm
  rw [cstUnion_eq, cstUnion_eq, e₁, e₂]

end Local

/-! ### The boundary values in the retained chart and the assembly -/

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The boundary values of the union mean in G7's retained chart at a disjoint pair** (the input of Aux. 28/29 in
the proof of Lemma 7.6, pp. 268–269). For every pair of capped versions (cap `capR u r`) and every version `g` of the
local-set mean of their stopped union (for the centred field `h − 𝔥₀`): almost surely at a disjoint pair, for every
harmonic representative `v` of `g` off the union, there is a finite set `E` of real chart points such that at every
other real chart point `w`, `v + 𝔥₀ + χ arg φ′`, read through the chart inverse `ψ = d.inv`, tends to the word datum
`β(w)`. -/
def IsRetChartBoundaryLimit (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) (d : RetData Ω) (β : Ω → BoundaryWord) : Prop :=
  ∀ (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) t)) →
    IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηc₁ ηc₂ d.u d.r ω → g ω φ = ∫ z, v z * φ z) →
      ∃ E : Set ℝ, E.Finite ∧ ∀ w : ℝ, w ∉ E →
        Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
          (𝓝[H] (w : ℂ)) (𝓝 ((β ω).fn w))

/-- **The deterministic core of the assembly in the retained chart** (as `Restart.tendsto_disk_of_chartBoundaryLimit`
for the first-contact chart). -/
theorem tendsto_disk_of_retChartBoundaryLimit {d : RetData Ω} (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
    {c : BoundaryWord} (hc : c.IsSorted) (χ : ℝ) {F v : ℂ → ℝ} {Eℝ : Set ℝ}
    (hlim : ∀ w : ℝ, w ∉ Eℝ → Tendsto (fun z => v (d.inv ω z) + F (d.inv ω z) + χ * d.lift ω (d.inv ω z))
      (𝓝[H] (w : ℂ)) (𝓝 (c.fn w))) :
    ∀ q ∈ sphere (0 : ℂ) 1, q ∉ insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' (Eℝ ∪ ↑c.jumps)) →
      Tendsto (fun ζ => (v ((d.inv ω ∘ cayleyInv) ζ) + F ((d.inv ω ∘ cayleyInv) ζ)) -
          (c.mean (d.fwd ω ((d.inv ω ∘ cayleyInv) ζ)) - χ * d.lift ω ((d.inv ω ∘ cayleyInv) ζ)))
        (𝓝[ball 0 1] q) (𝓝 0) := by
  intro q hq hqE
  have hq1 : q ≠ 1 := fun h1 => hqE (Set.mem_insert_iff.2 (Or.inl h1))
  set w : ℝ := (cayleyInv q).re with hw
  have hqw : cayleyInv q = (w : ℂ) := cayleyInv_eq_ofReal_re hq
  have hwE : w ∉ Eℝ ∪ ↑c.jumps := by
    intro hmem
    refine hqE (mem_insert_of_mem _ ⟨w, hmem, ?_⟩)
    show cayley (w : ℂ) = q
    rw [← hqw]
    exact QuantumZipper.CA.cayley_cayleyInv hq1
  have hT : Tendsto cayleyInv (𝓝[ball 0 1] q) (𝓝[H] (w : ℂ)) := by
    rw [← hqw]; exact Sec6.tendsto_cayleyInv_nhdsWithin_ball hq1
  have h1 := (hlim w fun h => hwE (Or.inl h)).comp hT
  have h2 := BoundaryWord.tendsto_mean_comp hc hT (fun h => hwE (Or.inr h))
  have hC := (hd.isRetChart hE).2
  have hfi : ∀ y ∈ H, d.fwd ω (d.inv ω y) = y := hC.2.2.1
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hζH : cayleyInv ζ ∈ H := QuantumZipper.CA.cayleyInv_mem_H hζ
  simp only [Function.comp_apply, hfi _ hζH]
  ring

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **The mean identification at a disjoint pair from its chart boundary values** (proof of Lemma 7.6, pp. 268–269,
with Aux. lemmas 28–29: "The remaining `L²` harmonic function has zero boundary values except at the physical point
zero and vanishes"). A datum `β`, sorted at disjoint pairs, with the chart boundary values of the union mean
(`IsRetChartBoundaryLimit`), satisfies the mean identification `IsRetMeanIdent`. Inputs: Lemma 7.5 (and Aux. 56 at
first entrances, `WholeField.retainedRangeEntranceStatement`). -/
theorem isRetMeanIdent_of_chartBoundaryLimit {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hsort : ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).IsSorted)
    (hbd : IsRetChartBoundaryLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d β) :
    IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β := by
  intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  set χ := QuantumZipper.chiC κ with hχ
  have hum : d.u < capR d.u d.r := lt_capR_left d.u d.r
  have hrm : d.r < capR d.u d.r := lt_capR_right d.u d.r
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hA := measurable_cstUnion hc₁ hc₂ hm₁ hm₂ d.u d.r
  have hloc := isLocalSet_cstUnion_of_isFlowLine hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR d.u d.r) d.u d.r hag₁ hag₂
  obtain ⟨hu₀h, ⟨M₀, hM₀⟩, -⟩ := hu₀
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀h z hz).1.continuousAt.continuousWithinAt
  have hid := Sec6.ae_eqOn_component_of_tendsto_global hh0 hA hloc hg hu₀h ⟨M₀, hM₀⟩ χ
  filter_upwards [hid, hbd ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hsort, hag, hag₁, hag₂, hg.2.1, hloc.2.1]
    with ω hidω hbdω hsortω hagω hc₁' hc₂' ⟨v, hv, hvrep⟩ ⟨_, hAo⟩ hp φ
  obtain ⟨hG, a₁, a₂⟩ := hagω hp.1 hp.2.1
  have hE : ω ∈ d.E := mem_E_of_isDisjointPair hd hG a₁ a₂ hp
  have hcs : (β ω).IsSorted := hsortω hp
  -- the stopped union and the component `D`
  have i₁ : ηc₁ ω '' Icc 0 d.u = d.η₁ ω '' Icc 0 d.u := image_congr fun s hs => by
    rw [hc₁' s, capTime_eq_of_lt hp.1 hum hs.2, a₁ s hs.2]
  have i₂ : ηc₂ ω '' Icc 0 d.r = d.η₂ ω '' Icc 0 d.r := image_congr fun t ht => by
    rw [hc₂' t, capTime_eq_of_lt hp.2.1 hrm ht.2, a₂ t ht.2]
  have hU : cstUnion ηc₁ ηc₂ d.u d.r ω = d.K ω ∩ H := by
    rw [cstUnion_eq, RetData.K_of_mem hE, prefixSet, i₁, i₂]
  have hK := hd.isCompact_K ω
  obtain ⟨R0, hR0, hKR, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hK.isClosed hK.isBounded
  have hDdef : d.D ω = H \ fillH (d.K ω) := rfl
  set z₀ : ℂ := ((R0 + 1 : ℝ) : ℂ) * I with hz₀def
  have hcc : connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) z₀ = d.D ω := by
    rw [hU, H_diff_inter_H, hDdef, hEq]
  have hz₀D : z₀ ∈ d.D ω := by
    rw [hDdef, hEq]
    refine mem_connectedComponentIn ⟨?_, fun hz => ?_⟩
    · show (0 : ℝ) < (((R0 + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith
    · have h1 := hKR hz
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
      linarith
  have hDU : d.D ω ⊆ H \ cstUnion ηc₁ ηc₂ d.u d.r ω := hcc ▸ connectedComponentIn_subset _ _
  have hz₀' : z₀ ∈ H \ cstUnion ηc₁ ηc₂ d.u d.r ω := hDU hz₀D
  -- the chart data
  have hC := (hd.isRetChart hE).2
  have h0₂ : (d.η₂ ω 0).im = 0 := (hd.good ω hG).2.2.2.2.2.1
  unfold IsRetChart at hC
  obtain ⟨hact, hψbij, -, -, hlc, hder, hψd, -⟩ := hC
  rw [activeDomain_retPath h0₂, ← hd.D_of_mem hE] at hact hψbij hlc hder
  have hf : IsConformalBijection (d.inv ω ∘ cayleyInv) (ball 0 1)
      (connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) z₀) :=
    hcc ▸ isConformalBijection_comp ⟨hψd, hψbij⟩ isConformalBijection_cayleyInv
  have hφc : IsConformalBijection (d.fwd ω) (connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) z₀)
      {w : ℂ | 0 < w.im} :=
    hcc ▸ ⟨hact.2.1, hact.1⟩
  have hmean := (β ω).isBoundedHarmonicExtension_mean hcs
  obtain ⟨Eℝ, hEfin, hlim⟩ := hbdω hp v hv hvrep
  have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' (Eℝ ∪ ↑(β ω).jumps))).Finite :=
    ((hEfin.union (β ω).jumps.finite_toSet).image _).insert 1
  have heqD := hidω z₀ hz₀' v hv hvrep (d.inv ω ∘ cayleyInv) (d.fwd ω) (β ω).mean (d.lift ω) _ hf hφc hmean.1
    ⟨hmean.2.1.choose, fun w hw => hmean.2.1.choose_spec w hw⟩ (hcc ▸ hlc)
    (fun z hz => by rw [hcc] at hz; rw [mul_comm _ I]; exact hder z hz) hEd
    (tendsto_disk_of_retChartBoundaryLimit hd hE hcs χ hlim)
  rw [hcc] at heqD
  -- the chart transport
  refine Restart.chartTransport_eq_integral_of_eq_integral (hd.isConformal_chart ω) (hd.continuousOn_lift_chart ω) χ
    (BoundaryWord.continuousOn_mean (β ω)) (fun ψ hψ => ?_) φ
  rw [hd.coe_dom_chart ω] at hψ
  rw [RetData.chart_of_mem hE]
  have hψU : tsupport ψ ⊆ H \ cstUnion ηc₁ ηc₂ d.u d.r ω := hψ.trans hDU
  have hvc : ContinuousOn v (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) := fun z hz =>
    (hv z hz).1.continuousAt.continuousWithinAt
  have hi₁ : Integrable fun z => v z * ψ z := integrable_mul_test hAo hvc ψ hψU
  have hi₂ : Integrable fun z => u₀ z * ψ z := integrable_mul_test QuantumZipper.isOpen_H hu₀c ψ ψ.tsupport_subset
  rw [add_apply, hvrep ψ hψU,
    SupercriticalConformalCovariance.GM24.smoothDist_apply (B := upperHalfPlaneOpens) hu₀c ψ]
  have hi₂' : (∫ z, ψ z * u₀ z) = ∫ z, u₀ z * ψ z := by simp_rw [mul_comm]
  rw [hi₂', ← integral_add hi₁ hi₂]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show v z * ψ z + u₀ z * ψ z = ((β ω).mean (d.fwd ω z) - χ * d.lift ω z) * ψ z
  by_cases hz : z ∈ tsupport ψ
  · rw [← heqD z (hψ hz)]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    ring

end Assembly

end Lemma76F

end Sec7

end InteractingSLE
