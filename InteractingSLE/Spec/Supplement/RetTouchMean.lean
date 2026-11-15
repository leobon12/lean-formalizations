/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76FAssembly
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj

/-!
# The touching-prefix initial word: the mean identification from the chart boundary values

Packet PROVE-T15-RET4 (Theorem 1.5's leaf `RLC.RetTouchMeanWordStatement`; Aux. lemma 86, supplement pp. 300–301,
and the ordinary retained pair of Lemma G7, p. 497, whose prefixes may meet). Aux. lemma 86's last step: once the
boundary values of the union mean in the retained chart are known outside finitely many real chart points, the
uniqueness statement of Aux. lemmas 28–29 in bounded coordinates identifies the whole conditional mean. This is
PROVE-T15-CLOSE1's assembly (`Sec7.Lemma76F.isRetMeanIdent_of_chartBoundaryLimit`, stated at disjoint pairs) on an
**arbitrary event** `O` of pairs on which the retained chart exists:

* **`IsRetChartBoundaryLimitOn`**: `Lemma76F.IsRetChartBoundaryLimit` with the disjoint-pair event replaced by `O`;
* **`isRetMeanIdentOn_of_chartBoundaryLimitOn`**: on `O` (almost surely: both cutoffs before the lifetimes and the
  chart event), the boundary values and the sortedness of the datum give the mean identification `IsRetMeanIdentOn`;
* **`RetTouchChartBoundaryStatement`** (named input): the boundary values at the ordinary retained pairs whose
  prefixes meet, with the word clauses of `RetTouchMeanWordStatement` — the touching analogue of
  `Sec7.Lemma76ChartBoundaryStatement` (Aux. lemmas 82–85 and the boundary part of Aux. lemma 86);
* **`retTouchMeanWordStatement_of_chartBoundary`**: `RetTouchMeanWordStatement` from Lemma 7.5 and that input.

R43/R48: Lemma 7.5 and the named input only; for Theorem 1.5.
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

namespace RLC

open Supp7 Restart Sec6 LocalSets LQGMetric Sec7.Lemma76F

section Defs

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The boundary values of the union mean in the retained chart on an event `O`** (`Lemma76F.IsRetChartBoundaryLimit`
with the disjoint-pair event replaced by `O`). For every pair of capped versions (cap `capR u r`) and every version `g`
of the local-set mean of their stopped union (for the centred field `h − 𝔥₀`): almost surely on `O`, for every
harmonic representative `v` of `g` off the union, there is a finite set `E` of real chart points such that at every
other real chart point `w`, `v + 𝔥₀ + χ arg φ′`, read through the chart inverse `ψ = d.inv`, tends to the word datum
`β(w)`. -/
def IsRetChartBoundaryLimitOn (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) (d : RetData Ω) (O : Set Ω) (β : Ω → BoundaryWord) : Prop :=
  ∀ (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) t)) →
    IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, ω ∈ O →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηc₁ ηc₂ d.u d.r ω → g ω φ = ∫ z, v z * φ z) →
      ∃ E : Set ℝ, E.Finite ∧ ∀ w : ℝ, w ∉ E →
        Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
          (𝓝[H] (w : ℂ)) (𝓝 ((β ω).fn w))

end Defs

section Assembly

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **The mean identification on an event from the chart boundary values** (Aux. lemmas 28–29 in bounded
coordinates; the proof of `Sec7.Lemma76F.isRetMeanIdent_of_chartBoundaryLimit` on an arbitrary event `O` on which,
almost surely, both cutoffs precede the lifetimes and the retained chart exists). -/
theorem isRetMeanIdentOn_of_chartBoundaryLimitOn {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {O : Set Ω}
    (hO : ∀ᵐ ω ∂P, ω ∈ O → (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E)
    {β : Ω → BoundaryWord} (hsort : ∀ᵐ ω ∂P, ω ∈ O → (β ω).IsSorted)
    (hbd : IsRetChartBoundaryLimitOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ d O β) :
    IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β := by
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
  filter_upwards [hid, hbd ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hsort, hag, hag₁, hag₂, hg.2.1, hloc.2.1, hO]
    with ω hidω hbdω hsortω hagω hc₁' hc₂' ⟨v, hv, hvrep⟩ ⟨_, hAo⟩ hOω hp φ
  obtain ⟨hu, hr, hE⟩ := hOω hp
  obtain ⟨-, a₁, a₂⟩ := hagω hu hr
  have hcs : (β ω).IsSorted := hsortω hp
  -- the stopped union and the component `D`
  have i₁ : ηc₁ ω '' Icc 0 d.u = d.η₁ ω '' Icc 0 d.u := image_congr fun s hs => by
    rw [hc₁' s, capTime_eq_of_lt hu hum hs.2, a₁ s hs.2]
  have i₂ : ηc₂ ω '' Icc 0 d.r = d.η₂ ω '' Icc 0 d.r := image_congr fun t ht => by
    rw [hc₂' t, capTime_eq_of_lt hr hrm ht.2, a₂ t ht.2]
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
  have hG : ω ∈ d.G := RetData.E₀_subset_G (RetData.E_subset_E₀ hE)
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

/-! ### The touching-prefix word from its chart boundary values -/

/-- **Named input: the chart boundary values at a touching ordinary retained pair** (Aux. lemmas 82–85 and the
boundary part of Aux. lemma 86, supplement pp. 296–301: the outer boundary (OF2) of an ordered union whose prefixes
meet, with the heights (OF3) on its four oriented pieces, established at old common points through the protected
prime-end collars of Aux. lemmas 82–83, and the transported original data on the untouched real boundary). The
touching analogue of `Sec7.Lemma76ChartBoundaryStatement`: a datum `β`, measurable for the retained σ-algebra, whose
word datum is, outside finitely many real chart points, the boundary value of the union mean in the retained chart at
the ordinary pairs whose prefixes meet (`IsRetChartBoundaryLimitOn`), and which there is sorted, has the first tip at
a positive chart point, and has the retained and untouched word clauses. **Not proved in Lean.** -/
def RetTouchChartBoundaryStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω), d.IsMeasGood →
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∃ β : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β ∧
      IsRetChartBoundaryLimitOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ d
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r ∧
          ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r)} β ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r) →
        (β ω).IsSorted ∧ 0 < tipPos d η₁ ω ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω) ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω)

/-- **The touching-prefix initial word from Lemma 7.5 and its chart boundary values** (Aux. lemma 86's uniqueness
step): the mean identification on the touching ordinary pairs is `isRetMeanIdentOn_of_chartBoundaryLimitOn` (at an
ordinary pair both cutoffs precede the lifetimes and the chart event holds, `IsMeasGood.mem_E_of_ordinary`); the word
clauses are the input's. -/
theorem retTouchMeanWordStatement_of_chartBoundary (hL75 : Theorem15.Lemma75Statement.{u})
    (hCB : RetTouchChartBoundaryStatement.{u}) : RetTouchMeanWordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  obtain ⟨β, hβ, hbd, hword⟩ :=
    hCB κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  refine ⟨β, hβ, ?_, hword⟩
  refine isRetMeanIdentOn_of_chartBoundaryLimitOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ ?_ ?_ hbd
  · filter_upwards [hag] with ω hω hp
    obtain ⟨hG, a₁, a₂⟩ := hω hp.1.1 hp.1.2.1
    exact ⟨hp.1.1, hp.1.2.1, hd.mem_E_of_ordinary hG a₁ a₂ hp.1⟩
  · filter_upwards [hword] with ω hω hp
    exact (hω hp.1 hp.2).1

end RLC

end InteractingSLE
