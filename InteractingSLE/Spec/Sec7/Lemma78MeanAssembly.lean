/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1MeanChart
import InteractingSLE.Spec.Sec6.Prop61BGlobal
import InteractingSLE.Spec.Sec6.DiskCaratheodory
import InteractingSLE.Spec.Sec7.Lemma78MeanReal
import InteractingSLE.Spec.Sec7.Lemma78MeanBdry
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Complex.RiemannMap

/-!
# Lemma 7.8's mean formula on every box from its boundary values in the chart

Packet PROVE-PRIMEEND2, item (d) of `planning/handoffs/PROVE-PRIMEEND.md` ("the assembly"). Lemma 7.8's proof
(p. 294): "Aux. lemma 29, applied in these bounded coordinates to that finite set of physical points, now gives
`𝒞_K = 𝔤 ∘ φ − χ arg φ′` on `D`." Here the uniqueness step is the landed `Sec6.ae_eqOn_component_of_tendsto_global`
(Aux. 28 with logarithmic growth at `∞`, on every component), applied to the first-contact union of two capped flow
lines, the component `D`, the Riemann map `ψ ∘ cayleyInv` (`ψ = d.inv` the inverse of the first-contact chart) and the
candidate `𝔤_β ∘ φ − χ arg φ′` with `𝔤_β` the word mean. Its prime ends are read in the chart: a point `q ≠ 1` of the
unit circle is the real point `cayleyInv q`.

What it needs is the boundary behaviour of the actual mean in chart coordinates (`IsBoxChartBoundaryLimit`): at every
real chart point `w` outside a finite set, `(v + 𝔥₀ + χ arg φ′)(ψ(z)) → 𝔤_β(w)` as `z → w` in `ℍ`, for every
harmonic representative `v` of the union mean. Lemma 7.8's proof supplies it from three sources: the real-boundary
decay (`Sec7.IsLocalSetMean.ae_tendsto_zero_of_real`) on untouched original real intervals, the single-path
comparisons on the exposed sides, and Aux. 57 for the derivative-argument branch.

## Main results

* `isLocalSet_fcUnion_of_isFlowLine`: for **every** pair of capped versions of the two flow lines, their first-contact
  union is a local set of the centred field (Lemma 7.7, through Lemmas 7.5, 7.7 and Aux. 56 at first entrances);
* `IsBoxChartBoundaryLimit`: the boundary values of the union mean in the first-contact chart;
* **`isBoxPointwiseMean_of_chartBoundaryLimit`**: `IsBoxChartBoundaryLimit` and the sortedness of `β` give
  `IsBoxPointwiseMean` (Lemma 7.8's mean formula on every box), hence `IsBoxMeanIdentification`.
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

namespace Restart

open LQGMetric (DistOn TestOn)
open LocalSets

/-! ### The first-contact union of any capped versions is a local set -/

section Local

/-- The first-contact union only depends on the two paths at `ω`. -/
theorem fcUnion_congr {Ω : Type*} {ηa₁ ηa₂ ηb₁ ηb₂ : Ω → ℝ≥0 → ℂ} {ω : Ω} (e₁ : ηa₁ ω = ηb₁ ω)
    (e₂ : ηa₂ ω = ηb₂ ω) : fcUnion ηa₁ ηa₂ ω = fcUnion ηb₁ ηb₂ ω := by
  rw [fcUnion_eq, fcUnion_eq]
  simp only [fullHist, e₁, e₂]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 7.7's locality for every pair of capped versions**: in the setting of `FirstContactKernelClockStatement`,
for every cap `m` and all versions `ηc₁, ηc₂` almost surely equal to the capped flow lines, the first-contact union
`fcUnion ηc₁ ηc₂` is a local set of the centred field `h − 𝔥₀`. (`exists_fcUnion_marked_of_isFlowLine` builds one
pair of versions; local sets are a property of the law, so all versions follow.) -/
theorem isLocalSet_fcUnion_of_isFlowLine (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (m : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) :
    IsLocalSet (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P := by
  obtain ⟨ηs₁, hc₁, hm₁, h0₁, hfr₁, hs₁, hdet₁, hdetζ₁⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηs₂, hc₂, hm₂, h0₂, hfr₂, hs₂, hdet₂, hdetζ₂⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hloc₁ := hA56 κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m ηs₁ hc₁ hm₁ hs₁
  have hloc₂ := hA56 κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m ηs₂ hc₂ hm₂ hs₂
  have hζm₁ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζm₂ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₂)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- Lemma 7.7's common first point for the capped paths
  have hfc : ∀ᵐ ω ∂P, (∃ s t : ℝ≥0, ηs₁ ω s = ηs₂ ω t) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (ηs₁ ω) ⊤ (ηs₂ ω) ⊤ s₀ t₀ := by
    filter_upwards [hL77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, hs₁, hs₂]
      with ω h77 ha₁ ha₂
    rintro ⟨s, t, hst⟩
    rw [ha₁, ha₂] at hst
    obtain ⟨s₀, t₀, hfc, -, -⟩ := h77 ⟨_, _, capTime_le m (ζ₁ ω) s, capTime_le m (ζ₂ ω) t, hst⟩
    obtain ⟨hs₀, ht₀⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s) (capTime_le m (ζ₂ ω) t) hst
    have hcs₀ : capTime m (ζ₁ ω) s₀ = s₀ := capTime_of_le m (ζ₁ ω)
      (le_min hfc.1 (ENNReal.coe_le_coe.2 (hs₀.trans (capTime_le_cap m (ζ₁ ω) s))))
    have hct₀ : capTime m (ζ₂ ω) t₀ = t₀ := capTime_of_le m (ζ₂ ω)
      (le_min hfc.2.1 (ENNReal.coe_le_coe.2 (ht₀.trans (capTime_le_cap m (ζ₂ ω) t))))
    refine ⟨s₀, t₀, le_top, le_top, ?_, fun s' t' _ _ he => ?_⟩
    · rw [ha₁, ha₂, hcs₀, hct₀]
      exact hfc.2.2.1
    · rw [ha₁, ha₂] at he
      obtain ⟨a, c⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s') (capTime_le m (ζ₂ ω) t') he
      exact ⟨a.trans (min_le_left _ _), c.trans (min_le_left _ _)⟩
  -- the capped union is relatively closed
  have hcl : ∀ᵐ ω ∂P, IsOpen (H \ fcUnion ηs₁ ηs₂ ω) := by
    refine Eventually.of_forall fun ω => ?_
    have hK : IsCompact (ηs₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist ηs₁ ηs₂ ω)} ∪
        ηs₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist ηs₁ ηs₂ ω)}) :=
      (isCompact_image_of_const (hc₁ ω) (hfr₁ ω) _).union (isCompact_image_of_const (hc₂ ω) (hfr₂ ω) _)
    have e : H \ fcUnion ηs₁ ηs₂ ω = H \ (ηs₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recFst (fullHist ηs₁ ηs₂ ω)} ∪
        ηs₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ recSnd (fullHist ηs₁ ηs₂ ω)}) := by
      rw [fcUnion_eq]
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, not_and]
      exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hu => hn hu hz⟩, fun ⟨hz, hn⟩ => ⟨hz, fun hu _ => hn hu⟩⟩
    rw [e]
    exact QuantumZipper.isOpen_H.sdiff hK.isClosed
  have hloc := isLocalSet_fcUnion (x₁ := (x₁ : ℂ)) (x₂ := (x₂ : ℂ)) hh0.measurable hc₁ hc₂ h0₁ h0₂ hm₁ hm₂ hζm₁ hζm₂
    hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc hh0 hcl
  refine Sec7.IsLocalSet.congr_ae hloc ?_
  filter_upwards [hag₁, hag₂, hs₁, hs₂] with ω ha₁ ha₂ hb₁ hb₂
  exact fcUnion_congr (funext fun t => (ha₁ t).trans (hb₁ t).symm) (funext fun t => (ha₂ t).trans (hb₂ t).symm)

end Local

/-! ### The boundary values in the chart and the assembly -/

section Assembly

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The boundary values of the union mean in the first-contact chart** (the input of Aux. 28/29 in Lemma 7.8's
proof, pp. 293–294). For every cap `m`, every pair of capped versions and every version `g` of the local-set mean of
their first-contact union (for the centred field `h − 𝔥₀`): almost surely on the box `m`, for every harmonic
representative `v` of `g` off the union, there is a finite set `E` of real chart points such that at every other real
chart point `w`, `v + 𝔥₀ + χ arg φ′`, read through the chart inverse `ψ = d.inv`, tends to the word datum `β(w)`. -/
def IsBoxChartBoundaryLimit (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) (d : PairData Ω) (β : Ω → BoundaryWord) : Prop :=
  ∀ (m : ℕ) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) →
    IsLocalSetMean (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ fcUnion ηc₁ ηc₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fcUnion ηc₁ ηc₂ ω → g ω φ = ∫ z, v z * φ z) →
      ∃ E : Set ℝ, E.Finite ∧ ∀ w : ℝ, w ∉ E →
        Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
          (𝓝[H] (w : ℂ)) (𝓝 ((β ω).fn w))

/-- The real chart points of the unit circle: `cayleyInv q` is real for `‖q‖ = 1`. -/
theorem cayleyInv_eq_ofReal_re {q : ℂ} (hq : q ∈ sphere (0 : ℂ) 1) : cayleyInv q = ((cayleyInv q).re : ℂ) := by
  refine Complex.ext (by simp) ?_
  rw [ofReal_im, QuantumZipper.CA.im_cayleyInv, mem_sphere_zero_iff_norm.1 hq, one_pow, sub_self, zero_div]

/-- **The deterministic core of the assembly**: on the contact event, a harmonic representative `v` of a distribution
on `D` whose chart boundary values are those of the sorted word `c` (outside a finite set) satisfies
`v + 𝔥₀ = 𝔤_c ∘ φ − χ arg φ′` on `D`, as soon as the uniqueness statement of Aux. 28 is available on `D`. This lemma
builds the chart data and the boundary hypothesis of `Sec6.ae_eqOn_component_of_tendsto_global`. -/
theorem tendsto_disk_of_chartBoundaryLimit {d : PairData Ω} (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E)
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
  have hC := (hd.isFirstContactChart hE).2
  have hfi : ∀ y ∈ H, d.fwd ω (d.inv ω y) = y := hC.2.2.1
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  have hζH : cayleyInv ζ ∈ H := QuantumZipper.CA.cayleyInv_mem_H hζ
  simp only [Function.comp_apply, hfi _ hζH]
  ring

variable [IsProbabilityMeasure P] {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **Lemma 7.8's mean formula on every box from its chart boundary values** (p. 294: "Aux. lemma 29, applied in
these bounded coordinates to that finite set of physical points, now gives `𝒞_K = 𝔤 ∘ φ − χ arg φ′` on `D`"). In the
setting of `FirstContactWordKernelStatement`, with Lemma 7.5, Lemma 7.7 and Aux. 56 at first entrances (the inputs of
the glued (R1)), a datum `β` that is sorted on the meeting branch and has the chart boundary values of the union mean
(`IsBoxChartBoundaryLimit`) satisfies Lemma 7.8's formula on every box (`IsBoxPointwiseMean`). -/
theorem isBoxPointwiseMean_of_chartBoundaryLimit {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hL75 : Theorem15.Lemma75Statement.{u}) (hL77 : Supp10.Lemma77Statement.{u})
    (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hsort : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hbd : IsBoxChartBoundaryLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d β) :
    IsBoxPointwiseMean κ P h η₁ η₂ ζ₁ ζ₂ u₀ d β := by
  subst hζ₁ hζ₂
  intro m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
  set χ := QuantumZipper.chiC κ with hχ
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hA := measurable_fcUnion hc₁ hc₂ hm₁ hm₂
  have hloc := isLocalSet_fcUnion_of_isFlowLine hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m hag₁ hag₂
  obtain ⟨hu₀h, ⟨M₀, hM₀⟩, -⟩ := hu₀
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀h z hz).1.continuousAt.continuousWithinAt
  have hid := Sec6.ae_eqOn_component_of_tendsto_global hh0 hA hloc hg hu₀h ⟨M₀, hM₀⟩ χ
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  filter_upwards [hid, hbd m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hsort, hcmp, hae, hag₁, hag₂, hg.2.1,
    hloc.2.1] with ω hidω hbdω hsortω hcmpω haeω hc₁' hc₂' ⟨v, hv, hvrep⟩ ⟨_, hAo⟩ hbox φ hφ
  obtain ⟨-, heq⟩ := hcmpω
  obtain ⟨-, ha₁, ha₂⟩ := haeω
  have hE : ω ∈ d.E := (mem_meetBox_iff.1 hbox).1
  have hcs : (β ω).IsSorted := hsortω (mem_iUnion.2 ⟨m, hbox⟩)
  -- the union on the box and the component `D`
  have hU : fcUnion ηc₁ ηc₂ ω = d.K ω ∩ H := fcUnion_eq_K_of_good m hbox ha₁ ha₂ hc₁' hc₂' (heq hbox)
  obtain ⟨z₀, hz₀⟩ := nonempty_D hd ω
  have hDcc := D_eq_connectedComponentIn hd ω hz₀
  have hz₀' : z₀ ∈ H \ fcUnion ηc₁ ηc₂ ω := by
    rw [hU, H_diff_inter_H]
    exact HalfPlaneSep.H_diff_fillH_subset_H_diff (hd.isCompact_K ω).isClosed hz₀
  have hcc : connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀ = d.D ω := by
    rw [hU, H_diff_inter_H, ← hDcc]
  have hDU : d.D ω ⊆ H \ fcUnion ηc₁ ηc₂ ω := hcc ▸ connectedComponentIn_subset _ _
  -- the chart data
  have hC := (hd.isFirstContactChart hE).2
  obtain ⟨hact, hψbij, -, -, hlc, hder, hψd, -⟩ := hC
  rw [← hd.D_of_mem hE] at hact hψbij hlc hder
  have hf : IsConformalBijection (d.inv ω ∘ cayleyInv) (ball 0 1) (connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀) :=
    hcc ▸ isConformalBijection_comp ⟨hψd, hψbij⟩ isConformalBijection_cayleyInv
  have hφc : IsConformalBijection (d.fwd ω) (connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀) {w : ℂ | 0 < w.im} :=
    hcc ▸ ⟨hact.2.1, hact.1⟩
  have hmean := (β ω).isBoundedHarmonicExtension_mean hcs
  obtain ⟨Eℝ, hEfin, hlim⟩ := hbdω hbox v hv hvrep
  have hEd : (insert (1 : ℂ) ((fun w : ℝ => cayley (w : ℂ)) '' (Eℝ ∪ ↑(β ω).jumps))).Finite :=
    ((hEfin.union (β ω).jumps.finite_toSet).image _).insert 1
  have heqD := hidω z₀ hz₀' v hv hvrep (d.inv ω ∘ cayleyInv) (d.fwd ω) (β ω).mean (d.lift ω) _ hf hφc hmean.1
    ⟨hmean.2.1.choose, fun w hw => hmean.2.1.choose_spec w hw⟩ (hcc ▸ hlc)
    (fun z hz => by rw [hcc] at hz; rw [mul_comm _ I]; exact hder z hz) hEd
    (tendsto_disk_of_chartBoundaryLimit hd hE hcs χ hlim)
  rw [hcc] at heqD
  -- the pairing
  have hφU : tsupport φ ⊆ H \ fcUnion ηc₁ ηc₂ ω := hφ.trans hDU
  have hvc : ContinuousOn v (H \ fcUnion ηc₁ ηc₂ ω) := fun z hz => (hv z hz).1.continuousAt.continuousWithinAt
  have hi₁ : Integrable fun z => v z * φ z := integrable_mul_test hAo hvc φ hφU
  have hi₂ : Integrable fun z => u₀ z * φ z := integrable_mul_test QuantumZipper.isOpen_H hu₀c φ φ.tsupport_subset
  rw [add_apply, hvrep φ hφU,
    SupercriticalConformalCovariance.GM24.smoothDist_apply (B := upperHalfPlaneOpens) hu₀c φ]
  have hi₂' : (∫ z, φ z * u₀ z) = ∫ z, u₀ z * φ z := by simp_rw [mul_comm]
  rw [hi₂', ← integral_add hi₁ hi₂]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show v z * φ z + u₀ z * φ z = ((β ω).mean (d.fwd ω z) - χ * d.lift ω z) * φ z
  by_cases hz : z ∈ tsupport φ
  · rw [← heqD z (hφ hz)]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hz]
    ring

end Assembly

end Restart

end InteractingSLE
