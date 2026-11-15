/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma78MeanAssembly

/-!
# Lemma 7.8's chart boundary values on untouched original real intervals

Packet PROVE-PRIMEEND2. Lemma 7.8's proof (p. 293): "On a trace-free original boundary interval, ordinary local-set
boundary decay gives the original datum", and Aux. 57 "fixes the argument lift on every untouched original-real
interval". In the first-contact chart: at a real chart point `w` whose chart preimage `x = ψ(w)` is an original real
point with a neighbourhood free of the first-contact compact `K`, the actual mean `v + 𝔥₀` tends to the original
datum `b(x)` and `arg φ′` tends to `0`, so `(v + 𝔥₀ + χ arg φ′) ∘ ψ → b(x)`.

## Main results

* `disjoint_ball_fillH_of_mem_closure`: a ball centred in `closure (ℍ \ fill K)` that misses `K` misses `fill K`;
* `PairData.IsMeasGood.D_subset_of_box`: on the box, `D ⊆ ℍ \ fcUnion` for the capped versions;
* **`ae_tendsto_chart_of_untouched`**: the untouched-real part of `IsBoxChartBoundaryLimit`, for every cap, every
  pair of capped versions and every version of the union mean.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

open LQGMetric (DistOn TestOn)
open LocalSets

/-- **A ball around an accessible real point that misses `K` misses `fill K`**: if `B(x, r)` misses the closed set
`K` and `x ∈ closure (ℍ \ fill K)`, then `B(x, r)` misses `fill K` (the upper half-ball is connected, misses `K`, and
meets the unbounded part `ℍ \ fill K`). -/
theorem disjoint_ball_fillH_of_mem_closure {K : Set ℂ} (hK : IsClosed K) {x : ℂ} {r : ℝ}
    (hdis : Disjoint (ball x r) K) (hx : x ∈ closure (H \ fillH K)) : Disjoint (ball x r) (fillH K) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr]
    exact Set.empty_disjoint _
  obtain ⟨z₁, hz₁b, hz₁D⟩ : (ball x r ∩ (H \ fillH K)).Nonempty :=
    mem_closure_iff.1 hx _ isOpen_ball (mem_ball_self hr)
  set U := ball x r ∩ H with hU
  have hUconn : IsPreconnected U := ((convex_ball x r).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im)
    Complex.imLm.isLinear 0)).isPreconnected
  have hUK : U ⊆ H \ closure K := by
    rw [hK.closure_eq]
    exact fun z hz => ⟨hz.2, fun hzK => Set.disjoint_left.1 hdis hz.1 hzK⟩
  have hz₁U : z₁ ∈ U := ⟨hz₁b, hz₁D.1⟩
  have hsub := hUconn.subset_connectedComponentIn hz₁U hUK
  refine Set.disjoint_left.2 fun z hzb hzF => ?_
  have hzU : z ∈ U := ⟨hzb, hzF.1⟩
  have hz₁nF : z₁ ∉ fillH K := hz₁D.2
  apply hz₁nF
  refine ⟨hz₁D.1, Or.inr ?_⟩
  rcases hzF.2 with hzK | hbd
  · exact absurd hzK (hUK hzU).2
  · rw [connectedComponentIn_eq (hsub hzU)]
    exact hbd

section Box

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : PairData Ω}

/-- **On the box, the chart domain lies off the capped first-contact union.** -/
theorem PairData.IsMeasGood.D_subset_of_box (hd : d.IsMeasGood) {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (m : ℕ) {ω : Ω}
    (hbox : ω ∈ meetBox d m) (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ ω t)
    (hc₁ : ∀ t, ηc₁ ω t = η₁ ω (capTime m (d.ζ₁ ω) t)) (hc₂ : ∀ t, ηc₂ ω t = η₂ ω (capTime m (d.ζ₂ ω) t))
    (heq : retHist d ω = fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω) :
    d.D ω ⊆ H \ fcUnion ηc₁ ηc₂ ω := by
  rw [fcUnion_eq_K_of_good m hbox ha₁ ha₂ hc₁ hc₂ heq, H_diff_inter_H]
  exact HalfPlaneSep.H_diff_fillH_subset_H_diff (hd.isCompact_K ω).isClosed

/-- The chart inverse sends the approach to a real chart point `w` within `ℍ` to the approach to `ψ(w)` within `D`,
and `ψ(w)` is accessible from `D`. -/
theorem PairData.IsMeasGood.tendsto_inv_real (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) (w : ℝ) :
    Tendsto (d.inv ω) (𝓝[H] (w : ℂ)) (𝓝[d.D ω] (d.inv ω w)) ∧ d.inv ω w ∈ closure (d.D ω) := by
  have hC := (hd.isFirstContactChart hE).2
  obtain ⟨-, hψbij, -, -, -, -, -, hψc, -⟩ := hC
  rw [← hd.D_of_mem hE] at hψbij
  have hwH : (w : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (w : ℂ).im by simp
  have ht : Tendsto (d.inv ω) (𝓝[H] (w : ℂ)) (𝓝 (d.inv ω w)) :=
    ((hψc w hwH).tendsto).mono_left (nhdsWithin_mono _ fun z (hz : 0 < z.im) => show (0 : ℝ) ≤ z.im from hz.le)
  have hev : ∀ᶠ z in 𝓝[H] (w : ℂ), d.inv ω z ∈ d.D ω :=
    eventually_nhdsWithin_of_forall fun z hz => hψbij.mapsTo hz
  refine ⟨tendsto_nhdsWithin_iff.2 ⟨ht, hev⟩, ?_⟩
  have hne : (𝓝[H] (w : ℂ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hwH
  exact mem_closure_of_tendsto ht hev

end Box

section Untouched

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 7.8's chart boundary values at untouched original real points** (p. 293: "On a trace-free original
boundary interval, ordinary local-set boundary decay gives the original datum"; Aux. 57 fixes the lift there). In the
setting of `FirstContactWordKernelStatement`: for every cap `m`, every pair of capped versions and every version `g`
of the union mean, almost surely on the box `m`, for every harmonic representative `v` of `g` and every real chart
point `w` whose chart preimage `x = ψ(w)` is real, is not an original jump, and has a neighbourhood free of the
first-contact compact `K`: `(v + 𝔥₀ + χ arg φ′)(ψ(z)) → b(x)` as `z → w` in `ℍ`. -/
theorem ae_tendsto_chart_of_untouched (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℕ) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    {g : Ω → DistOn upperHalfPlaneOpens} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t) (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t))
    (hg : IsLocalSetMean (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ fcUnion ηc₁ ηc₂ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fcUnion ηc₁ ηc₂ ω → g ω φ = ∫ z, v z * φ z) →
      ∀ w : ℝ, (d.inv ω w).im = 0 → (∃ r > 0, Disjoint (ball (d.inv ω w) r) (d.K ω)) →
        (d.inv ω w).re ∉ jumps →
        Tendsto (fun z => v (d.inv ω z) + u₀ (d.inv ω z) + QuantumZipper.chiC κ * d.lift ω (d.inv ω z))
          (𝓝[H] (w : ℂ)) (𝓝 (b (d.inv ω w).re)) := by
  subst hζ₁ hζ₂
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hA := measurable_fcUnion hc₁ hc₂ hm₁ hm₂
  have hloc := isLocalSet_fcUnion_of_isFlowLine hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m hag₁ hag₂
  have hdecay := Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hA hloc hg
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  filter_upwards [hdecay, hcmp, hae, hag₁, hag₂] with ω hdec hcmpω haeω hc₁' hc₂' hbox v hv hvrep w hwim
    ⟨r, hr, hdis⟩ hwj
  obtain ⟨-, heq⟩ := hcmpω
  obtain ⟨-, ha₁, ha₂⟩ := haeω
  have hE : ω ∈ d.E := (mem_meetBox_iff.1 hbox).1
  set x : ℝ := (d.inv ω w).re with hxdef
  have hxw : d.inv ω w = (x : ℂ) := Complex.ext (by simp [hxdef]) (by simp [hwim])
  obtain ⟨hT, hcl⟩ := hd.tendsto_inv_real hE w
  rw [hxw] at hT hcl hdis
  have hDU := hd.D_subset_of_box m hbox ha₁ ha₂ hc₁' hc₂' (heq hbox)
  have hdisF : Disjoint (ball (x : ℂ) r) (fillH (d.K ω)) :=
    disjoint_ball_fillH_of_mem_closure (hd.isCompact_K ω).isClosed hdis hcl
  -- the three limits
  have hTU : Tendsto (d.inv ω) (𝓝[H] (w : ℂ)) (𝓝[H \ fcUnion ηc₁ ηc₂ ω] (x : ℂ)) :=
    hT.mono_right (nhdsWithin_mono _ hDU)
  have hTH : Tendsto (d.inv ω) (𝓝[H] (w : ℂ)) (𝓝[H] (x : ℂ)) :=
    hT.mono_right (nhdsWithin_mono _ fun z hz => hz.1)
  have hdisU : Disjoint (ball (x : ℂ) r) (fcUnion ηc₁ ηc₂ ω) := by
    rw [fcUnion_eq_K_of_good m hbox ha₁ ha₂ hc₁' hc₂' (heq hbox)]
    exact hdis.mono_right inter_subset_left
  have h1 := (hdec v hv hvrep x ⟨r, hr, hdisU⟩).comp hTU
  have h2 := (hu₀.2.2 x hwj).comp hTH
  have h3 := ((hd.tendsto_lift_of_disjoint ω hr hdisF).comp hTH).const_mul (QuantumZipper.chiC κ)
  have := (h1.add h2).add h3
  simpa only [zero_add, mul_zero, add_zero, Function.comp_def] using this

end Untouched

end Restart

end InteractingSLE
