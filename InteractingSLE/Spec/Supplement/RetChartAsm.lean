/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetChartOut
import InteractingSLE.Spec.Supplement.RetTouchMean

/-!
# The touching-pair chart boundary values: reduction to Aux. lemmas 82, 83 and 85

Packet PROVE-T15-RET5 (Theorem 1.5's leaf `RLC.RetTouchChartBoundaryStatement`; Aux. lemmas 82–86, supplement
pp. 296–301). The leaf is proved from Lemma 7.5 and four named inputs, each a single step of the source:

* **`RetTouchZonesStatement`** (deterministic; Aux. lemma 85 in the retained chart): at a touching ordinary retained
  pair, the zone data `RetChart.zoneDataT` of the retained chart have the outer boundary (OF2) (`IsTouchZones`);
* **`RetTouchSidesStatement`** (deterministic; Aux. lemma 85's sides read in the individual charts): the two
  single-path chart boundary functions along the retained chart (limits, monotonicity, value `0` at the tips);
* **`RetTouchClearStatement`** (deterministic; Aux. lemma 83, (OM2)): at an old common point on the first prefix's
  exposed right side (resp. the second prefix's exposed left side), the individual chart value has a ball missing the
  individual chart image of the transition hull `fill(K) ∖ fill(prefix)`;
* **`RetCollarMeanStatement`** (probabilistic; Aux. lemma 82): almost surely at the touching ordinary pairs, along every
  approach within the active domain on which an individual chart tends to a cleared real point, the union mean minus
  the individual range mean tends to `0`.

Main result: **`retTouchChartBoundaryStatement_of_parts`**. The datum is the measurable touching word
`RetChart.wordT` of the stopped capped copy (as `Sec7.Lemma76G.wordM` in the disjoint case); the boundary values are
`RetChart.exists_finite_tendsto_touchWord_of_clear`; the word clauses are PROVE-T15-RET4's.

R43/R48: Lemma 7.5 and the named inputs only; for Theorem 1.5.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Restart Sec6 LocalSets LQGMetric Sec7 Sec7.Lemma76F Sec7.Lemma76G Sec7.SideHeightBox RetTouch RetChart

/-! ### The named inputs -/

/-- **Named input: Aux. lemma 85 in the retained chart** (supplement pp. 299–300, (OF2)). At a touching ordinary
retained pair of two good paths (`x₂ ≤ x₁`) with the retained chart `(φ, ψ, lift)`, the touching zone data have the
outer boundary (OF2): the outer real zones left of the second base and right of the first base, the second prefix's
left side `(L₂, 0)` and exposed right side `(0, J)`, the junction `J` (the last common point), the first prefix's
exposed left side `(J, M₁)` and right side `(M₁, R₁)`. **Not proved in Lean.** -/
def RetTouchZonesStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (ζ₁ ζ₂ : ℝ≥0∞) (x₁ x₂ : ℝ) (a b : ℝ≥0) (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ),
    IsPathGood α ζ₁ x₁ → IsPathGood β ζ₂ x₂ → x₂ ≤ x₁ → IsOrdinaryRetainedPair α ζ₁ a β ζ₂ b →
    ¬ Disjoint (α '' Icc 0 a) (β '' Icc 0 b) → IsRetChart α a β b φ ψ lift →
    IsTouchZones α a β b ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b)

/-- **Named input: the individual chart boundary functions at a touching pair** (Aux. lemma 85's sides in the
individual charts; the touching analogue of `Sec7.Lemma76G.IsSetting.side₁`/`side₂`). In the setting of
`RetTouchZonesStatement`, with the zone data's (OF2) and the generating drivers `W₁`, `W₂` of the two paths: right of
the junction, the first path's individual chart composed with `ψ` has real boundary values, strictly increasing, `0`
at the first tip; left of the junction, the same for the second path, `0` at the second tip. **Not proved in Lean.** -/
def RetTouchSidesStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (ζ₁ ζ₂ : ℝ≥0∞) (x₁ x₂ : ℝ) (a b : ℝ≥0) (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (W₁ W₂ : ℝ≥0 → ℝ),
    IsPathGood α ζ₁ x₁ → IsPathGood β ζ₂ x₂ → x₂ ≤ x₁ → IsOrdinaryRetainedPair α ζ₁ a β ζ₂ b →
    ¬ Disjoint (α '' Icc 0 a) (β '' Icc 0 b) → IsRetChart α a β b φ ψ lift →
    IsTouchZones α a β b ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b) →
    IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁) → ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁} → W₁ 0 = 0 →
    IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂) → ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂} → W₂ 0 = 0 →
    ((∀ w : ℝ, (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₂ < w →
        Tendsto (fun y => physF W₁ a x₁ (ψ y)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((bdryVal (physF W₁ a x₁) ψ w : ℝ) : ℂ))) ∧
      StrictMonoOn (bdryVal (physF W₁ a x₁) ψ) (Ioi (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₂) ∧
      bdryVal (physF W₁ a x₁) ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b).M₁ = 0) ∧
    ((∀ w : ℝ, w < (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₂ →
        Tendsto (fun y => physF W₂ b x₂ (ψ y)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((bdryVal (physF W₂ b x₂) ψ w : ℝ) : ℂ))) ∧
      StrictMonoOn (bdryVal (physF W₂ b x₂) ψ) (Iio (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₂) ∧
      bdryVal (physF W₂ b x₂) ψ 0 = 0)

/-- **Named input: Aux. lemma 83, prime-end clearance at the old common points** (supplement pp. 297–298, (OM2) from
W0's proper completions). In the setting of `RetTouchSidesStatement`: at a chart point `w ∈ (M₁, R₁)` of the first
prefix's exposed right side whose image is also on the second prefix, the first path's individual chart value at `w`
has a ball missing that chart's image of the transition hull `fill(α[0,a] ∪ β[0,b]) ∖ fill(α[0,a])`; symmetrically at
`w ∈ (L₂, 0)` on the second prefix's left side with image on the first prefix. **Not proved in Lean.** -/
def RetTouchClearStatement : Prop :=
  ∀ (α β : ℝ≥0 → ℂ) (ζ₁ ζ₂ : ℝ≥0∞) (x₁ x₂ : ℝ) (a b : ℝ≥0) (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (W₁ W₂ : ℝ≥0 → ℝ),
    IsPathGood α ζ₁ x₁ → IsPathGood β ζ₂ x₂ → x₂ ≤ x₁ → IsOrdinaryRetainedPair α ζ₁ a β ζ₂ b →
    ¬ Disjoint (α '' Icc 0 a) (β '' Icc 0 b) → IsRetChart α a β b φ ψ lift →
    IsTouchZones α a β b ψ (zoneDataT φ (activeDomain α a β b) ψ α a β b) →
    IsGeneratingTrace W₁ ζ₁ (fun t => α t - x₁) → ContinuousOn W₁ {s | (s : ℝ≥0∞) < ζ₁} → W₁ 0 = 0 →
    IsGeneratingTrace W₂ ζ₂ (fun t => β t - x₂) → ContinuousOn W₂ {s | (s : ℝ≥0∞) < ζ₂} → W₂ 0 = 0 →
    (∀ w : ℝ, (zoneDataT φ (activeDomain α a β b) ψ α a β b).M₁ < w →
      w < (zoneDataT φ (activeDomain α a β b) ψ α a β b).R₁ → ψ w ∈ β '' Icc 0 b → ∃ ρ > 0,
        Disjoint (ball ((bdryVal (physF W₁ a x₁) ψ w : ℝ) : ℂ) ρ)
          (physF W₁ a x₁ '' (fillH (prefixSet α a β b) \ fillH (α '' Icc 0 a)))) ∧
    (∀ w : ℝ, (zoneDataT φ (activeDomain α a β b) ψ α a β b).L₂ < w → w < 0 → ψ w ∈ α '' Icc 0 a → ∃ ρ > 0,
        Disjoint (ball ((bdryVal (physF W₂ b x₂) ψ w : ℝ) : ℂ) ρ)
          (physF W₂ b x₂ '' (fillH (prefixSet α a β b) \ fillH (β '' Icc 0 b))))

/-- **Named input: Aux. lemma 82, the union mean at cleared prime ends** (supplement pp. 296–297). Two flow lines
(`x₂ ≤ x₁`, `θ₁ < θ₂`) of a GFF with piecewise constant boundary data, deterministic cutoffs `u`, `r`, generating
drivers `W₁`, `W₂`, capped versions `ηc₁`, `ηc₂` (cap `capR u r`), and versions `g`, `G₁`, `G₂` of the conditional
means of the centred field given the stopped union and the two stopped ranges. Almost surely at a touching ordinary
retained pair, for all harmonic representatives `v`, `vA₁`, `vA₂`: along every approach `F` within the active domain on
which the first path's individual chart tends to a real `y` whose ball misses that chart's image of the transition hull
`fill(α[0,u] ∪ β[0,r]) ∖ fill(α[0,u])`, `v − vA₁ → 0`; symmetrically for the second path. **Not proved in Lean.** -/
def RetCollarMeanStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (u r : ℝ≥0) (u₀ : ℂ → ℝ), IsBoundedHarmonicExtension b jumps u₀ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) (fun t => η₁ ω t - x₁) ∧
        ContinuousOn (fun t => W₁ t ω) {s | (s : ℝ≥0∞) < ζ₁ ω} ∧ W₁ 0 ω = 0) →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) (fun t => η₂ ω t - x₂) ∧
        ContinuousOn (fun t => W₂ t ω) {s | (s : ℝ≥0∞) < ζ₂ ω} ∧ W₂ 0 ω = 0) →
    ∀ (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g G₁ G₂ : Ω → DistOn upperHalfPlaneOpens),
      (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
      (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR u r) (ζ₁ ω) t)) →
      (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR u r) (ζ₂ ω) t)) →
      IsLocalSetMean (cstUnion ηc₁ ηc₂ u r) (WholeField.centredField h u₀) P g →
      IsLocalSetMean (fun ω => ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ u} ∩ H) (WholeField.centredField h u₀) P G₁ →
      IsLocalSetMean (fun ω => ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ r} ∩ H) (WholeField.centredField h u₀) P G₂ →
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        ¬ Disjoint (η₁ ω '' Icc 0 u) (η₂ ω '' Icc 0 r) →
        ∀ v vA₁ vA₂ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ cstUnion ηc₁ ηc₂ u r ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ cstUnion ηc₁ ηc₂ u r ω → g ω φ = ∫ z, v z * φ z) →
        InnerProductSpace.HarmonicOnNhd vA₁ (H \ (ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ u} ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ u} ∩ H) →
          G₁ ω φ = ∫ z, vA₁ z * φ z) →
        InnerProductSpace.HarmonicOnNhd vA₂ (H \ (ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ r} ∩ H)) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ r} ∩ H) →
          G₂ ω φ = ∫ z, vA₂ z * φ z) →
        (∀ y ρ : ℝ, 0 < ρ → Disjoint (ball (y : ℂ) ρ) (physF (fun t => W₁ t ω) u x₁ ''
            (fillH (prefixSet (η₁ ω) u (η₂ ω) r) \ fillH (η₁ ω '' Icc 0 u))) →
          ∀ F : Filter ℂ, F ≤ 𝓟 (activeDomain (η₁ ω) u (η₂ ω) r) →
            Tendsto (physF (fun t => W₁ t ω) u x₁) F (𝓝 (y : ℂ)) → Tendsto (fun z => v z - vA₁ z) F (𝓝 0)) ∧
        (∀ y ρ : ℝ, 0 < ρ → Disjoint (ball (y : ℂ) ρ) (physF (fun t => W₂ t ω) r x₂ ''
            (fillH (prefixSet (η₁ ω) u (η₂ ω) r) \ fillH (η₂ ω '' Icc 0 r))) →
          ∀ F : Filter ℂ, F ≤ 𝓟 (activeDomain (η₁ ω) u (η₂ ω) r) →
            Tendsto (physF (fun t => W₂ t ω) r x₂) F (𝓝 (y : ℂ)) → Tendsto (fun z => v z - vA₂ z) F (𝓝 0))

/-! ### The reduction -/

/-- **The touching-pair chart boundary values from Lemma 7.5 and Aux. lemmas 82, 83 and 85** (proof of Aux. lemma
86, supplement pp. 300–301; the touching analogue of `Sec7.Lemma76G.lemma76ChartBoundaryStatement_of_lemma75`). The
datum is the measurable touching word `wordT` of the stopped capped copy; at a touching ordinary pair it is the
truncated touching word of `zoneDataT` (`wordT_eq`, with (OF2) from `RetTouchZonesStatement`); its datum is the
boundary value of the union mean outside finitely many chart points (`exists_finite_tendsto_touchWord_of_clear`, with
the single-path side functions, the clearance and the mean comparison from the other three inputs); it is sorted, has
the first tip at the positive chart point `M₁`, and has the retained and untouched word clauses (PROVE-T15-RET4). -/
theorem retTouchChartBoundaryStatement_of_parts (hL75 : Theorem15.Lemma75Statement.{u})
    (hZ : RetTouchZonesStatement) (hS : RetTouchSidesStatement) (hCl : RetTouchClearStatement)
    (hM : RetCollarMeanStatement.{u}) : RetTouchChartBoundaryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  set χ := QuantumZipper.chiC κ with hχ
  set g₁ := -sleLambda κ - θ₂ * χ with hg₁
  set g₂ := sleLambda κ - θ₂ * χ with hg₂
  set g₃ := -sleLambda κ - θ₁ * χ with hg₃
  set g₄ := sleLambda κ - θ₁ * χ with hg₄
  obtain ⟨c₀, hc₀, hc₀J, hc₀b⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb
  set m := capR d.u d.r with hm
  have hum : d.u < m := lt_capR_left d.u d.r
  have hrm : d.r < m := lt_capR_right d.u d.r
  obtain ⟨ηs₁, hsc₁, hsm₁, hs0₁, -, hsag₁, -, -⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηs₂, hsc₂, hsm₂, hs0₂, -, hsag₂, -, -⟩ := exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hζm₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζm₂ := measurable_lifetime_of_isFlowLine hη₂
  set F := cstHist ηs₁ ηs₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) d.u d.r with hF
  have hFm : Measurable F := measurable_cstHist hsm₁ hsm₂ ((measurable_cutLife m).comp hζm₁)
    ((measurable_cutLife m).comp hζm₂) d.u d.r
  set d' := stopRet ηs₁ ηs₂ d.u d.r with hd'def
  have hd'F : @RetData.IsMeasGood Ω (MeasurableSpace.comap F inferInstance) d' :=
    isMeasGood_stopRet (ζ₁ := fun ω => cutLife (ζ₁ ω) m) (ζ₂ := fun ω => cutLife (ζ₂ ω) m) le_rfl hsc₁ hsc₂
      hs0₁ hs0₂
  have hd' : d'.IsMeasGood := RetData.IsMeasGood.mono_sigma hd'F hFm.comap_le
  set β := wordT d' c₀ g₁ g₂ g₃ g₄ with hβdef
  have hβF : Measurable[MeasurableSpace.comap F inferInstance] β :=
    @measurable_wordT Ω (MeasurableSpace.comap F inferInstance) d' hd'F c₀ g₁ g₂ g₃ g₄
  -- the retained σ-algebra
  have hFret : ∀ᵐ ω ∂P, F ω = retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r ω := by
    filter_upwards [hsag₁, hsag₂] with ω h1 h2
    have e1 : ηs₁ ω = cappedPath η₁ ζ₁ m ω := funext h1
    have e2 : ηs₂ ω = cappedPath η₂ ζ₂ m ω := funext h2
    simp only [hF, retHist76, cstHist, e1, e2]
    rfl
  have hβR : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β := by
    intro S hS
    obtain ⟨T, hT, hTS⟩ := hβF hS
    refine ⟨?_, ⟨retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r ⁻¹' T, ⟨T, hT, rfl⟩, ?_⟩⟩
    · rw [← hTS]; exact hFm hT
    · rw [← hTS]
      filter_upwards [hFret] with ω hω
      simp only [mem_preimage, hω]
  -- the pathwise facts at a touching ordinary pair
  have hpg₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hpg₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  have hword : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      ¬ Disjoint (η₁ ω '' Icc 0 d.u) (η₂ ω '' Icc 0 d.r) →
      β ω = ((zoneDataT (d.fwd ω) (activeDomain (η₁ ω) d.u (η₂ ω) d.r) (d.inv ω) (η₁ ω) d.u (η₂ ω) d.r).word
        c₀ g₁ g₂ g₃ g₄).trunc ∧
      IsTouchZones (η₁ ω) d.u (η₂ ω) d.r (d.inv ω)
        (zoneDataT (d.fwd ω) (activeDomain (η₁ ω) d.u (η₂ ω) d.r) (d.inv ω) (η₁ ω) d.u (η₂ ω) d.r) ∧
      IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) ∧ ω ∈ d.E ∧
      d.K ω = prefixSet (η₁ ω) d.u (η₂ ω) d.r ∧ d.D ω = activeDomain (η₁ ω) d.u (η₂ ω) d.r ∧
      IsPathGood (η₁ ω) (ζ₁ ω) x₁ ∧ IsPathGood (η₂ ω) (ζ₂ ω) x₂ := by
    filter_upwards [hag, hsag₁, hsag₂, ae_im_nonneg_of_isFlowLine' hη₁, ae_im_nonneg_of_isFlowLine' hη₂, hpg₁, hpg₂]
      with ω hagω e₁ e₂ hi₁ hi₂ hp₁ hp₂ hp hnd
    obtain ⟨hG, a₁, a₂⟩ := hagω hp.1 hp.2.1
    have b₁ : ∀ s ≤ d.u, d'.η₁ ω s = η₁ ω s := fun s hs => by
      show hproj (ηs₁ ω (min s d.u)) = _
      rw [min_eq_left hs, e₁ s, capTime_eq_of_lt hp.1 hum hs, hproj_of_im_nonneg]
      exact hi₁ s ((ENNReal.coe_le_coe.2 hs).trans hp.1.le)
    have b₂ : ∀ t ≤ d.r, d'.η₂ ω t = η₂ ω t := fun t ht => by
      show hproj (ηs₂ ω (min t d.r)) = _
      rw [min_eq_left ht, e₂ t, capTime_eq_of_lt hp.2.1 hrm ht, hproj_of_im_nonneg]
      exact hi₂ t ((ENNReal.coe_le_coe.2 ht).trans hp.2.1.le)
    have hG' : ω ∈ d'.G := by
      intro t ht he
      have he' : d'.η₂ ω t = d'.η₂ ω d.r := he
      rw [b₂ t ht.le, b₂ d.r le_rfl] at he'
      have := (Sec7.IsPathGood.injOn_Icc hp₂ hp.2.1.le) ⟨zero_le, ht.le⟩ ⟨zero_le, le_rfl⟩ he'
      exact (ne_of_lt ht) this
    have hE : ω ∈ d.E := hd.mem_E_of_ordinary hG a₁ a₂ hp
    obtain ⟨hEiff, -, hch⟩ := RetData.chart_eq_of_agree (d := d) (G' := d'.G) (η₁' := d'.η₁) (η₂' := d'.η₂)
      hG hG' (fun s hs => (b₁ s hs).trans (a₁ s hs).symm) (fun t ht => (b₂ t ht).trans (a₂ t ht).symm)
    have hE' : ω ∈ d'.E := hEiff.2 hE
    have hcheq : d'.chart ω = d.chart ω := hch
    rw [RetData.chart_of_mem hE', RetData.chart_of_mem hE] at hcheq
    have hfwd : d'.fwd ω = d.fwd ω := (Prod.ext_iff.1 hcheq).1
    have hinv : d'.inv ω = d.inv ω := (Prod.ext_iff.1 (Prod.ext_iff.1 hcheq).2).1
    have hC : IsRetChart (η₁ ω) d.u (η₂ ω) d.r (d.fwd ω) (d.inv ω) (d.lift ω) :=
      (isRetChart_congr a₁ a₂).1 (hd.isRetChart hE).2
    have hDeq : d.D ω = activeDomain (η₁ ω) d.u (η₂ ω) d.r := by
      rw [hd.D_of_mem hE]
      exact activeDomain_congr_Icc (fun s hs => a₁ s hs.2) (fun t ht => a₂ t ht.2)
    have ht := hZ (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω) (d.lift ω) hp₁ hp₂ hx hp hnd hC
    have htip₃ : ∀ s < d.u, η₁ ω s ≠ η₁ ω d.u := fun s hs he =>
      (ne_of_lt hs) ((Sec7.IsPathGood.injOn_Icc hp₁ hp.1.le) ⟨zero_le, hs.le⟩ ⟨zero_le, le_rfl⟩ he)
    refine ⟨?_, ht, hC, hE, ?_, hDeq, hp₁, hp₂⟩
    · have ht' : IsTouchZones (η₁ ω) d'.u (η₂ ω) d'.r (d'.inv ω)
          (zoneDataT (d'.fwd ω) (activeDomain (η₁ ω) d'.u (η₂ ω) d'.r) (d'.inv ω) (η₁ ω) d'.u (η₂ ω) d'.r) := by
        rw [hfwd, hinv]; exact ht
      rw [hβdef, wordT_eq hd' hE' b₁ b₂ ht' hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.1 htip₃ hc₀ g₁ g₂ g₃ g₄, hfwd, hinv]
      rfl
    · rw [RetData.K_of_mem hE]; exact prefixSet_congr' a₁ a₂
  refine ⟨β, hβR, ?_, ?_⟩
  · intro ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
    obtain ⟨hBm, hBloc, hBdet, hBunb⟩ :=
      cstUnion_facts hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ m d.u d.r hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
    have hF₁ := range_facts hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hu₀ m d.u hc₁ hm₁ hag₁
    have hF₂ := range_facts hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₂ hu₀ m d.r hc₂ hm₂ hag₂
    obtain ⟨G₁, hG₁⟩ := IsLocalSet.exists_isLocalSetMean hh0 hF₁.1 hF₁.2.1
    obtain ⟨G₂, hG₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hF₂.1 hF₂.2.1
    have hC₁ := ae_tendsto_sub_of_locals hh0 hBm hF₁.1 hBloc hF₁.2.1 hBdet hF₁.2.2.1 hBunb hF₁.2.2.2 hg hG₁
    have hC₂ := ae_tendsto_sub_of_locals hh0 hBm hF₂.1 hBloc hF₂.2.1 hBdet hF₂.2.2.1 hBunb hF₂.2.2.2 hg hG₂
    obtain ⟨_, _, W₁, _, _, _, -, hcoup₁, htr₁⟩ := id hη₁
    obtain ⟨_, _, W₂, _, _, _, -, hcoup₂, htr₂⟩ := id hη₂
    have hS₁ := singlePathSideHeight_slit (m := m) (q := d.u) hL75 WholeField.retainedRangeEntranceStatement hκ hκ4
      hb hh hη₁ htr₁ hu₀ hum.le hc₁ hm₁ hag₁ hG₁
    have hS₂ := singlePathSideHeight_slit (m := m) (q := d.r) hL75 WholeField.retainedRangeEntranceStatement hκ hκ4
      hb hh hη₂ htr₂ hu₀ hrm.le hc₂ hm₂ hag₂ hG₂
    have hdec := Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hBm hBloc hg
    have hdrv₁ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W₁ t ω) (ζ₁ ω) (fun t => η₁ ω t - x₁) ∧
        ContinuousOn (fun t => W₁ t ω) {s | (s : ℝ≥0∞) < ζ₁ ω} ∧ W₁ 0 ω = 0 := by
      filter_upwards [htr₁, hcoup₁.1.2.2.2.2] with ω h1 h2 using ⟨h1, h2.2.2.2.1, h2.1⟩
    have hdrv₂ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W₂ t ω) (ζ₂ ω) (fun t => η₂ ω t - x₂) ∧
        ContinuousOn (fun t => W₂ t ω) {s | (s : ℝ≥0∞) < ζ₂ ω} ∧ W₂ 0 ω = 0 := by
      filter_upwards [htr₂, hcoup₂.1.2.2.2.2] with ω h1 h2 using ⟨h1, h2.2.2.2.1, h2.1⟩
    have hcol := hM κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d.u d.r u₀ hu₀ W₁ W₂ hdrv₁
      hdrv₂ ηc₁ ηc₂ g G₁ G₂ hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg hG₁ hG₂
    filter_upwards [hword, hag₁, hag₂, hdrv₁, hdrv₂, hC₁, hC₂, hS₁, hS₂, hdec, hG₁.2.1, hG₂.2.1, hcol]
      with ω hwordω e₁ e₂ hdrv₁ω hdrv₂ω hC₁ω hC₂ω hS₁ω hS₂ω hdecω hR₁ω hR₂ω hcolω hp v hv hvrep
    obtain ⟨hp, hnd⟩ := hp
    obtain ⟨hβω, ht, hC, hE, hK, hDeq, hp₁, hp₂⟩ := hwordω hp hnd
    obtain ⟨htr₁ω, hWc₁ω, hW0₁ω⟩ := hdrv₁ω
    obtain ⟨htr₂ω, hWc₂ω, hW0₂ω⟩ := hdrv₂ω
    -- the sets
    have i₁ : ηc₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u :=
      image_congr fun s hs => by rw [e₁ s, capTime_eq_of_lt hp.1 hum hs.2]
    have i₂ : ηc₂ ω '' Icc 0 d.r = η₂ ω '' Icc 0 d.r :=
      image_congr fun t ht => by rw [e₂ t, capTime_eq_of_lt hp.2.1 hrm ht.2]
    have hU : cstUnion ηc₁ ηc₂ d.u d.r ω = d.K ω ∩ H := by
      rw [cstUnion_eq, hK, prefixSet, i₁, i₂]
    have hA₁ : ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.u} ∩ H = η₁ ω '' Icc 0 d.u ∩ H := by
      rw [Sec7.image_capped_eq e₁ (le_min hp.1.le (ENNReal.coe_le_coe.2 hum.le))]
    have hA₂ : ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.r} ∩ H = η₂ ω '' Icc 0 d.r ∩ H := by
      rw [Sec7.image_capped_eq e₂ (le_min hp.2.1.le (ENNReal.coe_le_coe.2 hrm.le))]
    obtain ⟨vA₁, hvA₁, hvA₁r⟩ := hR₁ω
    obtain ⟨vA₂, hvA₂, hvA₂r⟩ := hR₂ω
    obtain ⟨hcm₁, hcm₂⟩ := hcolω hp hnd v vA₁ vA₂ hv hvrep hvA₁ hvA₁r hvA₂ hvA₂r
    have hdec' := hdecω v hv hvrep
    have hcmp₁ := hC₁ω v vA₁ hv hvrep hvA₁ hvA₁r
    have hcmp₂ := hC₂ω v vA₂ hv hvrep hvA₂ hvA₂r
    rw [hU] at hdec' hcmp₁ hcmp₂
    rw [hA₁] at hcmp₁
    rw [hA₂] at hcmp₂
    have hsh₁ := hS₁ω hp.1 vA₁ hvA₁ hvA₁r
    have hsh₂ := hS₂ω hp.2.1 vA₂ hvA₂ hvA₂r
    -- positivity of the cutoffs
    have hu0 : 0 < d.u := by
      refine pos_iff_ne_zero.2 fun h0 => ?_
      have h1 : (0 : ℝ) < (η₁ ω d.u).im := hp.2.2.1
      rw [h0, Sec7.IsPathGood.zero hp₁] at h1
      simp at h1
    have hr0 : 0 < d.r := by
      refine pos_iff_ne_zero.2 fun h0 => ?_
      have h1 : (0 : ℝ) < (η₂ ω d.r).im := hp.2.2.2.1
      rw [h0, Sec7.IsPathGood.zero hp₂] at h1
      simp at h1
    -- the inputs in the retained chart
    obtain ⟨hfun₁, hfun₂⟩ := hS (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω) (d.lift ω)
      (fun t => W₁ t ω) (fun t => W₂ t ω) hp₁ hp₂ hx hp hnd hC ht htr₁ω hWc₁ω hW0₁ω htr₂ω hWc₂ω hW0₂ω
    obtain ⟨hcl₁, hcl₂⟩ := hCl (η₁ ω) (η₂ ω) (ζ₁ ω) (ζ₂ ω) x₁ x₂ d.u d.r (d.fwd ω) (d.inv ω) (d.lift ω)
      (fun t => W₁ t ω) (fun t => W₂ t ω) hp₁ hp₂ hx hp hnd hC ht htr₁ω hWc₁ω hW0₁ω htr₂ω hWc₂ω hW0₂ω
    rw [← hDeq] at hcm₁ hcm₂
    obtain ⟨E, hEf, hlim⟩ := exists_finite_tendsto_touchWord_of_clear (χ := χ) (g₁ := g₁) (g₂ := g₂) (g₃ := g₃)
      (g₄ := g₄) hd hE ht hC hp₁ hp₂ hp.1 hp.2.1 hu0 hr0 hK htr₁ω hWc₁ω hW0₁ω htr₂ω hWc₂ω hW0₂ω hfun₁ hfun₂
      hu₀.2.2 hdec' hcmp₁ hcmp₂ (fun p F hF hFle y hy => hsh₁ p F hF hFle y hy)
      (fun p F hF hFle y hy => hsh₂ p F hF hFle y hy) hcl₁ hcl₂ hcm₁ hcm₂ hc₀ hc₀J hc₀b
    refine ⟨E, hEf, fun w hw => ?_⟩
    rw [hβω, BoundaryWord.trunc_fn]
    exact hlim w hw
  · filter_upwards [hword] with ω hω hp hnd
    obtain ⟨hβω, ht, -, -, -, hDeq, -, -⟩ := hω hp hnd
    rw [hβω]
    refine ⟨(GoodT.word_isSorted ht.good hc₀).trunc, ?_, isRetainedWord_touchWord ht hc₀ κ θ₁ θ₂,
      isUntouchedWord_touchWord ht hc₀ hc₀J hc₀b g₁ g₂ g₃ g₄⟩
    have e : tipPos d η₁ ω =
        (zoneDataT (d.fwd ω) (activeDomain (η₁ ω) d.u (η₂ ω) d.r) (d.inv ω) (η₁ ω) d.u (η₂ ω) d.r).M₁ := by
      simp only [tipPos, zoneDataT, chartPt, hDeq]
    rw [e]
    exact ht.zero_lt_M₁

end RLC

end InteractingSLE
