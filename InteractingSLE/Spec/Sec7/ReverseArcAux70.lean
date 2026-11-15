/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ReverseArcMain
import InteractingSLE.Spec.Sec7.Aux70
import InteractingSLE.Spec.Sec7.Aux70Wire
import InteractingSLE.Spec.Sec7.SideHeight

/-!
# Aux. lemma 70 without the geometric input: interior-tip stops and the assembly

Packet PROVE-LEMMA76B (specification §7.2, Aux. lemma 70, p. 274). PROVE-LEMMA76's `aux70Statement_of_inputs`
(`Aux70.lean`) derives Aux. lemma 70 from Lemma 7.5, Aux. lemma 56 at first entrances, the single-path side heights
(`SinglePathSideHeightStatement`) and the chart geometry of the reverse arc (`ReverseArcChartStatement`). This file
removes the last input:

* `exists_rat_reverseArc_mem_H`: the rational stops of `exists_rat_reverseArc` can be chosen with **interior tips**
  `α(q₁), β(q₂) ∈ ℍ` (interior times of good paths are dense, `IsPathGood.exists_rat_mem_H`);
* at interior tips the chart geometry is proved (`ReverseArc.reverseArcChart_of_mem_H`, `ReverseArcMain.lean`);
* **`aux70Statement_of_sideHeight`**: Aux. lemma 70 from Lemma 7.5, Aux. lemma 56 at first entrances and the
  single-path side heights alone; with PROVE-SIDEHEIGHT's `SideHeight.singlePathSideHeightStatement_of_inputs`,
  **`aux70Statement_of_lemma75`**: Aux. lemma 70 from Lemma 7.5 and Aux. lemma 56 at first entrances.

The proof of `aux70Statement_of_sideHeight` is PROVE-LEMMA76's assembly, with the interior-tip selection and the proved
chart geometry in place of `ReverseArcChartStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6 Restart

universe u

/-! ### Interior-tip stops -/

section Select

variable {α β : ℝ≥0 → ℂ} {A B : ℝ≥0} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **The rational stops of a reverse minimal common arc, with interior tips** (the selection of
`exists_rat_reverseArc`, proof of Aux. lemma 70, p. 274, with both rational stops chosen at interior times). -/
theorem exists_rat_reverseArc_mem_H (hα : ContinuousOn α (Icc 0 A)) (hβ : ContinuousOn β (Icc 0 B))
    (hαi : InjOn α (Icc 0 A)) (hβi : InjOn β (Icc 0 B)) (hpα : IsPathGood α ζ₁ x₁) (hpβ : IsPathGood β ζ₂ x₂)
    (hAζ : (A : ℝ≥0∞) ≤ ζ₁) (hBζ : (B : ℝ≥0∞) ≤ ζ₂) (hrev : ¬ NoReverseMinimalArc α A β B) :
    ∃ (r₁ r₂ : ℚ) (σ₁ σ₂ s₀ : ℝ≥0) (f : ℝ≥0 → ℝ≥0),
      (r₁ : ℝ).toNNReal < A ∧ (r₂ : ℝ).toNNReal < B ∧ σ₁ < s₀ ∧ s₀ < (r₁ : ℝ).toNNReal ∧
      σ₂ < (r₂ : ℝ).toNNReal ∧ ContinuousOn f (Icc σ₁ (r₁ : ℝ).toNNReal) ∧
      StrictAntiOn f (Icc σ₁ (r₁ : ℝ).toNNReal) ∧ f σ₁ = (r₂ : ℝ).toNNReal ∧ f (r₁ : ℝ).toNNReal = σ₂ ∧
      (∀ s ∈ Icc σ₁ (r₁ : ℝ).toNNReal, β (f s) = α s) ∧
      α '' Icc 0 (r₁ : ℝ).toNNReal ∩ β '' Icc 0 (r₂ : ℝ).toNNReal ⊆ α '' Icc σ₁ (r₁ : ℝ).toNNReal ∧
      α s₀ ∈ H ∧ α (r₁ : ℝ).toNNReal ∈ H ∧ β (r₂ : ℝ).toNNReal ∈ H := by
  simp only [NoReverseMinimalArc, not_forall, not_not] at hrev
  obtain ⟨a, c, hac, hsub⟩ := hrev
  obtain ⟨f, hfc, hfa, hfim, hfP, hfeq, -⟩ :=
    exists_strictAntiOn_of_Icc_subset_fst_image hα hβ hαi hβi hac.le hsub
  have haI : a ∈ Icc a c := ⟨le_rfl, hac.le⟩
  have hcI : c ∈ Icc a c := ⟨hac.le, le_rfl⟩
  have hcA : c ≤ A := (hfP c hcI).1.1.2
  have hfaB : f a ≤ B := (hfP a haI).1.2.1.2
  -- the first stop, with an interior tip
  obtain ⟨r₁, hr₁a, hr₁c, hr₁H⟩ := IsPathGood.exists_rat_mem_H hpα hac ((ENNReal.coe_le_coe.2 hcA).trans hAζ)
  set q₁ := (r₁ : ℝ).toNNReal with hq₁
  have hq₁I : q₁ ∈ Icc a c := ⟨hr₁a.le, hr₁c.le⟩
  -- the second stop
  have hfq₁ : f q₁ < f a := hfa haI hq₁I hr₁a
  obtain ⟨r₂, hr₂l, hr₂r, hr₂H⟩ := IsPathGood.exists_rat_mem_H hpβ hfq₁ ((ENNReal.coe_le_coe.2 hfaB).trans hBζ)
  set q₂ := (r₂ : ℝ).toNNReal with hq₂
  -- the first-path time of the second stop
  have hq₂im : q₂ ∈ f '' Icc a c := by
    rw [hfim]
    exact ⟨(hfa.antitoneOn hq₁I hcI hr₁c.le).trans hr₂l.le, hr₂r.le⟩
  obtain ⟨σ₁, hσ₁I, hfσ₁⟩ := hq₂im
  have hσ₁q₁ : σ₁ < q₁ := by
    by_contra hle
    rw [not_lt] at hle
    have := hfa.antitoneOn hq₁I hσ₁I hle
    rw [hfσ₁] at this
    exact absurd hr₂l (not_lt.2 this)
  -- an interior time on the common arc
  obtain ⟨s₀, hs₀, hs₀H⟩ := IsPathGood.exists_mem_H hpα hσ₁q₁
    ((ENNReal.coe_le_coe.2 (hr₁c.le.trans hcA)).trans hAζ)
  have hsubI : Icc σ₁ q₁ ⊆ Icc a c := Icc_subset_Icc hσ₁I.1 hq₁I.2
  refine ⟨r₁, r₂, σ₁, f q₁, s₀, f, lt_of_lt_of_le hr₁c hcA, lt_of_lt_of_le hr₂r hfaB, hs₀.1, hs₀.2, hr₂l,
    hfc.mono hsubI, hfa.mono hsubI, hfσ₁, rfl, fun s hs => hfeq s (hsubI hs), ?_, hs₀H, hr₁H, hr₂H⟩
  -- the exact overlap
  rintro z ⟨⟨s, hs, rfl⟩, ⟨t, ht, hts⟩⟩
  have hsA : s ∈ Icc 0 A := ⟨zero_le, hs.2.trans (hr₁c.le.trans hcA)⟩
  have htB : t ∈ Icc 0 B := ⟨zero_le, ht.2.trans (hr₂r.le.trans hfaB)⟩
  have hC : (s, t) ∈ contactSet α A β B := ⟨hsA, htB, hts.symm⟩
  obtain ⟨p, hpP, hp₁, hp₂⟩ := exists_mem_minimalContacts_le hα hβ hC
  -- the dominated minimal contact has its first coordinate in `[a, c]`
  have hpa : a ≤ p.1 := by
    by_contra hlt
    rw [not_le] at hlt
    have h2 := (fst_lt_iff_snd_lt_of_mem_minimalContacts hpP (hfP a haI)).1 hlt
    exact absurd (h2.trans_le hp₂) (not_lt.2 (ht.2.trans (hr₂r.le)))
  have hpc : p.1 ≤ c := hp₁.trans (hs.2.trans hq₁I.2)
  have hpI : p.1 ∈ Icc a c := ⟨hpa, hpc⟩
  have hpf : p = (p.1, f p.1) :=
    eq_of_mem_contactSet_of_fst_eq hβi hpP.1 (hfP p.1 hpI).1 rfl
  have hσ₁p : σ₁ ≤ p.1 := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 := hfa (show p.1 ∈ Icc a c from hpI) hσ₁I hlt
    rw [hfσ₁] at h1
    have h2 : p.2 = f p.1 := congrArg Prod.snd hpf
    have h3 : f p.1 ≤ q₂ := h2 ▸ hp₂.trans ht.2
    exact absurd h1 (not_lt.2 h3)
  exact ⟨s, ⟨hσ₁p.trans hp₁, hs.2⟩, rfl⟩

end Select

/-! ### Aux. lemma 70 -/

section Assembly

/-- **Aux. lemma 70 from Lemma 7.5, Aux. lemma 56 at first entrances and the single-path side heights** (a conditional
helper with the named inputs `Theorem15.Lemma75Statement`, `Restart.RetainedRangeEntranceStatement` and
`SinglePathSideHeightStatement`; the chart geometry `ReverseArcChartStatement` of PROVE-LEMMA76's
`aux70Statement_of_inputs` is no longer an input: the stops are selected with interior tips and the geometry is
`ReverseArc.reverseArcChart_of_mem_H`). The proof is PROVE-LEMMA76's assembly with these two substitutions. -/
theorem aux70Statement_of_sideHeight (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (hside : SinglePathSideHeightStatement.{u}) :
    Aux70Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ m
  classical
  set χ := QuantumZipper.chiC κ with hχ
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  set hc' := WholeField.centredField h u₀ with hc'def
  obtain ⟨ηs, hc, h0, hηm, hdet, hloc, hfr, him, hs₁, hs₂⟩ :=
    exists_twoHist_versions hL75 hA56 hκ hκ4 hb hh hη₁ hη₂ hu₀ (m : ℝ≥0)
  have hx0 : ∀ i, ((![(x₁ : ℂ), (x₂ : ℂ)] : Fin 2 → ℂ) i).im = 0 := by
    intro i; fin_cases i <;> simp
  have hηs0 : ∀ i ω, (ηs i ω 0).im = 0 := fun i ω => by rw [h0 i ω]; exact hx0 i
  -- the drivers
  obtain ⟨_, _, W₁, _, _, _, -, hcoup₁, htr₁⟩ := id hη₁
  obtain ⟨_, _, W₂, _, _, _, -, hcoup₂, htr₂⟩ := id hη₂
  have hinj₁ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hinj₂ := Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  -- the local sets and their means at every rational stop
  have hloc' : ∀ s : Fin 2 → ℝ≥0∞, IsLocalSet (explored ηs fun i _ => s i) hc' P := fun s =>
    isLocalSet_explored_const hh0 hc h0 hηm hdet hloc hfr s
  have hmean : ∀ s : Fin 2 → ℝ≥0∞, ∃ g, IsLocalSetMean (explored ηs fun i _ => s i) hc' P g := fun s =>
    IsLocalSet.exists_isLocalSetMean hh0 (measurable_explored_const hc hηm s) (hloc' s)
  choose G hG using hmean
  -- the pathwise sets
  have hA₁ : ∀ (r : ℚ) ω, explored ηs (fun i _ => stop₁ r i) ω =
      ηs 0 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H := fun r ω =>
    explored_pair_left ηs _ (hηs0 1 ω)
  have hA₂ : ∀ (r : ℚ) ω, explored ηs (fun i _ => stop₂ r i) ω =
      ηs 1 ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H := fun r ω =>
    explored_pair_right ηs _ (hηs0 0 ω)
  -- the single-path side heights at every rational stop
  have hN₁ : ∀ r : ℚ, ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) →
      ((((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) →
        G (stop₁ r) ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < (r : ℝ).toNNReal → η₁ ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η₁ ω '' Icc 0 (r : ℝ).toNNReal)] (η₁ ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)) F
          (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)).im) F
            (𝓝 (sleLambda κ - θ₁ * χ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₁ s.toNNReal ω) (r : ℝ).toNNReal (z - x₁)).im) F
            (𝓝 (-sleLambda κ - θ₁ * χ)))) := by
    intro r
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · have hg : IsLocalSetMean (fun ω => ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) hc' P
          (G (stop₁ r)) := by
        have e : (fun ω => ηs 0 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) =
            explored ηs (fun i _ => stop₁ r i) := funext fun ω => (hA₁ r ω).symm
        rw [e]
        exact hG _
      filter_upwards [hside κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ W₁ htr₁ u₀ hu₀ (m : ℝ≥0)
        (r : ℝ).toNNReal hrm (ηs 0) (hc 0) (hηm 0) hs₁ (G (stop₁ r)) hg] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  have hN₂ : ∀ r : ℚ, ∀ᵐ ω ∂P, (r : ℝ).toNNReal ≤ (m : ℝ≥0) →
      ((((r : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ₂ ω → ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ (ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) →
        G (stop₂ r) ω φ = ∫ z, v z * φ z) →
      ∀ t₀ : ℝ≥0, t₀ < (r : ℝ).toNNReal → η₂ ω t₀ ∈ H → ∀ F : Filter ℂ, F.NeBot →
        F ≤ 𝓝[H \ fillH (η₂ ω '' Icc 0 (r : ℝ).toNNReal)] (η₂ ω t₀) → ∀ y : ℝ,
        Tendsto (fun z => QuantumZipper.fwdMap (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)) F
          (𝓝 (y : ℂ)) →
          (0 < y → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)).im) F
            (𝓝 (sleLambda κ - θ₂ * χ))) ∧
          (y < 0 → Tendsto (fun z => v z + u₀ z + χ *
              (QuantumZipper.logDerivFwd (fun s : ℝ => W₂ s.toNNReal ω) (r : ℝ).toNNReal (z - x₂)).im) F
            (𝓝 (-sleLambda κ - θ₂ * χ)))) := by
    intro r
    by_cases hrm : (r : ℝ).toNNReal ≤ (m : ℝ≥0)
    · have hg : IsLocalSetMean (fun ω => ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) hc' P
          (G (stop₂ r)) := by
        have e : (fun ω => ηs 1 ω '' {t | (t : ℝ≥0∞) ≤ (r : ℝ).toNNReal} ∩ H) =
            explored ηs (fun i _ => stop₂ r i) := funext fun ω => (hA₂ r ω).symm
        rw [e]
        exact hG _
      filter_upwards [hside κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ W₂ htr₂ u₀ hu₀ (m : ℝ≥0)
        (r : ℝ).toNNReal hrm (ηs 1) (hc 1) (hηm 1) hs₂ (G (stop₂ r)) hg] with ω hω _
      exact hω
    · exact Eventually.of_forall fun ω h => absurd h hrm
  -- Proposition 3.8 at every rational pair
  have hmc : ∀ r₁ r₂ : ℚ, (fun (i : Fin 2) (_ : Ω) => max (stop₂ r₂ i) (stop₁ r₁ i)) =
      fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i) := fun _ _ => by
    funext i _
    exact max_comm _ _
  have hPa : ∀ r₁ r₂ : ℚ, ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd u (H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω →
        G (fun i => max (stop₁ r₁ i) (stop₂ r₂ i)) ω φ - G (stop₁ r₁) ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ explored ηs (fun i _ => stop₁ r₁ i) ω ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, explored ηs (fun i _ => stop₂ r₂ i) ω ∩ ball z₀ r ⊆ explored ηs (fun i _ => stop₁ r₁ i) ω) →
        Tendsto u (𝓝[H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω] z₀) (𝓝 0) := by
    intro r₁ r₂
    have hg : IsLocalSetMean (explored ηs fun i _ => max (stop₂ r₂ i) (stop₁ r₁ i)) hc' P
        (G (fun i => max (stop₁ r₁ i) (stop₂ r₂ i))) := by
      rw [hmc]
      exact hG _
    have := ae_tendsto_sub_explored_const hh0 hc h0 hx0 hηm hdet hloc hfr him (stop₂ r₂) (stop₁ r₁) hg (hG _)
    rw [hmc] at this
    exact this
  have hPb : ∀ r₁ r₂ : ℚ, ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd u (H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω →
        G (fun i => max (stop₁ r₁ i) (stop₂ r₂ i)) ω φ - G (stop₂ r₂) ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ explored ηs (fun i _ => stop₂ r₂ i) ω ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, explored ηs (fun i _ => stop₁ r₁ i) ω ∩ ball z₀ r ⊆ explored ηs (fun i _ => stop₂ r₂ i) ω) →
        Tendsto u (𝓝[H \ explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω] z₀) (𝓝 0) := fun r₁ r₂ =>
    ae_tendsto_sub_explored_const hh0 hc h0 hx0 hηm hdet hloc hfr him (stop₁ r₁) (stop₂ r₂) (hG _) (hG _)
  -- the probability-one event
  filter_upwards [hs₁, hs₂, htr₁, htr₂, hcoup₁.1.2.2.2.2, hcoup₂.1.2.2.2.2, hinj₁, hinj₂, ae_all_iff.2 hN₁,
    ae_all_iff.2 hN₂, ae_all_iff.2 fun r₁ => ae_all_iff.2 (hPa r₁), ae_all_iff.2 fun r₁ => ae_all_iff.2 (hPb r₁),
    ae_all_iff.2 fun r => (hG (stop₁ r)).2.1, ae_all_iff.2 fun r => (hG (stop₂ r)).2.1]
    with ω ha₁ ha₂ ht₁ ht₂ hp₁ hp₂ hi₁ hi₂ hn₁ hn₂ hpa hpb hr₁ hr₂
  by_contra hrev
  set T₁ := truncTime (ζ₁ ω) m with hT₁
  set T₂ := truncTime (ζ₂ ω) m with hT₂
  -- pathwise regularity of the stopped paths
  have hcont : ∀ {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {x : ℝ},
      IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x) →
      ContinuousOn (η ω) (Icc 0 (truncTime (ζ ω) m)) := fun {η ζ W x} ht => by
    have hc : ContinuousOn (fun t => (η ω t - x) + x) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ ω} :=
      ht.2.1.add continuousOn_const
    simp only [sub_add_cancel] at hc
    exact hc.mono (Icc_truncTime_subset _ m)
  have hcont₁ := hcont ht₁
  have hcont₂ := hcont ht₂
  have hinjI₁ : InjOn (η₁ ω) (Icc 0 T₁) := hi₁.mono (Icc_truncTime_subset _ m)
  have hinjI₂ : InjOn (η₂ ω) (Icc 0 T₂) := hi₂.mono (Icc_truncTime_subset _ m)
  have hpg₁ : IsPathGood (η₁ ω) (ζ₁ ω) x₁ := ⟨hi₁, fun t => W₁ t ω, hp₁.2.2.2.1, hp₁.1, ht₁⟩
  have hpg₂ : IsPathGood (η₂ ω) (ζ₂ ω) x₂ := ⟨hi₂, fun t => W₂ t ω, hp₂.2.2.2.1, hp₂.1, ht₂⟩
  obtain ⟨r₁, r₂, σ₁, σ₂, s₀, f, hq₁T, hq₂T, hσs₀, hs₀q, hσ₂q, hfc, hfa, hfσ, hfq, hfeq, hover, hs₀H, hq₁H,
    hq₂H⟩ := exists_rat_reverseArc_mem_H hcont₁ hcont₂ hinjI₁ hinjI₂ hpg₁ hpg₂ (coe_truncTime_le _ m)
      (coe_truncTime_le _ m) hrev
  set q₁ := (r₁ : ℝ).toNNReal with hq₁
  set q₂ := (r₂ : ℝ).toNNReal with hq₂
  -- the stops are strictly available and below the cap
  have hTle : ∀ ζ : ℝ≥0∞, ((truncTime ζ m : ℝ≥0) : ℝ≥0∞) = min ζ (((m : ℝ≥0)) : ℝ≥0∞) := fun ζ => by
    rw [coe_truncTime, ENNReal.coe_natCast]
  have hq₁min : (q₁ : ℝ≥0∞) ≤ min (ζ₁ ω) ((m : ℝ≥0) : ℝ≥0∞) := by
    rw [← hTle]; exact ENNReal.coe_le_coe.2 hq₁T.le
  have hq₂min : (q₂ : ℝ≥0∞) ≤ min (ζ₂ ω) ((m : ℝ≥0) : ℝ≥0∞) := by
    rw [← hTle]; exact ENNReal.coe_le_coe.2 hq₂T.le
  have hq₁ζ : (q₁ : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_lt_coe.2 hq₁T).trans_le (coe_truncTime_le _ m)
  have hq₂ζ : (q₂ : ℝ≥0∞) < ζ₂ ω := (ENNReal.coe_lt_coe.2 hq₂T).trans_le (coe_truncTime_le _ m)
  have hq₁m : q₁ ≤ (m : ℝ≥0) := by
    have := hq₁min.trans (min_le_right _ _)
    exact_mod_cast this
  have hq₂m : q₂ ≤ (m : ℝ≥0) := by
    have := hq₂min.trans (min_le_right _ _)
    exact_mod_cast this
  -- the chart geometry of the reverse arc
  obtain ⟨s, hsI, hsH, F, hFne, hF, y₁, y₂, hy₁, hy₂, hf₁, hf₂, hL⟩ :=
    ReverseArc.reverseArcChart_of_mem_H (η₁ ω) (η₂ ω) x₁ x₂ hx (fun t => W₁ t ω) (fun t => W₂ t ω) (ζ₁ ω) (ζ₂ ω)
      ht₁ hp₁.2.2.2.1 hp₁.1 ht₂ hp₂.2.2.2.1 hp₂.1 hi₁ hi₂ q₁ q₂ σ₁ σ₂ s₀ f hq₁ζ hq₂ζ hσs₀ hs₀q hσ₂q hfc hfa hfσ
      hfq hfeq hover hs₀H hq₁H hq₂H
  have := hFne
  obtain ⟨ρ, hρ, hagree⟩ := local_agree_of_reverseArc hcont₁ hcont₂ hinjI₁ hinjI₂ hq₁T.le hq₂T.le hfc hfa hfσ hfq
    hfeq hover hsI
  -- the pathwise sets
  have hA₁ω : explored ηs (fun i _ => stop₁ r₁ i) ω = η₁ ω '' Icc 0 q₁ ∩ H := by
    rw [hA₁, image_capped_eq ha₁ hq₁min]
  have hA₂ω : explored ηs (fun i _ => stop₂ r₂ i) ω = η₂ ω '' Icc 0 q₂ ∩ H := by
    rw [hA₂, image_capped_eq ha₂ hq₂min]
  have hUω : explored ηs (fun i _ => max (stop₁ r₁ i) (stop₂ r₂ i)) ω =
      (η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H) := by
    rw [← explored_const_union (stop₁ r₁) (stop₂ r₂) ω, hA₁ω, hA₂ω]
  have hsI' : s ∈ Icc σ₁ q₁ := Ioo_subset_Icc_self hsI
  have hσI : σ₁ ∈ Icc σ₁ q₁ := ⟨le_rfl, hsI'.1.trans hsI'.2⟩
  have hfs : f s < q₂ := hfσ ▸ hfa hσI hsI' hsI.1
  have hz₂ : η₂ ω (f s) = η₁ ω s := hfeq s hsI'
  have hz₀₁ : η₁ ω s ∈ η₁ ω '' Icc 0 q₁ ∩ H := ⟨⟨s, ⟨zero_le, hsI.2.le⟩, rfl⟩, hsH⟩
  have hz₀₂ : η₁ ω s ∈ η₂ ω '' Icc 0 q₂ ∩ H := ⟨⟨f s, ⟨zero_le, hfs.le⟩, hz₂⟩, hsH⟩
  have hsub₂₁ : (η₂ ω '' Icc 0 q₂ ∩ H) ∩ ball (η₁ ω s) ρ ⊆ η₁ ω '' Icc 0 q₁ ∩ H := by
    rintro z ⟨⟨hz, hzH⟩, hzb⟩
    have : z ∈ η₂ ω '' Icc 0 q₂ ∩ ball (η₁ ω s) ρ := ⟨hz, hzb⟩
    rw [← hagree] at this
    exact ⟨this.1, hzH⟩
  have hsub₁₂ : (η₁ ω '' Icc 0 q₁ ∩ H) ∩ ball (η₁ ω s) ρ ⊆ η₂ ω '' Icc 0 q₂ ∩ H := by
    rintro z ⟨⟨hz, hzH⟩, hzb⟩
    have : z ∈ η₁ ω '' Icc 0 q₁ ∩ ball (η₁ ω s) ρ := ⟨hz, hzb⟩
    rw [hagree] at this
    exact ⟨this.1, hzH⟩
  -- Proposition 3.8 at the point
  obtain ⟨ua, hua, huar, hual⟩ := hpa r₁ r₂
  obtain ⟨ub, hub, hubr, hubl⟩ := hpb r₁ r₂
  rw [hUω] at hua huar hual hub hubr hubl
  rw [hA₁ω, hA₂ω] at hual hubl
  have hla := hual (η₁ ω s) (Or.inl hz₀₁) ⟨ρ, hρ, hsub₂₁⟩
  have hlb := hubl (η₁ ω s) (Or.inl hz₀₂) ⟨ρ, hρ, hsub₁₂⟩
  -- harmonic representatives of the two single-prefix means
  obtain ⟨v₁, hv₁, hv₁r⟩ := hr₁ r₁
  obtain ⟨v₂, hv₂, hv₂r⟩ := hr₂ r₂
  have hO : IsOpen (H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H))) := by
    rw [← hUω]
    exact isOpen_H_diff_explored_of_frozen (fun i => hc i ω) (fun i => hfr i ω)
  have hO₁ : H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H)) ⊆ H \ explored ηs (fun i _ => stop₁ r₁ i) ω := by
    rw [hA₁ω]; exact sdiff_subset_sdiff_right subset_union_left
  have hO₂ : H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H)) ⊆ H \ explored ηs (fun i _ => stop₂ r₂ i) ω := by
    rw [hA₂ω]; exact sdiff_subset_sdiff_right subset_union_right
  have h12 := tendsto_sub_of_union_means hO hO₁ hO₂ hv₁ hv₁r hv₂ hv₂r hua huar hub hubr hla hlb
  -- the approach lies off the union
  have hfillsub : ∀ {K : Set ℂ}, H \ fillH K ⊆ H \ (K ∩ H) := fun {K} z hz =>
    ⟨hz.1, fun hzK => hz.2 ⟨hzK.2, Or.inl (subset_closure hzK.1)⟩⟩
  have hFO : F ≤ 𝓝[H \ ((η₁ ω '' Icc 0 q₁ ∩ H) ∪ (η₂ ω '' Icc 0 q₂ ∩ H))] (η₁ ω s) := by
    refine hF.trans (nhdsWithin_mono _ ?_)
    rw [← union_inter_distrib_right]
    exact hfillsub
  have hF₁ : F ≤ 𝓝[H \ fillH (η₁ ω '' Icc 0 q₁)] (η₁ ω s) :=
    hF.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_left)))
  have hF₂ : F ≤ 𝓝[H \ fillH (η₂ ω '' Icc 0 q₂)] (η₂ ω (f s)) := by
    rw [hz₂]
    exact hF.trans (nhdsWithin_mono _ (sdiff_subset_sdiff_right (fillH_mono subset_union_right)))
  -- the single-path side heights
  rw [hA₁ r₁ ω] at hv₁ hv₁r
  rw [hA₂ r₂ ω] at hv₂ hv₂r
  have h₁ := (hn₁ r₁ hq₁m hq₁ζ v₁ hv₁ hv₁r s hsI.2 hsH F hFne hF₁ y₁ hf₁).1 hy₁
  have h₂ := (hn₂ r₂ hq₂m hq₂ζ v₂ hv₂ hv₂r (f s) hfs (hz₂ ▸ hsH) F hFne hF₂ y₂ hf₂).2 hy₂
  exact sleLambda_sub_ne hκ hκ4 hθ (eq_of_side_limits (h12.mono_left hFO) hL h₁ h₂)

end Assembly

/-! ### Wiring -/

/-- **Aux. lemma 70 from Lemma 7.5 and Aux. lemma 56 at first entrance times** (a conditional helper): the single-path
side heights are PROVE-SIDEHEIGHT's `SideHeight.singlePathSideHeightStatement_of_inputs`. -/
theorem aux70Statement_of_lemma75 (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) : Aux70Statement.{u} :=
  aux70Statement_of_sideHeight hL75 hA56 (SideHeight.singlePathSideHeightStatement_of_inputs hL75 hA56)

/-- **Lemma 7.7** from Lemma 7.6, Lemma 7.5 and Aux. lemma 56 at first entrance times (a conditional helper). -/
theorem lemma77Statement_of_lemma76_of_lemma75 (h76 : Lemma76Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : Restart.RetainedRangeEntranceStatement.{u}) :
    Supp10.Lemma77Statement.{u} :=
  lemma77Statement_of_aux70_of_lemma76 (aux70Statement_of_lemma75 hL75 hA56) h76

/-- **Theorem 1.5's first-contact input** from the same inputs (a conditional helper). -/
theorem w8FirstContactStatement_of_lemma76_of_lemma75 (h76 : Lemma76Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u}) (hA56 : Restart.RetainedRangeEntranceStatement.{u}) :
    Theorem15.W8FirstContactStatement.{u} :=
  w8FirstContactStatement_of_aux70_of_lemma76 (aux70Statement_of_lemma75 hL75 hA56) h76

end Sec7

end InteractingSLE
