/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1Flow
import InteractingSLE.Spec.Sec6.Prop61BExplored
import InteractingSLE.Spec.Sec6.CondMeanLocality
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# Two retained flow-line histories at deterministic stops: the joint conditional field

Packet PROVE-LEMMA76 (specification §7.2, proof of Lemma 7.6, p. 267–268, `source/spec/p241-288.md#lem-7.6-proof`:
"Retain the two labelled histories and their canonical germs. For the original coupling specification, Aux. lemma
56 supplies these canonical range kernels on every continuous prefix […] The stopping-time local-set theorem gives
their joint Gaussian conditional law in each complementary component"; proof of Aux. lemma 70, p. 274: "Work on a
probability-one event on which the single-path conditional-mean laws, the local-set union law and its boundary
comparison hold for every pair of rational stopped parameters").

Two paths `η 0, η 1` (in the application: capped versions of two flow lines, frozen after a cap `m`) are stopped at
**deterministic** times `s 0, s 1 ∈ [0, ∞]`. Their explored set `explored η (fun i _ => s i)` (the `ℍ`-part of
`η 0([0, s 0]) ∪ η 1([0, s 1])`) is the union of the two stopped prefixes; stopping one path at `0` gives the other
single prefix (a real seed contributes nothing in `ℍ`). Under the hypotheses of Lemma 6.2 (continuity, real seeds,
field determination = Lemma 7.5, history-sensitive locality at first entrance times = Aux. lemma 56), this file
proves, for every pair of deterministic stops:

* `isLocalSet_explored_const`: the stopped union is a local set (Lemma 6.2 with constant stopping rules);
* `condIndepEv_explored_const`: any two such stopped unions are conditionally independent given the field (both are
  determined by it);
* **`ae_tendsto_sub_explored_const`**: Proposition 3.8 for two stopped unions `A₁, A₂`: the difference of the means
  of `A₁ ∪ A₂` and `A₂` is harmonic off the union and tends to `0` at every point of `A₂ ∪ ℝ` near which
  `A₁ ⊆ A₂`;
* **`ae_condExp_exp_eq_explored_const`**: the joint Gaussian conditional law in each complementary component, given
  the germs of the stopped union **and the two labelled stopped histories**.

For two flow lines (`exists_twoHist_versions`) the hypotheses come from Lemma 7.5 (`Theorem15.Lemma75Statement`) and
Aux. lemma 56 at first entrance times (`Restart.RetainedRangeEntranceStatement`), the two named inputs of the landed
first-contact locality (`Restart.exists_fcUnion_marked_of_isFlowLine`); the conclusions are then stated for the
centred field `h − 𝔥₀` in `isLocalSet_twoHist`, `ae_tendsto_sub_twoHist` and `ae_condExp_exp_eq_twoHist`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

open QuantumZipper (H)
open LQGMetric (DistOn TestOn CondIndepEv)
open LocalSets Sec6

/-! ### Deterministic stops for paths frozen after a cap -/

section Abstract

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {k : ℕ} {η : Fin k → Ω → ℝ≥0 → ℂ} {x : Fin k → ℂ} {m : ℝ≥0}

omit mΩ in
/-- The explored set of paths frozen after a finite cap is relatively closed in `ℍ`, at any stops. -/
theorem isOpen_H_diff_explored_of_frozen {τ : Fin k → Ω → ℝ≥0∞} {ω : Ω} (hc : ∀ i, Continuous (η i ω))
    (hfr : ∀ i t, m ≤ t → η i ω t = η i ω m) : IsOpen (H \ explored η τ ω) := by
  have e : H \ explored η τ ω = H \ ⋃ i, η i ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ i ω} := by
    ext z
    simp only [explored, Set.mem_sdiff, mem_inter_iff, not_and]
    exact ⟨fun ⟨hz, h⟩ => ⟨hz, fun h' => h h' hz⟩, fun ⟨hz, h⟩ => ⟨hz, fun h' _ => h h'⟩⟩
  rw [e]
  exact QuantumZipper.isOpen_H.sdiff (isClosed_iUnion_of_finite fun i =>
    (Restart.isCompact_image_of_const (hc i) (hfr i) (τ i ω)).isClosed)

omit [IsProbabilityMeasure P] in
/-- Explored sets at deterministic stops are measurable random closed sets. -/
theorem measurable_explored_const (hc : ∀ i ω, Continuous (η i ω)) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (s : Fin k → ℝ≥0∞) : Measurable[mΩ, hittingSigma] (explored η fun i _ => s i) :=
  measurable_explored hc hηm fun _ => measurable_const

/-- **Lemma 6.2 at deterministic stops**: under the hypotheses of Lemma 6.2, the union of the prefixes of paths
frozen after a cap, stopped at deterministic times, is a local set. -/
theorem isLocalSet_explored_const (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P) (hfr : ∀ i ω t, m ≤ t → η i ω t = η i ω m)
    (s : Fin k → ℝ≥0∞) : IsLocalSet (explored η fun i _ => s i) h P :=
  isLocalSet_explored (S := fun j _ _ => s j) hh hc h0 hηm hdet hloc (fun _ => measurable_const)
    (fun j => isGalmarino_const (s j)) (fun _ _ => rfl) (fun _ => measurable_const)
    (Eventually.of_forall fun ω => isOpen_H_diff_explored_of_frozen (fun i => hc i ω) (fun i => hfr i ω))

omit [IsProbabilityMeasure P] in
/-- Explored sets at deterministic stops are almost surely determined by the field. -/
theorem comap_explored_const_le_aeSigma (hc : ∀ i ω, Continuous (η i ω))
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω)) (s : Fin k → ℝ≥0∞) :
    MeasurableSpace.comap (explored η fun i _ => s i) hittingSigma ≤
      aeSigma (MeasurableSpace.comap h inferInstance) P :=
  comap_explored_le_aeSigma (S := fun j _ _ => s j) hc hdet (fun _ => measurable_const)
    (fun j => isGalmarino_const (s j)) (fun _ _ => rfl)

/-- **Two stopped unions are conditionally independent given the field** (both are determined by it; the hypothesis
of Proposition 3.8). -/
theorem condIndepEv_explored_const (hhm : Measurable h) (hc : ∀ i ω, Continuous (η i ω))
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω)) (s₁ s₂ : Fin k → ℝ≥0∞) :
    CondIndepEv (MeasurableSpace.comap h inferInstance)
      (MeasurableSpace.comap (explored η fun i _ => s₁ i) hittingSigma)
      (MeasurableSpace.comap (explored η fun i _ => s₂ i) hittingSigma) P :=
  condIndepEv_of_ae_measurableSet hhm.comap_le
    (fun a ha => comap_explored_const_le_aeSigma hc hdet s₁ a ha)
    (fun b hb => comap_explored_const_le_aeSigma hc hdet s₂ b hb)

omit mΩ [IsProbabilityMeasure P] in
/-- The union of two explored sets at deterministic stops is the explored set at the larger stops. -/
theorem explored_const_union (s₁ s₂ : Fin k → ℝ≥0∞) (ω : Ω) :
    explored η (fun i _ => s₁ i) ω ∪ explored η (fun i _ => s₂ i) ω =
      explored η (fun i _ => max (s₁ i) (s₂ i)) ω :=
  explored_union_eq_max η _ _ ω

/-- **Proposition 3.8 for two stopped unions.** Under the hypotheses of Lemma 6.2 (paths frozen after a cap, in the
closed half-plane, from real seeds), for deterministic stops `s₁, s₂` with stopped unions `A₁, A₂` and versions `g`
of the mean of `A₁ ∪ A₂` (the explored set at the larger stops) and `g₂` of the mean of `A₂`: almost surely
`g − g₂` is, off `A₁ ∪ A₂`, a harmonic function `u`, and `u → 0` at every point of `A₂ ∪ ℝ` that has a neighbourhood
in which `A₁ ⊆ A₂`. -/
theorem ae_tendsto_sub_explored_const (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hx : ∀ i, (x i).im = 0)
    (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P) (hfr : ∀ i ω t, m ≤ t → η i ω t = η i ω m)
    (him : ∀ᵐ ω ∂P, ∀ i t, 0 ≤ (η i ω t).im) (s₁ s₂ : Fin k → ℝ≥0∞) {g g₂ : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (explored η fun i _ => max (s₁ i) (s₂ i)) h P g)
    (hg₂ : IsLocalSetMean (explored η fun i _ => s₂ i) h P g₂) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd u (H \ explored η (fun i _ => max (s₁ i) (s₂ i)) ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ explored η (fun i _ => max (s₁ i) (s₂ i)) ω →
        g ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      ∀ z₀ ∈ explored η (fun i _ => s₂ i) ω ∪ {z : ℂ | z.im = 0},
        (∃ r > 0, explored η (fun i _ => s₁ i) ω ∩ ball z₀ r ⊆ explored η (fun i _ => s₂ i) ω) →
        Tendsto u (𝓝[H \ explored η (fun i _ => max (s₁ i) (s₂ i)) ω] z₀) (𝓝 0) := by
  have hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (explored η (fun i _ => s₂ i) ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (explored η (fun i _ => s₂ i) ω)) z) := by
    filter_upwards [him] with ω hω
    exact not_isBounded_lowerUnion_explored (fun i => hc i ω) (fun i => by rw [h0 i ω]; exact hx i)
      (fun i t => hω i t)
  have hg' : IsLocalSetMean (fun ω => explored η (fun i _ => s₁ i) ω ∪ explored η (fun i _ => s₂ i) ω) h P g := by
    have e : (fun ω => explored η (fun i _ => s₁ i) ω ∪ explored η (fun i _ => s₂ i) ω) =
        explored η fun i _ => max (s₁ i) (s₂ i) := funext fun ω => explored_const_union s₁ s₂ ω
    rw [e]
    exact hg
  have := IsLocalSetMean.ae_tendsto_sub_of_union hh (measurable_explored_const hc hηm s₁)
    (measurable_explored_const hc hηm s₂) (condIndepEv_explored_const hh.measurable hc hdet s₁ s₂)
    (isLocalSet_explored_const hh hc h0 hηm hdet hloc hfr s₁)
    (isLocalSet_explored_const hh hc h0 hηm hdet hloc hfr s₂) hunb hg' hg₂
  filter_upwards [this] with ω ⟨u, hu, hrep, hlim⟩
  rw [explored_const_union s₁ s₂ ω] at hu hrep hlim
  exact ⟨u, hu, hrep, hlim⟩

/-- **The joint Gaussian conditional law in each complementary component** (proof of Lemma 7.6, p. 268: "The
stopping-time local-set theorem gives their joint Gaussian conditional law in each complementary component"). Under
the hypotheses of Lemma 6.2, for deterministic stops `s` with stopped union `A` and a version `g` of its local-set
mean: almost surely, for every test function `φ` supported in a component `C` of `ℍ ∖ A`, given the germs of `A`
**and the labelled stopped histories**, `h(φ)` is Gaussian with mean `g(φ)` and the zero-boundary variance of `C`. -/
theorem ae_condExp_exp_eq_explored_const (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (η i ω)) (h0 : ∀ i ω, η i ω 0 = x i) (hηm : ∀ i t, Measurable fun ω => η i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (η i) h P) (hfr : ∀ i ω t, m ≤ t → η i ω t = η i ω m)
    (s : Fin k → ℝ≥0∞) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean (explored η fun i _ => s i) h P g) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ explored η (fun i _ => s i) ω,
      tsupport φ ⊆ connectedComponentIn (H \ explored η (fun i _ => s i) ω) z₀ →
      P[fun ω' => cexp (I * (h ω' φ : ℂ)) |
          germSigma (explored η fun i _ => s i) h ⊔ stoppedHistSigma η (fun i _ => s i)] ω =
        cexp (I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
            (connectedComponentIn (H \ explored η (fun i _ => s i) ω) z₀) φ φ) : ℝ) : ℂ) :=
  ae_condExp_exp_eq_of_component_marked hh (measurable_explored_const hc hηm s)
    (isLocalSet_explored_const hh hc h0 hηm hdet hloc hfr s)
    (stoppedHistSigma_le hηm fun _ => measurable_const)
    (isHistoryAvoidanceLocal_explored (S := fun j _ _ => s j) hh.measurable hc h0 hηm hdet hloc
      (fun _ => measurable_const) (fun j => isGalmarino_const (s j)) (fun _ _ => rfl)) hg φ

end Abstract

/-! ### Two flow lines -/

section Flow

universe u

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

omit [IsProbabilityMeasure P] in
/-- A flow line lies almost surely in the closed half-plane on its closed available interval. -/
theorem ae_im_nonneg_of_isFlowLine' {x θ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → 0 ≤ (η ω t).im := by
  obtain ⟨_, _, W, _, _, _, -, hcoup, htr⟩ := hη
  filter_upwards [htr, hcoup.1.2.2.2.2] with ω hω hpath t ht
  have h0 := IsGeneratingTrace.mem_Hbar hω hpath.2.2.2.1 hpath.1 ht
  have him : (η ω t - x).im = (η ω t).im := by simp
  rw [← him]
  exact h0

/-- **The two retained flow-line histories as paths satisfying Lemma 6.2's hypotheses.** For two flow lines, a
cap `m` and the bounded harmonic extension `u₀` of the boundary data, there are versions `ηs 0`, `ηs 1` of the two
capped flow lines `ηᵢ(· ∧ ζᵢ ∧ m)` which are continuous, measurable at each time, started at `x₁`, `x₂`, frozen after
`m`, almost surely in the closed half-plane, almost surely Borel functions of the centred field `h − 𝔥₀` (Lemma 7.5),
and history-sensitively local at first entrance times for it (Aux. lemma 56). -/
theorem exists_twoHist_versions (hL75 : Theorem15.Lemma75Statement.{u})
    (hA56 : Restart.RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0) :
    ∃ ηs : Fin 2 → Ω → ℝ≥0 → ℂ, (∀ i ω, Continuous (ηs i ω)) ∧
      (∀ i ω, ηs i ω 0 = (![(x₁ : ℂ), (x₂ : ℂ)] : Fin 2 → ℂ) i) ∧ (∀ i t, Measurable fun ω => ηs i ω t) ∧
      (∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
        (fun ω => ηs i ω t) =ᵐ[P] fun ω => f (WholeField.centredField h u₀ ω)) ∧
      (∀ i, IsEntranceHistoryLocal (ηs i) (WholeField.centredField h u₀) P) ∧
      (∀ i ω t, m ≤ t → ηs i ω t = ηs i ω m) ∧ (∀ᵐ ω ∂P, ∀ i t, 0 ≤ (ηs i ω t).im) ∧
      (∀ᵐ ω ∂P, ∀ t, ηs 0 ω t = η₁ ω (Restart.capTime m (ζ₁ ω) t)) ∧
      (∀ᵐ ω ∂P, ∀ t, ηs 1 ω t = η₂ ω (Restart.capTime m (ζ₂ ω) t)) := by
  obtain ⟨ηs₁, hc₁, hm₁, h0₁, hfr₁, hs₁, hdet₁, -⟩ := Restart.exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηs₂, hc₂, hm₂, h0₂, hfr₂, hs₂, hdet₂, -⟩ := Restart.exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hloc₁ := (hA56 κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m ηs₁ hc₁ hm₁ hs₁).isEntranceHistoryLocal
  have hloc₂ := (hA56 κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m ηs₂ hc₂ hm₂ hs₂).isEntranceHistoryLocal
  refine ⟨![ηs₁, ηs₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs₁, hs₂⟩
  · intro i; fin_cases i
    exacts [hc₁, hc₂]
  · intro i; fin_cases i
    exacts [h0₁, h0₂]
  · intro i; fin_cases i
    exacts [hm₁, hm₂]
  · intro i; fin_cases i
    exacts [hdet₁, hdet₂]
  · intro i; fin_cases i
    exacts [hloc₁, hloc₂]
  · intro i; fin_cases i
    exacts [hfr₁, hfr₂]
  · filter_upwards [hs₁, hs₂, ae_im_nonneg_of_isFlowLine' hη₁, ae_im_nonneg_of_isFlowLine' hη₂]
      with ω ha₁ ha₂ hi₁ hi₂ i t
    fin_cases i
    · show 0 ≤ (ηs₁ ω t).im
      rw [ha₁]
      exact hi₁ _ (Restart.capTime_le m (ζ₁ ω) t)
    · show 0 ≤ (ηs₂ ω t).im
      rw [ha₂]
      exact hi₂ _ (Restart.capTime_le m (ζ₂ ω) t)

end Flow

end Sec7

end InteractingSLE
