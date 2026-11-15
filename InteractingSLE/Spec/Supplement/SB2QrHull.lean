/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MoHull
import InteractingSLE.Spec.Supplement.SBS3MarkedMean
import InteractingSLE.Spec.Supplement.OrdFstShift

/-!
# A retained kernel law in the canonical hull chart gives the retained mean (D5's F3, the adapter)

Worker REVIEW-FABLE-T14 (proving phase; orchestrator adjustment: D5's F3, `hind₁` of SB2(2)'s conditional half).

The retained union `A = fill(K)` of SB2(2) is read in its canonical hull chart `Mo.hullChart A 0`. If, conditionally on
retained marks `𝒢`, the field read in that chart (possibly with a real offset `x₀`) is a Gaussian free field with the
boundary data of a word `β`, then every harmonic representative `w₁` of every local-set mean of `A` satisfies
`w₁ + u₀ = β₁.mean ∘ g_A − χ · Im (canonDerivLog A)` on `ℍ ∖ A`, `β₁` the word `β` shifted by `−x₀`: the body of
`Ms.SB2LowerRetainedMeanStatement` (`SB2MsF3`).

* `measurableSet_closedBall_subset_H_diff_fillH`: closed-disc events of the complement of a random filled compact set
  observed through its dyadic hits are measurable (compactness and the dyadic covers);
* `retainedChartData_hullChart`: the chart family `ω ↦ Mo.hullChart (fillH (K ω)) (x₀ ω)` is retained chart data
  (`S3.RetainedChartData`) for every σ-algebra for which `K` is dyadic-hit measurable and `x₀` is measurable;
* **`ae_eqOn_hullMean_of_kernelWord`**: the adapter (generic in the marks, the event, the sets and the chart
  offset `x₀`; the word of the conclusion is the law's word shifted by `−x₀`, in the chart of offset `0`).

R48: no source theorem is assumed in this file.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qr

open Exist Exist.StagedLaw Restart LocalSets

/-! ### Closed-disc events of a random hull complement -/

/-- **Closed-disc events of the complement of a random filled compact set are measurable**, for a set observed
through its dyadic hits: a closed disc inside `ℍ ∖ fill K` is already inside `ℍ ∖ fill` of a dyadic cover of `K`. -/
theorem measurableSet_closedBall_subset_H_diff_fillH {Ω : Type*} [MeasurableSpace Ω] {K : Ω → Set ℂ}
    (hK : IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω)) (z : ℂ) (ε : ℝ) :
    MeasurableSet {ω | closedBall z ε ⊆ H \ fillH (K ω)} := by
  have heq : {ω | closedBall z ε ⊆ H \ fillH (K ω)} =
      ⋃ n : ℕ, {ω | closedBall z ε ⊆ H \ fillH (coverOf n (dyadicIdx n (K ω)))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, ← dyadicCover_eq_coverOf]
    constructor
    · intro hsub
      have hopen : ∀ n : ℕ, IsOpen (H \ fillH (dyadicCover n (K ω))) := fun n =>
        isOpen_H_diff_fillH (isCompact_dyadicCover (hKc ω).isBounded n).isBounded
      have hcov : closedBall z ε ⊆ ⋃ n : ℕ, H \ fillH (dyadicCover n (K ω)) := by
        intro x hx
        obtain ⟨hxH, hxK⟩ := hsub hx
        rw [← iInter_fillH_dyadicCover (hKc ω)] at hxK
        obtain ⟨n, hn⟩ := not_forall.1 (mem_iInter.not.1 hxK)
        exact mem_iUnion.2 ⟨n, hxH, hn⟩
      have hdir : Directed (· ⊆ ·) fun n : ℕ => H \ fillH (dyadicCover n (K ω)) := by
        refine Monotone.directed_le fun m n hmn x hx => ⟨hx.1, fun hxn => hx.2 ?_⟩
        exact fillH_mono (dyadicCover_antitone hmn) hxn
      exact (isCompact_closedBall z ε).elim_directed_cover _ hopen hcov hdir
    · rintro ⟨n, hn⟩ x hx
      exact ⟨(hn hx).1, fun hxK => (hn hx).2 (fillH_subset_fillH_dyadicCover n hxK)⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    measurableSet_comp_dyadicIdx hK (fun ω => (hKc ω).isBounded) n
      fun S => closedBall z ε ⊆ H \ fillH (coverOf n S)

/-! ### The canonical hull chart family as retained chart data -/

/-- The lift of the canonical hull chart is harmonic on its domain. -/
theorem harmonicOnNhd_lift_hullChart {A : Set ℂ} (hA : IsHPHull A) (x₀ : ℝ) :
    InnerProductSpace.HarmonicOnNhd (Mo.hullChart A x₀).2.2 (Mo.hullChart A x₀).dom := by
  rw [Mo.coe_dom_hullChart hA x₀]
  obtain ⟨hL, -⟩ := Restart.isCanonicalDerivLog_canonDerivLog hA
  have hU : IsOpen (H \ A) := hA.2.2.1
  intro z hz
  exact (hL.1.analyticAt (hU.mem_nhds hz)).harmonicAt_im

/-- **The canonical hull chart family is retained chart data** for every σ-algebra for which the random compact set
is dyadic-hit measurable and the chart offset is measurable. -/
theorem retainedChartData_hullChart {Ω : Type u} {𝒢 : MeasurableSpace Ω} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hK : @IsDyadicHitMeasurable Ω 𝒢 K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[𝒢] x₀) :
    S3.RetainedChartData 𝒢 fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω) := by
  have hA : ∀ ω, IsHPHull (fillH (K ω)) := Mo.isHPHull_fillH hKc hKp
  refine ⟨fun ω => Mo.isConformal_hullChart (hA ω) (x₀ ω),
    fun z => @Mo.measurableSet_mem_dom_hullChart Ω 𝒢 K x₀ hK hKc hKp z,
    fun z => @Mo.measurable_indicator_fwd_hullChart Ω 𝒢 K x₀ hK hKc hKp hx₀ z,
    fun z ε => ?_,
    fun z => @Mo.measurable_indicator_lift_hullChart Ω 𝒢 K x₀ hK hKc hKp z,
    fun ω => harmonicOnNhd_lift_hullChart (hA ω) (x₀ ω)⟩
  have e : {ω | closedBall z ε ⊆ ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ)} =
      {ω | closedBall z ε ⊆ H \ fillH (K ω)} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [Mo.coe_dom_hullChart (hA ω) (x₀ ω)]
  rw [e]
  exact @measurableSet_closedBall_subset_H_diff_fillH Ω 𝒢 K hK hKc z ε

/-! ### The adapter -/

/-- **A retained kernel law in a canonical hull chart gives the retained mean** (the body of
`Ms.SB2LowerRetainedMeanStatement`). Let `K` be a random compact set connected to the real line, dyadic-hit
measurable for marks `𝒢 ≤ mΩ`, let `x₀` be a `𝒢`-measurable chart offset, and let `A` be a local set of the centred
field, history-avoidance local for `𝒢`, with `fill (K ω) = A ω` almost surely on a `𝒢`-event `G`. If almost surely on
`G` the field `Y` read in the canonical hull chart `Mo.hullChart (fillH (K ω)) (x₀ ω)` has, under the regular
conditional law given `𝒢`, the boundary data of a sorted word `β ω`, then almost surely on `G` every harmonic
representative `w₁` of every local-set mean of `A` satisfies
`w₁ + u₀ = (β ω shifted by −x₀ ω).mean ∘ g_A − χ(κ) · Im (canonDerivLog A)` on `ℍ ∖ A ω`, in the canonical hull chart
of offset `0`. -/
theorem ae_eqOn_hullMean_of_kernelWord {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {κ : ℝ} {K : Ω → Set ℂ}
    {x₀ : Ω → ℝ} (hK : @IsDyadicHitMeasurable Ω 𝒢 K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable[𝒢] x₀)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {h Y : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (hY : Measurable Y) {β : Ω → BoundaryWord} {G : Set Ω} (hG : MeasurableSet[𝒢] G)
    (hsort : ∀ᵐ ω ∂P, ω ∈ G → (β ω).IsSorted)
    (htr : ∀ᵐ ω ∂P, ω ∈ G →
      IsChartTransport (Mo.hullChart (fillH (K ω)) (x₀ ω)) 1 0 (chiC κ) (h ω) (Y ω))
    (hlaw : ∀ᵐ ω ∂P, ω ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω) Y (β ω).fn (β ω).jumps)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal 𝒢 A (WholeField.centredField h u₀) P)
    (hAK : ∀ᵐ ω ∂P, ω ∈ G → fillH (K ω) = A ω)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ G → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, w₁ z * φ z) →
      EqOn (fun z => w₁ z + u₀ z)
        (fun z => (BoundaryWord.shiftW (-(x₀ ω)) (β ω)).mean ((Mo.hullChart (A ω) 0).1 z) -
          chiC κ * (Mo.hullChart (A ω) 0).2.2 z)
        (H \ A ω) := by
  have hHP : ∀ ω, IsHPHull (fillH (K ω)) := Mo.isHPHull_fillH hKc hKp
  have hc := retainedChartData_hullChart hK hKc hKp hx₀
  have hAD : ∀ᵐ ω ∂P, ω ∈ G → ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) ⊆ H \ A ω ∧
      IsOpen ((H \ A ω) \ (Mo.hullChart (fillH (K ω)) (x₀ ω)).dom) := by
    filter_upwards [hAK] with ω hω hGω
    rw [Mo.coe_dom_hullChart (hHP ω) (x₀ ω), hω hGω]
    refine ⟨Subset.rfl, ?_⟩
    have e : (H \ A ω) \ (H \ A ω) = ∅ := by
      ext x
      simp only [Set.mem_sdiff, mem_empty_iff_false, iff_false]
      tauto
    rw [e]
    exact isOpen_empty
  have hm := S3.ae_eqOn_mean_of_kernelWord h𝒢 hc hh hu₀ hY hG hsort htr hlaw hA hloc hmark hAD hg
  filter_upwards [hm, hAK] with ω hmω hω hGω w₁ hw₁ hrep z hz
  have he := hmω hGω w₁ hw₁ hrep
  have hz' : z ∈ ((Mo.hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) := by
    rw [Mo.coe_dom_hullChart (hHP ω) (x₀ ω), hω hGω]
    exact hz
  have hval := he hz'
  rw [hω hGω] at hval
  simp only [Mo.hullChart_fwd, Mo.hullChart_lift] at hval ⊢
  rw [RLC.OrdDet.mean_shiftW]
  have harg : ConformalImage.mapOut (A ω) z - ((0 : ℝ) : ℂ) + ((-(x₀ ω) : ℝ) : ℂ) =
      ConformalImage.mapOut (A ω) z - ((x₀ ω : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  linarith

end InteractingSLE.Theorem14.SB.Qr
