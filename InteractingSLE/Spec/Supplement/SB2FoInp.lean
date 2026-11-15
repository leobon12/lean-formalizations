/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoAsm

/-!
# D34's left heights: the stage inputs of the step `ae_leftAdm_succ_succ`

Worker PROVE-SB2-F3LAW (round 3). From the consumer's objects at stage `ℓ`:

* **`ae_lawx_of_mvLaw`**: the kernel law of the relative chart field at the offset `x₀` (`hlawx`), from the retained
  law `Fl.MvLaw` (as in `Fl.mvLaw_succ_succ`'s proof);
* **`ae_read_of_meanIdentity`**: the original heights at the boundary values of untouched real points (`hread`),
  from F3's mean identity (Statement5's premise) and Lemma 7.8;
* **`ae_not_thr_of_cells`**: the seed of the relative piece is not at threshold (`hseedF`), from the seed cells.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Exist Exist.Staged Exist.StagedLaw Fm Qw

/-- **The kernel law of the relative chart field at the offset `x₀`** from the retained law at `ℓ` (as in
`Fl.mvLaw_succ_succ`'s proof): the input `hlawx` of `ae_leftAdm_succ_succ`. -/
theorem ae_lawx_of_mvLaw {κ : ℝ} {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) (h𝓜 : 𝓜 ≤ mΩ) {A : Ω → Set ℂ} {Kℓ : Ω → Set ℂ} {Gℓ : Set Ω}
    {Yℓ : Ω → DistOn upperHalfPlaneOpens} {β₁ : Ω → BoundaryWord} {Mℓ : ℝ}
    (hlaw : Fl.MvLaw κ 𝓜 P h A Kℓ Gℓ Yℓ β₁ Mℓ) {K : Ω → Set ℂ} (hKm : @Restart.IsDyadicHitMeasurable Ω 𝓜 K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {x₀ : Ω → ℝ}
    (hx₀ : Measurable[𝓜] x₀) {F : Set Ω} (hF : MeasurableSet[𝓜] F) (hFG : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ Gℓ)
    (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A ω) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) (Fl.canonField κ h x₀ hKc hKp)
      (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).jumps := by
  obtain ⟨-, -, -, -, hKℓA, -, hYℓt, -, -, -, -, hlawℓ⟩ := hlaw
  have hlawF : ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Yℓ (β₁ ω₀).fn (β₁ ω₀).jumps := by
    filter_upwards [hlawℓ, hFG] with ω₀ h1 h2 hω₀ using h1 (h2 hω₀)
  have hKΩ : @IsDyadicHitMeasurable Ω mΩ K := fun n j => h𝓜 _ (hKm n j)
  have hx₀m : Measurable x₀ := hx₀.mono h𝓜 le_rfl
  have heq0 : ∀ᵐ ω ∂P, ω ∈ F → Yℓ ω = Fl.canonField κ h (fun _ => (0 : ℝ)) hKc hKp ω := by
    filter_upwards [hFG, hKℓA, hKF, hYℓt] with ω h1 h2 h3 h4 hωF
    have e : fillH (Kℓ ω) = fillH (K ω) := (h2 (h1 hωF)).trans (h3 hωF).symm
    have h5 := h4 (h1 hωF)
    rw [e] at h5
    exact Fl.canonField_eq_of_transport (x₀ := fun _ => (0 : ℝ)) hKc hKp h5
  have hlaw0 := Fl.ae_isGFF_congr_on h𝓜 hF (Fl.measurable_canonField κ hhm hKc hKp hKΩ measurable_const) hlawF heq0
  exact Mu.ae_isGFF_hullChart_shift h𝓜 hKc hKp hx₀ (Fl.measurable_canonField κ hhm hKc hKp hKΩ hx₀m) hlaw0

/-- **The original heights at the boundary values of untouched real points**, almost surely, for a word with F3's mean
identity (the input `hread` of `ae_leftAdm_succ_succ`; Lemma 7.8's vanishing harmonic part). -/
theorem ae_read_of_meanIdentity {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A₁ : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A₁)
    (hloc : IsLocalSet A₁ (WholeField.centredField h u₀) P) {β₁ : Ω → BoundaryWord} (hβs : ∀ ω, (β₁ ω).IsSorted)
    {S : Set Ω}
    (hmean : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens,
      LocalSets.IsLocalSetMean A₁ (WholeField.centredField h u₀) P g₁ →
        ∀ᵐ ω ∂P, ω ∈ S →
          ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
            EqOn (fun z => w₁ z + u₀ z)
              (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ ω) 0).1 z) -
                chiC κ * (Mo.hullChart (A₁ ω) 0).2.2 z) (H \ A₁ ω)) :
    ∀ᵐ ω ∂P, ω ∈ S → IsHPHull (A₁ ω) → ∀ x r : ℝ, 0 < r → Disjoint (ball (x : ℂ) r) (A₁ ω) → x ∉ jumps →
      bdryVal (A₁ ω) x ∉ (β₁ ω).jumps → (β₁ ω).fn (bdryVal (A₁ ω) x) = b x := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨g₁, hg₁⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hh0 hAm hloc
  filter_upwards [Sec7.IsLocalSetMean.ae_tendsto_zero_of_real hh0 hAm hloc hg₁, hmean g₁ hg₁, hg₁.2.1]
    with ω hw hid hharm hωS hHP x r hr hd hxJ hyJ
  obtain ⟨v, hv, hrep⟩ := hharm
  exact fn_bdryVal_eq hHP (hβs ω) hu₀ (hid hωS v hv hrep) hr hd (hw v hv hrep x ⟨r, hr, hd⟩) hxJ hyJ

/-- **The seed of the relative piece is not at threshold** on the live event (the seed cells of the covering types;
the input `hseedF` of `ae_leftAdm_succ_succ`). -/
theorem ae_not_thr_of_cells {κ θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {cw : Ω → BoundaryWord}
    {F : Set Ω} {types : Set Supp8.Q3Stop.WordType} (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → Lv.angleWordType κ θ (cw ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ Lv.wordTypeCell κ θ cw F w → ω ∈ Lv.seedCell κ θ cw F w) :
    ∀ᵐ ω ∂P, ω ∈ F → ¬ ForceWord.ThresholdCondition (flowLineRhoL κ (cw ω).fn (cw ω).jumps 0 θ)
      (flowLineRhoR κ (cw ω).fn (cw ω).jumps 0 θ) 0 (flowLineXL (cw ω).fn (cw ω).jumps 0)
      (flowLineXR (cw ω).fn (cw ω).jumps 0) := by
  filter_upwards [hcover, (ae_ball_iff htypes).2 hseed] with ω hc hs hωF
  exact not_thr_of_mem_seedCell (hs _ (hc hωF) ⟨hωF, rfl⟩)

end InteractingSLE.Theorem14.SB.Fo
