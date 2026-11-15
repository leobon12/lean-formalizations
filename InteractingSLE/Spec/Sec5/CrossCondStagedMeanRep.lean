/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedMeanFlow
import InteractingSLE.Spec.Sec7.SideHeightHull

/-!
# The staged prefix's own mean, IV: a harmonic representative for every test function at once

Packet PROVE-CROSSCOND-STAGED2. `Sec5.CrossCond.Staged.ae_condExp_union_cfGlueT_add_eq` (the staged mean identification
on the θ-glued space) takes the flow side's own mean as a harmonic representative `wA` valid **almost surely for every
test function** (`hwA`). This file puts the staged prefix's own mean (`ae_apply_eq_stageChartMean`, one test function
at a time) in that form:

* `stageMean`: the candidate `𝔤 ∘ F − χ ℓ` (the bounded harmonic mean of the stop word read in the chart after the
  pieces), harmonic on the domain (`harmonicOnNhd_stageMean`, from `harmonicOnNhd_couplingMean`);
* **`ae_forall_apply_eq_stageMean`**: almost surely on the success event, for every `φ` supported in the domain `D`
  after the pieces, `g(φ) = ∫ (stageMean − 𝔥₀) φ` (the quantifier exchange of `WangWu.ae_forall_apply_eq_of_forall_ae`
  on the domain);
* **`exists_rep_stageMean`**: when the explored set's complement is `D` on the success event, a representative `wA`
  in exactly the form of `hwA`, equal to `stageMean − 𝔥₀` on the success event.

Conditional helpers with distinct names; R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Staged

universe u

open Exist Exist.Staged Exist.StagedLaw Restart Theorem14.GW2Schedule Sec7.StripSideHeightProb LocalSets

/-! ### Harmonicity of the chart mean -/

section Harm

variable {w : ℕ → ℝ≥0 → ℝ} {T : ℕ → ℝ≥0}

/-- **The chart mean of a bounded harmonic function is harmonic on the domain** of the chart of the concatenation. -/
theorem harmonicOnNhd_catChartN_mean (κ x₀ : ℝ) (hc : ∀ j, Continuous (w j)) (h0 : ∀ j, w j 0 = 0) (k : ℕ)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) :
    InnerProductSpace.HarmonicOnNhd
      (fun z => u ((catChartN x₀ w T k).1 z) - chiC κ * (catChartN x₀ w T k).2.2 z) (catChartN x₀ w T k).dom := by
  have hW := continuous_rpath_of (continuous_catN (T := T) hc h0 k)
  have hW0 := rpath_zero_of_zero (catN_zero (T := T) h0 k)
  have ht := (cumT T k).coe_nonneg
  intro z hz
  have hz' : z + ((-x₀ : ℝ) : ℂ) ∈ H \ fwdHull (Ito.rpath (catN w T k)) (cumT T k) := by
    rw [show z + ((-x₀ : ℝ) : ℂ) = z - x₀ by push_cast; ring]
    exact (mem_dom_loewner_iff_mem_diff_hull hW hW0 ht).1 ((mem_dom_recenter_loewner_iff x₀ hW hW0 ht).1 hz)
  have h1 := Exist.harmonicAt_comp_add_const (a := ((-x₀ : ℝ) : ℂ))
    (f := couplingMean κ (Ito.rpath (catN w T k)) (cumT T k) u) (z := z)
    (Sec7.SideHeight.harmonicOnNhd_couplingMean hW ht hu _ hz')
  have e : (fun z' => couplingMean κ (Ito.rpath (catN w T k)) (cumT T k) u (z' + ((-x₀ : ℝ) : ℂ))) =
      fun z => u ((catChartN x₀ w T k).1 z) - chiC κ * (catChartN x₀ w T k).2.2 z := by
    funext z'
    rw [show z' + ((-x₀ : ℝ) : ℂ) = z' - x₀ by push_cast; ring]
    change _ = u (QuantumZipper.fwdMap _ _ (z' - x₀)) -
      chiC κ * ((QuantumZipper.logDerivFwd _ _ (z' - x₀)).im + 0)
    rw [add_zero]
    rfl
  rwa [e] at h1

end Harm

/-! ### The staged mean, for every test function at once -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}

/-- **The candidate own mean after the stopped pieces `0, …, ℓ`**: the bounded harmonic mean of the stop word read in
the chart after the pieces, `𝔤 ∘ F − χ ℓ`. -/
def stageMean (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (Δ : ℕ → ℝ≥0∞)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℕ → ℝ) (ℓ : ℕ) (β : Ω → BoundaryWord) (ω : Ω) (z : ℂ) : ℝ :=
  (stopWord κ (β ω, θ ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))).mean
      ((stageChart κ b jumps spec Δ E ℓ ω).1 z) - chiC κ * (stageChart κ b jumps spec Δ E ℓ ω).2.2 z

omit mΩ [StandardBorelSpace Ω] in
theorem harmonicOnNhd_stageMean (ℓ : ℕ) (β : Ω → BoundaryWord) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (stageMean κ b jumps spec Δ E θ ℓ β ω)
      (stageChart κ b jumps spec Δ E ℓ ω).dom :=
  harmonicOnNhd_catChartN_mean κ spec.1 (continuous_stageDrv ℓ ω) (stageDrv_zero ℓ ω) ℓ
    ((stopWord κ _).isBoundedHarmonicExtension_mean (isSorted_stopWord κ _)).1

/-- **The staged prefix's own mean, for every test function at once**: in the setting of
`ae_apply_eq_stageChartMean`, almost surely on the success event, for every `φ` supported in the domain `D` after the
pieces, `g(φ) = ∫ (stageMean − 𝔥₀) φ`. -/
theorem ae_forall_apply_eq_stageMean (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps spec E (ℓ + 1)) A
      (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
      ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (stageChart κ b jumps spec Δ E ℓ ω).dom))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∃ β : Ω → BoundaryWord, Measurable[pastSigma κ b jumps spec E ℓ] β ∧
      ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ → ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ (stageChart κ b jumps spec Δ E ℓ ω).dom →
        g ω φ = ∫ z, (stageMean κ b jumps spec Δ E θ ℓ β ω z - u₀ z) * φ z := by
  classical
  obtain ⟨β, hβ, hmean⟩ := ae_apply_eq_stageChartMean hκ hb hh hS hreg hgw hprog hΔ hℓ hu₀ hA hloc hmark hAD hg
  refine ⟨β, hβ, ?_⟩
  set G := stageGood κ b jumps spec Δ E ℓ with hG
  set D : Ω → Set ℂ := fun ω => ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) with hD
  -- the open set on which the representation is exchanged: `D` on the success event, `∅` off it
  set A' : Ω → Set ℂ := fun ω => if ω ∈ G then H \ D ω else H with hA'
  have hDH : ∀ ω, D ω ⊆ H := fun ω => (isConformal_stageChart Δ ℓ ω).dom_subset
  have hA'G : ∀ ω, ω ∈ G → H \ A' ω = D ω := fun ω hω => by
    simp only [hA', hω, ↓reduceIte, sdiff_sdiff_right_self]
    exact inter_eq_right.2 (hDH ω)
  have hA'n : ∀ ω, ω ∉ G → H \ A' ω = ∅ := fun ω hω => by simp only [hA', hω, ↓reduceIte, sdiff_self]
  set m : Ω → ℂ → ℝ := fun ω z => stageMean κ b jumps spec Δ E θ ℓ β ω z - u₀ z with hm
  have hzero : ∀ ω, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A' ω → ω ∉ G → φ = 0 := by
    intro ω φ hφ hω
    rw [hA'n ω hω] at hφ
    exact Restart.eq_zero_of_tsupport_subset_empty hφ
  have hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A' ω) := by
    filter_upwards [hg.2.1, hAD] with ω hgω hADω
    by_cases hω : ω ∈ G
    · obtain ⟨v, hv, hvg⟩ := hgω
      rw [hA'G ω hω]
      exact ⟨v, fun z hz => hv z ((hADω hω).1 hz), fun φ hφ => hvg φ (hφ.trans (hADω hω).1)⟩
    · refine ⟨fun _ => 0, fun z hz => ?_, fun φ hφ => ?_⟩
      · rw [hA'n ω hω] at hz
        exact absurd hz (notMem_empty z)
      · rw [hzero ω φ hφ hω, map_zero]
        simp
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · rw [hA'G ω hω]; exact (stageChart κ b jumps spec Δ E ℓ ω).dom.isOpen
    · rw [hA'n ω hω]; exact isOpen_empty
  have hmh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · rw [hA'G ω hω]
      intro z hz
      exact (harmonicOnNhd_stageMean ℓ β ω z hz).sub (hu₀.1 z (hDH ω hz))
    · rw [hA'n ω hω]
      intro z hz
      exact absurd hz (notMem_empty z)
  have hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ H \ A' ω → g ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [hmean φ] with ω hω hsupp
    by_cases hωG : ω ∈ G
    · rw [hA'G ω hωG] at hsupp
      rw [hω hωG hsupp]
      have hc1 : ContinuousOn (stageMean κ b jumps spec Δ E θ ℓ β ω) (D ω) := fun z hz =>
        (harmonicOnNhd_stageMean ℓ β ω z hz).1.continuousAt.continuousWithinAt
      have hc2 : ContinuousOn u₀ (D ω) := fun z hz => (hu₀.1 z (hDH ω hz)).1.continuousAt.continuousWithinAt
      have hi1 := WholeField.integrable_mul_testOn hc1 φ hsupp
      have hi2 := WholeField.integrable_mul_testOn hc2 φ hsupp
      change (∫ z, stageMean κ b jumps spec Δ E θ ℓ β ω z * φ z) - ∫ z, u₀ z * φ z = _
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hm, stageMean]
      ring
    · rw [hzero ω φ hsupp hωG, map_zero]
      simp
  filter_upwards [WangWu.ae_forall_apply_eq_of_forall_ae hharm hopen hmh hφ] with ω hω hωG φ hsupp
  exact hω φ (by rw [hA'G ω hωG]; exact hsupp)

/-- **A representative of the staged prefix's own mean in the form of `hwA`**: if the explored set's complement is the
domain after the pieces on the success event, there is `wA` harmonic on `ℍ ∖ A` representing `g` there almost
surely for every test function, equal to `stageMean − 𝔥₀` on the success event. -/
theorem exists_rep_stageMean (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps spec E (ℓ + 1)) A
      (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ → H \ A ω = (stageChart κ b jumps spec Δ E ℓ ω).dom)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∃ (β : Ω → BoundaryWord) (wA : Ω → ℂ → ℝ), Measurable[pastSigma κ b jumps spec E ℓ] β ∧
      (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (wA ω) (H \ A ω) ∧
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, wA ω z * φ z) ∧
      ∀ ω, ω ∈ stageGood κ b jumps spec Δ E ℓ → H \ A ω = (stageChart κ b jumps spec Δ E ℓ ω).dom →
        wA ω = fun z => stageMean κ b jumps spec Δ E θ ℓ β ω z - u₀ z := by
  classical
  have hAD' : ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
      ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (stageChart κ b jumps spec Δ E ℓ ω).dom) := by
    filter_upwards [hAD] with ω hω hωG
    rw [hω hωG, sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩
  obtain ⟨β, hβ, hall⟩ := ae_forall_apply_eq_stageMean hκ hb hh hS hreg hgw hprog hΔ hℓ hu₀ hA hloc hmark hAD' hg
  set good : Ω → Prop := fun ω => ω ∈ stageGood κ b jumps spec Δ E ℓ ∧
    H \ A ω = (stageChart κ b jumps spec Δ E ℓ ω).dom with hgood
  refine ⟨β, fun ω => if hω : good ω then fun z => stageMean κ b jumps spec Δ E θ ℓ β ω z - u₀ z else
    if hr : IsHarmonicDistOn (g ω) (H \ A ω) then Classical.choose hr else fun _ => 0, hβ, ?_, fun ω hω hωD => ?_⟩
  · filter_upwards [hall, hg.2.1] with ω hω hgω
    by_cases hgd : good ω
    · simp only [hgd, ↓reduceDIte]
      refine ⟨?_, fun φ hφ => ?_⟩
      · rw [hgd.2]
        intro z hz
        exact (harmonicOnNhd_stageMean ℓ β ω z hz).sub
          (hu₀.1 z ((isConformal_stageChart Δ ℓ ω).dom_subset hz))
      · rw [hgd.2] at hφ
        exact hω hgd.1 φ hφ
    · simp only [hgd, hgω, ↓reduceDIte]
      exact Classical.choose_spec hgω
  · have hgd : good ω := ⟨hω, hωD⟩
    simp only [hgd, ↓reduceDIte]

end Main

end InteractingSLE.Sec5.CrossCond.Staged
