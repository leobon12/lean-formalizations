/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutIncident
import InteractingSLE.Spec.Sec7.R5WallCover

/-!
# R.5 assembled from relative reference collars

PROVE-R5-OUTER, R88. The reference set is the complement of the earlier
incident component. Its raw law, domain clause and conditioned increment
law are proved here. The remaining input `R5Cover` is explicitly the
reference-height and collar clause, rather than an R.5 law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H Hbar)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets WholeField PocketTraversal PocketAdapt PocketCoupling PocketUnionPt
  PocketStopSide PocketStop R5Enl PocketStopField R5Phase Lemma71C PhaseSel Aux29Cor

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit mΩ in
/-- A relative incident component has an open complement and is unchanged by reference regularization. -/
theorem relativeReference_facts
    {A : Set Ω} {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω))
    (p : ℝ≥0) :
    (∀ ω, activeCompl A γ c p ω ⊆ H ∧ IsOpen (H \ activeCompl A γ c p ω)) ∧
      liveExt A γ C (activeCompl A γ c p) 0 = activeCompl A γ c p ∧
      activeCompl A γ c p = liveExt A γ C
        (fun ω => HOuter.relHull (C ω) (ψ ω) (γ ω) p) p := by
  have hact : ∀ ω ∈ A, (p : ℝ≥0∞) < capLife (γ ω) →
      activeDom A γ c p ω = C ω ∩ (H \ HOuter.relHull (C ω) (ψ ω) (γ ω) p) := by
    intro ω hω hp
    rw [activeDom_eq_relChart_dom hω hp (hγ ω hω) (hc ω hω).1,
      current_dom_eq_relHull hω hp (hγ ω hω) (hc ω hω).1 (hc ω hω).2.1
        (hc ω hω).2.2 (hCH ω hω) (hψ ω hω),
      HOuter.H_diff_relHull (hCH ω hω), ← inter_assoc, inter_self]
  have heq := activeCompl_eq_liveExt hact
  refine ⟨activeCompl_regular hact hCo (fun ω hω hp => HOuter.isOpen_H_diff_relHull
    (hCo ω hω) (hCH ω hω) (hψ ω hω).1.continuousOn (hγ ω hω) hp), ?_, heq⟩
  rw [heq]
  exact liveExt_liveExt_zero hγ p

/-- R.5's probabilistic clauses for relative references, with only the collar and height clause left as input. -/
theorem r5ClausesCompOn_of_relativeCover
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω))
    (hU : ∀ s, PocketStopUnionLaw 𝓦 P A γ C
      (fun ω => HOuter.relHull (C ω) (ψ ω) (γ ω) s) h₀ s)
    {p : ℕ → ℝ≥0} {q : ℝ≥0} (hpq : ∀ i, p i ≤ q)
    (hfwd : ∀ i z, Measurable[germSigma (activeCompl A γ c (p i)) h₀ ⊔ locPrefixSigma 𝓦 A γ (p i)]
      (({ω | ω ∈ A ∧ (p i : ℝ≥0∞) < capLife (γ ω)} ∩
        {ω | z ∈ (relChart c γ (p i) ω).dom}).indicator fun ω => (relChart c γ (p i) ω).1 z))
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ}
    {u : ℂ → ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ}
    (hX : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hCover : R5Wall.R5Cover κ ρL ρR P A γ xL xR c a h₀ u C
      (fun i => activeCompl A γ c (p i)) δ X (fun i ω => (relChart c γ (p i) ω).2.2)
      (fun _ => {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)})
      (fun i => relChart c γ (p i)) q (fun _ _ => True)) :
    R5ClausesCompOn κ ρL ρR P A γ xL xR c a h₀ u C (fun i => activeCompl A γ c (p i)) δ X
      (fun i ω => (relChart c γ (p i) ω).2.2)
      (fun _ => {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)}) (fun i => relChart c γ (p i)) q := by
  have hB := fun i => relativeReference_facts hγ hCo hCH hψ hc (p i)
  refine ⟨hX, hLattice, ?_, ?_, (R5Wall.r5Cover_true_iff).1 hCover⟩
  · intro i ω hω
    have hp : (p i : ℝ≥0∞) < capLife (γ ω) := lt_of_le_of_lt (by exact_mod_cast hpq i) hω.2
    refine ⟨hω.1, hω.2, isConformal_relChart_of_driven (hγ ω hω.1) hp (hc ω hω.1).1,
      relChart_dom_antitone (hc ω hω.1).1 (hγ ω hω.1) hω.2 (hpq i), ?_⟩
    rw [(hB i).2.1, H_diff_activeCompl_eq_relChart_dom hω.1 hp (hγ ω hω.1) (hc ω hω.1).1]
  · intro gB hgB g hg i
    have hgi : IsLocalSetMean (activeCompl A γ c (p i)) h₀ P (gB i) := by
      rw [← (hB i).2.1]
      exact hgB i
    exact hasOldChartIncrementLawOn_relHull hh₀ h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc hU
      (hpq i) (hfwd i) (gB i) hgi g hg

/-- R.5 from relative reference collars, with their raw laws and increment laws discharged. -/
theorem pocketStopPhaseSideLimit_of_relativeCover
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    {ψ : Ω → ℂ → ℂ} (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z))
    (hCin : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝓦] {ω | ω ∈ A ∧ U ⊆ C ω})
    {c : Ω → Chart}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ ((c ω).dom : Set ℂ) = C ω ∧ EqOn (c ω).1 (ψ ω) (C ω))
    (hU : ∀ s, PocketStopUnionLaw 𝓦 P A γ C
      (fun ω => HOuter.relHull (C ω) (ψ ω) (γ ω) s) h₀ s)
    {p : ℕ → ℝ≥0} {q : ℝ≥0} (hpq : ∀ i, p i ≤ q)
    (hfwd : ∀ i z, Measurable[germSigma (activeCompl A γ c (p i)) h₀ ⊔ locPrefixSigma 𝓦 A γ (p i)]
      (({ω | ω ∈ A ∧ (p i : ℝ≥0∞) < capLife (γ ω)} ∩
        {ω | z ∈ (relChart c γ (p i) ω).dom}).indicator fun ω => (relChart c γ (p i) ω).1 z))
    {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ}
    {u : ℂ → ℝ} {δ : Ω → ℝ} {X : Ω → Set ℂ}
    (hX : ∀ ω, (X ω).Finite)
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hCover : R5Wall.R5Cover κ ρL ρR P A γ xL xR c a h₀ u C
      (fun i => activeCompl A γ c (p i)) δ X (fun i ω => (relChart c γ (p i) ω).2.2)
      (fun _ => {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)})
      (fun i => relChart c γ (p i)) q (fun _ _ => True))
    (hκ : 0 < κ) {ℓ : Ω → ℂ → ℂ}
    (hLog : ∀ ω ∈ A, IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hcInf : ∀ ω ∈ A, ∃ z : ℂ,
      Tendsto (fun w => mob ((c ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 z))
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ B : ℝ, ∀ z ∈ H, |u z| ≤ B) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) δ q := by
  have hB := fun i => relativeReference_facts hγ hCo hCH hψ hc (p i)
  have hpre := locPrefixSigma_le h𝓦 hA hγ hγm
  have hRaw : ∀ i, PocketStopUnionLaw (locPrefixSigma 𝓦 A γ (p i)) P A γ C
      (activeCompl A γ c (p i)) h₀ 0 := by
    intro i
    rw [(hB i).2.2]
    exact pocketStopUnionLaw_reference (p i) (hpre (p i)) (hU (p i))
  have hcl := r5ClausesCompOn_of_relativeCover hh₀ h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc hU
    hpq hfwd hX hLattice hCover
  exact pocketStopPhaseSideLimit_of_r5ClausesCompOn
    (ℳ := fun i => locPrefixSigma 𝓦 A γ (p i)) hκ hh₀
    (fun i => by rw [locPrefixSigma_prefix_zero]; exact hpre (p i)) hCo
    (fun i ω _ => (hB i).1 ω |>.2) hRaw hγ
    (fun ω hω => ⟨(hc ω hω).1, hLog ω hω⟩) hcExt hcInf
    ((PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH hψ hCm hψm hCin hc q).mono
      (hpre q) le_rfl) hu hub hcl

end InteractingSLE.Sec7.R5Out
