/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlCollar
import InteractingSLE.Spec.Sec7.R5OutDomain

/-!
# R.5's conditioned collar engine in a reference component

Ruling R88, PROVE-R5-OUTER. A reference chart may uniformize only the
incident component of the reference complement. The engine needs its domain
contained in that complement: harmonic representatives restrict to this domain.
The conditioned increment law is already a statement in the selected chart.
This removes the full-complement equality in clause 3 without changing the
phase-side-limit conclusion. References keep their full local-set means.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling
  Aux119Heights PocketStopSide PhaseSel Aux29Cor R5Phase R5Enl

/-- **R.5's collar germ (C1) at a fixed relative capacity, from the conditioned increment laws**
(`PocketStopSide.collar_of_oldChartIncrementLaws` with `HasOldChartIncrementLawOn`). -/
theorem collar_of_oldChartIncrementLawsCompOn {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    {q : ℝ≥0} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {k : ℝ}
    {B : ι → Ω → Set ℂ} {liftB : ι → Ω → ℂ → ℝ} {J : Ω → Set ℝ} {Wd : Ω → ℝ → ℝ}
    {M : ι → Set Ω} {old : ι → Ω → Chart}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hOld : ∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
      ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧ ((old i ω).dom : Set ℂ) ⊆ H \ B i ω)
    (hLaw : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (B i) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ i, HasOldChartIncrementLawOn P (M i) (old i) (relChart c γ q) (gB i) g)
    (hCover : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (B i) h₀ P (gB i)) →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ J ω →
        ∃ (i : ι) (x r b d : ℝ), ω ∈ M i ∧ 0 < r ∧
          (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
          Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun y => harmRep (gB i ω) (H \ B i ω) ((relChart c γ q ω).2.1 y) +
              u ((relChart c γ q ω).2.1 y) + k * liftB i ω ((relChart c γ q ω).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
          Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
              liftB i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
          b + k * d = Wd ω ξ) :
    ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (B i) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ activeCompl A γ c q ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ activeCompl A γ c q ω →
            g ω φ = ∫ z, v z * φ z) →
          ∀ ξ : ℝ, ξ ∉ J ω →
            ∃ (i : ι) (b d : ℝ),
              let inv := (relChart c γ q ω).2.1;
              let vB := harmRep (gB i ω) (H \ B i ω);
              Tendsto (fun y => v (inv y) - vB (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun y => vB (inv y) + u (inv y) + k * liftB i ω (inv y)) (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
              Tendsto (fun y => (relChart c γ q ω).2.2 (inv y) - liftB i ω (inv y))
                (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
              b + k * d = Wd ω ξ := by
  intro gB hgB g hg
  have hGerm := fun i => ae_physical_germ_of_old_chart_increment_law_on (P := P) (M := M i)
    (old := old i) (current := relChart c γ q) (gOld := gB i) (gNow := g)
    (fun ω hω => (hOld i ω hω).2.2.1)
    (fun ω hω => isConformal_relChart_of_driven (hγ ω (hOld i ω hω).1) (hOld i ω hω).2.1
      (hc ω (hOld i ω hω).1))
    (fun ω hω => (hOld i ω hω).2.2.2.1) (hLaw gB hgB g hg i)
  have hAll := ae_all_iff.2 hGerm
  have hRep : ∀ᵐ ω ∂P, ∀ i, IsHarmonicDistOn (gB i ω) (H \ B i ω) :=
    ae_all_iff.2 fun i => (hgB i).2.1
  filter_upwards [hAll, hRep, hCover gB hgB] with ω hωG hωR hωC hωA hq v hv hvr ξ hξ
  obtain ⟨i, x, r, b, d, hMi, hr, hcol, htr, hb, hd, hid⟩ := hωC hωA hq ξ hξ
  obtain ⟨hvB, hvBr⟩ := harmRep_spec (hωR i)
  have hdomOld := (hOld i ω hMi).2.2.2.2
  have hdomCur := H_diff_activeCompl_eq_relChart_dom hωA hq (hγ ω hωA) (hc ω hωA)
  refine ⟨i, b, d, ?_, hb, hd, hid⟩
  have hvB' : InnerProductSpace.HarmonicOnNhd (harmRep (gB i ω) (H \ B i ω)) (old i ω).dom := by
    exact hvB.mono hdomOld
  have hvBr' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (old i ω).dom →
      gB i ω φ = ∫ z, harmRep (gB i ω) (H \ B i ω) z * φ z := by
    exact fun φ hφ => hvBr φ (hφ.trans hdomOld)
  have hv' : InnerProductSpace.HarmonicOnNhd v (relChart c γ q ω).dom := by
    rw [← hdomCur]
    exact hv
  have hvr' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (relChart c γ q ω).dom →
      g ω φ = ∫ z, v z * φ z := by
    rw [← hdomCur]
    exact hvr
  exact hωG i hMi _ v hvB' hvBr' hv' hvr' ξ x r hr hcol htr

/-- **Lemma R.5 on one pocket test at one relative capacity, from the conditioned increment laws**
(`R5Phase.pocketStopPhaseSideLimit_of_incrementLaws_offExc` with `HasOldChartIncrementLawOn`). -/
theorem pocketStopPhaseSideLimit_of_incrementLawsCompOn_offExc {Ω ι : Type*} [Countable ι]
    {ℳ : ι → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {C : Ω → Set ℂ} {F : ι → Ω → Set ℂ} {q q₀ : ℝ≥0} {δ : Ω → ℝ}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hpre : ∀ i, locPrefixSigma (ℳ i) A γ q₀ ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ i ω, ω ∈ A → IsOpen (H \ F i ω))
    (hRawReference : ∀ i, PocketStopUnionLaw (ℳ i) P A γ C (F i) h₀ q₀)
    {liftB : ι → Ω → ℂ → ℝ}
    (hLattice : ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, δ ω = m * phaseStep κ)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ℓ : Ω → ℂ → ℂ}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hcInf : ∀ ω ∈ A, ∃ p : ℂ,
      Tendsto (fun w => mob ((c ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p))
    (hKm : Measurable[mΩ, hittingSigma] (activeCompl A γ c q))
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {X : Ω → Set ℂ} (hX : ∀ ω, (X ω).Finite)
    {M : ι → Set Ω} {old : ι → Ω → Chart}
    (hOld : ∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
      ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧
      ((old i ω).dom : Set ℂ) ⊆ H \ liveExt A γ C (F i) q₀ ω)
    (hLaw : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ i, HasOldChartIncrementLawOn P (M i) (old i) (relChart c γ q) (gB i) g)
    (hCover : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A γ C (F i) q₀) h₀ P (gB i)) →
      ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
        extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
        ∃ (i : ι) (x r b d : ℝ), ω ∈ M i ∧ 0 < r ∧
          (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
          Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ C (F i) q₀ ω) ((relChart c γ q ω).2.1 y) +
              u ((relChart c γ q ω).2.1 y) + chiC κ * liftB i ω ((relChart c γ q ω).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
          Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
              liftB i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
          b + chiC κ * d = phaseData κ ρL ρR
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
            (δ ω) ξ - a) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) δ q := by
  classical
  refine pocketStopPhaseSideLimit_of_collar_offExc (liftB := liftB) hκ hh₀ hpre hCo hFo hRawReference hLattice hγ
    hc hcExt hcInf hKm hu hub hX ?_
  intro gB hgB g hg
  have hcol := collar_of_oldChartIncrementLawsCompOn (P := P) (A := A) (γ := γ) (c := c) (q := q) (h₀ := h₀) (u := u)
    (k := chiC κ) (B := fun i => liveExt A γ C (F i) q₀) (liftB := liftB)
    (J := fun ω => {ξ : ℝ | ξ ∈ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) ∨
      extendFrom H (relChart c γ q ω).2.1 ξ ∈ X ω})
    (Wd := fun ω ξ => phaseData κ ρL ρR
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) (δ ω) ξ - a)
    (M := M) (old := old) hγ (fun ω hω => (hc ω hω).1) hOld hLaw ?_ gB hgB g hg
  · filter_upwards [hcol] with ω hω hωA hq v hv hvr ξ hξ hξX
    exact hω hωA hq v hv hvr ξ (fun h => h.elim hξ hξX)
  · intro gB' hgB'
    filter_upwards [hCover gB' hgB'] with ω hω hωA hq ξ hξ
    exact hω hωA hq ξ (fun h => hξ (Or.inl h)) (fun h => hξ (Or.inr h))

/-- **Lemma R.5's remaining clauses at the relative capacity `q` with the conditioned increment laws**
(`R5Phase.R5Clauses` with `HasOldChartIncrementLawOn` in its fourth clause). -/
def R5ClausesCompOn {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (A : Set Ω) (γ : Ω → ℝ → ℂ)
    (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (a : ℝ)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (C : Ω → Set ℂ) (F : ℕ → Ω → Set ℂ) (δ : Ω → ℝ)
    (X : Ω → Set ℂ) (liftB : ℕ → Ω → ℂ → ℝ) (M : ℕ → Set Ω) (old : ℕ → Ω → Chart) (q : ℝ≥0) : Prop :=
  (∀ ω, (X ω).Finite) ∧
  (∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∃ m : ℤ, δ ω = m * phaseStep κ) ∧
  (∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
    ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧
    ((old i ω).dom : Set ℂ) ⊆ H \ liveExt A γ C (F i) 0 ω) ∧
  (∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt A γ C (F i) 0) h₀ P (gB i)) →
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
    ∀ i, HasOldChartIncrementLawOn P (M i) (old i) (relChart c γ q) (gB i) g) ∧
  ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt A γ C (F i) 0) h₀ P (gB i)) →
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
      extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
      ∃ (i : ℕ) (x r b d : ℝ), ω ∈ M i ∧ 0 < r ∧
        (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
        Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ C (F i) 0 ω) ((relChart c γ q ω).2.1 y) +
            u ((relChart c γ q ω).2.1 y) + chiC κ * liftB i ω ((relChart c γ q ω).2.1 y))
          (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
        Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
            liftB i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
        b + chiC κ * d = phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
          (δ ω) ξ - a

/-- **Lemma R.5 on one pocket test from its conditioned clauses**: raw reference laws at level `0`, the base chart's
analytic data and `R5ClausesCompOn` give the phase side limit at `q`. -/
theorem pocketStopPhaseSideLimit_of_r5ClausesCompOn {Ω : Type*} {ℳ : ℕ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {C : Ω → Set ℂ} {F : ℕ → Ω → Set ℂ} {q : ℝ≥0} {δ : Ω → ℝ}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hpre : ∀ i, locPrefixSigma (ℳ i) A γ 0 ≤ mΩ)
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hFo : ∀ i ω, ω ∈ A → IsOpen (H \ F i ω))
    (hRawReference : ∀ i, PocketStopUnionLaw (ℳ i) P A γ C (F i) h₀ 0)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) {ℓ : Ω → ℂ → ℂ}
    (hc : ∀ ω ∈ A, (c ω).IsConformal ∧ IsDerivLog (c ω).1 (ℓ ω) (c ω).dom ∧
      ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ ω z).im)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hcInf : ∀ ω ∈ A, ∃ p : ℂ,
      Tendsto (fun w => mob ((c ω).2.1 w)) (Bornology.cobounded ℂ ⊓ 𝓟 H) (𝓝 p))
    (hKm : Measurable[mΩ, hittingSigma] (activeCompl A γ c q))
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    {X : Ω → Set ℂ} {liftB : ℕ → Ω → ℂ → ℝ} {M : ℕ → Set Ω} {old : ℕ → Ω → Chart}
    (hcl : R5ClausesCompOn κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q) :
    PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (activeCompl A γ c q) δ q := by
  obtain ⟨hX, hLattice, hOld, hLaw, hCover⟩ := hcl
  exact pocketStopPhaseSideLimit_of_incrementLawsCompOn_offExc hκ hh₀ hpre hCo hFo hRawReference hLattice hγ hc hcExt
    hcInf hKm hu hub hX hOld hLaw hCover

/-- The unconditioned clauses imply the conditioned ones. -/
theorem r5ClausesCompOn_of_r5Clauses {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ}
    {ρR : Fin (nR + 1) → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {C : Ω → Set ℂ} {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ}
    {X : Ω → Set ℂ} {liftB : ℕ → Ω → ℂ → ℝ} {M : ℕ → Set Ω} {old : ℕ → Ω → Chart} {q : ℝ≥0}
    (h : R5Clauses κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q) :
    R5ClausesCompOn κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q := by
  obtain ⟨hX, hLattice, hOld, hLaw, hCover⟩ := h
  exact ⟨hX, hLattice, fun i ω hω =>
    ⟨(hOld i ω hω).1, (hOld i ω hω).2.1, (hOld i ω hω).2.2.1,
      (hOld i ω hω).2.2.2.1, (hOld i ω hω).2.2.2.2.subset⟩, fun gB hgB g hg i =>
    hasOldChartIncrementLawOn_of_hasOldChartIncrementLaw (hLaw gB hgB g hg i), hCover⟩

end InteractingSLE.Sec7.R5Out
