/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInResidualLaw
import InteractingSLE.Spec.Sec7.PocketStopSideCoverGeometry
import InteractingSLE.Spec.Sec7.PocketSideInRef

/-!
# R.5's collar germ at a fixed relative capacity from old-chart increment laws

PROVE-SIDE-LATCOL. The collar leaf `hCollar` of `pocketStopSideLimit_of_reference_germs_probes` (and its native
late form `hSideCollar`) asks, at a fixed relative capacity `q`, for every current access `ξ` off the force
jumps, a reference `i` with four clauses: (C1) the current mean and the reference mean have the same germ at `ξ`
in the current relative chart, (C2) the reference's own corrected height `b`, (C3) the inherited lift
difference `d`, and (C4) the word identity `b + χ d = (word with phase)(ξ) − a`.

Lemma R.5's proof (spec p. 475) obtains (C1) as follows: for each rational original time `s` apply the nested
marked local-set law at the enlarged stop `T ∨ s`; in the `s` chart the subsequently added local set avoids a
selected half-disc, and zero-boundary decay preserves the old germ there; intersect the countably many
probability-one statements before selecting the suitable member pathwise. PROVE-POCKET-SIDEIN proved the
fixed-pair step (`ae_physical_germ_of_old_chart_increment_law`, from the named law
`HasOldChartIncrementLaw`) for original rational pairs `(s, T)`.

Here the same step is assembled at a **fixed relative capacity `q`** (the collar's quantifier), with the
current chart the relative chart at `q`, a countable family of reference charts and pair events, and the laws
`HasOldChartIncrementLaw P (M i) (old i) (relChart c γ q) (gB i) g` for every version of the means — the
source's per-`(s, q)` law at `T(q) ∨ s`. The output is exactly the collar's shape: (C1) is **proved**, and only
the pathwise selection with the reference's own height, lift and word identity (C2)–(C4) remains an input
(`hCover`). The word `Wd` and the jump set `J` are arbitrary, so the same theorem serves the generic `phaseData`
form and the native late form.

No Theorem 1.2/1.3 or `*_of_param` result is used (R43/R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling Aux119Heights

section Charts

variable {Ω : Type*} {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart} {q : ℝ≥0} {ω : Ω}

/-- The relative chart of a driven curve in a conformal chart is conformal before the lifetime. -/
theorem isConformal_relChart_of_driven (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    (hc : (c ω).IsConformal) : (relChart c γ q ω).IsConformal := by
  obtain ⟨W, hW, hW0, -, -, -, hrel⟩ := exists_relChart_eq_loewner (c := c) hγ hq
  rw [hrel]
  exact hc.loewner hW hW0 q.coe_nonneg

/-- Before the lifetime, the complement of the canonical marked set is the relative chart's domain. -/
theorem H_diff_activeCompl_eq_relChart_dom (hω : ω ∈ A) (hq : (q : ℝ≥0∞) < capLife (γ ω))
    (hγ : IsDrivenCurve (γ ω)) (hc : (c ω).IsConformal) :
    H \ activeCompl A γ c q ω = ((relChart c γ q ω).dom : Set ℂ) := by
  have hdom := activeDom_eq_relChart_dom hω hq hγ hc
  have hsub : activeDom A γ c q ω ⊆ H := by
    rw [hdom, (isConformal_relChart_of_driven hγ hq hc).coe_dom]
    exact image_subset_iff.2 (isConformal_relChart_of_driven hγ hq hc).2.1
  rw [activeCompl, sdiff_sdiff_cancel_left hsub, hdom]

end Charts

/-- **R.5's collar germ (C1) at a fixed relative capacity.** Let `old i` be countably many reference charts
with pair events `M i` inside the live event, each conformal with domain `H ∖ B i` containing the current
relative chart's domain, and suppose the per-pair old-chart increment laws hold for every version of the
reference means `gB` and of the current mean `g`. If the pathwise selection `hCover` supplies, at every access
off `J`, a reference whose old inverse half-disc lies in the current domain, the old-forward/current-inverse
transition limit, and the reference's own height, lift difference and word identity, then the full collar
conclusion holds, with the germ comparison (C1) proved. -/
theorem collar_of_oldChartIncrementLaws {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    {q : ℝ≥0} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {k : ℝ}
    {B : ι → Ω → Set ℂ} {liftB : ι → Ω → ℂ → ℝ} {J : Ω → Set ℝ} {Wd : Ω → ℝ → ℝ}
    {M : ι → Set Ω} {old : ι → Ω → Chart}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hOld : ∀ i, ∀ ω ∈ M i, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω) ∧ (old i ω).IsConformal ∧
      ((relChart c γ q ω).dom : Set ℂ) ⊆ (old i ω).dom ∧ ((old i ω).dom : Set ℂ) = H \ B i ω)
    (hLaw : ∀ gB : ι → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (B i) h₀ P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (activeCompl A γ c q) h₀ P g →
      ∀ i, HasOldChartIncrementLaw P (M i) (old i) (relChart c γ q) (gB i) g)
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
  have hGerm := fun i => ae_physical_germ_of_old_chart_increment_law (P := P) (M := M i)
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
    rw [hdomOld]
    exact hvB
  have hvBr' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (old i ω).dom →
      gB i ω φ = ∫ z, harmRep (gB i ω) (H \ B i ω) z * φ z := by
    rw [hdomOld]
    exact hvBr
  have hv' : InnerProductSpace.HarmonicOnNhd v (relChart c γ q ω).dom := by
    rw [← hdomCur]
    exact hv
  have hvr' : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ (relChart c γ q ω).dom →
      g ω φ = ∫ z, v z * φ z := by
    rw [← hdomCur]
    exact hvr
  exact hωG i hMi _ v hvB' hvBr' hv' hvr' ξ x r hr hcol htr

end InteractingSLE.Sec7.PocketStopSide
