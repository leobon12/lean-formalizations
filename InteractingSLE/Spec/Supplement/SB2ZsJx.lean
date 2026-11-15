/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JxLate
import InteractingSLE.Spec.Supplement.SB2ZsEarly

/-!
# SB2ZsJx: `SB2JxLate` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2JxLate` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

/-!
# SB2(1)'s late (S) line mean, part 2: the assembly from FIN's union mean at a stopping time

Packet PROVE-T14-SB2DRV (round 8). The late regime of the (S) line mean (`SB2LineSMeanLateStatement`, `T_L < t`)
is reduced to FIN's union mean for the union `walkFill A' ∪ (K + u)` of `exists_flowUnion` (the coupling hull at a
finite stopping time `τ ≤ t`, `τ < ζ`), read in the launch chart on `{t ≤ τ}`:

* **`SB2JxFinStatement`** (named input, engineering: `FinRel.ae_chartTransport_eq_couplingMean_of_relConfigJK` in the
  coupling's coordinates; route in the handoff §R8): every local-set mean of that union, read in the launch chart, is
  K2's canonical mean off the relative hull, almost surely on the live cell after `T_L` and on `{t ≤ τ}`;
* **`SB2JxTipStatement`** (named hypothesis, NEW MATHEMATICS — the fixed-time no-contact statement): at a fixed line
  time after `T_L`, almost surely on the live cell, the upper flow's tip lies in the launch chart's domain
  `ℍ \ fill(A)` (`OrdGap.ae_mem_H_at` gives only `η(t) ∈ ℍ`); it is what FIN's configuration at the line time needs
  (`FinRel.isRelConfigJK_of_s2_liftOn`'s `hγH`);
* **`sb2LineSMeanLateStatement_of_fin`** (PROVED): an announcing sequence `σ_n ↑ ζ` of the driving filtration, the
  stops `τ_n = min(σ_n, t)`, the comparison of `exists_flowUnion` (the line set's mean equals the union's on
  `{t ≤ τ_n}`), and the cover of the live cell by `{t ≤ σ_n}` (`Vd.alive`: `t < ζ`);
* `sb2DriverLinkAmbStatement_of_versionR_fin`.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets Sec6

/-- **Named input (FIN's union mean at a stopping time of the flow, read in the launch chart)**: for the upper flow's
coupling, a finite stopping time `τ ≤ t` of its driving filtration with `τ < ζ`, a version `K` of the coupling hull
`K_τ`, and a local-set mean `gU` of `walkFill A' ∪ (K + u)`, the field `gU + u₀` read in the launch chart is K2's
canonical mean off the relative hull at `a t`, almost surely on the live cell, after `T_L` and on `{t ≤ τ}`. -/
def SB2JxFinStatementG : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionG HP I D),
    ∀ w ∈ I.types, ∀ A' : Ω → Set ℂ, (∀ ω, A' ω ⊆ H) →
    (∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] {ω | Disjoint (A' ω) U}) →
    (∀ᵐ ω ∂P, A' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) →
    ∀ (t : ℝ≥0) (h' : Ω → DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
      (VL : Fin (flowLineNL b jumps u) → ℝ≥0 → Ω → ℝ) (VR : Fin (flowLineNR b jumps u) → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ), (∀ ω, IsTranslateAddConst u (ψ * chiC κ) (h ω) (h' ω)) →
    IsOptionalHullCoupling κ (flowLineXL b jumps u) (flowLineXR b jumps u) (flowLineRhoL κ b jumps u ψ)
      (flowLineRhoR κ b jumps u ψ) P 𝓕 W VL VR B ζ h' →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun s => W s ω) (ζ ω) (fun s => η ω s - u)) →
    ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (τ : Ω → WithTop ℝ≥0),
    IsStoppingTime (drivingFiltration P hX) τ → (∀ᵐ ω ∂P, τ ω < ζ ω) → (∀ ω, τ ω ≤ (t : WithTop ℝ≥0)) →
    ∀ K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] K →
    (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => W r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
    ∀ gU : Ω → DistOn upperHalfPlaneOpens,
    IsLocalSetMean (fun ω => walkFill κ b jumps E k A' ω ∪ (fun z : ℂ => z + u) '' K ω)
      (WholeField.centredField h u₀) P gU → ∀ φ : TestOn upperHalfPlaneOpens,
    ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < Vd.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
      (t : WithTop ℝ≥0) ≤ τ ω →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (gU ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z
/-- **The late regime of the (S) line mean from FIN's union mean at the stops `min(σ_n, t)`** (Theorems 1.2–1.3 as
hypotheses). -/
theorem sb2LineSMeanLateStatement_of_finG (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hF : SB2JxFinStatementG.{u}) : SB2LineSMeanLateStatementG.{u} := by
  intro κ b jumps Ω _ _ P _ h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw A' hA'H hA'm hA'ae t g hg φ
  classical
  obtain ⟨h', 𝓕, W, VL, VR, B, htrans, hC, htr⟩ := HP.flow
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ) 0
      (flowLineXL b jumps u) (flowLineXR b jumps u)
  · -- an inadmissible seed: the flow dies at once, the live cell is empty
    have h0 := IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hseed
    filter_upwards [h0, Vd.alive w hw t] with ω hζ0 hal hcell hlt _ _
    have := hal hcell hlt
    rw [hζ0] at this
    exact absurd this (not_lt.2 zero_le)
  obtain ⟨σ, hσ⟩ := WholeField.exists_isAnnouncingSeq_driving hC.1 HP.kappa_pos hX hseed
  have key : ∀ n : ℕ, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < Vd.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < (t : ℝ≥0∞) →
      t ≤ σ n ω →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (g ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z := by
    intro n
    have hτ : IsStoppingTime (drivingFiltration P hX)
        (fun ω => min ((σ n ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0)) := (hσ.1 n).min_const t
    have hτζ : ∀ᵐ ω ∂P, min ((σ n ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0) < ζ ω :=
      (hσ.2.2.1 n).mono fun ω hω => lt_of_le_of_lt (min_le_left _ _) hω
    have hτt : ∀ ω, min ((σ n ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0) :=
      fun ω => min_le_right _ _
    obtain ⟨K, hKm, hKe, hUm, -, hUl, hcmp⟩ :=
      exists_flowUnion h12p h13 HP hu₀ D hA'H hA'm hA'ae t htrans hC htr hX hτ hτζ hτt
    obtain ⟨gU, hgU⟩ := IsLocalSet.exists_isLocalSetMean hh0 hUm hUl
    have h1 := hcmp g gU hg hgU
    have h2 := hF κ b jumps P h E k u ψ η ζ HP I u₀ hu₀ D Vd w hw A' hA'H hA'm hA'ae t h' 𝓕 W VL VR B htrans hC
      htr hX _ hτ hτζ hτt K hKm hKe gU hgU φ
    filter_upwards [h1, h2] with ω e1 e2 hcell hlt hφ hTL htσ
    have htτ : (t : WithTop ℝ≥0) ≤ min ((σ n ω : ℝ≥0) : WithTop ℝ≥0) (t : WithTop ℝ≥0) :=
      le_min (WithTop.coe_le_coe.2 htσ) le_rfl
    rw [← e1 hcell.1.1 hTL htτ]
    exact e2 hcell hlt hφ hTL htτ
  filter_upwards [ae_all_iff.2 key, Vd.alive w hw t, hσ.2.2.2] with ω hk hal hann hcell hlt hφ hTL
  obtain ⟨n, hn⟩ := hann t (hal hcell hlt)
  exact hk n hcell hlt hφ hTL hn
end InteractingSLE.Theorem14.SB.Lv

