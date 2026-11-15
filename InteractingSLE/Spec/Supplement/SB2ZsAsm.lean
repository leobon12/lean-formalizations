/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineAsm
import InteractingSLE.Spec.Supplement.SB2ZsSet

/-!
# SB2ZsAsm: `SB2DrvLineAsm` for the lifetime-generic line version `SB2LineVersionG`

Packet PROVE-T14-SB2DRV (round 15, decision D4: SB2(1) at announced stops). The declarations of `SB2DrvLineAsm` that
depend on the line version, for `SB2LineVersionG` (guards `a t < Λ w` in place of `a t < thr`), with the suffix `G`.
The proofs are the landed ones with the guard replaced. No source theorem is replaced.
-/
/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/

/-!
# SB2(1)'s line kernels, part 3: the kernel half from a geometric and a mean input

Packet PROVE-T14-SB2DRV (round 4). With the line sets `lineB` (`SB2DrvLineSet`: hull identity by construction, locality
by almost-sure enlargement of the proved line locality of `D.absSet`), the kernel half `SB2LineKernelRStatement` reduces
to two per-time statements:

* **`SB2LineGeomStatement`** (geometry): almost surely on the live cell, the physical union `A ∪ η([0, max(T, T_L)])`
  at the absolute physical time `T` misses the chart image `c(ℍ \ K_{a T})` of the complement of the relative hull;
* **`SB2LineMeanStatement`** (the line mean, the flow-line chart law of the remainder): for every local-set mean `g` of
  the line set, `g + u₀` read in the launch chart is the canonical mean `couplingMean κ W (a t) (bheProc …)` off the
  relative hull, almost surely on the live cell.

**`hasSafeLaw_hasSafeMembers_of_lineGeom`**, **`sb2LineKernelStatement_of_geom_mean`**, and
**`sb2DriverLinkAmbStatement_of_version_geom_mean`** (SB2(1)'s driver link from the version half and these two inputs).

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Restart Exist Exist.Staged Exist.StagedLaw GW1W GW1Conn WalkInf Restart.DomainMarkov Restart.DomainMarkov.K2
  Supp8.Q3Stop Sec7.PocketTraversal LocalSets

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **(S) and (L) on a type cell from the geometric and the mean input.** -/
theorem hasSafeLaw_hasSafeMembers_of_lineGeomG (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionG HP I D) {w : WordType} (hw : w ∈ I.types)
    (hIncl : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ lineLiveG Vd w t →
      Disjoint (D.absSet (t : ℝ≥0∞) ω) (chartImage (I.chart ω) (relHullG Vd t ω)))
    (hmean : ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (lineBG Vd w t) (WholeField.centredField h u₀) P g → ∀ φ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ I.word D.event w →
      Vd.a t ω < Vd.Λ w ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal) →
      Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ)
          (g ω + (h ω - WholeField.centredField h u₀ ω)) φ =
        ∫ z, couplingMean κ (fun s : ℝ => Vd.W s.toNNReal ω) (Vd.a t ω).toNNReal
          (bheProc κ (typedRhoL w) (typedRhoR w) Vd.W (geomLW Vd.W (cellXL κ ψ I.word w))
            (geomRW Vd.W (cellXR κ ψ I.word w)) ω (Vd.a t ω).toNNReal) z * φ z) :
    HasSafeLaw κ (typedRhoL w) (typedRhoR w) P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (Vd.Λ w) Vd.W
        (geomLW Vd.W (cellXL κ ψ I.word w)) (geomRW Vd.W (cellXR κ ψ I.word w))
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) ∧
      HasSafeMembers P Vd.𝓗 (seedCell κ ψ I.word D.event w)
        (Vd.Λ w) Vd.W
        (fun ω => Chart.chartTransport (I.chart_measurable.1 ω) 1 (ψ * chiC κ) (chiC κ) (h ω)) := by
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData HP.field hu₀
  have hBm : ∀ t, Measurable[mΩ, hittingSigma] (lineBG Vd w t) := fun t =>
    WalkMean.measurable_hitting_of_avoid ((D.lineFiltC HP).le t) fun U hUH => measurableSet_disjoint_lineBG Vd hw t hUH
  have hBc : ∀ t ω, lineBG Vd w t ω ⊆ H ∧ IsOpen (H \ lineBG Vd w t ω) := fun t ω =>
    ⟨lineB_subset_HG Vd w t ω, isOpen_H_sdiff_lineBG Vd w t ω⟩
  have hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (D.lineFiltC HP t) (lineBG Vd w t)
      (WholeField.centredField h u₀) P := by
    intro t
    refine isHistoryAvoidanceLocal_of_ae_enlargement
      (D.isHistoryAvoidanceLocal_lineFiltC HP t (D.isHistoryAvoidanceLocal_abs h12p h13 HP hu₀ (t : ℝ≥0∞))) ?_
      fun U hUH => measurableSet_disjoint_lineBG Vd hw t hUH
    filter_upwards [hIncl t] with ω hω
    by_cases hl : ω ∈ lineLiveG Vd w t
    · intro z hz
      unfold lineBG
      rw [ite_eq_left hl]
      exact ⟨hz.2, fun hzc => Set.disjoint_left.1 (hω hl) hz.1 hzc⟩
    · intro z hz
      unfold lineBG
      rw [ite_eq_right hl]
      exact hz.2
  have hlocal : ∀ t, IsLocalSet (lineBG Vd w t) (WholeField.centredField h u₀) P := fun t =>
    ((isLocalSet_tfae hh0 (hBm t) (Eventually.of_forall (hBc t))).out 4 1).2 (hloc t).isAvoidanceLocal
  choose g hg using fun t => IsLocalSet.exists_isLocalSetMean hh0 (hBm t) (hlocal t)
  exact hasSafeLaw_hasSafeMembers_of_lineSetsG HP I hu₀ D Vd hw (lineBG Vd w) hBm hBc hloc
    (fun t => Eventually.of_forall fun ω hF hlt => H_sdiff_lineB_of_liveG Vd w t ⟨hF, hlt⟩) g hg
    (fun t φ => hmean t (g t) (hg t) φ)
/-- **Named input (geometry of the lines)**: almost surely on the live cell, the physical union up to `max(T, T_L)`
misses the chart image of the complement of the relative hull at `a T`. -/
def SB2LineGeomStatementG : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ) (_hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (Vd : SB2LineVersionG HP I D),
    ∀ w ∈ I.types, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ lineLiveG Vd w t →
      Disjoint (D.absSet (t : ℝ≥0∞) ω) (chartImage (I.chart ω) (relHullG Vd t ω))
end InteractingSLE.Theorem14.SB.Lv

