/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEraseCore

/-!
# SB2(1)'s erasure, part 3: the erasure clause (E2)

Packet PROVE-T14-SB2DRV (round 3). **`ae_erasure`**: almost surely on the launch event, the field read in the launch
chart record is, under the regular conditional law given the entrance σ-algebra `𝒢' = D.marks`, the GFF of the launch
word — exactly clause (E2) of `SB2EntranceK2NStatement` (on the whole launch event, so a fortiori on the entrance
event). From `exists_mean_hcond` (the conditional characteristic functionals on `D_A` agree given `𝒢'` and given the
retained past) by the random-chart transport `Restart.ae_condExp_cexp_chartTransport_random_on` applied under both
σ-algebras, the chart law of the retained past (`ae_condExp_chartField_eq_gaussCF`), the kernel GFF law from the
conditional characteristic functionals (`Exist.StagedLaw.ae_isGFFWithBoundaryData_condExpKernel`), and the frozen
chart under the `𝒢'`-kernels (`ae_frozen_chart_of_le`).

Inputs: Theorems 1.2–1.3 (as hypotheses, R48) and the named geometric input `SB2ErasedAvoidStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart WalkInf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **The chart law given the entrance σ-algebra**, in conditional-expectation form. -/
theorem ae_condExp_chartField_marks (hgeo : SB2ErasedAvoidStatement.{u}) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      P[fun ω' => Complex.exp (Complex.I * (chartField I h ω' φ : ℂ)) | D.marks] ω =
        gaussCF (sortedRep (I.word ω)) φ := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have h𝒢 := hS.2.1 (k + 1)
  have h𝒢' := D.marks_le HP
  have hpast := D.past_le_marks
  obtain ⟨M₀, hc𝒢, hc𝒢'⟩ := exists_mean_hcond hgeo h12p h13 HP I hu₀ D
  obtain ⟨hc, hliftc, -, hdom, hfwd, -, hliftm⟩ := I.chart_measurable
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma HP.boundary hS.1 (HP.drivers_regular _) (k + 1)
  have r1 := ae_condExp_cexp_chartTransport_random_on h𝒢 hc hdom hfwd hliftm hliftc HP.field.1 (chiC κ) hL𝒢
    hc𝒢 φ
  have r2 := ae_condExp_cexp_chartTransport_random_on (𝒢 := D.marks) h𝒢' hc (fun z => hpast _ (hdom z))
    (fun z => (hfwd z).mono hpast le_rfl) (fun z => (hliftm z).mono hpast le_rfl) hliftc HP.field.1 (chiC κ)
    (hpast _ hL𝒢) hc𝒢' φ
  filter_upwards [r1, r2, ae_condExp_chartField_eq_gaussCF HP I φ] with ω h1 h2 h3 hl
  have e1 := h1 hl
  have e2 := h2 hl
  have e3 := h3 hl
  exact e2.trans (e1.symm.trans e3)

/-- **Clause (E2): the erasure.** Almost surely on the launch event, the field read in the launch chart record is,
given the entrance σ-algebra, the GFF of the launch word. -/
theorem ae_erasure (hgeo : SB2ErasedAvoidStatement.{u}) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E (k + 1) → ∃ h' : Ω → DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport (I.chart ω₀) 1 0 (chiC κ) (h ω) (h' ω)) ∧
      IsGFFWithBoundaryData (condExpKernel P D.marks ω₀) h' (I.word ω₀).fn (I.word ω₀).jumps := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have h𝒢 := hS.2.1 (k + 1)
  have h𝒢' := D.marks_le HP
  have hYm := measurable_chartField I HP.field.1 h𝒢
  have hsort : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → (sortedRep (I.word ω)).IsSorted := by
    filter_upwards [I.field] with ω hf hl
    exact (sortedRep_spec (hf hl).1).1
  have hker := ae_isGFFWithBoundaryData_condExpKernel (𝒢 := D.marks) h𝒢' hsort hYm
    (fun φ => ae_condExp_chartField_marks hgeo h12p h13 HP I hu₀ D φ)
  filter_upwards [hker, ae_frozen_chart_of_le HP I h𝒢' D.past_le_marks, I.field] with ω₀ hk hfr hf hl
  obtain ⟨hc, hliftc, -⟩ := I.chart_measurable
  refine ⟨fun ω => Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω),
    fun ω => CondDriverBridge.isChartTransport_chartTransport_of_continuousOn (hc ω₀) (hliftc ω₀) 1 0 (chiC κ)
      (h ω), ?_⟩
  have hgff := (isGFFWithBoundaryData_sortedRep_iff (hf hl).1).1 (hk hl)
  have hm' : Measurable fun ω => Chart.chartTransport (hc ω₀) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun _ => I.chart ω₀) (fun _ => hc ω₀)
      (fun _ => MeasurableSet.const _) (fun _ => measurable_const.indicator (MeasurableSet.const _))
      (fun _ => measurable_const.indicator (MeasurableSet.const _)) (fun _ => hliftc ω₀) HP.field.1 1 0 (chiC κ)
  refine isGFFWithBoundaryData_congr_ae hgff hm' ?_
  filter_upwards [hfr hl] with ω hω
  exact chartTransport_congr_chart _ _ hω 1 0 (chiC κ) (h ω)

end InteractingSLE.Theorem14.SB.Lv
