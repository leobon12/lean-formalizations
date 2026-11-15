/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEraseGeo
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas
import InteractingSLE.Spec.Exist.StagedLawData
import InteractingSLE.Spec.Exist.StagedLawKernel
import InteractingSLE.Spec.Exist.StagedLawStep
import InteractingSLE.Spec.Sec5.CrossCondStagedMean
import InteractingSLE.Spec.Supplement.RelSafeS6
import InteractingSLE.Spec.Restart.R1Glue
import InteractingSLE.Spec.Supplement.CondDriverBridge

/-!
# SB2(1)'s erasure, part 1: the chart law of the retained past in conditional-expectation form

Packet PROVE-T14-SB2DRV (round 3), toward clause (E2). The landed chart record `K2LaunchInputs` gives the law of the
chart field under the regular conditional laws given the retained past `pastSigma (k + 1)`; the erasure argument
works with conditional characteristic functionals. Here:

* `sortedRep`: a sorted word with the same boundary data (`IsGFFWithBoundaryData` only sees the data off the jumps);
  the Gaussian characteristic functional `gaussCF` is that of the sorted representative;
* `chartField I h ω = chartTransport (I.chart ω) 1 0 χ (h ω)` and **`ae_condExp_chartField_eq_gaussCF`**: a.s. on the
  launch event, `E[exp(i ⟨chartField, ψ⟩) | pastSigma (k + 1)] = gaussCF (sortedRep (I.word ω)) ψ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart WalkInf

/-! ### Sorted representatives -/

open Classical in
/-- A sorted word with the same boundary data (the word itself if its data are not piecewise constant). -/
def sortedRep (c : BoundaryWord) : BoundaryWord :=
  if hc : IsPiecewiseConstantBoundaryData c.fn c.jumps then
    Classical.choose (Restart.BoundaryWord.exists_fn_eq_strictMonoOn hc)
  else c

theorem sortedRep_spec {c : BoundaryWord} (hc : IsPiecewiseConstantBoundaryData c.fn c.jumps) :
    (sortedRep c).IsSorted ∧ (sortedRep c).jumps = c.jumps ∧ ∀ y ∉ c.jumps, (sortedRep c).fn y = c.fn y := by
  have e : sortedRep c = Classical.choose (Restart.BoundaryWord.exists_fn_eq_strictMonoOn hc) :=
    dite_eq_left_of_eq_true (eq_true hc)
  obtain ⟨hmono, hj, hfn⟩ := Classical.choose_spec (Restart.BoundaryWord.exists_fn_eq_strictMonoOn hc)
  rw [e]
  refine ⟨fun i j hij hj' => hmono.monotoneOn (show i ∈ Iio _ from lt_of_le_of_lt hij hj') hj' hij, hj, hfn⟩

/-- The GFF law sees only the boundary data of the sorted representative. -/
theorem isGFFWithBoundaryData_sortedRep_iff {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {Y : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} (hc : IsPiecewiseConstantBoundaryData c.fn c.jumps) :
    IsGFFWithBoundaryData Q Y (sortedRep c).fn (sortedRep c).jumps ↔ IsGFFWithBoundaryData Q Y c.fn c.jumps := by
  obtain ⟨-, hj, hfn⟩ := sortedRep_spec hc
  rw [hj]
  exact Restart.isGFFWithBoundaryData_congr Q Y fun y hy => hfn y (by simpa using hy)

/-! ### The chart law of the retained past -/

section ChartLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- The field read in the launch chart record. -/
def chartField (I : K2LaunchInputs κ b jumps P h E k u ψ) (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  Chart.chartTransport (I.chart_measurable.1 ω) 1 0 (chiC κ) (h ω)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem chartTransport_congr_chart {c c' : Chart} (hc : c.IsConformal) (hc' : c'.IsConformal) (e : c = c')
    (σ a k' : ℝ) (f : DistOn upperHalfPlaneOpens) :
    Chart.chartTransport hc σ a k' f = Chart.chartTransport hc' σ a k' f := by
  subst e
  rfl

theorem measurable_chartField (I : K2LaunchInputs κ b jumps P h E k u ψ) (hhm : Measurable h)
    (h𝒢 : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ mΩ) :
    Measurable (chartField I h) := by
  obtain ⟨hc, hliftc, -, hdom, hfwd, -, hliftm⟩ := I.chart_measurable
  exact Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z)) (fun z => (hfwd z).mono h𝒢 le_rfl)
    (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hhm 1 0 (chiC κ)

theorem isChartTransport_chartField (I : K2LaunchInputs κ b jumps P h E k u ψ) (ω : Ω) :
    IsChartTransport (I.chart ω) 1 0 (chiC κ) (h ω) (chartField I h ω) :=
  CondDriverBridge.isChartTransport_chartTransport_of_continuousOn (I.chart_measurable.1 ω)
    (I.chart_measurable.2.1 ω) 1 0 (chiC κ) (h ω)

/-- **The chart law of the retained past, in conditional-expectation form.** -/
theorem ae_condExp_chartField_eq_gaussCF (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      P[fun ω' => Complex.exp (Complex.I * (chartField I h ω' φ : ℂ)) |
        pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] ω = gaussCF (sortedRep (I.word ω)) φ := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have h𝒢 := hS.2.1 (k + 1)
  have hYm := measurable_chartField I HP.field.1 h𝒢
  have hint : Integrable (fun ω' => Complex.exp (Complex.I * (chartField I h ω' φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hYm)
  filter_upwards [condExp_ae_eq_integral_condExpKernel h𝒢 hint, I.field, I.frozen] with ω₀ hce hf hfr hl
  obtain ⟨hpc, h', hct, hgff⟩ := hf hl
  have hY : (fun ω => chartField I h ω) =ᵐ[condExpKernel P (pastSigma κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1))
      ω₀] h' := by
    filter_upwards [hfr] with ω hω
    have h1 : IsChartTransport (I.chart ω₀) 1 0 (chiC κ) (h ω) (chartField I h ω) := by
      have := isChartTransport_chartField I (h := h) ω
      have e : I.chart ω = I.chart ω₀ := hω
      rwa [e] at this
    exact h1.unique (I.chart_measurable.1 ω₀) (hct ω)
  have hsort := (sortedRep_spec hpc).1
  have hgff' := (isGFFWithBoundaryData_sortedRep_iff hpc).2 hgff
  rw [hce]
  refine (integral_congr_ae ?_).trans (integral_cexp_eq_gaussCF hsort hgff' φ)
  filter_upwards [hY] with ω hω
  rw [hω]

end ChartLaw

end InteractingSLE.Theorem14.SB.Lv
