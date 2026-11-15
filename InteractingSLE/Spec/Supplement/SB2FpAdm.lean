/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WeLow
import InteractingSLE.Spec.Supplement.SB2FpHull
import InteractingSLE.Spec.Supplement.SB2NcFrz
import InteractingSLE.Spec.Supplement.SB2FmWord
import InteractingSLE.Spec.Supplement.SB2QxCanon

/-!
# The upper stage witness word is admissible left of the entry

Worker PROVE-SB2-F3LAW (round 4). SB2WORD's root clause `Lz.sb2LowerLeftWeightStatement_of_theorem13` holds for every
relative datum of the upper launch; read on the stage witness `(β₀, Y₀)` of the regularized upper history (whose field
is, under the upper kernel, the chart transport of `h` by the launch chart) it gives `Fm.LeftAdm κ (β₀ ω₀) upperEntry`.

* `lt_of_cumWeightLeft_gt`, `ae_left_regFam` (the lower walk's premise for the regularized family),
  **`ae_leftAdm_witness`**.

R48: Theorem 1.3 (at universe `0`) appears only as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fp

open Restart Exist Exist.Staged Exist.StagedLaw Lu Fm FlowDilate

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- The clause's form converted back: a left cumulative weight `> −2` is a height below `λ`. -/
theorem lt_of_cumWeightLeft_gt (hκ : 0 < κ) {v : ℝ} (hv : -2 < Sec4.cumWeightLeft κ v) : v < sleLambda κ := by
  have hl := Sec4.sleLambda_pos hκ
  unfold Sec4.cumWeightLeft at hv
  have h1 : v / sleLambda κ < 1 := by rw [neg_div] at hv; linarith
  exact (div_lt_one hl).1 h1

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The lower walk's premise for the regularized family** (from the family's, through the a.s. equal runs). -/
theorem ae_left_regFam {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ}
    (hrunU : ∀ᵐ ω ∂P, ∀ n, ExplState.run κ b jumps (upperSpec u l)
      (fun j => StagedReg.regFam E (upperSpec u l) j ω) n =
      ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) n)
    (hrunB : ∀ᵐ ω ∂P, ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    (hleft : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) :
    ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps (StagedReg.regFam E) u l k →
      upperPrefix κ b jumps (StagedReg.regFam E) u l k ω ∩
        rightSideOf (lowerWalkSet κ b jumps (StagedReg.regFam E) ω) = ∅ := by
  filter_upwards [hrunU, hrunB, hleft] with ω hU hB hl hω
  have hω' : ω ∈ upperLaunchSet κ b jumps E u l k := by
    have : (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [← hU (k + 1)]
      exact hω
    exact this
  have hP : upperPrefix κ b jumps (StagedReg.regFam E) u l k ω = upperPrefix κ b jumps E u l k ω := by
    show prefixPhysSet κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω) k ∪ _ =
      prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪ _
    rw [Qx.prefixPhysSet_congr _ (hU k)]
  have hW : lowerWalkSet κ b jumps (StagedReg.regFam E) ω = lowerWalkSet κ b jumps E ω := by
    unfold lowerWalkSet ExplState.physSet
    simp only [hB]
  rw [hP, hW]
  exact hl hω'

/-- **The upper stage witness word is admissible left of the entry** (SB2WORD's root clause read on the witness):
for a stage witness `(β₀, Y₀)` of the regularized upper history at `k`, almost surely on a launch at `k`, every
height of `β₀ ω₀` left of `upperEntry` has left weight `> −2` for the lower flow. -/
theorem ae_leftAdm_witness (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} (hu : u ≤ 0) (hlp : l.Pairwise (fun p q => p.2 < q.2))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hleft : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {β₀ : Ω → BoundaryWord} {Y₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h (upperSpec u l) (StagedReg.regFam E (upperSpec u l)) k β₀ Y₀) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ upperLaunchSet κ b jumps (StagedReg.regFam E) u l k →
      LeftAdm κ (β₀ ω₀) (upperEntry κ b jumps (StagedReg.regFam E) u l k ω₀) := by
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hbcU := isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hbcB := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hER' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    WalkLaw.stagedPiecesRegular_regHist (hER spec hs)
  have hleft' := ae_left_regFam (k := k) (hrun _ hbcU) (hrun _ hbcB) hleft
  have hLz := Lz.sb2LowerLeftWeightStatement_of_theorem13 h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    (StagedReg.regFam E) hE' hER' u l k hu hlp hlθ hL hleft'
  have hm : pastSigma κ b jumps (upperSpec u l) (StagedReg.regFam E (upperSpec u l)) k ≤ mΩ :=
    (hE' _ hbcU).2.1 k
  have hrunQ := Nc.ae_ae_run_eq_of_regular (P := P) (upperSpec u l) (hreg' (upperSpec u l)) hm le_rfl
  have htrQ := KernelTower.ae_ae_condExpKernel_of_ae (P := P) hm hW.2.2.1
  filter_upwards [hLz, hrunQ, htrQ, hW.2.2.2, hW.2.2.1] with ω₀ hLzω hrunω htrω hlawω hcω hlaunch
  obtain ⟨⟨c₀, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlaunch
  have hc0 := (eq_launch_of_launches _ _ hcθ).2.2
  obtain ⟨hconf, hcont, -⟩ := hcω hlaunch
  rw [← hc0] at hconf hcont
  set h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf 1 0 (chiC κ) (h ω) with hh'
  have htr' : ∀ ω, IsChartTransport c₀ 1 0 (chiC κ) (h ω) (h' ω) := fun ω =>
    Chart.isChartTransport_chartTransport hconf (Chart.locallyIntegrableOn_of_continuousOn hcont) 1 0 (chiC κ) (h ω)
  have hh'm : Measurable h' := (Chart.measurable_chartTransport hconf 1 0 (chiC κ)).comp hh.1
  have hYeq : Y₀ =ᵐ[condExpKernel P (pastSigma κ b jumps (upperSpec u l)
      (StagedReg.regFam E (upperSpec u l)) k) ω₀] h' := by
    filter_upwards [hrunω, htrω] with ω hr ht
    have hlω : (ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω)
        (k + 1)).2.2.2.1 k ≠ none := by
      rw [launches_run_succ_of_run_eq (upperSpec u l) (hr k le_rfl)]
      exact hlaunch
    obtain ⟨-, -, htω⟩ := ht hlω
    rw [hr k le_rfl, ← hc0] at htω
    exact htω.unique hconf (htr' ω)
  have hlaw' := isGFFWithBoundaryData_congr_ae (hlawω hlaunch) hh'm hYeq
  have hadm := hLzω c₀ θ hcθ (β₀ ω₀).fn (β₀ ω₀).jumps h' (BoundaryWord.isPiecewiseConstantBoundaryData _) htr'
    hlaw' _ rfl
  intro y hy hyJ
  have h1 := hadm (y - upperEntry κ b jumps (StagedReg.regFam E) u l k ω₀) (by linarith) (by
    intro hmem
    obtain ⟨z, hz, hze⟩ := Finset.mem_image.1 hmem
    apply hyJ
    have : z = y := by simp only [raff] at hze; linarith
    rw [← this]
    exact hz)
  have h2 : affData 1 (-upperEntry κ b jumps (StagedReg.regFam E) u l k ω₀) (β₀ ω₀).fn
      (y - upperEntry κ b jumps (StagedReg.regFam E) u l k ω₀) = (β₀ ω₀).fn y := by
    simp only [affData]
    congr 1
    ring
  rw [h2] at h1
  exact lt_of_cumWeightLeft_gt hκ h1

end InteractingSLE.Theorem14.SB.Fp
