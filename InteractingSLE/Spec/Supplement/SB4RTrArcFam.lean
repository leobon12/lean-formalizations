/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrArcSets

/-!
# The staged family read from the end of the forced arc

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). **`exists_arcFam`**: in the setting of SB4's
initial-arc leaf, the field read from `v` (`affField (−v) h`, data `b(· + v)`) carries a staged family (for every
boundary-continued program, with regular pieces) whose schedule from `0` is the translated schedule from `v` (same
drivers, runs translated almost surely) and whose lower walk is the original lower walk restarted at `v` (almost surely
`lowerWalk − v = [−v, 0] ∪ lowerWalk'`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate Lu
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

theorem trInstr_scheduleProgram (v : ℝ) (τ₀ : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    (scheduleProgram τ₀ l).map (trInstr v) = scheduleProgram τ₀ l := by
  induction l generalizing τ₀ with
  | nil => rfl
  | cons p l ih =>
    simp only [scheduleProgram, List.map_cons, ih]
    rfl

theorem trSpec_sspec (v : ℝ) (l : List (ℝ × ℝ≥0)) : trSpec v (sspec v l) = upperSpec 0 l := by
  show (v - v, true, (scheduleProgram 0 l).map (trInstr v)) = _
  rw [trInstr_scheduleProgram, sub_self]
  rfl

section Fam

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The staged family read from the end of the forced arc.** -/
theorem exists_arcFam (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b J P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b J P spec (E spec))
    {v : ℝ} (hv : 0 < v) (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b J, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∃ ET : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ (affData 1 (-v) b) (affJumps 1 (-v) J) P (fun ω => affField (-v) one_pos (h ω)) spec
          (ET spec)) ∧
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ (affData 1 (-v) b) (affJumps 1 (-v) J) P spec (ET spec)) ∧
      ET (upperSpec 0 l) = StagedReg.regHist (sspec v l) (E (sspec v l)) ∧
      (∀ᵐ ω ∂P, ∀ k, ExplState.run κ (affData 1 (-v) b) (affJumps 1 (-v) J) (upperSpec 0 l)
          (fun j => ET (upperSpec 0 l) j ω) k =
        trState v (ExplState.run κ b J (sspec v l) (fun j => E (sspec v l) j ω) k)) ∧
      ∀ᵐ ω ∂P, (fun z => z - (v : ℂ)) '' lowerWalkSet κ b J E ω =
        ((↑) : ℝ → ℂ) '' Icc (-v) 0 ∪ lowerWalkSet κ (affData 1 (-v) b) (affJumps 1 (-v) J) ET ω := by
  classical
  set B := affData 1 (-v) b with hB
  set JB := affJumps 1 (-v) J with hJB
  have hbB : IsPiecewiseConstantBoundaryData B JB := isPiecewiseConstantBoundaryData_affData one_pos hb
  have hhT : IsGFFWithBoundaryData P (fun ω => affField (-v) one_pos (h ω)) B JB :=
    IsGFFWithBoundaryData.affine_finset (m := -v) one_pos hh
  obtain ⟨E₀, hE₀⟩ := exists_isStagedHistory_regular_of_thm12_thm13 h12 h13 hκ hκ4 hbB hhT
  set lwT := boundaryWalkSpec B JB (-(Real.pi / 2)) true with hlwT
  set sch := upperSpec 0 l with hsch
  have hlwTb : IsBoundaryContinuedProgram lwT.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec B JB ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hschb : IsBoundaryContinuedProgram (sspec v l).2.2 := GW2Sched.isBoundaryContinuedProgram_scheduleProgram hθ 0
  have hne : sch ≠ lwT := fun he => by
    have := congrArg (fun s : ExplSpec => s.2.1) he
    simp [hsch, hlwT, upperSpec, boundaryWalkSpec] at this
  obtain ⟨hSs, hSr, hSrun⟩ := isStagedHistory_tr_regHist (κ := κ) hb v (hE _ hschb) (hER _ hschb)
  rw [trSpec_sspec] at hSs hSr hSrun
  obtain ⟨hWs, hWr, hWphys⟩ := restartFam_spec h13₀ hκ hκ4 hb hh hcf hζ' hE hER hv hlow0 hlow
    (hE₀ lwT hlwTb).1 (hE₀ lwT hlwTb).2
  set ET : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun spec =>
    if spec = sch then StagedReg.regHist (sspec v l) (E (sspec v l))
    else if spec = lwT then restartFam (StagedReg.regHist lwT (E₀ lwT) 0)
      (StagedReg.regHist (boundaryWalkSpec b J (-(Real.pi / 2)) true) (E (boundaryWalkSpec b J (-(Real.pi / 2)) true)))
    else E₀ spec with hET
  have hETs : ET sch = StagedReg.regHist (sspec v l) (E (sspec v l)) := by simp [hET]
  have hETw : ET lwT = restartFam (StagedReg.regHist lwT (E₀ lwT) 0)
      (StagedReg.regHist (boundaryWalkSpec b J (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b J (-(Real.pi / 2)) true))) := by
    simp [hET, Ne.symm hne]
  have hETo : ∀ spec, spec ≠ sch → spec ≠ lwT → ET spec = E₀ spec := fun spec h1 h2 => by simp [hET, h1, h2]
  refine ⟨ET, fun spec hspec => ?_, fun spec hspec => ?_, hETs, ?_, ?_⟩
  · by_cases h1 : spec = sch
    · rw [h1, hETs]; exact hSs
    · by_cases h2 : spec = lwT
      · rw [h2, hETw]; exact hWs
      · rw [hETo spec h1 h2]; exact (hE₀ spec hspec).1
  · by_cases h1 : spec = sch
    · rw [h1, hETs]; exact hSr
    · by_cases h2 : spec = lwT
      · rw [h2, hETw]; exact hWr
      · rw [hETo spec h1 h2]; exact (hE₀ spec hspec).2
  · rw [hETs]
    exact hSrun
  · filter_upwards [hWphys] with ω hω
    rw [hω]
    unfold lowerWalkSet
    rw [← hlwT, hETw]

end Fam

end InteractingSLE.Theorem14.SB.Lf
