/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CtStmt

/-!
# Switching between data words of one field law at the relative root

Packet PROVE-SB2-CONDFIN, round 11 (D55). Three facts for the root's determination:

* **`isStageWitness_zero_of_law`**: at stage `0` any constant word `w` that is a data word of the field read in the
  initial chart gives a stage witness (the past at stage `0` is trivial);
* **`ae_codeMatch_switch`** (Theorems 1.2–1.3): two constant data words `w`, `w'` of one field law give, almost
  surely, the same driver code: the code of `(w', Y)` matches the driver of `(w, Y)`. This is LCMEAN's law-code switch
  (`Mx.ae_codeMatch_of_lawCode`) applied to the relative walk whose every piece is the driver of `(w, Y)`;
* **`ent_relOff_of_not_zeroRoot`**: when `R` lies on B's walk and the relative root is not the zero root, `R` has
  entered by the offset stage.

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ct

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx FlowDilate

/-- **A constant data word of the field in the initial chart is a stage-`0` witness.** -/
theorem isStageWitness_zero_of_law {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hm : Measurable h) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {w : BoundaryWord}
    (hw : IsGFFWithBoundaryData P (fun ω => flowField spec.1 0 (h ω)) w.fn w.jumps) :
    IsStageWitness κ b jumps P h spec E 0 (fun _ => w) (fun ω => flowField spec.1 0 (h ω)) := by
  refine ⟨measurable_const, (measurable_flowField _ _).comp hm, Eventually.of_forall fun ω _ => ?_, ?_⟩
  · exact ⟨Chart.isConformal_id.recenter _, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift,
      isChartTransport_shiftChart _ _ _⟩
  · rw [pastSigma_zero]
    filter_upwards [ae_isGFFWithBoundaryData_condExpKernel_bot hw] with ω₀ h0 _
    exact h0

/-- **Two constant data words of one field law give the same code almost surely** (Theorems 1.2–1.3). -/
theorem ae_codeMatch_switch (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J') (m : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : Measurable g) {w w' : BoundaryWord}
    (hw : IsGFFWithBoundaryData μ (fun ω => flowField 0 0 (g ω)) w.fn w.jumps)
    (hw' : IsGFFWithBoundaryData μ (fun ω => flowField 0 0 (g ω)) w'.fn w'.jumps) :
    ∀ᵐ ω ∂μ, IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (w', flowField 0 0 (g ω)))
      (driverOf h12p hκ (-(Real.pi / 2)) (w, flowField 0 0 (g ω))).1
      (driverOf h12p hκ (-(Real.pi / 2)) (w, flowField 0 0 (g ω))).2 := by
  set E' : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun _ ω => driverOf h12p hκ (-(Real.pi / 2)) (w, flowField 0 0 (g ω))
    with hE'
  have hE'm : ∀ j, Measurable (E' j) := fun _ =>
    (measurable_driverOf h12p hκ _).comp (measurable_const.prodMk ((measurable_flowField 0 0).comp hg))
  have hE'r : ∀ j ω, IsRegularDriver (E' j ω) := fun _ _ => Mz.isRegularDriver_driverOf h12p hκ _ _
  have hlaunch : ∀ ω, (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m)
      (fun i => E' i ω) (0 + 1)).2.2.2.1 0 ≠ none := fun ω => by
    rw [Mn.relRun_one_launches κ b' J' m E' ω]
    exact Option.some_ne_none _
  have h𝒢 : pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) E' 0 ≤ ‹MeasurableSpace Ω› := by
    rw [pastSigma_zero]
    exact bot_le
  have hW := isStageWitness_zero_of_law (κ := κ) (b := affData 1 m b') (jumps := affJumps 1 m J')
    (spec := relLowerSpec b' J' m) (E := E') hg hw
  have hW' := isStageWitness_zero_of_law (κ := κ) (b := affData 1 m b') (jumps := affJumps 1 m J')
    (spec := relLowerSpec b' J' m) (E := E') hg hw'
  have hmain := Mx.ae_codeMatch_of_lawCode (P := μ) h12p h13 hκ (-(Real.pi / 2))
    (isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb') hE'm hE'r ⟨_, h𝒢⟩ (LocalSets.le_aeSigma _ μ) hg
    hW.1 (G := univ)
    (by
      filter_upwards [hW.2.2.2] with ω₁ h1 _
      exact h1 (hlaunch ω₁))
    (Eventually.of_forall fun ω _ =>
      ⟨mem_univ ω, Mu.isDriverCodeMatch_driverOf h12p hκ _ (w, flowField 0 0 (g ω))⟩)
    (by
      filter_upwards [KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hW.2.2.1] with ω₁ h1 _
      filter_upwards [h1] with ω hω
      exact (hω (hlaunch ω)).2.2)
    hW'
  filter_upwards [hmain] with ω h1
  exact h1 (hlaunch ω)

/-- **`R` has entered by the offset stage** when it lies on B's walk and the root is not the zero root. -/
theorem ent_relOff_of_not_zeroRoot {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {R : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : (R : ℂ) ∈ ExplState.physSet κ b J (boundaryWalkSpec b J θ true) D) (hz : ¬ Lk.ZeroRoot κ θ b J R D) :
    Mz.Ent κ θ b J R D (Lk.relOff κ θ b J R D) := by
  classical
  have hex := Lk.exists_mem_statePhysicalSet_succ hR
  have hin := (Lk.entryStage_spec κ θ b J hex).1
  by_cases hA : Lk.ArcEntry κ θ b J R D
  · have hM : Lk.MarkEntry κ θ b J R D := by
      by_contra hM
      exact hz ⟨hA, hM⟩
    have hs := (Lk.startOff_eq κ θ b J R D).1 hA
    rw [Lk.relOff_of_mark κ θ b J hM]
    exact Lk.statePhysicalSet_mono (by omega) hin
  · have hs := (Lk.startOff_eq κ θ b J R D).2 hA
    have hM : ¬ Lk.MarkEntry κ θ b J R D := fun h => hA h.1
    show (R : ℂ) ∈ _
    rw [Lk.relOff_of_not_mark κ θ b J hM, hs]
    exact hin

end InteractingSLE.Theorem14.SB.Ct
