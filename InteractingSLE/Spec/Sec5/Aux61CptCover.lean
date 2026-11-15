/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptFamily
import InteractingSLE.Spec.Sec5.Aux61NjCompare
import InteractingSLE.Spec.Sec5.Aux61GWindow19Windows

/-!
# The fibre cover from R103's per-outcome family

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). For the family `cptChoices S`:

* `cptAccess`: almost surely on every selected record, every point of `O₀` is an own collar point (seed interval) or
  a counterflow access (landing interval), in NOJUMP's pinch-free forms — PROVED with no input.
* `cptAdmission S`: GLUEINST's initial-record admission for this family (the exact `hAdmission` argument of
  `SeedPlacement.completed_cover_of_admission`), named here.
* `dyCover_of_cptAdmission`: the fibre leaf `DyActFibreCoverOn (¬ IsLargeGap) RefWin` from `cptAdmission` alone, through
  NOJUMP's `dyCover_of_finiteRestrict_capture_access` with GLUEINST's window data and capture.

Conditional helper with a distinct name: `cptAdmission` is the one remaining input (GLUEINST's packet).
R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Aux61Cmp LawUnique Aux61Restart
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61R1C Aux61Asm2 Aux61SlitWX Aux61GWindow17
open Aux61GR1F Aux61GInst Aux61FibData Aux61GWindow19 Aux61WndCap
universe u

variable (S : SourceSetting.{u})

/-- The finite-buffer restriction of the family. -/
abbrev cptFinite : RestartChoices S := Aux61SlitWAC.restrictChoices (cptChoices S) (finiteRestrict (cptChoices S))

/-- The family's window data (GLUEINST). -/
abbrev cptWindows : WindowData (finiteRestart (cptChoices S)) (cptFinite S).hasChart :=
  localizedRealWindows S _ _ _ _ _ _ _

/-- The family's reader facts. -/
abbrev cptReaders : ReaderFacts (cptFinite S).toR1Restart :=
  Aux61SlitWZ.readers _ (selected_measurable_finiteRestrict (cptChoices S) (cptChoices_selected_measurable S))

/-- **The access hypothesis on the whole comparison set**, almost surely on every selected record. -/
theorem cptAccess : ∀ i, ∀ᵐ p ∂S.μ,
    (S.marksData (normSource (finiteRestart (cptChoices S)) (cptFinite S).hasChart)).Z i p ∈
      (S.marksData (normSource (finiteRestart (cptChoices S)) (cptFinite S).hasChart)).B i →
    ∀ b ∈ ((S.marksData (normSource (finiteRestart (cptChoices S)) (cptFinite S).hasChart)).data i).O₀,
      Aux61Nj.OwnCollarPointNP S (normSource (finiteRestart (cptChoices S)) (cptFinite S).hasChart) i p b ∨
        Aux61Nj.CfAccessNP S (normSource (finiteRestart (cptChoices S)) (cptFinite S).hasChart) i p b := by
  intro i
  set k : CptIndex S := i.1 with hk
  have hTip := Aux61SlitWY.ownTipForwardLimit S
  have hExit := physicalExit_finiteRestrict (cptChoices S) (cptChoices_selected_measurable S)
  have ht : idxTime (cptFinite S) i = k.1.1 := Subtype.ext rfl
  have hsel : ∀ y ∈ (normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).selected i,
      y ∈ cptTests S k := fun y hy => hy.1.1.2
  have hL : ∀ y ∈ (normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).selected i,
      y ∈ landRecords S (idxTime (cptFinite S) i) k.1.2.2.1 := fun y hy => by
    rw [ht]; exact (hsel y hy).1
  have hP : ∀ y ∈ (normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).selected i,
      y ∈ seedRecords S (idxTime (cptFinite S) i) k.1.2.2.2 := fun y hy => by
    rw [ht]; exact (hsel y hy).2
  have hbR : ((normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).data i).bR = (cptWord S k).boundary :=
    rfl
  have hJR : ((normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).data i).JR = (cptWord S k).jumps := rfl
  have hwordL : ∀ b : ℝ, |b - k.1.2.2.1.1.1| < k.1.2.2.1.1.2.1 →
      ((normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).data i).bR b = Aux61Nj.eastHeight S 1 :=
    fun b hb => by rw [hbR]; exact cptWord_land S k (mem_landInterval_iff.2 hb)
  have hwordS : ∀ b : ℝ, |b| < k.1.2.2.2.1.2.2.1 → b ≠ 0 →
      b ∉ ((normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).data i).JR ∧
      ((normSource (cptFinite S).toR1Restart (cptFinite S).hasChart).data i).bR b =
        if b < 0 then -sleLambda S.κ else sleLambda S.κ := by
    intro b hb hb0
    refine ⟨?_, by rw [hbR]; exact cptWord_seed S k hb⟩
    rw [hJR, cptWord_jumps]
    have h1 := seedRad_pos k.1.2.2.2
    have h2 := landLo_lt_landHi k.1.2.2.1
    have hb' : |b| < seedRad k.1.2.2.2 := hb
    rw [abs_lt] at hb'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    rcases k.2.1 with h' | h'
    · exact ⟨by linarith, by linarith, hb0⟩
    · exact ⟨by linarith, by linarith, hb0⟩
  filter_upwards [ae_ownCollarPointNP_of_seedRecords (cptFinite S) (cptReaders S) hTip (cptWindows S) hExit
      i k.1.2.2.2 hP hwordS,
    ae_cfAccessNP_of_landRecords (cptFinite S) (cptReaders S) hTip (cptWindows S) hExit i k.1.2.2.1 hL hwordL]
    with p hown hcf hB b hb
  rcases hb with hb | hb
  · left
    exact hown hB b (abs_lt.2 hb)
  · right
    have h1 := seedRad_pos k.1.2.2.2
    refine hcf hB b (mem_landInterval_iff.1 hb) ?_ ?_
    · rintro rfl
      rcases k.2.1 with h' | h'
      · linarith [hb.1]
      · linarith [hb.2]
    · rw [hJR, cptWord_jumps]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hb.1.ne', hb.2.ne, ?_⟩
      rintro rfl
      rcases k.2.1 with h' | h'
      · linarith [hb.1]
      · linarith [hb.2]

/-- **The initial-record admission for the family** (GLUEINST's `hAdmission`, PROVE-AUX61-GLUEINST): at a sample of
the window event, for the source's retained time and the capture's chart landing `y`, a real neighbourhood `O` of
`0` and `y` such that every thin window admitting the record whose closed buffer meets `ℝ` in `O` is installed by
some index of the family whose selected set contains the record and whose landing interval contains `y`. -/
def CptAdmission : Prop :=
  ∀ᵐ p ∂S.μ, S.windowEvent p →
    ∀ t : GoodTime S, t.1 = S.t → ∀ y : ℝ, y ≠ 0 →
    Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) →
    ∃ O : Set ℝ, IsOpen O ∧ 0 ∈ O ∧ y ∈ O ∧
      ∀ J : AllowedWindow,
        timeRecord S t p ∈ windowRecords S t J →
        (∀ z ∈ closure (outerBuffer J.1.1), z.im = 0 → z.re ∈ O) →
        ∃ i : (cptChoices S).Idx, (cptChoices S).q i.1 = t.1 ∧
          (cptChoices S).record i.1 p ∈ (cptChoices S).toR1Restart.selected i ∧
          bufferedWindow J.1.1 ⊆ ((cptChoices S).data i.1).V ∧
          y ∈ Ioo ((cptChoices S).left i.1) ((cptChoices S).right i.1)

/-- **The fibre leaf from the family's admission.** -/
theorem dyCover_of_cptAdmission (hAdm : ∀ S : SourceSetting.{u}, CptAdmission S) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  Aux61Nj.dyCover_of_finiteRestrict_capture_access cptChoices cptChoices_selected_measurable
    cptWindows (fun S i => (cptSeed S i).1) (fun S i => (cptSeed S i).2) cptAccess
    (fun S => (localizedRealPlacement S _ _ _ _ _ _ _).completed_cover_of_admission
      (cptChoices_selected_measurable S) (localizedReal_window_fields S _ _ _ _ _ _ _) (hAdm S))

end InteractingSLE.Sec5.Aux61Cpt
