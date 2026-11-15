/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptLandTest
import InteractingSLE.Spec.Supplement.GW2LaterMeas

/-!
# The Borel seed test of the per-outcome family

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). On the certified retained records of a good time, a rational seed
parameter `P = (δ, δ', ε, d)` with `0 < δ' < δ`, `ε, d > 0` defines the **seed test** (`seedTest`), read from the record:

1. at every rational point of the own half-disc `ℍ ∩ B(0, δ)` the inverse own Loewner map `F_r` (record driver
   `ownDrv`) lands at distance `≥ d` from the retained obstacle `retObs` (lower half-plane, real line and counterflow
   hull) — the own collar;
2. at every rational point of the chart half-disc `ℍ ∩ B(0, ε)` the own forward map of the inverse chart has modulus
   `≤ δ'` — the seed interval of the chart sits inside the collar;
3. the own left (right) force positions at the restart are `≤ −δ` (`≥ δ`) — the own word is `∓λ` on the collar.

`measurableSet_seedRecords`: the passing records form a Borel set. R48/R77 respected; nothing here replaces a source
theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.CA (cayley cayleyInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu Aux61SlitW Aux61R1C Aux61GInst Aux61GWindow17 LawUnique Aux61Marks Restart.FlowStopIdentG
universe u

variable (S : SourceSetting.{u}) (t : GoodTime S)

/-- The own driver read from a record (frozen at the restart time). -/
def ownDrv (y : SourceRecord S.nL S.nR) : ℝ → ℝ := Ito.rpath (fun r => recU t.1 r y)

/-- The own left force positions at the restart, read from a record (relative to the driver). -/
def ownVLrec (y : SourceRecord S.nL S.nR) (j : Fin S.nL) : ℝ :=
  (histState y.2 (rationalTime t.1)).2.1 j - (histState y.2 (rationalTime t.1)).1

/-- The own right force positions at the restart, read from a record (relative to the driver). -/
def ownVRrec (y : SourceRecord S.nL S.nR) (j : Fin S.nR) : ℝ :=
  (histState y.2 (rationalTime t.1)).2.2 j - (histState y.2 (rationalTime t.1)).1

/-- Rational seed parameters `(δ, δ', ε, d)` with `0 < δ' < δ` and `ε, d > 0`. -/
abbrev SeedParam := {P : ℚ × ℚ × ℚ × ℚ // 0 < P.2.1 ∧ P.2.1 < P.1 ∧ 0 < P.2.2.1 ∧ 0 < P.2.2.2}

/-- **The seed test** of a record. -/
def seedTest (P : SeedParam) (y : SourceRecord S.nL S.nR) : Prop :=
  (∀ a b : ℚ, 0 < b → ratPt a b ∈ ball (0 : ℂ) (P.1.1 : ℝ) →
    (P.1.2.2.2 : ℝ) ≤ infDist (fwdMapInv (ownDrv S t y) (rationalTime t.1) (ratPt a b))
      (retObs (rationalTime S.s) y)) ∧
  (∀ a b : ℚ, 0 < b → ratPt a b ∈ ball (0 : ℂ) (P.1.2.2.1 : ℝ) →
    ‖fwdMap (ownDrv S t y) (rationalTime t.1) (recPhys S t y (ratPt a b))‖ ≤ (P.1.2.1 : ℝ)) ∧
  (∀ j, ownVLrec S t y j ≤ -(P.1.1 : ℝ)) ∧ (∀ j, (P.1.1 : ℝ) ≤ ownVRrec S t y j)

/-- **The seed records**: certified records passing the seed test. -/
def seedRecords (P : SeedParam) : Set (SourceRecord S.nL S.nR) :=
  certifiedRecords S t ∩ {y | seedTest S t P y}

/-! ### Measurability -/

/-- The own record driver is continuous and starts at `0` on certified records. -/
theorem ownDrv_facts {y : SourceRecord S.nL S.nR} (hy : y ∈ certifiedRecords S t) :
    Continuous (fun r => recU t.1 r y) ∧ recU t.1 0 y = 0 ∧
      IsLoewnerTrace (ownDrv S t y) (recη t.1 y) := by
  have hg : y ∈ goodSet (rationalTime S.s) t.1 := hy.1.2
  obtain ⟨-, hc, h0, htr, -⟩ := hg.1.facts
  exact ⟨hc, h0, htr⟩

theorem measurable_ownDrv_apply (r : ℝ≥0) :
    Measurable (fun y : certifiedRecords S t => recU t.1 r y.1) :=
  (measurable_frozenDrv (rationalTime t.1) r).comp (measurable_snd.comp measurable_subtype_coe)

/-- The inverse own Loewner map at a fixed upper point is measurable on the certified records. -/
theorem measurable_ownInv_cert {z : ℂ} (hz : z ∈ H) :
    Measurable (fun y : certifiedRecords S t => fwdMapInv (ownDrv S t y.1) (rationalTime t.1) z) :=
  Theorem14.GW2Later.measurable_fwdMapInv_apply (B := fun r (y : certifiedRecords S t) => recU t.1 r y.1)
    (measurable_ownDrv_apply S t) (fun y => (ownDrv_facts S t y.2).1) (fun y => (ownDrv_facts S t y.2).2.1)
    (NNReal.coe_nonneg _) ⟨z, hz⟩

/-- The own forward map at a measurable point is measurable on the certified records. -/
theorem measurable_ownFwd_cert {u : certifiedRecords S t → ℂ} (hu : Measurable u) :
    Measurable (fun y : certifiedRecords S t => fwdMap (ownDrv S t y.1) (rationalTime t.1) (u y)) := by
  refine (Exist.StagedLaw.measurable_fwdMap_param (W := fun y : certifiedRecords S t => ownDrv S t y.1)
    (fun y => (ownDrv_facts S t y.2).1.comp continuous_real_toNNReal)
    (fun r => measurable_ownDrv_apply S t r.toNNReal)
    (fun y => by simpa [ownDrv, Ito.rpath] using (ownDrv_facts S t y.2).2.1)
    (τ := fun _ => ((rationalTime t.1 : ℝ≥0) : ℝ)) measurable_const
    (fun _ => NNReal.coe_nonneg _) hu).1

theorem measurable_ownVLrec (j : Fin S.nL) : Measurable (fun y : SourceRecord S.nL S.nR => ownVLrec S t y j) := by
  have h : Measurable (fun y : SourceRecord S.nL S.nR => histState y.2 (rationalTime t.1)) :=
    (measurable_histState (nL := S.nL) (nR := S.nR) (rationalTime t.1)).comp measurable_snd
  exact ((measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp h))).sub
    (measurable_fst.comp h)

theorem measurable_ownVRrec (j : Fin S.nR) : Measurable (fun y : SourceRecord S.nL S.nR => ownVRrec S t y j) := by
  have h : Measurable (fun y : SourceRecord S.nL S.nR => histState y.2 (rationalTime t.1)) :=
    (measurable_histState (nL := S.nL) (nR := S.nR) (rationalTime t.1)).comp measurable_snd
  exact ((measurable_pi_apply j).comp (measurable_snd.comp (measurable_snd.comp h))).sub
    (measurable_fst.comp h)

/-- **The seed records are Borel.** -/
theorem measurableSet_seedRecords (P : SeedParam) : MeasurableSet (seedRecords S t P) := by
  have hset : MeasurableSet {y : certifiedRecords S t | seedTest S t P y.1} := by
    simp only [seedTest, ofPred_and, ofPred_forall]
    refine (MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => MeasurableSet.iInter fun hb =>
      MeasurableSet.iInter fun _ => ?_).inter ((MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      MeasurableSet.iInter fun hb => MeasurableSet.iInter fun _ => ?_).inter
      ((MeasurableSet.iInter fun j => ?_).inter (MeasurableSet.iInter fun j => ?_)))
    · have hz : ratPt a b ∈ H := by
        change (0 : ℝ) < (ratPt a b).im
        simp only [ratPt]
        exact_mod_cast hb
      exact measurableSet_le measurable_const
        (measurable_comp_of_continuous_of_measurable
          (u := fun z' (y : certifiedRecords S t) => infDist z' (retObs (rationalTime S.s) y.1))
          (fun _ => continuous_infDist_pt _)
          (fun z' => (measurable_infDist_retObs (rationalTime S.s) z').comp measurable_subtype_coe)
          (measurable_ownInv_cert S t hz))
    · exact measurableSet_le (measurable_ownFwd_cert S t
        (measurable_recPhys_cert S t (ratPt_mem_Hbar (a := a) hb))).norm measurable_const
    · exact measurableSet_le ((measurable_ownVLrec S t j).comp measurable_subtype_coe) measurable_const
    · exact measurableSet_le measurable_const ((measurable_ownVRrec S t j).comp measurable_subtype_coe)
  have himg : seedRecords S t P = Subtype.val '' {y : certifiedRecords S t | seedTest S t P y.1} := by
    ext y
    constructor
    · rintro ⟨hy, hT⟩
      exact ⟨⟨y, hy⟩, hT, rfl⟩
    · rintro ⟨y', hT, rfl⟩
      exact ⟨y'.2, hT⟩
  rw [himg]
  exact (measurableSet_certifiedRecords S t).subtype_image hset

end InteractingSLE.Sec5.Aux61Cpt
