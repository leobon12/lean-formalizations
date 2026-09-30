import QuantumZipper.Proofs.Zipper.Cor15FieldGoodNoGo
import QuantumZipper.Proofs.Zipper.Cor15ZipFixLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-FIELDGOOD: the corrected field good-set node and the rewired Corollary 1.5 headline

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
no proof in the paper). Task COR15-FIELDGOOD.

`Cor15UnzipZipFieldGoodStmt` is false as stated (`Cor15FieldGoodNoGo.ae_avgReg_const_of_fieldGood`:
it forces the unzipped field to have constant regularized averages), because a measurable set of
B1-FULL data cannot see continuity of the driver `x.2`, and `D_a` is junk when the zipped driver
is discontinuous right after time `a`. The corrected node only asks for the round trip at
configurations with a **continuous** driver:

* `Cor15UnzipZipFieldGoodStmt'` (weaker than the old node: `cor15UnzipZipFieldGoodStmt'_of_old`);
* `Cor15UnzipZipGoodStmt'`, `cor15UnzipZipGoodStmt'_of_fieldGood'`: the driver half is discharged
  exactly as in `cor15UnzipZipGoodStmt_of_fieldGood` (`Cor15UnzipZipSelfDrive`);
* `cor15UnzipZipSelfStmt_of_good'`: the B1-FULL transfer of `cor15UnzipZipSelfStmt_of_good`
  (`Cor15UnzipZipSelfGood`), using that the genuine driver `√κ B` is a.s. continuous;
* `theorem1_5_of_theorem1_3_of_zipFixRead''`: the D42 headline
  `theorem1_5_of_theorem1_3_of_zipFixRead'` with the corrected node.

Own bookkeeping (copies of the cited proofs with the continuity hypothesis threaded through).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Corrected field good-set node.** As `Cor15UnzipZipFieldGoodStmt`, but the deterministic
round trip is only required at configurations `x` whose driver `x.2` is continuous. -/
def Cor15UnzipZipFieldGoodStmt' (κ a : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) : Prop :=
  ∃ A : Set B1E, MeasurableSet A ∧
    (∀ x : FieldSample × (ℝ → ℝ), Continuous x.2 → b1Data x ∈ A →
      RegEq (zipCapDown (Real.sqrt κ) a (zipCapUp (Real.sqrt κ) a x)).1 x.1) ∧
    ∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) ∈ A

/-- Corrected good-set node for the whole round trip. -/
def Cor15UnzipZipGoodStmt' (κ a : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∃ A : Set B1E, MeasurableSet A ∧
    (∀ x : FieldSample × (ℝ → ℝ), Continuous x.2 → b1Data x ∈ A →
      UnzipZipHolds (Real.sqrt κ) a x) ∧
    ∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω)) ∈ A

/-- The corrected good-set node from its field half (proof of
`cor15UnzipZipGoodStmt_of_fieldGood`, with the continuity hypothesis carried along). -/
theorem cor15UnzipZipGoodStmt'_of_fieldGood' (h13 : theorem1_3)
    (hRSS : Blueprint.RohdeSchrammSimple) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {a : ℝ} (ha : 0 < a) (hfield : Cor15UnzipZipFieldGoodStmt' κ a P B X) :
    Cor15UnzipZipGoodStmt' κ a P B X := by
  obtain ⟨A₁, hA₁, hdec₁, hyA₁⟩ := hfield
  obtain ⟨F, hFm, A₂, hA₂, hEq, hyA₂⟩ := cor15WeldRead h13 hRSS hκ hκ4 hB hX hind ha
  set A₃ : Set B1E := A₂ ∩ {d | F d 0 = 0 ∧ (d.2 0 : ℝ) = 0} with hA₃
  have hmF : Measurable fun d : B1E => F d 0 := (measurable_pi_apply (0 : ℝ)).comp hFm
  have hmD : Measurable fun d : B1E => (d.2 0 : ℝ) :=
    (measurable_pi_apply (0 : ℝ≥0)).comp measurable_snd
  have hA₃m : MeasurableSet A₃ := hA₂.inter
    ((measurableSet_eq_fun hmF measurable_const).inter
      (measurableSet_eq_fun hmD measurable_const))
  have hw0 : ∀ᵐ ω ∂P, F (b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) 0 = 0 := by
    filter_upwards [ae_eqOn_weldDriver_zipCapDown h13 hRSS hκ hκ4 P B X hB hX hind ha,
      hyA₂] with ω hEqOn hω
    have hr : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
    rw [← hEq _ hω hr, hEqOn hr, B2.vrev_zero ha.le]
  refine ⟨A₁ ∩ A₃, hA₁.inter hA₃m, ?_, ?_⟩
  · intro x hxc hx
    simp only [Set.mem_inter_iff, hA₃, Set.mem_ofPred_eq] at hx
    obtain ⟨hx₁, hx₂, hxF0, hx0⟩ := hx
    have hW0 : weldDriver (Real.sqrt κ) x.1 a 0 = 0 := by
      rw [hEq x hx₂ (by simp only [mem_Icc]; exact ⟨le_rfl, ha.le⟩)]
      exact hxF0
    have hx00 : x.2 0 = 0 := by simpa only [b1Data, NNReal.coe_zero] using hx0
    exact (unzipZipHolds_iff_regEq (γ := Real.sqrt κ) ha.le hW0 hx00).2 (hdec₁ x hxc hx₁)
  · filter_upwards [hyA₁, hyA₂, hw0, b1Data_zipCapDown_snd_zero_ae (κ := κ) (a := a) (B := B)]
      with ω h₁ h₂ h₃ h₄
    exact ⟨h₁, ⟨h₂, h₃, h₄⟩⟩

/-- **`Cor15UnzipZipSelfStmt` from the corrected good-set node** (proof of
`cor15UnzipZipSelfStmt_of_good`; the genuine driver is a.s. continuous). -/
theorem cor15UnzipZipSelfStmt_of_good'
    (hgood : ∀ κ : ℝ, 0 < κ → κ < 4 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
      ∀ a : ℝ, 0 < a → Cor15UnzipZipGoodStmt' κ a P B X) :
    Cor15UnzipZipSelfStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hS a ha
  obtain ⟨A, hA, hdec, hyA⟩ := hgood κ hκ hκ4 P B X hS a ha
  have hlaw : P.map (fun ω => b1Data (grpCfg κ B X ω)) =
      P.map (fun ω => b1Data (zipCapDown (Real.sqrt κ) a (grpCfg κ B X ω))) :=
    (b1_full_data (κ := κ) (B := B) (X := X) hκ hS.1 hS.2.1 hS.2.2 ha).symm
  have hAc : ∀ᵐ ω ∂P, b1Data (grpCfg κ B X ω) ∈ A :=
    ae_mem_of_map_eq (e := b1Data) hA (aemeasurable_b1Data_c κ hS.1 hS.2.1)
      (aemeasurable_b1Data_unzip κ hκ hS.1 hS.2.1 hS.2.2 ha) hlaw hyA
  filter_upwards [hAc, hS.1.cont] with ω hω hc
  exact hdec (grpCfg κ B X ω) (drive_continuous hc) hω

/-- `Cor15UnzipZipSelfStmt` from the corrected field node, for every genuine setup. -/
theorem cor15UnzipZipSelfStmt_of_fieldGood' (h13 : theorem1_3)
    (hRSS : Blueprint.RohdeSchrammSimple)
    (hfield : ∀ κ : ℝ, 0 < κ → κ < 4 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
      ∀ a : ℝ, 0 < a → Cor15UnzipZipFieldGoodStmt' κ a P B X) :
    Cor15UnzipZipSelfStmt :=
  cor15UnzipZipSelfStmt_of_good' fun κ hκ hκ4 _ _ P _ B X hS a ha =>
    cor15UnzipZipGoodStmt'_of_fieldGood' h13 hRSS hκ hκ4 hS.1 hS.2.1 hS.2.2 ha
      (hfield κ hκ hκ4 P B X hS a ha)

/-- **Corollary 1.5 (D42 headline, corrected field node)**: as
`theorem1_5_of_theorem1_3_of_zipFixRead'`, with `Cor15UnzipZipFieldGoodStmt'` in place of the
false `Cor15UnzipZipFieldGoodStmt`. -/
theorem theorem1_5_of_theorem1_3_of_zipFixRead'' (h13 : theorem1_3) (hSG : Cor15ShiftGoodStmt)
    (hfield : ∀ κ : ℝ, 0 < κ → κ < 4 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
      ∀ a : ℝ, 0 < a → Cor15UnzipZipFieldGoodStmt' κ a P B X)
    (hR : ∀ κ : ℝ, 0 < κ → κ < 4 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
      ∀ a : ℝ, 0 < a → Cor15ZipCoordReadStmt κ a P B X) : theorem1_5 :=
  theorem1_5_of_theorem1_3_of_genuine' h13 hSG
    ⟨cor15MarkovStmt_holds,
      cor15ZipOntoStmt'_of hSG
        (cor15UnzipZipSelfStmt_of_fieldGood' h13 RS.rohdeSchrammSimple hfield)
        (cor15ZipGenuineStmt'_of_version' h13
          (cor15ZipVersionStmt'_of_coordLaw h13 freeCircleReconStmt_holds
            (cor15ZipCoordLawStmt'_of_read h13 hR) (cor15ZipRawConvStmt_of_read h13 hR)))⟩

end Cor15Group
end QuantumZipper
