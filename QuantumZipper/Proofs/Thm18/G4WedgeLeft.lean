import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.F1B4dPath
import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.LQG.WedgeBdryInfB4
import QuantumZipper.Proofs.LQG.AllOffsets
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.Section5.Prop17RawLaw

/-!
# G4-WEDGE (1): infinite boundary length of a wedge on `(−∞, 0]`

`WedgeLeftInfStmt` (G4): for the `(γ − 2/γ)`-wedge `Y`, a.s. `ν_Y(−∞,0] = ∞` (Sheffield,
arXiv:1012.4797, §1.6, p. 21: a wedge has "an infinite amount [of boundary length] in each
neighborhood of ∞"). The right-side statement `ν_Y[0,∞) = ∞` is proved in `WedgeBdryInf*`; the
left side follows by the reflection `z ↦ −z̄` (own elementary argument):

1. For the reference field `W = h† + Q(−log|·|) + A_{−log|·|}` built from a free field `X`, let
   `Wσ` be the same field built from the reflected free field `X(−·̄)` (same `A`). The dyadic
   coordinates of `Wσ` and `W` have the same law (`F1.B4d.map_coords_wedgeField_reflect`), so the
   right-side event `ν[0,∞) = ∞` (with goodness) transfers from `W` to `Wσ`.
2. Given `F1.WedgeLatReflRegStmt γ α` (`avgReg Wσ = avgReg (W(−·̄))` a.s.; open input (i) of B4(d),
   being proved by task WEDGE-CREG), `ν_{Wσ} = ν_{W(−·̄)} = (−·)_* ν_W`
   (`AllOffsets.qBoundaryMeasure_reflectH`), hence `ν_W(−∞,0] = ν_{Wσ}[0,∞) = ∞`.
3. Canonicalization (rescaling by `scaleParam > 0`) preserves `ν(−∞,0] = ∞`, and the event
   transfers to every quantum wedge through `fieldLawFull` (`WedgeBdry.ae_of_fieldLawFull_eq`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- Infinite boundary mass on `(−∞,0]`, with goodness. -/
def InfMassLeftGood (γ : ℝ) (x : FieldSample) : Prop :=
  qBoundaryMeasure γ x (Iic (0 : ℝ)) = ⊤ ∧ IsLQGGood γ x

theorem measurableSet_infMassLeftGood (γ : ℝ) :
    MeasurableSet {x : FieldSample | InfMassLeftGood γ x} := by
  classical
  set g : FieldSample → Measure ℝ :=
    fun x => if IsLQGGood γ x then qBoundaryMeasure γ x else 0 with hg_def
  have hg : Measurable g := GoodMeas.measurable_qBoundaryMeasure_global γ
  have hcomp : Measurable fun x : FieldSample => (g x) (Iic (0 : ℝ)) :=
    (Measure.measurable_coe measurableSet_Iic).comp hg
  have he : {x : FieldSample | InfMassLeftGood γ x} = {x | IsLQGGood γ x} ∩
      {x | (g x) (Iic (0 : ℝ)) = ⊤} := by
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, InfMassLeftGood]
    constructor
    · rintro ⟨hI, hG⟩
      exact ⟨hG, by simpa only [hg_def, if_pos hG] using hI⟩
    · rintro ⟨hG, hI⟩
      exact ⟨by simpa only [hg_def, if_pos hG] using hI, hG⟩
  rw [he]
  exact (GoodMeas.measurableSet_isLQGGood γ).inter (hcomp (measurableSet_singleton ⊤))

theorem infMassLeftGood_reconstruct (γ : ℝ) (x : FieldSample) :
    InfMassLeftGood γ (Factorization.reconstruct (Factorization.coords x)) ↔
      InfMassLeftGood γ x := by
  simp only [InfMassLeftGood, WedgeBdry.qBoundaryMeasure_reconstruct,
    GoodSample.isLQGGood_iff_reconstruct]

/-- Rescaling by `a > 0` preserves `ν(−∞,0] = ∞`. -/
theorem infMassLeft_rescale {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsLQGGood γ x)
    {a : ℝ} (ha : 0 < a) (h : qBoundaryMeasure γ x (Iic (0 : ℝ)) = ⊤) :
    qBoundaryMeasure γ (rescale x (Qc γ) a) (Iic (0 : ℝ)) = ⊤ := by
  have hm : Measurable fun u : ℝ => u / a := measurable_id.div_const a
  rw [GoodTransforms.qBoundaryMeasure_rescale hx hγ ha, Measure.map_apply hm measurableSet_Iic]
  have e : (fun u : ℝ => u / a) ⁻¹' Iic (0 : ℝ) = Iic (0 : ℝ) := by
    ext u
    simp only [mem_preimage, mem_Iic, div_nonpos_iff]
    constructor
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · linarith
      · exact h1
    · intro h; exact Or.inr ⟨h, ha.le⟩
  rw [e, h]

section Ref

variable {γ α : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}

/-- Step 1: the reference field built from the reflected free field has infinite boundary mass
on `[0,∞)`. -/
theorem ae_infMassGood_wedgeField_reflect (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess α (Qc γ) A P')
    (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', WedgeBdry.InfMassGood γ
      (wedgeField (lateralPart (RegClosure.reflectH (X ω))) (fun t => A t ω) (Qc γ)) := by
  obtain ⟨α'', hαα'', hα''Q⟩ : ∃ α'' : ℝ, α < α'' ∧ α'' < Qc γ :=
    ⟨(α + Qc γ) / 2, by linarith, by linarith⟩
  set S : Set (ℕ → ℝ) := {c | WedgeBdry.InfMassGood γ (Factorization.reconstruct c)} with hS
  have hSm : MeasurableSet S :=
    Factorization.measurable_reconstruct (WedgeBdry.measurableSet_infMassGood γ)
  have hWm : AEMeasurable (fun ω =>
      Factorization.coords (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) P' :=
    ((F1.B4d.measurable_coordsW (Qc γ)).comp_aemeasurable
      ((F1.B4d.measurable_latId.comp (WedgeTK.measurable_X_pi hX)).aemeasurable.prodMk
        (ZoomRadial.aemeasurable_wedgePath hA))).congr
      (F1.B4d.coords_wedgeField_ae_eq hA).symm
  have hσm := F1.B4d.aemeasurable_coords_wedgeField_reflect hX hA
  have hW : ∀ᵐ ω ∂P', Factorization.coords
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) ∈ S := by
    filter_upwards [WedgeBdry.ae_qBoundaryMeasure_Ici_top_wedgeField
        WedgeBdry.wedgeBdryFreeInfStmt_holds hγ hγ2 hαα'' hα''Q Ω' P' X A inferInstance hX hA hI,
      WedgeBdry.ae_bReg_wedgeField hγ hγ2 hα hX hA hI] with ω h1 h2
    show WedgeBdry.InfMassGood γ (Factorization.reconstruct (Factorization.coords _))
    rw [WedgeBdry.infMassGood_reconstruct]
    exact ⟨h1, h2.1⟩
  have h1 := (ae_map_iff hWm hSm).2 hW
  rw [← F1.B4d.map_coords_wedgeField_reflect hX hA hI] at h1
  filter_upwards [(ae_map_iff hσm hSm).1 h1] with ω hω
  exact (WedgeBdry.infMassGood_reconstruct γ _).1 hω

/-- Step 2: the reference field has infinite boundary mass on `(−∞,0]`, given
`F1.WedgeLatReflRegStmt`. -/
theorem ae_infMassLeftGood_wedgeField (hreg : F1.WedgeLatReflRegStmt γ α) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hα : α < Qc γ) (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', InfMassLeftGood γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) := by
  filter_upwards [ae_infMassGood_wedgeField_reflect hγ hγ2 hα hX hA hI,
    hreg Ω' P' X A inferInstance hX hA hI, WedgeBdry.ae_bReg_wedgeField hγ hγ2 hα hX hA hI]
    with ω hσ hr hb
  refine ⟨?_, hb.1⟩
  have hreq : RegEq (wedgeField (lateralPart (RegClosure.reflectH (X ω))) (fun t => A t ω) (Qc γ))
      (RegClosure.reflectH (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) :=
    fun k z => congrFun (congrFun hr k) z
  have hν := F1.qBoundaryMeasure_congr_regEq hreq γ
  rw [AllOffsets.qBoundaryMeasure_reflectH hb.1] at hν
  have h := hσ.1
  rw [WedgeBdry.InfMassIci, hν, Measure.map_apply measurable_neg measurableSet_Ici] at h
  have e : (fun s : ℝ => -s) ⁻¹' Ici (0 : ℝ) = Iic (0 : ℝ) := by
    ext s; simp
  rwa [e] at h

end Ref

/-- **Infinite boundary mass on `(−∞,0]` for every quantum wedge** (`α < Q`), given the
reflection identity `F1.WedgeLatReflRegStmt γ α`. -/
theorem ae_qBoundaryMeasure_Iic_top_of_isQuantumWedge {γ α : ℝ}
    (hreg : F1.WedgeLatReflRegStmt γ α) (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → FieldSample}
    (hW : IsQuantumWedge γ α Y P) : ∀ᵐ ω ∂P, qBoundaryMeasure γ (Y ω) (Iic 0) = ⊤ := by
  have hY := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  have hZW : IsQuantumWedge γ α (S5.FieldLaw.Raw.refField γ X A) P' :=
    ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  have hZ := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hZW
  have href : ∀ᵐ ω ∂P', InfMassLeftGood γ (S5.FieldLaw.Raw.refField γ X A ω) := by
    filter_upwards [ae_infMassLeftGood_wedgeField hreg hγ hγ2 hα hX hA hI,
      Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI] with ω h hs
    exact ⟨infMassLeft_rescale hγ h.2 hs.1 h.1, hs.2.1⟩
  filter_upwards [WedgeBdry.ae_of_fieldLawFull_eq hlaw hY hZ (InfMassLeftGood γ)
    (measurableSet_infMassLeftGood γ) (infMassLeftGood_reconstruct γ) href] with ω hω
  exact hω.1

/-- **`WedgeLeftInfStmt`**, given the reflection identity `F1.WedgeLatReflRegStmt γ (γ − 2/γ)`
(open input (i) of B4(d), task WEDGE-CREG). -/
theorem wedgeLeftInfStmt_of_latRefl
    (hreg : ∀ γ : ℝ, 0 < γ → γ < 2 → F1.WedgeLatReflRegStmt γ (γ - 2 / γ)) :
    WedgeLeftInfStmt := by
  intro γ Ω _ P _ Y hγ hγ2 hW
  exact ae_qBoundaryMeasure_Iic_top_of_isQuantumWedge (hreg γ hγ hγ2) hγ hγ2 hW

end Thm18Asm
end QuantumZipper
