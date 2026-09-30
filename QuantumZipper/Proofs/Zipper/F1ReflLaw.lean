import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.LQG.WedgeMeasurable
import Mathlib.Probability.BrownianMotion.Basic

/-!
# F1d input (c): reflection invariance of `P_*` at the level of `configLawFull`

Theorem 1.3, node F1d (Sheffield, arXiv:1012.4797, §5.4 p. 72: "by symmetry"). The law `P_*` of
the configuration `(Y, √κ B)` (wedge field `Y`, independent Brownian motion `B`) is invariant
under the reflection `reflectConfig : (h, W) ↦ (h(−·̄), −W)`.

* `reflectH_eq_reconstruct`, `dataFull_reflectH_eq`, `measurable_reflData`: the data
  `configLawFull` reads from `reflectH x` is a measurable function (`reflData`) of the circle
  coordinates `coordsFull x` alone (exactly, for every `x`, no regularity needed).
* `map_pathOf_neg`: `−B` has the path law of `B` (finite-dimensional laws, mathlib
  `IsPreBrownianReal.neg`, and uniqueness of projective limits).
* `configLawFull_reflect_of_field`: independence of `Y` and `B` reduces the configuration
  statement to the field statement `law(dataFull (reflectH Y)) = law(dataFull Y)`.
* `map_dataFull_reflectH_transfer`: the field statement transfers along equality of
  `fieldLawFull` (so it suffices to prove it for the reference field of `IsQuantumWedge`).
* `WedgeRefReflectStmt` (B4(d), the reflection invariance of the reference wedge field) and
  `configLawFull_reflect_of_wedge` (input (c) conditional on it).

All arguments are own elementary arguments (the paper only says "by symmetry").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace F1

open CoordsFull

/-! ## 1. The reflected data is a measurable function of the circle coordinates -/

/-- The data read by `configLawFull` (and `fieldLawFull H`) from a field sample. -/
abbrev dataH (x : FieldSample) : (ℕ → ℝ) × (TestFun H → ℝ) := WedgeMeas.dataFull H x

theorem measurable_dataH_of {β : Type*} [MeasurableSpace β] {g : β → FieldSample}
    (hg : ∀ μ : Measure ℂ, SFinite μ → Measurable fun b => g b μ) :
    Measurable fun b => dataH (g b) :=
  (measurable_pi_iff.2 fun _ => hg _ inferInstance).prodMk
    (measurable_pi_iff.2 fun _ => (hg _ inferInstance).sub (hg _ inferInstance))

theorem measurable_dataH : Measurable dataH :=
  measurable_dataH_of (g := id) fun μ _ => measurable_pi_apply μ

/-- `reflectH` only reads the circle coordinates. -/
theorem reflectH_eq_reconstruct (x : FieldSample) :
    RegClosure.reflectH x =
      RegClosure.reflectH (Factorization.reconstruct (WedgeCan4.piC (coordsFull x))) := by
  funext μ
  simp only [RegClosure.reflectH, WedgeCan4.piC_coordsFull]
  rw [Factorization.evalReg_congr (Factorization.avgReg_reconstruct_coords x)]

/-- The data of the reflected field, as a function of the circle coordinates. -/
def reflData (c : ℕ → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  dataH (RegClosure.reflectH (Factorization.reconstruct (WedgeCan4.piC c)))

theorem measurable_reflData : Measurable reflData :=
  measurable_dataH_of fun _ _ => (measurable_evalReg _).comp
    (Factorization.measurable_reconstruct.comp WedgeCan4.measurable_piC)

theorem dataFull_reflectH_eq (x : FieldSample) :
    dataH (RegClosure.reflectH x) = reflData (dataH x).1 := by
  simp only [reflData, dataH, WedgeMeas.dataFull]
  rw [← reflectH_eq_reconstruct]

theorem measurable_dataH_reflectH : Measurable fun x => dataH (RegClosure.reflectH x) := by
  have : (fun x => dataH (RegClosure.reflectH x)) = fun x => reflData (dataH x).1 :=
    funext dataFull_reflectH_eq
  rw [this]
  exact measurable_reflData.comp (measurable_fst.comp measurable_dataH)

/-! ## 2. The path law of `−B` -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two pre-Brownian motions with a.e.-measurable paths have the same path law (on
`ℝ≥0 → ℝ` with the product σ-algebra): uniqueness of projective limits. -/
theorem map_pathOf_eq_of_isPreBrownianReal {B C : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hC : IsPreBrownianReal C P) (hBm : AEMeasurable (pathOf B) P)
    (hCm : AEMeasurable (pathOf C) P) : P.map (pathOf B) = P.map (pathOf C) := by
  have key : ∀ {D : ℝ≥0 → Ω → ℝ}, IsPreBrownianReal D P → AEMeasurable (pathOf D) P →
      IsProjectiveLimit (P.map (pathOf D)) BrownianReal.projectiveFamily := by
    intro D hD hDm I
    rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict I).aemeasurable hDm]
    exact (hD.hasLaw I).map_eq
  exact (key hB hBm).unique (key hC hCm)

/-! ## 3. Independence reduces (c) to the field statement -/

/-- The driver on `[0,∞)` read by `configLawFull`, as a function of the Brownian path. -/
def drivePath (κ : ℝ) (p : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => Real.sqrt κ * p t

theorem measurable_drivePath (κ : ℝ) : Measurable (drivePath κ) :=
  measurable_pi_iff.2 fun t => (measurable_pi_apply t).const_mul _

omit [MeasurableSpace Ω] in
theorem drive_nnreal (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (fun t : ℝ≥0 => drive κ B ω t) = drivePath κ (pathOf B ω) := by
  funext t
  simp [drive, drivePath, pathOf]

omit [MeasurableSpace Ω] in
theorem neg_drive_nnreal (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (fun t : ℝ≥0 => (-drive κ B ω) t) = drivePath κ (pathOf (-B) ω) := by
  funext t
  simp [drive, drivePath, pathOf]

/-- **(c), reduction to the field.** If `B` is a pre-Brownian motion independent of the field
`Y`, the data of `Y` is a.e.-measurable, and the data of the reflected field `h(−·̄)` has the law
of the data of `Y`, then the configuration law is invariant under `reflectConfig`. -/
theorem configLawFull_reflect_of_field [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (κ : ℝ) (hB : IsPreBrownianReal B P)
    (hBm : AEMeasurable (pathOf B) P) (hind : IndepFun (pathOf B) Y P)
    (hY : AEMeasurable (fun ω => dataH (Y ω)) P)
    (hfield : P.map (fun ω => dataH (RegClosure.reflectH (Y ω))) = P.map (fun ω => dataH (Y ω))) :
    configLawFull (fun ω => reflectConfig (Y ω, drive κ B ω)) P =
      configLawFull (fun ω => (Y ω, drive κ B ω)) P := by
  have e1 : configLawFull (fun ω => reflectConfig (Y ω, drive κ B ω)) P =
      P.map fun ω => (dataH (RegClosure.reflectH (Y ω)), drivePath κ (pathOf (-B) ω)) := by
    show P.map _ = _
    congr 1
    funext ω
    exact Prod.ext rfl (neg_drive_nnreal κ B ω)
  have e2 : configLawFull (fun ω => (Y ω, drive κ B ω)) P =
      P.map fun ω => (dataH (Y ω), drivePath κ (pathOf B ω)) := by
    show P.map _ = _
    congr 1
    funext ω
    exact Prod.ext rfl (drive_nnreal κ B ω)
  have hnegB : IsPreBrownianReal (-B) P := hB.neg
  have hpath : pathOf (-B) = (fun p : ℝ≥0 → ℝ => -p) ∘ pathOf B := by
    funext ω t; simp [pathOf]
  have hnBm : AEMeasurable (pathOf (-B)) P := by
    rw [hpath]; exact measurable_neg.comp_aemeasurable hBm
  -- independence of both pairs
  have hi1 : IndepFun (fun ω => dataH (RegClosure.reflectH (Y ω)))
      (fun ω => drivePath κ (pathOf (-B) ω)) P := by
    rw [hpath]
    exact (hind.symm.comp measurable_dataH_reflectH
      ((measurable_drivePath κ).comp measurable_neg) :)
  have hi2 : IndepFun (fun ω => dataH (Y ω)) (fun ω => drivePath κ (pathOf B ω)) P :=
    (hind.symm.comp measurable_dataH (measurable_drivePath κ) :)
  -- measurability
  have hYr : AEMeasurable (fun ω => dataH (RegClosure.reflectH (Y ω))) P :=
    ((measurable_reflData.comp measurable_fst).comp_aemeasurable hY).congr
      (ae_of_all _ fun ω => (dataFull_reflectH_eq (Y ω)).symm)
  have hD1 : AEMeasurable (fun ω => drivePath κ (pathOf (-B) ω)) P :=
    (measurable_drivePath κ).comp_aemeasurable hnBm
  have hD2 : AEMeasurable (fun ω => drivePath κ (pathOf B ω)) P :=
    (measurable_drivePath κ).comp_aemeasurable hBm
  have hmapD : P.map (fun ω => drivePath κ (pathOf (-B) ω)) =
      P.map (fun ω => drivePath κ (pathOf B ω)) := by
    rw [show (fun ω => drivePath κ (pathOf (-B) ω)) = drivePath κ ∘ pathOf (-B) from rfl,
      show (fun ω => drivePath κ (pathOf B ω)) = drivePath κ ∘ pathOf B from rfl,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_drivePath κ).aemeasurable
        hnBm,
      ← AEMeasurable.map_map_of_aemeasurable (measurable_drivePath κ).aemeasurable
        hBm, map_pathOf_eq_of_isPreBrownianReal hnegB hB hnBm hBm]
  rw [e1, e2, (indepFun_iff_map_prod_eq_prod_map_map hYr hD1).1 hi1,
    (indepFun_iff_map_prod_eq_prod_map_map hY hD2).1 hi2, hfield, hmapD]

/-! ## 4. Transfer along `fieldLawFull` and the wedge form of (c) -/

/-- The reflected data law transfers along equality of `fieldLawFull H` laws, for fields with
a.e.-measurable data. -/
theorem map_dataH_reflectH_transfer {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} {Y : Ω → FieldSample} {Z : Ω' → FieldSample}
    (hY : AEMeasurable (fun ω => dataH (Y ω)) P) (hZ : AEMeasurable (fun ω => dataH (Z ω)) P')
    (hlaw : fieldLawFull H Y P = fieldLawFull H Z P') :
    P.map (fun ω => dataH (RegClosure.reflectH (Y ω))) =
      P'.map (fun ω => dataH (RegClosure.reflectH (Z ω))) := by
  have hl : P.map (fun ω => dataH (Y ω)) = P'.map (fun ω => dataH (Z ω)) := hlaw
  have e1 : (fun ω => dataH (RegClosure.reflectH (Y ω))) =
      (reflData ∘ Prod.fst) ∘ fun ω => dataH (Y ω) :=
    funext fun ω => dataFull_reflectH_eq (Y ω)
  have e2 : (fun ω => dataH (RegClosure.reflectH (Z ω))) =
      (reflData ∘ Prod.fst) ∘ fun ω => dataH (Z ω) :=
    funext fun ω => dataFull_reflectH_eq (Z ω)
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable
      (measurable_reflData.comp measurable_fst).aemeasurable hY,
    ← AEMeasurable.map_map_of_aemeasurable
      (measurable_reflData.comp measurable_fst).aemeasurable hZ, hl]

/-- **B4(d), reflection invariance of the reference wedge field** (open input). For the
reference field `canonical γ (h† + Q(−log|·|) + A_{−log|·|})` of `IsQuantumWedge`, its data is
a.e.-measurable and the data of its reflection `h(−·̄)` has the law of its data. (Measurability
is part of the statement: at this mathlib pin the pushforward along a non-a.e.-measurable map is
a Dirac mass, so the law identity alone would not transfer.) -/
def WedgeRefReflectStmt (γ α : ℝ) : Prop :=
  ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    AEMeasurable (fun ω => dataH
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))) P' ∧
    P'.map (fun ω => dataH (RegClosure.reflectH
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))))) =
      P'.map (fun ω => dataH
        (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))))

/-- **Reflection invariance of a quantum wedge** (given B4(d)): the data of `h(−·̄)` has the law
of the data of `h`. -/
theorem map_dataH_reflectH_wedge {γ α : ℝ}
    (href : WedgeRefReflectStmt γ α) {Y : Ω → FieldSample} (hW : IsQuantumWedge γ α Y P)
    (hY : AEMeasurable (fun ω => dataH (Y ω)) P) :
    P.map (fun ω => dataH (RegClosure.reflectH (Y ω))) = P.map (fun ω => dataH (Y ω)) := by
  obtain ⟨-, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  obtain ⟨hZ, hZr⟩ := href Ω' P' X A hP' hX hA hI
  rw [map_dataH_reflectH_transfer hY hZ hlaw, hZr]
  exact hlaw.symm

/-- **F1d input (c): reflection invariance of `P_*`** (given B4(d)). For a quantum wedge `Y`
with a.e.-measurable data and an independent pre-Brownian motion `B` with a.e.-measurable
paths, the law `configLawFull` of `(Y, √κ B)` is invariant under `reflectConfig`. This is the
hypothesis `hlaw` of `f1d_lengths_agree` for `c ω = (Y ω, drive κ B ω)`. -/
theorem configLawFull_reflect_of_wedge [IsProbabilityMeasure P] {γ α κ : ℝ}
    (href : WedgeRefReflectStmt γ α) {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ}
    (hW : IsQuantumWedge γ α Y P) (hY : AEMeasurable (fun ω => dataH (Y ω)) P)
    (hB : IsPreBrownianReal B P) (hBm : AEMeasurable (pathOf B) P)
    (hind : IndepFun (pathOf B) Y P) :
    configLawFull (fun ω => reflectConfig (Y ω, drive κ B ω)) P =
      configLawFull (fun ω => (Y ω, drive κ B ω)) P :=
  configLawFull_reflect_of_field κ hB hBm hind hY (map_dataH_reflectH_wedge href hW hY)

end F1
end QuantumZipper
