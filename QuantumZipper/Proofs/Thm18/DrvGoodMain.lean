import QuantumZipper.Proofs.Thm18.DrvGoodBM
import QuantumZipper.Proofs.Thm18.RT6bUnzGood
import QuantumZipper.Proofs.Thm18.RT6bFar
import QuantumZipper.Proofs.Thm18.R18ZipFacMain
import QuantumZipper.Proofs.Thm18.R18RoundDownWire
import QuantumZipper.Proofs.Thm18.R18DownTime
import QuantumZipper.Proofs.Thm18.R18Zero
import QuantumZipper.Proofs.Thm18.RT5FarDrv
import QuantumZipper.Proofs.Thm18.R18T4bWeld
import QuantumZipper.Proofs.Thm18.R18ReadMeas
import QuantumZipper.Proofs.Thm18.G4Zero
import QuantumZipper.Proofs.Thm18.G4ASepLog
import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G4ASepDefs
import QuantumZipper.Proofs.Thm18.G4ASepBackLog
import QuantumZipper.Proofs.Thm18.R18UpWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DRVGOOD: the unzipped and the zipped drivers are good (law transfer)

Sheffield, arXiv:1012.4797, Theorem 1.8 (p. 26): the unzipped / zipped curve is again an
SLE_κ curve, since the configuration has the same law. Here: the driver path of `c₁ = Z_{−b} c₀`
has the law of the driver path of `c₀` (E6 on the full data, `map_cfgData_zipLenDownA`), and the
driver path of `Z_ℓ c₀` (the old zip-up `zipLenUpA`, D81) is a.s. a fixed measurable function of
the full data of `c₀` whose value at the full data of `c₁` is the driver of `c₀` (factorization
`g4ZipFactorFullAStmt_of_X1` and the round trip `Z_ℓ ∘ Z_{−ℓ} = id` from A-sep and the welding
core, `g4RoundDownA_of`); at `ℓ = 0` clause (3) `g4ZeroAStmt_holds`. The measurable good set
`DrvGood.goodSet` (DrvGoodDefs.lean) is a.s. hit by the SLE driver (DrvGoodBM.lean), hence by the
transported drivers, and membership gives goodness deterministically (DrvGoodDet.lean). The zip
scale is positive by the area transport of `R18DownTime` (`areaAll_map_revMap`). No D87 (`zipLenMO`)
law is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm DrvGood

theorem drvGood_drive_max (κ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) (r : ℝ) :
    drive κ B ω r = drive κ B ω (max r 0) := by
  simp only [drive]
  congr 2
  apply NNReal.eq
  simp [Real.coe_toNNReal']

/-- A.s. the driver path of `c₀` is in the good set. -/
theorem ae_goodSet_wedge {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, (fun t : ℝ≥0 => (wedgeAConfig γ B Y ω).drv t) ∈ goodSet := by
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith [hS.1, hS.2.1]
  filter_upwards [ae_good_drive hS.2.2.1 (κ := γ ^ 2) (by nlinarith [hS.1]) hκ4,
    D74.ae_wedgeConfig_snd_good hS] with ω hg hω
  show Good (pW fun t : ℝ≥0 => drive (γ ^ 2) B ω t)
  have hc : Continuous (drive (γ ^ 2) B ω) := hω.1
  have hc0 : drive (γ ^ 2) B ω 0 = 0 := hω.2
  rw [pW_eq hc hc0 (drvGood_drive_max _ B ω)]
  exact hg

/-- **The unzipped driver satisfies the radial Hölder bound** (law transfer). -/
theorem unzRadialGoodStmt_holds (hX1 : BaseFin.BaseFiniteStmt) : UnzRadialGoodStmt := by
  intro γ Ω _ P _ B Y hS hIn b hb
  have hA : MeasurableSet {d : E6.FullData | d.2 ∈ goodSet} :=
    measurableSet_goodSet.preimage measurable_snd
  have h1 := Cor15Group.ae_mem_of_map_eq (e := fun x : AreaConfig => cfgData x.toPair)
    (c := fun ω => zipLenDownA γ b (wedgeAConfig γ B Y ω)) (y := wedgeAConfig γ B Y) hA
    (aemeasurable_cfgData_zipLenDownA hX1 hS hb) (aemeasurable_cfgData_wedgeConfig hS hIn)
    (map_cfgData_zipLenDownA hX1 hS hb) (ae_goodSet_wedge hS)
  filter_upwards [h1, D74.ae_wedgeConfig_snd_good hS] with ω h hω
  obtain ⟨hc, hc0⟩ := zipLenDownA_drv_good (γ := γ) (ℓ := b) (c := wedgeAConfig γ B Y ω) hω.1
  have hmax : ∀ r, (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv r =
      (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv (max r 0) := fun r => by
    simp only [zipLenDownA, canonAConfig]
    rw [max_eq_left (le_max_right r 0)]
  have hg : Good (zipLenDownA γ b (wedgeAConfig γ B Y ω)).drv := by
    rw [← pW_eq hc hc0 hmax]; exact h
  exact (good_spec hc hc0 hg).1

/-- At `ℓ = 0` the zipped driver is the driver (deterministic, as `toPair_zipLenA_zero`). -/
theorem zipLenUpA_zero_drv {γ : ℝ} {c : AreaConfig} (hμ : c.area = qAreaMeasure γ c.fld)
    (hsc : scaleParam γ c.fld = 1) (hc0 : c.drv 0 = 0) (t : ℝ≥0) :
    (zipLenUpA γ 0 c).drv t = c.drv t := by
  obtain ⟨hT, hcV, h0⟩ := lenWeldDriver_zero_spec γ c.fld
  have hmap : (c.area.restrict H).map (revMap (lenWeldDriver γ c.fld 0).2 0) =
      c.area.restrict H := by
    have hae : revMap (lenWeldDriver γ c.fld 0).2 0 =ᵐ[c.area.restrict H] id :=
      (ae_restrict_iff' isOpen_H.measurableSet).2
        (Filter.Eventually.of_forall fun z hz => CharFun.revMap_zero_eq hcV h0 hz)
    rw [Measure.map_congr hae, Measure.map_id]
  have hL : areaScale (zipWeldUpA γ (lenWeldDriver γ c.fld 0).1
      (lenWeldDriver γ c.fld 0).2 c).area = 1 := by
    show areaScale ((c.area.restrict H).map
      (revMap (lenWeldDriver γ c.fld 0).2 (lenWeldDriver γ c.fld 0).1)) = 1
    rw [hT, hmap, areaScale_restrict_H, hμ, areaScale_qAreaMeasure, hsc]
  simp only [zipLenUpA, canonAConfig]
  rw [hL]
  simp only [one_pow, one_mul, div_one]
  rw [max_eq_left (NNReal.coe_nonneg t)]
  show rt5V (lenWeldDriver γ c.fld 0).1 (lenWeldDriver γ c.fld 0).2 c.drv t = c.drv t
  rw [hT]
  unfold rt5V
  split_ifs with h
  · have e : (t : ℝ) = 0 := le_antisymm h t.2
    rw [e]; simp [h0, hc0]
  · simp [h0]

/-- A.s. the driver path of `Z_0 c₀` is in the good set. -/
theorem ae_goodSet_zipZero {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, (fun t : ℝ≥0 => (zipLenUpA γ 0 (wedgeAConfig γ B Y ω)).drv t) ∈ goodSet := by
  obtain ⟨hR, -⟩ := Wire4.wedgeZeroRegStmt γ P Y hS.1 hS.2.1 hS.2.2.2.1
  filter_upwards [hR, ae_goodSet_wedge hS, D74.ae_wedgeConfig_snd_good hS] with ω hω hg hω'
  have hμ : (wedgeAConfig γ B Y ω).area = qAreaMeasure γ (wedgeAConfig γ B Y ω).fld := rfl
  have hsc : scaleParam γ (wedgeAConfig γ B Y ω).fld = 1 := hω.2
  have hc0 : (wedgeAConfig γ B Y ω).drv 0 = 0 := hω'.2
  have e : (fun t : ℝ≥0 => (zipLenUpA γ 0 (wedgeAConfig γ B Y ω)).drv t) =
      fun t : ℝ≥0 => (wedgeAConfig γ B Y ω).drv t :=
    funext fun t => zipLenUpA_zero_drv hμ hsc hc0 t
  rw [e]; exact hg

end R18
end QuantumZipper
