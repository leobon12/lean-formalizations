import QuantumZipper.Proofs.Thm18.RT5ODefs
import QuantumZipper.Proofs.Thm18.RT5OCurve
import QuantumZipper.Proofs.Thm18.R18RTZipMain
import QuantumZipper.Proofs.Thm18.R18UpWeld
import QuantumZipper.Proofs.Thm18.R18T6Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT5, D86 + D87 form: `Z_ℓ ∘ Z_{−ℓ}^{pieces} = id` off the curve, from FarPull alone

Sheffield, arXiv:1012.4797, Theorem 1.8 (1), p. 26: `Z^LEN_ℓ` is the inverse of `Z^LEN_{−ℓ}`,
defined by conformal welding of the two pieces by their quantum boundary lengths. With the zip-up
acting on the pieces read off the curve (D87) and welding them by their open-arc lengths (D86,
`zipLenUpOA`, RT5ODefs.lean), `Z_ℓ = zipLenUpOA γ ℓ ∘ offConfig γ`, and the boundary-measure node
`Rt5BdryStmt` of R18RTZipMain.lean is not needed:

* the pieces of `Z_{−ℓ}^{pieces} c₀` are those of `A' = Z_{−ℓ} c₀` (RT2: equal masked data);
* the pieces of `A'` agree with `A'` off its curve, which meets `ℝ` only at `0`
  (`real_not_mem_curveOf_outDrv`), so they have the open-arc welding driver of `A'`
  (`lenWeldDriverO_offConfig_eq`); `A'` has a global boundary limit without atoms
  (`ae_bReg_zipLenDownA`: E6 transfer of `WedgeBdry.BReg`, as in `g4UpWeldCoreAStmt_of_X1`), so
  this is its old welding driver (`ae_lenWeldDriverO_offConfig_zipLenDownA`); same at the wedge
  (`ae_lenWeldDriverO_offConfig_wedge`);
* then the zip-up congruence under FarPull (`rt5o_zipLenUpOA_congr`) and T7b.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core Thm18Asm.G1ZA1c LocLen D3Plus

/-! ## A.s. inputs at the unzipped configuration -/

/-- A.s. the unzipped wedge `Z_{−ℓ} c₀` has a global boundary limit without atoms (and positive
on intervals): E6 transfer from the wedge (the argument of `g4UpWeldCoreAStmt_of_X1`). -/
theorem ae_bReg_zipLenDownA (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, WedgeBdry.BReg γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld := by
  have hE6 := e6StmtArc_of_X1 hX1
  have hum := unzipMeasArc_of_X1 hX1
  set c := wedgeConfig γ B Y with hc
  set c' := fun ω => zipLenDownArc γ ℓ (c ω) with hc'
  have hpath : AEMeasurable (fun ω => fun t : ℝ≥0 => (c ω).2 t) P := by
    have hm : Measurable fun a : ℝ≥0 → ℝ => fun t : ℝ≥0 =>
        Real.sqrt (γ ^ 2) * a ((t : ℝ).toNNReal) :=
      measurable_pi_iff.2 fun t => (measurable_pi_apply _).const_mul _
    exact hm.comp_aemeasurable (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hS.2.2.1)
  have hmc : AEMeasurable (fun ω => g1zCfgData (c ω)) P := hIn.2.1.prodMk hpath
  have hmc' : AEMeasurable (fun ω => g1zCfgData (c' ω)) P :=
    aemeasurable_cfgData_zipLenDownArc hum hS hℓ
  have hlaw : P.map (fun ω => g1zCfgData (c' ω)) = P.map (fun ω => g1zCfgData (c ω)) :=
    e6Arc_thm18 hE6 hS ℓ hℓ
  have hBY : ∀ᵐ ω ∂P, WedgeBdry.BReg γ (Y ω) := by
    filter_upwards [hIn.1, ae_atomless_pos_wedge hS hIn] with ω h1 h2
    exact WedgeBdry.bReg_of h1.1 h2.1 h2.2
  have hflaw : fieldLawFull H (fun ω => (c' ω).1) P = fieldLawFull H Y P := by
    have e1 : fieldLawFull H (fun ω => (c' ω).1) P =
        (P.map fun ω => g1zCfgData (c' ω)).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hmc').symm
    have e2 : fieldLawFull H Y P = (P.map fun ω => g1zCfgData (c ω)).map Prod.fst :=
      (AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable hmc).symm
    rw [e1, e2, hlaw]
  have hB' : ∀ᵐ ω ∂P, WedgeBdry.BReg γ (c' ω).1 :=
    WedgeBdry.ae_of_fieldLawFull_eq hflaw hmc'.fst hIn.2.1 (WedgeBdry.BReg γ)
      (WedgeBdry.measurableSet_bReg γ) (WedgeBdry.bReg_reconstruct γ) hBY
  filter_upwards [hB', ae_toPair_zipLenDownA_eq hS ℓ] with ω hb htp
  have hfld : (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld = (c' ω).1 :=
    congrArg Prod.fst htp
  rw [hfld]
  exact hb

/-- A.s. the wedge field has a global boundary limit without atoms. -/
theorem ae_bReg_wedge {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, WedgeBdry.BReg γ (Y ω) := by
  filter_upwards [hIn.1, ae_atomless_pos_wedge hS hIn] with ω h1 h2
  exact WedgeBdry.bReg_of h1.1 h2.1 h2.2

/-- A.s. the curve of the unzipped wedge meets `ℝ` only at `0`. -/
theorem ae_real_not_mem_curveOf_zipLenDownA {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (ℓ : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, t ≠ 0 →
      (t : ℂ) ∉ curveOf (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).drv := by
  have hκ : 0 < γ ^ 2 := by have := hS.1; positivity
  have hκ4 : γ ^ 2 < 4 := by have := hS.1; have := hS.2.1; nlinarith
  filter_upwards [RS.ae_radialGood_drive hS.2.2.1 hκ (by linarith), hIn.2.2,
    ae_areaScale_zipCapDownA_wedge_pos hS ℓ] with ω hRG hω ha
  intro t ht
  have hT : 0 ≤ lenTimeOpen γ ℓ (wedgeAConfig γ B Y ω).toPair := lenTimeOpen_nonneg _ _ _
  exact real_not_mem_curveOf_outDrv hRG hω.1.2.2.1 hω.1.2.2.2.1 hω.1.2.2.2.2 hT
    (hω.2.1 _ hT) ha ht

/-! ## Zip-up congruence, D86 form (deterministic) -/

/-- Same open-arc welding driver as the old driver of `c'`, same driver and area, fields equal off
the curve, FarPull at `c'` ⇒ the D86 zip-up of `c` and the zip-up of `c'` agree off the zipped
curve and have the same driver. -/
theorem rt5o_zipLenUpOA_congr {γ ℓ : ℝ} {c c' : AreaConfig}
    (hp : lenWeldDriverO γ c.fld ℓ = lenWeldDriver γ c'.fld ℓ) (hd : c.drv = c'.drv)
    (ha : c.area = c'.area) (hreg : RegEqOff (curveOf c'.drv) c.fld c'.fld)
    (hfar : Rt5FarPull γ ℓ c') :
    RegEqOff (curveOf (zipLenUpA γ ℓ c').drv) (zipLenUpOA γ ℓ c).fld (zipLenUpA γ ℓ c').fld ∧
      (zipLenUpOA γ ℓ c).drv = (zipLenUpA γ ℓ c').drv := by
  obtain ⟨hpos, hfar⟩ := hfar
  refine ⟨?_, ?_⟩
  swap
  · simp only [zipLenUpOA, zipLenUpA, canonAConfig, zipWeldUpA, zipWeldUp, AreaConfig.toPair,
      hp, hd, ha]
  set p := lenWeldDriver γ c'.fld ℓ with hpdef
  set a := areaScale (zipWeldUpA γ p.1 p.2 c').area with hadef
  set K := curveOf (zipLenUpA γ ℓ c').drv with hKdef
  have e1 : (zipLenUpOA γ ℓ c).fld =
      rescale (coordChange c.fld (revMapInv p.2 p.1) (Qc γ)) (Qc γ) a := by
    simp only [zipLenUpOA, canonAConfig, zipWeldUpA, zipWeldUp, AreaConfig.toPair, hp, ha, hadef]
  have e2 : (zipLenUpA γ ℓ c').fld =
      rescale (coordChange c'.fld (revMapInv p.2 p.1) (Qc γ)) (Qc γ) a := rfl
  rw [e1, e2]
  have h1 : RegEqOff {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K}
      (coordChange c.fld (revMapInv p.2 p.1) (Qc γ))
      (coordChange c'.fld (revMapInv p.2 p.1) (Qc γ)) :=
    regEqOff_coordChange_of_pull (Qc γ) fun d k hc => by
      obtain ⟨δ, hδ, hν⟩ := hfar d k hc
      exact evalReg_congr_of_regEqOff_far hreg hδ hν
  have h2 := regEqOff_rescaleU h1 (Qc γ) hpos
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  refine regEqOff_monoU (fun w hw => ?_) h2
  have hw' : ((a⁻¹ : ℝ) : ℂ) * ((a : ℂ) * w) ∈ K := hw
  rwa [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ haC, one_mul] at hw'

/-! ## Boundary identities for the pieces (stable names, used by RT6) -/

/-- A.s. the wedge curve meets `ℝ` only at `0`. -/
theorem ae_real_not_mem_curveOf_wedge {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, t ≠ 0 → (t : ℂ) ∉ curveOf (wedgeAConfig γ B Y ω).drv := by
  have hκ : 0 < γ ^ 2 := by have := hS.1; positivity
  have hκ4 : γ ^ 2 < 4 := by have := hS.1; have := hS.2.1; nlinarith
  filter_upwards [RS.ae_radialGood_drive hS.2.2.1 hκ (by linarith), hIn.2.2] with ω hRG hω
  intro t ht
  have h := real_not_mem_curveOf_outDrv hRG hω.1.2.2.1 hω.1.2.2.2.1 hω.1.2.2.2.2 le_rfl
    (hω.2.1 0 le_rfl) one_pos ht
  have hW0 := hRG.2.1
  have e : curveOf (outDrv (drive (γ ^ 2) B ω) 0 1) = curveOf (drive (γ ^ 2) B ω) :=
    curveOf_congr fun u hu => by simp [outDrv, max_eq_left hu, hW0]
  rw [e] at h
  exact h

/-- **Boundary identity at the wedge (D86 + D87)**: a.s., for every `ℓ`, the open-arc welding
driver of the pieces of `c₀` read off the curve is the welding driver of `c₀`. -/
theorem ae_lenWeldDriverO_offConfig_wedge {γ : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, ∀ ℓ : ℝ, lenWeldDriverO γ (offConfig γ (wedgeAConfig γ B Y ω)).fld ℓ =
      lenWeldDriver γ (wedgeAConfig γ B Y ω).fld ℓ := by
  filter_upwards [D74.ae_wedgeConfig_snd_good hS, ae_real_not_mem_curveOf_wedge hS hIn,
    ae_bReg_wedge hS hIn] with ω hω hR hb ℓ
  rw [lenWeldDriverO_offConfig_eq γ hω.1 hω.2 hR ℓ]
  exact lenWeldDriverO_eq_of (openArcLen_eq_of_bReg hb) ℓ

/-- **Boundary identity at the unzipped wedge (D86 + D87)**: a.s., for every `ℓ'`, the open-arc
welding driver of the pieces of `Z_{−ℓ} c₀` read off the curve is the welding driver of
`Z_{−ℓ} c₀`. -/
theorem ae_lenWeldDriverO_offConfig_zipLenDownA (hX1 : BaseFin.BaseFiniteStmt) {γ : ℝ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y)
    (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∀ᵐ ω ∂P, ∀ ℓ' : ℝ,
      lenWeldDriverO γ (offConfig γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).fld ℓ' =
        lenWeldDriver γ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld ℓ' := by
  filter_upwards [D74.ae_wedgeConfig_snd_good hS, ae_real_not_mem_curveOf_zipLenDownA hS hIn ℓ,
    ae_bReg_zipLenDownA hX1 hS hIn hℓ] with ω hω hR hb ℓ'
  have hd := zipLenDownA_drv_good (γ := γ) (ℓ := ℓ) (c := wedgeAConfig γ B Y ω) hω.1
  rw [lenWeldDriverO_offConfig_eq γ hd.1 hd.2 hR ℓ']
  exact lenWeldDriverO_eq_of (openArcLen_eq_of_bReg hb) ℓ'

/-! ## RT5, D86 + D87 form -/

/-- **Second round trip of clause (1), D82 + D86 + D87 form**: `Z_ℓ = zipLenUpOA γ ℓ ∘ offConfig γ`
after `Z_{−ℓ} = zipLenDownMA γ ℓ`. -/
def G4RoundDownOMStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∀ ℓ : ℝ, 0 < ℓ → ∀ᵐ ω ∂P,
      ConfigEqOff (zipLenUpOA γ ℓ (offConfig γ (zipLenDownMA γ ℓ (wedgeAConfig γ B Y ω)))).toPair
        (wedgeAConfig γ B Y ω).toPair

end R18
end QuantumZipper
