import QuantumZipper.Proofs.Thm18.RTMeas3Cert
import QuantumZipper.Proofs.Thm18.RTMeas2Area
import QuantumZipper.Proofs.Thm18.R18ZipFacMain
import QuantumZipper.Proofs.Thm18.RT5OMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS3, part 5: `UpPiecesReadStmt` for `ℓ > 0`

The Borel set: flag `1`, driver `0` at time `0`, the pieces' open-arc welding driver read by `ZO`
(`GamO`), and the area certificate (`AreaCertD`, RTMeas2Area.lean). The Borel map: `phiO` masked
and encoded (RTMeas3Zip.lean). A.s. along the wedge: the pieces carry `CertO`
(`certO_offConfig`, from the wedge's boundary certificates `g4WedgeCertStmt` and `BReg`); their
open-arc welding drivers are the wedge's (closed-arc) welding drivers (`openArcLen_congr_off`,
`isLenWeldingDriverO_eq_of`); and a good one exists a.s. by D81's law transfer of the unzipped
configuration's good driver (`ae_zipLenDownA_goodDrv`, `map_cfgData_zipLenDownA`; Sheffield p. 26,
`Z^LEN_ℓ` is a.s. uniquely defined by welding). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm14Determination Cor15Group

/-- The open-arc welding drivers of the pieces are the welding drivers of the field. -/
theorem isLenWeldingDriverO_offConfig {γ : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (h0 : c.drv 0 = 0) (hR : ∀ t : ℝ, t ≠ 0 → (t : ℂ) ∉ curveOf c.drv)
    (hb : WedgeBdry.BReg γ c.fld) (ℓ : ℝ) :
    IsLenWeldingDriverO γ (offConfig γ c).fld ℓ = IsLenWeldingDriver γ c.fld ℓ := by
  have hK := D74.isClosed_curveOf c.drv
  have h := regEqOff_offConfig γ hc h0
  have hL : lenWeldPointO γ (offConfig γ c).fld ℓ = lenWeldPointO γ c.fld ℓ := by
    unfold lenWeldPointO
    congr 1
    ext s
    exact and_congr_right fun _ => by
      rw [openArcLen_congr_off hK h γ hR (Or.inl le_rfl)]
  have hW : weldHomRO γ (offConfig γ c).fld = weldHomRO γ c.fld := by
    funext s
    unfold weldHomRO
    congr 1
    ext r
    exact and_congr_right fun _ => by
      rw [openArcLen_congr_off hK h γ hR (Or.inl le_rfl),
        openArcLen_congr_off hK h γ hR (Or.inr le_rfl)]
  rw [← isLenWeldingDriverO_eq_of (openArcLen_eq_of_bReg hb)]
  funext p
  simp only [IsLenWeldingDriverO, hL, hW]

/-- A.s. the wedge field has a length-welding driver from the Borel good set (D81's transfer). -/
theorem ae_wedge_goodDrv {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Good : Set PathT} (hGm : MeasurableSet Good) (hGood : ∀ p ∈ Good, GoodP p)
    (hGae : ∀ᵐ ω ∂P, ∀ t' a : ℝ, 0 < t' → 0 < a → ∃ p ∈ Good, p.2 = t' / a ^ 2 ∧
        ∀ u : Icc (0 : ℝ) 1, p.1 u = gStarVal (drive (γ ^ 2) B ω) t' u) :
    ∀ᵐ ω ∂P, ∃ p ∈ Good, IsLenWeldingDriver γ (Y ω) ℓ (p.2, sclDrv p) := by
  have hX1 := X1_holds
  have hE6 := e6AStmt_of_X1 hX1 γ P B Y hS hIn
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  obtain ⟨Z', hZ'm, hZ'G⟩ :=
    exists_measurable_of_partialGraph (measurableSet_gamS γ ℓ hGm) (isPartialGraph_gamS hGood)
  set G : Set E6.FullData := {d | (d.1.1, Z' d.1.1) ∈ GamS γ ℓ Good} with hGdef
  have hc : Measurable fun d : E6.FullData => d.1.1 := measurable_fst.comp measurable_fst
  have hGmeas : MeasurableSet G := (hc.prodMk (hZ'm.comp hc)) (measurableSet_gamS γ ℓ hGm)
  have hyG : ∀ᵐ ω ∂P, cfgData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair ∈ G := by
    filter_upwards [ae_zipLenDownA_goodDrv hX1 hS hIn hE6 hEq hℓ hGood hGae] with ω h
    obtain ⟨hcert, p, hp, hL⟩ := h
    have hmem := mem_gamS hGood hcert hp ((isLenWeldingDriver_fromC_iff γ ℓ _ _).2 hL)
    have e1 : (cfgData (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).toPair).1.1 =
        CoordsFull.coordsFull (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld := rfl
    rw [hGdef, mem_setOf_eq, e1, hZ'G _ hmem]
    exact hmem
  have hmc : AEMeasurable (fun ω => cfgData (wedgeAConfig γ B Y ω).toPair) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hmy := aemeasurable_cfgData_zipLenDownA hX1 hS hℓ
  have hlaw := map_cfgData_zipLenDownA hX1 hS hℓ
  have hcG : ∀ᵐ ω ∂P, cfgData (wedgeAConfig γ B Y ω).toPair ∈ G :=
    Cor15Group.ae_mem_of_map_eq hGmeas hmc hmy hlaw.symm hyG
  filter_upwards [hcG] with ω h
  exact ⟨_, h.2.1, (isLenWeldingDriver_fromC_iff γ ℓ (Y ω) _).1 (isLenWeldingDriver_of_mem hGood h)⟩

/-- **`UpPiecesReadStmt` for `ℓ > 0`.** -/
theorem upPiecesRead_pos (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample)
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    ∃ (Bs : Set RD) (g : RD → RD), MeasurableSet Bs ∧ Measurable g ∧
      (∀ e : (ℕ → ℝ) × (ℝ≥0 → ℝ), Continuous e.2 → encR e ∈ Bs →
        g (encR e) = encR (πdO (zipRead γ ℓ e))) ∧
      ∀ᵐ ω ∂P, encR (πdO (wedgeAConfig γ B Y ω)) ∈ Bs := by
  classical
  obtain ⟨Good, hGm, hGood, hGae⟩ := exists_goodSet_allTimes hS.1 hS.2.1 hS.2.2.1 (P := P)
  obtain ⟨ZO, hZOm, hZOG⟩ := exists_weldReaderO γ ℓ hGm hGood
  obtain ⟨GA, hGAm, hGA, hGAae⟩ := areaRegStmt_holds γ P B Y hS hIn
  have hGA' : ∀ p ∈ GA, AreaGood γ (dfull p) := fun p hp => hGA (dfull p) hp
  refine ⟨{y : RD | y.2 = 1 ∧ y.1.2 0 = 0 ∧ (y, ZO y) ∈ GamO γ ℓ Good ∧ decM y ∈ GA},
    fun y => encT' (πd (D74.maskSel (phiO γ GA ZO (dfull (decM y))))), ?_, ?_, ?_, ?_⟩
  · exact (measurableSet_eq_fun measurable_snd measurable_const).inter
      ((measurableSet_eq_fun ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_fst))
        measurable_const).inter (((measurable_id.prodMk hZOm) (measurableSet_gamO γ ℓ hGm)).inter
          (measurable_decM hGAm)))
  · exact measurable_encT'.comp (measurable_πd.comp (D74.measurable_maskSel.comp
      ((measurable_phiO γ hGAm hGA' hZOm).comp (measurable_dfull.comp measurable_decM))))
  · rintro e hc ⟨-, h0, hG, hA⟩
    have h0' : e.2 0 = 0 := by
      have : (encR e).1.2 0 = e.2 (ratNN 0) := rfl
      rw [this] at h0
      have e0 : ratNN 0 = 0 := by apply NNReal.eq; show max ((0 : ℚ) : ℝ) 0 = 0; simp
      rwa [e0] at h0
    rw [decM_encR hc] at hA
    have hz : zipRead γ ℓ e = zipLenUpOA γ ℓ (configOfData γ (liftπ e)) := by
      unfold zipRead; rw [if_pos hℓ.le]
    show encT' (πd (D74.maskSel (phiO γ GA ZO (dfull (decM (encR e)))))) = _
    rw [decM_encR hc, hz, encR_zipLenUpOA_eq hGood hc h0' hG hA]
    rfl
  · filter_upwards [D74.ae_wedgeConfig_snd_good hS, hGAae,
      ae_wedge_goodDrv hS hIn hℓ hGm hGood hGae, ae_bReg_wedge hS hIn,
      g4WedgeCertStmt γ P B Y hS hIn, ae_real_not_mem_curveOf_wedge hS hIn] with
      ω hW hA hD hb hcert hR
    set c := wedgeAConfig γ B Y ω with hcdef
    set e := πdO c with hedef
    have hc : Continuous e.2 := hW.1.comp continuous_subtype_val
    have hcont : Continuous c.drv := hW.1
    have hc0 : c.drv 0 = 0 := hW.2
    have hflag : (encR e).2 = 1 := by simp [encR, hc]
    have he0 : (encR e).1.2 0 = 0 := by
      show e.2 (ratNN 0) = 0
      have e0 : ratNN 0 = 0 := by apply NNReal.eq; show max ((0 : ℚ) : ℝ) 0 = 0; simp
      rw [e0]; exact hc0
    have hX : Xf (encR e) = (offConfig γ c).fld := by
      show readOffField (dfull (decM (encR e))) = _
      rw [decM_encR hc]; rfl
    obtain ⟨-, hatQ, hinfQ⟩ := (certC_iff_certF γ (Y ω)).1 hcert
    have hCO : CertO γ (Xf (encR e)) := by
      rw [hX]; exact certO_offConfig hcont hc0 hR hb.1 hatQ hinfQ
    obtain ⟨p, hp, hL⟩ := hD
    have hLO : IsLenWeldingDriverO γ (Xf (encR e)) ℓ (p.2, sclDrv p) := by
      rw [hX, isLenWeldingDriverO_offConfig hcont hc0 hR hb]; exact hL
    have hmem := mem_gamO hGood hCO hp hLO
    have hZ := hZOG _ hmem
    refine ⟨hflag, he0, ?_, ?_⟩
    · show (encR e, ZO (encR e)) ∈ GamO γ ℓ Good
      rw [hZ]; exact hmem
    · rw [decM_encR hc]; exact hA

end RTMeas
end R18
end QuantumZipper
