import QuantumZipper.Proofs.Thm18.ASepD84

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP / D84: consumers of the A-sep leaf rewired to `G4SepRep0Stmt`

Verbatim copies, with `G4DriverPushSepAllStmt` replaced by its `τ' = 0` form
`ASep.G4DriverPushSep0Stmt` (the only parameters used), of `R18.g4RoundDownA_of`
(R18RoundDownWire.lean), `R18.g4ZipRegAStmt_of` (R18ZipReg.lean), `R18.g4RoundAStmt_of`
(R18Headline.lean) and `R18.theorem1_8Paper_of_frontier6` (R18ZipFacHead.lean). Sources as there
(Sheffield, arXiv:1012.4797, Theorem 1.8 (1), (3), p. 26). Decision D84. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core R18

/-- `Z^LEN_ℓ ∘ Z^LEN_{−ℓ} = id` off the curve, from A-sep at `τ' = 0` and the welding node. -/
theorem g4RoundDownA0_of (hA : G4DriverPushSep0Stmt) (hU : G4UpWeldCoreAStmt) :
    G4RoundDownAStmt := by
  intro γ Ω _ P _ B Y hS hIn hE6 hEq ℓ hℓ
  have hN := curveAreaNull_holds γ hS.1 hS.2.1 P B Y hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2
  obtain ⟨hw, -⟩ := Wire4.wedgeZeroRegStmt γ P Y hS.1 hS.2.1 hS.2.2.2.1
  filter_upwards [hU γ P B Y hS hIn hE6 hEq ℓ hℓ, hA γ P B Y hS hIn, hN, hw,
    wedgeRegSampleStmt_holds γ P Y hS.1 hS.2.1 hS.2.2.2.1, hIn.2.2, D74.ae_curveOf_drive_eq hS,
    ae_remHull_revDrv hS, D74.ae_wedgeConfig_snd_good hS]
    with ω hu hsep hnull hw1 hreg hin hcurve hrem hgood
  obtain ⟨ha, ht, hz, hwe⟩ := hu
  set c := wedgeAConfig γ B Y ω with hcdef
  set t := lenTimeOpen γ ℓ c.toPair with htdef
  set a := areaScale (zipCapDownA γ t c).area with hadef
  have hc : Continuous c.drv := hgood.1
  have hc0 : c.drv 0 = 0 := hgood.2
  have hsub : fwdHull c.drv t ⊆ curveOf c.drv := by
    show fwdHull (drive (γ ^ 2) B ω) t ⊆ curveOf (drive (γ ^ 2) B ω)
    rw [hcurve, hin.2.1 t ht.le]
    exact image_mono fun x hx => le_of_lt hx.1
  have hK : c.area (fwdHull c.drv t ∩ H) = 0 :=
    measure_mono_null (inter_subset_left.trans hsub) hnull
  have hH : c.area Hᶜ = 0 := E6.awt_qAreaMeasure_compl_H γ (Y ω)
  have h1 : areaScale c.area = 1 := hw1.2
  have hq : IsLenWeldingDriver γ (zipLenDownA γ ℓ c).fld ℓ (revDrv c.drv t a) := by
    refine ⟨by simp only [revDrv]; positivity, by simp only [revDrv]; fun_prop,
      by simp [revDrv], Or.inr ?_, hz, hwe⟩
    exact isSimpleCurveHull_revDrv hc hc0 ht ha hin.1 (hin.2.1 _ ht.le)
  exact configEqOff_zipLenUpA_zipLenDownA_of hℓ.le hc hc0 hH h1 rfl rfl ht ha hK hsub hq
    (hrem _ _ ht ha) (pushRegOffAt_of_sep0 hsep ht ha)
    (regEq_rescale_rescale_inv hreg (Qc γ) hw1.1 ha)

/-- Off-curve regularity of the re-zipped field from A-sep at `τ' = 0` and the welding core. -/
theorem g4ZipRegA0_of (hA : G4DriverPushSep0Stmt) (hU : G4UpWeldCoreAStmt) :
    G4ZipRegAStmt := by
  intro γ Ω _ P _ B Y hS hIn hE6 hEq ℓ hℓ
  have hRD := g4RoundDownA0_of hA hU γ P B Y hS hIn hE6 hEq ℓ hℓ
  have hN := curveAreaNull_holds γ hS.1 hS.2.1 P B Y hS.2.2.1 hS.2.2.2.1 hS.2.2.2.2
  obtain ⟨hw, -⟩ := Wire4.wedgeZeroRegStmt γ P Y hS.1 hS.2.1 hS.2.2.2.1
  have hreg := wedgeRegSampleStmt_holds γ P Y hS.1 hS.2.1 hS.2.2.2.1
  -- the re-zipped field, exactly, a.s.
  have hF : ∀ᵐ ω ∂P, ∃ (a : ℝ) (G : FieldSample) (K' : Set ℂ), 0 < a ∧
      (zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω))).fld = rescale G (Qc γ) a⁻¹ ∧
      RegEqOff K' G (rescale (Y ω) (Qc γ) a) ∧
      {w : ℂ | ((a⁻¹ : ℝ) : ℂ) * w ∈ K'} ⊆ curveOf (drive (γ ^ 2) B ω) := by
    filter_upwards [hU γ P B Y hS hIn hE6 hEq ℓ hℓ, hA γ P B Y hS hIn, hN,
      hw, hIn.2.2, D74.ae_curveOf_drive_eq hS, ae_remHull_revDrv hS,
      D74.ae_wedgeConfig_snd_good hS] with ω hu hsep hnull hw1 hin hcurve hrem hgood
    obtain ⟨ha, ht, hz, hwe⟩ := hu
    set c := wedgeAConfig γ B Y ω with hcdef
    set t := lenTimeOpen γ ℓ c.toPair with htdef
    set a := areaScale (zipCapDownA γ t c).area with hadef
    have hc : Continuous c.drv := hgood.1
    have hc0 : c.drv 0 = 0 := hgood.2
    have hsub : fwdHull c.drv t ⊆ curveOf c.drv := by
      show fwdHull (drive (γ ^ 2) B ω) t ⊆ curveOf (drive (γ ^ 2) B ω)
      rw [hcurve, hin.2.1 t ht.le]
      exact image_mono fun x hx => le_of_lt hx.1
    have hK : c.area (fwdHull c.drv t ∩ H) = 0 :=
      measure_mono_null (inter_subset_left.trans hsub) hnull
    have hH : c.area Hᶜ = 0 := E6.awt_qAreaMeasure_compl_H γ (Y ω)
    have h1 : areaScale c.area = 1 := hw1.2
    have hq : IsLenWeldingDriver γ (zipLenDownA γ ℓ c).fld ℓ (revDrv c.drv t a) := by
      refine ⟨by simp only [revDrv]; positivity, by simp only [revDrv]; fun_prop,
        by simp [revDrv], Or.inr ?_, hz, hwe⟩
      exact isSimpleCurveHull_revDrv hc hc0 ht ha hin.1 (hin.2.1 _ ht.le)
    obtain ⟨G, K', h1', h2', h3'⟩ := zipLenA_zipLenDownA_fld_eq hℓ.le hc hc0 hH h1 rfl rfl ht ha
      hK hsub hq (hrem _ _ ht ha) (pushRegOffAt_of_sep0 hsep ht ha)
    exact ⟨a, G, K', ha, h1', h2', h3'⟩
  refine ⟨?_, fun ρ => ?_⟩
  · filter_upwards [hF, hRD, hreg] with ω hf hrd hr i hi
    obtain ⟨a, G, K', ha, hfld, hG, hsub⟩ := hf
    set Z := zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)) with hZ
    have hcur : curveOf Z.drv = curveOf (drive (γ ^ 2) B ω) := curveOf_congr hrd.2
    have hrd1 : RegEqOff (curveOf (drive (γ ^ 2) B ω)) Z.fld (Y ω) := hrd.1
    rw [hcur] at hi
    have hri := UnzipFull.fullIndex_radius_pos i
    rw [evalReg_foldedCircle_congr_of_regEqOff hrd1 hri.le hi, hfld,
      rescale_fc_congr_off hG _ (inv_pos.2 ha) hsub hri.le hi,
      G1.rescale_rescale_inv_fc hr _ ha _ hri]
  · obtain ⟨hs, hc, hH⟩ := ρ.2
    have hH' : tsupport (-ρ.1) ⊆ H := by rw [tsupport_neg]; exact hH
    filter_upwards [hF, hRD, hreg, wedgePairContStmt_holds γ P Y hS.1 hS.2.1 hS.2.2.2.1 ρ]
      with ω hf hrd hr hpc hd
    obtain ⟨a, G, K', ha, hfld, hG, hsub⟩ := hf
    set Z := zipLenA γ ℓ (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)) with hZ
    have hcur : curveOf Z.drv = curveOf (drive (γ ^ 2) B ω) := curveOf_congr hrd.2
    have hrd1 : RegEqOff (curveOf (drive (γ ^ 2) B ω)) Z.fld (Y ω) := hrd.1
    rw [hcur] at hd
    rw [pairTest_congr_of_regEqOff (D74.isClosed_curveOf _) hrd1 ρ hd]
    obtain ⟨r, hr0, hrr⟩ := Metric.exists_pos_forall_lt_edist ρ.2.2.1
      (D74.isClosed_curveOf (drive (γ ^ 2) B ω)) hd
    have hr0' : (0 : ℝ) < r := hr0
    have hfar : ∀ w ∈ tsupport ρ.1, 0 ≤ w.im ∧
        ∀ p ∈ curveOf (drive (γ ^ 2) B ω), (r : ℝ) ≤ dist w p := fun w hw =>
      ⟨le_of_lt (ρ.2.2.2 hw), fun p hp => by
        have := hrr w hw p hp
        rw [edist_dist] at this
        exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1
          (by simpa using this))⟩
    have hae : ∀ f : ℂ → ℝ, (∀ z, z ∉ tsupport ρ.1 → f z = 0) →
        ∀ᵐ w ∂(volume.withDensity fun z => ENNReal.ofReal (f z)), w ∈ tsupport ρ.1 := by
      intro f hf
      rw [ae_iff]
      have hm : MeasurableSet {a : ℂ | a ∉ tsupport ρ.1} :=
        (isClosed_tsupport ρ.1).isOpen_compl.measurableSet
      rw [withDensity_apply _ hm, setLIntegral_congr_fun hm (g := fun _ => 0) (fun z hz => by
        show ENNReal.ofReal (f z) = 0
        rw [hf z hz, ENNReal.ofReal_zero]), lintegral_zero]
    have hai : 0 < a⁻¹ := inv_pos.2 ha
    have hmeas : MeasurableSet {w : ℂ | 0 ≤ w.im ∧ ∀ p ∈ K', a⁻¹ * r ≤ dist w p} := by
      have e : {w : ℂ | 0 ≤ w.im ∧ ∀ p ∈ K', a⁻¹ * r ≤ dist w p} =
          {w : ℂ | 0 ≤ w.im} ∩ ⋂ p ∈ K', {w : ℂ | a⁻¹ * r ≤ dist w p} := by
        ext w; simp
      rw [e]
      exact ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_biInter fun p _ => isClosed_le continuous_const
          (continuous_id.dist continuous_const))).measurableSet
    have key : ∀ f : ℂ → ℝ, (∀ z, z ∉ tsupport ρ.1 → f z = 0) →
        rescale G (Qc γ) a⁻¹ (volume.withDensity fun z => ENNReal.ofReal (f z)) =
          rescale (rescale (Y ω) (Qc γ) a) (Qc γ) a⁻¹
            (volume.withDensity fun z => ENNReal.ofReal (f z)) := by
      intro f hf
      refine rescale_far_congr_off hG _ (d := a⁻¹ * r) (by positivity) ?_
      have hm : Measurable fun z : ℂ => ((a⁻¹ : ℝ) : ℂ) * z := measurable_const_mul _
      refine (ae_map_iff hm.aemeasurable hmeas).2 ((hae f hf).mono fun u hu => ?_)
      obtain ⟨him, hdist⟩ := hfar u hu
      refine ⟨?_, far_scale hai hsub hdist⟩
      rw [Complex.im_ofReal_mul]
      exact mul_nonneg hai.le him
    obtain ⟨hi1, hc1⟩ := hpc ρ.1 (Set.mem_insert _ _)
    obtain ⟨hi2, hc2⟩ := hpc (-ρ.1) (Set.mem_insert_of_mem _ rfl)
    have e1 := rescale_rescale_inv_tmeas hr (Qc γ) ha hs.continuous hc hH hi1 hc1
    have e2 := rescale_rescale_inv_tmeas hr (Qc γ) ha hs.continuous.neg hc.neg hH' hi2 hc2
    unfold pairTest pairRaw
    rw [hfld, key ρ.1 (fun z hz => image_eq_zero_of_notMem_tsupport hz),
      key (fun z => -ρ.1 z) (fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz])]
    exact congrArg₂ (· - ·) e1.symm e2.symm

end ASep
end QuantumZipper
