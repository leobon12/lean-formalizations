import QuantumZipper.Proofs.Zipper.Cor15LastCore
import QuantumZipper.Proofs.Zipper.Cor15RegWire
import QuantumZipper.Proofs.Zipper.Cor15RegZc

/-!
# COR15-LAST (1): `Cor15ZcReadStmt`, hence `hZc`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18; no
proof in the paper). Own assembly.

* `measurableSet_hullNull`: for a family `Vp a` of continuous drivers, measurable in `a`, the event
  "the forward hull of `trev (Vp a) t` at time `t` is Lebesgue-null" is measurable in `a`
  (`NonSwallow.measurableSet_fwdHull_prod` + `measurable_measure_prodMk_left`).
* `exists_weldRead_cont_ae`: the driver reading of `cor15WeldRead` together with continuity of the
  reading on the good set (`exists_weldRead_of_goodSet_cont`); the a.s. part is the argument of
  `cor15WeldRead_of_reg` with `hreg := ae_reg_zipCapDown`.
* **`cor15ZcRead`**: `Cor15ZcReadStmt`. `Vp e := F e ∘ projIcc` on the good set, `0` off it. On the
  unzipped side the reading is `vrev (√κ B) t`, whose time-reversed hull is the SLE hull `K_t`
  (null a.s., `NonSwallow.ae_measure_fwdHull_eq_zero`); both events are measurable in `b1Data`,
  and they transfer to the zipped side by the B1 law equality (`b1_full`).
* **`aemeasurable_mod0Data_zipCapUp_c`**: `hZc`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull Thm14Determination Thm14WeldingData Thm14GoodDriverSet

/-- The zero-area event of the time-reversed hull is measurable in the parameter. -/
theorem measurableSet_hullNull {α : Type} [MeasurableSpace α] {Vp : α → ℝ → ℝ}
    (hVc : ∀ a, Continuous (Vp a)) (hVm : ∀ s, Measurable fun a => Vp a s) {t : ℝ}
    (ht : 0 ≤ t) :
    MeasurableSet {a | volume (fwdHull (ArcDriver.trev (Vp a) t) t) = 0} := by
  set Bf : ℝ≥0 → α → ℝ := fun r a => ArcDriver.trev (Vp a) t r with hBf
  have hBm : ∀ r, Measurable (Bf r) := fun r => by
    simp only [hBf, ArcDriver.trev]; exact (hVm _).sub (hVm _)
  have hBc : ∀ a, Continuous fun r => Bf r a := fun a =>
    (ArcDriver.continuous_trev (hVc a) t).comp NNReal.continuous_coe
  have hS := (NonSwallow.measurableSet_fwdHull_prod hBm hBc 1 ht).preimage measurable_swap
  have hmeas := measurable_measure_prodMk_left (ν := (volume : Measure ℂ)) hS
  have heq : ∀ a, fwdHull (ArcDriver.trev (Vp a) t) t = fwdHull (drive 1 Bf a) t := fun a =>
    CharFunRhs.fwdHull_eq_of_eqOn (ArcDriver.continuous_trev (hVc a) t)
      (continuous_const.mul ((hBc a).comp continuous_real_toNNReal)) ht fun r hr => by
        show _ = Real.sqrt 1 * ArcDriver.trev (Vp a) t (r.toNNReal : ℝ)
        rw [Real.sqrt_one, one_mul, Real.coe_toNNReal _ hr.1]
  have e : {a | volume (fwdHull (ArcDriver.trev (Vp a) t) t) = 0} =
      (fun a => volume (Prod.mk a ⁻¹' (Prod.swap ⁻¹'
        {p : ℂ × α | p.1 ∈ fwdHull (drive 1 Bf p.2) t}))) ⁻¹' {0} := by
    ext a
    simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    rw [heq a]
    rfl
  rw [e]
  exact hmeas (measurableSet_singleton 0)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **The driver reading with continuity on the good set** (from Theorem 1.3 and
Rohde–Schramm). -/
theorem exists_weldRead_cont_ae (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∃ F : B1E → ℝ → ℝ, Measurable F ∧ ∃ A : Set B1E, MeasurableSet A ∧
      (∀ x, b1Data x ∈ A → EqOn (weldDriver (Real.sqrt κ) x.1 t) (F (b1Data x)) (Icc 0 t)) ∧
      (∀ e ∈ A, ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧ EqOn (F e) W (Icc 0 t)) ∧
      ∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A := by
  set γ := Real.sqrt κ
  obtain ⟨B', hB', hind', hae⟩ := ae_coordsFull_unzip_map κ hB hX hind ht.le
  obtain ⟨G, hGm, hgood, hGae⟩ := exists_goodPathRSet hRSS hκ hκ4 ht P B' hB'
  obtain ⟨F, hFm, A, hAm, hEq, hcrit, hcont⟩ := exists_weldRead_of_goodSet_cont γ ht hGm hgood
  refine ⟨F, hFm, A, hAm, hEq, fun e he => ?_, ?_⟩
  · obtain ⟨g, hg, hFg⟩ := hcont e he
    exact ⟨_, continuous_extIccPath ht.le g, (hgood g hg).1.1, hFg⟩
  have h4a := Thm14Wire.theorem1_4a_of_theorem1_3_rss h13 hRSS κ hκ hκ4 t ht P B' X hB' hX hind'
  have hrc := RevCouplingReg.revCouplingBoundaryMeasureRegular κ hκ hκ4 t ht P B' X hB' hX hind'
  filter_upwards [hae, h4a, hGae, hrc, ae_reg_zipCapDown hκ hκ4 hB hX hind ht] with ω ⟨_, hC⟩
    ⟨⟨_, hw⟩, _⟩ ⟨hc, hmemG⟩ ⟨hatom, _, _⟩ ⟨hbc, hcert, hinf⟩
  set y := zipCapDown γ t (ofFun (h0rev κ) + X ω, drive κ B ω) with hy
  set V := drive κ B' ω
  have hqy : qBoundaryMeasure γ y.1 =
      qBoundaryMeasure γ (couplingFieldRev κ V t (X ω)) :=
    UnzipFull.qBoundaryMeasure_congr_of_coordsFull _ hC
  have hcertf := bCert_fieldOf hbc hcert
  obtain ⟨ν, hν⟩ := E1.M4.exists_isVagueLimitR_of_bCert hcertf
  have hνe : ν = _ • qBoundaryMeasure γ y.1 :=
    (qBoundaryMeasure_eq hν).symm.trans (qBoundaryMeasure_fieldOf hbc γ)
  refine hcrit _ ⟨zeroMinus V t, pathC t V, hmemG, ?_⟩ ((bdryConvAE_fieldOf_iff y.1).2 hbc)
    hcertf (atomQ_of_atomless hν fun s => ?_) (infQ_of_measure_Ici hν ?_)
  · rw [weldingDataC_eq ht.le CaraR.revMapCaratheodory ht (hgood _ hmemG).1.1
      (hgood _ hmemG).1.2.1, weldingData_congr (extIccPath_pathC ht.le hc)]
    unfold weldingData Thm14WDG.candData
    refine Prod.ext rfl (funext fun q => ?_)
    simp only
    split_ifs with hq
    · rw [← weldHomR_eq_weldReadB1 hbc hν q, hw q hq]
      show weldR γ (couplingFieldRev κ V t (X ω)) q = weldHomR γ y.1 q
      unfold weldR weldHomR
      rw [hqy]
    · rfl
  · rw [hνe, Measure.smul_apply, hqy, hatom s, smul_zero]
  · rw [hνe, Measure.smul_apply, hinf, smul_eq_mul, ENNReal.mul_top]
    exact LocalRule.ofReal_exp_ne_zero _

/-- **The reading `Vp` of the welding driver** (continuous, pointwise measurable, `Vp e 0 = 0`)
with a measurable good set `A` of `b1Data` values on which it reads the welding driver and has a
Lebesgue-null time-reversed hull; `A` is charged a.s. on both sides, and on the unzipped side the
reading is `vrev (√κ B) t`. -/
theorem exists_readVp (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∃ Vp : B1E → ℝ → ℝ, (∀ e, Continuous (Vp e)) ∧ (∀ e, Vp e 0 = 0) ∧
      (∀ s, Measurable fun e => Vp e s) ∧ ∃ A : Set B1E, MeasurableSet A ∧
      (∀ x, b1Data x ∈ A → EqOn (weldDriver (Real.sqrt κ) x.1 t) (Vp (b1Data x)) (Icc 0 t) ∧
        volume (fwdHull (ArcDriver.trev (Vp (b1Data x)) t) t) = 0) ∧
      (∀ᵐ ω ∂P, b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A ∧
        EqOn (Vp (b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))))
          (B2.vrev (drive κ B ω) t) (Icc 0 t)) ∧
      ∀ᵐ ω ∂P, b1Data (ofFun (h0rev κ) + X ω, drive κ B ω) ∈ A := by
  classical
  obtain ⟨F, hFm, A, hAm, hEq, hcont, hyA⟩ :=
    exists_weldRead_cont_ae h13 hRSS hκ hκ4 hB hX hind ht
  set Vp : B1E → ℝ → ℝ := fun e s => if e ∈ A then F e (projIcc 0 t ht.le s) else 0 with hVp
  have hVc : ∀ e, Continuous (Vp e) := by
    intro e
    by_cases he : e ∈ A
    · obtain ⟨W, hWc, -, hW⟩ := hcont e he
      have : Vp e = fun s => W (projIcc 0 t ht.le s) := funext fun s => by
        simp only [hVp, he, ↓reduceIte]; exact hW (projIcc 0 t ht.le s).2
      rw [this]; exact hWc.comp (continuous_subtype_val.comp continuous_projIcc)
    · have : Vp e = fun _ => 0 := funext fun s => by simp only [hVp, he, ↓reduceIte]
      rw [this]; exact continuous_const
  have hV0 : ∀ e, Vp e 0 = 0 := by
    intro e
    by_cases he : e ∈ A
    · obtain ⟨W, -, hW0, hW⟩ := hcont e he
      simp only [hVp, he, ↓reduceIte, projIcc_left]
      exact (hW ⟨le_rfl, ht.le⟩).trans hW0
    · simp only [hVp, he, ↓reduceIte]
  have hVm : ∀ s, Measurable fun e => Vp e s := fun s =>
    Measurable.ite hAm ((measurable_pi_apply _).comp hFm) measurable_const
  have hVeq : ∀ e ∈ A, EqOn (Vp e) (F e) (Icc 0 t) := fun e he s hs => by
    simp only [hVp, he, ↓reduceIte, projIcc_of_mem _ hs]
  set N := {e : B1E | volume (fwdHull (ArcDriver.trev (Vp e) t) t) = 0} with hN
  have hNm : MeasurableSet N := measurableSet_hullNull hVc hVm ht.le
  -- the unzipped side
  obtain ⟨B₁, hB₁m, hB₁c, hB₁0, hB₁, hB₁eq⟩ := RS.exists_good_version0 hB
  have hyN : ∀ᵐ ω ∂P,
      b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A ∩ N ∧
        EqOn (Vp (b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))))
          (B2.vrev (drive κ B ω) t) (Icc 0 t) := by
    filter_upwards [hyA, NonSwallow.ae_measure_fwdHull_eq_zero hB₁.toIsPreBrownianReal hB₁m
      hB₁c hκ hκ4.le volume t, hB₁eq,
      ae_eqOn_weldDriver_zipCapDown h13 hRSS hκ hκ4 P B X hB hX hind ht] with ω hA hn hb hE
    have hdr : drive κ B ω = drive κ B₁ ω := by funext r; simp [drive, hb]
    have hW' : EqOn (Vp (b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω,
        drive κ B ω)))) (B2.vrev (drive κ B ω) t) (Icc 0 t) := fun r hr =>
      (hVeq _ hA hr).trans ((hEq _ hA hr).symm.trans (hE hr))
    have hW : EqOn (Vp (b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω,
        drive κ B ω)))) (B2.vrev (drive κ B₁ ω) t) (Icc 0 t) := by rw [← hdr]; exact hW'
    refine ⟨⟨hA, ?_⟩, hW'⟩
    show volume (fwdHull (ArcDriver.trev (Vp _) t) t) = 0
    rw [CharFunRhs.fwdHull_eq_of_eqOn (ArcDriver.continuous_trev (hVc _) t)
      (continuous_drive_of hB₁c κ ω) ht.le fun r hr => ?_]
    · exact hn
    · rw [← trev_vrev_eqOn (W := drive κ B₁ ω) (by simp [drive, hB₁0]) ht.le r hr]
      simp only [ArcDriver.trev]
      rw [hW ⟨by linarith [hr.2], by linarith [hr.1]⟩, hW ⟨ht.le, le_rfl⟩]
  -- transfer to the zipped side
  have hl : P.map (fun ω => b1Data (zipCapDown (Real.sqrt κ) t (ofFun (h0rev κ) + X ω,
      drive κ B ω))) = P.map (fun ω => b1Data (ofFun (h0rev κ) + X ω, drive κ B ω)) :=
    b1_full κ hκ P B X hB hX hind ht
  have hcN := ae_mem_of_map_eq (hAm.inter hNm) (aemeasurable_b1Data_c κ hB hX)
    (aemeasurable_b1Data_unzip κ hκ hB hX hind ht) hl.symm (hyN.mono fun _ h => h.1)
  refine ⟨Vp, hVc, hV0, hVm, A ∩ N, hAm.inter hNm, fun x hx => ⟨fun r hr =>
    (hEq _ hx.1 hr).trans (hVeq _ hx.1 hr).symm, hx.2⟩, hyN, hcN⟩

/-- **COR15-LAST (1): `Cor15ZcReadStmt`**, from Theorem 1.3 and Rohde–Schramm. -/
theorem cor15ZcRead (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    Cor15ZcReadStmt κ t P B X := by
  obtain ⟨Vp, hVc, hV0, hVm, A, -, hdet, -, hcA⟩ :=
    exists_readVp h13 hRSS hκ hκ4 hB hX hind ht
  refine ⟨Vp, hVc, hV0, hVm, ?_⟩
  filter_upwards [hcA] with ω hA
  exact hdet (ofFun (h0rev κ) + X ω, drive κ B ω) hA

/-- **COR15-LAST: `hZc`** (the a.e.-measurability of `mod0Data ∘ Z_t ∘ c`). -/
theorem aemeasurable_mod0Data_zipCapUp_c (h13 : theorem1_3)
    (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    {t : ℝ} (ht : 0 < t) :
    AEMeasurable (fun ω => mod0Data (zipCapUp (Real.sqrt κ) t
      (ofFun (h0rev κ) + X ω, drive κ B ω))) P :=
  aemeasurable_mod0Data_zipCapUp_c_of_read hB hX ht
    (cor15ZcRead h13 hRSS hκ hκ4 hB hX hind ht)

end Cor15Group
end QuantumZipper
