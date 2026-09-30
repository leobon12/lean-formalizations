import QuantumZipper.Proofs.Thm14.RemovableDoubledHull
import QuantumZipper.Proofs.Thm14.DriverSide

/-!
# OPTB-SWITCH (conditional form): the Theorem 1.4 consumers under Option B

DECISIONS D6, TASKS §4 "EXT-JS / D6" (OPTB-SWITCH). The consumers of `Thm14/FromThm13`,
`Thm14/WeldingData`, `Thm14/GoodDriverSet` and `Thm14/DriverSide` take the pair
`(hRSH : Blueprint.RohdeSchrammHolder) (hJS : Blueprint.JonesSmirnovRemovable)` only to know that
the doubled reverse SLE hull is almost surely conformally removable. Here each of them is
restated with that pair replaced by the hypotheses `hC0 : JS.C0Stmt`, `hC1 : JS.C1Stmt` (the
blueprint statements of EXT-JS nodes C0 and C1, still being proved) together with
`Blueprint.RevMapCaratheodory` (added where missing) and `Blueprint.RohdeSchrammSimple`;
removability comes from `JS.ae_removable_doubledHull_optB` and the Hölder input from
`RS.revMapHolder` (Rohde–Schramm, Ann. of Math. 161 (2005), Thm 5.2). The proofs are those of the
original files with this single change; the original files are left untouched.

Once C0 and C1 are proved, the hypotheses `hC0 hC1` are discharged by one line each.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace Thm14OptB

open Thm14Determination Thm14WeldingData Thm14GoodDriverSet Thm14FromThm13

/-- Option B form of `Thm14WeldingData.ae_good_drive`. -/
theorem ae_good_drive (hC0 : JS.C0Stmt) (hC1 : JS.C1Stmt) (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ} (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 ∧
      IsSimpleCurveHull (revHull (drive κ B ω) T) ∧
      IsConformallyRemovable (closure (revHull (drive κ B ω) T) ∪
        conj '' closure (revHull (drive κ B ω) T)) := by
  filter_upwards [ae_isSimpleCurveHull_revHull hRSS hκ0 hκ4 hT P B hB,
    JS.ae_removable_doubledHull_optB hC0 hC1 hCar hRSS κ hκ0 hκ4 T hT P B hB, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hs hrem hc h0
  exact ⟨continuous_drive hc, by simp [drive, h0], hs, hrem⟩

/-- Option B form of `Thm14GoodDriverSet.ae_goodDriver`. -/
theorem ae_goodDriver (hC0 : JS.C0Stmt) (hC1 : JS.C1Stmt) (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ GoodDriver T (drive κ B ω) := by
  have hB' := isBrownianReal_revBM hB T.toNNReal
  filter_upwards [ae_good_drive hC0 hC1 hCar hRSS hκ0 hκ4 hT P B hB,
    hRSS κ hκ0 hκ4.le P _ hB', hB'.cont] with ω ⟨hc, h0, hK, hrem⟩ ⟨hchord, hhull⟩ hc'
  refine ⟨hc, h0, hK, hrem, _, hchord, fun s hs => ?_⟩
  rw [← hhull s hs.1]
  refine fwdHull_eq_of_eqOn (by fun_prop) (continuous_drive hc') hs.1 fun r hr => ?_
  exact drive_revBM B ω ⟨hr.1, hr.2.trans hs.2⟩

/-- Option B form of `Thm14GoodDriverSet.exists_goodDriverSet`. -/
theorem exists_goodDriverSet (hC0 : JS.C0Stmt) (hC1 : JS.C1Stmt)
    (hCar : Blueprint.RevMapCaratheodory) (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ} (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ G : Set C(Icc (0 : ℝ) T, ℝ), MeasurableSet G ∧
      (∀ g ∈ G, GoodDriver T (extIccPath hT.le g)) ∧
      ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ Thm14WeldingData.pathC T (drive κ B ω) ∈ G := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB'B : IsBrownianReal B' P :=
    { toIsPreBrownianReal := hB.toIsPreBrownianReal.congr fun t => by
        filter_upwards [hB'eq] with ω hω using (hω t).symm
      cont := ae_of_all _ hB'c }
  set g := CharFun.pathC T B' hB'c with hg_def
  have hg : Measurable g := CharFun.measurable_pathC T hB'm hB'c
  set μ := P.map g with hμ
  have : IsProbabilityMeasure μ := inferInstance
  -- the good paths form a `μ`-conull set
  have hglue := isBrownianReal_glue T hT.le hB'B hB'm hB'c
  have hae0 := ae_goodDriver hC0 hC1 hCar hRSS hκ0 hκ4 hT (μ.prod P) _ hglue
  have hae1 : ∀ᵐ f ∂μ, GoodDriver T (CharFun.Wof κ T hT.le f) := by
    have h := Measure.ae_ae_of_ae_prod (p := fun x => GoodDriver T (CharFun.Wof κ T hT.le x.1))
      (hae0.mono fun x ⟨hc, hgood⟩ => goodDriver_congr hT.le hc
        (CharFun.continuous_Wof κ T hT.le x.1) (drive_glue_eqOn hT.le κ B' x) hgood)
    filter_upwards [h] with f hf
    exact hf.exists.choose_spec
  set G₀ := (toMeasurable μ {f | ¬ GoodDriver T (CharFun.Wof κ T hT.le f)})ᶜ with hG₀
  have hG₀m : MeasurableSet G₀ := (measurableSet_toMeasurable _ _).compl
  have hG₀good : ∀ f ∈ G₀, GoodDriver T (CharFun.Wof κ T hT.le f) := fun f hf => by
    by_contra h
    exact hf (subset_toMeasurable _ _ h)
  have hG₀ae : ∀ᵐ f ∂μ, f ∈ G₀ := by
    refine compl_mem_ae_iff.2 ?_
    rw [measure_toMeasurable]
    exact ae_iff.1 hae1
  have hG₀P : ∀ᵐ ω ∂P, g ω ∈ G₀ := (ae_map_iff hg.aemeasurable hG₀m).1 hG₀ae
  -- rescale by `√κ`
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ0
  refine ⟨(fun h : C(Icc (0 : ℝ) T, ℝ) => (Real.sqrt κ)⁻¹ • h) ⁻¹' G₀,
    (continuous_const_smul _).measurable hG₀m, fun h hh => ?_, ?_⟩
  · refine goodDriver_congr hT.le (CharFun.continuous_Wof κ T hT.le _)
      (continuous_extIccPath hT.le h) (fun r _ => ?_) (hG₀good _ hh)
    simp only [CharFun.Wof, extIccPath, ContinuousMap.smul_apply, smul_eq_mul]
    field_simp
  · filter_upwards [hG₀P, hB'eq, hB.cont] with ω hω heq hc
    have hdc : Continuous (drive κ B ω) := continuous_drive hc
    refine ⟨hdc, ?_⟩
    have hpath : (Real.sqrt κ)⁻¹ • Thm14WeldingData.pathC T (drive κ B ω) = g ω := by
      ext x
      simp only [Thm14WeldingData.pathC, hdc, dite_true, ContinuousMap.smul_apply,
        ContinuousMap.coe_mk, smul_eq_mul, hg_def, CharFun.pathC, drive, heq]
      field_simp
    show (Real.sqrt κ)⁻¹ • Thm14WeldingData.pathC T (drive κ B ω) ∈ G₀
    rw [hpath]
    exact hω

/-- Option B form of `Thm14DriverSide.exists_driverGraph`. -/
theorem exists_driverGraph (hC0 : JS.C0Stmt) (hC1 : JS.C1Stmt)
    (hCar : Blueprint.RevMapCaratheodory) (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ G' : Set ((ℝ × (ℚ → ℝ)) × (ℚ → ℝ)), MeasurableSet G' ∧ IsPartialGraph G' ∧
      ∀ᵐ ω ∂P, (weldingData (drive κ B ω) T, sampleDrive T (drive κ B ω)) ∈ G' := by
  obtain ⟨G, hGm, hgood, hae⟩ := exists_goodDriverSet hC0 hC1 hCar hRSS hκ0 hκ4 hT P B hB
  exact exists_weldingGraph_of_goodSet hCar hT hGm
    (fun f hf => ⟨(hgood f hf).1, (hgood f hf).2.1⟩)
    (Thm14DriverSide.injOn_weldingDataC_of_good hCar hT hgood) P (drive κ B) hae

/-- Option B form of `Thm14DriverSide.exists_measurable_driver_of_weldingData`: the driver is
almost surely a measurable function of the welding data. -/
theorem exists_measurable_driver_of_weldingData (hC0 : JS.C0Stmt) (hC1 : JS.C1Stmt)
    (hCar : Blueprint.RevMapCaratheodory) (hRSS : Blueprint.RohdeSchrammSimple) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ}
    (hT : 0 < T) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ F : ℝ × (ℚ → ℝ) → (ℝ → ℝ), Measurable F ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) T, F (weldingData (drive κ B ω) T) t = drive κ B ω t := by
  obtain ⟨G', hG'm, hG'g, hmem⟩ := exists_driverGraph hC0 hC1 hCar hRSS hκ0 hκ4 hT P B hB
  obtain ⟨F₀, hF₀, hF₀ae⟩ := exists_measurable_ae_eq_of_partialGraph P hG'm hG'g
    (fun ω => weldingData (drive κ B ω) T) (fun ω => sampleDrive T (drive κ B ω)) hmem
  refine ⟨fun d => recoverDrive (F₀ d), measurable_recoverDrive.comp hF₀, ?_⟩
  filter_upwards [hF₀ae, hB.cont] with ω hω hc t ht
  rw [hω]
  exact recoverDrive_sampleDrive (continuous_drive hc) ht

/-- **Theorem 1.4(a) from Theorem 1.3, Option B** (form of
`Thm14FromThm13.theorem1_4a_of_theorem1_3` with `RohdeSchrammHolder ∧ JonesSmirnovRemovable`
replaced by nodes C0, C1; the Hölder input is `RS.revMapHolder`). -/
theorem theorem1_4a_of_theorem1_3 (h13 : theorem1_3) (hC0 : JS.C0Stmt) (hC1 : JS.C1Stmt)
    (hCar : Blueprint.RevMapCaratheodory) (hRSS : Blueprint.RohdeSchrammSimple)
    (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) : theorem1_4a := by
  intro κ hκ0 hκ4 T hT Ω _ P _ B X hB hX hind
  filter_upwards [h13 κ hκ0 hκ4 T hT P B X hB hX hind,
    JS.ae_removable_doubledHull_optB hC0 hC1 hCar hRSS κ hκ0 hκ4 T hT P B hB,
    ae_isSimpleCurveHull_revHull hRSS hκ0 hκ4 hT P B hB, hReg κ hκ0 hκ4 T hT P B X hB hX hind,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω h13ω hrem hsimple hregω hc h0
  obtain ⟨c1, c2, -⟩ := h13ω
  obtain ⟨hatom, hpos, hfin⟩ := hregω
  have hWc : Continuous (drive κ B ω) := continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  obtain ⟨F, hF⟩ := hCar _ hWc hW0 T hT hsimple
  have hEq := weldingHom_eq_sInf_of_car hWc hT hF hatom hpos hfin c1
    (fun xm xp h1 h2 h3 h4 => c2 xm xp h1 h2 h3 (Set.mem_insert_of_mem _ h4))
  have hne : (revHull (drive κ B ω) T).Nonempty := by
    obtain ⟨γ, -, -, -, -, hK⟩ := id hsimple
    exact ⟨γ 1, by rw [hK]; exact ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩⟩
  refine ⟨⟨zeroMinus_neg_of_car hF hne, fun s hs => hEq s hs⟩, ?_⟩
  intro T' hT' W' hW' hW'0 hK' hzm hweld
  refine revHull_eq_of_welding_eq hCar hWc hW' hW0 hW'0 hT hT' hsimple hK'
    hzm.symm ?_ hrem
  intro s hs
  rw [hEq s hs, hweld s hs]
  rfl

end Thm14OptB

end QuantumZipper
