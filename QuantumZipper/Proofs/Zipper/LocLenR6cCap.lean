import QuantumZipper.Proofs.Zipper.LocLenCanonRegCore
import QuantumZipper.Proofs.Zipper.LocLenPosMain
import QuantumZipper.Proofs.Thm18.G4B3CapFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6c: the capacity field cocycle and the restarted side images at `P_*` samples

Sheffield, arXiv:1012.4797, §1.4 (the capacity zipper is a flow; the left side of `η[0,t₀]` is
mapped at time `t` onto an initial segment of `[O⁻_t, 0]`, the left side of `η[t₀,t]` onto the
rest) and §5.4 pp. 69–72; Berestycki–Powell arXiv:2404.16642 Def 8.12 p. 281.

* `pStarCapRegOff_of_core`: copy of `Thm18Asm.G4Core.pStarCapReg_of_core` (G4B3CapFree.lean:61)
  with the global flow core (`F1.UnscaledFlowRegStmt`, which needs the global X-G) replaced by
  the off-root-image core `UnscaledFlowCoreOffStmt` (R6b-2); only its scale-consistency and RC3
  clauses are read, as in the original. Closed form `pStarCapRegOff_of_yMergeOffTip`.
* `ae_pstar_zeroMinus_facts`: the restarted left side image. At a `P_*` sample, for
  `0 ≤ t₀ < T`, unzipping `zipCapDown t₀ c` by `T − t₀` has left side image
  `m = 0₋^{vrev W T}(T − t₀)` with `O⁻_T ≤ m < 0` (copy of the `0₊` half of
  `Thm18Asm.G4Core.ae_zeroPlus_facts` and of `ae_sideImages_zipCapDown`, for `0₋`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open WedgeUnzip Thm18Asm.G4Core

/-- **The capacity field cocycle at every `P_*` sample, goodness off the root images only**
(copy of `Thm18Asm.G4Core.pStarCapReg_of_core`). -/
theorem pStarCapRegOff_of_core (hR : PStarRealizeStmt) (hRC : F1.WedgeFlowRC3Stmt)
    (hFR : UnscaledFlowCoreOffStmt) (hE : WedgeExactAllStmt) (hC : WedgeContinuumStmt) :
    ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
      ∀ᵐ ω ∂P', Thm18Asm.UnzipCapRegData (Real.sqrt κ) (Y ω, drive κ B' ω) := by
  intro κ Ω' _ P' _ Y B' hPS
  obtain ⟨hκ, hκ4, -⟩ := id hPS
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ := hR κ P' Y B' hPS
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  refine ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hRC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hFR κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hE κ hκ hκ4 _ X' A B'' hX hA hI hB hIB, hC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hRω hrc hfr hEω hCω hspec hc h0
  obtain ⟨havg, hcfg⟩ := hRω
  set γ := Real.sqrt κ with hγdef
  set Z := F2.zU γ X' A ω with hZ
  set W := drive κ B'' ω with hWdef
  set a := scaleParam γ Z with ha_def
  have ha : 0 < a := hspec.1
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  have hWmax := F2.drive_max κ B'' ω
  have hB3 : ∀ t : ℝ, 0 ≤ t → RegEq (unzippedField γ (canonConfig γ (Z, W)) t)
      (rescale (unzippedField γ (Z, W) (a ^ 2 * t)) (Qc γ) a) := by
    intro t ht
    have has : 0 ≤ a ^ 2 * t := mul_nonneg (sq_nonneg _) ht
    have hraw := unzippedField_canonConfig_fc hW hW0 hWmax ha ht (fun d r hr => by
        rw [B3d.canonConfig_snd_of_max hWmax]
        have hC' := hCω.2 _ has ((a : ℂ) * d) _ (mul_pos ha hr)
        exact scaleConsistent_of_continuum hCω.1 _ hW hW0 ha ht d hr hC'.1 hC'.2)
      (hEω _ has)
    exact S5.FieldShift.regEq_of_fc fun d _ r hr => hraw d r hr
  have hU : ∀ v t : ℝ, 0 ≤ v → 0 ≤ t → RegEq (unzippedField γ (zipCapDown γ v (Z, W)) t)
      (unzippedField γ (Z, W) (v + t)) := fun v t hv ht =>
    F1.regEq_of_fc_Hbar fun d hd r hr =>
      F1.flow_raw_cocycle_of_rc3 γ Z hW hW0 hv ht d hr (hrc v t hv ht d hd r hr)
  intro t u ht hu
  have e1 : zipCapDown γ t (Y ω.1, drive κ B' ω.1) = zipCapDown γ t (canonConfig γ (Z, W)) := by
    rw [hcfg]
    simp only [zipCapDown, Factorization.coordChange_congr havg]
  have e2 : unzippedField γ (Y ω.1, drive κ B' ω.1) (t + u) =
      unzippedField γ (canonConfig γ (Z, W)) (t + u) := by
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  rw [e1, e2]
  set c'' := zipCapDown γ (a ^ 2 * t) (Z, W) with hc''
  have hW'' : Continuous c''.2 :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hW''0 : c''.2 0 = 0 := by simp [hc'', zipCapDown]
  have e3 : zipCapDown γ t (canonConfig γ (Z, W)) =
      (unzippedField γ (canonConfig γ (Z, W)) t, fun r => c''.2 (a ^ 2 * r) / a) :=
    Prod.ext rfl (F1.zipCapDown_canonConfig_snd Z W ht)
  have e4 : unzippedField γ (unzippedField γ (canonConfig γ (Z, W)) t,
        fun r => c''.2 (a ^ 2 * r) / a) u =
      unzippedField γ (rescale c''.1 (Qc γ) a, fun r => c''.2 (a ^ 2 * r) / a) u :=
    Factorization.coordChange_congr (B3d.avgReg_eq_of_regEq (hB3 t ht)) _ _
  obtain ⟨hsc, hexact, -⟩ := hfr t u ht hu
  have h1 : RegEq (unzippedField γ (rescale c''.1 (Qc γ) a, fun r => c''.2 (a ^ 2 * r) / a) u)
      (rescale (unzippedField γ c'' (a ^ 2 * u)) (Qc γ) a) :=
    F1.regEq_unzippedField_rescaled hW'' hW''0 ha hu hsc hexact
  have h2 : RegEq (rescale (unzippedField γ c'' (a ^ 2 * u)) (Qc γ) a)
      (rescale (unzippedField γ (Z, W) (a ^ 2 * (t + u))) (Qc γ) a) := by
    have := hU (a ^ 2 * t) (a ^ 2 * u) (mul_nonneg (sq_nonneg _) ht) (mul_nonneg (sq_nonneg _) hu)
    rw [← mul_add] at this
    exact regEq_rescale_congr this _ _
  rw [e3, e4]
  exact regEq_trans' h1 (regEq_trans' h2 (regEq_symm' (hB3 (t + u) (add_nonneg ht hu))))

/-- **Closed form**: the `P_*` capacity field cocycle from the offset merging input only. -/
theorem pStarCapRegOff_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
      ∀ᵐ ω ∂P', Thm18Asm.UnzipCapRegData (Real.sqrt κ) (Y ω, drive κ B' ω) :=
  pStarCapRegOff_of_core pStarRealizeStmt_holds
    (wedgeFlowRC3Stmt_of_xOff (xGoodOffAll_of_yMergeOffTip hYO) xContinuumStmt_holds
      F1.xFlowRC3Stmt_holds F1.XFlowC.xFlowContStmt_holds)
    (unscaledFlowCoreOff_of_yMergeOffTip hYO) (wedgeExactAll_of_yMergeOffTip hYO)
    (wedgeContinuum_of_x WDec.wedgeDecompStmt_holds xContinuumStmt_holds)

/-- **The restarted left side image at a `P_*` sample** (a.s., all times): for `0 ≤ t₀ < T`,
`m = 0₋^{vrev W T}(T − t₀)` is the left side image of `zipCapDown t₀ c` unzipped by `T − t₀`,
`O⁻_T ≤ m < 0`, and `r ↦ 0₋^{vrev W T}(r)` is continuous on `[0,T]`, `0` at `0`, and equal
to `O⁻_T` at `T`. -/
theorem ae_pstar_zeroMinus_facts {κ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → FieldSample} {B' : ℝ≥0 → Ω' → ℝ}
    (hP : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', ∀ T : ℝ, 0 < T →
      ContinuousOn (zeroMinus (B2.vrev (drive κ B' ω) T)) (Icc 0 T) ∧
      StrictAntiOn (zeroMinus (B2.vrev (drive κ B' ω) T)) (Icc 0 T) ∧
      zeroMinus (B2.vrev (drive κ B' ω) T) 0 = 0 ∧
      (sideImages (drive κ B' ω) T).1 = zeroMinus (B2.vrev (drive κ B' ω) T) T ∧
      ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < T →
        (sideImages (zipCapDown (Real.sqrt κ) t₀ (Y ω, drive κ B' ω)).2 (T - t₀)).1 =
          zeroMinus (B2.vrev (drive κ B' ω) T) (T - t₀) := by
  have hS := F1.thm18Setting_of_pstar hP
  have e : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hP.1.le
  have hκ : 0 < κ := hP.1
  have hκ4 : κ ≤ 4 := hP.2.1.le
  have hB : IsBrownianReal B' P' := hS.2.2.1
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4 P'
      B' hB, RS.ae_real_alive hB hκ hκ4, hB.cont, hB.eval_zero_ae_eq_zero,
    Thm18Asm.G4Core.ae_sideImages_zipCapDown hS] with ω hK hal hc h0 hsi T hT
  set W := drive κ B' ω with hWdef
  have hW : Continuous W := by
    rw [hWdef]; unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
  simp only [B2.Vr] at hK
  have hVc : Continuous (B2.vrev W T) := B2.continuous_vrev hW T
  have hV0 : B2.vrev W T 0 = 0 := B2.vrev_zero hT.le
  refine ⟨B5.continuousOn_zeroMinus_Icc hVc hV0 hT (hK T hT),
    B5.strictAntiOn_zeroMinus hVc hV0 hT (hK T hT), B5.zeroMinus_zero_time hVc hV0,
    B5.sideImages_fst_eq_zeroMinus_vrev hW hW0 hT (hK T hT) fun x hx => hal x hx T hT.le,
    fun t₀ ht₀ hlt => ?_⟩
  have h := (hsi T (T - t₀) ⟨sub_pos.2 hlt, by linarith⟩).1
  simp only [wedgeConfig, e, sub_sub_cancel] at h
  exact h

end LocLen
end QuantumZipper
