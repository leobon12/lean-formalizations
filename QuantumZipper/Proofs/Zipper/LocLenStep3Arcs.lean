import QuantumZipper.Proofs.Zipper.LocLenStep3Defs
import QuantumZipper.Proofs.Zipper.LSWArcsStage
import QuantumZipper.Proofs.Zipper.LogShiftW2Trace
import QuantumZipper.Proofs.Zipper.XFlowRC3Raw
import QuantumZipper.Proofs.Zipper.LogShiftW2Cap
import QuantumZipper.Proofs.Zipper.LogShiftWRed
import QuantumZipper.Proofs.Zipper.LocLenPairCfgMain
import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Zipper.LocLenB5ULocal
import QuantumZipper.Proofs.Zipper.LocLenBridge
import QuantumZipper.Proofs.Zipper.LocLenRules
import QuantumZipper.Proofs.Zipper.E4GridMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R7a-G: `Step3GammaArcsStmt` (stage geometry of the `Γ⁰` picture, open arcs)

`step3GammaArcs_holds : Step3GammaArcsStmt` (no hypothesis). Copy of the first clause
(the `u = 0` stage) of `F1.logShiftWArcsStmt_of_cfg` (LSWArcsMain.lean), with open arcs:

* the stage measure `qBoundaryMeasureOn γ y_t (offSet W t)ᶜ` is the atomless local limit `ν_t`
  of `h⁰_t = y_t` off the tip (`unifLocalStmt_holds`), read on `(offSet)ᶜ` (the finite set
  `offSet` is `ν_t`-null);
* the restarted stage length `(unzipLengthsArc (zipCapDown v cfg) (t − v)).1` is
  `ν_t (A v, 0)` by the `Γ⁰` field cocycle (`RegUnif.capCocycleRegAllStmt_holds`) and the local
  reading `arcLen_eq_of_isVagueLimitOnR`; with the open-arc pair cocycle
  (`lenPairCocycleCfgArc_holds`) this gives `L_v + ν_t[A v, 0] = L_t`;
* finiteness of the lengths from `b5UniformArcStmt_holds` (bounded arcs of the locally finite
  global measure of `h⁰_T`), continuity of `v ↦ L_v` from atomlessness of `ν_t`;
* the deterministic stage bookkeeping `F1.lswa_stage` with `u = 0`.

Paper: Sheffield arXiv:1012.4797 §1.4 (lengths of the two sides of `η[0,t]` as boundary
measures of the unzipped field), §5.4 pp. 70–72, p. 56; Berestycki–Powell arXiv:2404.16642
Def 8.12 p. 281. Own bookkeeping (as in LSWArcsMain.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- A local vague limit on `U` restricts to every open `V ⊆ U`. -/
theorem isVagueLimitOnR_mono_s3a {γ : ℝ} {x : FieldSample} {U V : Set ℝ} {ν : Measure ℝ}
    (hν : IsVagueLimitOnR U (bdryApprox γ x) ν) (hV : IsOpen V) (hVU : V ⊆ U) :
    IsVagueLimitOnR V (bdryApprox γ x) (ν.restrict V) := by
  obtain ⟨-, hK, ht⟩ := hν
  refine ⟨by rw [Measure.restrict_apply hV.measurableSet.compl]; simp,
    fun K hKc hKV => (Measure.restrict_apply_le _ _).trans_lt (hK K hKc (hKV.trans hVU)),
    fun f hf hfc hfV => ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun t ht => image_eq_zero_of_notMem_tsupport fun h => ht (hfV h))]
  exact ht f hf hfc (hfV.trans hVU)

/-- Distribution function of an atomless measure, left endpoint fixed. -/
theorem continuousOn_measure_Icc_right_s3a {ν : Measure ℝ} (hν : ∀ x, ν {x} = 0) {a b : ℝ}
    (hfin : ν (Icc a b) ≠ ⊤) : ContinuousOn (fun x => (ν (Icc a x)).toReal) (Icc a b) := by
  have : NullSingletonClass ν := ⟨hν⟩
  have hi : IntegrableOn (fun _ => (1 : ℝ)) (Icc a b) ν := integrableOn_const hfin
  refine (intervalIntegral.continuousOn_primitive_Icc hi).congr fun x _ => ?_
  simp [setIntegral_const, Measure.real]

/-- Distribution function of an atomless measure, right endpoint fixed. -/
theorem continuousOn_measure_Icc_left_s3a {ν : Measure ℝ} (hν : ∀ x, ν {x} = 0) {a b : ℝ}
    (hfin : ν (Icc a b) ≠ ⊤) : ContinuousOn (fun x => (ν (Icc x b)).toReal) (Icc a b) := by
  have : NullSingletonClass ν := ⟨hν⟩
  refine ((continuousOn_const (c := (ν (Icc a b)).toReal)).sub
    (continuousOn_measure_Icc_right_s3a hν hfin)).congr fun x hx => ?_
  have hsplit : ν (Icc a b) = ν (Icc a x) + ν (Icc x b) := by
    rw [← Ico_union_Icc_eq_Icc hx.1 hx.2, measure_union
      (Set.disjoint_left.2 fun y hy hy' => (not_le.2 hy.2) hy'.1) measurableSet_Icc,
      measure_congr (Ico_ae_eq_Icc (μ := ν))]
  have h1 : ν (Icc a x) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono (Icc_subset_Icc le_rfl hx.2))
  have h2 : ν (Icc x b) ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono (Icc_subset_Icc hx.1 le_rfl))
  show _ = (ν (Icc a b)).toReal - (ν (Icc a x)).toReal
  rw [hsplit, ENNReal.toReal_add h1 h2]
  ring

/-- **`Step3GammaArcsStmt` holds.** -/
theorem step3GammaArcs_holds : Step3GammaArcsStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hI
  obtain ⟨δt, -, htrace⟩ := RS.ae_sleTrace_good hB hκ (by linarith)
  have hCC : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ (n : ℝ) + 1 →
      RegEq (zipCapDown (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) u (B2.cfg κ B X ω))).1
        (zipCapDown (Real.sqrt κ) (u + s) (B2.cfg κ B X ω)).1 := by
    rw [ae_all_iff]
    intro n
    filter_upwards [RegUnif.capCocycleRegAllStmt_holds (κ := κ) hB hX hI ((n : ℝ) + 1)
      (by positivity)] with ω h u s hu hs hus
    exact (h u s hu hs hus).1
  have hUL : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1), ∃ ν : Measure ℝ,
      IsVagueLimitOnR ({0}ᶜ) (bdryApprox (Real.sqrt κ) (B2.h0f κ s B X ω)) ν ∧
        ∀ x, ν {x} = 0 := by
    rw [ae_all_iff]
    intro n
    exact unifLocalStmt_holds hκ hκ4 (by positivity) hB hX hI
  have hFin : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) s).1 ≠ ⊤ ∧
        (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) s).2 ≠ ⊤ := by
    rw [ae_all_iff]
    intro n
    filter_upwards [b5UniformArcStmt_holds κ hκ hκ4 ((n : ℝ) + 1) (by positivity) P B X hB hX hI]
      with ω h s hs
    rw [(h s hs).1, (h s hs).2]
    exact ⟨ne_top_of_le_ne_top (E4Grid.qBoundaryMeasure_Icc_lt_top _ _ _ _).ne
        (measure_mono Ioo_subset_Icc_self),
      ne_top_of_le_ne_top (E4Grid.qBoundaryMeasure_Icc_lt_top _ _ _ _).ne
        (measure_mono Ioo_subset_Icc_self)⟩
  filter_upwards [lenPairCocycleCfgArc_holds κ P B X hκ hκ4 hB hX hI,
    F1.lswPosStmt_holds κ hκ hκ4 P B hB, hCC, F1.ae_lsw2_driver_facts hκ hκ4 hB,
    hB.eval_zero_ae_eq_zero, htrace, hUL, hFin] with ω hPω hPosω hCCω hdrv h0 htrω hULω hFinω
  obtain ⟨-, -, -, -, -, hGC⟩ := hdrv
  set γ := Real.sqrt κ with hγ
  set W := drive κ B ω with hWdef
  set L : ℝ → ℝ≥0∞ × ℝ≥0∞ := fun r => unzipLengthsArc γ (B2.cfg κ B X ω) r with hL
  set η : ℝ → ℂ := fun r => trace W (max r 0) with hη
  have hLf : ∀ r : ℝ, 0 ≤ r → (L r).1 ≠ ⊤ ∧ (L r).2 ≠ ⊤ := by
    intro r hr
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact hFinω n r ⟨hr, by linarith⟩
  have hS0 : sideImages W 0 = (0, 0) := by
    rw [← F1.lswPos_zero_drive h0 0]; exact F1.lswPos_self W 0
  have hL0 : L 0 = (0, 0) := by
    simp only [hL, unzipLengthsArc, arcLen]
    rw [show (B2.cfg κ B X ω).2 = W from rfl, hS0]
    simp
  refine ⟨hLf, η, (htrω.2.1.comp_continuous (continuous_id.max continuous_const)
    (fun r => mem_Ici.2 (le_max_right _ _))).measurable, fun t ht => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_ge t
  obtain ⟨ν, hνv, hνa⟩ := hULω n t ⟨ht, by linarith⟩
  have : NullSingletonClass ν := ⟨hνa⟩
  have hyt : B2.h0f κ t B X ω = F2.unzY κ (X ω) W t := by
    rw [B2.h0f_eq_unzippedField]
    show unzippedField _ (ofFun (h0rev κ) + X ω, W) t = _
    rw [F2.h0rev_add_eq]
    rfl
  have hνeq : qBoundaryMeasureOn γ (F2.unzY κ (X ω) W t) (offSet W t)ᶜ = ν := by
    have hsub : (offSet W t)ᶜ ⊆ ({0}ᶜ : Set ℝ) :=
      compl_subset_compl.2 (singleton_subset_iff.2 (by simp [offSet]))
    rw [← hyt, LocalRule.qBoundaryMeasureOn_eq (isClosed_offSet W t).isOpen_compl
      (isVagueLimitOnR_mono_s3a hνv (isClosed_offSet W t).isOpen_compl hsub)]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    simp only [mem_compl_iff, not_not, ofPred_mem_eq]
    exact (((Set.finite_singleton _).insert _).insert _).measure_zero ν
  rw [hνeq]
  -- the restarted stage lengths
  have hlen : ∀ v ∈ Icc 0 t,
      (unzipLengthsArc γ (zipCapDown γ v (B2.cfg κ B X ω)) (t - v)).1 =
          ν (Ioo (F1.lswPos W t v).1 0) ∧
        (unzipLengthsArc γ (zipCapDown γ v (B2.cfg κ B X ω)) (t - v)).2 =
          ν (Ioo 0 (F1.lswPos W t v).2) := by
    intro v hv
    have hr := hCCω n v (t - v) hv.1 (sub_nonneg.2 hv.2) (by linarith)
    rw [add_sub_cancel] at hr
    have havg : avgReg (unzippedField γ (zipCapDown γ v (B2.cfg κ B X ω)) (t - v)) =
        avgReg (B2.h0f κ t B X ω) := by
      rw [B2.h0f_eq_unzippedField]
      funext k z
      exact hr k z
    refine ⟨?_, ?_⟩
    · show arcLen γ (unzippedField γ (zipCapDown γ v (B2.cfg κ B X ω)) (t - v))
        (F1.lswPos W t v).1 0 = _
      rw [arcLen_congr havg]
      exact arcLen_eq_of_isVagueLimitOnR hνv fun x hx => hx.2.ne
    · show arcLen γ (unzippedField γ (zipCapDown γ v (B2.cfg κ B X ω)) (t - v))
        0 (F1.lswPos W t v).2 = _
      rw [arcLen_congr havg]
      exact arcLen_eq_of_isVagueLimitOnR hνv fun x hx => hx.1.ne'
  have hpA : ∀ v ∈ Icc 0 t, (L v).1 + ν (Icc (F1.lswPos W t v).1 0) = (L t).1 := by
    intro v hv
    have h := (hPω v (t - v) hv.1 (sub_nonneg.2 hv.2)).1
    rw [add_sub_cancel] at h
    rw [measure_Icc_eq_Ioo_of_noAtoms (hνa _) (hνa _), ← (hlen v hv).1]
    exact h.symm
  have hpB : ∀ v ∈ Icc 0 t, (L v).2 + ν (Icc 0 (F1.lswPos W t v).2) = (L t).2 := by
    intro v hv
    have h := (hPω v (t - v) hv.1 (sub_nonneg.2 hv.2)).2
    rw [add_sub_cancel] at h
    rw [measure_Icc_eq_Ioo_of_noAtoms (hνa _) (hνa _), ← (hlen v hv).2]
    exact h.symm
  obtain ⟨hac, hbc, ham, hbm, htr⟩ := hPosω t ht
  have hself := F1.lswPos_self W t
  have h0t : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht⟩
  have htt : t ∈ Icc 0 t := ⟨ht, le_rfl⟩
  -- continuity of the lengths
  have hAmap : MapsTo (fun v => (F1.lswPos W t v).1) (Icc 0 t) (Icc (F1.lswPos W t 0).1 0) :=
    fun v hv => ⟨ham.monotoneOn h0t hv hv.1, by
      have := ham.monotoneOn hv htt hv.2; rwa [hself] at this⟩
  have hBmap : MapsTo (fun v => (F1.lswPos W t v).2) (Icc 0 t) (Icc 0 (F1.lswPos W t 0).2) :=
    fun v hv => ⟨by have := hbm.antitoneOn hv htt hv.2; rwa [hself] at this,
      hbm.antitoneOn h0t hv hv.1⟩
  have hfA : ν (Icc (F1.lswPos W t 0).1 0) ≠ ⊤ := ne_top_of_le_ne_top (hLf t ht).1
    (by rw [← hpA 0 h0t]; exact le_add_self)
  have hfB : ν (Icc 0 (F1.lswPos W t 0).2) ≠ ⊤ := ne_top_of_le_ne_top (hLf t ht).2
    (by rw [← hpB 0 h0t]; exact le_add_self)
  have hc1 : ContinuousOn (fun v => (L v).1.toReal) (Icc 0 t) := by
    refine ((continuousOn_const (c := (L t).1.toReal)).sub ((continuousOn_measure_Icc_left_s3a hνa hfA).comp hac
      hAmap)).congr fun v hv => ?_
    have h := hpA v hv
    have hv1 : (L v).1 ≠ ⊤ := ne_top_of_le_ne_top (hLf t ht).1 (by rw [← h]; exact le_self_add)
    have hv2 : ν (Icc (F1.lswPos W t v).1 0) ≠ ⊤ :=
      ne_top_of_le_ne_top (hLf t ht).1 (by rw [← h]; exact le_add_self)
    have e := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add hv1 hv2] at e
    show (L v).1.toReal = (L t).1.toReal - (ν (Icc (F1.lswPos W t v).1 0)).toReal
    linarith
  have hc2 : ContinuousOn (fun v => (L v).2.toReal) (Icc 0 t) := by
    refine ((continuousOn_const (c := (L t).2.toReal)).sub ((continuousOn_measure_Icc_right_s3a hνa hfB).comp hbc
      hBmap)).congr fun v hv => ?_
    have h := hpB v hv
    have hv1 : (L v).2 ≠ ⊤ := ne_top_of_le_ne_top (hLf t ht).2 (by rw [← h]; exact le_self_add)
    have hv2 : ν (Icc 0 (F1.lswPos W t v).2) ≠ ⊤ :=
      ne_top_of_le_ne_top (hLf t ht).2 (by rw [← h]; exact le_add_self)
    have e := congrArg ENNReal.toReal h
    rw [ENNReal.toReal_add hv1 hv2] at e
    show (L v).2.toReal = (L t).2.toReal - (ν (Icc 0 (F1.lswPos W t v).2)).toReal
    linarith
  have hE : ∀ v ∈ Ioc 0 t, F2.extInv W t ((F1.lswPos W t v).1 : ℂ) = η v ∧
      F2.extInv W t ((F1.lswPos W t v).2 : ℂ) = η v := by
    intro v hv
    simp only [hη, max_eq_left hv.1.le]
    exact htr v hv
  have hE' : Continuous (fun x : ℝ => F2.extInv W t x) :=
    (hGC t ht).comp_continuous Complex.continuous_ofReal
      (fun x => show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp)
  have h := F1.lswa_stage (ν := ν)
    (A := fun v => (F1.lswPos W t v).1) (B := fun v => (F1.lswPos W t v).2) (u := 0) (s := t)
    le_rfl ht (zero_add t) hac hbc ham hbm (by rw [hself]) (by rw [hself]) (hLf t ht).1
    (hLf t ht).2 hc1 hc2 hpA hpB (M := L)
    (fun r _ _ => ⟨by rw [show (L 0).1 = 0 from congrArg Prod.fst hL0, zero_add, zero_add],
      by rw [show (L 0).2 = 0 from congrArg Prod.snd hL0, zero_add, zero_add]⟩)
    (O := sideImages W t) (by rw [F1.lswPos_zero_drive h0]) hE'.measurable hE
  simpa only [zero_add] using h

end LocLen
end QuantumZipper
