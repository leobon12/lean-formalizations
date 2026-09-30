import QuantumZipper.Proofs.Zipper.LocLenR6fWire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6f (5): strict monotonicity of the `P_*` open-arc length `L⁻` without a
log-shift finiteness input

`lenStrictMonoArc_of_weight_baseFinite`: `LenStrictMonoArcStmt` from `YMergeOffTipStmt`, the
open-arc log-shift weight and X1 (`BaseFin.BaseFiniteStmt`), with no finiteness statement for
general log-shifted fields (`LogShiftLenFiniteArcStmt`). Argument (Sheffield arXiv:1012.4797 p. 70,
"strictly increasing"): along the capacity flow the unscaled wedge length is `ν(0,t]` with
`ν = w · μ`, `w > 0` on `(0,∞)` and `μ` the `Γ⁰` open-arc length measure, which charges every
interval (`lenStrictMonoCfgArc_holds`); so the new piece `ν(s,t]` is positive and
`L⁻_t = L⁻_s + ν(s,t] > L⁻_s` as soon as `L⁻_s < ∞`, which holds at all times by R6g
(`lenFiniteArc_of_baseFinite`, X1 + the wedge cocycle) and additivity
(`ae_unzipLengthsArc_lt_top_all`).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- A positive weight integrates positively over a charged piece (deterministic). -/
theorem lintegral_Ioc_pos {μ : Measure ℝ} {w : ℝ → ℝ≥0∞} (hw : Measurable w)
    (hpos : ∀ x : ℝ, 0 < x → w x ≠ 0) {s t : ℝ} (hs : 0 ≤ s) (hμ : μ (Ioc s t) ≠ 0) :
    ∫⁻ x in Ioc s t, w x ∂μ ≠ 0 := by
  intro h
  rw [lintegral_eq_zero_iff hw] at h
  apply hμ
  have h2 : ∀ᵐ x ∂(μ.restrict (Ioc s t)), False := by
    filter_upwards [h, ae_restrict_mem measurableSet_Ioc] with x hx hmem
    exact hpos x (lt_of_le_of_lt hs hmem.1) hx
  have h3 := (ae_iff.1 h2)
  simp only [not_false_eq_true, Set.ofPred_true] at h3
  rwa [Measure.restrict_apply MeasurableSet.univ, univ_inter] at h3

/-- **Unscaled wedge: `L⁻` grows strictly where it is finite** (from the weight input). -/
theorem ae_strictMonoFin_unscaled {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hW : LogShiftLenWeightArcStmt) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B'' : ℝ≥0 → Ω → ℝ}
    (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ, 0 ≤ s → s < t →
      (unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) s).1 ≠ ⊤ →
      (unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) s).1 <
        (unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t).1 := by
  refine ae_unscaled_of_logShift hκ hκ4
    (fun c => ∀ s t : ℝ, 0 ≤ s → s < t → (unzipLengthsArc (Real.sqrt κ) c s).1 ≠ ⊤ →
      (unzipLengthsArc (Real.sqrt κ) c s).1 < (unzipLengthsArc (Real.sqrt κ) c t).1) ?_
    hX hA hI hB hIB
  intro Ω₁ _ P₁ _ B X G Z hB1 hX1 hI1 hGZ
  filter_upwards [lenStrictMonoCfgArc_holds κ P₁ B X hκ hκ4 hB1 hX1 hI1,
    ae_gammaZeroArc_rep lenPairCocycleCfgArc_holds lenRegCfgArc_holds hκ hκ4 hB1 hX1 hI1,
    hW κ hκ hκ4 P₁ B X G Z hB1 hX1 hI1 hGZ] with ω hsm hrep hw
  obtain ⟨μm, μp, -, -, e⟩ := hrep
  obtain ⟨w, hwm, hpos, hZ, -⟩ := hw
  intro s t hs hst hfin
  have ht : 0 ≤ t := hs.trans hst.le
  have hZs := congrArg Prod.fst (hZ μm μp e s hs)
  have hZt := congrArg Prod.fst (hZ μm μp e t ht)
  simp only at hZs hZt
  rw [hZs] at hfin ⊢
  rw [hZt]
  -- the `Γ⁰` measure charges `(s,t]`
  have hμ : μm (Ioc s t) ≠ 0 := by
    intro h0
    have h1 := hsm hs ht hst
    simp only at h1
    rw [(congrArg Prod.fst (e s hs)), (congrArg Prod.fst (e t ht))] at h1
    simp only at h1
    rw [show t = s + (t - s) by ring, ursmp_cocycle μm hs (by linarith : 0 ≤ t - s),
      show s + (t - s) = t by ring, h0, add_zero] at h1
    exact lt_irrefl _ h1
  have hsplit : ∫⁻ x in Ioc 0 t, w x ∂μm =
      ∫⁻ x in Ioc 0 s, w x ∂μm + ∫⁻ x in Ioc s t, w x ∂μm := by
    rw [← Ioc_union_Ioc_eq_Ioc hs hst.le, lintegral_union measurableSet_Ioc
      (Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [hsplit]
  exact ENNReal.lt_add_right hfin (lintegral_Ioc_pos hwm hpos hs hμ)

/-- **`LenStrictMonoArcStmt` from `YMergeOffTipStmt`, the log-shift weight and X1.** -/
theorem lenStrictMonoArc_of_weight_baseFinite (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hW : LogShiftLenWeightArcStmt) (hX1 : BaseFin.BaseFiniteStmt) : LenStrictMonoArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  have hfinAll := ae_unzipLengthsArc_lt_top_all (lenPairCocycleArc_of_weight hYO hW)
    (lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_weight hW)) κ P' Y B' hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ :=
    WedgeUnzip.pStarRealizeStmt_holds κ P' Y B' hP
  obtain ⟨hκ, hκ4, -⟩ := hP
  have himp : ∀ᵐ ω ∂P', (∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1 < ⊤ ∧
      (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).2 < ⊤) →
      StrictMonoOn (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.pcfg κ Y B' ω) t).1) (Ici 0) := by
    refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
    filter_upwards [hae, ae_strictMonoFin_unscaled hκ hκ4 hW hX hA hI hB hIB,
      ae_pstar_arc hκ hκ4 (unscaledB3dLoc_of_yMergeOffTip hYO)
        (unscaledFlowCoreOff_of_yMergeOffTip hYO) hX hA hI hB hIB] with ω hRω hmono hflow hfin
    obtain ⟨havg, hcfg⟩ := hRω
    obtain ⟨hapos, hfl⟩ := hflow
    obtain ⟨ht, -⟩ := hfl _ _ havg hcfg
    intro s hs t ht' hst
    have hfs := (hfin s hs).1
    show (unzipLengthsArc _ (Y ω.1, drive κ B' ω.1) s).1 <
      (unzipLengthsArc _ (Y ω.1, drive κ B' ω.1) t).1
    change (unzipLengthsArc _ (Y ω.1, drive κ B' ω.1) s).1 < ⊤ at hfs
    rw [ht s hs] at hfs ⊢
    rw [ht t ht']
    exact hmono _ _ (mul_nonneg (sq_nonneg _) hs)
      (mul_lt_mul_of_pos_left hst (pow_pos hapos 2)) hfs.ne
  filter_upwards [himp, hfinAll] with ω h hf
  exact h hf

end LocLen
end QuantumZipper
