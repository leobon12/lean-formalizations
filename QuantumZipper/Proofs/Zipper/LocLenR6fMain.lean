import QuantumZipper.Proofs.Zipper.LocLenR6fDefs
import QuantumZipper.Proofs.Zipper.LocLenCanonRegMain
import QuantumZipper.Proofs.Zipper.LocLenF2Unscaled
import QuantumZipper.Proofs.Zipper.LocLenPairCfgMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6f (2): from the unscaled wedge to `P_*`, open arcs

Open-arc copies of the `P_*` bridges of F1KappaGuard.lean (`lenPairCocycleStmt_of_unscaled'`,
:219, and `lenStrictMonoStmt_of_unscaled'`, :146, used by `lenStrictMonoStmt_of_logShift`, :310).
Instead of the global B3(d) along the flow (`F1.UnscaledFlowLenScaleStmt`) we read the open-arc
lengths of the `P_*` configuration unzipped by `u` directly as the unscaled open-arc lengths at
the times `a² u`, `a² s` (`ae_pstar_flow_arc`), with the local wedge inputs of the proved
`LocLen.lenCanonRegArc_of_parts` (`UnscaledB3dLocStmt`, `UnscaledFlowCoreOffStmt`) and the
geometric fact that the open arcs of `η(U, U+S)` avoid `offSet W (U+S)`
(`arcs_subset_compl_offSet`). The rescaling of open-arc lengths is
`arcLen_rescale_of_hasBdryLimitOn` (Sheffield arXiv:1012.4797 §5.1; B-P arXiv:2404.16642
Def 6.41 p. 229: only the boundary limit on the open arcs is read).

Own bookkeeping (copies of the old proofs with the open-arc lemmas).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- **Scaling of the open-arc lengths for a field good off a set avoiding both arcs**
(`unzipLengthsArc_scale_off` with a general exceptional set `S`). -/
theorem unzipLengthsArc_scale_offS {γ : ℝ} {x x' : FieldSample} {W : ℝ → ℝ} {a t : ℝ}
    {S : Set ℝ} (hγ : 0 < γ) (ha : 0 < a) (ht : 0 ≤ t)
    (hL : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * t) r).re) (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hR : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (a ^ 2 * t) r).re) (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hsub₁ : Ioo (sideImages W (a ^ 2 * t)).1 0 ⊆ Sᶜ)
    (hsub₂ : Ioo 0 (sideImages W (a ^ 2 * t)).2 ⊆ Sᶜ)
    (hgood : IsLQGGoodOff γ (unzippedField γ (x, W) (a ^ 2 * t)) S)
    (hfield : RegEq (unzippedField γ (x', fun s => W (a ^ 2 * s) / a) t)
      (rescale (unzippedField γ (x, W) (a ^ 2 * t)) (Qc γ) a)) :
    unzipLengthsArc γ (x', fun s => W (a ^ 2 * s) / a) t =
      unzipLengthsArc γ (x, W) (a ^ 2 * t) := by
  obtain ⟨l, hl⟩ := hL
  obtain ⟨m, hm⟩ := hR
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hgood
  have hOl : (sideImages (fun s => W (a ^ 2 * s) / a) t).1 = l / a :=
    B3d.sideImages_fst_scale W ha ht hl
  have hOr : (sideImages (fun s => W (a ^ 2 * s) / a) t).2 = m / a :=
    B3d.sideImages_snd_scale W ha ht hm
  have hRl : (sideImages W (a ^ 2 * t)).1 = l := hl.limUnder_eq
  have hRr : (sideImages W (a ^ 2 * t)).2 = m := hm.limUnder_eq
  have hav := B3d.avgReg_eq_of_regEq hfield
  have ha' : a ≠ 0 := ha.ne'
  have e1 : a * (l / a) = l := by field_simp
  have e2 : a * (m / a) = m := by field_simp
  rw [hRl] at hsub₁
  rw [hRr] at hsub₂
  simp only [unzipLengthsArc, hOl, hOr, hRl, hRr]
  rw [arcLen_congr hav, arcLen_congr hav,
    arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν (by rw [e1, mul_zero]; exact hsub₁),
    arcLen_rescale_of_hasBdryLimitOn hreg hγ ha hν (by rw [e2, mul_zero]; exact hsub₂),
    arcLen_eq_of_hasBdryLimitOn hreg hν hsub₁, arcLen_eq_of_hasBdryLimitOn hreg hν hsub₂,
    e1, e2, mul_zero]

/-- **The `P_*` open-arc lengths are the unscaled ones at the time change `s ↦ a² s`, also
along the capacity flow** (deterministic; open-arc replacement of
`F1.ae_unzipLengths_canon_unscaled` and `F1.UnscaledFlowLenScaleStmt`). Inputs: the `P_*`
realization identities, B3(d) off the root images (`UnscaledB3dLocStmt`), the flow core off the
root images (`UnscaledFlowCoreOffStmt`) and aliveness of the restarted drivers. -/
theorem pstar_arc_det {γ : ℝ} (hγ : 0 < γ) {Z Y : FieldSample} {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hWmax : ∀ s, W (max s 0) = W s)
    (ha : 0 < scaleParam γ Z)
    (havg : avgReg Y = avgReg (canonical γ Z))
    (hcfg : canonConfig γ (Z, W) = (canonical γ Z, W'))
    (hD : (∀ t, 0 ≤ t → IsLQGGoodOff γ (unzippedField γ (Z, W) t) (offSet W t)) ∧
      ∀ s, 0 ≤ s → RegEq (unzippedField γ (canonConfig γ (Z, W)) s)
        (rescale (unzippedField γ (Z, W) (scaleParam γ Z ^ 2 * s)) (Qc γ) (scaleParam γ Z)))
    (hC : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → FlowScaleCoreOff γ Z W u s)
    (hal : ∀ u : ℝ, 0 ≤ u → ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s => W (u + max s 0) - W u) (x : ℂ) T v) :
    (∀ t : ℝ, 0 ≤ t → unzipLengthsArc γ (Y, W') t =
        unzipLengthsArc γ (Z, W) (scaleParam γ Z ^ 2 * t)) ∧
      ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
        unzipLengthsArc γ (zipCapDown γ u (Y, W')) s =
          unzipLengthsArc γ (zipCapDown γ (scaleParam γ Z ^ 2 * u) (Z, W))
            (scaleParam γ Z ^ 2 * s) := by
  set a := scaleParam γ Z with ha_def
  have hcc2 : (canonConfig γ (Z, W)).2 = fun r => W (a ^ 2 * r) / a :=
    B3d.canonConfig_snd_of_max hWmax
  have hW' : W' = fun r => W (a ^ 2 * r) / a := by rw [← hcc2, hcfg]
  refine ⟨fun t ht => ?_, fun u s hu hs => ?_⟩
  · have hat : 0 ≤ a ^ 2 * t := mul_nonneg (sq_nonneg a) ht
    rw [unzipLengthsArc_congr_avgReg γ havg, hW']
    have hfield := hD.2 t ht
    have hcc : canonConfig γ (Z, W) = (canonical γ Z, fun r => W (a ^ 2 * r) / a) :=
      Prod.ext rfl hcc2
    rw [hcc] at hfield
    exact unzipLengthsArc_scale_off hγ ha ht (F1.exists_tendsto_fwdMap_left hW hW0 hat)
      (F1.exists_tendsto_fwdMap_right hW hW0 hat)
      ⟨sideImages_fst_nonpos_of_cont hW hW0 hat, sideImages_snd_nonneg_of_cont hW hW0 hat⟩
      (hD.1 _ hat) hfield
  · have hU : 0 ≤ a ^ 2 * u := mul_nonneg (sq_nonneg a) hu
    have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
    set c'' := zipCapDown γ (a ^ 2 * u) (Z, W) with hc''
    have hW'' : Continuous c''.2 :=
      (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
    have hW''0 : c''.2 0 = 0 := by simp [hc'', zipCapDown]
    have e0 := zipCapDown_pstar_eq havg hcfg hu
    have hcore := hC u s hu hs
    have hraw := fun d {r' : ℝ} (hr' : 0 < r') =>
      pstar_flow_fc_off hW ha havg hcfg hu hs (hD.2 u hu) hcore d hr'
    have hf := regEq_of_fc_Hbar (fun d _ r' hr' => hraw d hr')
    rw [e0] at hf ⊢
    have hsub := arcs_subset_compl_offSet hW hW0 hU has (fun x hx => by
      obtain ⟨v, hv⟩ := hal 0 le_rfl x hx (a ^ 2 * u + a ^ 2 * s) (add_nonneg hU has)
      exact ⟨v, isForwardSol_congr_drive (fun s hs => by
        show W (0 + max s 0) - W 0 = W s
        rw [zero_add, max_eq_left hs.1, hW0, sub_zero]) hv⟩)
    exact unzipLengthsArc_scale_offS (x := c''.1) (W := c''.2) hγ ha hs
      (F1.exists_tendsto_fwdMap_left hW'' hW''0 has)
      (F1.exists_tendsto_fwdMap_right hW'' hW''0 has)
      (fun z hz => hsub (Or.inl hz)) (fun z hz => hsub (Or.inr hz)) hcore.2.2 hf

/-- The realization data of `PStarRealizeStmt` give `pstar_arc_det` a.s. on the product
extension. -/
theorem ae_pstar_arc {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hD : UnscaledB3dLocStmt)
    (hC : UnscaledFlowCoreOffStmt) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B'' : ℝ≥0 → Ω → ℝ}
    (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) :
    ∀ᵐ ω ∂P, 0 < scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ∧
      ∀ (Y : FieldSample) (W' : ℝ → ℝ),
      avgReg Y = avgReg (canonical (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω)) →
      canonConfig (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) =
        (canonical (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω), W') →
      (∀ t : ℝ, 0 ≤ t → unzipLengthsArc (Real.sqrt κ) (Y, W') t =
        unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)
          (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2 * t)) ∧
      ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
        unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (Y, W')) s =
          unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ)
            (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2 * u)
            (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω))
            (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2 * s) := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  filter_upwards [(FSMeas.pstar_of_unscaled_fs hκ hκ4 hX hA hI hB hIB).2,
    hD κ hκ hκ4 P X' A B'' hX hA hI hB hIB, hC κ hκ hκ4 P X' A B'' hX hA hI hB hIB,
    hB.cont, hB.eval_zero_ae_eq_zero, ae_shift_alive_all κ hκ hκ4.le _ B'' hB]
    with ω hspec hDω hCω hc h0 hal
  have hW : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  refine ⟨hspec.1, fun Y W' havg hcfg => ?_⟩
  exact pstar_arc_det hγ hW hW0 (F1.drive_max κ B'' ω) hspec.1 havg hcfg hDω hCω hal

/-- **`LenPairCocycleArcStmt` from the unscaled open-arc pair cocycle** (open-arc copy of
`F1.lenPairCocycleStmt_of_unscaled'`, F1KappaGuard.lean:219). -/
theorem lenPairCocycleArc_of_unscaled' (hU : LenPairCocycleUnscaledArcStmt')
    (hR : WedgeUnzip.PStarRealizeStmt) (hD : UnscaledB3dLocStmt)
    (hC : UnscaledFlowCoreOffStmt) : LenPairCocycleArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ := hR κ P' Y B' hP
  obtain ⟨hκ, hκ4, -⟩ := hP
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hU κ hκ hκ4 (P'.prod Q) X' A B'' hX hA hI hB hIB,
    ae_pstar_arc hκ hκ4 hD hC hX hA hI hB hIB] with ω hRω hcoc hflow
  obtain ⟨havg, hcfg⟩ := hRω
  obtain ⟨-, hfl⟩ := hflow
  obtain ⟨ht, hf⟩ := hfl _ _ havg hcfg
  intro u s hu hs
  show (unzipLengthsArc _ (Y ω.1, drive κ B' ω.1) (u + s)).1 =
      (unzipLengthsArc _ (Y ω.1, drive κ B' ω.1) u).1 +
        (unzipLengthsArc _ (zipCapDown _ u (Y ω.1, drive κ B' ω.1)) s).1 ∧
    (unzipLengthsArc _ (Y ω.1, drive κ B' ω.1) (u + s)).2 =
      (unzipLengthsArc _ (Y ω.1, drive κ B' ω.1) u).2 +
        (unzipLengthsArc _ (zipCapDown _ u (Y ω.1, drive κ B' ω.1)) s).2
  rw [ht _ (add_nonneg hu hs), ht u hu, hf u s hu hs, mul_add]
  exact hcoc _ _ (mul_nonneg (sq_nonneg _) hu) (mul_nonneg (sq_nonneg _) hs)

/-! ## Capstones -/

/-- **`LenPairCocycleArcStmt` from the open-arc log-shift weight and the `Γ⁰` open-arc
regularity** (the `Γ⁰` open-arc cocycle is proved, R6a; the wedge inputs come from
`YMergeOffTipStmt`, no tip input). -/
theorem lenPairCocycleArc_of_logShift (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hRc : LenRegCfgArcStmt) (hW : LogShiftLenWeightArcStmt) : LenPairCocycleArcStmt :=
  lenPairCocycleArc_of_unscaled'
    (lenPairCocycleUnscaledArc'_of_logShift
      (logShiftLenFlowMeasArc_of_weight lenPairCocycleCfgArc_holds hRc hW))
    WedgeUnzip.pStarRealizeStmt_holds (unscaledB3dLoc_of_yMergeOffTip hYO)
    (unscaledFlowCoreOff_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper
