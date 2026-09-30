import QuantumZipper.Proofs.Zipper.LocLenCanonRegCore
import QuantumZipper.Proofs.Zipper.LocLenCanonRegGeo
import QuantumZipper.Proofs.Zipper.LocLenF2Loc
import QuantumZipper.Proofs.Zipper.FlowRegAlive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6b-2 (part 3): `LenCanonRegArcStmt` from `YMergeOffTipStmt`

Sheffield arXiv:1012.4797 §1.4 and pp. 69–72; Berestycki–Powell arXiv:2404.16642 Def 6.41 p. 229,
Def 8.12 p. 281 (lengths of open boundary arcs).

* `pstar_flow_fc_off`: copy of `F1.pstar_flow_fc` (reads only scale consistency and RC3).
* `lenCanonRegArc_of_parts`: copy of `F1.lenCanonCoreStmt_of` + `F1.lenCanonRegStmt_of_core`
  with `F2.UnscaledB3dStmt ↦ UnscaledB3dLocStmt`, `UnscaledFlowCoreStmt ↦ UnscaledFlowCoreOffStmt`;
  the old `IsLQGGood` of the unzipped field is replaced by `ArcLimit`: the unzipped field of
  `zipCapDown τ` at time `b²r` is (on folded circles) the `a`-rescaling of the unscaled field
  unzipped by `a²τ + a²b²r`, which is good off `offSet W (a²τ + a²b²r)`, and the two open arcs
  avoid that set (`arcs_subset_compl_offSet`), so `HasBdryLimitOn.mono` applies.
* **`lenCanonRegArc_of_yMergeOffTip : YMergeOffTipStmt → LenCanonRegArcStmt`**.
Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- Copy of `F1.pstar_flow_fc` with `FlowScaleCoreOff` (only its first two clauses are read). -/
theorem pstar_flow_fc_off {γ : ℝ} {Z Y : FieldSample} {W W' : ℝ → ℝ} (hW : Continuous W)
    (ha : 0 < scaleParam γ Z)
    (havg : avgReg Y = avgReg (canonical γ Z))
    (hcfg : canonConfig γ (Z, W) = (canonical γ Z, W')) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s)
    (hB3 : RegEq (unzippedField γ (canonConfig γ (Z, W)) u)
      (rescale (unzippedField γ (Z, W) (scaleParam γ Z ^ 2 * u)) (Qc γ) (scaleParam γ Z)))
    (hcore : FlowScaleCoreOff γ Z W u s) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    unzippedField γ (zipCapDown γ u (Y, W')) s (foldedCircle d r) =
      rescale (unzippedField γ (zipCapDown γ (scaleParam γ Z ^ 2 * u) (Z, W))
        (scaleParam γ Z ^ 2 * s)) (Qc γ) (scaleParam γ Z) (foldedCircle d r) := by
  set a := scaleParam γ Z with ha_def
  set c'' := zipCapDown γ (a ^ 2 * u) (Z, W) with hc''
  have hW'' : Continuous c''.2 :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hW''0 : c''.2 0 = 0 := by simp [hc'', zipCapDown]
  have e0 : zipCapDown γ u (Y, W') =
      (unzippedField γ (canonConfig γ (Z, W)) u, fun r => c''.2 (a ^ 2 * r) / a) := by
    refine Prod.ext ?_ ?_
    · show coordChange Y (fwdMapInv W' u) (Qc γ) =
        coordChange (canonConfig γ (Z, W)).1 (fwdMapInv (canonConfig γ (Z, W)).2 u) (Qc γ)
      rw [hcfg]
      exact Factorization.coordChange_congr havg _ _
    · show (zipCapDown γ u (Y, W')).2 = fun r => c''.2 (a ^ 2 * r) / a
      rw [← zipCapDown_canonConfig_snd Z W hu, hcfg]
      rfl
  have hav : avgReg (unzippedField γ (canonConfig γ (Z, W)) u) = avgReg (rescale c''.1 (Qc γ) a) :=
    funext fun k => funext fun z => hB3 k z
  have hWa : Continuous fun r => c''.2 (a ^ 2 * r) / a := by fun_prop
  have hWa0 : (fun r => c''.2 (a ^ 2 * r) / a) 0 = 0 := by simp [hW''0]
  have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  obtain ⟨hφd, hφi, hφ0⟩ := WedgeUnzip.fwdMapInv_props hWa hWa0 hs
  obtain ⟨hψd, hψi, hψ0⟩ := WedgeUnzip.fwdMapInv_props hW'' hW''0 has
  have hscale : ∀ w ∈ H, (a : ℂ) * fwdMapInv (fun r => c''.2 (a ^ 2 * r) / a) s w =
      fwdMapInv c''.2 (a ^ 2 * s) ((a : ℂ) * w) := fun w hw => by
    rw [RS.fwdMapInv_scale hW'' hW''0 ha hs hw]
    have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
    rw [mul_div_cancel₀ _ ha']
  rw [e0]
  show coordChange (unzippedField γ (canonConfig γ (Z, W)) u)
      (fwdMapInv (fun r => c''.2 (a ^ 2 * r) / a) s) (Qc γ) (foldedCircle d r) = _
  rw [Factorization.coordChange_congr hav]
  exact WedgeUnzip.coordChange_rescale_fc_of_scale c''.1 (Qc γ) ha hφd hφi hφ0 hψd hψi hψ0
    hscale hcore.1 hcore.2.1 d r hr

/-- **`LenCanonRegArcStmt` from the local wedge inputs** (copy of `F1.lenCanonCoreStmt_of` and
`F1.lenCanonRegStmt_of_core`). -/
theorem lenCanonRegArc_of_parts (hR : WedgeUnzip.PStarRealizeStmt) (hD : UnscaledB3dLocStmt)
    (hC : UnscaledFlowCoreOffStmt) (hFC : WedgeFlowContStmt) (hSP : WedgeUnzipScalePosStmt) :
    LenCanonRegArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  obtain ⟨hκ, hκ4, -⟩ := id hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ := hR κ P' Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hD κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB, hFC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hSP κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero, ae_shift_alive_all κ hκ hκ4.le _ B'' hB]
    with ω hRω hDω hCω hFω hSω hspec hc h0 hal τ r hτ hr
  obtain ⟨havg, hcfg⟩ := hRω
  set γ := Real.sqrt κ
  set Z := F2.zU γ X' A ω
  set W := drive κ B'' ω
  set a := scaleParam γ Z
  have ha : 0 < a := hspec.1
  have hW : Continuous W := by
    show Continuous (drive κ B'' ω)
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [W, drive, h0]
  have hU : 0 ≤ a ^ 2 * τ := mul_nonneg (sq_nonneg a) hτ
  set c'' := zipCapDown γ (a ^ 2 * τ) (Z, W) with hc''
  have hW'' : Continuous c''.2 :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hW''0 : c''.2 0 = 0 := by simp [hc'', zipCapDown]
  have e0 := zipCapDown_pstar_eq havg hcfg hτ
  have hav0 : avgReg (zipCapDown γ τ (Y ω.1, drive κ B' ω.1)).1 =
      avgReg (rescale c''.1 (Qc γ) a) := by
    rw [e0]
    exact funext fun k => funext fun z => (hDω.2 τ hτ) k z
  have hyG : IsLQGGoodOff γ c''.1 (offSet W (a ^ 2 * τ)) := hDω.1 _ hU
  obtain ⟨μ0, hμ0⟩ := hyG.2.2
  set b := scaleParam γ (zipCapDown γ τ (Y ω.1, drive κ B' ω.1)).1 with hb_def
  have hb_eq : b = scaleParam γ c''.1 / a := by
    rw [hb_def, Factorization.scaleParam_congr hav0 γ, scaleParam_rescale_off hyG.1 hμ0 hγ ha]
  have hsU : 0 < scaleParam γ c''.1 := hSω _ hU
  have hb : 0 < b := by rw [hb_eq]; exact div_pos hsU ha
  have hS : 0 ≤ b ^ 2 * r := mul_nonneg (sq_nonneg b) hr
  have hcore := hCω τ (b ^ 2 * r) hτ hS
  have hraw := fun d {r' : ℝ} (hr' : 0 < r') =>
    pstar_flow_fc_off hW ha havg hcfg hτ hS (hDω.2 τ hτ) hcore d hr'
  have hsnd : (zipCapDown γ τ (Y ω.1, drive κ B' ω.1)).2 = fun r => c''.2 (a ^ 2 * r) / a :=
    congrArg Prod.snd e0
  refine ⟨hb, fun d r' hr' => ?_, fun d hd r' hr' => ?_, ?_⟩
  · -- scale consistency at the own scale `b`
    rw [scaleConsistentAt_congr hav0]
    have hcanon : (canonConfig γ (zipCapDown γ τ (Y ω.1, drive κ B' ω.1))).2 =
        fun s => c''.2 (a ^ 2 * (b ^ 2 * max s 0)) / a / b := by
      funext s
      show (zipCapDown γ τ (Y ω.1, drive κ B' ω.1)).2 (b ^ 2 * max s 0) / b = _
      rw [hsnd]
    have hd1 : (canonConfig γ (zipCapDown γ τ (Y ω.1, drive κ B' ω.1))).2 =
        fun s => c''.2 ((a * b) ^ 2 * s) / (a * b) := by
      rw [hcanon]; funext s; exact (zipCapDown_snd_rescale2 s).1
    have hd2 : (canonConfig γ (zipCapDown γ τ (Y ω.1, drive κ B' ω.1))).2 =
        fun s => (fun u => c''.2 (a ^ 2 * u) / a) (b ^ 2 * s) / b := by
      rw [hcanon]; funext s; exact (zipCapDown_snd_rescale2 s).2
    refine scaleConsistentAt_rescale hyG.1 _ ha hb ?_ ?_
    · rw [hd1]
      have hab : 0 < a * b := mul_pos ha hb
      have hF := hFω _ _ hU (mul_nonneg (sq_nonneg (a * b)) hr) (((a * b : ℝ) : ℂ) * d)
        ((a * b) * r') (mul_pos hab hr')
      exact WedgeUnzip.scaleConsistent_of_continuum hyG.1 _ hW'' hW''0 hab hr d hr' hF.1 hF.2
    · have hWa : Continuous fun u => c''.2 (a ^ 2 * u) / a := by fun_prop
      have hWa0 : (fun u => c''.2 (a ^ 2 * u) / a) 0 = 0 := by simp [hW''0]
      rw [hd2, WedgeUnzip.map_mul_fc_map_fwdMapInv_scale hWa hWa0 hb hr d hr']
      have hF := hFω _ _ hU (mul_nonneg (sq_nonneg a) (mul_nonneg (sq_nonneg b) hr))
        ((a : ℂ) * ((b : ℂ) * d)) (a * (b * r')) (mul_pos ha (mul_pos hb hr'))
      exact WedgeUnzip.scaleConsistent_of_continuum hyG.1 _ hW'' hW''0 ha
        (mul_nonneg (sq_nonneg b) hr) _ (mul_pos hb hr') hF.1 hF.2
  · -- RC3 along the flow
    have hreg := regEq_of_fc_Hbar (fun d _ r' hr' => hraw d hr')
    rw [Factorization.evalReg_congr (funext fun k => funext fun z => hreg k z),
      rc3_rescale_of_regular hcore.2.2.1 _ ha hd hr', hraw d hr']
  · -- the local boundary limit on the two open arcs
    have hS' : 0 ≤ a ^ 2 * (b ^ 2 * r) := mul_nonneg (sq_nonneg a) hS
    have hG' := isLQGGoodOff_of_fc_Hbar (fun d _ r' hr' => hraw d hr') (hcore.2.2.rescale hγ ha)
    obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hG'
    obtain ⟨l, hl⟩ := exists_tendsto_fwdMap_left hW'' hW''0 hS'
    obtain ⟨m, hm⟩ := exists_tendsto_fwdMap_right hW'' hW''0 hS'
    have e1 : (sideImages (fun r => W (a ^ 2 * τ + max r 0) - W (a ^ 2 * τ))
        (a ^ 2 * (b ^ 2 * r))).1 = l := hl.limUnder_eq
    have e2 : (sideImages (fun r => W (a ^ 2 * τ + max r 0) - W (a ^ 2 * τ))
        (a ^ 2 * (b ^ 2 * r))).2 = m := hm.limUnder_eq
    have hsub := arcs_subset_compl_offSet hW hW0 hU hS' (fun x hx => by
      obtain ⟨v, hv⟩ := hal 0 le_rfl x hx (a ^ 2 * τ + a ^ 2 * (b ^ 2 * r)) (add_nonneg hU hS')
      exact ⟨v, isForwardSol_congr_drive (fun s hs => by
        show W (0 + max s 0) - W 0 = W s
        rw [zero_add, max_eq_left hs.1, hW0, sub_zero]) hv⟩)
    rw [e1, e2] at hsub
    refine ⟨hreg, ν.restrict _, hν.mono (isOpen_Ioo.union isOpen_Ioo) ?_⟩
    rw [hsnd, B3d.sideImages_fst_scale c''.2 ha hS hl, B3d.sideImages_snd_scale c''.2 ha hS hm]
    intro z hz hmem
    rw [mem_preimage] at hmem
    refine hsub ?_ hmem
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [div_lt_iff₀ ha] at h1
      exact ⟨by linarith, by nlinarith⟩
    · right
      rw [lt_div_iff₀ ha] at h2
      exact ⟨by positivity, by linarith⟩

/-- **`LenCanonRegArcStmt` from the offset merge statement** (no TipCore, no TIP-X, no global
goodness at variable times). -/
theorem lenCanonRegArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    LenCanonRegArcStmt :=
  lenCanonRegArc_of_parts WedgeUnzip.pStarRealizeStmt_holds (unscaledB3dLoc_of_yMergeOffTip hYO)
    (unscaledFlowCoreOff_of_yMergeOffTip hYO)
    (wedgeFlowContStmt_of_xOff (xGoodOffAll_of_yMergeOffTip hYO) WedgeUnzip.xContinuumStmt_holds
      XFlowC.xFlowContStmt_holds)
    wedgeUnzipScalePos_holds

end LocLen
end QuantumZipper
