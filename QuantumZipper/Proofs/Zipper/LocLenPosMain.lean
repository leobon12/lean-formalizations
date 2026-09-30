import QuantumZipper.Proofs.Zipper.LocLenPosY
import QuantumZipper.Proofs.Zipper.LocLenPStarGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R8a (2): open-arc boundary positivity through the unscaled wedge

Open-arc copy of `T13Hard3Pos.lean`:
* `wedgePosOffAll_of_yGood` (copy of `WedgeUnzip.wedgeBdryPosAll_of_uw`): the unzipped
  unscaled wedge field is the `x`-field plus `G ∘ E_t`, continuous on `ℍ̄` (proved raw
  decomposition `WDec.wedgeDecompStmt_holds`); rule (5.1) keeps open-arc positivity
  (`PosOff.add_ofFun`), starting from `ae_posOff_unzX`.
* `pStarPosOff_of_core` (copy of `WedgeUnzip.pStarBdryPosAll_of_core`): transport to `P_*`
  samples by the realization and the raw B3(d) identity; the local rescaling rule
  (`PosOff.rescale`) and the scaling of `offSet` (as in `pStarGoodOffAll_of_core`).
* `unzipBdryPosArc_of_unscaled`, closed form **`unzipBdryPosArc_of_yMergeOffTip`**.

No TipCore, no TIP-X, no global goodness, no UW, no `F2.Step3LocalDensityStmt`.
Paper: Sheffield arXiv:1012.4797 p. 56, §5.1 B3(d) pp. 60–62, §5.4 rule (5.1);
Berestycki–Powell arXiv:2404.16642 Def 8.12 p. 281. Bookkeeping own (as in the old proofs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- Open-arc positivity of the unzipped unscaled wedge fields at all times (proved below,
`wedgePosOffAll_of_yGood`; the `PosOff` form of `WedgeUnzip.WedgeBdryPosAllStmt`). -/
def WedgePosOffAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → PosOff (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t)
      (offSet (drive κ B'' ω) t) (sideImages (drive κ B'' ω) t).1

/-- **Unscaled open-arc positivity** (copy of `WedgeUnzip.wedgeBdryPosAll_of_uw`). -/
theorem wedgePosOffAll_of_yGood (hYG : YGoodOffAllStmt) : WedgePosOffAllStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [ae_posOff_unzX hYG hκ hκ4 hB2 hX'' hI2,
    xGoodOffAll_of_yGoodOff hYG κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    WedgeUnzip.xContinuumStmt_holds κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 _ _ hB2,
    F2.step3SideSign_holds κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hae, hB2.cont,
    hB2.eval_zero_ae_eq_zero] with ω hxP hG hCo hCa hsgn hZ hc h0
  obtain ⟨hGc, -, hZfc⟩ := hZ
  intro t ht
  set W := drive κ (fun t (ω : Ω × Ω₂) => B'' t ω.1) ω
  have hW : Continuous W := by
    show Continuous (drive κ _ ω)
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [W, drive, h0]
  have hreg : RegEq (F2.zU (Real.sqrt κ) X' A ω.1) (X'' ω + F2.logSingField κ + ofFun (G ω)) :=
    S5.FieldShift.regEq_of_fc hZfc
  have e1 : unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω.1, drive κ B'' ω.1) t =
      unzippedField (Real.sqrt κ) (X'' ω + F2.logSingField κ + ofFun (G ω), W) t :=
    Factorization.coordChange_congr (funext fun k => funext fun z => hreg k z) _ _
  rw [e1]
  have hraw := WedgeUnzip.unzipAddFun (Real.sqrt κ) (X'' ω + F2.logSingField κ) (G ω) W t ht.le
    hW hW0 hGc hCo.1 (fun d _ r hr => hCo.2 t ht.le d r hr)
  refine PosOff.congr_coords (WedgeUnzip.coords_eq_of_fc hraw) ?_
  have hdis : ∀ u v : ℝ, (sideImages W t).1 ≤ u → u < v → v ≤ 0 →
      Ioo u v ⊆ (offSet W t)ᶜ := fun u v hu _ hv z hz =>
    disjoint_left.1 (Ioo_left_disjoint_offSet _ t (hsgn t ht.le).2) (Ioo_subset_Ioo hu hv hz)
  exact (hxP t ht).add_ofFun (hG t ht.le).1 (isClosed_offSet _ t) isOpen_univ
    (fun _ _ => mem_univ _) (by rw [univ_inter]; exact hGc.comp_continuousOn (hCa t ht.le)) hdis

/-- **`P_*` open-arc positivity** (copy of `WedgeUnzip.pStarBdryPosAll_of_core`). -/
theorem pStarPosOff_of_core (hR : WedgeUnzip.PStarRealizeStmt) (hP : WedgePosOffAllStmt)
    (hG : WedgeGoodOffAllStmt) (hE : WedgeUnzip.WedgeExactAllStmt)
    (hC : WedgeUnzip.WedgeContinuumStmt) (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ)
    (hPS : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t → PosOff (Real.sqrt κ)
      (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) (offSet (drive κ B' ω) t)
      (sideImages (drive κ B' ω) t).1 := by
  obtain ⟨hκ, hκ4, -⟩ := id hPS
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ := hR κ P' Y B' hPS
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hP κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hG κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hE κ hκ hκ4 _ X' A B'' hX hA hI hB hIB, hC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4.le]
    with ω hRω hPω hGω hEω hCω hspec hc h0 halive
  obtain ⟨havg, hcfg⟩ := hRω
  intro t ht
  set Z := F2.zU (Real.sqrt κ) X' A ω
  have ha : 0 < scaleParam (Real.sqrt κ) Z := hspec.1
  have hW : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  have hWmax := F2.drive_max κ B'' ω
  have e1 : unzippedField (Real.sqrt κ) (Y ω.1, drive κ B' ω.1) t =
      unzippedField (Real.sqrt κ) (canonConfig (Real.sqrt κ) (Z, drive κ B'' ω)) t := by
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  have has : 0 < scaleParam (Real.sqrt κ) Z ^ 2 * t := by positivity
  have hraw := WedgeUnzip.unzippedField_canonConfig_fc hW hW0 hWmax ha ht.le (fun d r hr => by
      rw [B3d.canonConfig_snd_of_max hWmax]
      have hC' := hCω.2 _ has.le ((scaleParam (Real.sqrt κ) Z : ℂ) * d) _ (mul_pos ha hr)
      exact WedgeUnzip.scaleConsistent_of_continuum hCω.1 _ hW hW0 ha ht.le d hr hC'.1 hC'.2)
    (hEω _ has.le)
  have hdrvY : drive κ B' ω.1 = fun r =>
      drive κ B'' ω (scaleParam (Real.sqrt κ) Z ^ 2 * r) / scaleParam (Real.sqrt κ) Z := by
    have h := B3d.canonConfig_snd_of_max (γ := Real.sqrt κ) (y := Z) hWmax
    rw [hcfg] at h
    exact h
  obtain ⟨l, m, hl, hm⟩ := F1.exists_tendsto_sideImages_of_alive has.le
    (fun x hx => halive x hx _ has.le)
  have s1 : (sideImages (drive κ B' ω.1) t).1 = l / scaleParam (Real.sqrt κ) Z := by
    rw [hdrvY]; exact B3d.sideImages_fst_scale _ ha ht.le hl
  have s2 : (sideImages (drive κ B' ω.1) t).2 = m / scaleParam (Real.sqrt κ) Z := by
    rw [hdrvY]; exact B3d.sideImages_snd_scale _ ha ht.le hm
  have s1' : (sideImages (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t)).1 = l :=
    hl.limUnder_eq
  have s2' : (sideImages (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t)).2 = m :=
    hm.limUnder_eq
  have hoff : offSet (drive κ B' ω.1) t = (fun u => scaleParam (Real.sqrt κ) Z * u) ⁻¹'
      offSet (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t) := by
    ext u
    simp only [offSet, mem_preimage, mem_insert_iff, mem_singleton_iff, s1, s2, s1', s2']
    rw [eq_div_iff ha.ne', eq_div_iff ha.ne', mul_comm u, mul_eq_zero]
    simp [ha.ne']
  rw [e1, hoff, s1, ← s1']
  refine PosOff.congr_coords (WedgeUnzip.coords_eq_of_fc fun d _ r hr => hraw d r hr) ?_
  exact (hPω _ has).rescale (hGω _ has.le).1 hγ ha

/-- **Open-arc `P_*` positivity from the core statements.** -/
theorem pStarBdryPosAllArc_of_core (hR : WedgeUnzip.PStarRealizeStmt) (hYG : YGoodOffAllStmt)
    (hG : WedgeGoodOffAllStmt) (hE : WedgeUnzip.WedgeExactAllStmt)
    (hC : WedgeUnzip.WedgeContinuumStmt) (hPG : PStarGoodOffAllStmt) :
    PStarBdryPosAllArcStmt := by
  intro κ Ω' _ P' _ Y B' hPS
  filter_upwards [pStarPosOff_of_core hR (wedgePosOffAll_of_yGood hYG) hG hE hC κ P' Y B' hPS,
    hPG κ P' Y B' hPS] with ω h1 h2 t ht
  exact (h1 t ht).qBoundaryMeasureOn_pos (h2 t ht.le).1 (isClosed_offSet _ t)

/-- **`UnzipBdryPosArcStmt` through the unscaled wedge** (copy of
`Thm18Asm.unzipBdryPosStmt_of_unscaled`). -/
theorem unzipBdryPosArc_of_unscaled (hR : WedgeUnzip.PStarRealizeStmt) (hYG : YGoodOffAllStmt)
    (hG : WedgeGoodOffAllStmt) (hE : WedgeUnzip.WedgeExactAllStmt)
    (hC : WedgeUnzip.WedgeContinuumStmt) (hPG : PStarGoodOffAllStmt) : UnzipBdryPosArcStmt :=
  unzipBdryPosArc_of_pStar (pStarBdryPosAllArc_of_core hR hYG hG hE hC hPG)

/-- **Closed form**: open-arc boundary positivity from the offset merging input only. -/
theorem unzipBdryPosArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    UnzipBdryPosArcStmt :=
  unzipBdryPosArc_of_unscaled WedgeUnzip.pStarRealizeStmt_holds (yGoodOffAll_of_yMergeOffTip hYO)
    (wedgeGoodOffAll_of_yMergeOffTip hYO) (wedgeExactAll_of_yMergeOffTip hYO)
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)
    (pStarGoodOffAll_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper
