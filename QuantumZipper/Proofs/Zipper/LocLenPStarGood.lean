import QuantumZipper.Proofs.Zipper.LocLenWedgeGood
import QuantumZipper.Proofs.Zipper.LocLenStmtsPStar
import QuantumZipper.Proofs.Zipper.F1PStarShiftRegAll
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.Zipper.XFlowClose
import QuantumZipper.Proofs.Zipper.T13Hard3Realize

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R4c: `P_*` fields good off the root images at all times

Local copies (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1) of
* `WedgeUnzip.wedgeExactAll_of_x` (`WedgeUnzipXC.lean`): it uses X-G only for the regularity of
  the unzipped `x`-fields, which `XGoodOffAllStmt` also gives (`wedgeExactAll_of_xOff`);
* `WedgeUnzip.pStarGoodAll_of_core` (`WedgeUnzipPStar.lean`): the realization is pointwise
  (`PStarRealizeStmt`, no law transfer); the `P_*` field at time `t` is the `a`-rescaling of the
  wedge field at time `a² t`, and the root images scale the same way
  (`offSet (W(a²·)/a) t = (a·)⁻¹' offSet W (a² t)`, from `B3d.sideImages_fst/snd_scale` and the
  a.s. existence of the side limits, `RS.ae_real_alive`, `F1.exists_tendsto_sideImages_of_alive`);
* `F1.pStarShiftRegStmt_of_core` (uses W-G only for regularity) and
  `F1.pStarZipLenInputs_of_core'` → `pStarZipLenInputsLoc_of_core'`.

Sources: Sheffield, arXiv:1012.4797, p. 70 (the sides are wedges; Prop 1.6), pp. 70–72 ("by
scaling"), §1.6 (1.8); Berestycki–Powell arXiv:2404.16642, Def 6.41 p. 229. Bookkeeping as in the
global versions (own bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1 Thm18Asm

/-- **W-X from W-D, X-G off the root images, X-X, X-C and C** (copy of
`WedgeUnzip.wedgeExactAll_of_x`; only the regularity part of X-G is used). -/
theorem wedgeExactAll_of_xOff (hD : WedgeUnzip.WedgeDecompStmt) (hXG : XGoodOffAllStmt)
    (hXX : WedgeUnzip.XExactAllStmt) (hXC : WedgeUnzip.XContinuumStmt)
    (hC : WedgeUnzip.GlobalCaraStmt) : WedgeUnzip.WedgeExactAllStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ := hD κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hXG κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hXX κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    hXC κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hC κ hκ hκ4 _ _ hB2, hae, hB2.cont,
    hB2.eval_zero_ae_eq_zero] with ω hG hXx hCo hCa hZ hc h0
  obtain ⟨hGc, -, hZfc⟩ := hZ
  intro t ht d hd r hr
  have hW : Continuous (drive κ B'' ω.1) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω.1 0 = 0 := by simp [drive, h0]
  have hreg := S5.FieldShift.regEq_of_fc hZfc
  have e1 : unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω.1, drive κ B'' ω.1) t =
      unzippedField (Real.sqrt κ) (X'' ω + F2.logSingField κ + ofFun (G ω), drive κ B'' ω.1) t :=
    Factorization.coordChange_congr (funext fun k => funext fun z => hreg k z) _ _
  rw [e1]
  have hraw := WedgeUnzip.unzipAddFun (Real.sqrt κ) (X'' ω + F2.logSingField κ) (G ω)
    (drive κ B'' ω.1) t ht hW hW0 hGc hCo.1 (fun d _ r hr => hCo.2 t ht d r hr)
  have hreg2 := S5.FieldShift.regEq_of_fc hraw
  obtain ⟨F, hF⟩ : IsRegularSample
      (unzippedField (Real.sqrt κ) (X'' ω + F2.logSingField κ, drive κ B'' ω.1) t) := (hG t ht).1
  have hGE : ContinuousOn (G ω ∘ F2.extInv (drive κ B'' ω.1) t) Hbar :=
    hGc.comp_continuousOn (hCa t ht)
  rw [Factorization.evalReg_congr (funext fun k => funext fun z => hreg2 k z),
    GoodSample.evalReg_add_ofFun_fc hF hGE hd hr, hraw d hd r hr]
  have hx : evalReg (unzippedField (Real.sqrt κ) (X'' ω + F2.logSingField κ, drive κ B'' ω.1) t)
      (foldedCircle d r) =
      unzippedField (Real.sqrt κ) (X'' ω + F2.logSingField κ, drive κ B'' ω.1) t
        (foldedCircle d r) := hXx t ht d hd r hr
  rw [hx]
  rfl

/-- **`P_*` goodness off the root images at all times from the core statements** (copy of
`WedgeUnzip.pStarGoodAll_of_core`). -/
theorem pStarGoodOffAll_of_core (hR : WedgeUnzip.PStarRealizeStmt) (hG : WedgeGoodOffAllStmt)
    (hE : WedgeUnzip.WedgeExactAllStmt) (hC : WedgeUnzip.WedgeContinuumStmt) :
    PStarGoodOffAllStmt := by
  intro κ Ω' _ P' _ Y B' hP
  obtain ⟨hκ, hκ4, -⟩ := id hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ := hR κ P' Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hG κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hE κ hκ hκ4 _ X' A B'' hX hA hI hB hIB, hC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero, RS.ae_real_alive hB hκ hκ4.le]
    with ω hRω hGω hEω hCω hspec hc h0 halive
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
  have has : 0 ≤ scaleParam (Real.sqrt κ) Z ^ 2 * t := mul_nonneg (sq_nonneg _) ht
  have hraw := WedgeUnzip.unzippedField_canonConfig_fc hW hW0 hWmax ha ht (fun d r hr => by
      rw [B3d.canonConfig_snd_of_max hWmax]
      have hC' := hCω.2 _ has ((scaleParam (Real.sqrt κ) Z : ℂ) * d) _ (mul_pos ha hr)
      exact WedgeUnzip.scaleConsistent_of_continuum hCω.1 _ hW hW0 ha ht d hr hC'.1 hC'.2)
    (hEω _ has)
  -- the root images of the `P_*` driver are the rescaled root images of the wedge driver
  have hdrvY : drive κ B' ω.1 = fun r =>
      drive κ B'' ω (scaleParam (Real.sqrt κ) Z ^ 2 * r) / scaleParam (Real.sqrt κ) Z := by
    have h := B3d.canonConfig_snd_of_max (γ := Real.sqrt κ) (y := Z) hWmax
    rw [hcfg] at h
    exact h
  obtain ⟨l, m, hl, hm⟩ := F1.exists_tendsto_sideImages_of_alive has
    (fun x hx => halive x hx _ has)
  have hoff : offSet (drive κ B' ω.1) t = (fun u => scaleParam (Real.sqrt κ) Z * u) ⁻¹'
      offSet (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t) := by
    have e1 : (sideImages (drive κ B' ω.1) t).1 = l / scaleParam (Real.sqrt κ) Z := by
      rw [hdrvY]; exact B3d.sideImages_fst_scale _ ha ht hl
    have e2 : (sideImages (drive κ B' ω.1) t).2 = m / scaleParam (Real.sqrt κ) Z := by
      rw [hdrvY]; exact B3d.sideImages_snd_scale _ ha ht hm
    have e1' : (sideImages (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t)).1 = l :=
      hl.limUnder_eq
    have e2' : (sideImages (drive κ B'' ω) (scaleParam (Real.sqrt κ) Z ^ 2 * t)).2 = m :=
      hm.limUnder_eq
    ext u
    simp only [offSet, mem_preimage, mem_insert_iff, mem_singleton_iff, e1, e2, e1', e2']
    rw [eq_div_iff ha.ne', eq_div_iff ha.ne', mul_comm u, mul_eq_zero]
    simp [ha.ne']
  rw [e1, isLQGGoodOff_congr_coords (WedgeUnzip.coords_eq_of_fc fun d _ r hr => hraw d r hr),
    hoff]
  exact (hGω _ has).rescale hγ ha

/-- **`F1.PStarShiftRegStmt` from the core statements with W-G off the root images** (copy of
`F1.pStarShiftRegStmt_of_core`; W-G is used only for regularity). -/
theorem pStarShiftRegStmt_of_coreOff (hR : WedgeUnzip.PStarRealizeStmt)
    (hG : WedgeGoodOffAllStmt) (hE : WedgeUnzip.WedgeExactAllStmt)
    (hC : WedgeUnzip.WedgeContinuumStmt) : F1.PStarShiftRegStmt := by
  intro κ Ω' _ P' _ Y B' hP
  obtain ⟨hκ, hκ4, hWedge, -, -⟩ := id hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα : Real.sqrt κ - 2 / Real.sqrt κ < Qc (Real.sqrt κ) := F2.alpha_lt_Qc' hγ hγ2
  have hgY : ∀ᵐ ω ∂P', IsLQGGood (Real.sqrt κ) (Y ω) :=
    Wire2.wedgeGoodStmt hγ hγ2 hα P' Y hWedge
  have hPos : ∀ᵐ ω ∂P', ∀ k : ℝ, 0 < scaleParam (Real.sqrt κ) (addConst (Y ω) k) := by
    filter_upwards [ae_all_iff.2 fun n : ℤ => F1.ae_pos_scaleParam_addConst_pStar hP (n : ℝ),
      hgY] with ω h1 h2
    exact F1.scaleParam_addConst_pos_all hγ h2 h1
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ := hR κ P' Y B' hP
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hG κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    hE κ hκ hκ4 _ X' A B'' hX hA hI hB hIB, hC κ hκ hκ4 _ X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI, hB.cont, hB.eval_zero_ae_eq_zero,
    F1.ae_prod_fst_of_ae (Q := Q) hPos, F1.ae_prod_fst_of_ae (Q := Q) hgY] with
    ω hRω hGω hEω hCω hspec hc h0 hpos hgYω
  obtain ⟨havg, hcfg⟩ := hRω
  have hb : 0 < scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) := hspec.1
  have hW'' : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW''0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  have hW''max := F2.drive_max κ B'' ω
  have hWmax := F2.drive_max κ B' ω.1
  have hWdef : drive κ B' ω.1 = fun u => drive κ B'' ω
      (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2 * u) /
        scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) := by
    have e := congrArg Prod.snd hcfg
    rw [B3d.canonConfig_snd_of_max hW''max] at e
    exact e.symm
  have hCZ : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      F1.ContData (F2.zU (Real.sqrt κ) X' A ω)
        ((foldedCircle c r).map (fwdMapInv (drive κ B'' ω) t)) :=
    fun t ht c r hr => hCω.2 t ht c r hr
  have hGZ : ∀ t : ℝ, 0 ≤ t → IsRegularSample
      (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t) :=
    fun t ht => (hGω t ht).1
  intro k
  refine ⟨fun t ht => F1.clause1_pt hCω.1 hb hW'' hW''0 hWdef hCZ hgYω.1 havg k ht,
    fun s hs d r hr => F1.clause2_pt hCω.1 hb hW'' hW''0 hWdef hWmax hCZ hgYω.1 havg k (hpos k)
      hs d hr,
    fun s hs d hd r hr => F1.clause3_pt hCω.1 hb hW'' hW''0 hW''max hcfg hWdef hCZ hGZ hEω
      hgYω.1 havg k (mul_nonneg (sq_nonneg _) hs) hd hr⟩

/-- **`PStarZipLenInputsLocStmt` from the core statements** (copy of
`F1.pStarZipLenInputs_of_core` / `F1.pStarZipLenInputs_of_core'`). -/
theorem pStarZipLenInputsLoc_of_core' (hR : WedgeUnzip.PStarRealizeStmt)
    (hG : WedgeGoodOffAllStmt) (hE : WedgeUnzip.WedgeExactAllStmt)
    (hC : WedgeUnzip.WedgeContinuumStmt) : PStarZipLenInputsLocStmt := by
  have hReg := pStarShiftRegStmt_of_coreOff hR hG hE hC
  intro κ Ω' _ P' _ Y B' hP k
  have hPS : Thm13Asm.IsPStarSample κ P' Y B' := hP
  obtain ⟨hκ, hκ4, hWedge, hB', -⟩ := hPS
  dsimp only [F1.pcfg]
  filter_upwards [F1.ae_pos_scaleParam_addConst_pStar hP k, RS.ae_real_alive hB' hκ hκ4.le,
    hB'.cont, hB'.eval_zero_ae_eq_zero,
    pStarGoodOffAll_of_core hR hG hE hC κ P' Y B' hP, hReg κ P' Y B' hP] with
    ω hposω halive hcont h0 hgood hreg
  refine ⟨hposω, ?_, ?_, hgood, ?_⟩
  · intro t ht
    obtain ⟨a, -, h1, -⟩ := F1.exists_tendsto_sideImages_of_alive ht
      fun x hx => halive x hx t ht
    exact ⟨a, h1⟩
  · intro t ht
    obtain ⟨-, b, -, h2⟩ := F1.exists_tendsto_sideImages_of_alive ht
      fun x hx => halive x hx t ht
    exact ⟨b, h2⟩
  · intro s hs
    obtain ⟨hK, hsc, hexact⟩ := hreg k
    set W := drive κ B' ω with hWdef
    have hWc : Continuous W := F1.continuous_drive_of κ hcont
    have hW0 : W 0 = 0 := by simp [hWdef, drive, h0]
    have hWmax : ∀ u : ℝ, W (max u 0) = W u := fun u => F1.drive_max κ B' ω u
    have hmain := WedgeUnzip.regEq_unzippedField_canonConfig (γ := Real.sqrt κ)
      (y := addConst (Y ω) k) (W := W) hWc hW0 hWmax hposω hs (hsc s hs) (hexact s hs)
    have hresc : rescale (unzippedField (Real.sqrt κ) (addConst (Y ω) k, W)
          (scaleParam (Real.sqrt κ) (addConst (Y ω) k) ^ 2 * s)) (Qc (Real.sqrt κ))
          (scaleParam (Real.sqrt κ) (addConst (Y ω) k)) =
        rescale (addConst (unzippedField (Real.sqrt κ) (Y ω, W)
          (scaleParam (Real.sqrt κ) (addConst (Y ω) k) ^ 2 * s)) k) (Qc (Real.sqrt κ))
          (scaleParam (Real.sqrt κ) (addConst (Y ω) k)) :=
      Factorization.coordChange_congr
        (funext fun j => funext fun z => hK _ (mul_nonneg (sq_nonneg _) hs) j z) _ _
    rw [hresc] at hmain
    exact hmain

/-! ## Closed forms (no TipCore, no TIP-X, no goodness at all times) -/

/-- W-X with its X-G input replaced by X-G off the root images. -/
theorem wedgeExactAll_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    WedgeUnzip.WedgeExactAllStmt :=
  wedgeExactAll_of_xOff WedgeUnzip.WDec.wedgeDecompStmt_holds (xGoodOffAll_of_yMergeOffTip hYO)
    F1.xExactAllStmt_holds WedgeUnzip.xContinuumStmt_holds WedgeUnzip.globalCaraStmt_holds

theorem pStarGoodOffAll_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    PStarGoodOffAllStmt :=
  pStarGoodOffAll_of_core WedgeUnzip.pStarRealizeStmt_holds (wedgeGoodOffAll_of_yMergeOffTip hYO)
    (wedgeExactAll_of_yMergeOffTip hYO)
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)

theorem pStarZipLenInputsLoc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    PStarZipLenInputsLocStmt :=
  pStarZipLenInputsLoc_of_core' WedgeUnzip.pStarRealizeStmt_holds
    (wedgeGoodOffAll_of_yMergeOffTip hYO) (wedgeExactAll_of_yMergeOffTip hYO)
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)

end LocLen
end QuantumZipper
