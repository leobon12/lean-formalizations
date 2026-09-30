import QuantumZipper.Proofs.Zipper.LocLenWedgeGood
import QuantumZipper.Proofs.Zipper.BaseFinReduce
import QuantumZipper.Proofs.Zipper.LocLenF2Loc
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll
import QuantumZipper.Proofs.Zipper.T13Hard3Realize
import QuantumZipper.Proofs.Zipper.LocLenF1Flow
import QuantumZipper.Proofs.Zipper.LocLenPairCfgDefs
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Wire2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6g: X1 in `P_*` form (`LenFiniteArcStmt`)

At a fixed capacity time `q ≥ 0`, a.s. both open-arc lengths of the `P_*` sample are finite
(Berestycki–Powell, arXiv:2404.16642, p. 285, "L(1) < ∞"; Sheffield, arXiv:1012.4797, p. 70:
the two sides of `η[0,t]` are pieces of wedges of finite length). Route (FOLLOW-PAPER-13 row R6g):

1. **Fixed time, wedge picture** (`ae_wedge_arcLen_lt_top_fixed`): the unscaled wedge field is
   `X'' + α₀(−log|·|) + G` with `G` continuous (W-D, `wedgeDecompStmt_holds`, Sheffield §1.6);
   unzipping commutes with adding `G` (`WedgeUnzip.unzipAddFun`), so on the open arcs the
   wedge length measure is `e^{γ G∘F_t/2}` times the `x_t` measure (rule (5.1), Sheffield
   pp. 60–62, `HasBdryLimitOn.add_ofFun`). `G∘F_t` is continuous on `ℍ̄` (global Carathéodory,
   `globalCaraStmt_holds`), hence bounded on the compact closed arc, and the `x_t`-masses of the
   open arcs are finite by X1 (`BaseFin.BaseFiniteStmt`). At `t = 0` both arcs are empty.
2. **All times, wedge picture** (`ae_wedge_arcLen_lt_top_all`): from the integer times and the
   capacity cocycle of the wedge open-arc lengths (`WedgePairCocycleArcStmt`, the open-arc copy of
   `F1.LenPairCocycleUnscaledStmt'`, produced by R6f), `lt_top_of_nat_of_cocycle`.
3. **`P_*` form** (`lenFiniteArc_of_baseFinite`): a `P_*` sample is the canonical description of
   an unscaled wedge configuration (`pStarRealizeStmt_holds`), and the canonical rescaling maps
   open-arc lengths at time `q` to those of the wedge at the random time `a²q`
   (`unzipLengthsArc_canon`, with the regularity from `unscaledB3dLoc_of_yMergeOffTip`). Step 2
   gives finiteness at every time, in particular at `a²q`.

Own bookkeeping (the bounded-density estimate on a compact arc is elementary); the analytic inputs
are the cited proved nodes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **Wedge capacity cocycle of the open-arc lengths** (open-arc copy of
`F1.LenPairCocycleUnscaledStmt'`, F1KappaGuard.lean:84; the wedge cocycle of FOLLOW-PAPER-13 row
R6f). -/
def WedgePairCocycleArcStmt : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, PairCocycleArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)

/-- **Bounded density on a compact arc** (own elementary): if `x` has a local limit `ν` on
`(a,b)` with finite mass and `φ` is continuous on `ℍ̄`, the open-arc length of `x + φ` is
finite (rule (5.1): its local measure is `e^{γφ/2} ν`, and `φ` is bounded on `[a,b]`). -/
theorem arcLen_add_ofFun_lt_top {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x) {a b : ℝ}
    {ν : Measure ℝ} (hν : HasBdryLimitOn γ x (Ioo a b) ν) (hfin : ν (Ioo a b) < ⊤)
    {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) : arcLen γ (x + ofFun φ) a b < ⊤ := by
  have h2 := hν.add_ofFun hx isOpen_Ioo (W := univ) isOpen_univ (fun _ _ => mem_univ _)
    (by rwa [univ_inter])
  rw [arcLen_eq_of_hasBdryLimitOn (GoodSample.gs_add_ofFun_sample hx hφ) h2 subset_rfl,
    withDensity_apply _ measurableSet_Ioo]
  have hφR : ContinuousOn (fun t : ℝ => φ t) (Icc a b) :=
    hφ.comp Complex.continuous_ofReal.continuousOn fun t _ =>
      show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im by simp
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφR
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (Real.exp (γ / 2 * φ t)) ∂ν
      ≤ ∫⁻ _t in Ioo a b, ENNReal.ofReal (Real.exp (|γ / 2| * K)) ∂ν := by
        refine setLIntegral_mono measurable_const fun t ht => ?_
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        have hb := hK t (Ioo_subset_Icc_self ht)
        rw [Real.norm_eq_abs] at hb
        calc γ / 2 * φ t ≤ |γ / 2 * φ t| := le_abs_self _
          _ = |γ / 2| * |φ t| := abs_mul _ _
          _ ≤ |γ / 2| * K := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = ENNReal.ofReal (Real.exp (|γ / 2| * K)) * ν (Ioo a b) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B'' : ℝ≥0 → Ω → ℝ}

/-- **Step 1: fixed-time finiteness for the unscaled wedge configuration**, from X1. -/
theorem ae_wedge_arcLen_lt_top_fixed (hX1 : BaseFin.BaseFiniteStmt) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P,
      (unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t).1 < ⊤ ∧
      (unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t).2 < ⊤ := by
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  have hXG := xGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds κ hκ hκ4 _ _ X'' hB2
    hX'' hI2
  rcases ht.eq_or_lt with ht0 | ht0
  · -- time `0`: both arcs are empty
    subst ht0
    filter_upwards [hB2.cont, hB2.eval_zero_ae_eq_zero] with ω hc h0
    have hW0 : drive κ B'' ω.1 0 = 0 := by simp [drive, h0]
    simp only [unzipLengthsArc, B5.sideImages_fst_zero_time hW0,
      F2.sideImages_snd_zero_time hW0, arcLen, Ioo_self, measure_empty]
    exact ⟨ENNReal.zero_lt_top, ENNReal.zero_lt_top⟩
  filter_upwards [hXG, WedgeUnzip.xContinuumStmt_holds κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 _ _ hB2, hae, hB2.cont, hB2.eval_zero_ae_eq_zero,
    hX1 κ hκ hκ4 _ _ X'' hB2 hX'' hI2 t ht0] with ω hG hCo hCa hZ hc h0 hfin
  obtain ⟨hGc, -, hZfc⟩ := hZ
  set γ := Real.sqrt κ with hγdef
  set W := drive κ (fun t (ω : Ω × Ω₂) => B'' t ω.1) ω with hWdef
  have hW : Continuous W := by
    show Continuous (drive κ _ ω)
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [W, drive, h0]
  have hreg : RegEq (F2.zU γ X' A ω.1) (X'' ω + F2.logSingField κ + ofFun (G ω)) :=
    S5.FieldShift.regEq_of_fc hZfc
  have e1 : unzippedField γ (F2.zU γ X' A ω.1, drive κ B'' ω.1) t =
      unzippedField γ (X'' ω + F2.logSingField κ + ofFun (G ω), W) t :=
    Factorization.coordChange_congr (funext fun k => funext fun z => hreg k z) _ _
  have hraw := WedgeUnzip.unzipAddFun γ (X'' ω + F2.logSingField κ) (G ω) W t ht
    hW hW0 hGc hCo.1 (fun d _ r hr => hCo.2 t ht d r hr)
  have hco := WedgeUnzip.coords_eq_of_fc hraw
  have havg : avgReg (unzippedField γ (X'' ω + F2.logSingField κ + ofFun (G ω), W) t) =
      avgReg (F2.unzX κ (X'' ω) W t + ofFun (G ω ∘ F2.extInv W t)) := by
    rw [← Factorization.avgReg_reconstruct_coords, hco, Factorization.avgReg_reconstruct_coords]
    rfl
  have hφ : ContinuousOn (G ω ∘ F2.extInv W t) Hbar := hGc.comp_continuousOn (hCa t ht)
  obtain ⟨hr, ⟨ν, hν⟩, -⟩ := hG t ht
  have hm : (sideImages W t).1 ≤ 0 := sideImages_fst_nonpos_of_cont hW hW0 ht
  have hp : 0 ≤ (sideImages W t).2 := sideImages_snd_nonneg_of_cont hW hW0 ht
  have hsubL : Ioo (sideImages W t).1 0 ⊆ (offSet W t)ᶜ :=
    fun u hu hu' => Set.disjoint_left.1 (Ioo_left_disjoint_offSet W t hp) hu hu'
  have hsubR : Ioo 0 (sideImages W t).2 ⊆ (offSet W t)ᶜ :=
    fun u hu hu' => Set.disjoint_left.1 (Ioo_right_disjoint_offSet W t hm) hu hu'
  obtain ⟨hfL, hfR⟩ := hfin
  have key : ∀ {a b : ℝ}, Ioo a b ⊆ (offSet W t)ᶜ →
      qBoundaryMeasureOn γ (F2.unzX κ (X'' ω) W t) (Ioo a b) (Ioo a b) < ⊤ →
      arcLen γ (unzippedField γ (F2.zU γ X' A ω.1, drive κ B'' ω.1) t) a b < ⊤ := by
    intro a b hab hlt
    rw [e1, arcLen_congr havg]
    refine arcLen_add_ofFun_lt_top hr (hν.mono isOpen_Ioo hab) ?_ hφ
    rw [Measure.restrict_apply_self, ← arcLen_eq_of_hasBdryLimitOn hr hν hab]
    exact hlt
  exact ⟨key hsubL hfL, key hsubR hfR⟩

/-- **Step 2: finiteness at all times for the unscaled wedge configuration**, from the integer
times and the wedge capacity cocycle. -/
theorem ae_wedge_arcLen_lt_top_all (hX1 : BaseFin.BaseFiniteStmt) (hC : WedgePairCocycleArcStmt)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t).1 < ⊤ ∧
      (unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t).2 < ⊤ := by
  have hn := ae_all_iff.2 fun n : ℕ =>
    ae_wedge_arcLen_lt_top_fixed hX1 hκ hκ4 hX hA hI hB hIB (n : ℝ) (Nat.cast_nonneg n)
  filter_upwards [hn, hC κ hκ hκ4 P X' A B'' hX hA hI hB hIB] with ω hω hc t ht
  exact ⟨lt_top_of_nat_of_cocycle
      (f := fun t => (unzipLengthsArc (Real.sqrt κ)
        (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t).1)
      (fun u s hu hs => (hc u s hu hs).1) (fun n => (hω n).1) ht,
    lt_top_of_nat_of_cocycle
      (f := fun t => (unzipLengthsArc (Real.sqrt κ)
        (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t).2)
      (fun u s hu hs => (hc u s hu hs).2) (fun n => (hω n).2) ht⟩

/-- **R6g: `LenFiniteArcStmt` (X1 in `P_*` form)** from X1 (`BaseFin.BaseFiniteStmt`) and the
wedge capacity cocycle of R6f. -/
theorem lenFiniteArc_of_baseFinite (hX1 : BaseFin.BaseFiniteStmt)
    (hC : WedgePairCocycleArcStmt) : LenFiniteArcStmt := by
  intro κ Ω' _ P' _ Y B' hP q hq
  obtain ⟨hκ, hκ4, -⟩ := id hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hI, hB, hIB, hae⟩ :=
    WedgeUnzip.pStarRealizeStmt_holds κ P' Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae,
    unscaledB3dLoc_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds κ hκ hκ4 _ X' A B'' hX hA hI
      hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero,
    ae_wedge_arcLen_lt_top_all hX1 hC hκ hκ4 hX hA hI hB hIB] with ω hRω hDω hspec hc h0 hfin
  obtain ⟨havg, hcfg⟩ := hRω
  set γ := Real.sqrt κ
  set Z := F2.zU γ X' A ω
  set W := drive κ B'' ω with hWdef
  set a := scaleParam γ Z
  have ha : 0 < a := hspec.1
  have hW : Continuous W := by
    show Continuous (drive κ B'' ω)
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [W, drive, h0]
  have has : 0 ≤ a ^ 2 * q := mul_nonneg (sq_nonneg a) hq
  have hu : unzippedField γ (Y ω.1, drive κ B' ω.1) q =
      unzippedField γ (canonConfig γ (Z, W)) q := by
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  have e0 : unzipLengthsArc γ (F1.pcfg κ Y B' ω.1) q =
      unzipLengthsArc γ (canonConfig γ (Z, W)) q := by
    show (arcLen γ (unzippedField γ (Y ω.1, drive κ B' ω.1) q)
        (sideImages (drive κ B' ω.1) q).1 0,
      arcLen γ (unzippedField γ (Y ω.1, drive κ B' ω.1) q) 0
        (sideImages (drive κ B' ω.1) q).2) = _
    rw [hu]
    unfold unzipLengthsArc
    rw [hcfg]
  have hgood : ArcLimit γ (Z, W) (a ^ 2 * q) := by
    obtain ⟨hr, ⟨ν, hν⟩, -⟩ := hDω.1 _ has
    refine ⟨hr, ν.restrict _, hν.mono (isOpen_Ioo.union isOpen_Ioo) ?_⟩
    have hm := sideImages_fst_nonpos_of_cont hW hW0 has
    have hp := sideImages_snd_nonneg_of_cont hW hW0 has
    refine union_subset (fun u hu hu' => ?_) (fun u hu hu' => ?_)
    · exact Set.disjoint_left.1 (Ioo_left_disjoint_offSet W _ hp) hu hu'
    · exact Set.disjoint_left.1 (Ioo_right_disjoint_offSet W _ hm) hu hu'
  rw [e0, unzipLengthsArc_canon hγ ha (F2.drive_max κ B'' ω) hq
    (F1.exists_tendsto_fwdMap_left hW hW0 has) (F1.exists_tendsto_fwdMap_right hW hW0 has)
    hgood (hDω.2 q hq)]
  exact hfin _ has

end LocLen
end QuantumZipper
