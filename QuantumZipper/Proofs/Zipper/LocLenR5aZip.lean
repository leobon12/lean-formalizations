import QuantumZipper.Proofs.Zipper.LocLenR5aZipDet
import QuantumZipper.Proofs.Zipper.LocLenYGood
import QuantumZipper.Proofs.Zipper.ZipLen2Main
import QuantumZipper.Proofs.Zipper.ZipLen2Area
import QuantumZipper.Proofs.Zipper.CfgFMClose
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): `CanonZipRawAllArcStmt` without the tip core

Copy of the chain `E6.canonZipRawAllStmt_of_dens` (E6FlowPair.lean:289) →
`E6.canonZipRawAllStmt_of_pair` (E6FlowRaw.lean) → `E6.canonZipRawAllStmt_of_reg`
(E6InReduce.lean:140), with open-arc lengths and with the inputs

* `ZipLenInputsArcStmt` (copy of `B3d.ZipLenInputsStmt` with goodness off the chart tip),
  proved in `zipLenInputsArc_holds` by copying `B3d.ZipLen.zipLenInputsStmt_of_y`
  (ZipLenMain.lean:127) with `YGoodOffAllStmt` (R3a, `yGoodOffAll_of_yMergeOffTip` with the
  proved `SWCore.yMergeOffTipStmt_holds`) in place of `YGoodAllStmt`;
* the proved field cocycle (`RegUnif.capCocycleRegStmt_holds`, `capCocycleAddStmt_holds`), the
  proved `Γ⁰` nodes (`yExactAllStmt_holds`, `yAreaAllStmt_of_merge yAreaMergeStmt_holds`,
  `yFlowRC3Stmt_holds`, `yFlowContStmt_holds`) and the smoothed-pairing node
  `CfgFM.cfgDensStmt_holds`.

No tip estimate enters. Sources: Sheffield arXiv:1012.4797 §5.4 pp. 70–72 (E6 identity
`Z_C C̄_x = Z^LEN_{−ℓ₁}(Z_C C̄_y)`); own bookkeeping (verbatim copies of the old proofs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 E1 D3Plus E6

variable {γ : ℝ}

/-- Goodness off `S` transfers along `RegEq` to a regular sample (copy of
`Thm18Asm.isLQGGood_of_regEq`). -/
theorem isLQGGoodOff_of_regEq_r5a {x y : FieldSample} {S : Set ℝ} (hx : IsRegularSample x)
    (hxy : RegEq x y) (hy : IsLQGGoodOff γ y S) : IsLQGGoodOff γ x S := by
  have hav : avgReg x = avgReg y := funext fun k => funext fun z => hxy k z
  have he := Factorization.evalReg_congr hav
  have ha : areaR γ x = areaR γ y := by
    funext r; unfold areaR areaDens; rw [he]
  obtain ⟨-, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hy
  refine ⟨hx, ⟨ν, (hasBdryLimitOn_congr_avg hav).2 hν⟩, ⟨μ, ?_⟩⟩
  unfold HasAreaLimit at hμ ⊢
  rw [ha]
  exact hμ

variable {Ω : Type} [MeasurableSpace Ω]

/-- Copy of `B3d.ZipLenInputsStmt` with goodness off the chart tip (proved below). -/
def ZipLenInputsArcStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ᵐ ω ∂P, ∀ u k : ℝ, 0 ≤ u → u ≤ T →
    let c := zipCapDown (Real.sqrt κ) u (B2.cfg κ B X ω)
    let a := scaleParam (Real.sqrt κ) (addConst c.1 k)
    0 < a ∧
    (∀ t, 0 ≤ t →
      0 < scaleParam (Real.sqrt κ) (addConst (unzippedField (Real.sqrt κ) c t) k)) ∧
    (∀ t, 0 ≤ t → ∃ l, Tendsto (fun r : ℝ => (fwdMap c.2 t r).re) (𝓝[<] (0 : ℝ)) (𝓝 l)) ∧
    (∀ t, 0 ≤ t → IsLQGGoodOff (Real.sqrt κ) (unzippedField (Real.sqrt κ) c t) {0}) ∧
    (∀ s, 0 ≤ s → RegEq
      (unzippedField (Real.sqrt κ) (canonConfig (Real.sqrt κ) (addConst c.1 k, c.2)) s)
      (rescale (addConst (unzippedField (Real.sqrt κ) c (a ^ 2 * s)) k) (Qc (Real.sqrt κ)) a))

/-- **`ZipLenInputsArcStmt` holds** (copy of `B3d.ZipLen.zipLenInputsStmt_of_y` with
`YGoodOffAllStmt`). -/
theorem zipLenInputsArc_holds {κ T : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ZipLenInputsArcStmt κ T P B X := by
  filter_upwards [RegUnif.ae_drive_good hB κ,
    yGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds κ hκ hκ4 P B X hB hX hind,
    B3d.ZipLen.yExactAllStmt_holds κ hκ hκ4 P B X hB hX hind,
    B3d.ZipLen.yAreaAllStmt_of_merge SWCore.yAreaMergeStmt_holds κ hκ hκ4 P B X hB hX hind,
    B3d.ZipLen.yFlowRC3Stmt_holds κ hκ hκ4 P B X hB hX hind,
    B3d.ZipLen.yFlowContStmt_holds κ hκ hκ4 P B X hB hX hind,
    ae_all_iff.2 fun n : ℕ => RegUnif.capCocycleRegStmt_holds (κ := κ) (T := (n : ℝ) + 1)
      hB hX hind (by positivity)] with ω hdr hg he harea hrc hcont hcoc
  intro u k hu _
  set γ := Real.sqrt κ with hγ_def
  set W := drive κ B ω with hW_def
  set y₀ := ofFun (h0rev κ) + X ω with hy₀_def
  have hcfg : B2.cfg κ B X ω = (y₀, W) := rfl
  have hEq : ∀ t, unzippedField γ (y₀, W) t = F2.unzY κ (X ω) W t := fun t =>
    B3d.ZipLen.unzippedField_cfg_eq κ t (X ω) W
  simp_rw [← hEq] at hg he harea hrc hcont
  rw [hcfg] at hcoc ⊢
  have hcoc' : ∀ t : ℝ, 0 ≤ t →
      RegEq (unzippedField γ (zipCapDown γ u (y₀, W)) t) (unzippedField γ (y₀, W) (u + t)) ∧
        LocalRule.RawConverges (unzippedField γ (zipCapDown γ u (y₀, W)) t) univ := by
    intro t ht
    obtain ⟨h1, h2, -⟩ := hcoc ⌈u + t⌉₊ u t hu ht
      ((Nat.le_ceil (u + t)).trans (le_add_of_nonneg_right zero_le_one))
    exact ⟨h1, h2⟩
  have hreg : ∀ t : ℝ, 0 ≤ t → IsRegularSample (unzippedField γ (zipCapDown γ u (y₀, W)) t) :=
    fun t ht => B3d.ZipLen.isRegularSample_of_regEq_raw (hcoc' t ht).2 (hcoc' t ht).1
      (hg _ (add_nonneg hu ht)).1
  have hpos : ∀ t : ℝ, 0 ≤ t → ∀ k' : ℝ,
      0 < scaleParam γ (addConst (unzippedField γ (zipCapDown γ u (y₀, W)) t) k') := by
    intro t ht k'
    rw [F1.scaleParam_addConst_congr_of_isRegularSample (hreg t ht) (hg _ (add_nonneg hu ht)).1
      (B3d.avgReg_eq_of_regEq (hcoc' t ht).1) k' γ]
    exact scaleParam_addConst_pos_off (hg _ (add_nonneg hu ht))
      (harea _ (add_nonneg hu ht)).1 (harea _ (add_nonneg hu ht)).2 k'
  have ha : 0 < scaleParam γ (addConst (zipCapDown γ u (y₀, W)).1 k) :=
    scaleParam_addConst_pos_off (hg u hu) (harea u hu).1 (harea u hu).2 k
  refine ⟨ha, fun t ht => hpos t ht k,
    fun t ht => (F1.zipCapDown_side_limits (γ := γ) (c := (y₀, W)) hdr.1 u ht).1,
    fun t ht => isLQGGoodOff_of_regEq_r5a (hreg t ht) (hcoc' t ht).1 (hg _ (add_nonneg hu ht)),
    fun s hs => ?_⟩
  exact B3d.ZipLen.zipLen_field_pt hdr.1 hdr.2 (fun t ht => (hg t ht).1) he hrc hcont hu k ha hs

/-- **`CanonZipRawArcStmt` at a fixed horizon** (copies of `B3d.zipLenCanonStmt_of`,
`E6.canonZipStmt_of`, `E6.canonZipPairStmt_of_dens`, `E6.canonZipRegStmt_of_pair`,
`E6.canonZipRawStmt_of_reg`). -/
theorem canonZipRawArcStmt_holds {κ T : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    CanonZipRawArcStmt κ T P B X := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  filter_upwards [zipLenInputsArc_holds (T := T) hκ hκ4 hB hX hind,
    CfgFM.cfgDensStmt_holds κ T hB hX hind,
    RegUnif.ae_forall_isRegularSample (γ := Real.sqrt κ) hB hX hind,
    RegUnif.capCocycleAddStmt_holds hB hX hind hT] with ω hZ hDω hRg hCC
  intro u t₀ k ℓ hu ht hut hℓ ht₀
  obtain ⟨ha, hb, hside, hgood, hfield⟩ := hZ u k hu (by linarith)
  obtain ⟨ha', -⟩ := hZ (u + t₀) k (by linarith) hut
  have hxBreg : IsRegularSample (zipCapDown (Real.sqrt κ) (u + t₀) (cfg κ B X ω)).1 :=
    (hRg (u + t₀) (by linarith)).1
  have hDB := hDω (u + t₀) (by linarith) hut
  -- the `ConfigEq` zip identity
  have hWmax := Thm18Asm.zipCapDown_snd_max (Real.sqrt κ) u (cfg κ B X ω)
  have hCE := zipLenDownArc_canonConfig_addConst
    (x := (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).1)
    (W := (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2) hγ ha hWmax hside hgood hfield ht₀
    (hb t₀ ht)
  rw [canonConfig_congr_avgReg (hCC u t₀ k hu ht hut)
    (zipCapDown_snd_cocycle _ u t₀ _ ht)] at hCE
  -- raw regularity of both sides
  have hL : RawRegular (zipLenDownArc (Real.sqrt κ) ℓ (canonConfig (Real.sqrt κ)
      (addConst (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).1 k,
        (zipCapDown (Real.sqrt κ) u (cfg κ B X ω)).2))).1 :=
    rawRegular_of_halves (rawCircRegular_zipLenDownArc_canon hγ ha hb hgood hfield)
      (rawPairRegular_zipLenDownArc_canon hγ hWmax ha hb hside hgood hfield ht₀ hxBreg
        (hCC u t₀ k hu ht hut).symm hDB)
  have hR : RawRegular (canonConfig (Real.sqrt κ)
      (addConst (zipCapDown (Real.sqrt κ) (u + t₀) (cfg κ B X ω)).1 k,
        (zipCapDown (Real.sqrt κ) (u + t₀) (cfg κ B X ω)).2)).1 := by
    refine rawRegular_of_halves (rawCircRegular_rescale (hxBreg.addConst' k) _ ha') ?_
    obtain ⟨F, hF⟩ := hxBreg.addConst' k
    exact rawPairRegular_rescale hF _ ha' (densPair_addConst hxBreg ha' (hDB _ ha') k)
  exact rawEq_of_configEq_of_rawRegular hCE hL hR

/-- **`CanonZipRawAllArcStmt` PROVED** (no tip core). -/
theorem canonZipRawAllArcStmt_holds : CanonZipRawAllArcStmt :=
  fun _ _ _ _ _ _ _ _ hκ hκ4 hT hB hX hind => canonZipRawArcStmt_holds hκ hκ4 hT hB hX hind

end LocLen
end QuantumZipper
