import QuantumZipper.Proofs.Zipper.SWCoreB8UoAnchor
import QuantumZipper.Proofs.Zipper.UnifUOMain
import QuantumZipper.Proofs.Zipper.WedgeYGoodArea
import QuantumZipper.Proofs.LQG.LogSingGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8 (d), part 3: offset merging off the tip, minus side (offset form of `ae_offTip_minus`)

* `ae_merge_time_zero_off`: at time `0`, `h⁰_0 = 𝔥₀ + X` (up to the full coordinates) is a good
  sample (`LogSingGood.logSingGoodAS_holds`, `𝔥₀ + X = X + (−2/√κ)(−log|·|)`), so its offset
  approximations merge with the dyadic ones;
* **`ae_offTip_minus_off`**: a.s., for all `s ∈ [0,T]` and every test function supported in
  `(−∞, 0)`, the offset approximations of `h⁰_s` merge with the dyadic ones along `goodFilter`.
  For `s > 0` the window geometry is that of `ae_offTip_minus` (`F_s` maps `(−∞, 0₋(T − s))`
  onto a set whose closure contains `(−∞, 0)`; a rational anchor `q < s` keeps the window live),
  and the merging on the window is `ae_anchor_off`.

Own bookkeeping (the geometry is verbatim that of `UnifUOMain.ae_offTip_minus`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4 CoordsFull

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Time `0`**: the offset approximations of `h⁰_0` merge with the dyadic ones. -/
theorem ae_merge_time_zero_off (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (WedgeUnzip.bdryMergeDiff (Real.sqrt κ) (h0f κ 0 B X ω) g) goodFilter (𝓝 0) := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hα : -(2 / Real.sqrt κ) < Qc (Real.sqrt κ) := by
    have h1 : 0 < Qc (Real.sqrt κ) := by unfold Qc; positivity
    have h2 : 0 < 2 / Real.sqrt κ := by positivity
    linarith
  filter_upwards [ae_coordsFull_h0f_zero (κ := κ) hB hX,
    LogSingGood.logSingGoodAS_holds hγ (gamma_lt_two_of_kappa hκ4) hα Ω _ P X inferInstance hX]
    with ω hcf hgood g hg hgc
  have e : ofFun (h0rev κ) + X ω =
      X ω + ofFun fun z => -(2 / Real.sqrt κ) * -Real.log ‖z‖ :=
    WedgeUnzip.h0rev_add_eq_Lf κ (X ω)
  have hR : ∀ r, bdryR (Real.sqrt κ) (h0f κ 0 B X ω) r =
      bdryR (Real.sqrt κ) (X ω + ofFun fun z => -(2 / Real.sqrt κ) * -Real.log ‖z‖) r := by
    intro r
    unfold bdryR bdryDens
    rw [evalReg_congr_full hcf, e]
  obtain ⟨ν, hν⟩ := hgood.2.1
  have h1 := hν.2 g hg hgc
  have h2 := h1.comp WedgeUnzip.tendsto_fst_one_goodFilter
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr fun i => ?_
  simp only [WedgeUnzip.bdryMergeDiff, Function.comp, hR]
  simp [goodRad]

/-- **Offset UO, minus side**, from the offset input. -/
theorem ae_offTip_minus_off (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamOffStmt κ T P B X) :
    ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      tsupport g ⊆ Iio 0 →
      Tendsto (WedgeUnzip.bdryMergeDiff (Real.sqrt κ) (h0f κ s B X ω) g) goodFilter (𝓝 0) := by
  filter_upwards [ae_anchor_off hκ hκ4 hT hB hX hind hF, ae_merge_time_zero_off hκ hκ4 hB hX,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB,
    ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le P B hB,
    hB.eval_zero_ae_eq_zero]
    with ω hA h0 hzm hcont hK hKs hB0 s hs g hg hgc hgneg
  rcases hs.1.eq_or_lt with hs0 | hs0
  · subst hs0
    exact h0 g hg hgc
  rcases (tsupport g).eq_empty_or_nonempty with he | hne
  · have hg0 : ∀ x, g x = 0 := fun x =>
      image_eq_zero_of_notMem_tsupport (by rw [he]; exact notMem_empty x)
    have : WedgeUnzip.bdryMergeDiff (Real.sqrt κ) (h0f κ s B X ω) g = fun _ => 0 := by
      funext i
      simp [WedgeUnzip.bdryMergeDiff, hg0]
    rw [this]
    exact tendsto_const_nhds
  obtain ⟨m, hm⟩ := hgc.isCompact.exists_isLeast hne
  obtain ⟨M, hM⟩ := hgc.isCompact.exists_isGreatest hne
  have hM0 : M < 0 := hgneg hM.1
  obtain ⟨v, hMv, hv⟩ := exists_rat_btwn hM0
  obtain ⟨u, hu⟩ := exists_rat_lt m
  have hgs : tsupport g ⊆ Ioo (u : ℝ) v := fun x hx =>
    ⟨hu.trans_le (hm.2 hx), (hM.2 hx).trans_lt hMv⟩
  obtain ⟨-, -, -, hzc, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hWc : Continuous (drive κ B ω) := drive_continuous hcont
  have hVc : Continuous V := continuous_vrev hWc T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set t := T - s with htdef
  have ht : 0 ≤ t := by rw [htdef]; linarith [hs.2]
  set F := realRevMap V t with hFdef
  obtain ⟨-, -, -, hC⟩ := realRevMap_endpoints hVc hV0 hT hK (continuous_vrev hWc s)
    (vrev_zero hs0.le) hs0 (hKs s hs0) ht (by rw [htdef]; ring)
    (fun r hr => (vrev_shift hs0.le hs.2 hr).symm)
  set c := zeroMinus V t with hcdef
  obtain ⟨l, hlc, hl⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 (hC.eventually (lt_mem_nhds hv))
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show l < c from hlc)
  have hFb : (v : ℝ) < F b := hl ⟨hb1, hb2⟩
  obtain ⟨m', hm'⟩ := eventually_atBot.1 ((CaraR.tendsto_realRevMap_atBot hVc ht).eventually
    (eventually_lt_atBot (u : ℝ)))
  obtain ⟨a, ha⟩ := exists_rat_lt (min m' (b : ℝ))
  have hab : (a : ℝ) < b := ha.trans_le (min_le_right _ _)
  have hFa : F a < u := hm' a (ha.trans_le (min_le_left _ _)).le
  have htm : t ∈ Icc 0 T := ⟨ht, by rw [htdef]; linarith⟩
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (hzc t htm) (c - b) (by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt (sub_lt_self s hδ) hs0)
  have hq0 : (0 : ℝ) ≤ q := ((le_max_right _ _).trans_lt hq1).le
  have hbq : (b : ℝ) < zeroMinus V (T - q) := by
    have hmem : T - q ∈ Icc 0 T := ⟨by linarith [hs.2], by linarith⟩
    have hd : dist (T - q) t < δ := by
      rw [Real.dist_eq, abs_lt, htdef]
      constructor <;> linarith [(le_max_left _ _).trans_lt hq1]
    have := hδc hmem hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hsub : Ioo (u : ℝ) v ⊆ Ioo (F a) (F b) := fun x hx =>
    ⟨hFa.trans hx.1, hx.2.trans hFb⟩
  exact hA q a b hq0 (hq2.trans_le hs.2) hab hbq s ⟨hq2.le, hs.2⟩ g hg hgc (hgs.trans hsub)

end RegUnif
end QuantumZipper
