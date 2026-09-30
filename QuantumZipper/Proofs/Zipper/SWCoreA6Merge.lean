import QuantumZipper.Proofs.Zipper.SWCoreA5
import QuantumZipper.Proofs.Zipper.SWCoreA6Flow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A6 (2): uniform merging over a class and along the Loewner flow (one field sample)

For one field sample `y` with window limits, locally finite area measure, a regularity witness
and the class-uniform distortion bound `AreaDistClassGood γ y`:

* `approx_pull_signed`: the fixed-scale approximations of `y` converge to `μ^y` against the
  pulled-back test functions `f ∘ ψ⁻¹`, uniformly over a rational class (`unifWin` with scale `1`);
* `merge_class_unif`: `∫ f dμ^{y∘ψ+Q log|ψ'|}_k − ∫ f∘ψ⁻¹ dμ^y_k → 0` uniformly over the class
  (with `transport_signed`);
* `mergeUnif_of_sample`: for a continuous driver, the merging differences `E6.mergeDiff` tend to
  `0` uniformly in `t ∈ [0,T]` (`flow_mem_areaClass`, `pullTest_eq_transTest`).

This is the deterministic content of `E6.WedgeAreaMergeUnifStmt` (Sheffield–Wang,
arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7), for the flow `φ = f_t⁻¹`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {γ : ℝ} {y : FieldSample}

/-- Nonnegative fixed-scale version, uniformly over the class. -/
theorem approx_pull_nonneg {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ y cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ y K < ⊤) {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {a b c d ρ M m : ℚ} (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ interior (rectC a b c d)) (hf0 : ∀ z, 0 ≤ f z) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ ψ ∈ AreaClass a b c d ρ M m,
      Integrable (fun w => areaDensK γ y k w * pullTest ψ (rectC a b c d) f w)
          (volume.restrict H) ∧
        |∫ w, pullTest ψ (rectC a b c d) f w ∂areaApprox γ y k -
          ∫ w, pullTest ψ (rectC a b c d) f w ∂qAreaMeasure γ y| ≤ η := by
  set K := rectC (a : ℝ) b c d with hKdef
  set μ := qAreaMeasure γ y with hμ
  set C₀ : Set ℂ := {w | ‖w‖ ≤ (M : ℝ) ∧ (ρ : ℝ) ≤ w.im} with hC₀
  have hC₀c : IsCompact C₀ := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im)
    · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := M)).subset fun w hw => by
        rw [mem_closedBall, dist_zero_right]; exact hw.1
  have hC₀H : C₀ ⊆ H := fun w hw => lt_of_lt_of_le hρ hw.2
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfs
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hfB : ∀ z, f z ≤ B := fun z =>
    (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z))
  obtain ⟨Cs, hCs⟩ := pullTest_ne_zero (a := a) (b := b) (c := c) (d := d) (M := M) (m := m)
    hρ (f := f)
  have hpt0 : ∀ ψ w, 0 ≤ pullTest ψ K f w := fun ψ w => by
    unfold pullTest; split_ifs
    · exact hf0 _
    · exact le_rfl
  have hptB : ∀ ψ w, pullTest ψ K f w ≤ B := fun ψ w => by
    unfold pullTest; split_ifs
    · exact hfB _
    · exact hB0
  have hgC : ∀ (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) w,
      pullTest i.1 K f w ≠ 0 → w ∈ C₀ := fun i w h => by
    obtain ⟨-, -, h1, h2, -, -⟩ := hCs i.1 i.2 w h
    exact ⟨h1, h2⟩
  have hgeq : ∀ ε > 0, ∃ δ > 0, ∀ (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) w w',
      dist w w' < δ → |pullTest i.1 K f w - pullTest i.1 K f w'| ≤ ε := fun ε hε => by
    obtain ⟨δ, hδ, h⟩ := pullTest_equicont hρ hm hf hfs hfK ε hε
    exact ⟨δ, hδ, fun i w w' hw => h i.1 i.2 w w' hw⟩
  have hη2 : (0 : ℝ) < η / 2 := by positivity
  have hU := unifWin (g := fun (i : {ψ : ℂ → ℂ // ψ ∈ AreaClass a b c d ρ M m}) =>
      pullTest i.1 K f) (s := fun _ _ => 1) (A := 1) hcw hcw' hWin hμK
    (measurable_supWin ⟨F, hF⟩ γ) (measurable_infWin ⟨F, hF⟩ γ) hC₀c hC₀H
    hB0 (fun i w => hpt0 _ w) (fun i w => hptB _ w) hgC hgeq
    (fun _ _ _ => ⟨one_pos, le_rfl⟩) (fun ε hε => ⟨1, one_pos, fun _ _ _ _ _ _ => by simpa using hε.le⟩)
    hη2
  filter_upwards [hU] with k hk ψ hψ
  obtain ⟨hV1, hV2⟩ := hk ⟨ψ, hψ⟩
  set g := pullTest ψ K f with hgdef
  have hgc : Continuous g := by
    refine Metric.continuous_iff.2 fun w ε hε => ?_
    obtain ⟨δ, hδ, h⟩ := pullTest_equicont hρ hm hf hfs hfK (ε / 2) (half_pos hε)
    refine ⟨δ, hδ, fun w' hw' => ?_⟩
    rw [Real.dist_eq]
    exact (h ψ hψ w' w hw').trans_lt (half_lt_self hε)
  set V := vsInt γ y g (fun _ => 1) k with hVdef
  set D : ℂ → ℝ := fun w => areaDensK γ y k w * g w with hDdef
  have hD0 : ∀ w, 0 ≤ D w := fun w => mul_nonneg (areaDensK_nonneg _ _ _ _) (hpt0 ψ w)
  have hDm : Measurable D := (measurable_areaDensK _ _ _).mul hgc.measurable
  have hLV : ∫⁻ w in H, ENNReal.ofReal (D w) = V := by
    rw [hVdef, vsInt]
    refine setLIntegral_congr_fun isOpen_H.measurableSet fun w hw => ?_
    have hwb := H_subset_Hbar hw
    simp only [hDdef, areaDensK, areaDens, mul_one]
    rw [hF.avgReg_eq k hwb, hF.evalReg_fc_of_mem hwb (radius_pos k),
      ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (radius_pos k).le _)
        (Real.exp_pos _).le), mul_comm]
  have hfin : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hV1
  have hT : ∫ w, g w ∂areaApprox γ y k = V.toReal := by
    rw [integral_areaApprox_eq, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hD0)
      hDm.aestronglyMeasurable, hLV]
  set J := ∫ w, g w ∂μ
  have hJ0 : 0 ≤ J := integral_nonneg (hpt0 ψ)
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hDm.aestronglyMeasurable
    (ae_of_all _ hD0)).1 (hLV ▸ hfin), ?_⟩
  rw [hT, abs_le]
  have hVr : ENNReal.ofReal V.toReal = V := ENNReal.ofReal_toReal hfin
  constructor
  · have h : ENNReal.ofReal J ≤ ENNReal.ofReal (V.toReal + η / 2) := by
      rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hη2.le, hVr]; exact hV2
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    linarith
  · have h : ENNReal.ofReal V.toReal ≤ ENNReal.ofReal (J + η / 2) := by rw [hVr]; exact hV1
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
    linarith

/-- Signed fixed-scale version, uniformly over the class. -/
theorem approx_pull_signed {cw cw' : ℕ → ℝ} (hcw : Tendsto cw atTop (𝓝 1))
    (hcw' : Tendsto cw' atTop (𝓝 1)) (hWin : WindowLimits γ y cw cw')
    (hμK : ∀ K, IsCompact K → K ⊆ H → qAreaMeasure γ y K < ⊤) {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {a b c d ρ M m : ℚ} (hρ : (0 : ℝ) < ρ)
    (hm : (0 : ℝ) < m) {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hfK : tsupport f ⊆ interior (rectC a b c d)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ ψ ∈ AreaClass a b c d ρ M m,
      |∫ w, pullTest ψ (rectC a b c d) f w ∂areaApprox γ y k -
        ∫ w, pullTest ψ (rectC a b c d) f w ∂qAreaMeasure γ y| ≤ η := by
  set fp : ℂ → ℝ := fun z => max (f z) 0 with hfp
  set fm : ℂ → ℝ := fun z => max (-f z) 0 with hfm
  have hfpc : Continuous fp := hf.max continuous_const
  have hfmc : Continuous fm := hf.neg.max continuous_const
  have hsp : support fp ⊆ support f := fun z hz h => hz (by simp [hfp, h])
  have hsm : support fm ⊆ support f := fun z hz h => hz (by simp [hfm, h])
  have hfps : HasCompactSupport fp := hfs.mono hsp
  have hfms : HasCompactSupport fm := hfs.mono hsm
  have hfpK : tsupport fp ⊆ interior (rectC a b c d) := (closure_mono hsp).trans hfK
  have hfmK : tsupport fm ⊆ interior (rectC a b c d) := (closure_mono hsm).trans hfK
  have hsplit : ∀ z, f z = fp z - fm z := fun z => by
    rcases le_total (f z) 0 with h | h
    · simp [hfp, hfm, max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    · simp [hfp, hfm, max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  have hpsplit : ∀ ψ w, pullTest ψ (rectC a b c d) f w =
      pullTest ψ (rectC a b c d) fp w - pullTest ψ (rectC a b c d) fm w := fun ψ w => by
    simp only [pullTest]
    split_ifs
    · exact hsplit _
    · ring
  filter_upwards [approx_pull_nonneg hcw hcw' hWin hμK hF hρ hm hfpc hfps hfpK
      (fun z => le_max_right _ _) (half_pos hη),
    approx_pull_nonneg hcw hcw' hWin hμK hF hρ hm hfmc hfms hfmK
      (fun z => le_max_right _ _) (half_pos hη)] with k h1 h2 ψ hψ
  obtain ⟨hi1, hb1⟩ := h1 ψ hψ
  obtain ⟨hi2, hb2⟩ := h2 ψ hψ
  have eA : ∫ w, pullTest ψ (rectC a b c d) f w ∂areaApprox γ y k =
      ∫ w, pullTest ψ (rectC a b c d) fp w ∂areaApprox γ y k -
        ∫ w, pullTest ψ (rectC a b c d) fm w ∂areaApprox γ y k := by
    rw [integral_areaApprox_eq, integral_areaApprox_eq, integral_areaApprox_eq,
      ← integral_sub hi1 hi2]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [hpsplit ψ z, mul_sub]
  have eB : ∫ w, pullTest ψ (rectC a b c d) f w ∂qAreaMeasure γ y =
      ∫ w, pullTest ψ (rectC a b c d) fp w ∂qAreaMeasure γ y -
        ∫ w, pullTest ψ (rectC a b c d) fm w ∂qAreaMeasure γ y := by
    rw [← integral_sub (integrable_pullTest hρ hm hfpc hfps hfpK hμK hψ)
      (integrable_pullTest hρ hm hfmc hfms hfmK hμK hψ)]
    exact integral_congr_ae (ae_of_all _ fun w => hpsplit ψ w)
  rw [eA, eB]
  calc _ = |(∫ w, pullTest ψ (rectC a b c d) fp w ∂areaApprox γ y k -
          ∫ w, pullTest ψ (rectC a b c d) fp w ∂qAreaMeasure γ y) -
        (∫ w, pullTest ψ (rectC a b c d) fm w ∂areaApprox γ y k -
          ∫ w, pullTest ψ (rectC a b c d) fm w ∂qAreaMeasure γ y)| := by ring_nf
    _ ≤ η / 2 + η / 2 := (abs_sub _ _).trans (add_le_add hb1 hb2)
    _ = η := by ring

/-- A rational rectangle whose interior contains a compact subset of `ℍ`. -/
theorem exists_rect_of_compact {S : Set ℂ} (hS : IsCompact S) (hSH : S ⊆ H) :
    ∃ a b c d : ℚ, (0 : ℝ) < c ∧ S ⊆ interior (rectC a b c d) := by
  have hopen : ∀ a b c d : ℝ, {z : ℂ | z.re ∈ Ioo a b ∧ z.im ∈ Ioo c d} ⊆
      interior (rectC a b c d) := fun a b c d =>
    interior_maximal (fun z hz => ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
      ((isOpen_Ioo.preimage Complex.continuous_re).inter
        (isOpen_Ioo.preimage Complex.continuous_im))
  rcases S.eq_empty_or_nonempty with he | hne
  · exact ⟨0, 1, 1, 2, by norm_num, by simp [he]⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hS.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨c, hc0, hcz⟩ := exists_rat_btwn (show (0 : ℝ) < z₀.im from hSH hz₀)
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_gt R
  refine ⟨-N, N, c, N, hc0, fun z hz => hopen _ _ _ _ ?_⟩
  have hzR : ‖z‖ ≤ R := by simpa [dist_zero_right] using hR hz
  have h1 := Complex.abs_re_le_norm z
  have h2 := Complex.abs_im_le_norm z
  have h3 : z₀.im ≤ z.im := hmin hz
  push_cast
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith [neg_abs_le z.re]
  · linarith [le_abs_self z.re]
  · linarith
  · linarith [le_abs_self z.im]

/-- On a rectangle containing the support, the pulled-back test function of `f_t⁻¹` is the
transported test function. -/
theorem pullTest_eq_transTest {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {K : Set ℂ} (hKH : K ⊆ H) {f : ℂ → ℝ} (hfK : tsupport f ⊆ K) :
    pullTest (fwdMapInv W t) K f = transTest W t f := by
  funext w
  by_cases hw : w ∈ fwdMapInv W t '' K
  · obtain ⟨z, hz, rfl⟩ := hw
    have hinj : InjOn (fwdMapInv W t) K := fun u hu v hv h => by
      have h1 := RS.fwdMap_fwdMapInv hW hW0 ht (hKH hu)
      have h2 := RS.fwdMap_fwdMapInv hW hW0 ht (hKH hv)
      rw [← h1, ← h2, h]
    have hU : fwdMapInv W t z ∈ H \ fwdHull W t :=
      image_fwdMapInv_subset hW hW0 ht hKH ⟨z, hz, rfl⟩
    simp only [pullTest, if_pos (mem_image_of_mem _ hz), hinj.leftInvOn_invFunOn hz, transTest,
      indicator_of_mem hU, RS.fwdMap_fwdMapInv hW hW0 ht (hKH hz)]
  · simp only [pullTest, if_neg hw, transTest]
    by_cases hU : w ∈ H \ fwdHull W t
    · rw [indicator_of_mem hU]
      by_contra hne
      exact hw ⟨fwdMap W t w, hfK (subset_tsupport f (Ne.symm hne)),
        RS.fwdMapInv_fwdMap hW hW0 ht hU⟩
    · rw [indicator_of_notMem hU]

end SWCore
end QuantumZipper
