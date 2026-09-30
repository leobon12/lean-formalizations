import QuantumZipper.Proofs.Thm18.R18Basic
import QuantumZipper.Proofs.Zipper.UnzipInvariance
import QuantumZipper.Proofs.Thm14.FromThm13
import QuantumZipper.Proofs.Thm11.CharFunRhs
import QuantumZipper.Proofs.Loewner.ReverseHolo
import QuantumZipper.Proofs.Zipper.AreaCoordBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8 (D76): bookkeeping of the carried quantum area

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, p. 26 (the zipper moves the
quantum area of the pieces with the conformal maps, and (1.8) rescales it so that `B₁(0)` has
area one). The deterministic identities of the carried area `μ` of an `AreaConfig`
(**own elementary bookkeeping**; the paper uses them implicitly: "the transformed quantum
measure"):

* `areaScale_map_inv_mul`: the scale of `μ ∘ (a·)⁻¹`-pushforward is `areaScale μ / a`;
* `areaScale_restrict_diff_of_null`, `areaScale_restrict_H`: restricting to `ℍ ∖ K` does not
  change the scale if `μ (K ∩ ℍ) = 0`;
* `zipCapDownA_zipWeldUpA_area`: unzipping what was just zipped returns `μ|_ℍ`
  (`f_T ∘ R_T = id` on `ℍ`, `R_T(ℍ) ⊆ ℍ ∖ K_T`, `UnzipInvariance.fwdMap_revMap_timeRev_of_nonneg`);
* `zipWeldUpA_zipCapDownA_area`: zipping up along the reverse driver `W(t − ·) − W t` of the
  unzipped segment returns `μ|_{ℍ ∖ K_t}`.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal Pointwise

namespace QuantumZipper
namespace R18

theorem measurableSet_H_mu : MeasurableSet H := isOpen_H.measurableSet

/-- The carried area after unzipping is `E6.areaTransport` (definitional). -/
theorem zipCapDownA_area_eq_areaTransport (γ t : ℝ) (c : AreaConfig) :
    (zipCapDownA γ t c).area = E6.areaTransport c.area c.drv t := rfl

/-- The scale (1.8) of the pushforward of `μ` by `z ↦ z / a` is `areaScale μ / a`. -/
theorem areaScale_map_inv_mul (μ : Measure ℂ) {a : ℝ} (ha : 0 < a) :
    areaScale (μ.map fun z => ((a : ℂ))⁻¹ * z) = areaScale μ / a := by
  have hmeas : Measurable fun z : ℂ => ((a : ℂ))⁻¹ * z := measurable_id.const_mul _
  have hpre : ∀ r : ℝ, (fun z : ℂ => ((a : ℂ))⁻¹ * z) ⁻¹' (Metric.ball 0 r ∩ H) =
      Metric.ball 0 (a * r) ∩ H := by
    intro r
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right]
    rw [← Complex.ofReal_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 ha.le),
      inv_mul_lt_iff₀ ha]
    refine and_congr Iff.rfl ?_
    show 0 < ((a⁻¹ : ℝ) * z : ℂ).im ↔ 0 < z.im
    rw [Complex.im_ofReal_mul]
    exact mul_pos_iff_of_pos_left (inv_pos.2 ha)
  unfold areaScale
  have hset : {r : ℝ | 0 < r ∧ 1 ≤ (μ.map fun z => ((a : ℂ))⁻¹ * z) (Metric.ball 0 r ∩ H)} =
      a⁻¹ • {r : ℝ | 0 < r ∧ 1 ≤ μ (Metric.ball 0 r ∩ H)} := by
    ext r
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ha.ne'), inv_inv, smul_eq_mul]
    simp only [Set.mem_ofPred_eq]
    rw [Measure.map_apply hmeas (Metric.isOpen_ball.measurableSet.inter measurableSet_H_mu), hpre]
    exact and_congr (mul_pos_iff_of_pos_left ha).symm Iff.rfl
  rw [hset, Real.sInf_smul_of_nonneg (inv_nonneg.2 ha.le), smul_eq_mul, div_eq_inv_mul]

/-- Restricting to `ℍ ∖ K` does not change the scale (1.8) when `K ∩ ℍ` is `μ`-null. -/
theorem areaScale_restrict_diff_of_null {μ : Measure ℂ} {K : Set ℂ} (hK : μ (K ∩ H) = 0) :
    areaScale (μ.restrict (H \ K)) = areaScale μ := by
  unfold areaScale
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  rw [Measure.restrict_apply (Metric.isOpen_ball.measurableSet.inter measurableSet_H_mu)]
  have : Metric.ball 0 r ∩ H ∩ (H \ K) = (Metric.ball 0 r ∩ H) \ (K ∩ H) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_sdiff]
    tauto
  rw [this, measure_sdiff_null hK]

/-- Restricting to `ℍ` does not change the scale (1.8). -/
theorem areaScale_restrict_H (μ : Measure ℂ) : areaScale (μ.restrict H) = areaScale μ := by
  simpa using areaScale_restrict_diff_of_null (μ := μ) (K := ∅) (by simp)

/-- The zip-up driver of `zipWeldUp` is continuous. -/
theorem continuous_zipWeldUp_drv {γ T : ℝ} (hT : 0 ≤ T) {W' : ℝ → ℝ} (hW' : Continuous W')
    (hW'0 : W' 0 = 0) {c : FieldSample × (ℝ → ℝ)} (hc : Continuous c.2) (hc0 : c.2 0 = 0) :
    Continuous (zipWeldUp γ T W' c).2 := by
  simp only [zipWeldUp]
  refine Continuous.if_le ((hW'.comp (continuous_const.sub
    (continuous_id.max continuous_const))).sub continuous_const)
    ((hc.comp (continuous_id.sub continuous_const)).sub continuous_const) continuous_id
    continuous_const fun s hs => ?_
  rw [hs, max_eq_left hT, sub_self, hW'0, hc0]

/-- **Round trip down-then-up, area part.** Zipping up, along the reverse driver
`s ↦ W(t − s) − W t` of the unzipped segment, what was unzipped by capacity `t` returns the
restriction of the carried area to `ℍ ∖ K_t`. -/
theorem zipWeldUpA_zipCapDownA_area {γ t : ℝ} (ht : 0 ≤ t) {c : AreaConfig}
    (hc : Continuous c.drv) (hc0 : c.drv 0 = 0) :
    (zipWeldUpA γ t (fun s => c.drv (t - s) - c.drv t) (zipCapDownA γ t c)).area =
      c.area.restrict (H \ fwdHull c.drv t) := by
  set W := c.drv with hWdef
  set W'' : ℝ → ℝ := fun s => W (t - s) - W t with hW''def
  have hW'' : Continuous W'' := (hc.comp (continuous_const.sub continuous_id)).sub continuous_const
  have hW''0 : W'' 0 = 0 := by simp [hW''def]
  have hVV : (fun s => W'' (t - s) - W'' t) = W := by
    funext s; simp only [hW''def, sub_sub_cancel, sub_self, hc0]; ring
  set U := H \ fwdHull W t with hUdef
  have hU : MeasurableSet U := (FwdHolo.isOpen_compl_fwdHull hc ht).measurableSet
  set ν := c.area.restrict U with hν
  have hF : AEMeasurable (fwdMap W t) ν :=
    (FwdHolo.differentiableOn_fwdMap hc ht).continuousOn.aemeasurable hU
  have hae : ∀ᵐ z ∂ν, z ∈ U := ae_restrict_mem hU
  have hres : (ν.map (fwdMap W t)).restrict H = ν.map (fwdMap W t) :=
    Measure.restrict_eq_self_of_ae_mem ((ae_map_iff hF (p := (· ∈ H)) measurableSet_H_mu).2
      (hae.mono fun z hz => FwdHolo.mapsTo_fwdMap hc ht hz))
  show ((ν.map (fwdMap W t)).restrict H).map (revMap W'' t) = ν
  rw [hres]
  have hR : AEMeasurable (revMap W'' t) (ν.map (fwdMap W t)) := by
    rw [← hres]
    exact (differentiableOn_revMap W'' hW'' ht).continuousOn.aemeasurable
      measurableSet_H_mu
  rw [AEMeasurable.map_map_of_aemeasurable hR hF]
  conv_rhs => rw [← Measure.map_id (μ := ν)]
  refine Measure.map_congr (hae.mono fun z hz => ?_)
  simp only [Function.comp_apply, id]
  have hw : fwdMap W t z ∈ H := FwdHolo.mapsTo_fwdMap hc ht hz
  obtain ⟨h1, h2⟩ := UnzipInvariance.fwdMap_revMap_timeRev_of_nonneg W'' hW'' hW''0 ht hw
  rw [hVV] at h1 h2
  have hmem : revMap W'' t (fwdMap W t z) ∈ U :=
    ⟨lt_of_lt_of_le hw (im_le_im_revMap W'' hW'' _ hw ht), h1⟩
  exact FwdHolo.injOn_fwdMap hc ht hmem hz h2

end R18
end QuantumZipper
