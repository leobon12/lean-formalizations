import QuantumZipper.Proofs.LQG.AreaP3bInner

/-!
# M4-P3(b), area version, part 2: Gaussian laws of the interior inner field

Continuation of `AreaP3bInner`. For the inner field `Y = innerS X z δ D R` at the radius
`ε = 2^{-k}` we identify (almost surely, pointwise in `w`)
`Y_ε(w) = Z_ε(w) − Ω` and `Y_{ε/2}(w) − Y_ε(w) = Z_{ε/2}(w) − Z_ε(w)`, compute the variance
`Var Y_ε(w) = log(δ/ε) + 2 log R − log D − log ‖w − w̄‖`, and instantiate the Gaussian
hypotheses `TwoRadiusC.TRLHypC` of the planar two-radius lemma for the inner field
(`trlHypC_inner`), with `L = ½ log(δ/ε)` measured **relative to `δ`**. This is the interior
analogue of `FracMom.trlHyp_inner` (boundary case).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaP3b

open GaussTK KernelId TwoRadiusC

section Cov

variable {z w : ℂ} {δ D R ε : ℝ}

theorem fcPairCov_Z_omZ (hε : 0 < ε) (hwe : ‖w - z‖ + ε ≤ δ) (hδD : δ ≤ D) (hDz : D ≤ z.im)
    (hDR : ‖z‖ + D ≤ R) :
    fcPairCov (w, ε, 0, R) (z, δ, z, D) = log D - log δ := by
  have hδ : 0 < δ := by linarith [norm_nonneg (w - z)]
  have hD : 0 < D := by linarith
  have hεw : ε ≤ w.im := im_ge_of_inner hwe (hδD.trans hDz)
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_nested' hε hεw (hδD.trans hDz) hwe,
    kernelCov_fc_interior_nested' hε hεw hDz (by linarith),
    kernelCov_fc_bigCircle_left hδ (by linarith), kernelCov_fc_bigCircle_left hD hDR]
  ring

theorem fcPairCov_omZ_self (hδ : 0 < δ) (hδD : δ ≤ D) (hDz : D ≤ z.im) :
    fcPairCov (z, δ, z, D) (z, δ, z, D) = log D - log δ := by
  have hD : 0 < D := by linarith
  have hδz : δ ≤ z.im := hδD.trans hDz
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_sameCenter hδ hδ hδz hδz,
    kernelCov_fc_interior_sameCenter hδ hD hδz hDz,
    kernelCov_fc_interior_sameCenter hD hδ hDz hδz,
    kernelCov_fc_interior_sameCenter hD hD hDz hDz, max_self, max_self, max_eq_right hδD,
    max_eq_left hδD]
  ring

theorem fcPairCov_incr_omZ (hε : 0 < ε) (hwe : ‖w - z‖ + ε ≤ δ) (hδD : δ ≤ D)
    (hDz : D ≤ z.im) :
    fcPairCov (w, ε / 2, w, ε) (z, δ, z, D) = 0 := by
  have hεw : ε ≤ w.im := im_ge_of_inner hwe (hδD.trans hDz)
  have hε2 : 0 < ε / 2 := by positivity
  have hε2w : ε / 2 ≤ w.im := by linarith
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_interior_nested' hε2 hε2w (hδD.trans hDz) (by linarith),
    kernelCov_fc_interior_nested' hε2 hε2w hDz (by linarith),
    kernelCov_fc_interior_nested' hε hεw (hδD.trans hDz) hwe,
    kernelCov_fc_interior_nested' hε hεw hDz (by linarith)]
  ring

end Cov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Law of a difference of two pair values. -/
theorem hasLaw_fcPairVal_sub [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {p q : FcIdx} (hp : p.Good) (hq : q.Good) :
    HasLaw (fun ω => fcPairVal X p ω - fcPairVal X q ω)
      (gaussianReal 0 (fcPairCov p p - 2 * fcPairCov p q + fcPairCov q q).toNNReal) P := by
  have hG := (isGaussianProcess_fcPair hX (P := P)).hasGaussianLaw_fun_sub
    (s := ⟨p, hp⟩) (t := ⟨q, hq⟩)
  have hm : AEMeasurable (fun ω => fcPairVal X p ω - fcPairVal X q ω) P :=
    ((measurable_fcPairVal hX p).sub (measurable_fcPairVal hX q)).aemeasurable
  have hLp : MemLp (fcPairVal X p) 2 P :=
    ((isGaussianProcess_fcPair hX (P := P)).hasGaussianLaw_eval ⟨p, hp⟩).memLp_two
  have hLq : MemLp (fcPairVal X q) 2 P :=
    ((isGaussianProcess_fcPair hX (P := P)).hasGaussianLaw_eval ⟨q, hq⟩).memLp_two
  refine ⟨hm, ?_⟩
  rw [hG.map_eq_gaussianReal, integral_sub (hLp.integrable one_le_two)
    (hLq.integrable one_le_two), integral_fcPairVal hX hp, integral_fcPairVal hX hq, sub_zero,
    variance_fun_sub hLp hLq, ← covariance_self (measurable_fcPairVal hX p).aemeasurable,
    ← covariance_self (measurable_fcPairVal hX q).aemeasurable, covariance_fcPairVal hX hp hp,
    covariance_fcPairVal hX hp hq, covariance_fcPairVal hX hq hq]

/-- Inner coordinate `Y_{2^{-k}}(w)`. -/
def iU (X : Ω → FieldSample) (z : ℂ) (δ D R : ℝ) (k : ℕ) (w : ℂ) (ω : Ω) : ℝ :=
  avgReg (innerS X z δ D R ω) k w

/-- Inner increment `Y_{2^{-k-1}}(w) − Y_{2^{-k}}(w)`. -/
def iΔ (X : Ω → FieldSample) (z : ℂ) (δ D R : ℝ) (k : ℕ) (w : ℂ) (ω : Ω) : ℝ :=
  iU X z δ D R (k + 1) w ω - iU X z δ D R k w ω

theorem measurable_iU (hX : IsFreeGFFModConstH X P) (z : ℂ) (δ D R : ℝ) (k : ℕ) :
    Measurable (fun p : ℂ × Ω => iU X z δ D R k p.1 p.2) :=
  (measurable_avgReg k).comp
    (((measurable_innerS hX z δ D R).comp measurable_snd).prodMk measurable_fst)

theorem iU_ae_eq (hX : IsFreeGFFModConstH X P) {z : ℂ} {δ D R : ℝ} {k : ℕ} {w : ℂ}
    (hw : w ∈ Hbar) (hs : ‖w - z‖ + radius k < δ) :
    iU X z δ D R k w =ᵐ[P]
      fun ω => fcPairVal X (w, radius k, 0, R) ω - fcPairVal X (z, δ, z, D) ω := by
  filter_upwards [ae_avgReg_aZ_eq_inner hX (P := P) z δ D R k,
    AreaExist.avgReg_aZ_ae_eq hX R k hw] with ω h1 h2
  have := h1 w hw hs
  rw [h2] at this
  simp only [iU, omZ] at this ⊢
  linarith

theorem iΔ_ae_eq (hX : IsFreeGFFModConstH X P) {z : ℂ} {δ D R : ℝ} {k : ℕ} {w : ℂ}
    (hw : w ∈ Hbar) (hs : ‖w - z‖ + radius k < δ) :
    iΔ X z δ D R k w =ᵐ[P] fcPairVal X (w, radius k / 2, w, radius k) := by
  have hs1 : ‖w - z‖ + radius (k + 1) < δ := by
    rw [AreaExist.aradius_succ]; linarith [radius_pos k]
  filter_upwards [iU_ae_eq hX (P := P) (D := D) (R := R) hw hs,
    iU_ae_eq hX (P := P) (D := D) (R := R) hw hs1] with ω h1 h2
  simp only [iΔ, h1, h2, fcPairVal, AreaExist.aradius_succ]
  ring

/-- Variance of the inner coordinate. -/
def vI (z : ℂ) (δ D R : ℝ) (k : ℕ) (w : ℂ) : ℝ≥0 :=
  (2 * log R - log (radius k) - log ‖w - conj w‖ - log D + log δ).toNNReal

theorem hasLaw_iU [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {z : ℂ} {δ D R : ℝ}
    (hδD : δ ≤ D) (hDz : D ≤ z.im) (hDR : ‖z‖ + D ≤ R) {k : ℕ} {w : ℂ}
    (hs : ‖w - z‖ + radius k < δ) :
    HasLaw (iU X z δ D R k w) (gaussianReal 0 (vI z δ D R k w)) P := by
  have hr := radius_pos k
  have hδ : 0 < δ := by linarith [norm_nonneg (w - z)]
  have hrw : radius k ≤ w.im := im_ge_of_inner hs.le (hδD.trans hDz)
  have hw : w ∈ Hbar := AreaExist.mem_Hbar_of_le_im hr hrw
  have hwR : ‖w‖ + radius k ≤ R := by
    have := norm_add_le (w - z) z
    rw [sub_add_cancel] at this
    linarith
  have hR0 : 0 < R := by linarith [norm_nonneg w]
  have hL := (hasLaw_fcPairVal_sub hX (P := P) (good_Z hw hr hR0)
    (good_omZ hδ hδD hDz)).congr (iU_ae_eq hX hw hs)
  rw [AreaExist.fcPairCov_Zself_int hr hrw hwR, fcPairCov_Z_omZ hr hs.le hδD hDz hDR,
    fcPairCov_omZ_self hδ hδD hDz] at hL
  convert hL using 3
  simp only [vI]
  congr 1
  ring

/-- **The Gaussian hypotheses of the planar two-radius lemma for the inner field**, at the radii
`2^{-k}` and `2^{-k-1}`, with `L = ½ log(δ/2^{-k})` and `K = 2 log R − log D − log(2d)`. -/
theorem trlHypC_inner [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {z : ℂ}
    {δ D R d : ℝ} (hδD : δ ≤ D) (hDz : D ≤ z.im) (hDR : ‖z‖ + D ≤ R) (hD1 : D ≤ 1)
    (hR1 : 1 ≤ R) (hd : 0 < d) (hd1 : 2 * d ≤ 1) {S : Set ℂ} (hSd : ∀ w ∈ S, d ≤ w.im) {k : ℕ}
    (hSk : ∀ w ∈ S, ‖w - z‖ + radius k < δ) :
    TRLHypC P S (2 * radius k) (2 * log R - log D - log (2 * d)) (log 2)
      (fun _ => 1 / 2 * log (δ / radius k)) (vI z δ D R k) (fun _ => (log 2).toNNReal)
      (iU X z δ D R k) (iΔ X z δ D R k) := by
  have hr := radius_pos k
  have hlog2 : (0 : ℝ) ≤ log 2 := log_nonneg one_le_two
  have hδ : ∀ w ∈ S, 0 < δ := fun w hw => by linarith [norm_nonneg (w - z), hSk w hw]
  have hrw : ∀ w ∈ S, radius k ≤ w.im := fun w hw =>
    im_ge_of_inner (hSk w hw).le (hδD.trans hDz)
  have hwH : ∀ w ∈ S, w ∈ Hbar := fun w hw => AreaExist.mem_Hbar_of_le_im hr (hrw w hw)
  have hwR : ∀ w ∈ S, ‖w‖ + radius k ≤ R := fun w hw => by
    have := norm_add_le (w - z) z
    rw [sub_add_cancel] at this
    linarith [hSk w hw]
  have hR0 : 0 < R := by linarith
  refine
    { measU := measurable_iU hX z δ D R k
      measΔ := (measurable_iU hX z δ D R (k + 1)).sub (measurable_iU hX z δ D R k)
      measL := measurable_const
      measw := measurable_const
      lawU := fun w hw => hasLaw_iU hX hδD hDz hDR (hSk w hw)
      lawΔ := ?_, varU := ?_, varΔ := ?_, indep := ?_, decor := ?_ }
  · intro w hw
    have := (AreaExist.hasLaw_fcPairVal' hX (P := P) (p := (w, radius k / 2, w, radius k))
      ⟨hwH w hw, by positivity, hwH w hw, hr⟩).congr
        (iΔ_ae_eq (D := D) (R := R) hX (hwH w hw) (hSk w hw))
    rwa [AreaExist.fcPairCov_incr_self_int hr (hrw w hw)] at this
  · intro w hw
    have hlogR : 0 ≤ log R := log_nonneg hR1
    have hlogD : log D ≤ 0 := log_nonpos (by linarith [hδ w hw]) hD1
    have hlogd : log (2 * d) ≤ 0 := log_nonpos (by positivity) hd1
    have hc : log (2 * d) ≤ log ‖w - conj w‖ :=
      log_le_log (by positivity) (by linarith [AreaExist.two_im_le_norm_sub_conj w, hSd w hw])
    have hL0 : 0 ≤ log (δ / radius k) :=
      log_nonneg (by rw [le_div_iff₀ hr]; linarith [norm_nonneg (w - z), hSk w hw])
    rw [log_div (hδ w hw).ne' hr.ne'] at hL0 ⊢
    show ((2 * log R - log (radius k) - log ‖w - conj w‖ - log D + log δ).toNNReal : ℝ) ≤ _
    rw [Real.coe_toNNReal']
    exact max_le (by linarith) (by linarith)
  · intro w _
    exact (Real.coe_toNNReal _ hlog2).le
  · intro w hw
    have hI := indepFun_fcPair hX (P := P)
      (fun _ : Unit => (⟨(w, radius k / 2, w, radius k),
        ⟨hwH w hw, by positivity, hwH w hw, hr⟩⟩ : {p : FcIdx // p.Good}))
      (fun i : Fin 2 => (⟨![(w, radius k, 0, R), (z, δ, z, D)] i, by
        fin_cases i
        · exact good_Z (hwH w hw) hr hR0
        · exact good_omZ (hδ w hw) hδD hDz⟩ : {p : FcIdx // p.Good}))
      (fun _ i => by
        fin_cases i
        · exact AreaExist.fcPairCov_incr_Zsame_int (by positivity) (by linarith) (hrw w hw)
            (hwR w hw)
        · exact fcPairCov_incr_omZ hr (hSk w hw).le hδD hDz)
    have hφ : Measurable (fun v : Fin 2 → ℝ => v 0 - v 1) :=
      (measurable_pi_apply 0).sub (measurable_pi_apply 1)
    have hI2 := hI.comp (measurable_pi_apply ()) hφ
    exact hI2.congr (iΔ_ae_eq hX (hwH w hw) (hSk w hw)).symm (iU_ae_eq hX (hwH w hw) (hSk w hw)).symm
  · intro t ht u hu htu
    have hI := indepFun_fcPair hX (P := P)
      (fun _ : Unit => (⟨(t, radius k / 2, t, radius k),
        ⟨hwH t ht, by positivity, hwH t ht, hr⟩⟩ : {p : FcIdx // p.Good}))
      (fun i : Fin 4 => (⟨![(t, radius k, 0, R), (u, radius k, 0, R), (z, δ, z, D),
          (u, radius k / 2, u, radius k)] i, by
        fin_cases i
        · exact good_Z (hwH t ht) hr hR0
        · exact good_Z (hwH u hu) hr hR0
        · exact good_omZ (hδ t ht) hδD hDz
        · exact ⟨hwH u hu, div_pos hr two_pos, hwH u hu, hr⟩⟩ : {p : FcIdx // p.Good}))
      (fun _ i => by
        fin_cases i
        · exact AreaExist.fcPairCov_incr_Zsame_int (by positivity) (by linarith) (hrw t ht)
            (hwR t ht)
        · exact AreaExist.fcPairCov_incr_Zfar_int (by positivity) (by linarith) (hrw t ht) hr
            (hrw u hu) (hwR t ht) (by linarith)
        · exact fcPairCov_incr_omZ hr (hSk t ht).le hδD hDz
        · exact AreaExist.fcPairCov_incr_incr_far_int (by positivity) (by linarith) (hrw t ht)
            (by positivity) (by linarith) (hrw u hu) (by linarith))
    have hφ : Measurable (fun v : Fin 4 → ℝ => (v 0 - v 2, v 1 - v 2, v 3)) :=
      ((measurable_pi_apply 0).sub (measurable_pi_apply 2)).prodMk
        (((measurable_pi_apply 1).sub (measurable_pi_apply 2)).prodMk (measurable_pi_apply 3))
    have hI2 := hI.comp (measurable_pi_apply ()) hφ
    refine hI2.congr (iΔ_ae_eq hX (hwH t ht) (hSk t ht)).symm ?_
    filter_upwards [iU_ae_eq hX (P := P) (D := D) (R := R) (hwH t ht) (hSk t ht),
      iU_ae_eq hX (P := P) (D := D) (R := R) (hwH u hu) (hSk u hu),
      iΔ_ae_eq hX (P := P) (D := D) (R := R) (hwH u hu) (hSk u hu)] with ω h1 h2 h3
    simp [h1, h2, h3]

end AreaP3b
end QuantumZipper
