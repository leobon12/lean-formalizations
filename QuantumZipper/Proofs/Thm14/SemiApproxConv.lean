import QuantumZipper.Proofs.Thm14.SemiApproxGeom
import QuantumZipper.Proofs.Zipper.TReg

/-!
# SEMI-APPROX, part 4: dominated convergence in the parameter space

For weights `w_j → v` (uniformly bounded, converging on the box) and radii perturbations
`e_j → 0` with `|e_j| ≤ s/4`:

* `sa_kernelCov_tendsto`: the pushed-forward Neumann covariances of
  `(saM.withDensity w_j).map (f ∘ Γ_{e_j})` converge to those of the limit measures;
* `sa_integral_tendsto`: `∫ w_j · 𝔥_T ∘ Γ_{e_j} dm → ∫ v · 𝔥_T ∘ Γ_0 dm`.

Domination: `abs_neumannH_revMap_le` and `abs_hTrev_le`, with the geometric bounds of
`SemiApproxGeom`; integrability `integrable_logChord_saM`, `integrable_logSin_saM`. Pointwise
limits off the null diagonal `{θ = θ'}`: `revMap` is continuous and injective on `ℍ`, `neumannH`
is continuous off the diagonal and its reflection, `𝔥_T` is continuous on `ℍ`. Own elementary
argument.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Real NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm14WDG

theorem sa_ae_good :
    ∀ᵐ x ∂(saM.prod saM), x.1 ∈ saBox ∧ x.2 ∈ saBox ∧ x.1.2 ≠ x.2.2 := by
  have h1 : ∀ᵐ x ∂(saM.prod saM), x.1 ∈ saBox := Measure.quasiMeasurePreserving_fst.ae ae_saM_mem
  have h2 : ∀ᵐ x ∂(saM.prod saM), x.2 ∈ saBox := Measure.quasiMeasurePreserving_snd.ae ae_saM_mem
  have h3 : ∀ᵐ x ∂(saM.prod saM), x.1.2 ≠ x.2.2 := by
    have hS : MeasurableSet {x : (ℝ × ℝ) × (ℝ × ℝ) | x.1.2 = x.2.2} :=
      measurableSet_eq_fun (measurable_snd.comp measurable_fst) (measurable_snd.comp measurable_snd)
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [Measure.measure_prod_null hS]
    refine ae_of_all _ fun p => ?_
    have : Prod.mk p ⁻¹' {x : (ℝ × ℝ) × (ℝ × ℝ) | x.1.2 = x.2.2} = univ ×ˢ {p.2} := by
      ext q; simp [eq_comm]
    simp only [Pi.zero_apply]
    rw [this]
    unfold saM
    rw [Measure.prod_prod]
    exact mul_eq_zero_of_right _ (nonpos_iff_eq_zero.1 ((Measure.restrict_le_self (μ := volume)
      (s := Ioo 0 π)) {p.2} |>.trans (measure_singleton _).le))
  filter_upwards [h1, h2, h3] with x a b c using ⟨a, b, c⟩

theorem sa_continuousAt_neumannH {a b : ℂ} (h1 : a ≠ b) (h2 : a ≠ conj b) :
    ContinuousAt (fun y : ℂ × ℂ => neumannH y.1 y.2) (a, b) := by
  unfold neumannH
  refine ((ContinuousAt.log (by fun_prop) ?_).neg).sub (ContinuousAt.log (by fun_prop) ?_)
  · exact norm_ne_zero_iff.2 (sub_ne_zero.2 h1)
  · exact norm_ne_zero_iff.2 (sub_ne_zero.2 h2)

theorem tendsto_saGam (c s : ℝ) {e : ℕ → ℝ} (hl : Tendsto e atTop (𝓝 0)) (p : ℝ × ℝ) :
    Tendsto (fun j => saGam c s (e j) p) atTop (𝓝 (saGam c s 0 p)) := by
  have hGe : Continuous fun e : ℝ => saGam c s e p :=
    (continuous_circleMap_prod (c : ℂ)).comp
      ((continuous_const.add (continuous_id.mul continuous_const)).prodMk continuous_const)
  exact (hGe.tendsto 0).comp hl

theorem sa_abs_zero_le {s : ℝ} (hs : 0 < s) : |(0 : ℝ)| ≤ s / 4 := by
  rw [abs_zero]; positivity

/-- **Dominated convergence for the pushed-forward Neumann covariances.** -/
theorem sa_kernelCov_tendsto {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (c : ℝ)
    {s : ℝ} (hs : 0 < s) {e₁ e₂ : ℕ → ℝ} (he₁ : ∀ j, |e₁ j| ≤ s / 4) (he₂ : ∀ j, |e₂ j| ≤ s / 4)
    (hl₁ : Tendsto e₁ atTop (𝓝 0)) (hl₂ : Tendsto e₂ atTop (𝓝 0))
    {w₁ w₂ : ℕ → ℝ × ℝ → ℝ≥0} {v₁ v₂ : ℝ × ℝ → ℝ≥0}
    (hw₁ : ∀ j, Measurable (w₁ j)) (hw₂ : ∀ j, Measurable (w₂ j))
    (hv₁ : Measurable v₁) (hv₂ : Measurable v₂) {M : ℝ} (hM : 0 ≤ M)
    (hM₁ : ∀ j p, (w₁ j p : ℝ) ≤ M) (hM₂ : ∀ j p, (w₂ j p : ℝ) ≤ M)
    (hc₁ : ∀ p : ℝ × ℝ, p ∈ saBox → Tendsto (fun j => w₁ j p) atTop (𝓝 (v₁ p)))
    (hc₂ : ∀ p : ℝ × ℝ, p ∈ saBox → Tendsto (fun j => w₂ j p) atTop (𝓝 (v₂ p))) :
    Tendsto (fun j => kernelCov neumannH
        ((saM.withDensity fun p => (w₁ j p : ℝ≥0∞)).map (revMap W T ∘ saGam c s (e₁ j)))
        ((saM.withDensity fun p => (w₂ j p : ℝ≥0∞)).map (revMap W T ∘ saGam c s (e₂ j)))) atTop
      (𝓝 (kernelCov neumannH
        ((saM.withDensity fun p => (v₁ p : ℝ≥0∞)).map (revMap W T ∘ saGam c s 0))
        ((saM.withDensity fun p => (v₂ p : ℝ≥0∞)).map (revMap W T ∘ saGam c s 0)))) := by
  have hfm : Measurable (revMap W T) := TwoPoint.measurable_revMap hW hT
  have hK := TwoPoint.measurable_neumannH_uncurry
  have key : ∀ (a b : ℝ × ℝ → ℝ≥0) (ea eb : ℝ), Measurable a → Measurable b →
      kernelCov neumannH ((saM.withDensity fun p => (a p : ℝ≥0∞)).map (revMap W T ∘ saGam c s ea))
        ((saM.withDensity fun p => (b p : ℝ≥0∞)).map (revMap W T ∘ saGam c s eb)) =
      ∫ p, ∫ q, (a p : ℝ) * ((b q : ℝ) *
        neumannH (revMap W T (saGam c s ea p)) (revMap W T (saGam c s eb q))) ∂saM ∂saM := by
    intro a b ea eb ha hb
    rw [kernelCov_map_withDensity ha hb (hfm.comp (continuous_saGam _ _ _).measurable)
      (hfm.comp (continuous_saGam _ _ _).measurable) hK]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [Function.comp_apply]
    rw [integral_const_mul]
  rw [key _ _ _ _ hv₁ hv₂]
  refine Tendsto.congr (fun j => (key _ _ _ _ (hw₁ j) (hw₂ j)).symm) ?_
  obtain ⟨C, hC⟩ := abs_neumannH_revMap_le hW hT (|c| + 2 * s)
  have hbound : ∀ ea eb : ℝ, |ea| ≤ s / 4 → |eb| ≤ s / 4 → ∀ x : (ℝ × ℝ) × (ℝ × ℝ),
      x.1 ∈ saBox → x.2 ∈ saBox → x.1.2 ≠ x.2.2 →
      |neumannH (revMap W T (saGam c s ea x.1)) (revMap W T (saGam c s eb x.2))| ≤
        C + 2 * (|Real.log (3 * s / 4)| + |Real.log (5 * s / 2)| +
          |Real.log ‖saU x.1.2 - saU x.2.2‖|) +
        (|Real.log (3 * s / 4)| + |Real.log (5 * s / 4)| + |Real.log (Real.sin x.1.2)|) +
        (|Real.log (3 * s / 4)| + |Real.log (5 * s / 4)| + |Real.log (Real.sin x.2.2)|) := by
    intro ea eb ha hb x h1 h2 h3
    have hu0 : 0 < ‖saU x.1.2 - saU x.2.2‖ := norm_pos_iff.2 (sub_ne_zero.2 (saU_ne h1.2 h2.2 h3))
    obtain ⟨d1, d2⟩ := dist_saGam_bounds (c := c) hs ha hb h1 h2
    have hne : saGam c s ea x.1 ≠ saGam c s eb x.2 := by
      intro h
      rw [h, sub_self, norm_zero] at d1
      nlinarith
    have hk := hC _ _ (saGam_mem_H hs ha h1) (saGam_mem_H hs hb h2) (norm_saGam_le hs ha h1)
      (norm_saGam_le hs hb h2) hne
    have hl1 := sa_abs_log_le (by positivity : (0 : ℝ) < 3 * s / 4) hu0 d1 d2
    obtain ⟨i1, i2⟩ := im_saGam_bounds (c := c) hs ha h1
    obtain ⟨i1', i2'⟩ := im_saGam_bounds (c := c) hs hb h2
    have hs1 := Real.sin_pos_of_pos_of_lt_pi h1.2.1 h1.2.2
    have hs2 := Real.sin_pos_of_pos_of_lt_pi h2.2.1 h2.2.2
    have hl2 := sa_abs_log_le (by positivity : (0 : ℝ) < 3 * s / 4) hs1 i1 i2
    have hl3 := sa_abs_log_le (by positivity : (0 : ℝ) < 3 * s / 4) hs2 i1' i2'
    linarith
  have hLS1 : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => |Real.log (Real.sin x.1.2)|)
      (saM.prod saM) := integrable_logSin_saM.comp_fst saM
  have hLS2 : Integrable (fun x : (ℝ × ℝ) × (ℝ × ℝ) => |Real.log (Real.sin x.2.2)|)
      (saM.prod saM) := integrable_logSin_saM.comp_snd saM
  refine tendsto_iterated_integral
    (F := fun j x => (w₁ j x.1 : ℝ) * ((w₂ j x.2 : ℝ) *
      neumannH (revMap W T (saGam c s (e₁ j) x.1)) (revMap W T (saGam c s (e₂ j) x.2))))
    (F₀ := fun x => (v₁ x.1 : ℝ) * ((v₂ x.2 : ℝ) *
      neumannH (revMap W T (saGam c s 0 x.1)) (revMap W T (saGam c s 0 x.2))))
    (D := fun x => M * (M * (C + 2 * (|Real.log (3 * s / 4)| + |Real.log (5 * s / 2)| +
          |Real.log ‖saU x.1.2 - saU x.2.2‖|) +
        (|Real.log (3 * s / 4)| + |Real.log (5 * s / 4)| + |Real.log (Real.sin x.1.2)|) +
        (|Real.log (3 * s / 4)| + |Real.log (5 * s / 4)| + |Real.log (Real.sin x.2.2)|))))
    (fun j => ?_) ?_ (fun j => ?_) ?_
  · exact (((hw₁ j).coe_nnreal_real.comp measurable_fst).mul
      (((hw₂ j).coe_nnreal_real.comp measurable_snd).mul (hK.comp
        ((hfm.comp ((continuous_saGam _ _ _).measurable.comp measurable_fst)).prodMk
          (hfm.comp ((continuous_saGam _ _ _).measurable.comp measurable_snd)))))).aestronglyMeasurable
  · refine Integrable.const_mul (Integrable.const_mul ?_ _) _
    exact ((((integrable_const _).add (((integrable_const _).add
      integrable_logChord_saM).const_mul 2)).add ((integrable_const _).add hLS1)).add
      ((integrable_const _).add hLS2))
  · filter_upwards [sa_ae_good] with x ⟨h1, h2, h3⟩
    have hk := hbound _ _ (he₁ j) (he₂ j) x h1 h2 h3
    rw [Real.norm_eq_abs, abs_mul, abs_mul, NNReal.abs_eq, NNReal.abs_eq]
    exact mul_le_mul (hM₁ j x.1) (mul_le_mul (hM₂ j x.2) hk (abs_nonneg _) hM)
      (mul_nonneg (NNReal.coe_nonneg _) (abs_nonneg _)) hM
  · filter_upwards [sa_ae_good] with x ⟨h1, h2, h3⟩
    have hz := saGam_mem_H (c := c) hs (sa_abs_zero_le hs) h1
    have hw := saGam_mem_H (c := c) hs (sa_abs_zero_le hs) h2
    have hne : saGam c s 0 x.1 ≠ saGam c s 0 x.2 := by
      have hu0 : 0 < ‖saU x.1.2 - saU x.2.2‖ :=
        norm_pos_iff.2 (sub_ne_zero.2 (saU_ne h1.2 h2.2 h3))
      obtain ⟨d1, -⟩ := dist_saGam_bounds (c := c) hs (sa_abs_zero_le hs) (sa_abs_zero_le hs) h1 h2
      intro h
      rw [h, sub_self, norm_zero] at d1
      nlinarith
    have hfne : revMap W T (saGam c s 0 x.1) ≠ revMap W T (saGam c s 0 x.2) :=
      fun h => hne (injOn_revMap W hW hT hz hw h)
    have hfne' : revMap W T (saGam c s 0 x.1) ≠ conj (revMap W T (saGam c s 0 x.2)) := by
      intro h
      have a1 := TwoPoint.im_revMap_pos hW hz hT
      have a2 := TwoPoint.im_revMap_pos hW hw hT
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    have hfc : ∀ z ∈ H, ContinuousAt (revMap W T) z := fun z hz =>
      (differentiableOn_revMap W hW hT).continuousOn.continuousAt (isOpen_H.mem_nhds hz)
    have t1 := ((hfc _ hz).tendsto.comp (tendsto_saGam c s hl₁ x.1))
    have t2 := ((hfc _ hw).tendsto.comp (tendsto_saGam c s hl₂ x.2))
    have tK := (sa_continuousAt_neumannH hfne hfne').tendsto.comp (t1.prodMk_nhds t2)
    have tw1 := (NNReal.continuous_coe.tendsto _).comp (hc₁ _ h1)
    have tw2 := (NNReal.continuous_coe.tendsto _).comp (hc₂ _ h2)
    exact tw1.mul (tw2.mul tK)

/-- **Dominated convergence for the deterministic term.** -/
theorem sa_integral_tendsto (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (c : ℝ) {s : ℝ} (hs : 0 < s) {e : ℕ → ℝ} (he : ∀ j, |e j| ≤ s / 4)
    (hl : Tendsto e atTop (𝓝 0)) {w : ℕ → ℝ × ℝ → ℝ≥0} {v : ℝ × ℝ → ℝ≥0}
    (hw : ∀ j, Measurable (w j)) {M : ℝ} (hM : 0 ≤ M) (hMw : ∀ j p, (w j p : ℝ) ≤ M)
    (hc : ∀ p : ℝ × ℝ, p ∈ saBox → Tendsto (fun j => w j p) atTop (𝓝 (v p))) :
    Tendsto (fun j => ∫ p, (w j p : ℝ) * hTrev κ W T (saGam c s (e j) p) ∂saM) atTop
      (𝓝 (∫ p, (v p : ℝ) * hTrev κ W T (saGam c s 0 p) ∂saM)) := by
  obtain ⟨C, C', hC⟩ := abs_hTrev_le κ hW hT (|c| + 2 * s)
  have hhm := TReg.measurable_hTrev κ hW hT
  refine tendsto_integral_of_dominated_convergence
    (fun p => M * (C + |C'| * (|Real.log (3 * s / 4)| + |Real.log (5 * s / 4)| +
      |Real.log (Real.sin p.2)|)))
    (fun j => (((hw j).coe_nnreal_real).mul (hhm.comp
      (continuous_saGam _ _ _).measurable)).aestronglyMeasurable)
    (((integrable_const C).add (((integrable_const _).add
      integrable_logSin_saM).const_mul |C'|)).const_mul M) (fun j => ?_) ?_
  · filter_upwards [ae_saM_mem] with p hp
    have hz := saGam_mem_H (c := c) hs (he j) hp
    have hk := hC _ hz (norm_saGam_le hs (he j) hp)
    obtain ⟨i1, i2⟩ := im_saGam_bounds (c := c) hs (he j) hp
    have hs1 := Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2
    have hl2 := sa_abs_log_le (by positivity : (0 : ℝ) < 3 * s / 4) hs1 i1 i2
    have hk' : |hTrev κ W T (saGam c s (e j) p)| ≤ C + |C'| * (|Real.log (3 * s / 4)| +
        |Real.log (5 * s / 4)| + |Real.log (Real.sin p.2)|) := by
      refine hk.trans ?_
      have := mul_le_mul_of_nonneg_left hl2 (abs_nonneg C')
      nlinarith [le_abs_self C', abs_nonneg (Real.log (saGam c s (e j) p).im)]
    rw [Real.norm_eq_abs, abs_mul, NNReal.abs_eq]
    exact mul_le_mul (hMw j p) hk' (abs_nonneg _) hM
  · filter_upwards [ae_saM_mem] with p hp
    have hz := saGam_mem_H (c := c) hs (sa_abs_zero_le hs) hp
    have t1 := ((CharFun.continuousOn_hTrev κ hW hT).continuousAt
      (isOpen_H.mem_nhds hz)).tendsto.comp (tendsto_saGam c s hl p)
    exact ((NNReal.continuous_coe.tendsto _).comp (hc _ hp)).mul t1

end Thm14WDG
end QuantumZipper
