import QuantumZipper.Proofs.GFF.K3.MixedM7D3
import QuantumZipper.Proofs.GFF.K3.MixedM6Kernel

/-!
# K3-mixed M7-a3, half-disc covariance, step D4: the reflection identity

For a finite measure `μ` on `Hbar ∩ closedBall t r'` (`0 < r' < r`), with `U = ball t r ∩ H`,
`V₀ = mixedSpace U (realSet (Icc (t − r) (t + r)))`, `B = ball t r` and `μ̃ = μ + conj_* μ`:

  `dualNormSq U V₀ μ = dualNormSq B (zeroSpace B) μ̃ / 2`   (`dualNormSq_halfDisc_eq_m7d`).

`≤` is D3 (`sq_integral_le_halfDisc_m7d`). `≥`: the even part `g_s = ½ (g + g ∘ conj)` of
`g ∈ zeroSpace B` lies in `V₀`, `∫ g_s dμ = ½ ∫ g dμ̃`, and `E_U(g_s) ≤ ½ E_B(g)` (convexity of
the energy and reflection symmetry).

This is the reflection principle for the Neumann condition: the mixed GFF on the half-disc is
the even part of the zero-boundary GFF on the disc. Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Real Topology ComplexConjugate ENNReal

namespace QuantumZipper.K3

/-- The even part of a function with respect to `conj`. -/
def evenPart (g : ℂ → ℝ) (z : ℂ) : ℝ := (1 / 2 : ℝ) * (g z + g (conj z))

theorem contDiff_comp_conj_m7d {n : WithTop ℕ∞} {g : ℂ → ℝ} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun z => g (conj z) :=
  hg.comp Complex.conjCLE.contDiff

theorem hasFDerivAt_evenPart_m7d {g : ℂ → ℝ} (hg : Differentiable ℝ g) (z : ℂ) :
    HasFDerivAt (evenPart g) ((1 / 2 : ℝ) • (fderiv ℝ g z +
      (fderiv ℝ g (conj z)).comp Complex.conjCLE.toContinuousLinearMap)) z := by
  have h2 : HasFDerivAt (fun z => g (conj z))
      ((fderiv ℝ g (conj z)).comp Complex.conjCLE.toContinuousLinearMap) z :=
    (hg (conj z)).hasFDerivAt.comp z Complex.conjCLE.hasFDerivAt
  exact ((hg z).hasFDerivAt.add h2).const_mul (1 / 2 : ℝ)

theorem sq_norm_fderiv_evenPart_le_m7d {g : ℂ → ℝ} (hg : Differentiable ℝ g) (z : ℂ) :
    ‖fderiv ℝ (evenPart g) z‖ ^ 2 ≤
      (1 / 2 : ℝ) * (‖fderiv ℝ g z‖ ^ 2 + ‖fderiv ℝ g (conj z)‖ ^ 2) := by
  rw [(hasFDerivAt_evenPart_m7d hg z).fderiv, norm_sq_clm_complex, norm_sq_clm_complex,
    norm_sq_clm_complex]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_one, Complex.conj_I, map_neg, smul_eq_mul]
  nlinarith [sq_nonneg (fderiv ℝ g z 1 - fderiv ℝ g (conj z) 1),
    sq_nonneg (fderiv ℝ g z Complex.I + fderiv ℝ g (conj z) Complex.I)]

theorem evenPart_mem_m7d {t r : ℝ} {g : ℂ → ℝ} (hg : g ∈ zeroSpace (ball (t : ℂ) r)) :
    evenPart g ∈ mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r))) := by
  obtain ⟨hgs, hgc, hgt⟩ := hg
  have hes : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evenPart g) :=
    contDiff_const.mul (hgs.add (contDiff_comp_conj_m7d hgs))
  refine ⟨hes, ?_, (tsupport g)ᶜ ∩ (conj ⁻¹' tsupport g)ᶜ,
    (isClosed_tsupport g).isOpen_compl.inter
      ((isClosed_tsupport g).preimage Complex.continuous_conj).isOpen_compl, ?_, ?_⟩
  · refine ((hes.continuous_fderiv (by simp)).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (t : ℂ) r) |>.mono_set
      (inter_subset_left.trans ball_subset_closedBall)
  · rintro z ⟨hz, hzS⟩
    have hopen : IsOpen (ball (t : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
    rw [hopen.frontier_eq] at hz
    have hzB : z ∉ ball (t : ℂ) r := by
      intro hzB
      have hzH : z ∉ H := fun h => hz.2 ⟨hzB, h⟩
      have hHH : H ⊆ Hbar := fun w hw =>
        show (0 : ℝ) ≤ w.im from le_of_lt (show (0 : ℝ) < w.im from hw)
      have hzHb : z ∈ Hbar := closure_minimal (inter_subset_right.trans hHH) isClosed_Hbar hz.1
      have him : z.im = 0 := le_antisymm (not_lt.1 hzH) hzHb
      apply hzS
      refine ⟨z.re, ?_, Complex.ext (by simp) (by simp [him])⟩
      have : ‖z - t‖ < r := by rwa [mem_ball, dist_eq_norm] at hzB
      have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
      rw [hzr, norm_ofReal_sub_ofReal_m7d, abs_lt] at this
      exact ⟨by linarith, by linarith⟩
    refine ⟨fun h => hzB (hgt h), fun h => hzB ?_⟩
    have := hgt h
    rw [mem_ball, dist_eq_norm, norm_conj_sub_ofReal_k3] at this
    rwa [mem_ball, dist_eq_norm]
  · rintro z ⟨h1, h2⟩
    simp only [evenPart, image_eq_zero_of_notMem_tsupport h1,
      image_eq_zero_of_notMem_tsupport h2, add_zero, mul_zero]

/-- **D4 (energy of the even part).** -/
theorem energy_evenPart_le_m7d {t r : ℝ} {g : ℂ → ℝ} (hg : g ∈ zeroSpace (ball (t : ℂ) r)) :
    dirichletEnergyOn (ball (t : ℂ) r ∩ H) (evenPart g) ≤
      (1 / 2 : ℝ) * dirichletEnergyOn (ball (t : ℂ) r) g := by
  obtain ⟨hgs, hgc, hgt⟩ := hg
  have hgd : Differentiable ℝ g := hgs.differentiable (by simp)
  set B := ball (t : ℂ) r with hB
  have hDc : Continuous fun z => ‖fderiv ℝ g z‖ ^ 2 :=
    (hgs.continuous_fderiv (by simp)).norm.pow 2
  have hDcc : Continuous fun z => ‖fderiv ℝ g (conj z)‖ ^ 2 :=
    hDc.comp Complex.continuous_conj
  set h : ℂ → ℝ := B.indicator fun z => ‖fderiv ℝ g z‖ ^ 2 + ‖fderiv ℝ g (conj z)‖ ^ 2
  have hBm : MeasurableSet B := isOpen_ball.measurableSet
  have hint : ∀ φ : ℂ → ℝ, Continuous φ → IntegrableOn φ B := fun φ hφ =>
    (hφ.continuousOn.integrableOn_compact (isCompact_closedBall (t : ℂ) r)).mono_set
      ball_subset_closedBall
  have hhi : Integrable h := ((hint _ (hDc.add hDcc))).integrable_indicator hBm
  have hconjB : ∀ z, conj z ∈ B ↔ z ∈ B := fun z => by
    simp only [hB, mem_ball, dist_eq_norm, norm_conj_sub_ofReal_k3]
  have heven : ∀ z, h (conj z) = h z := by
    intro z
    by_cases hz : z ∈ B
    · simp only [h, indicator_of_mem hz, indicator_of_mem ((hconjB z).2 hz),
        Complex.conj_conj]; ring
    · simp only [h, indicator_of_notMem hz, indicator_of_notMem (fun h' => hz ((hconjB z).1 h'))]
  have h2 := integral_eq_two_mul_setIntegral_H hhi heven
  -- `∫ h = 2 ∫_B ‖Dg‖²`
  have hmp : MeasurePreserving (Complex.conjLIE : ℂ → ℂ) volume volume :=
    Complex.conjLIE.measurePreserving
  have hemb : MeasurableEmbedding (Complex.conjLIE : ℂ → ℂ) :=
    Complex.conjLIE.toHomeomorph.measurableEmbedding
  have hpre : (Complex.conjLIE : ℂ → ℂ) ⁻¹' B = B := by
    ext z; simp only [mem_preimage, Complex.conjLIE_apply]; exact hconjB z
  have hconjint : ∫ z in B, ‖fderiv ℝ g (conj z)‖ ^ 2 = ∫ z in B, ‖fderiv ℝ g z‖ ^ 2 := by
    have := hmp.setIntegral_preimage_emb hemb (fun z => ‖fderiv ℝ g z‖ ^ 2) B
    rw [hpre] at this
    simpa using this
  have hwhole : ∫ z, h z = 2 * ∫ z in B, ‖fderiv ℝ g z‖ ^ 2 := by
    rw [integral_indicator hBm, integral_add (hint _ hDc) (hint _ hDcc), hconjint]; ring
  -- `∫_H h = ∫_U (…)`
  have hU : ∫ z in H, h z = ∫ z in B ∩ H,
      (‖fderiv ℝ g z‖ ^ 2 + ‖fderiv ℝ g (conj z)‖ ^ 2) := by
    rw [setIntegral_indicator hBm, inter_comm]
  -- pointwise convexity
  have hUm : MeasurableSet (B ∩ H) := hBm.inter measurableSet_H_k3
  have hes : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (evenPart g) :=
    contDiff_const.mul (hgs.add (contDiff_comp_conj_m7d hgs))
  have hi1 : IntegrableOn (fun z => ‖fderiv ℝ (evenPart g) z‖ ^ 2) (B ∩ H) :=
    (hint _ ((hes.continuous_fderiv (by simp)).norm.pow 2)).mono_set inter_subset_left
  have hi2 : IntegrableOn (fun z => (1 / 2 : ℝ) *
      (‖fderiv ℝ g z‖ ^ 2 + ‖fderiv ℝ g (conj z)‖ ^ 2)) (B ∩ H) :=
    ((hint _ (hDc.add hDcc)).mono_set inter_subset_left).const_mul _
  have hmono := setIntegral_mono_on hi1 hi2 hUm fun z _ => sq_norm_fderiv_evenPart_le_m7d hgd z
  rw [integral_const_mul, ← hU] at hmono
  unfold dirichletEnergyOn
  have : ∫ z in B ∩ H, ‖fderiv ℝ (evenPart g) z‖ ^ 2 ≤ (1 / 2 : ℝ) * ∫ z in B, ‖fderiv ℝ g z‖ ^ 2 := by
    rw [hwhole] at h2; linarith
  have hpi : 0 ≤ (2 * π)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hpi]

/-- **D4 (reflection identity).** The dual norm of the half-disc mixed space is half the
zero-boundary dual norm of the disc, evaluated at the symmetrized measure. -/
theorem dualNormSq_halfDisc_eq_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (hμH : ∀ᵐ z ∂μ, z ∈ Hbar)
    (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0) :
    dualNormSq (ball (t : ℂ) r ∩ H)
        (mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r)))) μ =
      dualNormSq (ball (t : ℂ) r) (zeroSpace (ball (t : ℂ) r)) (μ + μ.map conj) / 2 := by
  have hr : 0 < r := hr'.trans hr'r
  set U := ball (t : ℂ) r ∩ H with hUdef
  set V₀ := mixedSpace U (realSet (Icc (t - r) (t + r))) with hV₀
  set B := ball (t : ℂ) r with hBdef
  set μt := μ + μ.map conj with hμt
  have hconjm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  apply le_antisymm
  · by_cases htop : dualNormSq B (zeroSpace B) μt = ⊤
    · rw [htop, ENNReal.top_div_of_ne_top (by norm_num)]; exact le_top
    have hfin : dualNormSq B (zeroSpace B) μt < ⊤ := lt_top_iff_ne_top.2 htop
    refine iSup₂_le fun f hf => ?_
    have h := sq_integral_le_halfDisc_m7d hr' hr'r hμH hμK hfin hf.1
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ hf.2]; exact h
  · refine ENNReal.div_le_of_le_mul ?_
    refine iSup₂_le fun g hg => ?_
    set X := (∫ x, g x ∂μt) ^ 2 with hX
    have hgs := evenPart_mem_m7d (t := t) (r := r) hg.1
    have hE := energy_evenPart_le_m7d hg.1
    have hgc : Continuous g := hg.1.1.continuous
    have hgi : ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], Integrable g ν := fun ν _ =>
      hgc.integrable_of_hasCompactSupport hg.1.2.1
    have hgci : Integrable (fun z => g (conj z)) μ :=
      (integrable_map_measure hgc.aestronglyMeasurable hconjm.aemeasurable).1 (hgi _)
    have hpair : ∫ x, evenPart g x ∂μ = (1 / 2 : ℝ) * ∫ x, g x ∂μt := by
      simp only [evenPart]
      rw [integral_const_mul, integral_add (hgi μ) hgci, hμt,
        integral_add_measure (hgi μ) (hgi _), integral_map hconjm.aemeasurable
          hgc.aestronglyMeasurable]
    have hX0 : 0 ≤ X := sq_nonneg _
    rcases (energy_nonneg U (evenPart g)).lt_or_eq with hpos | hzero
    · have h1 := le_dualNormSq (μ := μ) hgs hpos
      have hle : X / dirichletEnergyOn B g ≤
          (∫ x, evenPart g x ∂μ) ^ 2 / dirichletEnergyOn U (evenPart g) * 2 := by
        rw [hpair, mul_pow, div_mul_eq_mul_div, ← hX]
        rw [show (1 / 2 : ℝ) ^ 2 * X * 2 = X / 2 by ring, div_div]
        exact div_le_div_of_nonneg_left hX0 (by positivity) (by linarith)
      calc ENNReal.ofReal (X / dirichletEnergyOn B g)
          ≤ ENNReal.ofReal ((∫ x, evenPart g x ∂μ) ^ 2 / dirichletEnergyOn U (evenPart g) * 2) :=
            ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal ((∫ x, evenPart g x ∂μ) ^ 2 / dirichletEnergyOn U (evenPart g)) * 2 := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
        _ ≤ dualNormSq U V₀ μ * 2 := by gcongr
    · by_cases hDU : dualNormSq U V₀ μ = ⊤
      · rw [hDU, ENNReal.top_mul (by norm_num)]; exact le_top
      have hDN := isDNSpace_mixedSpace U (realSet (Icc (t - r) (t + r)))
      have hpt : ((t : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I) ∈ U := by
        refine ⟨?_, ?_⟩
        · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I,
            mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          linarith
        · show (0 : ℝ) < ((t : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I).im
          simp; linarith
      have hpos' := exists_pos_energy_mixedSpace (S := realSet (Icc (t - r) (t + r)))
        (isOpen_ball.inter isOpen_H) ⟨_, hpt⟩
      have h := sq_integral_le hDN ⟨closedBall (t : ℂ) r', isCompact_closedBall _ _, hμK⟩
        (lt_top_iff_ne_top.2 hDU) hpos' hgs
      rw [norm_gradFeat_sq (hDN.smooth _ hgs) (hDN.energy _ hgs), ← hzero, mul_zero] at h
      have h0 : (∫ x, evenPart g x ∂μ) ^ 2 = 0 := le_antisymm h (sq_nonneg _)
      rw [hpair, mul_pow] at h0
      have hX' : X = 0 := by nlinarith
      rw [hX', zero_div, ENNReal.ofReal_zero]; exact zero_le

end QuantumZipper.K3
