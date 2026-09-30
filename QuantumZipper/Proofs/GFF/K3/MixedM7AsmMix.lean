import QuantumZipper.Proofs.GFF.K3.MixedM7AsmVer3
import QuantumZipper.Proofs.GFF.K3.MixedM5Weak

/-!
# K3-mixed M7, assembly part 1: the mixed Poisson curve is weakly harmonic

For `V = mixedSpace D (realSet (Icc c d))`, a half-disc `ball t r ∩ H ⊆ D` on the free arc and
`0 < ρ < r`, the curve `mixCurve z = v_{P_{retr z}} = rieszVec D V (halfDiscPoisson t r (retr t ρ z))`
satisfies, for every `e ∈ GradSpace D`,

* the weak mean-value property over folded circles inside `ball t ρ`
  (`inner_mixCurve_meanValue`): `⟪v_{P_z}, e⟫ = ∫ ⟪v_{P_x}, e⟫ d fold_{z,σ}(x)`; on the gradients
  `∇f`, `f ∈ V`, this is `∫ f dP_z = ∫∫ f dP_x d fold_{z,σ}(x)` (`bind_foldedCircle_halfDiscPoisson`),
  and it extends to the gradient closure by boundedness (`inner_eq_integral_of_mem_closure_span`)
  and to all `e` by orthogonal projection;
* weak harmonicity (`harmonicOnNhd_inner_mixCurve`): `z ↦ ⟪mixCurve (foldH z), e⟫` is harmonic on
  `ball t ρ` (Weyl's lemma, `harmonicOnNhd_of_meanValue`, using the Lipschitz bound
  `exists_lip_rieszVec_halfDiscPoisson` for continuity).

This is the hypothesis of M7-b (`PoissonHarmonicVersionStmt`, proved) for the harmonic part
`Ξ(v_{P_z})` of the mixed field. Source: Sheffield, *Gaussian free fields for mathematicians*,
PTRF 139 (2007), Thm 2.17 (the harmonic part of the Markov decomposition is harmonic); the proof
here is an own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- The mixed Poisson curve, retracted onto `closedBall t ρ ∩ Hbar`. -/
def mixCurve (D : Set ℂ) (c d t r ρ : ℝ) (z : ℂ) : GradSpace D :=
  rieszVec D (mixedSpace D (realSet (Icc c d))) (halfDiscPoisson t r (retr t ρ z))

section

variable {D : Set ℂ} {c d t r ρ : ℝ}

theorem mixCurve_foldH (z : ℂ) : mixCurve D c d t r ρ (foldH z) = mixCurve D c d t r ρ z := by
  simp only [mixCurve, retr_foldH_m7b]

theorem mixCurve_conj (z : ℂ) : mixCurve D c d t r ρ (conj z) = mixCurve D c d t r ρ z := by
  simp only [mixCurve, retr_conj_m7b]

theorem mixCurve_eq {z : ℂ} (hz : z ∈ Hbar) (hzt : ‖z - t‖ ≤ ρ) :
    mixCurve D c d t r ρ z = rieszVec D (mixedSpace D (realSet (Icc c d)))
      (halfDiscPoisson t r z) := by
  simp only [mixCurve, retr_eq_self hz hzt]

/-- `mixCurve` is Lipschitz and bounded. -/
theorem exists_lip_mixCurve (hgeom : Prop16Geometry D c d) (ht : t ∈ Set.Ioo c d)
    (hρ : 0 < ρ) (hρr : ρ < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ (∀ z w, ‖mixCurve D c d t r ρ z - mixCurve D c d t r ρ w‖ ≤
      L * (2 * ‖z - w‖)) ∧ ∀ z, ‖mixCurve D c d t r ρ z‖ ≤ B := by
  obtain ⟨L, hL0, hL⟩ := exists_lip_rieszVec_halfDiscPoisson hgeom ht hρ hρr hsub
  have hK : ∀ z, retr t ρ z ∈ closedBall (t : ℂ) ρ ∩ Hbar := fun z =>
    ⟨mem_closedBall_iff_norm.2 (norm_retr_sub_le hρ z), retr_mem_Hbar hρ z⟩
  have hlip : ∀ z w, ‖mixCurve D c d t r ρ z - mixCurve D c d t r ρ w‖ ≤ L * (2 * ‖z - w‖) :=
    fun z w => (hL _ (hK z) _ (hK w)).trans
      (mul_le_mul_of_nonneg_left (norm_retr_sub_retr_le hρ z w) hL0)
  refine ⟨L, ‖mixCurve D c d t r ρ (t : ℂ)‖ + L * (2 * ρ), hL0, by positivity, hlip, fun z => ?_⟩
  have h1 := hlip z (retr t ρ z)
  have h2 : mixCurve D c d t r ρ (retr t ρ z) = mixCurve D c d t r ρ z := by
    simp only [mixCurve, retr_eq_self (hK z).2 (mem_closedBall_iff_norm.1 (hK z).1)]
  have h3 := hlip (retr t ρ z) (t : ℂ)
  have h4 : ‖retr t ρ z - (t : ℂ)‖ ≤ ρ := norm_retr_sub_le hρ z
  rw [h2] at h3
  calc ‖mixCurve D c d t r ρ z‖ = ‖(mixCurve D c d t r ρ z - mixCurve D c d t r ρ (t : ℂ)) +
        mixCurve D c d t r ρ (t : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖mixCurve D c d t r ρ z - mixCurve D c d t r ρ (t : ℂ)‖ +
        ‖mixCurve D c d t r ρ (t : ℂ)‖ := norm_add_le _ _
    _ ≤ L * (2 * ρ) + ‖mixCurve D c d t r ρ (t : ℂ)‖ := by
        gcongr
        exact h3.trans (mul_le_mul_of_nonneg_left (by linarith) hL0)
    _ = _ := by ring

theorem continuous_mixCurve (hgeom : Prop16Geometry D c d) (ht : t ∈ Set.Ioo c d)
    (hρ : 0 < ρ) (hρr : ρ < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) :
    Continuous (mixCurve D c d t r ρ) := by
  obtain ⟨L, B, hL0, -, hlip, -⟩ := exists_lip_mixCurve hgeom ht hρ hρr hsub
  refine (LipschitzWith.of_dist_le_mul (K := (2 * L).toNNReal) fun z w => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  linarith [hlip z w]

/-- **Weak mean-value property** of the mixed Poisson curve. -/
theorem inner_mixCurve_meanValue (hgeom : Prop16Geometry D c d) (ht : t ∈ Set.Ioo c d)
    (hρ : 0 < ρ) (hρr : ρ < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) {z : ℂ} (hz : z ∈ Hbar)
    {σ : ℝ} (hσ : 0 < σ) (hzσ : ‖z - t‖ + σ < ρ) (e : GradSpace D) :
    ∫ x, ⟪mixCurve D c d t r ρ x, e⟫ ∂foldedCircle z σ = ⟪mixCurve D c d t r ρ z, e⟫ := by
  set V := mixedSpace D (realSet (Icc c d)) with hVdef
  have hV : IsDNSpace D V := isDNSpace_mixedSpace D _
  have hr : 0 < r := hρ.trans hρr
  obtain ⟨L, B, -, -, -, hB⟩ := exists_lip_mixCurve hgeom ht hρ hρr hsub
  have hcont := continuous_mixCurve hgeom ht hρ hρr hsub
  have hadm := (mixedHalfDiscMarkovCov_holds D c d t r ρ hgeom ht hρ hρr hsub).1
  have hK : foldedCircle z σ (closedBall (t : ℂ) ρ ∩ Hbar)ᶜ = 0 := by
    refine measure_mono_null (compl_subset_compl.2 fun x hx => ⟨?_, hx.2⟩)
      (foldedCircle_compl_eq_zero hz hσ.le)
    have hx1 := mem_closedBall_iff_norm.1 hx.1
    rw [mem_closedBall_iff_norm]
    calc ‖x - t‖ = ‖(x - z) + (z - t)‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z - t‖ := norm_add_le _ _
      _ ≤ ρ := by linarith
  have hzK : z ∈ closedBall (t : ℂ) ρ ∩ Hbar := ⟨mem_closedBall_iff_norm.2 (by linarith), hz⟩
  -- reduce to the gradient closure
  set G := gradClosure D V with hG
  have hproj : ∀ w ∈ G, ⟪w, e⟫ = ⟪w, G.starProjection e⟫ := fun w hw => by
    rw [← G.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hw]
  have hPe : G.starProjection e ∈ (Submodule.span ℝ (gradFeat D '' V)).topologicalClosure := by
    rw [Submodule.starProjection_apply]; exact (G.orthogonalProjection e).2
  have hmem : ∀ x, mixCurve D c d t r ρ x ∈ G := fun x => rieszVec_mem
  by_cases hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g
  swap
  · have h0 : ∀ x, mixCurve D c d t r ρ x = 0 := fun x =>
      eq_zero_of_mem_gradClosure_of_nopos hV hpos (hmem x)
    simp [h0]
  have hmain := inner_eq_integral_of_mem_closure_span (μ := foldedCircle z σ)
    (G := gradFeat D '' V) (v := mixCurve D c d t r ρ) (B := B) (ae_of_all _ hB)
    (fun g _ => (hcont.inner continuous_const).aestronglyMeasurable)
    (y := mixCurve D c d t r ρ z) ?_ hPe
  · rw [hproj _ (hmem z), hmain.2]
    exact integral_congr_ae (ae_of_all _ fun x => hproj _ (hmem x))
  · rintro _ ⟨f, hf, rfl⟩
    have hfc : Continuous f := (hV.smooth f hf).continuous
    have hbind := bind_foldedCircle_halfDiscPoisson hr hσ (by linarith : ‖z - t‖ + σ < r)
    have hzb : z ∈ ball (t : ℂ) r := mem_ball_iff_norm.2 (by linarith)
    have := isProbabilityMeasure_halfDiscPoisson hr hzb
    have hint : Integrable f ((foldedCircle z σ).bind (halfDiscPoisson t r)) := by
      rw [hbind]
      have hKc : IsCompact (sphere (t : ℂ) r ∩ Hbar) := (isCompact_sphere _ _).inter_right
        isClosed_Hbar
      have hIK : IntegrableOn f (sphere (t : ℂ) r ∩ Hbar) (halfDiscPoisson t r z) :=
        hfc.continuousOn.integrableOn_compact hKc
      rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_halfDiscPoisson_mem hr z)] at hIK
    rw [mixCurve_eq hz (mem_closedBall_iff_norm.1 hzK.1), pair_rieszVec hV (hadm z hzK) hpos f hf,
      ← hbind, integral_bind_halfDiscPoisson_m7as _ hint]
    refine integral_congr_ae ?_
    filter_upwards [mem_ae_iff.2 hK] with x hx
    rw [mixCurve_eq hx.2 (mem_closedBall_iff_norm.1 hx.1), pair_rieszVec hV (hadm x hx) hpos f hf]

/-- **Weak harmonicity** of the mixed Poisson curve on `ball t ρ`. -/
theorem harmonicOnNhd_inner_mixCurve (hgeom : Prop16Geometry D c d) (ht : t ∈ Set.Ioo c d)
    (hρ : 0 < ρ) (hρr : ρ < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) (e : GradSpace D) :
    InnerProductSpace.HarmonicOnNhd (fun z => ⟪mixCurve D c d t r ρ (foldH z), e⟫)
      (ball (t : ℂ) ρ) := by
  simp only [mixCurve_foldH]
  have hcont : Continuous fun z => ⟪mixCurve D c d t r ρ z, e⟫ :=
    (continuous_mixCurve hgeom ht hρ hρr hsub).inner continuous_const
  refine harmonicOnNhd_of_meanValue hcont isOpen_ball fun z _ σ hσ hball => ?_
  have hzσ := add_lt_of_closedBall_subset_ball hσ hball
  have hfold : ∫ x, ⟪mixCurve D c d t r ρ x, e⟫ ∂circleUnif z σ =
      ∫ x, ⟪mixCurve D c d t r ρ x, e⟫ ∂foldedCircle z σ := by
    rw [foldedCircle, integral_map measurable_foldH.aemeasurable hcont.aestronglyMeasurable]
    simp only [mixCurve_foldH]
  rw [hfold]
  by_cases hz : z ∈ Hbar
  · exact inner_mixCurve_meanValue hgeom ht hρ hρr hsub hz hσ hzσ e
  · have hz' : conj z ∈ Hbar := by
      have : z.im < 0 := lt_of_not_ge hz
      show 0 ≤ (conj z).im
      simp only [Complex.conj_im]; linarith
    rw [← CoordReg.integral_foldedCircle_conj hcont.measurable,
      inner_mixCurve_meanValue hgeom ht hρ hρr hsub hz' hσ
        (by rw [norm_conj_sub_ofReal_k3]; exact hzσ) e, mixCurve_conj]

end

end QuantumZipper.K3
