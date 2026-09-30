import QuantumZipper.Proofs.GFF.K3.MixedM7B2
import QuantumZipper.Proofs.GFF.K3.MixedM7B3
import QuantumZipper.Proofs.GFF.K3.MixedM5Weak

/-!
# K3-mixed M7-a2′ (proved): Poisson reproduction for Neumann-harmonic elements

`mixedHarmonicPairing_holds : MixedHarmonicPairingStmt D c d t r r'`.

Proof. By `MixedM7B2`, `⟪v_μ, w⟫ = ⟪v_{bal t ρ μ}, w⟫` for all `ρ ∈ (r', r)`. As `ρ ↑ r`,
`v_{bal t ρ μ} → v_{bal t r μ}` weakly on the gradient closure
(`tendsto_inner_of_mem_closure_span`): the norms are bounded by the uniform trace bound
(`poissonBound_uniform_m7b`, `MixedM7B3`) and Jensen, and on test gradients
`∫ f d(bal t ρ μ) → ∫ f d(bal t r μ)` (`tendsto_integral_bal_m7b`: continuity of the Poisson
integral in the radius, then dominated convergence). This is the boundary step of Sheffield,
PTRF 139 (2007), Thm 2.17 (p. 14) in the weak formulation; own elementary argument for the
limit (cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- Jensen: `(∫ f d(bal t ρ μ))² ≤ μ(ℂ)² · max C 0 · (f,f)_∇` from the Poisson bound (copy of the
computation in `isAdmissibleDual_bal_of_bound_m7a`). -/
theorem sq_integral_bal_le_m7b {D : Set ℂ} {V : Set (ℂ → ℝ)} (hV : IsDNSpace D V)
    {t ρ r' : ℝ} (hρ : 0 < ρ) (hr'ρ : r' < ρ) {C : ℝ}
    (hC : ∀ z ∈ closedBall (t : ℂ) r' ∩ Hbar, ∀ f ∈ V,
      (∫ x, f x ∂halfDiscPoisson t ρ z) ^ 2 ≤ C * dirichletEnergyOn D f)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0)
    {f : ℂ → ℝ} (hf : f ∈ V) :
    (∫ x, f x ∂bal t ρ μ) ^ 2 ≤ μ.real univ ^ 2 * max C 0 * dirichletEnergyOn D f := by
  have := hμ.1
  have := isFiniteMeasure_bal hρ hr'ρ hμK
  have hKc : IsCompact (sphere (t : ℂ) ρ ∩ Hbar) :=
    (isCompact_sphere _ _).inter_right isClosed_Hbar
  have hbK : bal t ρ μ (sphere (t : ℂ) ρ ∩ Hbar)ᶜ = 0 :=
    bal_null_of_forall (isClosed_sphere.measurableSet.inter isClosed_Hbar.measurableSet).compl
      fun z => halfDiscPoisson_compl_eq_zero hρ z
  have hHbar : μ Hbarᶜ = 0 := by
    obtain ⟨-, ⟨K, -, hKH, hK⟩, -⟩ := hμ
    exact measure_mono_null (compl_subset_compl.2 hKH) hK
  have hae : ∀ᵐ z ∂μ, z ∈ closedBall (t : ℂ) r' ∩ Hbar := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hμK hHbar)
    by_contra h
    exact hz (by simpa [not_or] using h)
  have hE := energy_nonneg D f
  have hfi : Integrable f (bal t ρ μ) := integrable_of_mem hV ⟨_, hKc, hbK⟩ hf
  rw [(integral_bal hfi).2]
  have hs : 0 ≤ max C 0 * dirichletEnergyOn D f := mul_nonneg (le_max_right _ _) hE
  have hb : ∀ᵐ z ∂μ, ‖∫ x, f x ∂halfDiscPoisson t ρ z‖ ≤
      Real.sqrt (max C 0 * dirichletEnergyOn D f) := by
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ((hC z hz f hf).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hE
  have h1 := norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at h1
  calc (∫ z, ∫ x, f x ∂halfDiscPoisson t ρ z ∂μ) ^ 2
      = |∫ z, ∫ x, f x ∂halfDiscPoisson t ρ z ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (max C 0 * dirichletEnergyOn D f) * μ.real univ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = μ.real univ ^ 2 * max C 0 * dirichletEnergyOn D f := by
        rw [mul_pow, Real.sq_sqrt hs]; ring

/-- The Poisson integral in polar form, with the radius clamped below by `ρ₀` (a jointly
continuous integrand). -/
def poissonPolar (f : ℂ → ℝ) (t ρ₀ δ : ℝ) (z : ℂ) (ρ θ : ℝ) : ℝ :=
  ((max ρ ρ₀) ^ 2 - ‖z - t‖ ^ 2) /
    max (‖circleMap (t : ℂ) (max ρ ρ₀) θ - z‖ ^ 2) (δ ^ 2) *
      f (foldH (circleMap (t : ℂ) (max ρ ρ₀) θ))

theorem integral_halfDiscPoisson_eq_polar_m7b {f : ℂ → ℝ} (hf : Continuous f) {t ρ₀ ρ r' : ℝ}
    {z : ℂ} (hz : ‖z - t‖ ≤ r') (hr'ρ₀ : r' < ρ₀) (hρ : ρ₀ ≤ ρ) :
    ∫ x, f x ∂halfDiscPoisson t ρ z =
      (2 * π)⁻¹ * ∫ θ in Icc (-π) π, poissonPolar f t ρ₀ (ρ₀ - r') z ρ θ := by
  have hρ0 : 0 < ρ := lt_of_le_of_lt (le_trans (norm_nonneg _) hz) (hr'ρ₀.trans_le hρ)
  set δ : ℝ := ρ₀ - r' with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set g : ℂ → ℝ := fun w => (ρ ^ 2 - ‖z - t‖ ^ 2) / max (‖w - z‖ ^ 2) (δ ^ 2) * f (foldH w)
    with hg
  have hgc : Continuous g := by
    refine ((continuous_const.div ((continuous_id.sub continuous_const).norm.pow 2 |>.max
      continuous_const) fun w => ?_).mul (hf.comp continuous_foldH_K3))
    exact (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'
  rw [integral_halfDiscPoisson_eq_circle t ρ z hf.aestronglyMeasurable]
  have hcongr : (fun w => (ENNReal.ofReal ((ρ ^ 2 - ‖z - t‖ ^ 2) / ‖w - z‖ ^ 2)).toReal •
      f (foldH w)) =ᵐ[circleUnif (t : ℂ) ρ] g := by
    filter_upwards [ae_mem_sphere_circleUnif_k3 (t : ℂ) hρ0] with w hw
    have hwt : ‖w - t‖ = ρ := mem_sphere_iff_norm.1 hw
    have hwz : δ ≤ ‖w - z‖ := by
      have : ‖w - t‖ ≤ ‖w - z‖ + ‖z - t‖ := by
        calc ‖w - t‖ = ‖(w - z) + (z - t)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      rw [hδ]; linarith
    have hmax : max (‖w - z‖ ^ 2) (δ ^ 2) = ‖w - z‖ ^ 2 :=
      max_eq_left (pow_le_pow_left₀ hδ0.le hwz 2)
    have hnn : 0 ≤ (ρ ^ 2 - ‖z - t‖ ^ 2) / ‖w - z‖ ^ 2 := by
      refine div_nonneg ?_ (sq_nonneg _)
      have : ‖z - t‖ ≤ ρ := by linarith
      nlinarith [norm_nonneg (z - t)]
    rw [ENNReal.toReal_ofReal hnn, smul_eq_mul, hg]
    simp only [hmax]
  rw [integral_congr_ae hcongr, integral_circleUnif_eq hgc, integral_Icc_eq_integral_Ioo]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  simp only [hg, poissonPolar, max_eq_left hρ]

theorem continuous_poissonPolar_m7b {f : ℂ → ℝ} (hf : Continuous f) (t ρ₀ : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (z : ℂ) : Continuous (Function.uncurry (poissonPolar f t ρ₀ δ z)) := by
  have hcm : Continuous fun q : ℝ × ℝ => circleMap (t : ℂ) (max q.1 ρ₀) q.2 := by
    unfold circleMap; fun_prop
  unfold poissonPolar
  refine ((((continuous_fst.max continuous_const).pow 2).sub continuous_const).div
    (((hcm.sub continuous_const).norm.pow 2).max continuous_const) fun q => ?_).mul
      (hf.comp (continuous_foldH_K3.comp hcm))
  exact (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'

/-- **Continuity of the balayage in the radius** on continuous test functions. -/
theorem tendsto_integral_bal_m7b {f : ℂ → ℝ} (hf : Continuous f) {t r r' : ℝ} (hr' : 0 < r')
    (hr'r : r' < r) {μ : Measure ℂ} [IsFiniteMeasure μ] (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0) :
    Tendsto (fun ρ => ∫ x, f x ∂bal t ρ μ) (𝓝[<] r) (𝓝 (∫ x, f x ∂bal t r μ)) := by
  set ρ₀ : ℝ := (r' + r) / 2 with hρ₀
  have hr'ρ₀ : r' < ρ₀ := by rw [hρ₀]; linarith
  have hρ₀r : ρ₀ < r := by rw [hρ₀]; linarith
  have hr : 0 < r := hr'.trans hr'r
  obtain ⟨M, hM⟩ := (isCompact_closedBall (t : ℂ) r).exists_bound_of_continuousOn hf.continuousOn
  have hPb : ∀ ρ, 0 < ρ → ρ ≤ r → ∀ z, ∀ᵐ x ∂halfDiscPoisson t ρ z, ‖f x‖ ≤ M := by
    intro ρ hρ hρr z
    filter_upwards [ae_halfDiscPoisson_mem hρ z] with x hx
    exact hM x (closedBall_subset_closedBall hρr (sphere_subset_closedBall hx.1))
  have hint : ∀ ρ, r' < ρ → ρ ≤ r → Integrable f (bal t ρ μ) := by
    intro ρ hρ hρr
    have hρ0 : 0 < ρ := hr'.trans hρ
    have := isFiniteMeasure_bal hρ0 hρ hμK
    refine (integrable_const M).mono' hf.aestronglyMeasurable ?_
    have hbK : bal t ρ μ (closedBall (t : ℂ) r)ᶜ = 0 :=
      bal_null_of_forall isClosed_closedBall.measurableSet.compl fun z =>
        measure_mono_null (compl_subset_compl.2 fun x hx =>
          closedBall_subset_closedBall hρr (sphere_subset_closedBall hx.1))
          (halfDiscPoisson_compl_eq_zero hρ0 z)
    filter_upwards [mem_ae_iff.2 hbK] with x hx
    exact hM x hx
  set F : ℝ → ℂ → ℝ := fun ρ z => ∫ x, f x ∂halfDiscPoisson t ρ z with hF
  have hev : ∀ᶠ ρ in 𝓝[<] r, ∫ x, f x ∂bal t ρ μ = ∫ z, F ρ z ∂μ := by
    filter_upwards [Ioo_mem_nhdsLT hρ₀r] with ρ hρ
    exact (integral_bal (hint ρ (hr'ρ₀.trans hρ.1) hρ.2.le)).2
  rw [(integral_bal (hint r hr'r le_rfl)).2]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hae : ∀ᵐ z ∂μ, z ∈ closedBall (t : ℂ) r' := mem_ae_iff.2 hμK
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
    (integrable_const M) ?_
  · filter_upwards [Ioo_mem_nhdsLT hρ₀r] with ρ hρ
    exact (integral_bal (hint ρ (hr'ρ₀.trans hρ.1) hρ.2.le)).1.aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsLT hρ₀r] with ρ hρ
    filter_upwards [hae] with z hz
    have hρ0 : 0 < ρ := hr'.trans (hr'ρ₀.trans hρ.1)
    have hzt : ‖z - t‖ ≤ r' := mem_closedBall_iff_norm.1 hz
    have := isProbabilityMeasure_halfDiscPoisson hρ0
      (mem_ball_of_le_k3 (hr'ρ₀.trans hρ.1) hzt)
    have h1 := norm_integral_le_of_norm_le_const (hPb ρ hρ0 hρ.2.le z)
    simpa using h1
  · filter_upwards [hae] with z hz
    have hzt : ‖z - t‖ ≤ r' := mem_closedBall_iff_norm.1 hz
    have hc := (continuous_const.mul (continuous_parametric_integral_of_continuous
      (continuous_poissonPolar_m7b hf t ρ₀ (by linarith : (0 : ℝ) < ρ₀ - r') z)
      (isCompact_Icc (a := -π) (b := π)) (μ := volume))).tendsto r
      (f := fun ρ => (2 * π)⁻¹ * ∫ θ in Icc (-π) π, poissonPolar f t ρ₀ (ρ₀ - r') z ρ θ)
    rw [← integral_halfDiscPoisson_eq_polar_m7b hf hzt hr'ρ₀ hρ₀r.le] at hc
    refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hρ₀r] with ρ hρ
    exact (integral_halfDiscPoisson_eq_polar_m7b hf hzt hr'ρ₀ hρ.1.le).symm

/-- **M7-a2′ (proved): Poisson reproduction for Neumann-harmonic elements** (Sheffield,
PTRF 139 (2007), Thm 2.17, for the mixed half-disc). -/
theorem mixedHarmonicPairing_holds (D : Set ℂ) (c d t r r' : ℝ) :
    MixedHarmonicPairingStmt D c d t r r' := by
  intro hgeom _ht hr' hr'r hsub μ hμ hμK w hwG hw
  have hDN := isDNSpace_mixedSpace D (realSet (Icc c d))
  by_cases hpos : ∃ g ∈ mixedSpace D (realSet (Icc c d)), 0 < dirichletEnergyOn D g
  swap
  · have h0 : ∀ ρ, rieszVec D (mixedSpace D (realSet (Icc c d))) ρ = 0 := fun ρ =>
      eq_zero_of_mem_gradClosure_of_nopos hDN hpos rieszVec_mem
    simp [h0]
  have hμf := hμ.1
  have hr : 0 < r := hr'.trans hr'r
  set ρ₀ : ℝ := (r' + r) / 2 with hρ₀
  have hr'ρ₀ : r' < ρ₀ := by rw [hρ₀]; linarith
  have hρ₀r : ρ₀ < r := by rw [hρ₀]; linarith
  obtain ⟨C, hC⟩ := poissonBound_uniform_m7b hgeom hsub hr'.le hr'ρ₀ hρ₀r.le
  have hCρ : ∀ ρ ∈ Icc ρ₀ r, ∀ z ∈ closedBall (t : ℂ) r' ∩ Hbar,
      ∀ f ∈ mixedSpace D (realSet (Icc c d)),
        (∫ x, f x ∂halfDiscPoisson t ρ z) ^ 2 ≤ C * dirichletEnergyOn D f :=
    fun ρ hρ z hz => hC ρ hρ z (mem_closedBall_iff_norm.1 hz.1)
  have hsubρ : ∀ ρ, ρ ≤ r → ball (t : ℂ) ρ ∩ H ⊆ D := fun ρ hρ x hx =>
    hsub ⟨ball_subset_ball hρ hx.1, hx.2⟩
  have hadm : ∀ ρ ∈ Icc ρ₀ r,
      IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) (bal t ρ μ) := fun ρ hρ =>
    isAdmissibleDual_bal_of_bound_m7a hDN (hr'.trans (hr'ρ₀.trans_le hρ.1))
      (hr'ρ₀.trans_le hρ.1) (hsubρ ρ hρ.2) (hCρ ρ hρ) hμ hμK
  set M : ℝ := μ.real univ ^ 2 * max C 0 * (2 * π)⁻¹ with hM
  have hM0 : 0 ≤ M := by rw [hM]; have := le_max_right C 0; positivity
  have hnorm : ∀ ρ ∈ Icc ρ₀ r,
      ‖rieszVec D (mixedSpace D (realSet (Icc c d))) (bal t ρ μ)‖ ≤ Real.sqrt (M * (2 * π)) := by
    intro ρ hρ
    refine norm_rieszVec_le_of_sq_le (hadm ρ hρ) hM0 fun f hf => ?_
    have h := sq_integral_bal_le_m7b hDN (hr'.trans (hr'ρ₀.trans_le hρ.1))
      (hr'ρ₀.trans_le hρ.1) (hCρ ρ hρ) hμ hμK hf
    have hE : dirichletEnergyOn D f = (2 * π)⁻¹ * ∫ w in D, ‖fderiv ℝ f w‖ ^ 2 := rfl
    rw [hE] at h
    rw [hM]
    linarith
  have hT : Tendsto (fun ρ => ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (bal t ρ μ), w⟫)
      (𝓝[<] r) (𝓝 ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (bal t r μ), w⟫) := by
    refine tendsto_inner_of_mem_closure_span (B := Real.sqrt (M * (2 * π)))
      (G := gradFeat D '' mixedSpace D (realSet (Icc c d))) ?_ ?_ hwG
    · filter_upwards [Ioo_mem_nhdsLT hρ₀r] with ρ hρ
      exact hnorm ρ ⟨hρ.1.le, hρ.2.le⟩
    · rintro _ ⟨f, hf, rfl⟩
      rw [pair_rieszVec hDN (hadm r ⟨hρ₀r.le, le_rfl⟩) hpos f hf]
      refine (tendsto_integral_bal_m7b hf.1.continuous hr' hr'r hμK).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hρ₀r] with ρ hρ
      exact (pair_rieszVec hDN (hadm ρ ⟨hρ.1.le, hρ.2.le⟩) hpos f hf).symm
  have hconst : ∀ᶠ ρ in 𝓝[<] r,
      ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) μ, w⟫ =
        ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (bal t ρ μ), w⟫ := by
    filter_upwards [Ioo_mem_nhdsLT hρ₀r] with ρ hρ
    exact inner_rieszVec_bal_eq_m7b hgeom hsub hr' (hr'ρ₀.trans hρ.1) hρ.2 hμ hμK hwG hw
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' hconst) hT

end QuantumZipper.K3
