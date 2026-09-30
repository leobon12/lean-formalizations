import QuantumZipper.Proofs.GFF.K3.MixedM7A3

/-!
# K3-mixed M7-a2′, part 3: the trace bound uniformly in the radius

`poissonBound_uniform_m7b`: there is `C` with `(∫ f dP^ρ_z)² ≤ C (f,f)_∇` for all
`f ∈ mixedSpace D (realSet (Icc c d))`, all `ρ ∈ [ρ₀, r]` and all `‖z − t‖ ≤ r''` (`r'' < ρ₀`),
where `P^ρ_z = halfDiscPoisson t ρ z`. This is M7-a1 (`mixedPoissonBound_holds`) with the
constant made uniform in the radius: the ray from the fixed inner radius `a = ρ₀/2` replaces
the ray from `ρ/2`. Own elementary argument (cost rule), the radial device of Gilbarg–Trudinger,
*Elliptic PDE of Second Order*, Lemma 7.16, p. 162; the proofs are copies of those of
`MixedM7A2`/`MixedM7A3` with the inner radius generalized.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- Ray bound from a general inner radius `a ≤ r` (copy of `ofReal_abs_le_ray_m7a`). -/
theorem ofReal_abs_le_ray_gen_m7b {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (t : ℂ) {a r : ℝ}
    (ha : 0 < a) (har : a ≤ r) {x : ℂ} (hx : ‖x - t‖ ≤ r) :
    ENNReal.ofReal |f x| ≤ ENNReal.ofReal |f (t + ((a / r : ℝ) : ℂ) * (x - t))| +
      ∫⁻ ρ in Ioc a r, ‖fderiv ℝ f (t + ((ρ / r : ℝ) : ℂ) * (x - t))‖ₑ := by
  have hr : 0 < r := ha.trans_le har
  set γ : ℝ → ℂ := fun ρ => t + ((ρ / r : ℝ) : ℂ) * (x - t) with hγdef
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hγc : Continuous γ := by rw [hγdef]; fun_prop
  have hγ : ∀ ρ, HasDerivAt γ (((1 / r : ℝ) : ℂ) * (x - t)) ρ := by
    intro ρ
    have h1 : HasDerivAt (fun ρ : ℝ => ((ρ / r : ℝ) : ℂ)) ((1 / r : ℝ) : ℂ) ρ :=
      ((hasDerivAt_id ρ).div_const r).ofReal_comp
    exact (h1.mul_const (x - t)).const_add t
  have hd : ∀ ρ, HasDerivAt (fun ρ => f (γ ρ))
      (fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t))) ρ :=
    fun ρ => ((hf.differentiable one_ne_zero (γ ρ)).hasFDerivAt).comp_hasDerivAt ρ (hγ ρ)
  have hdcont : Continuous fun ρ => fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t)) :=
    (hdc.comp hγc).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ => hd ρ)
    (hdcont.intervalIntegrable a r)
  have hγr : γ r = x := by
    show t + ((r / r : ℝ) : ℂ) * (x - t) = x
    rw [div_self hr.ne', Complex.ofReal_one, one_mul, add_sub_cancel]
  have hnorm : ∀ ρ, ‖fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t))‖ ≤ ‖fderiv ℝ f (γ ρ)‖ := by
    intro ρ
    have h1 : ‖((1 / r : ℝ) : ℂ) * (x - t)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), one_div,
        inv_mul_le_iff₀ hr]
      linarith
    calc _ ≤ ‖fderiv ℝ f (γ ρ)‖ * ‖((1 / r : ℝ) : ℂ) * (x - t)‖ := (fderiv ℝ f (γ ρ)).le_opNorm _
      _ ≤ ‖fderiv ℝ f (γ ρ)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := mul_one _
  have hgi : IntegrableOn (fun ρ => ‖fderiv ℝ f (γ ρ)‖) (Ioc a r) :=
    ((hdc.comp hγc).norm.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hreal : |f x| ≤ |f (γ a)| + ∫ ρ in Ioc a r, ‖fderiv ℝ f (γ ρ)‖ := by
    have e : f x = f (γ a) +
        ∫ ρ in a..r, fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t)) := by
      rw [hFTC, hγr]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    gcongr
    rw [intervalIntegral.integral_of_le har, ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hgi (Eventually.of_forall hnorm)
  calc ENNReal.ofReal |f x|
      ≤ ENNReal.ofReal (|f (γ a)| + ∫ ρ in Ioc a r, ‖fderiv ℝ f (γ ρ)‖) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal |f (γ a)| + ∫⁻ ρ in Ioc a r, ‖fderiv ℝ f (γ ρ)‖ₑ := by
        rw [ENNReal.ofReal_add (abs_nonneg _)
            (setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _),
          ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun _ => norm_nonneg _)]
        simp only [ofReal_norm]

/-- Radial scaling about a real centre maps `fold_{t,r}` to `fold_{t,a}`. -/
theorem lintegral_foldedCircle_scale_m7b {F : ℂ → ℝ≥0∞} (hF : Measurable F) (t : ℝ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ x, F ((t : ℂ) + ((a / r : ℝ) : ℂ) * (x - t)) ∂(foldedCircle (t : ℂ) r) =
      ∫⁻ x, F x ∂(foldedCircle (t : ℂ) a) := by
  have hm1 : Measurable fun x : ℂ => F ((t : ℂ) + ((a / r : ℝ) : ℂ) * (x - t)) :=
    hF.comp (by fun_prop)
  have hm2 : Measurable fun w : ℂ => F ((t : ℂ) + ((a / r : ℝ) : ℂ) * (foldH w - t)) :=
    hm1.comp measurable_foldH
  have hm3 : Measurable fun w : ℂ => F (foldH w) := hF.comp measurable_foldH
  rw [foldedCircle, foldedCircle, lintegral_map hm1 measurable_foldH,
    lintegral_map hF measurable_foldH, lintegral_circleUnif_eq' hm2, lintegral_circleUnif_eq' hm3]
  congr 1
  refine lintegral_congr fun θ => ?_
  rw [foldH_circleMap_scale_m7a t hr ha θ]

/-- The ray term from the inner radius `a`, averaged over `fold_{t,r}` (copy of
`lintegral_ray_foldedCircle_le_m7a`). -/
theorem lintegral_ray_foldedCircle_gen_m7b {D : Set ℂ} (hDm : MeasurableSet D) {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (t : ℝ) {a r : ℝ} (ha : 0 < a) (har : a ≤ r)
    (hsub : ∀ y ∈ H, ‖y - t‖ < r → y ∈ D) :
    ∫⁻ x, (∫⁻ ρ in Ioc a r, ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (x - t))‖ₑ)
        ∂(foldedCircle (t : ℂ) r) ≤
      (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (1 / a) *
        (2 * ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ) := by
  have hr : 0 < r := ha.trans_le har
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set g : ℂ → ℝ≥0∞ := fun y => ‖fderiv ℝ f (foldH y)‖ₑ with hg
  have hgm : Measurable g := (hdc.comp continuous_foldH_K3).enorm.measurable
  have hFm : Measurable fun x : ℂ => ∫⁻ ρ in Ioc a r,
      ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (x - t))‖ₑ :=
    Measurable.lintegral_prod_right'
      (f := fun p : ℂ × ℝ => ‖fderiv ℝ f ((t : ℂ) + ((p.2 / r : ℝ) : ℂ) * (p.1 - t))‖ₑ)
      (hdc.comp (by fun_prop)).enorm.measurable
  have hFm' : Measurable fun x : ℂ => ∫⁻ ρ in Ioc a r,
      ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (foldH x - t))‖ₑ :=
    hFm.comp measurable_foldH
  rw [foldedCircle, lintegral_map hFm measurable_foldH, lintegral_circleUnif_eq' hFm', mul_assoc]
  refine mul_le_mul_right ?_ _
  have hinner : ∀ θ, ∫⁻ ρ in Ioc a r,
      ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (foldH (circleMap (t : ℂ) r θ) - t))‖ₑ =
      ∫⁻ ρ in Ioc a r, g (circleMap (t : ℂ) ρ θ) := by
    intro θ
    refine setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => ?_)
    rw [foldH_circleMap_scale_m7a t hr (by linarith [hρ.1]) θ]
  have hsw : Measurable (Function.uncurry fun θ ρ => g (circleMap (t : ℂ) ρ θ)) :=
    hgm.comp ((continuous_circleMap_uncurry (t : ℂ)).comp continuous_swap).measurable
  rw [lintegral_congr (fun θ => hinner θ), lintegral_lintegral_swap hsw.aemeasurable]
  calc ∫⁻ ρ in Ioc a r, ∫⁻ θ in Ioo (-π) π, g (circleMap (t : ℂ) ρ θ)
      ≤ ∫⁻ ρ in Ioc a r, ENNReal.ofReal (1 / a) *
          ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap (t : ℂ) ρ θ) := by
        refine setLIntegral_mono' measurableSet_Ioc (fun ρ hρ => ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun θ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        have h1 : 1 ≤ 1 / a * ρ := by
          rw [one_div, inv_mul_eq_div, le_div_iff₀ ha]; linarith [hρ.1]
        calc g (circleMap (t : ℂ) ρ θ) = 1 * g (circleMap (t : ℂ) ρ θ) := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.one_le_ofReal.2 h1) zero_le
    _ = ENNReal.ofReal (1 / a) * ∫⁻ ρ in Ioc a r,
          ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap (t : ℂ) ρ θ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 / a) * (2 * ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ) := by
        refine mul_le_mul_right ?_ _
        rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm]
        exact (lintegral_radius_circle_le hgm (t : ℂ) ha.le).trans
          (lintegral_ball_foldH_le hDm (show (t : ℂ) ∈ Hbar by simp [Hbar]) hsub
            hdc.enorm.measurable)

/-- **Uniform trace bound** for the half-disc Poisson measures of radii `ρ ∈ [ρ₀, r]`. -/
theorem poissonBound_uniform_m7b {D : Set ℂ} {c d t r r'' ρ₀ : ℝ}
    (hgeom : Prop16Geometry D c d) (hsub : ball (t : ℂ) r ∩ H ⊆ D) (hr'' : 0 ≤ r'')
    (hr''ρ₀ : r'' < ρ₀) (hρ₀r : ρ₀ ≤ r) :
    ∃ C : ℝ, ∀ ρ ∈ Icc ρ₀ r, ∀ z : ℂ, ‖z - t‖ ≤ r'' →
      ∀ f ∈ mixedSpace D (realSet (Icc c d)),
        (∫ x, f x ∂halfDiscPoisson t ρ z) ^ 2 ≤ C * dirichletEnergyOn D f := by
  have hρ₀ : 0 < ρ₀ := lt_of_le_of_lt hr'' hr''ρ₀
  set a : ℝ := ρ₀ / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have har : a < r := by rw [ha_def]; linarith
  have ht0 : (t : ℂ) ∈ Hbar := by simp [Hbar]
  have hS : realSet (Icc c d) ⊆ {z : ℂ | z.im = 0} := by
    rintro _ ⟨s, -, rfl⟩
    simp
  have hDm : MeasurableSet D := hgeom.1.measurableSet
  obtain ⟨M1, hM1top, hM1⟩ := mixed_local_L1_bound_m7a hgeom.1 hgeom.2.2.2.1 hgeom.2.2.1 hS
    (K := closedBall (t : ℂ) a ∩ Hbar) (R := (r - a) / 4) (by linarith)
    (fun z hz => localBall_of_halfDisc_m7a hgeom har hsub hz)
    (isAdmissibleH_foldedCircle ht0 ha) (foldedCircle_compl_eq_zero ht0 ha.le)
  set VD : ℝ≥0∞ := volume D with hVD
  have hVD_lt : VD < ⊤ := hgeom.2.2.1.measure_lt_top
  set Pm : ℝ≥0∞ := ENNReal.ofReal (r ^ 2 / (ρ₀ - r'') ^ 2) with hPm
  set K : ℝ≥0∞ := Pm *
    (M1 + (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (1 / a) * (2 * VD ^ (1 / 2 : ℝ))) with hK
  have hKtop : K ≠ ⊤ := by
    have h1 : VD ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVD_lt.ne
    have h2 : (ENNReal.ofReal (2 * π))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
    rw [hK]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hM1top,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top h2 ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num) h1)⟩)
  refine ⟨K.toReal ^ 2 * (2 * π), fun ρ hρ z hz f hf => ?_⟩
  have hρ0 : 0 < ρ := hρ₀.trans_le hρ.1
  have haρ : a ≤ ρ := by rw [ha_def]; linarith [hρ.1]
  have hsubH : ∀ y ∈ H, ‖y - t‖ < ρ → y ∈ D := fun y hy hyr =>
    hsub ⟨mem_ball_iff_norm.2 (lt_of_lt_of_le hyr hρ.2), hy⟩
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le one_le_smooth
  have hfc : Continuous f := hf1.continuous
  set G : ℝ := ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hDm fun _ _ => sq_nonneg _
  set Y : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt G) with hY
  have hFm : Measurable fun x => ENNReal.ofReal |f x| :=
    (continuous_abs.comp hfc).measurable.ennreal_ofReal
  have hPle : pBound ρ r'' ≤ Pm := by
    unfold pBound
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 0 < ρ₀ - r'' := by linarith
    have h2 : ρ₀ - r'' ≤ ρ - r'' := by linarith [hρ.1]
    have h3 : ρ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hρ0.le hρ.2 2
    have h4 : (ρ₀ - r'') ^ 2 ≤ (ρ - r'') ^ 2 := pow_le_pow_left₀ h1.le h2 2
    exact div_le_div₀ (sq_nonneg _) h3 (by positivity) h4
  have hae : ∀ᵐ x : ℂ ∂(foldedCircle (t : ℂ) ρ), ‖x - (t : ℂ)‖ ≤ ρ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (foldedCircle_compl_eq_zero ht0 hρ0.le)]
      with x hx
    exact mem_closedBall_iff_norm.1 (notMem_compl_iff.1 hx).1
  have hmain : ENNReal.ofReal |∫ x, f x ∂halfDiscPoisson t ρ z| ≤ K * Y := by
    calc ENNReal.ofReal |∫ x, f x ∂halfDiscPoisson t ρ z|
        ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂halfDiscPoisson t ρ z := by
          rw [← Real.enorm_eq_ofReal_abs]
          refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
          simp only [Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂(pBound ρ r'' • foldedCircle (t : ℂ) ρ) :=
          lintegral_mono' (halfDiscPoisson_le hρ0 (hr''ρ₀.trans_le hρ.1) hz) le_rfl
      _ = pBound ρ r'' * ∫⁻ x, ENNReal.ofReal |f x| ∂(foldedCircle (t : ℂ) ρ) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ Pm * ∫⁻ x, ENNReal.ofReal |f x| ∂(foldedCircle (t : ℂ) ρ) := by gcongr
      _ ≤ Pm * ((∫⁻ x, ENNReal.ofReal |f x| ∂(foldedCircle (t : ℂ) a)) +
          ∫⁻ x, (∫⁻ u in Ioc a ρ,
            ‖fderiv ℝ f ((t : ℂ) + ((u / ρ : ℝ) : ℂ) * (x - t))‖ₑ) ∂(foldedCircle (t : ℂ) ρ)) := by
          refine mul_le_mul_right ?_ _
          have hA : Measurable fun x : ℂ =>
              ENNReal.ofReal |f ((t : ℂ) + ((a / ρ : ℝ) : ℂ) * (x - t))| :=
            (continuous_abs.comp (hfc.comp (by fun_prop))).measurable.ennreal_ofReal
          rw [← lintegral_foldedCircle_scale_m7b hFm t ha hρ0, ← lintegral_add_left hA]
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with x hx
          exact ofReal_abs_le_ray_gen_m7b hf1 (t : ℂ) ha haρ hx
      _ ≤ Pm * (M1 * Y + (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (1 / a) *
            (2 * (VD ^ (1 / 2 : ℝ) * Y))) := by
          refine mul_le_mul_right (add_le_add (hM1 f hf) ?_) _
          refine (lintegral_ray_foldedCircle_gen_m7b hDm hf1 t ha haρ hsubH).trans ?_
          exact mul_le_mul_right (mul_le_mul_right
            (lintegral_enorm_fderiv_le_m7a hDm hf1 hf.2.1) 2) _
      _ = K * Y := by rw [hK]; ring
  rw [hY, ← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hmain
  have hI := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _))).1 hmain
  have hE : dirichletEnergyOn D f = (2 * π)⁻¹ * G := rfl
  have hπ : (2 * π) ≠ 0 := by positivity
  calc (∫ x, f x ∂halfDiscPoisson t ρ z) ^ 2 = |∫ x, f x ∂halfDiscPoisson t ρ z| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (K.toReal * Real.sqrt G) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hI 2
    _ = K.toReal ^ 2 * (2 * π) * dirichletEnergyOn D f := by
        rw [hE, mul_pow, Real.sq_sqrt hG0]
        field_simp

end QuantumZipper.K3
