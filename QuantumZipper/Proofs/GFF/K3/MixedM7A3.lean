import QuantumZipper.Proofs.GFF.K3.MixedM7A1
import QuantumZipper.Proofs.GFF.K3.MixedM7A2

/-!
# K3-mixed M7-a1: the uniform trace bound for the folded Poisson measures (proved)

`mixedPoissonBound_holds : MixedPoissonBoundStmt D c d t r r'`: there is `C` with
`(∫ f dP_z)² ≤ C (f,f)_∇` for all `f ∈ mixedSpace D (realSet (Icc c d))` and all
`z ∈ closedBall t r' ∩ Hbar`.

Proof (own elementary argument, cost rule; the radial device of Gilbarg–Trudinger, Lemma 7.16):
`|∫ f dP_z| ≤ ∫ |f| dP_z ≤ pBound r r' · ∫ |f| d fold_{t,r}` (`halfDiscPoisson_le`); along the
rays from `t`, `|f x| ≤ |f(t + ½(x − t))| + ∫_{r/2}^r ‖∇f(t + (ρ/r)(x−t))‖ dρ`
(`ofReal_abs_le_ray_m7a`); the first term integrates to `∫ |f| d fold_{t,r/2}`, bounded by the
`L¹` form of M4 (`mixed_local_L1_bound_m7a`), and the second to `≲ ∫_D ‖∇f‖ ≤ |D|^{1/2} ‖∇f‖₂`
(`lintegral_ray_foldedCircle_le_m7a`, Cauchy–Schwarz).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- Radial halving about a real centre maps `fold_{t,r}` to `fold_{t,r/2}`. -/
theorem lintegral_foldedCircle_half_m7a {F : ℂ → ℝ≥0∞} (hF : Measurable F) (t : ℝ) {r : ℝ}
    (hr : 0 < r) :
    ∫⁻ x, F ((t : ℂ) + (((r / 2) / r : ℝ) : ℂ) * (x - t)) ∂(foldedCircle (t : ℂ) r) =
      ∫⁻ x, F x ∂(foldedCircle (t : ℂ) (r / 2)) := by
  have hm1 : Measurable fun x : ℂ => F ((t : ℂ) + (((r / 2) / r : ℝ) : ℂ) * (x - t)) :=
    hF.comp (by fun_prop)
  have hm2 : Measurable fun w : ℂ => F ((t : ℂ) + (((r / 2) / r : ℝ) : ℂ) * (foldH w - t)) :=
    hm1.comp measurable_foldH
  have hm3 : Measurable fun w : ℂ => F (foldH w) := hF.comp measurable_foldH
  rw [foldedCircle, foldedCircle, lintegral_map hm1 measurable_foldH, lintegral_map hF measurable_foldH,
    lintegral_circleUnif_eq' hm2, lintegral_circleUnif_eq' hm3]
  congr 1
  refine lintegral_congr fun θ => ?_
  rw [foldH_circleMap_scale_m7a t hr (by linarith) θ]

/-- Cauchy–Schwarz for the gradient on `D`. -/
theorem lintegral_enorm_fderiv_le_m7a {D : Set ℂ} (hDm : MeasurableSet D) {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (hint : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D) :
    ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ ≤
      volume D ^ (1 / 2 : ℝ) * ENNReal.ofReal (Real.sqrt (∫ z in D, ‖fderiv ℝ f z‖ ^ 2)) := by
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set G : ℝ := ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hDm fun _ _ => sq_nonneg _
  have hEn : ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal G := by
    rw [hG, ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict D) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := fun y => ‖fderiv ℝ f y‖ₑ) aemeasurable_const
    hdc.enorm.measurable.aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const,
    Measure.restrict_apply_univ] at h
  refine h.trans (le_of_eq ?_)
  rw [hEn, Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hG0 (by norm_num)]

/-- **M7-a1 (proved).** -/
theorem mixedPoissonBound_holds (D : Set ℂ) (c d t r r' : ℝ) :
    MixedPoissonBoundStmt D c d t r r' := by
  intro hgeom _ht hr' hr'r hsub
  have hr : 0 < r := hr'.trans hr'r
  have ht0 : (t : ℂ) ∈ Hbar := by simp [Hbar]
  have hS : realSet (Icc c d) ⊆ {z : ℂ | z.im = 0} := by
    rintro _ ⟨s, -, rfl⟩
    simp
  have hDm : MeasurableSet D := hgeom.1.measurableSet
  have hsubH : ∀ y ∈ H, ‖y - t‖ < r → y ∈ D := fun y hy hyr =>
    hsub ⟨mem_ball_iff_norm.2 hyr, hy⟩
  obtain ⟨M1, hM1top, hM1⟩ := mixed_local_L1_bound_m7a hgeom.1 hgeom.2.2.2.1 hgeom.2.2.1 hS
    (K := closedBall (t : ℂ) (r / 2) ∩ Hbar) (R := (r - r / 2) / 4) (by linarith)
    (fun z hz => localBall_of_halfDisc_m7a hgeom (by linarith : r / 2 < r) hsub hz)
    (isAdmissibleH_foldedCircle ht0 (by linarith)) (foldedCircle_compl_eq_zero ht0 (by linarith))
  set VD : ℝ≥0∞ := volume D with hVD
  have hVD_lt : VD < ⊤ := hgeom.2.2.1.measure_lt_top
  set K : ℝ≥0∞ := pBound r r' *
    (M1 + (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (2 / r) * (2 * VD ^ (1 / 2 : ℝ))) with hK
  have hKtop : K ≠ ⊤ := by
    have h1 : VD ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVD_lt.ne
    have h2 : (ENNReal.ofReal (2 * π))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 (by positivity)).ne'
    rw [hK]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hM1top,
      ENNReal.mul_ne_top (ENNReal.mul_ne_top h2 ENNReal.ofReal_ne_top)
        (ENNReal.mul_ne_top (by norm_num) h1)⟩)
  refine ⟨K.toReal ^ 2 * (2 * π), fun z hz f hf => ?_⟩
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le one_le_smooth
  have hfc : Continuous f := hf1.continuous
  set G : ℝ := ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hDm fun _ _ => sq_nonneg _
  set Y : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt G) with hY
  have hFm : Measurable fun x => ENNReal.ofReal |f x| :=
    (continuous_abs.comp hfc).measurable.ennreal_ofReal
  have hz' : ‖z - t‖ ≤ r' := mem_closedBall_iff_norm.1 hz.1
  -- the chain of bounds
  have hae : ∀ᵐ x : ℂ ∂(foldedCircle (t : ℂ) r), ‖x - (t : ℂ)‖ ≤ r := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (foldedCircle_compl_eq_zero ht0 hr.le)]
      with x hx
    exact mem_closedBall_iff_norm.1 (notMem_compl_iff.1 hx).1
  have hmain : ENNReal.ofReal |∫ x, f x ∂halfDiscPoisson t r z| ≤ K * Y := by
    calc ENNReal.ofReal |∫ x, f x ∂halfDiscPoisson t r z|
        ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂halfDiscPoisson t r z := by
          rw [← Real.enorm_eq_ofReal_abs]
          refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
          simp only [Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂(pBound r r' • foldedCircle (t : ℂ) r) :=
          lintegral_mono' (halfDiscPoisson_le hr hr'r hz') le_rfl
      _ = pBound r r' * ∫⁻ x, ENNReal.ofReal |f x| ∂(foldedCircle (t : ℂ) r) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ pBound r r' * ((∫⁻ x, ENNReal.ofReal |f x| ∂(foldedCircle (t : ℂ) (r / 2))) +
          ∫⁻ x, (∫⁻ ρ in Ioc (r / 2) r,
            ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (x - t))‖ₑ) ∂(foldedCircle (t : ℂ) r)) := by
          refine mul_le_mul_right ?_ _
          have hA : Measurable fun x : ℂ =>
              ENNReal.ofReal |f ((t : ℂ) + (((r / 2) / r : ℝ) : ℂ) * (x - t))| :=
            (continuous_abs.comp (hfc.comp (by fun_prop))).measurable.ennreal_ofReal
          rw [← lintegral_foldedCircle_half_m7a hFm t hr, ← lintegral_add_left hA]
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with x hx
          exact ofReal_abs_le_ray_m7a hf1 (t : ℂ) hr hx
      _ ≤ pBound r r' * (M1 * Y + (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (2 / r) *
            (2 * (VD ^ (1 / 2 : ℝ) * Y))) := by
          refine mul_le_mul_right (add_le_add (hM1 f hf) ?_) _
          refine (lintegral_ray_foldedCircle_le_m7a hDm hf1 t hr hsubH).trans ?_
          exact mul_le_mul_right (mul_le_mul_right
            (lintegral_enorm_fderiv_le_m7a hDm hf1 hf.2.1) 2) _
      _ = K * Y := by rw [hK]; ring
  rw [hY, ← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hmain
  have hI := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _))).1 hmain
  have hE : dirichletEnergyOn D f = (2 * π)⁻¹ * G := rfl
  have hπ : (2 * π) ≠ 0 := by positivity
  calc (∫ x, f x ∂halfDiscPoisson t r z) ^ 2 = |∫ x, f x ∂halfDiscPoisson t r z| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (K.toReal * Real.sqrt G) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hI 2
    _ = K.toReal ^ 2 * (2 * π) * dirichletEnergyOn D f := by
        rw [hE, mul_pow, Real.sq_sqrt hG0]
        field_simp

/-- **M7-a from the two remaining sub-nodes** (M7-a1 is proved). -/
theorem mixedHalfDiscMarkovCov_of_mem_gram {D : Set ℂ} {c d t r r' : ℝ}
    (h2 : MixedLocalMemStmt D c d t r r') (h3 : MixedLocalGramStmt D c d t r r') :
    MixedHalfDiscMarkovCovStmt D c d t r r' :=
  mixedHalfDiscMarkovCov_of_nodes (mixedPoissonBound_holds D c d t r r') h2 h3

/-! ## M7-a2 in harmonic-pairing form -/

instance (D : Set ℂ) (V : Set (ℂ → ℝ)) (t r : ℝ) : CompleteSpace (localClosure D V t r) := by
  unfold localClosure; infer_instance

theorem localClosure_le_gradClosure (D : Set ℂ) (V : Set (ℂ → ℝ)) (t r : ℝ) :
    localClosure D V t r ≤ gradClosure D V :=
  Submodule.topologicalClosure_mono (Submodule.span_mono (image_mono fun _ hf => hf.1))

/-- In a closed subspace `G ⊇ L`, an element orthogonal to `G ∩ Lᗮ` lies in `L`. -/
theorem mem_of_forall_orthogonal_m7a {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {L G : Submodule ℝ E} [L.HasOrthogonalProjection] (hLG : L ≤ G) {m : E} (hm : m ∈ G)
    (h : ∀ w ∈ G, w ∈ Lᗮ → ⟪m, w⟫ = 0) : m ∈ L := by
  have hp : L.starProjection m ∈ L := L.starProjection_apply_mem m
  have hw : m - L.starProjection m ∈ Lᗮ := L.sub_starProjection_mem_orthogonal m
  have h1 : ⟪m, m - L.starProjection m⟫ = 0 := h _ (G.sub_mem hm (hLG hp)) hw
  have h2 : ⟪L.starProjection m, m - L.starProjection m⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hp hw
  have h3 : ⟪m - L.starProjection m, m - L.starProjection m⟫ = 0 := by
    rw [inner_sub_left, h1, h2, sub_zero]
  rw [sub_eq_zero.1 (inner_self_eq_zero.1 h3)]
  exact hp

/-- **M7-a2′ (sub-node, not proved): Poisson reproduction for Neumann-harmonic elements.** Every
`w` of the gradient closure orthogonal to `H_supp(U)` (weakly harmonic in the half-disc, with
Neumann condition on the diameter) pairs equally with `v_μ` and with `v_{bal μ}`: the weak form
of `h(z) = ∫ h dP_z` for the harmonic function `h` represented by `w`. -/
def MixedHarmonicPairingStmt (D : Set ℂ) (c d t r r' : ℝ) : Prop :=
  Prop16Geometry D c d → t ∈ Set.Ioo c d → 0 < r' → r' < r → ball (t : ℂ) r ∩ H ⊆ D →
    ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      ∀ w ∈ gradClosure D (mixedSpace D (realSet (Icc c d))),
        w ∈ (localClosure D (mixedSpace D (realSet (Icc c d))) t r)ᗮ →
        ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) μ, w⟫ =
          ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (bal t r μ), w⟫

/-- M7-a2 follows from its harmonic-pairing form (Sheffield 2007, Thm 2.17: `H = H_supp ⊕ H_harm`). -/
theorem mixedLocalMem_of_harmonicPairing {D : Set ℂ} {c d t r r' : ℝ}
    (h : MixedHarmonicPairingStmt D c d t r r') : MixedLocalMemStmt D c d t r r' := by
  intro hgeom ht hr' hr'r hsub μ hμ hμK
  refine mem_of_forall_orthogonal_m7a (localClosure_le_gradClosure _ _ _ _)
    (sub_mem rieszVec_mem rieszVec_mem) fun w hwG hwL => ?_
  rw [mixedLocVec, inner_sub_left, h hgeom ht hr' hr'r hsub μ hμ hμK w hwG hwL, sub_self]

/-- **M7-a from M7-a2′ and M7-a3.** -/
theorem mixedHalfDiscMarkovCov_of_pairing_gram {D : Set ℂ} {c d t r r' : ℝ}
    (h2 : MixedHarmonicPairingStmt D c d t r r') (h3 : MixedLocalGramStmt D c d t r r') :
    MixedHalfDiscMarkovCovStmt D c d t r r' :=
  mixedHalfDiscMarkovCov_of_mem_gram (mixedLocalMem_of_harmonicPairing h2) h3

end QuantumZipper.K3
