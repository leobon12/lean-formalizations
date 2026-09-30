import QuantumZipper.Proofs.GFF.K3.MixedM6ContBasic

/-!
# Norm continuity of `z ↦ v_{fold_{z,s}}` on `K` (GFF-K3 node M6, analytic input)

With `v_ρ = rieszVec D (mixedSpace D S) ρ`, `0 < s < R` and `a := (s + R)/2`:

* for `t ∈ (a, R)`, `v_{z,s} − v_{z',s} = (A_{z,s,t} − A_{z',s,t}) + (v_{z,t} − v_{z',t})`
  (`rieszVec_annulus'`); averaging over `t` with a smooth radial weight `φ` on `(a, R)` turns the
  last pairing with `∇f` into `∫ f (ψ(· − z) − ψ(· − z'))`, which is `O(|z − z'| ‖∇f‖)` (Lipschitz
  bound and Poincaré inequality, exactly as in M5(c), `exists_abs_inner_remVec_sub_le`);
* hence `‖v_{z,s} − v_{z',s}‖ ≤ sup_{t ∈ [a,R]} ‖A_{z,s,t} − A_{z',s,t}‖ + K₂ |z − z'|`
  (`exists_norm_rieszVec_foldedCircle_sub_le`), and the supremum tends to `0` as `z' → z` by the
  joint continuity of the annulus features (`MixedM6ContBasic`);
* `continuousOn_rieszVec_foldedCircle`: `z ↦ v_{fold_{z,s}}` is norm continuous on `K`.

Own argument (the blueprint route of M6 needs this continuity; no published source uses this
exact Hilbert-space setting; it combines dominated convergence with the M5(c) estimate).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

variable {D S K : Set ℂ} {R : ℝ}

theorem exists_norm_rieszVec_foldedCircle_sub_le (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {s : ℝ} (hs : 0 < s)
    (hsR : s < R) :
    ∃ K2 : ℝ, 0 ≤ K2 ∧ ∀ z ∈ K, ∀ z' ∈ K, ∀ η : ℝ,
      (∀ t ∈ Icc ((s + R) / 2) R, ‖annulusFeat D z s t - annulusFeat D z' s t‖ ≤ η) →
      ‖rieszVec D (mixedSpace D S) (foldedCircle z s) -
        rieszVec D (mixedSpace D S) (foldedCircle z' s)‖ ≤ η + K2 * ‖z - z'‖ := by
  have hR := h.pos
  have hV := isDNSpace_mixedSpace D S
  set a : ℝ := (s + R) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hsa : s < a := by rw [ha_def]; linarith
  have hab : a < R := by rw [ha_def]; linarith
  obtain ⟨φ, hφ, hφ0, hφa, hφb, hφ1⟩ := exists_radial_weight ha hab
  obtain ⟨L, hL⟩ := exists_lipschitz_radial hφ ha hφa hφb
  have hψb : ∀ y : ℂ, R ≤ ‖y‖ → φ ‖y‖ / ‖y‖ = 0 := fun y hy => by rw [hφb _ hy, zero_div]
  have hφcs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := a) (b := R)) (fun t ht => ?_)
    rw [mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · exact hφa t ht.le
    · exact hφb t ht.le
  have hφint : IntegrableOn φ (Ioi 0) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφcs).integrableOn
  obtain ⟨CP, hCP⟩ := mixed_poincare h.isOpen h.subset_H h.bounded h.free_real
  set vd : ℝ := (volume D ^ (1 / 2 : ℝ)).toReal with hvd
  set cp : ℝ := (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)).toReal with hcp
  set K2 : ℝ := (2 * π)⁻¹ * (4 * (vd * cp)) * L * Real.sqrt (2 * π) with hK2
  have hK20 : 0 ≤ K2 := by
    rw [hK2]
    have : 0 ≤ vd := ENNReal.toReal_nonneg
    have : 0 ≤ cp := ENNReal.toReal_nonneg
    positivity
  refine ⟨K2, hK20, fun z hz z' hz' η hη => ?_⟩
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη a ⟨le_rfl, hab.le⟩)
  have hzH := (h.local_ z hz).1
  have hz'H := (h.local_ z' hz').1
  have hsub : ∀ w ∈ K, ∀ y ∈ H, ‖y - w‖ < R → y ∈ D := fun w hw y hy hyw =>
    (h.local_ w hw).mem_of_mem_H h.isOpen h.free_real hy (by linarith)
  set x := rieszVec D (mixedSpace D S) (foldedCircle z s) -
    rieszVec D (mixedSpace D S) (foldedCircle z' s) with hx
  have hxG : x ∈ gradClosure D (mixedSpace D S) := sub_mem rieszVec_mem rieszVec_mem
  have hkey : ∀ f ∈ mixedSpace D S,
      |⟪x, gradFeat D f⟫| ≤ (η + K2 * ‖z - z'‖) * ‖gradFeat D f‖ := by
    intro f hfn
    have hfc : Continuous f := hfn.1.continuous
    have hf1 : ContDiff ℝ 1 f := hfn.1.of_le one_le_smooth
    obtain ⟨hIz, hAz⟩ := integral_radial_foldedCircle_eq hφ.continuous ha hφa hφb hfc z
    obtain ⟨hIz', hAz'⟩ := integral_radial_foldedCircle_eq hφ.continuous ha hφa hφb hfc z'
    set Az := ∫ t in Ioi 0, φ t * ∫ x, f x ∂(foldedCircle z t) with hAz_def
    set Az' := ∫ t in Ioi 0, φ t * ∫ x, f x ∂(foldedCircle z' t) with hAz'_def
    set G : ℝ := ∫ w in D, ‖fderiv ℝ f w‖ ^ 2 with hG
    have hG0 : 0 ≤ G := setIntegral_nonneg h.isOpen.measurableSet fun _ _ => sq_nonneg _
    have hgn : ‖gradFeat D f‖ ^ 2 = (2 * π)⁻¹ * G := by
      rw [norm_gradFeat_sq hf1 hfn.2.1]; rfl
    have hsqrtG : Real.sqrt G = Real.sqrt (2 * π) * ‖gradFeat D f‖ := by
      rw [← Real.sqrt_sq (norm_nonneg (gradFeat D f)), ← Real.sqrt_mul (by positivity), hgn,
        ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    have hE := ofReal_abs_integral_foldH_sub_le hfc hL hψb h.isOpen.measurableSet hzH hz'H
      (hsub z hz) (hsub z' hz')
    have hP := lintegral_enorm_le_of_poincare h.isOpen h.bounded hCP hfn
    rw [← hG] at hP
    have hVD : volume D ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) h.bounded.measure_lt_top.ne
    have hCPt : ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have hYt : ENNReal.ofReal G ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have hY : (ENNReal.ofReal G ^ (1 / 2 : ℝ)).toReal = Real.sqrt G := by
      rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hG0, Real.sqrt_eq_rpow]
    have hX := ENNReal.toReal_mono (by finiteness)
      (hE.trans (mul_le_mul_right (mul_le_mul_right hP 4) _))
    rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hX
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg L.coe_nonneg (norm_nonneg _))]
      at hX
    rw [hY] at hX
    rw [← hvd, ← hcp] at hX
    have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
    rw [h4] at hX
    have hdiff : |Az - Az'| ≤ K2 * ‖z - z'‖ * ‖gradFeat D f‖ := by
      rw [hAz, hAz', ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
      calc (2 * π)⁻¹ * |(∫ y, f (foldH y) * (φ ‖y - z‖ / ‖y - z‖)) -
              ∫ y, f (foldH y) * (φ ‖y - z'‖ / ‖y - z'‖)|
          ≤ (2 * π)⁻¹ * (L * ‖z - z'‖ * (4 * (vd * (cp * Real.sqrt G)))) :=
            mul_le_mul_of_nonneg_left hX (by positivity)
        _ = K2 * ‖z - z'‖ * ‖gradFeat D f‖ := by rw [hsqrtG, hK2]; ring
    have hDn : ∀ t ∈ Ioi (0 : ℝ), ‖φ t * (∫ x, f x ∂(foldedCircle z t) -
        ∫ x, f x ∂(foldedCircle z' t)) - φ t * ⟪x, gradFeat D f⟫‖ ≤
          φ t * (η * ‖gradFeat D f‖) := by
      intro t ht
      by_cases hta : t ≤ a
      · rw [hφa t hta]; simp
      by_cases htR : R ≤ t
      · rw [hφb t htR]; simp
      push Not at hta htR
      have ht2 : t < 2 * R := by linarith
      have e1 := pair_rieszVec hV (isAdmissibleDual_foldedCircle_of_local h.isOpen h.subset_H
        h.bounded h.free_real (h.local_ z hz) (ha.trans hta) ht2) hpos f hfn
      have e2 := pair_rieszVec hV (isAdmissibleDual_foldedCircle_of_local h.isOpen h.subset_H
        h.bounded h.free_real (h.local_ z' hz') (ha.trans hta) ht2) hpos f hfn
      have hA : x - (rieszVec D (mixedSpace D S) (foldedCircle z t) -
          rieszVec D (mixedSpace D S) (foldedCircle z' t)) =
          annulusFeat D z s t - annulusFeat D z' s t := by
        rw [hx, ← rieszVec_annulus' h.isOpen h.subset_H h.bounded h.free_real (h.local_ z hz) hs
          (hsa.trans hta) ht2, ← rieszVec_annulus' h.isOpen h.subset_H h.bounded h.free_real
          (h.local_ z' hz') hs (hsa.trans hta) ht2]
        abel
      rw [← e1, ← e2, ← inner_sub_left, ← mul_sub, ← inner_sub_left, norm_mul,
        Real.norm_of_nonneg (hφ0 t)]
      refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (hφ0 t)
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_sub_rev, hA]
      exact hη t ⟨hta.le, htR.le⟩
    have hrel : |(Az - Az') - ⟪x, gradFeat D f⟫| ≤ η * ‖gradFeat D f‖ := by
      have hI3 : IntegrableOn (fun t => φ t * (∫ x, f x ∂(foldedCircle z t) -
          ∫ x, f x ∂(foldedCircle z' t))) (Ioi 0) :=
        (hIz.sub hIz').congr_fun (fun t _ => by simp only [Pi.sub_apply, mul_sub])
          measurableSet_Ioi
      have e1 : Az - Az' = ∫ t in Ioi 0, φ t * (∫ x, f x ∂(foldedCircle z t) -
          ∫ x, f x ∂(foldedCircle z' t)) := by
        rw [hAz_def, hAz'_def, ← integral_sub hIz hIz']
        congr 1; funext t; ring
      have e2 : ∫ t in Ioi 0, φ t * ⟪x, gradFeat D f⟫ = ⟪x, gradFeat D f⟫ := by
        rw [integral_mul_const, hφ1, one_mul]
      have e : (Az - Az') - ⟪x, gradFeat D f⟫ = ∫ t in Ioi 0, (φ t * (∫ x, f x ∂(foldedCircle z t) -
          ∫ x, f x ∂(foldedCircle z' t)) - φ t * ⟪x, gradFeat D f⟫) := by
        rw [e1, integral_sub hI3 (hφint.mul_const _), e2]
      rw [e, ← Real.norm_eq_abs]
      calc ‖∫ t in Ioi 0, (φ t * (∫ x, f x ∂(foldedCircle z t) -
            ∫ x, f x ∂(foldedCircle z' t)) - φ t * ⟪x, gradFeat D f⟫)‖
          ≤ ∫ t in Ioi 0, φ t * (η * ‖gradFeat D f‖) :=
            norm_integral_le_of_norm_le (hφint.mul_const _)
              (ae_restrict_of_forall_mem measurableSet_Ioi hDn)
        _ = η * ‖gradFeat D f‖ := by rw [integral_mul_const, hφ1, one_mul]
    calc |⟪x, gradFeat D f⟫| = |(Az - Az') - ((Az - Az') - ⟪x, gradFeat D f⟫)| := by ring_nf
      _ ≤ |Az - Az'| + |(Az - Az') - ⟪x, gradFeat D f⟫| := abs_sub _ _
      _ ≤ K2 * ‖z - z'‖ * ‖gradFeat D f‖ + η * ‖gradFeat D f‖ := add_le_add hdiff hrel
      _ = (η + K2 * ‖z - z'‖) * ‖gradFeat D f‖ := by ring
  have hu2 : x ∈ closure (Submodule.span ℝ (gradFeat D '' mixedSpace D S) : Set (GradSpace D)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hxG
  obtain ⟨g, hg, hlim⟩ := mem_closure_iff_seq_limit.mp hu2
  choose f hf hfg using fun n => mem_image_of_mem_span hV (hg n)
  have hn : ∀ n, |⟪x, g n⟫| ≤ (η + K2 * ‖z - z'‖) * ‖g n‖ := fun n => by
    rw [← hfg n]; exact hkey _ (hf n)
  have hT1 : Tendsto (fun n => |⟪x, g n⟫|) atTop (𝓝 |⟪x, x⟫|) :=
    (tendsto_const_nhds.inner hlim).abs
  have hT2 : Tendsto (fun n => (η + K2 * ‖z - z'‖) * ‖g n‖) atTop
      (𝓝 ((η + K2 * ‖z - z'‖) * ‖x‖)) := hlim.norm.const_mul _
  have hle := le_of_tendsto_of_tendsto' hT1 hT2 hn
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hle
  have hC0 : 0 ≤ η + K2 * ‖z - z'‖ := by positivity
  by_cases hx0 : ‖x‖ = 0
  · rw [hx0]; exact hC0
  have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
  nlinarith

/-- **Norm continuity of the folded-circle Riesz vectors on `K`.** -/
theorem continuousOn_rieszVec_foldedCircle (h : MixedLocalHyp D S K R) {s : ℝ} (hs : 0 < s)
    (hsR : s < R) :
    ContinuousOn (fun z => rieszVec D (mixedSpace D S) (foldedCircle z s)) K := by
  have hV := isDNSpace_mixedSpace D S
  by_cases hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g
  swap
  · have h0 : ∀ ρ, rieszVec D (mixedSpace D S) ρ = 0 := fun ρ =>
      eq_zero_of_mem_gradClosure_of_nopos hV hpos rieszVec_mem
    simp_rw [h0]; exact continuousOn_const
  obtain ⟨K2, hK20, hK2⟩ := exists_norm_rieszVec_foldedCircle_sub_le h hpos hs hsR
  intro z0 hz0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδA⟩ := exists_norm_annulusFeat_sub_lt h.bounded (a := (s + R) / 2) (b := R)
    (D := D) hs z0 (half_pos hε)
  refine ⟨min δ (ε / 2 / (K2 + 1)), lt_min hδ (by positivity), fun z' hz' hd => ?_⟩
  rw [dist_eq_norm] at hd ⊢
  have hd1 : ‖z' - z0‖ < δ := hd.trans_le (min_le_left _ _)
  have hd2 : ‖z' - z0‖ < ε / 2 / (K2 + 1) := hd.trans_le (min_le_right _ _)
  have hb := hK2 z0 hz0 z' hz' (ε / 2) (fun t ht => (hδA z' hd1 t ht).le)
  have h3 : ‖z' - z0‖ * (K2 + 1) < ε / 2 := (lt_div_iff₀ (by positivity)).mp hd2
  have h4 : K2 * ‖z0 - z'‖ < ε / 2 := by
    rw [norm_sub_rev z0 z']; nlinarith [norm_nonneg (z' - z0)]
  calc ‖rieszVec D (mixedSpace D S) (foldedCircle z' s) -
        rieszVec D (mixedSpace D S) (foldedCircle z0 s)‖
      = ‖rieszVec D (mixedSpace D S) (foldedCircle z0 s) -
        rieszVec D (mixedSpace D S) (foldedCircle z' s)‖ := norm_sub_rev _ _
    _ ≤ ε / 2 + K2 * ‖z0 - z'‖ := hb
    _ < ε := by linarith

end QuantumZipper.K3
