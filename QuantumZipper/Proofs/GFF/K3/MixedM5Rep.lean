import QuantumZipper.Proofs.GFF.K3.MixedM5Pot
import QuantumZipper.Proofs.GFF.K3.MixedM5Stmt

/-!
# The remainder representation and the kernel form of the mixed covariance (GFF-K3 node M5(d))

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M5). With `μ_t := μ.bind (foldedCircle · t)`:

* `tendsto_integral_bind_foldedCircle`: `∫ f dμ_t → ∫ f dμ` (`t → 0⁺`, `f` continuous).
* `inner_rieszVec_bind_eq_integral`: `⟪v_{μ_t}, u⟫ = ∫ ⟪v_{fold_{z,t}}, u⟫ dμ(z)` on the gradient
  closure (the weak form of the Bochner identity `v_{μ_t} = ∫ v_{fold_{z,t}} dμ`).
* `exists_norm_rieszVec_bind_le`: `sup_{0<t≤R} ‖v_{μ_t}‖ < ∞` (M4 with explicit constants).
* `tendsto_inner_rieszVec_bind`: `v_{μ_t} → v_μ` weakly on the gradient closure (M4(ii)).
* `inner_rieszVec_eq_integral_of_mem_orthogonal`: for `u ⊥ M` in the gradient closure,
  `⟪v_μ, u⟫ = ∫ ⟪v_{fold_{z,s}}, u⟫ dμ(z)` (mean value property of M2 plus the limit).
* **M5(d)** `dualCovMixedKernel`: `dualCov D (mixedSpace D S) μ ν = Qann μ ν + kernelCov r_D μ ν`.

The blueprint's route (Bochner integrals of Riesz vectors) is replaced by the equivalent weak
formulation (scalar integrals only); the argument is the blueprint's (M4(ii), M5).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

variable {D S K : Set ℂ} {R : ℝ}

theorem MixedLocalHyp.subset_Hbar (h : MixedLocalHyp D S K R) : K ⊆ Hbar :=
  fun z hz => (h.local_ z hz).1

/-- `∫ f dμ_t → ∫ f dμ` as `t → 0⁺`. -/
theorem tendsto_integral_bind_foldedCircle {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (hμK : μ Kᶜ = 0) {f : ℂ → ℝ} (hf : Continuous f) :
    Tendsto (fun t => ∫ x, f x ∂(μ.bind fun w => foldedCircle w t)) (𝓝[>] 0)
      (𝓝 (∫ x, f x ∂μ)) := by
  set K1 := cthickening 1 K ∩ Hbar with hK1def
  have hK1 : IsCompact K1 := hK.cthickening.inter_right isClosed_Hbar
  obtain ⟨Mf, hMf⟩ := hK1.exists_bound_of_continuousOn hf.continuousOn
  have hae : ∀ᵐ z ∂μ, z ∈ K := mem_ae_iff.mpr hμK
  have hint : ∀ t ∈ Ioc (0 : ℝ) 1, Integrable f (μ.bind fun w => foldedCircle w t) := by
    intro t ht
    have := CircleFubini.isFiniteMeasure_bind_circle (r := t) μ
    refine Integrable.of_bound hf.aestronglyMeasurable Mf ?_
    have h0 := bind_cthickening_compl hK hKH hμK ht.1.le ht.2
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with x hx
    exact hMf x (not_not.mp hx)
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∫ z, (∫ x, f x ∂foldedCircle z t) ∂μ =
      ∫ x, f x ∂(μ.bind fun w => foldedCircle w t) := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    exact (CircleFubini.integral_bind_circle μ (hint t ht)).2.symm
  refine Tendsto.congr' hev ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => Mf) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    exact (CircleFubini.integral_bind_circle μ (hint t ht)).1.aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    filter_upwards [hae] with z hz
    have hc := foldedCircle_compl_eq_zero (hKH hz) ht.1.le
    refine (norm_integral_le_of_norm_le_const (C := Mf) ?_).trans (by simp)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hc] with x hx
    have hx' : x ∈ closedBall z t ∩ Hbar := not_not.mp hx
    exact hMf x ⟨closedBall_subset_cthickening hz 1 (closedBall_subset_closedBall ht.2 hx'.1),
      hx'.2⟩
  · filter_upwards [hae] with z hz
    have h := tendsto_integral_circleUnif_zero (hf.comp CircleFubini.continuous_foldH') z
    simp_rw [integral_foldedCircle_eq hf]
    rwa [Function.comp_apply, CircleFubini.foldH_of_mem' (hKH hz)] at h

/-- Mixed admissibility of `μ_t`. -/
theorem isAdmissibleDual_bind (h : MixedLocalHyp D S K R) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hμK : μ Kᶜ = 0) {t : ℝ} (ht : 0 < t) (htR : t < 2 * R) :
    IsAdmissibleDual D (mixedSpace D S) (μ.bind fun w => foldedCircle w t) := by
  have := hμ.1
  exact isAdmissibleDual_mixed_of_local h.isOpen h.subset_H h.bounded h.free_real
    (h.compact.cthickening.inter_right isClosed_Hbar) (R := (2 * R - t) / 2) (by linarith)
    (localBall_cthickening h.compact h.local_ ht.le htR) (isAdmissibleH_bind hμ ht)
    (bind_cthickening_compl h.compact h.subset_Hbar hμK ht.le le_rfl)

/-- The weak Bochner identity `v_{μ_t} = ∫ v_{fold_{z,t}} dμ(z)` on the gradient closure. -/
theorem inner_rieszVec_bind_eq_integral (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) {t : ℝ} (ht : 0 < t) (htR : t < R) {u : GradSpace D}
    (hu : u ∈ gradClosure D (mixedSpace D S)) :
    AEStronglyMeasurable (fun z => ⟪rieszVec D (mixedSpace D S) (foldedCircle z t), u⟫) μ ∧
      ⟪rieszVec D (mixedSpace D S) (μ.bind fun w => foldedCircle w t), u⟫ =
        ∫ z, ⟪rieszVec D (mixedSpace D S) (foldedCircle z t), u⟫ ∂μ := by
  have hμf := hμ.1
  have hV := isDNSpace_mixedSpace D S
  obtain ⟨B, hB⟩ := exists_norm_rieszVec_foldedCircle_le h.isOpen h.subset_H h.bounded
    h.free_real h.pos h.local_ ht htR
  have hae : ∀ᵐ z ∂μ, z ∈ K := mem_ae_iff.mpr hμK
  have hμt := isAdmissibleDual_bind h hμ hμK ht (by linarith [h.pos])
  have hfold : ∀ z ∈ K, IsAdmissibleDual D (mixedSpace D S) (foldedCircle z t) := fun z hz =>
    isAdmissibleDual_foldedCircle_of_local h.isOpen h.subset_H h.bounded h.free_real
      (h.local_ z hz) ht (by linarith [h.pos])
  refine inner_eq_integral_of_mem_closure_span (G := gradFeat D '' mixedSpace D S) (B := B)
    (by filter_upwards [hae] with z hz; exact hB z hz) ?_ ?_ hu
  · rintro _ ⟨f, hf, rfl⟩
    have hint : Integrable f (μ.bind fun w => foldedCircle w t) :=
      integrable_of_admissible hV hμt hf
    refine (CircleFubini.integral_bind_circle μ hint).1.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with z hz
    exact (pair_rieszVec hV (hfold z hz) hpos f hf).symm
  · rintro _ ⟨f, hf, rfl⟩
    have hint : Integrable f (μ.bind fun w => foldedCircle w t) :=
      integrable_of_admissible hV hμt hf
    rw [pair_rieszVec hV hμt hpos f hf, (CircleFubini.integral_bind_circle μ hint).2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    exact (pair_rieszVec hV (hfold z hz) hpos f hf).symm

/-- Uniform bound on `‖v_{μ_t}‖` for `0 < t ≤ R`. -/
theorem exists_norm_rieszVec_bind_le (h : MixedLocalHyp D S K R) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) :
    ∃ B : ℝ, ∀ t, 0 < t → t ≤ R →
      ‖rieszVec D (mixedSpace D S) (μ.bind fun w => foldedCircle w t)‖ ≤ B := by
  obtain ⟨hμf, -, C, hC, hbd⟩ := id hμ
  have hR := h.pos
  set R' : ℝ := (2 * R - R) / 2 with hR'
  have hR'0 : 0 < R' := by rw [hR']; linarith
  have hloc := localBall_cthickening h.compact h.local_ hR.le (by linarith)
  obtain ⟨CP, hCP⟩ := mixed_local_pairing_bound h.isOpen h.subset_H h.bounded h.free_real hR'0
    hloc
  set m : ℝ≥0∞ := μ univ with hm
  set Ct : ℝ≥0∞ := 2 * C + 2 * ENNReal.ofReal R * m with hCt
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * π)⁻¹ with hc
  set a : ℝ≥0∞ := ENNReal.ofReal (3 * R' ^ 2 / 2) with ha
  set Q : ℝ≥0∞ := (2 * ENNReal.ofReal (2 * π) *
      (1 + ENNReal.ofReal (max (Real.log (2 * (2 * R'))) 0)) * m +
      2 * ENNReal.ofReal (2 * π) * Ct) * m with hQ
  set B0 : ℝ≥0∞ := c * 2 * m * (volume D ^ (1 / 2 : ℝ) * ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)) +
    a * (c * 2 * Q ^ (1 / 2 : ℝ)) with hB0
  have hmt : m ≠ ⊤ := measure_ne_top _ _
  have hCt' : C ≠ ⊤ := hC.ne
  have hVD : volume D ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) h.bounded.measure_lt_top.ne
  have hQt : Q ≠ ⊤ := by rw [hQ, hCt]; finiteness
  have hB0t : B0 ≠ ⊤ := by
    have h1 : Q ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hQt
    have h2 : ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    rw [hB0]; finiteness
  have ha0 : 0 < 3 * R' ^ 2 / 2 := by positivity
  set M : ℝ := (B0.toReal / (3 * R' ^ 2 / 2)) ^ 2 with hM
  refine ⟨Real.sqrt (M * (2 * π)), fun t ht htR => ?_⟩
  have hμt := isAdmissibleH_bind hμ ht
  have hsupp := bind_cthickening_compl h.compact h.subset_Hbar hμK ht.le htR
  have huniv : (μ.bind fun w => foldedCircle w t) univ = m := CircleFubini.bind_circle_univ μ
  have hPP : ∫⁻ y, (∫⁻ w, kInv (2 * R') (y - w) ∂(μ.bind fun w => foldedCircle w t)) ^ (2 : ℝ)
      ≤ Q := by
    have hpot : ∀ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖)
        ∂(μ.bind fun w => foldedCircle w t) ≤ Ct := fun y => by
      refine (lintegral_negLog_bind_le hμ hbd ht y).trans ?_
      rw [hCt]
      gcongr
    have h1 := lintegral_kInvPot_sq_le hμt (ρ := 2 * R') (by positivity) hpot
    rwa [huniv] at h1
  have hpair : ∀ f ∈ mixedSpace D S, (∫ x, f x ∂(μ.bind fun w => foldedCircle w t)) ^ 2 ≤
      M * ∫ w in D, ‖fderiv ℝ f w‖ ^ 2 := by
    intro f hf
    have h0 := hCP _ hμt hsupp f hf
    rw [huniv] at h0
    have h' : a * ENNReal.ofReal |∫ x, f x ∂(μ.bind fun w => foldedCircle w t)| ≤
        ENNReal.ofReal (∫ w in D, ‖fderiv ℝ f w‖ ^ 2) ^ (1 / 2 : ℝ) * B0 := by
      refine h0.trans ?_
      rw [hB0]
      gcongr
    exact sq_le_of_ennreal_bound ha0 (setIntegral_nonneg h.isOpen.measurableSet
      fun _ _ => sq_nonneg _) hB0t h'
  have hadm : IsAdmissibleDual D (mixedSpace D S) (μ.bind fun w => foldedCircle w t) :=
    isAdmissibleDual_mixed_of_local h.isOpen h.subset_H h.bounded h.free_real
      (h.compact.cthickening.inter_right isClosed_Hbar) hR'0 hloc hμt hsupp
  exact norm_rieszVec_le_of_sq_le hadm (by positivity) hpair

/-- **M4(ii), weak form.** `v_{μ_t} → v_μ` weakly on the gradient closure. -/
theorem tendsto_inner_rieszVec_bind (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) {u : GradSpace D}
    (hu : u ∈ gradClosure D (mixedSpace D S)) :
    Tendsto (fun t => ⟪rieszVec D (mixedSpace D S) (μ.bind fun w => foldedCircle w t), u⟫)
      (𝓝[>] 0) (𝓝 ⟪rieszVec D (mixedSpace D S) μ, u⟫) := by
  have hμf := hμ.1
  have hV := isDNSpace_mixedSpace D S
  obtain ⟨B, hB⟩ := exists_norm_rieszVec_bind_le h hμ hμK
  have hμa := isAdmissibleDual_mixed_of_local h.isOpen h.subset_H h.bounded h.free_real
    h.compact h.pos h.local_ hμ hμK
  refine tendsto_inner_of_mem_closure_span (B := B) ?_ ?_ hu
  · filter_upwards [Ioc_mem_nhdsGT h.pos] with t ht
    exact hB t ht.1 ht.2
  · rintro _ ⟨f, hf, rfl⟩
    rw [pair_rieszVec hV hμa hpos f hf]
    refine Tendsto.congr' ?_ (tendsto_integral_bind_foldedCircle h.compact h.subset_Hbar hμK
      hf.1.continuous)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * R by linarith [h.pos])] with t ht
    exact (pair_rieszVec hV (isAdmissibleDual_bind h hμ hμK ht.1 ht.2) hpos f hf).symm

/-- **M5, representation of the remainder.** For `u ⊥ M` in the gradient closure,
`⟪v_μ, u⟫ = ∫ ⟪v_{fold_{z,s}}, u⟫ dμ(z)`. -/
theorem inner_rieszVec_eq_integral_of_mem_orthogonal (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) {s : ℝ} (hs : 0 < s) (hsR : s < 2 * R)
    {u : GradSpace D} (hu : u ∈ gradClosure D (mixedSpace D S)) (hu' : u ∈ (annulusSpan D S)ᗮ) :
    ⟪rieszVec D (mixedSpace D S) μ, u⟫ =
      ∫ z, ⟪rieszVec D (mixedSpace D S) (foldedCircle z s), u⟫ ∂μ := by
  have hμf := hμ.1
  have hae : ∀ᵐ z ∂μ, z ∈ K := mem_ae_iff.mpr hμK
  have hT := tendsto_inner_rieszVec_bind h hpos hμ hμK hu
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∫ z, ⟪rieszVec D (mixedSpace D S) (foldedCircle z s), u⟫ ∂μ =
        ⟪rieszVec D (mixedSpace D S) (μ.bind fun w => foldedCircle w t), u⟫ := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hs h.pos)] with t ht
    have ht1 : t < s := ht.2.trans_le (min_le_left _ _)
    have ht2 : t < R := ht.2.trans_le (min_le_right _ _)
    rw [(inner_rieszVec_bind_eq_integral h hpos hμ hμK ht.1 ht2 hu).2]
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    have hA := rieszVec_annulus' h.isOpen h.subset_H h.bounded h.free_real (h.local_ z hz) ht.1
      ht1 hsR
    have hmem := annulusFeat_mem_annulusSpan (h.local_ z hz) ht.1 ht1 hsR
    have h0 : ⟪annulusFeat D z t s, u⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hmem hu'
    rw [← hA, inner_sub_left, sub_eq_zero] at h0
    exact h0.symm
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' hev)

end QuantumZipper.K3
