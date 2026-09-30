import QuantumZipper.Proofs.GFF.K3.MixedM7A3
import QuantumZipper.Proofs.GFF.K3.MixedM5Rep

/-!
# K3-mixed M7-a2′, part 1: the local mean-value representation

Towards `MixedHarmonicPairingStmt` (Sheffield, *Gaussian free fields for mathematicians*,
PTRF 139 (2007), Thm 2.17, `literature/math_0312099.pdf` p. 14: an element of the Dirichlet
space orthogonal to the functions supported in `U` is harmonic in `U`). Fix `w` in the gradient
closure of the mixed space with `w ⊥ H_supp(U)`, `U = ball t r ∩ H`.

* `annulusFeat_mem_localClosure_m7b`: the annulus features of annuli inside `ball t r` lie in
  `H_supp(U)` (their smooth radial approximants are supported there);
* `inner_rieszVec_foldedCircle_eq_m7b`: `s ↦ ⟪v_{fold_{z,s}}, w⟫` is constant while
  `closedBall z s ⊆ ball t r` (M2: `v_{fold z s} − v_{fold z s'}` is the annulus feature);
* `inner_rieszVec_eq_integral_local_m7b`: a copy of M5 (`inner_rieszVec_eq_integral_of_mem_orthogonal`)
  using only the annuli about points of `K` (orthogonality hypothesis localized);
* `inner_rieszVec_eq_integral_halfDisc_m7b`: for admissible `μ` carried by
  `closedBall t r'' ∩ Hbar`, `r'' < r`, `⟪v_μ, w⟫ = ∫ ⟪v_{fold_{z,s}}, w⟫ dμ(z)`.

This is the mean-value (Weyl) route of Sheffield's proof in the weak formulation of M5.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-- Local balls inside the half-disc (as `localBall_of_halfDisc_m7a`, arbitrary centre). -/
theorem localBall_of_sub_m7b {D : Set ℂ} {c d t r : ℝ} (hgeom : Prop16Geometry D c d)
    (hsub : ball (t : ℂ) r ∩ H ⊆ D) {z : ℂ} (hz : z ∈ Hbar) {R0 : ℝ} (hR0 : 0 < R0)
    (hball : closedBall z R0 ⊆ ball (t : ℂ) r) : LocalBall D (realSet (Icc c d)) z R0 := by
  have hr : 0 < r := by
    have := mem_ball.1 (hball (mem_closedBall_self hR0.le))
    exact lt_of_le_of_lt dist_nonneg this
  refine ⟨hz, hR0, hgeom.2.2.2.1, ?_, ?_⟩
  · intro x hx
    exact halfDisc_subset_closure_m7a hr hsub ⟨ball_subset_closedBall (hball hx.1), hx.2⟩
  · intro x hx
    exact frontier_inter_ball_subset_m7a hgeom hsub ⟨hx.2, hball hx.1⟩

theorem closedBall_conj_subset_m7b {z : ℂ} {s t r : ℝ} (h : closedBall z s ⊆ ball (t : ℂ) r) :
    closedBall (conj z) s ⊆ ball (t : ℂ) r := by
  intro y hy
  have h1 : conj y ∈ closedBall z s := by
    rw [mem_closedBall_iff_norm] at hy ⊢
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj]; exact hy
  have h2 := mem_ball_iff_norm.1 (h h1)
  rw [norm_conj_sub_ofReal_k3] at h2
  exact mem_ball_iff_norm.2 h2

/-- **Annulus features of annuli inside the half-disc lie in `H_supp(U)`.** -/
theorem annulusFeat_mem_localClosure_m7b {D S : Set ℂ} (hb : Bornology.IsBounded D) {z : ℂ}
    {s s' t r : ℝ} (hloc : LocalBall D S z s') (hs : 0 < s) (hss' : s < s')
    (hball : closedBall z s' ⊆ ball (t : ℂ) r) :
    annulusFeat D z s s' ∈ localClosure D (mixedSpace D S) t r := by
  obtain ⟨Φ, ψ, -, -, -, hΦint, -, hψb', hmem, hT⟩ := exists_radialApprox_tendsto hb hloc hs hss'
  have hΦ0 : ∀ n u, s' ^ 2 ≤ u → Φ n u = 0 := by
    intro n u hu
    rw [hΦint n u]
    have : ∫ x in (s' ^ 2)..u, -ψ n x / (2 * x) = ∫ _ in (s' ^ 2)..u, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le hu] at hx
      simp [hψb' n x hx.1]
    rw [this, intervalIntegral.integral_zero]
  have hsupp : ∀ n, tsupport (radialApprox (Φ n) z) ⊆ ball (t : ℂ) r := by
    intro n
    have h1 : Function.support (radialApprox (Φ n) z) ⊆ closedBall z s' ∪ closedBall (conj z) s' := by
      intro x hx
      by_contra hc
      rw [mem_union, not_or, mem_closedBall_iff_norm, mem_closedBall_iff_norm, not_le,
        not_le] at hc
      apply hx
      have e1 : s' ^ 2 ≤ ‖x - z‖ ^ 2 := pow_le_pow_left₀ (by linarith) hc.1.le 2
      have e2 : s' ^ 2 ≤ ‖x - conj z‖ ^ 2 := pow_le_pow_left₀ (by linarith) hc.2.le 2
      simp only [radialApprox, hΦ0 n _ e1, hΦ0 n _ e2, add_zero]
    refine (closure_minimal h1 (isClosed_closedBall.union isClosed_closedBall)).trans ?_
    exact union_subset hball (closedBall_conj_subset_m7b hball)
  refine (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hT
    (Eventually.of_forall fun n => ?_)
  exact Submodule.le_topologicalClosure _
    (Submodule.subset_span ⟨_, ⟨hmem n, hsupp n⟩, rfl⟩)

/-- **Independence of the radius.** For `w ⊥ H_supp(U)`, `⟪v_{fold_{z,s}}, w⟫` does not depend
on `s` while `closedBall z s ⊆ ball t r` (M2 + the previous lemma). -/
theorem inner_rieszVec_foldedCircle_eq_m7b {D : Set ℂ} {c d t r : ℝ}
    (hgeom : Prop16Geometry D c d) (hsub : ball (t : ℂ) r ∩ H ⊆ D) {z : ℂ} (hz : z ∈ Hbar)
    {s₁ s₂ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂) (hzs : ‖z - t‖ + s₂ < r) {w : GradSpace D}
    (hw : w ∈ (localClosure D (mixedSpace D (realSet (Icc c d))) t r)ᗮ) :
    ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (foldedCircle z s₁), w⟫ =
      ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (foldedCircle z s₂), w⟫ := by
  have hS : realSet (Icc c d) ⊆ {z : ℂ | z.im = 0} := by
    rintro _ ⟨s, -, rfl⟩
    simp
  set R0 : ℝ := (s₂ + (r - ‖z - t‖)) / 2 with hR0
  have hball : ∀ ρ, ρ < r - ‖z - t‖ → closedBall z ρ ⊆ ball (t : ℂ) r := by
    intro ρ hρ x hx
    rw [mem_closedBall_iff_norm] at hx
    rw [mem_ball_iff_norm]
    calc ‖x - t‖ = ‖(x - z) + (z - t)‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z - t‖ := norm_add_le _ _
      _ < r := by linarith
  have hloc : LocalBall D (realSet (Icc c d)) z R0 :=
    localBall_of_sub_m7b hgeom hsub hz (by rw [hR0]; linarith) (hball R0 (by rw [hR0]; linarith))
  have hloc2 : LocalBall D (realSet (Icc c d)) z s₂ :=
    localBall_of_sub_m7b hgeom hsub hz (by linarith) (hball s₂ (by linarith))
  have hA := rieszVec_annulus' hgeom.1 hgeom.2.2.2.1 hgeom.2.2.1 hS hloc hs₁ h12
    (by rw [hR0]; linarith)
  have hmem := annulusFeat_mem_localClosure_m7b hgeom.2.2.1 hloc2 hs₁ h12 (hball s₂ (by linarith))
  have h0 : ⟪annulusFeat D z s₁ s₂, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hmem hw
  rw [← hA, inner_sub_left, sub_eq_zero] at h0
  exact h0

variable {D S K : Set ℂ} {R : ℝ}

/-- **Localized M5** (copy of `inner_rieszVec_eq_integral_of_mem_orthogonal`, with the
orthogonality to the annulus span replaced by orthogonality to the annuli about points of
`K`). -/
theorem inner_rieszVec_eq_integral_local_m7b (h : MixedLocalHyp D S K R)
    (hpos : ∃ g ∈ mixedSpace D S, 0 < dirichletEnergyOn D g) {μ : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hμK : μ Kᶜ = 0) {s : ℝ} (hs : 0 < s) (hsR : s < 2 * R)
    {u : GradSpace D} (hu : u ∈ gradClosure D (mixedSpace D S))
    (hu' : ∀ z ∈ K, ∀ a, 0 < a → a < s → ⟪annulusFeat D z a s, u⟫ = 0) :
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
    have h0 : ⟪annulusFeat D z t s, u⟫ = 0 := hu' z hz t ht.1 ht1
    rw [← hA, inner_sub_left, sub_eq_zero] at h0
    exact h0.symm
  exact tendsto_nhds_unique hT (tendsto_const_nhds.congr' hev)

/-- The local hypothesis of M5 on the closed half-disc `closedBall t r'' ∩ Hbar`, `r'' < r`. -/
theorem mixedLocalHyp_halfDisc_m7b {c d t r r'' : ℝ} (hgeom : Prop16Geometry D c d)
    (hr''r : r'' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) :
    MixedLocalHyp D (realSet (Icc c d)) (closedBall (t : ℂ) r'' ∩ Hbar) ((r - r'') / 4) where
  isOpen := hgeom.1
  subset_H := hgeom.2.2.2.1
  bounded := hgeom.2.2.1
  free_real := by
    rintro _ ⟨s, -, rfl⟩
    simp
  compact := (isCompact_closedBall _ _).inter_right isClosed_Hbar
  pos := by linarith
  local_ := fun _ hz => localBall_of_halfDisc_m7a hgeom hr''r hsub hz

/-- **Local mean-value representation.** For `w ⊥ H_supp(U)` in the gradient closure and
admissible `μ` carried by `closedBall t r'' ∩ Hbar`,
`⟪v_μ, w⟫ = ∫ ⟪v_{fold_{z,s}}, w⟫ dμ(z)` for `0 < s < (r − r'')/2`. -/
theorem inner_rieszVec_eq_integral_halfDisc_m7b {c d t r r'' : ℝ}
    (hgeom : Prop16Geometry D c d) (hr''r : r'' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ (closedBall (t : ℂ) r'' ∩ Hbar)ᶜ = 0)
    {s : ℝ} (hs : 0 < s) (hsR : s < (r - r'') / 2) {w : GradSpace D}
    (hwG : w ∈ gradClosure D (mixedSpace D (realSet (Icc c d))))
    (hw : w ∈ (localClosure D (mixedSpace D (realSet (Icc c d))) t r)ᗮ) :
    ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) μ, w⟫ =
      ∫ z, ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (foldedCircle z s), w⟫ ∂μ := by
  have hV := isDNSpace_mixedSpace D (realSet (Icc c d))
  by_cases hpos : ∃ g ∈ mixedSpace D (realSet (Icc c d)), 0 < dirichletEnergyOn D g
  swap
  · have h0 : ∀ ρ, rieszVec D (mixedSpace D (realSet (Icc c d))) ρ = 0 := fun ρ =>
      eq_zero_of_mem_gradClosure_of_nopos hV hpos rieszVec_mem
    simp [h0]
  have h := mixedLocalHyp_halfDisc_m7b hgeom hr''r hsub
  refine inner_rieszVec_eq_integral_local_m7b h hpos hμ hμK hs (by linarith) hwG ?_
  intro z hz a ha has
  have hzt : ‖z - t‖ ≤ r'' := mem_closedBall_iff_norm.1 hz.1
  have hball : closedBall z s ⊆ ball (t : ℂ) r := by
    intro x hx
    rw [mem_closedBall_iff_norm] at hx
    rw [mem_ball_iff_norm]
    calc ‖x - t‖ = ‖(x - z) + (z - t)‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z - t‖ := norm_add_le _ _
      _ < r := by linarith
  have hloc := localBall_of_sub_m7b hgeom hsub hz.2 (ha.trans has) hball
  exact Submodule.inner_right_of_mem_orthogonal
    (annulusFeat_mem_localClosure_m7b hgeom.2.2.1 hloc ha has hball) hw

end QuantumZipper.K3
