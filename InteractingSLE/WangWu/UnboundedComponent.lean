/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Growth
import SupercriticalConformalCovariance.ZBConformal.GFFLaw
import SupercriticalConformalCovariance.ZBConformal.Pullback
import LQGMetric.Complex.HarmonicComp

/-!
# Wang–Wu Corollary 4.8 for every component, bounded or not

Packet PROVE-WW-TRACE. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), §4.2,
Lemma 4.6 and Corollary 4.8 (text dump L1058–L1184):

> **Corollary 4.8** (Identification of a component mean). Let `C` be a simply connected component of the complement
> of a local set. Suppose its conditional mean `H_A` and a bounded harmonic candidate `v` have the same continuous
> boundary limits at every prime end except finitely many. Then `H_A = v` on `C`.
> *Proof.* After mapping the ambient domain to a bounded one, take a Riemann map `ϕ : 𝔻 → C` … Koebe distortion
> and the quarter theorem give `dist(ϕ(w), ∂C) ≥ c_ϕ (1 − |w|)²`. Lemma 4.6 therefore gives logarithmic radial
> growth for `(H_A − v) ∘ ϕ`. … Apply Lemma 4.7.

PROVE-WW-B2 proved Lemma 4.6 in bounded windows of `ℍ` (`ae_abs_le_log_of_condMean`) and Corollary 4.8 for
bounded components (`ae_eqOn_of_condMean`). A component of `ℍ \ A` can be unbounded (the complement of a trace),
and near `∞` the window bound gives no control. This file supplies the missing control by conformal transport, as
the source does, with the ℍ-automorphism `m(z) = −1/z` (which exchanges `0` and `∞`; at `κ = 4` the field transforms
as a scalar):

* the zero-boundary GFF pulls back to a zero-boundary GFF (SupercriticalConformalCovariance
  `isZeroBoundaryGFF_distPullback`), its conditional mean to the pulled-back conditional mean, and a harmonic
  representative `v` on `U` to the representative `v ∘ m` on `m(U)` (`integral_mul_confPushTest`,
  `harmonicOnNhd_comp_holo`);
* distances distort by at most `4|z|²`: `dist(m z, m(U)ᶜ) ≥ dist(z, Uᶜ)/(4|z|²)` (`le_infDist_negInv`);
* hence, from the window `|z| ≤ 1` for the field and for its transport, **Lemma 4.6 on all of `ℍ`**
  (`ae_abs_le_log_global_of_condMean`, `ae_abs_le_log_global_of_condMean_add`): a.s. there is a finite `C` with
  `|v(z)| ≤ C (1 + log(1 + |z|) + log(1 + 1/dist(z, A ∪ ℝ)))` for every `z ∈ ℍ \ A`;
* the Riemann map `f : 𝔻 → C` grows at most like a power of `1/(1 − |ζ|)` (QuantumZipper's Koebe growth theorem
  `CA.Koebe.norm_sub_le_growth_global`), so the extra `log(1 + |z|)` is again logarithmic in the disc
  (`eqOn_of_log_norm_growth_of_tendsto`, the deterministic core), and Lemma 4.7 (`eqOn_zero_of_log_growth`) applies;
* **Corollary 4.8 for every simply connected component** (`ae_eqOn_of_condMean_global`,
  `ae_eqOn_of_condMean_add_global`), with no boundedness hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.WangWu

open SupercriticalConformalCovariance SupercriticalConformalCovariance.ZBConformal
open QuantumZipper (H)

/-! ### The automorphism `z ↦ −1/z` of `ℍ` -/

/-- The involutive automorphism `m(z) = −1/z` of `ℍ`; it exchanges `0` and `∞`. -/
def negInv (z : ℂ) : ℂ := -z⁻¹

@[simp] lemma negInv_negInv (z : ℂ) : negInv (negInv z) = z := by simp [negInv]

lemma negInv_involutive : Function.Involutive negInv := negInv_negInv

lemma norm_negInv (z : ℂ) : ‖negInv z‖ = ‖z‖⁻¹ := by simp [negInv]

lemma ne_zero_of_mem_H {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  have h' : (0 : ℝ) < z.im := hz
  rw [h, zero_im] at h'
  exact lt_irrefl _ h'

lemma negInv_mem_H {z : ℂ} (hz : z ∈ H) : negInv z ∈ H := by
  have hz0 := ne_zero_of_mem_H hz
  have h0 : (0 : ℝ) < z.im := hz
  show 0 < (negInv z).im
  rw [negInv, neg_im, inv_im, neg_div, neg_neg]
  exact div_pos h0 (normSq_pos.2 hz0)

lemma differentiableOn_negInv : DifferentiableOn ℂ negInv H := fun _ hz =>
  ((differentiableAt_inv (ne_zero_of_mem_H hz)).neg).differentiableWithinAt

lemma continuousOn_negInv : ContinuousOn negInv H := differentiableOn_negInv.continuousOn

/-- `m` is a conformal bijection of `ℍ` onto itself. -/
theorem isConformalBijection_negInv :
    IsConformalBijection negInv (upperHalfPlaneOpens : Set ℂ) (upperHalfPlaneOpens : Set ℂ) :=
  ⟨differentiableOn_negInv, fun _ hz => negInv_mem_H hz, negInv_involutive.injective.injOn,
    fun y hy => ⟨negInv y, negInv_mem_H hy, negInv_negInv y⟩⟩

lemma image_negInv_subset_H {U : Set ℂ} (hU : U ⊆ H) : negInv '' U ⊆ H := by
  rintro _ ⟨z, hz, rfl⟩
  exact negInv_mem_H (hU hz)

lemma image_negInv_image_negInv (U : Set ℂ) : negInv '' (negInv '' U) = U := by
  rw [image_image]; simp

lemma isOpen_image_negInv {U : Set ℂ} (hUo : IsOpen U) (hU : U ⊆ H) : IsOpen (negInv '' U) := by
  have heq : negInv '' U = H ∩ negInv ⁻¹' U := by
    rw [negInv_involutive.image_eq_preimage_symm]
    ext z
    refine ⟨fun hz => ⟨?_, hz⟩, fun hz => hz.2⟩
    have := negInv_mem_H (hU hz)
    rwa [negInv_negInv] at this
  rw [heq]
  exact continuousOn_negInv.isOpen_inter_preimage QuantumZipper.isOpen_H hUo

/-! ### The support of a transported test function -/

/-- The transported test function `confPushTest hφ ψ` is supported in `φ(supp ψ)`. -/
theorem tsupport_confPushTest_subset {φ : ℂ → ℂ} {U V : TopologicalSpace.Opens ℂ}
    (hφ : IsConformalBijection φ U V) (ψ : LQGMetric.TestOn U) :
    tsupport (confPushTest hφ ψ) ⊆ φ '' tsupport ψ := by
  have hψφ : ∀ z ∈ (U : Set ℂ), Function.invFunOn φ U (φ z) = z := fun _ hz =>
    hφ.2.injOn.leftInvOn_invFunOn hz
  have hd : DifferentiableOn ℂ (Function.invFunOn φ U) V := by
    have h := SmallGammaGeodesics.CC.differentiableOn_leftInv U.isOpen hφ.1 hφ.2.injOn hψφ
    rwa [hφ.2.image_eq] at h
  have hi : InjOn (Function.invFunOn φ U) V := by
    have h := SmallGammaGeodesics.CC.injOn_leftInv hψφ
    rwa [hφ.2.image_eq] at h
  have hU : (U : Set ℂ) ⊆ Function.invFunOn φ U '' V := by
    rw [← hφ.2.image_eq, SmallGammaGeodesics.CC.image_leftInv_image hψφ subset_rfl]
  have hφψ : ∀ y ∈ (V : Set ℂ), φ (Function.invFunOn φ U y) = y := fun _ hy =>
    SmallGammaGeodesics.CC.apply_leftInv hψφ (hφ.2.image_eq.symm ▸ hy)
  exact SmallGammaGeodesics.CC.tsupport_confPullFun_subset V.isOpen hd hi hφψ ψ.hasCompactSupport
    (ψ.tsupport_subset.trans hU)

/-! ### Transport of harmonic representatives -/

/-- A harmonic representative `v` of a distribution `g` on `U ⊆ ℍ` transports to the representative `v ∘ m` of the
pulled-back distribution on `m(U)`. -/
theorem rep_negInv {U : Set ℂ} {g : LQGMetric.DistOn upperHalfPlaneOpens} {v : ℂ → ℝ}
    (hrep : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ U → g φ = ∫ z, v z * φ z)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψ : tsupport ψ ⊆ negInv '' U) :
    distPullback isConformalBijection_negInv g ψ = ∫ z, (v ∘ negInv) z * ψ z := by
  rw [distPullback_apply]
  have hsupp : tsupport (confPushTest isConformalBijection_negInv ψ) ⊆ U := by
    refine (tsupport_confPushTest_subset isConformalBijection_negInv ψ).trans ?_
    calc negInv '' tsupport ψ ⊆ negInv '' (negInv '' U) := image_mono hψ
      _ = U := image_negInv_image_negInv U
  rw [hrep _ hsupp, integral_mul_confPushTest]
  rfl

theorem harmonicOnNhd_comp_negInv {U : Set ℂ} (hUo : IsOpen U) (hU : U ⊆ H) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v U) :
    InnerProductSpace.HarmonicOnNhd (v ∘ negInv) (negInv '' U) := by
  refine LQGMetric.harmonicOnNhd_comp_holo hUo (isOpen_image_negInv hUo hU) hv
    (differentiableOn_negInv.mono (image_negInv_subset_H hU)) ?_
  rintro _ ⟨z, hz, rfl⟩
  rw [negInv_negInv]; exact hz

/-! ### Distortion of the distance to the complement -/

/-- **Distance distortion under `m`**: for `z ∈ U ⊆ ℍ`, `dist(m z, m(U)ᶜ) ≥ dist(z, Uᶜ)/(4|z|²)`. -/
theorem le_infDist_negInv {U : Set ℂ} (hU : U ⊆ H) {z : ℂ} (hz : z ∈ U) :
    infDist z Uᶜ / (4 * ‖z‖ ^ 2) ≤ infDist (negInv z) (negInv '' U)ᶜ := by
  have hzH := hU hz
  have hz0 := ne_zero_of_mem_H hzH
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set d := infDist z Uᶜ with hd
  have hdle : d ≤ ‖z‖ := (infDist_compl_le_im hU hzH).trans (Complex.im_le_norm z)
  have hd0 : 0 ≤ d := infDist_nonneg
  have hne : (negInv '' U)ᶜ.Nonempty := ⟨0, fun h => ne_zero_of_mem_H
    (image_negInv_subset_H hU h) rfl⟩
  refine (le_infDist hne).2 fun y hy => ?_
  by_contra hlt
  push Not at hlt
  apply hy
  set ε := d / (4 * ‖z‖ ^ 2) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεle : ε ≤ ‖z‖⁻¹ / 4 := by
    rw [hε, div_le_iff₀ (by positivity)]
    have : ‖z‖⁻¹ / 4 * (4 * ‖z‖ ^ 2) = ‖z‖ := by field_simp
    rw [this]; exact hdle
  have hdy : ‖y - negInv z‖ < ε := by rw [← dist_eq_norm, dist_comm]; exact hlt
  have hy0 : 3 / 4 * ‖z‖⁻¹ ≤ ‖y‖ := by
    have h1 : ‖negInv z‖ ≤ ‖y‖ + ‖y - negInv z‖ := by
      have := norm_sub_le y (y - negInv z)
      rw [sub_sub_cancel] at this
      linarith
    rw [norm_negInv] at h1
    linarith
  have hyne : y ≠ 0 := by
    intro h; rw [h, norm_zero] at hy0
    have : 0 < 3 / 4 * ‖z‖⁻¹ := by positivity
    linarith
  have hy0' : 0 < ‖y‖ := norm_pos_iff.2 hyne
  -- `m y − z = −z (y − m z)/y`
  have hid : negInv y - z = -(z * (y - negInv z)) / y := by
    simp only [negInv]
    field_simp
    ring
  have hdist : dist (negInv y) z < d := by
    rw [dist_eq_norm, hid, norm_div, norm_neg, norm_mul]
    rw [div_lt_iff₀ hy0']
    calc ‖z‖ * ‖y - negInv z‖ ≤ ‖z‖ * ε := mul_le_mul_of_nonneg_left hdy.le hn.le
      _ = d / (4 * ‖z‖) := by rw [hε]; field_simp
      _ < d * (3 / 4 * ‖z‖⁻¹) := by
          rcases hd0.lt_or_eq with hdpos | hdz
          · rw [div_lt_iff₀ (by positivity)]
            field_simp
            nlinarith
          · exfalso
            rw [← hdz, zero_div] at hε
            rw [hε] at hdy
            exact absurd hdy (not_lt.2 (norm_nonneg _))
      _ ≤ d * ‖y‖ := mul_le_mul_of_nonneg_left hy0 hd0
  have hmem : negInv y ∈ U := mem_of_dist_lt_infDist hdist
  exact ⟨negInv y, hmem, negInv_negInv y⟩

/-! ### Lemma 4.6 on all of `ℍ` -/

section Global

/-- The transported random set: `ℍ \ negInvSet A = m(ℍ \ A)`. -/
def negInvSet (A : Set ℂ) : Set ℂ := (negInv '' (H \ A))ᶜ

lemma H_diff_negInvSet (A : Set ℂ) : H \ negInvSet A = negInv '' (H \ A) := by
  rw [negInvSet, sdiff_compl, inter_eq_right.2 (image_negInv_subset_H sdiff_subset)]

/-- **The pointwise combination of the two windows.** If `v` is bounded by `C₁ (1 + log(1/d))` in the window
`|z| ≤ 1` and `v ∘ m` by `C₂ (1 + log(1/d))` in the window `|w| ≤ 1` of `m(U)`, then on all of `U`
`|v z| ≤ (|C₁| + 4|C₂|) (1 + log(1 + |z|) + log(1 + 1/d(z)))`, `d(z) = dist(z, Uᶜ)`. -/
theorem abs_le_global_of_windows {U : Set ℂ} (hUo : IsOpen U) (hU : U ⊆ H) {v : ℂ → ℝ}
    {C₁ C₂ : ℝ}
    (h1 : ∀ z ∈ U, ‖z‖ ≤ 1 → infDist z Uᶜ ≤ 1 → |v z| ≤ C₁ * (1 + Real.log (1 / infDist z Uᶜ)))
    (h2 : ∀ w ∈ negInv '' U, ‖w‖ ≤ 1 → infDist w (negInv '' U)ᶜ ≤ 1 →
      |(v ∘ negInv) w| ≤ C₂ * (1 + Real.log (1 / infDist w (negInv '' U)ᶜ)))
    {z : ℂ} (hz : z ∈ U) :
    |v z| ≤ (|C₁| + 4 * |C₂|) * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Uᶜ)) := by
  have hzH := hU hz
  have hUc : Uᶜ.Nonempty := ⟨0, fun h => ne_zero_of_mem_H (hU h) rfl⟩
  have hd0 : 0 < infDist z Uᶜ :=
    (hUo.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h hz)
  set d := infDist z Uᶜ with hd
  have hlogz : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hd1pos : 0 < 1 / d := one_div_pos.2 hd0
  have hlogd : 0 ≤ Real.log (1 + 1 / d) := Real.log_nonneg (by linarith)
  have hC : 0 ≤ |C₁| + 4 * |C₂| := by positivity
  have hLd : Real.log (1 / d) ≤ Real.log (1 + 1 / d) := Real.log_le_log hd1pos (by linarith)
  by_cases hz1 : ‖z‖ ≤ 1
  · have hd1 : d ≤ 1 := (infDist_compl_le_im hU hzH).trans ((Complex.im_le_norm z).trans hz1)
    have hL0 : 0 ≤ Real.log (1 / d) := Real.log_nonneg (by rw [le_div_iff₀ hd0]; linarith)
    calc |v z| ≤ C₁ * (1 + Real.log (1 / d)) := h1 z hz hz1 hd1
      _ ≤ |C₁| * (1 + Real.log (1 / d)) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ (|C₁| + 4 * |C₂|) * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / d)) :=
          mul_le_mul (by linarith [abs_nonneg C₂]) (by linarith) (by linarith) hC
  · push Not at hz1
    have hn : 0 < ‖z‖ := by linarith
    have hw : negInv z ∈ negInv '' U := ⟨z, hz, rfl⟩
    have hw1 : ‖negInv z‖ ≤ 1 := by rw [norm_negInv]; exact inv_le_one_of_one_le₀ hz1.le
    have hd'1 : infDist (negInv z) (negInv '' U)ᶜ ≤ 1 :=
      (infDist_compl_le_im (image_negInv_subset_H hU) (negInv_mem_H hzH)).trans
        ((Complex.im_le_norm _).trans hw1)
    have h := h2 _ hw hw1 hd'1
    simp only [Function.comp, negInv_negInv] at h
    set d' := infDist (negInv z) (negInv '' U)ᶜ with hd'
    have hlow := le_infDist_negInv hU hz
    rw [← hd, ← hd'] at hlow
    have hq : 0 < d / (4 * ‖z‖ ^ 2) := by positivity
    have hd'0 : 0 < d' := lt_of_lt_of_le hq hlow
    have hL0 : 0 ≤ Real.log (1 / d') := Real.log_nonneg (by rw [le_div_iff₀ hd'0]; linarith)
    have hL : Real.log (1 / d') ≤ 3 + 2 * Real.log (1 + ‖z‖) + Real.log (1 + 1 / d) := by
      have e1 : Real.log (1 / d') ≤ Real.log (4 * ‖z‖ ^ 2 * (1 / d)) := by
        refine Real.log_le_log (one_div_pos.2 hd'0) ?_
        have : 4 * ‖z‖ ^ 2 * (1 / d) = (d / (4 * ‖z‖ ^ 2))⁻¹ := by field_simp
        rw [this, one_div]
        exact inv_anti₀ hq hlow
      have e2 : Real.log (4 * ‖z‖ ^ 2 * (1 / d)) = Real.log 4 + 2 * Real.log ‖z‖ + Real.log (1 / d) := by
        rw [Real.log_mul (by positivity) hd1pos.ne', Real.log_mul (by norm_num) (by positivity),
          Real.log_pow]
        push_cast; ring
      have e3 : Real.log 4 ≤ 3 := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
        linarith
      have e4 : Real.log ‖z‖ ≤ Real.log (1 + ‖z‖) := Real.log_le_log hn (by linarith)
      linarith
    calc |v z| ≤ C₂ * (1 + Real.log (1 / d')) := h
      _ ≤ |C₂| * (1 + Real.log (1 / d')) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |C₂| * (4 + 2 * Real.log (1 + ‖z‖) + Real.log (1 + 1 / d)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ 4 * |C₂| * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / d)) := by
          nlinarith [abs_nonneg C₂]
      _ ≤ (|C₁| + 4 * |C₂|) * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / d)) :=
          mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C₁]) (by linarith)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Lemma 4.6 on all of `ℍ`.** Under the hypotheses of Lemma 4.6 (PROVE-WW-B2's
`ae_abs_le_log_of_condMean`), almost surely there is a finite constant `C` such that for every harmonic
representative `v` of the conditional mean on `ℍ \ A` and every `z ∈ ℍ \ A`,
`|v(z)| ≤ C (1 + log(1 + |z|) + log(1 + 1/dist(z, A ∪ ℝ)))`. -/
theorem ae_abs_le_log_global_of_condMean [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        h₁ ω φ = ∫ z, v z * φ z) →
      ∀ z ∈ H \ A ω,
        |v z| ≤ C * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z (H \ A ω)ᶜ)) := by
  let _ : MeasurableSpace Ω := mΩ
  have hh' := isZeroBoundaryGFF_distPullback isConformalBijection_negInv hh
  have hmean' : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => distPullback isConformalBijection_negInv (h₁ ω) ψ) =ᵐ[P]
        P[fun ω => distPullback isConformalBijection_negInv (h ω) ψ | 𝒜] := fun ψ => hmean _
  have hopen' : ∀ᵐ ω ∂P, IsOpen (H \ negInvSet (A ω)) := hopen.mono fun ω hω => by
    rw [H_diff_negInvSet]; exact isOpen_image_negInv hω sdiff_subset
  filter_upwards [ae_abs_le_log_of_condMean hh hmean hopen 1,
    ae_abs_le_log_of_condMean hh' hmean' hopen' 1, hopen] with ω ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ hUo
  refine ⟨|C₁| + 4 * |C₂|, fun v hv hrep z hz =>
    abs_le_global_of_windows hUo sdiff_subset (hC₁ v hv hrep) ?_ hz⟩
  have hv' := harmonicOnNhd_comp_negInv hUo sdiff_subset hv
  rw [← H_diff_negInvSet] at hv' ⊢
  exact hC₂ _ hv' fun ψ hψ => rep_negInv hrep ψ (by rwa [← H_diff_negInvSet])

/-- **Lemma 4.6 on all of `ℍ`, for a field with bounded harmonic mean** (`F = h + F₀`, `|F₀| ≤ M_F` on `ℍ`,
`h₁(ψ) = E[h(ψ) + ∫ F₀ ψ | 𝒜]`). -/
theorem ae_abs_le_log_global_of_condMean_add [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {F₀ : ℂ → ℝ} {MF : ℝ}
    (hF₀ : ∀ z ∈ H, |F₀ z| ≤ MF)
    {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ + ∫ z, F₀ z * φ z | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        h₁ ω φ = ∫ z, v z * φ z) →
      ∀ z ∈ H \ A ω,
        |v z| ≤ C * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z (H \ A ω)ᶜ)) := by
  let _ : MeasurableSpace Ω := mΩ
  have hh' := isZeroBoundaryGFF_distPullback isConformalBijection_negInv hh
  have hF₀' : ∀ z ∈ H, |(F₀ ∘ negInv) z| ≤ MF := fun z hz => hF₀ _ (negInv_mem_H hz)
  have hmean' : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => distPullback isConformalBijection_negInv (h₁ ω) ψ) =ᵐ[P]
        P[fun ω => distPullback isConformalBijection_negInv (h ω) ψ
          + ∫ z, (F₀ ∘ negInv) z * ψ z | 𝒜] := fun ψ => by
    have := hmean (confPushTest isConformalBijection_negInv ψ)
    rw [integral_mul_confPushTest] at this
    exact this
  have hopen' : ∀ᵐ ω ∂P, IsOpen (H \ negInvSet (A ω)) := hopen.mono fun ω hω => by
    rw [H_diff_negInvSet]; exact isOpen_image_negInv hω sdiff_subset
  filter_upwards [ae_abs_le_log_of_condMean_add hh h𝒜 hF₀ hmean hopen 1,
    ae_abs_le_log_of_condMean_add hh' h𝒜 hF₀' hmean' hopen' 1, hopen]
    with ω ⟨C₁, hC₁⟩ ⟨C₂, hC₂⟩ hUo
  refine ⟨|C₁| + 4 * |C₂|, fun v hv hrep z hz =>
    abs_le_global_of_windows hUo sdiff_subset (hC₁ v hv hrep) ?_ hz⟩
  have hv' := harmonicOnNhd_comp_negInv hUo sdiff_subset hv
  rw [← H_diff_negInvSet] at hv' ⊢
  exact hC₂ _ hv' fun ψ hψ => rep_negInv hrep ψ (by rwa [← H_diff_negInvSet])

end Global

/-! ### Corollary 4.8 for every component -/

section Cor48

open InteractingSLE.Sec6 QuantumZipper.CA.Koebe

/-- **Corollary 4.8, deterministic core, with growth at `∞`.** Let `f : 𝔻 → C` be a Riemann map onto an open set
`C` (bounded or not), `H'` harmonic on `C` with `|H'(z)| ≤ K (1 + log(1 + |z|) + log(1 + 1/dist(z, ∂C)))`, and `v` a
bounded harmonic candidate. If `H' − v` has boundary limit `0` at every point of the circle outside a finite set,
then `H' = v` on `C`. Koebe's distance estimate `dist(f(w), ∂C) ≥ κ (1 − |w|)^p` and growth theorem
`|f(w)| ≤ |f 0| + |f'(0)| (1 − |w|)^{−p₀}` make both logarithms logarithmic in `1/(1 − |w|)`; Lemma 4.7. -/
theorem eqOn_of_log_norm_growth_of_tendsto {C : Set ℂ} (hCo : IsOpen C) {f : ℂ → ℂ}
    (hf : IsConformalBijection f (ball 0 1) C) {H' v : ℂ → ℝ}
    (hH : InnerProductSpace.HarmonicOnNhd H' C) (hv : InnerProductSpace.HarmonicOnNhd v C)
    {M : ℝ} (hvb : ∀ z ∈ C, |v z| ≤ M) {K : ℝ}
    (hgrowth : ∀ z ∈ C, |H' z| ≤
      K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + (infDist z (frontier C))⁻¹)))
    {E : Set ℂ} (hE : E.Finite)
    (hbd : ∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
      Tendsto (fun ζ => H' (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) :
    EqOn H' v C := by
  obtain ⟨hfd, hfb⟩ := hf
  have hfinj := hfb.injOn
  have hfim : f '' ball 0 1 = C := hfb.image_eq
  have hball0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hCne : C.Nonempty := ⟨f 0, hfb.mapsTo hball0⟩
  have hCuniv : C ≠ univ := hfim ▸ QuantumZipper.CA.Koebe.image_ball_ne_univ one_pos hfd hfinj
  set κ := koebeCovConst * ‖deriv f 0‖
  have hκ : 0 < κ := mul_pos koebeCovConst_pos
    (norm_pos_iff.2 (QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hfd hfinj hball0))
  set p : ℝ := 1 + koebeDistExp
  have hp0 : 0 < koebeDistExp := koebeDistExp_pos
  have hp : 0 < p := by simp only [p]; linarith
  have hdist : ∀ ζ ∈ ball (0 : ℂ) 1, κ * (1 - ‖ζ‖) ^ p ≤ infDist (f ζ) (frontier C) := by
    intro ζ hζ
    have := koebe_mul_pow_le_infDist hfd hfinj hζ
    rw [hfim] at this
    exact this.trans (infDist_compl_le_infDist_frontier hCo hCne hCuniv _)
  set A₀ : ℝ := 1 + ‖f 0‖ + ‖deriv f 0‖
  have hA₀ : 1 ≤ A₀ := by simp only [A₀]; linarith [norm_nonneg (f 0), norm_nonneg (deriv f 0)]
  -- the growth theorem
  have hgrow : ∀ ζ ∈ ball (0 : ℂ) 1,
      Real.log (1 + ‖f ζ‖) ≤ Real.log A₀ + koebeDistExp * Real.log (1 / (1 - ‖ζ‖)) := by
    intro ζ hζ
    have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have hr : 0 < 1 - ‖ζ‖ := by linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hy : 0 < (1 - ‖ζ‖) ^ koebeDistExp := Real.rpow_pos_of_pos hr _
    have hy1 : (1 - ‖ζ‖) ^ koebeDistExp ≤ 1 := Real.rpow_le_one hr.le hr1 hp0.le
    have hX : 1 ≤ ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹ := one_le_inv₀ hy |>.2 hy1
    have h := QuantumZipper.CA.Koebe.norm_sub_le_growth_global hfd hfinj hζ
    rw [dist_zero_right, div_one, Real.rpow_neg hr.le] at h
    have hfz : 1 + ‖f ζ‖ ≤ A₀ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹ := by
      have h1 : ‖f ζ‖ ≤ ‖f 0‖ + ‖f ζ - f 0‖ := by
        have := norm_add_le (f 0) (f ζ - f 0)
        rwa [add_sub_cancel] at this
      have h2 : ‖ζ‖ * (‖deriv f 0‖ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹) ≤
          ‖deriv f 0‖ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹ :=
        mul_le_of_le_one_left (by positivity) hz1.le
      simp only [A₀]
      nlinarith [norm_nonneg (f 0), norm_nonneg (deriv f 0)]
    calc Real.log (1 + ‖f ζ‖) ≤ Real.log (A₀ * ((1 - ‖ζ‖) ^ koebeDistExp)⁻¹) :=
          Real.log_le_log (by positivity) hfz
      _ = Real.log A₀ + koebeDistExp * Real.log (1 / (1 - ‖ζ‖)) := by
          rw [Real.log_mul (by linarith) (inv_pos.2 hy).ne', Real.log_inv, Real.log_rpow hr, one_div,
            Real.log_inv]
          ring
  -- logarithmic radial growth of `(H' − v) ∘ f`
  set K' : ℝ := |K| * (1 + Real.log A₀ + koebeDistExp + Real.log (1 + κ⁻¹) + p) + |M|
  have hgrowth' : ∀ ζ ∈ ball (0 : ℂ) 1, 0 < ‖ζ‖ →
      |H' (f ζ) - v (f ζ)| ≤ K' * (1 + Real.log (1 / (1 - ‖ζ‖))) := by
    intro ζ hζ _
    have hz1 : ‖ζ‖ < 1 := mem_ball_zero_iff.1 hζ
    have hr : 0 < 1 - ‖ζ‖ := by linarith
    have hr1 : 1 - ‖ζ‖ ≤ 1 := by linarith [norm_nonneg ζ]
    have hL0 := log_one_div_nonneg hr hr1
    have hy : 0 < (1 - ‖ζ‖) ^ p := Real.rpow_pos_of_pos hr p
    have hy1 : (1 - ‖ζ‖) ^ p ≤ 1 := Real.rpow_le_one hr.le hr1 hp.le
    have hd := hdist ζ hζ
    have hd0 : 0 < κ * (1 - ‖ζ‖) ^ p := mul_pos hκ hy
    have h1 : 1 + (infDist (f ζ) (frontier C))⁻¹ ≤ (1 + κ⁻¹) * ((1 - ‖ζ‖) ^ p)⁻¹ := by
      have hinv : (infDist (f ζ) (frontier C))⁻¹ ≤ κ⁻¹ * ((1 - ‖ζ‖) ^ p)⁻¹ := by
        rw [← mul_inv]
        exact inv_anti₀ hd0 hd
      have hge : 1 ≤ ((1 - ‖ζ‖) ^ p)⁻¹ := one_le_inv₀ hy |>.2 hy1
      nlinarith [inv_pos.2 hκ]
    have hpos1 : 0 < 1 + (infDist (f ζ) (frontier C))⁻¹ := by
      have := inv_nonneg.2 (infDist_nonneg (x := f ζ) (s := frontier C)); linarith
    have hκ1 : 0 < 1 + κ⁻¹ := by have := inv_pos.2 hκ; linarith
    have h2 : Real.log (1 + (infDist (f ζ) (frontier C))⁻¹) ≤
        Real.log (1 + κ⁻¹) + p * Real.log (1 / (1 - ‖ζ‖)) := by
      calc Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)
          ≤ Real.log ((1 + κ⁻¹) * ((1 - ‖ζ‖) ^ p)⁻¹) := Real.log_le_log hpos1 h1
        _ = Real.log (1 + κ⁻¹) + p * Real.log (1 / (1 - ‖ζ‖)) := by
          rw [Real.log_mul hκ1.ne' (inv_pos.2 hy).ne', Real.log_inv, Real.log_rpow hr, one_div,
            Real.log_inv]
          ring
    have h3 := hgrow ζ hζ
    have hlogA : 0 ≤ Real.log A₀ := Real.log_nonneg hA₀
    have hκlog : 0 ≤ Real.log (1 + κ⁻¹) := Real.log_nonneg (by have := inv_pos.2 hκ; linarith)
    have hlog0 : 0 ≤ Real.log (1 + (infDist (f ζ) (frontier C))⁻¹) := Real.log_nonneg (by
      have := inv_nonneg.2 (infDist_nonneg (x := f ζ) (s := frontier C)); linarith)
    have hlogn : 0 ≤ Real.log (1 + ‖f ζ‖) := Real.log_nonneg (by linarith [norm_nonneg (f ζ)])
    set L := Real.log (1 / (1 - ‖ζ‖))
    have hHz : |H' (f ζ)| ≤
        |K| * (1 + Real.log A₀ + koebeDistExp + Real.log (1 + κ⁻¹) + p) * (1 + L) := by
      calc |H' (f ζ)| ≤ K * (1 + Real.log (1 + ‖f ζ‖) +
            Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)) := hgrowth _ (hfb.mapsTo hζ)
        _ ≤ |K| * (1 + Real.log (1 + ‖f ζ‖) +
            Real.log (1 + (infDist (f ζ) (frontier C))⁻¹)) :=
            mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
        _ ≤ |K| * (1 + (Real.log A₀ + koebeDistExp * L) + (Real.log (1 + κ⁻¹) + p * L)) := by
            gcongr
        _ ≤ |K| * (1 + Real.log A₀ + koebeDistExp + Real.log (1 + κ⁻¹) + p) * (1 + L) := by
            rw [mul_assoc]
            gcongr
            nlinarith
    have hvz : |v (f ζ)| ≤ |M| * (1 + L) :=
      ((hvb _ (hfb.mapsTo hζ)).trans (le_abs_self M)).trans
        (le_mul_of_one_le_right (abs_nonneg _) (by linarith))
    calc |H' (f ζ) - v (f ζ)| ≤ |H' (f ζ)| + |v (f ζ)| := abs_sub _ _
      _ ≤ _ := add_le_add hHz hvz
      _ = K' * (1 + L) := by simp only [K']; ring
  have hu := harmonicOnNhd_comp_sub ⟨hfd, hfb⟩ hH hv
  have h0 := eqOn_zero_of_log_growth hu hE hgrowth' hbd
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := hfb.surjOn hz
  have := h0 ζ hζ
  linarith

/-- For `z ∈ C ⊆ U ⊆ ℍ` (both open), `log(1 + 1/dist(z, Uᶜ)) ≤ log(1 + 1/dist(z, ∂C))`. -/
theorem log_one_add_inv_infDist_le {U C : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) (hCo : IsOpen C)
    (hCU : C ⊆ U) {z : ℂ} (hz : z ∈ C) :
    Real.log (1 + 1 / infDist z Uᶜ) ≤ Real.log (1 + (infDist z (frontier C))⁻¹) := by
  have hzU := hCU hz
  have hUc : Uᶜ.Nonempty := ⟨0, fun h0 => ne_zero_of_mem_H (hUH h0) rfl⟩
  have hCc : Cᶜ.Nonempty := hUc.mono (compl_subset_compl.2 hCU)
  have hd0 : 0 < infDist z Uᶜ :=
    (hUo.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h hzU)
  have hfr0 : 0 < infDist z (frontier C) := by
    have hfrne : (frontier C).Nonempty := by
      refine nonempty_frontier_iff.2 ⟨⟨z, hz⟩, fun huniv => ?_⟩
      obtain ⟨w, hw⟩ := hCc
      exact hw (huniv ▸ mem_univ w)
    exact (isClosed_frontier.notMem_iff_infDist_pos hfrne).1
      (fun hf' => (hCo.inter_frontier_eq.subset ⟨hz, hf'⟩ : z ∈ (∅ : Set ℂ)))
  have hdle : infDist z (frontier C) ≤ infDist z Uᶜ :=
    (infDist_frontier_le_infDist_compl hCo hz hCc).trans
      (infDist_le_infDist_of_subset (compl_subset_compl.2 hCU) hUc)
  refine Real.log_le_log (by positivity) ?_
  rw [one_div]
  linarith [inv_anti₀ hfr0 hdle]

/-- From the global bound of Lemma 4.6 on `U` to the growth hypothesis of the deterministic core on `C ⊆ U`. -/
theorem growth_of_global {U C : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) (hCo : IsOpen C)
    (hCU : C ⊆ U) {H' : ℂ → ℝ} {K : ℝ}
    (hK : ∀ z ∈ U, |H' z| ≤ K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Uᶜ))) :
    ∀ z ∈ C, |H' z| ≤
      |K| * (1 + Real.log (1 + ‖z‖) + Real.log (1 + (infDist z (frontier C))⁻¹)) := by
  intro z hz
  have hlogz : 0 ≤ Real.log (1 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
  have hUc : Uᶜ.Nonempty := ⟨0, fun h0 => ne_zero_of_mem_H (hUH h0) rfl⟩
  have hd0 : 0 < infDist z Uᶜ :=
    (hUo.isClosed_compl.notMem_iff_infDist_pos hUc).1 (fun h => h (hCU hz))
  have hlogd : 0 ≤ Real.log (1 + 1 / infDist z Uᶜ) :=
    Real.log_nonneg (by have := one_div_pos.2 hd0; linarith)
  calc |H' z| ≤ K * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Uᶜ)) := hK z (hCU hz)
    _ ≤ |K| * (1 + Real.log (1 + ‖z‖) + Real.log (1 + 1 / infDist z Uᶜ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    _ ≤ |K| * (1 + Real.log (1 + ‖z‖) + Real.log (1 + (infDist z (frontier C))⁻¹)) :=
        mul_le_mul_of_nonneg_left (by linarith [log_one_add_inv_infDist_le hUo hUH hCo hCU hz])
          (abs_nonneg K)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Corollary 4.8 (identification of a component mean), for every component.** Under the hypotheses of Lemma 4.6,
almost surely the following holds for every harmonic representative `H'` of the conditional mean on `ℍ \ A`: if
`C ⊆ ℍ \ A` is an open set (bounded or not) with a Riemann map `f : 𝔻 → C`, and `v` is a bounded harmonic function
on `C` such that `H' ∘ f − v ∘ f → 0` at every boundary point of the disc outside a finite set (the finitely many
exceptional prime ends), then `H' = v` on `C`. -/
theorem ae_eqOn_of_condMean_global [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) :
    ∀ᵐ ω ∂P, ∀ H' : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H' (H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        h₁ ω φ = ∫ z, H' z * φ z) →
      ∀ C : Set ℂ, IsOpen C → C ⊆ H \ A ω →
      ∀ f : ℂ → ℂ, IsConformalBijection f (ball 0 1) C →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      ∀ E : Set ℂ, E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => H' (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) →
      EqOn H' v C := by
  filter_upwards [ae_abs_le_log_global_of_condMean hh hmean hopen, hopen] with ω ⟨K, hK⟩ hUo
  intro H' hH' hrep C hCo hCU f hf v hv hvb E hE hbd
  obtain ⟨M, hM⟩ := hvb
  exact eqOn_of_log_norm_growth_of_tendsto hCo hf (fun z hz => hH' z (hCU hz)) hv hM
    (growth_of_global hUo sdiff_subset hCo hCU (hK H' hH' hrep)) hE hbd

/-- **Corollary 4.8 for every component, for a field with bounded harmonic mean** (`F = h + F₀`, `|F₀| ≤ M_F` on
`ℍ`, `h₁(ψ) = E[h(ψ) + ∫ F₀ ψ | 𝒜]`). -/
theorem ae_eqOn_of_condMean_add_global [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {𝒜 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) {F₀ : ℂ → ℝ} {MF : ℝ}
    (hF₀ : ∀ z ∈ H, |F₀ z| ≤ MF)
    {A : Ω → Set ℂ} {h₁ : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ + ∫ z, F₀ z * φ z | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) :
    ∀ᵐ ω ∂P, ∀ H' : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H' (H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
        h₁ ω φ = ∫ z, H' z * φ z) →
      ∀ C : Set ℂ, IsOpen C → C ⊆ H \ A ω →
      ∀ f : ℂ → ℂ, IsConformalBijection f (ball 0 1) C →
      ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v C → (∃ M, ∀ z ∈ C, |v z| ≤ M) →
      ∀ E : Set ℂ, E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => H' (f ζ) - v (f ζ)) (𝓝[ball 0 1] q) (𝓝 0)) →
      EqOn H' v C := by
  filter_upwards [ae_abs_le_log_global_of_condMean_add hh h𝒜 hF₀ hmean hopen, hopen]
    with ω ⟨K, hK⟩ hUo
  intro H' hH' hrep C hCo hCU f hf v hv hvb E hE hbd
  obtain ⟨M, hM⟩ := hvb
  exact eqOn_of_log_norm_growth_of_tendsto hCo hf (fun z hz => hH' z (hCU hz)) hv hM
    (growth_of_global hUo sdiff_subset hCo hCU (hK H' hH' hrep)) hE hbd

end Cor48

end InteractingSLE.WangWu
