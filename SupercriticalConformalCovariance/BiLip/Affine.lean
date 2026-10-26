import SupercriticalConformalCovariance.BiLip.LocalTools

/-!
# Lemma 2.1, step 2: annulus quantities under complex-affine changes of coordinates

Paper l. 118–119: "The constant factor `φ′_n(z_n)` is removed exactly by affine covariance". If `T(u) = c + a u`
(`a ≠ 0`) and `E(u, v) = D(T u, T v)` for all `u, v` (in applications from the affine-covariance modules'
`ae_complex_affine_covariance`), the `E`-curves are the `T⁻¹`-images of the `D`-curves with the same lengths,
and round annuli correspond: `D(around A_{|a|α, |a|β}(c)) = E(around A_{α,β}(0))` (`aroundDist_affine`), and
the same for the closed-annulus crossing cost (`acr_affine`).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric aroundDist EuclideanAnnulus Disconnects)
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr cann)

section Pull

variable (D E : LSCMetric) (T : ℂ → ℂ) (hT : ∀ x y : ℂ, D (T x, T y) = E (x, y))
include hT

theorem len_pull (P : ℝ → ℂ) (a b : ℝ) : E.len P a b = D.len (T ∘ P) a b := by
  unfold LSCMetric.len
  have h := LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    (F := E.pt ∘ P) (G := D.pt ∘ (T ∘ P)) (c := (1 : ℝ≥0∞))
    (fun s t => by
      change E (P s, P t) = 1 * D (T (P s), T (P t))
      rw [one_mul, hT]) (Icc a b)
  simpa only [one_mul] using h

theorem isCurve_pull (P : ℝ → ℂ) (a b : ℝ) : E.IsCurve P a b ↔ D.IsCurve (T ∘ P) a b := by
  constructor
  · rintro ⟨hab, hP⟩
    refine ⟨hab, fun t ht => ?_⟩
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    apply tendsto_iff_edist_tendsto_0.mpr
    change Tendsto (fun s => D (T (P s), T (P t))) (𝓝[Icc a b] t) (𝓝 0)
    change Tendsto (fun s => E (P s, P t)) (𝓝[Icc a b] t) (𝓝 0) at hlim
    simpa only [hT] using hlim
  · rintro ⟨hab, hP⟩
    refine ⟨hab, fun t ht => ?_⟩
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    apply tendsto_iff_edist_tendsto_0.mpr
    change Tendsto (fun s => E (P s, P t)) (𝓝[Icc a b] t) (𝓝 0)
    change Tendsto (fun s => D (T (P s), T (P t))) (𝓝[Icc a b] t) (𝓝 0) at hlim
    simpa only [hT] using hlim

end Pull

/-- the affine map `u ↦ c + a u` as a homeomorphism -/
def affHomeo (c a : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addLeft c)

theorem affHomeo_apply (c a : ℂ) (ha : a ≠ 0) (u : ℂ) : affHomeo c a ha u = c + a * u := rfl

theorem affHomeo_symm_apply (c a : ℂ) (ha : a ≠ 0) (x : ℂ) :
    (affHomeo c a ha).symm x = a⁻¹ * (x - c) := by
  apply (affHomeo c a ha).injective
  rw [Homeomorph.apply_symm_apply, affHomeo_apply]
  field_simp
  ring

theorem disconnects_image_homeo (e : ℂ ≃ₜ ℂ) {K E F : Set ℂ} (h : Disconnects K E F) :
    Disconnects (e '' K) (e '' E) (e '' F) := by
  rintro ⟨S, hS, hSK, ⟨_, huS, u₀, hu₀E, rfl⟩, ⟨_, hvS, v₀, hv₀F, rfl⟩⟩
  let T : Set ℂ := e.symm '' S
  have hTpre : IsPreconnected T := hS.image e.symm e.symm.continuous.continuousOn
  have hTsub : T ⊆ Kᶜ := by
    rintro x ⟨y, hyS, rfl⟩ hxK
    exact hSK hyS ⟨e.symm y, hxK, e.apply_symm_apply y⟩
  exact h ⟨T, hTpre, hTsub, ⟨u₀, ⟨e u₀, huS, e.symm_apply_apply u₀⟩, hu₀E⟩,
    ⟨v₀, ⟨e v₀, hvS, e.symm_apply_apply v₀⟩, hv₀F⟩⟩

theorem disconnects_image_homeo_iff (e : ℂ ≃ₜ ℂ) {K E F : Set ℂ} :
    Disconnects (e '' K) (e '' E) (e '' F) ↔ Disconnects K E F := by
  constructor
  · intro h
    have h' := disconnects_image_homeo e.symm h
    simpa [Set.image_image] using h'
  · exact disconnects_image_homeo e

section Affine

variable {c a : ℂ} (ha : a ≠ 0)

theorem dist_aff (u : ℂ) : dist (c + a * u) c = ‖a‖ * ‖u‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul]

theorem image_sphere_aff (α : ℝ) :
    affHomeo c a ha '' sphere 0 α = sphere c (‖a‖ * α) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_sphere, affHomeo_apply, dist_aff, mem_sphere_zero_iff_norm.1 hu]
  · intro hx
    refine ⟨a⁻¹ * (x - c), ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_mul, norm_inv, ← dist_eq_norm, mem_sphere.1 hx]
      field_simp
    · rw [affHomeo_apply]; field_simp; ring

theorem disconnects_aff_iff {K : Set ℂ} (α β : ℝ) :
    Disconnects (affHomeo c a ha '' K) (sphere c (‖a‖ * α)) (sphere c (‖a‖ * β)) ↔
      Disconnects K (sphere 0 α) (sphere 0 β) := by
  rw [← image_sphere_aff ha α, ← image_sphere_aff ha β]
  exact disconnects_image_homeo_iff _

variable (D E : LSCMetric) (hT : ∀ x y : ℂ, D (c + a * x, c + a * y) = E (x, y))
include ha hT

/-- **Affine transport of the around cost.** -/
theorem aroundDist_affine {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    aroundDist D ⟨(c, ‖a‖ * α, ‖a‖ * β), mul_pos (norm_pos_iff.2 ha) hα,
        mul_lt_mul_of_pos_left hαβ (norm_pos_iff.2 ha)⟩ =
      aroundDist E ⟨((0 : ℂ), α, β), hα, hαβ⟩ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hmem : ∀ u : ℂ, (c + a * u ∈ ball c (‖a‖ * β) \ closedBall c (‖a‖ * α) ↔
      u ∈ ball 0 β \ closedBall 0 α) := by
    intro u
    simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le, dist_aff,
      dist_zero_right]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨lt_of_mul_lt_mul_left h1 hna.le, lt_of_mul_lt_mul_left h2 hna.le⟩
    · rintro ⟨h1, h2⟩; exact ⟨mul_lt_mul_of_pos_left h1 hna, mul_lt_mul_of_pos_left h2 hna⟩
  have hTf : (fun u => c + a * u) = affHomeo c a ha := rfl
  apply le_antisymm
  · unfold aroundDist
    refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPA =>
      le_iInf fun hdisc => ?_
    have hP' : D.IsCurve ((fun u => c + a * u) ∘ P) s t :=
      (isCurve_pull D E (fun u => c + a * u) hT P s t).1 hP
    refine iInf_le_of_le ((fun u => c + a * u) ∘ P) <| iInf_le_of_le s <| iInf_le_of_le t <|
      iInf_le_of_le hP' <| iInf_le_of_le ?_ <| iInf_le_of_le ?_ ?_
    · intro u hu
      have := (annulus_toSet_mem hα hαβ).1 (hPA u hu)
      exact (annulus_toSet_mem (c := c) (mul_pos hna hα) (mul_lt_mul_of_pos_left hαβ hna)).2
        ((hmem (P u)).2 this)
    · have himg : ((fun u => c + a * u) ∘ P) '' Icc s t = affHomeo c a ha '' (P '' Icc s t) := by
        rw [image_comp]; rfl
      rw [himg]
      show Disconnects _ (sphere c (‖a‖ * α)) (sphere c (‖a‖ * β))
      exact (disconnects_aff_iff ha α β).2 hdisc
    · rw [len_pull D E (fun u => c + a * u) hT]
  · unfold aroundDist
    refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPA =>
      le_iInf fun hdisc => ?_
    set Pi : ℝ → ℂ := fun t => a⁻¹ * (P t - c) with hPi
    have hPPi : (fun u => c + a * u) ∘ Pi = P := by
      funext t; simp only [Function.comp_apply, hPi]; field_simp; ring
    have hPi' : E.IsCurve Pi s t := by
      rw [isCurve_pull D E (fun u => c + a * u) hT, hPPi]; exact hP
    refine iInf_le_of_le Pi <| iInf_le_of_le s <| iInf_le_of_le t <|
      iInf_le_of_le hPi' <| iInf_le_of_le ?_ <| iInf_le_of_le ?_ ?_
    · intro u hu
      have h1 := (annulus_toSet_mem (c := c) (mul_pos hna hα) (mul_lt_mul_of_pos_left hαβ hna)).1
        (hPA u hu)
      rw [← congrFun hPPi u] at h1
      exact (annulus_toSet_mem hα hαβ).2 ((hmem (Pi u)).1 h1)
    · show Disconnects _ (sphere 0 α) (sphere 0 β)
      rw [← disconnects_aff_iff ha α β]
      have himg : affHomeo c a ha '' (Pi '' Icc s t) = P '' Icc s t := by
        rw [← image_comp]; rw [← hPPi]; rfl
      rw [himg]; exact hdisc
    · rw [len_pull D E (fun u => c + a * u) hT, hPPi]

/-- **Affine transport of the closed-annulus crossing cost.** -/
theorem acr_affine (α β : ℝ) :
    acr D c (‖a‖ * α) (‖a‖ * β) = acr E 0 α β := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hmem : ∀ u : ℂ, (c + a * u ∈ cann c (‖a‖ * α) (‖a‖ * β) ↔ u ∈ cann 0 α β) := by
    intro u
    show ‖a‖ * α ≤ dist (c + a * u) c ∧ dist (c + a * u) c ≤ ‖a‖ * β ↔
      α ≤ dist u 0 ∧ dist u 0 ≤ β
    rw [dist_aff, dist_zero_right]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨le_of_mul_le_mul_left h1 hna, le_of_mul_le_mul_left h2 hna⟩
    · rintro ⟨h1, h2⟩; exact ⟨mul_le_mul_of_nonneg_left h1 hna.le, mul_le_mul_of_nonneg_left h2 hna.le⟩
  have hsph : ∀ (u : ℂ) (γ : ℝ), (c + a * u ∈ sphere c (‖a‖ * γ) ↔ u ∈ sphere 0 γ) := by
    intro u γ
    rw [mem_sphere, mem_sphere, dist_aff, dist_zero_right]
    constructor
    · intro h; exact mul_left_cancel₀ hna.ne' h
    · intro h; rw [h]
  apply le_antisymm
  · unfold acr
    refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPA =>
      le_iInf fun hs => le_iInf fun ht => ?_
    have hP' : D.IsCurve ((fun u => c + a * u) ∘ P) s t :=
      (isCurve_pull D E (fun u => c + a * u) hT P s t).1 hP
    refine iInf_le_of_le ((fun u => c + a * u) ∘ P) <| iInf_le_of_le s <| iInf_le_of_le t <|
      iInf_le_of_le hP' <| iInf_le_of_le ?_ <| iInf_le_of_le ((hsph _ _).2 hs) <|
      iInf_le_of_le ((hsph _ _).2 ht) ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact (hmem (P u)).2 (hPA ⟨u, hu, rfl⟩)
    · rw [len_pull D E (fun u => c + a * u) hT]
  · unfold acr
    refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPA =>
      le_iInf fun hs => le_iInf fun ht => ?_
    set Pi : ℝ → ℂ := fun t => a⁻¹ * (P t - c) with hPi
    have hPPi : ∀ t, c + a * Pi t = P t := fun t => by simp only [hPi]; field_simp; ring
    have hPPi' : (fun u => c + a * u) ∘ Pi = P := funext hPPi
    have hPi' : E.IsCurve Pi s t := by
      rw [isCurve_pull D E (fun u => c + a * u) hT, hPPi']; exact hP
    refine iInf_le_of_le Pi <| iInf_le_of_le s <| iInf_le_of_le t <|
      iInf_le_of_le hPi' <| iInf_le_of_le ?_ <| iInf_le_of_le ?_ <| iInf_le_of_le ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      have := hPA ⟨u, hu, rfl⟩
      rw [← hPPi u] at this
      exact (hmem _).1 this
    · rw [← hsph, hPPi]; exact hs
    · rw [← hsph, hPPi]; exact ht
    · rw [len_pull D E (fun u => c + a * u) hT, hPPi']

end Affine

end SupercriticalConformalCovariance.BiLip
