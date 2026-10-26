import Mathlib
import SupercriticalConformalCovariance.Regular.Measurability
import SupercriticalConformalCovariance.Recovery.Recovery
import SupercriticalLQGUniqueness.B2.Polylog.P4Transport

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness
open SupercriticalLQGUniqueness.B2.Polylog

/-- Euclidean source zoom as a homeomorphism. -/
def regularZoomHomeo (z : ℂ) {r : ℝ} (hr : 0 < r) : ℂ ≃ₜ ℂ :=
  (dilateHomeo hr).trans (Homeomorph.addRight z)

@[simp] theorem regularZoomHomeo_apply (z : ℂ) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    regularZoomHomeo z hr w = z + (r : ℂ) * w := by
  change r • w + z = _
  rw [Complex.real_smul]
  ring

theorem regularZoomHomeo_image_sphere (z x : ℂ) {r ρ : ℝ} (hr : 0 < r) :
    regularZoomHomeo z hr '' sphere x ρ =
      sphere (regularZoomHomeo z hr x) (r * ρ) := by
  calc
    regularZoomHomeo z hr '' sphere x ρ =
        (fun w => w + z) '' ((fun w => r • w) '' sphere x ρ) := by
          rw [image_image]
          rfl
    _ = sphere (r • x + z) (r * ρ) := by
      rw [image_smul_sphere hr x ρ, image_add_sphere]
    _ = sphere (regularZoomHomeo z hr x) (r * ρ) := rfl

theorem regularZoomHomeo_dist (z x y : ℂ) {r : ℝ} (hr : 0 < r) :
    dist (regularZoomHomeo z hr x) (regularZoomHomeo z hr y) = r * dist x y := by
  rw [regularZoomHomeo_apply, regularZoomHomeo_apply, dist_eq_norm, dist_eq_norm]
  have heq : z + (r : ℂ) * x - (z + (r : ℂ) * y) = (r : ℂ) * (x - y) := by ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

theorem regularZoomHomeo_image_closedAnnulus (z : ℂ) {r : ℝ} (hr : 0 < r)
    (x : ℂ) (ρ σ : ℝ) :
    regularZoomHomeo z hr '' SupercriticalConformalCovariance.Regular.closedAnnulus x ρ σ =
      SupercriticalConformalCovariance.Regular.closedAnnulus (regularZoomHomeo z hr x) (r * ρ) (r * σ) := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨h1,h2⟩
    change dist w x ≤ σ at h1
    change ¬ dist w x < ρ at h2
    have hd := regularZoomHomeo_dist z w x hr
    constructor
    · change dist (regularZoomHomeo z hr w) (regularZoomHomeo z hr x) ≤ r * σ
      rw [hd]
      exact mul_le_mul_of_nonneg_left h1 hr.le
    · change ¬ dist (regularZoomHomeo z hr w) (regularZoomHomeo z hr x) < r * ρ
      rw [hd]
      exact not_lt.mpr (mul_le_mul_of_nonneg_left (le_of_not_gt h2) hr.le)
  · intro hy
    let w := (regularZoomHomeo z hr).symm y
    have heq : regularZoomHomeo z hr w = y := (regularZoomHomeo z hr).apply_symm_apply y
    refine ⟨w, ?_, heq⟩
    rw [← heq] at hy
    rcases hy with ⟨h1,h2⟩
    have hd := regularZoomHomeo_dist z w x hr
    change dist (regularZoomHomeo z hr w) (regularZoomHomeo z hr x) ≤ r * σ at h1
    change ¬ dist (regularZoomHomeo z hr w) (regularZoomHomeo z hr x) < r * ρ at h2
    rw [hd] at h1 h2
    exact ⟨(le_of_mul_le_mul_left h1 hr), fun h => h2 (mul_lt_mul_of_pos_left h hr)⟩

/-- Affine transport of all three Euclidean annulus sets used by `aroundDist`. -/
theorem regularZoomHomeo_image_annAt (z c : ℂ) {r : ℝ} (hr : 0 < r)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) :
    let A := annAt c ρ σ hρ hρσ
    let A' := annAt (regularZoomHomeo z hr c) (r * ρ) (r * σ)
      (mul_pos hr hρ) (mul_lt_mul_of_pos_left hρσ hr)
    regularZoomHomeo z hr '' A.toSet = A'.toSet ∧
    regularZoomHomeo z hr '' A.innerBoundary = A'.innerBoundary ∧
    regularZoomHomeo z hr '' A.outerBoundary = A'.outerBoundary := by
  dsimp only
  have hd := image_dilate_annAt hr c ρ σ hρ hρσ
  have ht := image_translate_annAt z (r • c) (r * ρ) (r * σ)
    (mul_pos hr hρ) (mul_lt_mul_of_pos_left hρσ hr)
  have hcenter : regularZoomHomeo z hr c = r • c + z := rfl
  rw [hcenter]
  refine ⟨?_, ?_, ?_⟩
  · calc
      regularZoomHomeo z hr '' (annAt c ρ σ hρ hρσ).toSet =
          (Homeomorph.addRight z) '' ((dilateHomeo hr) ''
            (annAt c ρ σ hρ hρσ).toSet) := by rw [image_image]; rfl
      _ = (Homeomorph.addRight z) ''
          (annAt (r • c) (r * ρ) (r * σ)
            (mul_pos hr hρ) (mul_lt_mul_of_pos_left hρσ hr)).toSet :=
              congrArg _ hd.1
      _ = _ := ht.1
  · calc
      regularZoomHomeo z hr '' (annAt c ρ σ hρ hρσ).innerBoundary =
          (Homeomorph.addRight z) '' ((dilateHomeo hr) ''
            (annAt c ρ σ hρ hρσ).innerBoundary) := by rw [image_image]; rfl
      _ = (Homeomorph.addRight z) ''
          (annAt (r • c) (r * ρ) (r * σ)
            (mul_pos hr hρ) (mul_lt_mul_of_pos_left hρσ hr)).innerBoundary :=
              congrArg _ hd.2.1
      _ = _ := ht.2.1
  · calc
      regularZoomHomeo z hr '' (annAt c ρ σ hρ hρσ).outerBoundary =
          (Homeomorph.addRight z) '' ((dilateHomeo hr) ''
            (annAt c ρ σ hρ hρσ).outerBoundary) := by rw [image_image]; rfl
      _ = (Homeomorph.addRight z) ''
          (annAt (r • c) (r * ρ) (r * σ)
            (mul_pos hr hρ) (mul_lt_mul_of_pos_left hρσ hr)).outerBoundary :=
              congrArg _ hd.2.2
      _ = _ := ht.2.2

/-- The ambient point-to-sphere cost transports under a scaled metric and
an arbitrary homeomorphism carrying the tested sphere onto its image. -/
theorem pointSphereDist_comp_mul
    {m M : LSCMetric} {k : ℝ≥0∞} (T : ℂ ≃ₜ ℂ)
    (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hm : ∀ x y, m (x,y) = k * M (T x,T y))
    (x : ℂ) (ρ σ : ℝ)
    (hsphere : T '' sphere x ρ = sphere (T x) σ) :
    TwoScale.S36Events.pointSphereDist m x ρ =
      k * TwoScale.S36Events.pointSphereDist M (T x) σ := by
  simp only [TwoScale.S36Events.pointSphereDist,
    TwoScale.S36Events.spherePairInf, sphere_zero, iInf_singleton]
  simp only [hm, ENNReal.mul_iInf_of_ne hk0 hkt]
  apply le_antisymm
  · refine le_iInf fun y => le_iInf fun hy => ?_
    obtain ⟨a,ha,heq⟩ : y ∈ T '' sphere x ρ := by rw [hsphere]; exact hy
    subst y
    exact iInf₂_le a ha
  · refine le_iInf fun a => le_iInf fun ha => ?_
    have ha' : T a ∈ sphere (T x) σ := by rw [← hsphere]; exact ⟨a,ha,rfl⟩
    exact iInf₂_le (T a) ha'

/-- The exact dyadic loop cost is covariant under the affine zoom. -/
theorem aroundRat_regularZoomHomeo
    {m M : LSCMetric} {k : ℝ≥0∞} (z x : ℂ) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hm : ∀ a b, m (a,b) = k * M (regularZoomHomeo z hr a,
      regularZoomHomeo z hr b)) :
    TwoScale.Consolidated.aroundRat (m, (x, δ, Real.sqrt δ)) =
      k * TwoScale.Consolidated.aroundRat
        (M, (regularZoomHomeo z hr x, r * δ, r * Real.sqrt δ)) := by
  let A := SupercriticalConformalCovariance.Recovery.shortAnnulus x δ hδ hδ1
  let A' := annAt (regularZoomHomeo z hr x) (r * δ) (r * Real.sqrt δ)
    (mul_pos hr hδ) (mul_lt_mul_of_pos_left A.2.2 hr)
  have hA : A = annAt x δ (Real.sqrt δ) hδ A.2.2 := Subtype.ext rfl
  have hg := regularZoomHomeo_image_annAt z x hr δ (Real.sqrt δ) hδ A.2.2
  have hcost := aroundDist_comp_mul hk0 hkt (regularZoomHomeo z hr) hm
    (annAt x δ (Real.sqrt δ) hδ A.2.2) A' hg.1 hg.2.1 hg.2.2
  rw [← hA] at hcost
  have hleft := TwoScale.Consolidated.aroundDist_eq_aroundRat m A
  have hright := TwoScale.Consolidated.aroundDist_eq_aroundRat M A'
  rw [hleft, hright] at hcost
  exact hcost

/-- A regular pair at physical scale `r` becomes a regular pair at unit scale
for the affinely rescaled metric. All dyadic tests and the geodesic are carried. -/
theorem sourceRegularPair_regularZoomHomeo
    {m M : LSCMetric} (z u v : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hm : ∀ a b, m (a,b) = ENNReal.ofReal s *
      M (regularZoomHomeo z hr a,regularZoomHomeo z hr b))
    (α θ normalizer : ℝ) (hα0 : (3 / 4 : ℝ) < α) (hα : α < 1)
    (hreg : SupercriticalConformalCovariance.Regular.SourceRegularPair M z u v r α θ normalizer) :
    SupercriticalConformalCovariance.Regular.SourceRegularPair m 0
      ((regularZoomHomeo z hr).symm u)
      ((regularZoomHomeo z hr).symm v) 1 α θ (s * normalizer) := by
  let T := regularZoomHomeo z hr
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hst : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hMuv : m (T.symm u,T.symm v) = ENNReal.ofReal s * M (u,v) := by
    rw [hm, T.apply_symm_apply, T.apply_symm_apply]
  have hann : T '' SupercriticalConformalCovariance.Regular.closedAnnulus 0 α 1 =
      SupercriticalConformalCovariance.Regular.closedAnnulus z (α * r) r := by
    change regularZoomHomeo z hr '' SupercriticalConformalCovariance.Regular.closedAnnulus 0 α 1 = _
    simpa only [regularZoomHomeo_apply, mul_zero, add_zero, mul_one, mul_comm]
      using regularZoomHomeo_image_closedAnnulus z hr 0 α 1
  have hspα : T '' sphere 0 α = sphere z (α * r) := by
    change regularZoomHomeo z hr '' sphere 0 α = _
    simpa only [regularZoomHomeo_apply, mul_zero, add_zero, mul_comm]
      using regularZoomHomeo_image_sphere z 0 (hr := hr) (ρ := α)
  have hsp1 : T '' sphere 0 1 = sphere z r := by
    change regularZoomHomeo z hr '' sphere 0 1 = _
    simpa only [regularZoomHomeo_apply, mul_zero, add_zero, mul_one]
      using regularZoomHomeo_image_sphere z 0 (hr := hr) (ρ := 1)
  rcases hreg with ⟨⟨P,a,b,hgeo,htrace⟩,hu,hv,h7,h8u,h8v⟩
  have hgeo' : OptimalConstants.Ratios.Geodesic m (T.symm ∘ P) a b
      (T.symm u) (T.symm v) := by
    rcases hgeo with ⟨hcurve,hPa,hPb,hlen,hfin⟩
    have hP : (T ∘ (T.symm ∘ P)) = P := funext fun t => T.apply_symm_apply (P t)
    refine ⟨?_, by simp [Function.comp_apply, hPa], by simp [Function.comp_apply, hPb], ?_, ?_⟩
    · exact (isCurve_comp_mul_iff hs0 hst hm (T.symm ∘ P) a b).2 (by rwa [hP])
    · rw [len_comp_mul hm, hP, hMuv, hlen]
    · rw [hMuv]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have htrace' : (T.symm ∘ P) '' Icc a b ⊆ SupercriticalConformalCovariance.Regular.closedAnnulus 0 α 1 := by
    rintro w ⟨t,ht,rfl⟩
    have htold : P t ∈ SupercriticalConformalCovariance.Regular.closedAnnulus z (α * r) r :=
      htrace ⟨t,ht,rfl⟩
    have htimg : P t ∈ T '' SupercriticalConformalCovariance.Regular.closedAnnulus 0 α 1 := by rwa [hann]
    exact (T.injective.mem_set_image).mp (by simpa only [Function.comp_apply,
      T.apply_symm_apply] using htimg)
  have hu' : T.symm u ∈ sphere 0 (α * 1) := by
    have huimg : u ∈ T '' sphere 0 α := by rwa [hspα]
    simpa only [mul_one] using (T.injective.mem_set_image).mp
      (show T (T.symm u) ∈ T '' sphere 0 α by simpa using huimg)
  have hv' : T.symm v ∈ sphere 0 (1 : ℝ) := by
    have hvimg : v ∈ T '' sphere 0 1 := by rwa [hsp1]
    exact (T.injective.mem_set_image).mp
      (show T (T.symm v) ∈ T '' sphere 0 1 by simpa using hvimg)
  refine ⟨⟨T.symm ∘ P,a,b,hgeo',by simpa only [mul_one] using htrace'⟩,hu',hv',?_,?_,?_⟩
  · rw [hMuv]
    calc
      ENNReal.ofReal s * M (u,v) ≤
          ENNReal.ofReal s * ENNReal.ofReal ((1 - α)⁻¹ * normalizer) :=
            by gcongr
      _ = ENNReal.ofReal ((1 - α)⁻¹ * (s * normalizer)) := by
        rw [← ENNReal.ofReal_mul hs.le]
        congr 1
        ring
  · intro j hj hjα
    obtain ⟨hp,hl⟩ := h8u j hj hjα
    have hδ1 : SupercriticalConformalCovariance.Regular.dyadic j < 1 := by
      have hsq : (1 - α)^2 < 1 := by nlinarith [sq_nonneg α]
      exact hjα.trans_lt hsq
    have hsp : T '' sphere (T.symm u) (SupercriticalConformalCovariance.Regular.dyadic j) =
        sphere (T (T.symm u)) (SupercriticalConformalCovariance.Regular.dyadic j * r) := by
      have hh := regularZoomHomeo_image_sphere z (T.symm u) (hr := hr)
        (ρ := SupercriticalConformalCovariance.Regular.dyadic j)
      simpa only [mul_comm] using hh
    have hpoint := pointSphereDist_comp_mul T hs0 hst hm (T.symm u)
      (SupercriticalConformalCovariance.Regular.dyadic j) (SupercriticalConformalCovariance.Regular.dyadic j * r)
      hsp
    rw [T.apply_symm_apply] at hpoint
    have hloop := aroundRat_regularZoomHomeo z (T.symm u) hr hj hδ1 hs0 hst hm
    change TwoScale.Consolidated.aroundRat
      (m,(T.symm u,SupercriticalConformalCovariance.Regular.dyadic j,Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j))) =
      ENNReal.ofReal s * TwoScale.Consolidated.aroundRat
        (M,(T (T.symm u),r * SupercriticalConformalCovariance.Regular.dyadic j,
          r * Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j))) at hloop
    rw [T.apply_symm_apply] at hloop
    constructor
    · simpa only [mul_one] using (calc
        TwoScale.S36Events.pointSphereDist m (T.symm u) (SupercriticalConformalCovariance.Regular.dyadic j) =
            ENNReal.ofReal s * TwoScale.S36Events.pointSphereDist M u
              (SupercriticalConformalCovariance.Regular.dyadic j * r) := hpoint
        _ ≤ ENNReal.ofReal s *
            (ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * M (u,v)) := by gcongr
        _ = ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * m (T.symm u,T.symm v) := by
          rw [hMuv]
          ac_rfl)

    · simpa only [mul_one] using (calc
        TwoScale.Consolidated.aroundRat
          (m,(T.symm u,SupercriticalConformalCovariance.Regular.dyadic j,Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j))) =
            ENNReal.ofReal s * TwoScale.Consolidated.aroundRat
              (M,(u,SupercriticalConformalCovariance.Regular.dyadic j * r,
                Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j) * r)) := by
                  simpa only [mul_comm] using hloop
        _ ≤ ENNReal.ofReal s *
            (ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * M (u,v)) := by gcongr
        _ = ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * m (T.symm u,T.symm v) := by
          rw [hMuv]
          ac_rfl)
  · intro j hj hjα
    obtain ⟨hp,hl⟩ := h8v j hj hjα
    have hδ1 : SupercriticalConformalCovariance.Regular.dyadic j < 1 := by
      have hsq : (1 - α)^2 < 1 := by nlinarith [sq_nonneg α]
      exact hjα.trans_lt hsq
    have hsp : T '' sphere (T.symm v) (SupercriticalConformalCovariance.Regular.dyadic j) =
        sphere (T (T.symm v)) (SupercriticalConformalCovariance.Regular.dyadic j * r) := by
      have hh := regularZoomHomeo_image_sphere z (T.symm v) (hr := hr)
        (ρ := SupercriticalConformalCovariance.Regular.dyadic j)
      simpa only [mul_comm] using hh
    have hpoint := pointSphereDist_comp_mul T hs0 hst hm (T.symm v)
      (SupercriticalConformalCovariance.Regular.dyadic j) (SupercriticalConformalCovariance.Regular.dyadic j * r)
      hsp
    rw [T.apply_symm_apply] at hpoint
    have hloop := aroundRat_regularZoomHomeo z (T.symm v) hr hj hδ1 hs0 hst hm
    change TwoScale.Consolidated.aroundRat
      (m,(T.symm v,SupercriticalConformalCovariance.Regular.dyadic j,Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j))) =
      ENNReal.ofReal s * TwoScale.Consolidated.aroundRat
        (M,(T (T.symm v),r * SupercriticalConformalCovariance.Regular.dyadic j,
          r * Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j))) at hloop
    rw [T.apply_symm_apply] at hloop
    constructor
    · simpa only [mul_one] using (calc
        TwoScale.S36Events.pointSphereDist m (T.symm v) (SupercriticalConformalCovariance.Regular.dyadic j) =
            ENNReal.ofReal s * TwoScale.S36Events.pointSphereDist M v
              (SupercriticalConformalCovariance.Regular.dyadic j * r) := hpoint
        _ ≤ ENNReal.ofReal s *
            (ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * M (u,v)) := by gcongr
        _ = ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * m (T.symm u,T.symm v) := by
          rw [hMuv]
          ac_rfl)
    · simpa only [mul_one] using (calc
        TwoScale.Consolidated.aroundRat
          (m,(T.symm v,SupercriticalConformalCovariance.Regular.dyadic j,Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j))) =
            ENNReal.ofReal s * TwoScale.Consolidated.aroundRat
              (M,(v,SupercriticalConformalCovariance.Regular.dyadic j * r,
                Real.sqrt (SupercriticalConformalCovariance.Regular.dyadic j) * r)) := by
                  simpa only [mul_comm] using hloop
        _ ≤ ENNReal.ofReal s *
            (ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * M (u,v)) := by gcongr
        _ = ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j)^θ) * m (T.symm u,T.symm v) := by
          rw [hMuv]
          ac_rfl)

/-- The physical circle-average normalization becomes the exponential of
the circle-minus-smooth-average gap after zooming. -/
theorem regularZoom_normalizer (ξ Q r circle smooth : ℝ) (hr : 0 < r) :
    (r ^ (-(ξ * Q)) * Real.exp (-(ξ * smooth))) *
      (r ^ (ξ * Q) * Real.exp (ξ * circle)) =
      Real.exp (ξ * (circle - smooth)) := by
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr]
  simp only [← Real.exp_add]
  congr 1
  ring

end SupercriticalConformalCovariance.Small
