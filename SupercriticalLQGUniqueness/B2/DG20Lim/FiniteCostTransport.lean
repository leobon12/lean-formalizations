import SupercriticalLQGUniqueness.B2.DG20Lim.UnitAnnulusCoords
import LQGMetric.Metric.WeylScaling

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem disconnects_image_homeomorph
    (T : ℂ ≃ₜ ℂ) {X E F : Set ℂ}
    (h : LQGMetric.Disconnects X E F) :
    LQGMetric.Disconnects (T '' X) (T '' E) (T '' F) := by
  intro x y γ hx hy
  obtain ⟨e, he, rfl⟩ := hx
  obtain ⟨f, hf, rfl⟩ := hy
  let γ' : Path e f := {
    toFun := fun t => T.symm (γ t)
    continuous_toFun := T.symm.continuous.comp γ.continuous
    source' := by simp
    target' := by simp
  }
  obtain ⟨w, ⟨t, ht⟩, hw⟩ := h e f γ' he hf
  refine ⟨T w, ?_, ⟨w, hw, rfl⟩⟩
  refine ⟨t, ?_⟩
  have hγ : γ' t = T.symm (γ t) := rfl
  rw [← ht, hγ, T.apply_symm_apply]

private theorem len_comp_homeomorph_mul
    {D M : ContMetric} {k : ℝ≥0∞} (T : ℂ ≃ₜ ℂ)
    (hmetric : ∀ x y : ℂ,
      edist (D.pt x) (D.pt y) =
        k * edist (M.pt (T x)) (M.pt (T y)))
    (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b = k * M.len (T ∘ P) a b := by
  unfold ContMetric.len LQGMetric.MetricGeometry.curveLength
  exact LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    (F := D.pt ∘ P) (G := M.pt ∘ (T ∘ P)) (c := k)
    (fun s t => hmetric (P s) (P t)) (Icc a b)

 

theorem aroundDist_comp_homeomorph_mul
    {D M : ContMetric} {k : ℝ≥0∞}
    (hk0 : k ≠ 0) (hkt : k ≠ ∞) (T : ℂ ≃ₜ ℂ)
    (hmetric : ∀ x y : ℂ,
      edist (D.pt x) (D.pt y) =
        k * edist (M.pt (T x)) (M.pt (T y)))
    (A E F : Set ℂ) :
    D.aroundDist A E F =
      k * M.aroundDist (T '' A) (T '' E) (T '' F) := by
  have hmem : ∀ (S : Set ℂ) (x : ℂ), T x ∈ T '' S ↔ x ∈ S :=
    fun S x => T.injective.mem_set_image
  have hcancel (S : Set ℂ) : T.symm '' (T '' S) = S := by
    ext z
    simp
  unfold ContMetric.aroundDist
  simp only [ENNReal.mul_iInf_of_ne hk0 hkt]
  apply le_antisymm
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun Q => le_iInf fun hab =>
      le_iInf fun hQ => le_iInf fun hQA => le_iInf fun hQD => ?_
    have hQ' : T ∘ (T.symm ∘ Q) = Q :=
      funext fun t => T.apply_symm_apply (Q t)
    have hP : ContinuousOn (T.symm ∘ Q) (Icc a b) :=
      T.symm.continuous.comp_continuousOn hQ
    have hPA : (T.symm ∘ Q) '' Icc a b ⊆ A := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := hx
      apply (hmem A _).1
      apply hQA
      exact ⟨t, ht, (T.apply_symm_apply (Q t)).symm⟩
    have hPD : LQGMetric.Disconnects ((T.symm ∘ Q) '' Icc a b) E F := by
      have hh := disconnects_image_homeomorph T.symm hQD
      rw [hcancel E, hcancel F] at hh
      simpa only [image_comp] using hh
    have hlen := len_comp_homeomorph_mul T hmetric (T.symm ∘ Q) a b
    rw [hQ'] at hlen
    exact iInf_le_of_le a
      (iInf_le_of_le b (iInf_le_of_le (T.symm ∘ Q) (iInf_le_of_le hab
        (iInf_le_of_le hP (iInf_le_of_le hPA
          (iInf_le_of_le hPD hlen.le))))))
  · refine le_iInf fun a => le_iInf fun b => le_iInf fun P => le_iInf fun hab =>
      le_iInf fun hP => le_iInf fun hPA => le_iInf fun hPD => ?_
    have hQ : ContinuousOn (T ∘ P) (Icc a b) :=
      T.continuous.comp_continuousOn hP
    have hQA : (T ∘ P) '' Icc a b ⊆ T '' A := by
      rw [image_comp]
      exact image_mono hPA
    have hQD : LQGMetric.Disconnects ((T ∘ P) '' Icc a b)
        (T '' E) (T '' F) := by
      rw [image_comp]
      exact disconnects_image_homeomorph T hPD
    exact iInf_le_of_le a
      (iInf_le_of_le b (iInf_le_of_le (T ∘ P) (iInf_le_of_le hab
        (iInf_le_of_le hQ (iInf_le_of_le hQA
          (iInf_le_of_le hQD
            (len_comp_homeomorph_mul T hmetric P a b).ge))))))

 
theorem setDist_comp_homeomorph_mul
    {D M : ContMetric} {k : ℝ≥0∞}
    (hk0 : k ≠ 0) (hkt : k ≠ ∞) (T : ℂ ≃ₜ ℂ)
    (hmetric : ∀ x y : ℂ,
      edist (D.pt x) (D.pt y) =
        k * edist (M.pt (T x)) (M.pt (T y)))
    (E F : Set ℂ) :
    LQGMetric.Blueprint.setDist D E F =
      k * LQGMetric.Blueprint.setDist M (T '' E) (T '' F) := by
  rw [LQGMetric.Blueprint.setDist, LQGMetric.Blueprint.setDist,
    LQGMetric.MetricGeometry.setEDist_eq_iInf,
    LQGMetric.MetricGeometry.setEDist_eq_iInf]
  simp only [iInf_image, hmetric]
  simp_rw [ENNReal.mul_iInf_of_ne hk0 hkt]

end SupercriticalLQGUniqueness.B2.DG20Lim
