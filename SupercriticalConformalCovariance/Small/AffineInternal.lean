import SupercriticalConformalCovariance.Small.RescaleSource
import LQGMetric.Metric.InternalOps

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open LQGMetric.MetricGeometry
open LQGMetric

/-- The source zoom `w ↦ z + r w`, as a bijection of the plane. -/
def zoomEquiv (z : ℂ) {r : ℝ} (hr : r ≠ 0) : ℂ ≃ ℂ where
  toFun w := z + (r : ℂ) * w
  invFun x := (x - z) / r
  left_inv w := by
    change ((z + (r : ℂ) * w - z) / r) = w
    rw [add_sub_cancel_left]
    exact mul_div_cancel_left₀ w (Complex.ofReal_ne_zero.mpr hr)
  right_inv x := by
    change z + (r : ℂ) * ((x - z) / r) = x
    rw [mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr)]
    simpa only [add_comm] using sub_add_cancel x z

/-- A similarity of global lower-semicontinuous metrics transports all internal
distances, including distances confined to a closed disk. -/
theorem internal_image_of_scaled_equiv
    {D E : LSCMetric} (F : ℂ ≃ ℂ) {s : ℝ≥0∞}
    (hs0 : s ≠ 0) (hst : s ≠ ⊤)
    (hDE : ∀ x y : ℂ, E (F x, F y) = s * D (x,y))
    (A : Set ℂ) (x y : A) :
    E.internal (F '' A)
      (⟨F x, ⟨x.1,x.2,rfl⟩⟩, ⟨F y, ⟨y.1,y.2,rfl⟩⟩) =
      s * D.internal A (x,y) := by
  let e : D.Space ≃ E.Space :=
    { toFun := fun p => F p
      invFun := fun p => F.symm p
      left_inv := by intro p; exact F.symm_apply_apply p
      right_inv := by intro p; exact F.apply_symm_apply p }
  have he : ∀ a b : D.Space, edist (e a) (e b) = s * edist a b := by
    intro a b
    change E (F a,F b) = s * D (a,b)
    exact hDE a b
  have hi := internalEDist_image_of_edist_eq
    (X := D.Space) (Z := E.Space) e hs0 hst he
    (D.pt '' A) (D.pt x) (D.pt y)
  rw [D.internal_eq_internalEDist, E.internal_eq_internalEDist]
  have hset : e '' (D.pt '' A) = E.pt '' (F '' A) := by
    ext w
    constructor
    · rintro ⟨v, ⟨q,hq,rfl⟩, rfl⟩
      exact ⟨F q, ⟨q,hq,rfl⟩,rfl⟩
    · rintro ⟨v, ⟨q,hq,rfl⟩,rfl⟩
      exact ⟨D.pt q, ⟨q,hq,rfl⟩,rfl⟩
  have hx : e (D.pt x) = E.pt (F x) := rfl
  have hy : e (D.pt y) = E.pt (F y) := rfl
  rw [hset,hx,hy] at hi
  exact hi

/-- The normalized whole-plane identity induces the same identity for every
internal metric. The target carrier is the inverse image of the source domain. -/
theorem internal_of_rescaled_pointwise
    {Dorig Dzoom : LSCMetric} (F : ℂ ≃ ℂ) {s : ℝ≥0∞}
    (hs0 : s ≠ 0) (hst : s ≠ ⊤)
    (h : ∀ u v : ℂ, Dzoom (u,v) = s * Dorig (F u,F v))
    (A : Set ℂ) (x y : A) :
    Dzoom.internal (F.symm '' A)
      (⟨F.symm x, ⟨x.1,x.2,rfl⟩⟩,
       ⟨F.symm y, ⟨y.1,y.2,rfl⟩⟩) =
      s * Dorig.internal A (x,y) := by
  apply internal_image_of_scaled_equiv F.symm hs0 hst
  intro a b
  simpa only [F.apply_symm_apply] using h (F.symm a) (F.symm b)

/-- Affine covariance and smooth-average Weyl normalization for the internal
metric of any domain, on one simultaneous conull event. -/
theorem ae_rescaled_source_internal
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusCont h P)
    (r : Set.Ioi (0 : ℝ)) (z : ℂ) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (x y : A),
      (D (addConst (affineComp (r : ℝ) z (h ω)) (-c ω))).internal
        ((zoomEquiv z r.2.ne').symm '' A)
        (⟨(zoomEquiv z r.2.ne').symm x, ⟨x.1,x.2,rfl⟩⟩,
         ⟨(zoomEquiv z r.2.ne').symm y, ⟨y.1,y.2,rfl⟩⟩) =
      ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * c ω))) *
        (D (h ω)).internal A (x,y) := by
  filter_upwards [ae_rescaled_source_metric hD P h hh r z c] with ω hω
  intro A x y
  let s : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * c ω)))
  have hspos : 0 < (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * c ω)) :=
    mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hs0 : s ≠ 0 := (ENNReal.ofReal_pos.mpr hspos).ne'
  have hst : s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp : ∀ u v : ℂ,
      D (addConst (affineComp (r : ℝ) z (h ω)) (-c ω)) (u,v) =
        s * D (h ω) ((zoomEquiv z r.2.ne') u, (zoomEquiv z r.2.ne') v) := by
    intro u v
    exact hω u v
  exact internal_of_rescaled_pointwise (zoomEquiv z r.2.ne') hs0 hst hp A x y

end SupercriticalConformalCovariance.Small
