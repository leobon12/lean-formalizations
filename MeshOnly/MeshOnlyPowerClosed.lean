import MeshOnly.MeshOnlySobolevFlux

/-! The genuine marked-point field is weakly curl-free. Orthogonality appears
through the already proved outward-normal flux formula. A finite test-support
cutoff avoids assumptions about graph-neighbor closure of the region. -/

open scoped Classical BigOperators ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

/-- The common affine part of the displacement has no exterior test flux. -/
lemma meshOnly_sum_cell_partial_eq_zero
    (i : Fin (n + 1)) (R : Set T.V) [Fintype R]
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcell : ∀ v : R, (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ x ∈ T.facet v w, φ x = 0) :
    (∑ v : R, ∫ x in (T.cell v).carrier,
      (fderiv ℝ φ x) (coordinateAxis i) ∂volume) = 0 := by
  have h := T.meshOnly_sum_cell_partial_by_parts i R (fun _ => 1) φ hφ
    (fun v _ => hcell v) (fun v _ => hcut v)
  simpa using h

lemma meshOnly_coordinate_product_partial (i j : Fin (n + 1))
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ) (x : Euc (n + 1)) :
    (fderiv ℝ (fun y : Euc (n + 1) => y j * φ y) x) (coordinateAxis i) =
      x j * (fderiv ℝ φ x) (coordinateAxis i) + φ x * coordinateAxis i j := by
  have h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) j).hasFDerivAt.fun_mul
    ((hφ.differentiable one_ne_zero) x).hasFDerivAt
  simpa only [PiLp.proj_apply, add_apply, smul_apply, smul_eq_mul] using
    congrArg (fun L : Euc (n + 1) →L[ℝ] ℝ => L (coordinateAxis i)) h.fderiv

lemma meshOnly_affine_field_weak_curl
    (i j : Fin (n + 1)) (R : Set T.V) [Fintype R]
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcell : ∀ v : R, (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ x ∈ T.facet v w, φ x = 0) :
    (∑ v : R, ∫ x in (T.cell v).carrier,
      x j * (fderiv ℝ φ x) (coordinateAxis i) ∂volume) =
    (∑ v : R, ∫ x in (T.cell v).carrier,
      x i * (fderiv ℝ φ x) (coordinateAxis j) ∂volume) := by
  have hpartial (a b : Fin (n + 1)) :
      (∑ v : R, ∫ x in (T.cell v).carrier,
        x b * (fderiv ℝ φ x) (coordinateAxis a) ∂volume) +
      (∑ v : R, ∫ x in (T.cell v).carrier, φ x ∂volume) * coordinateAxis a b = 0 := by
    have hprod : ContDiff ℝ 1 (fun x : Euc (n + 1) => x b * φ x) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) b).contDiff.mul hφ
    have hzero := T.meshOnly_sum_cell_partial_eq_zero a R _ hprod hcell
      (fun v w hw hadj x hx => by rw [hcut v w hw hadj x hx, mul_zero])
    have hsplit (v : R) :
        (∫ x in (T.cell v).carrier,
          (fderiv ℝ (fun y : Euc (n + 1) => y b * φ y) x) (coordinateAxis a) ∂volume) =
        (∫ x in (T.cell v).carrier,
          x b * (fderiv ℝ φ x) (coordinateAxis a) ∂volume) +
        (∫ x in (T.cell v).carrier, φ x ∂volume) * coordinateAxis a b := by
      simp_rw [meshOnly_coordinate_product_partial a b φ hφ]
      rw [integral_add, integral_mul_const]
      · exact (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) b).continuous).mul
          ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const)).continuousOn.integrableOn_compact
            (T.cell v).compact
      · exact (hφ.continuous.mul_const _).continuousOn.integrableOn_compact (T.cell v).compact
    simp_rw [hsplit] at hzero
    simpa only [Finset.sum_add_distrib, ← Finset.sum_mul] using hzero
  have haxis : coordinateAxis i j = coordinateAxis j i := by
    simp [coordinateAxis, EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]
  have hi := hpartial i j
  have hj := hpartial j i
  rw [haxis] at hi
  linarith

/-- Each contact contribution to the antisymmetric derivative vanishes. -/
lemma meshOnly_coordinate_jump_cross (i j : Fin (n + 1))
    (φ : Euc (n + 1) → ℝ) (v w : T.V) :
    T.meshOnlyCoordinateContactFlux i φ v w * (T.pos w j - T.pos v j) =
      T.meshOnlyCoordinateContactFlux j φ v w * (T.pos w i - T.pos v i) := by
  by_cases hvw : T.adj v w
  · simp only [meshOnlyCoordinateContactFlux, hvw, ite_true, integral_const_mul]
    change ((T.pos w i - T.pos v i) / ‖T.pos w - T.pos v‖ *
      (∫ x in T.facet v w, φ x ∂μHE[n])) * (T.pos w j - T.pos v j) =
      ((T.pos w j - T.pos v j) / ‖T.pos w - T.pos v‖ *
      (∫ x in T.facet v w, φ x ∂μHE[n])) * (T.pos w i - T.pos v i)
    ring
  · simp [meshOnlyCoordinateContactFlux, hvw]

/-- Distributional symmetry of the derivative of the actual cellwise marked
field, expressed against a smooth scalar test with an explicit support cutoff.
No compatible power weights are assumed. -/
theorem meshOnly_mark_field_weak_curl
    (i j : Fin (n + 1)) (R : Set T.V) [Fintype R]
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcell : ∀ v : R, (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ x ∈ T.facet v w, φ x = 0) :
    (∑ v : R, (∫ x in (T.cell v).carrier,
      (fderiv ℝ φ x) (coordinateAxis i) ∂volume) * T.pos v j) =
    (∑ v : R, (∫ x in (T.cell v).carrier,
      (fderiv ℝ φ x) (coordinateAxis j) ∂volume) * T.pos v i) := by
  rw [T.meshOnly_sum_cell_partial_by_parts i R (fun v => T.pos v j) φ hφ
    (fun v _ => hcell v) (fun v _ => hcut v),
    T.meshOnly_sum_cell_partial_by_parts j R (fun v => T.pos v i) φ hφ
    (fun v _ => hcell v) (fun v _ => hcut v)]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  exact T.meshOnly_coordinate_jump_cross i j φ v w

/-- The complete cellwise displacement, including its affine part, has zero
weak curl against every test supported away from the finite region's exterior
contacts. This is a direct geometric statement about the actual cells. -/
theorem meshOnly_displacement_weak_curl
    (i j : Fin (n + 1)) (R : Set T.V) [Fintype R]
    (φ : Euc (n + 1) → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hcell : ∀ v : R, (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ x ∈ T.facet v w, φ x = 0) :
    (∑ v : R, ∫ x in (T.cell v).carrier,
      (x j - T.pos v j) * (fderiv ℝ φ x) (coordinateAxis i) ∂volume) =
    (∑ v : R, ∫ x in (T.cell v).carrier,
      (x i - T.pos v i) * (fderiv ℝ φ x) (coordinateAxis j) ∂volume) := by
  have hsplit (a b : Fin (n + 1)) (v : R) :
      (∫ x in (T.cell v).carrier,
        (x b - T.pos v b) * (fderiv ℝ φ x) (coordinateAxis a) ∂volume) =
      (∫ x in (T.cell v).carrier,
        x b * (fderiv ℝ φ x) (coordinateAxis a) ∂volume) -
      (∫ x in (T.cell v).carrier,
        (fderiv ℝ φ x) (coordinateAxis a) ∂volume) * T.pos v b := by
    have hdcont := (hφ.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const : Continuous (fun _ : Euc (n + 1) => coordinateAxis a))
    have ha := (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => ℝ) b).continuous).mul
      hdcont).continuousOn.integrableOn_compact (μ := volume) (T.cell v).compact
    have hb := (hdcont.const_mul (T.pos v b)).continuousOn.integrableOn_compact
      (μ := volume) (T.cell v).compact
    change IntegrableOn (fun x : Euc (n + 1) =>
      x b * (fderiv ℝ φ x) (coordinateAxis a)) (T.cell v).carrier volume at ha
    simp_rw [sub_mul]
    rw [integral_sub ha hb, integral_const_mul]
    ring
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [T.meshOnly_affine_field_weak_curl i j R φ hφ hcell hcut,
    T.meshOnly_mark_field_weak_curl i j R φ hφ hcell hcut]

end BouRabeeGwynne.OrthogonalTiling
