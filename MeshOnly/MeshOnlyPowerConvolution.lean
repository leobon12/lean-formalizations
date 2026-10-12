import MeshOnly.MeshOnlyPowerDifferential
import MeshOnly.MeshOnlyPowerPotential

/-! Differentiation of the actual displacement convolution and its geometric
closedness on every region where the translated kernel has no exterior flux. -/

open scoped Classical BigOperators Convolution MeasureTheory
open MeasureTheory ContinuousLinearMap

namespace BouRabeeGwynne

lemma meshOnly_bilinear_symmetric_of_coordinates {d : ℕ}
    (A : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)
    (hA : ∀ i j, A (EuclideanSpace.basisFun (Fin d) ℝ i)
      (EuclideanSpace.basisFun (Fin d) ℝ j) =
      A (EuclideanSpace.basisFun (Fin d) ℝ j) (EuclideanSpace.basisFun (Fin d) ℝ i))
    (u v : Euc d) : A u v = A v u := by
  have hexpand (u v : Euc d) :
      A u v = ∑ i : Fin d, ∑ j : Fin d,
        u i * v j * A (EuclideanSpace.basisFun (Fin d) ℝ i)
          (EuclideanSpace.basisFun (Fin d) ℝ j) := by
    have hfirst := continuousLinearMap_apply_eq_sum_coordinates
      ((ContinuousLinearMap.apply ℝ ℝ v).comp A) u
    change A u v = ∑ i : Fin d,
      u i * A (EuclideanSpace.basisFun (Fin d) ℝ i) v at hfirst
    rw [hfirst]
    have hsecond (i : Fin d) := continuousLinearMap_apply_eq_sum_coordinates
      (A (EuclideanSpace.basisFun (Fin d) ℝ i)) v
    simp only [hsecond, Finset.mul_sum, mul_assoc]
  rw [hexpand u v, hexpand v u]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hA i j]
  ring

lemma meshOnly_convolution_partial {d : ℕ} (Z : Euc d → Euc d)
    (hZ : LocallyIntegrable Z volume) (κ : Euc d → ℝ)
    (hκ : ContDiff ℝ 1 κ) (hcompact : HasCompactSupport κ)
    (x u : Euc d) (i : Fin d) :
    (fderiv ℝ (κ ⋆[lsmul ℝ ℝ, volume] Z) x u) i =
      ∫ y, (fderiv ℝ κ (x - y) u) * Z y i ∂volume := by
  let L : Euc d →L[ℝ] ℝ →L[ℝ] Euc d := (lsmul ℝ ℝ).flip
  have hD := hcompact.hasFDerivAt_convolution_right L hZ hκ x
  rw [← convolution_flip (lsmul ℝ ℝ), hD.fderiv]
  have hF := (hcompact.fderiv ℝ).convolutionExists_right (L.precompR (Euc d)) hZ
    (hκ.continuous_fderiv one_ne_zero) x
  rw [convolution_def, ContinuousLinearMap.integral_apply hF]
  let π : Euc d →L[ℝ] ℝ := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i
  let F : Euc d → Euc d := fun y =>
    ((L.precompR (Euc d)) (Z y) (fderiv ℝ κ (x - y))) u
  have hFu : Integrable F volume :=
    (ContinuousLinearMap.apply ℝ (Euc d) u).integrable_comp hF
  change π (∫ y, F y ∂volume) = _
  rw [← π.integral_comp_comm hFu]
  rfl

namespace OrthogonalTiling

theorem meshOnlyMollifiedDisplacement_coordinate_closed {n : ℕ}
    (T : OrthogonalTiling (n + 1)) (i j : Fin (n + 1))
    (R : Set T.V) [Fintype R] (φ : ContDiffBump (0 : Euc (n + 1)))
    (x : Euc (n + 1))
    (hcell : ∀ v : R, (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ y ∈ T.facet v w, φ.normed volume (x - y) = 0) :
    (fderiv ℝ (T.meshOnlyMollifiedDisplacement R φ) x (coordinateAxis i)) j =
      (fderiv ℝ (T.meshOnlyMollifiedDisplacement R φ) x (coordinateAxis j)) i := by
  have hk : ContDiff ℝ 1 (φ.normed volume) := φ.contDiff_normed
  have htrans : ContDiff ℝ 1 (fun y => φ.normed volume (x - y)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have hpartial (y : Euc (n + 1)) (a : Fin (n + 1)) :
      (fderiv ℝ (fun z => φ.normed volume (x - z)) y) (coordinateAxis a) =
        -(fderiv ℝ (φ.normed volume) (x - y)) (coordinateAxis a) := by
    have hderiv := ((hk.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    have hfd := hderiv.fderiv
    change fderiv ℝ (fun z => φ.normed volume (x - z)) y = _ at hfd
    rw [hfd]
    simp
  have hweak := T.meshOnlyDisplacementField_weak_curl i j R _ htrans hcell hcut
  simp_rw [hpartial, neg_mul, integral_neg] at hweak
  unfold meshOnlyMollifiedDisplacement
  rw [meshOnly_convolution_partial _ (T.meshOnlyDisplacementField_locallyIntegrable R)
      _ hk φ.hasCompactSupport_normed,
    meshOnly_convolution_partial _ (T.meshOnlyDisplacementField_locallyIntegrable R)
      _ hk φ.hasCompactSupport_normed]
  linarith

noncomputable def meshOnlyMollifiedPowerForm {d : ℕ} (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (φ : ContDiffBump (0 : Euc d)) :
    Euc d → Euc d →L[ℝ] ℝ :=
  fun x => innerSL ℝ (T.meshOnlyMollifiedDisplacement R φ x)

/-- Actual geometric closedness of the mollified power form. The only cutoff
hypothesis concerns the translated bump on omitted-cell contacts. -/
theorem meshOnlyMollifiedPowerForm_closed {n : ℕ}
    (T : OrthogonalTiling (n + 1))
    (R : Set T.V) [Fintype R] (φ : ContDiffBump (0 : Euc (n + 1)))
    (x : Euc (n + 1))
    (hcell : ∀ v : R, (T.cell v).carrier ⊆ interior T.domain)
    (hcut : ∀ v : R, ∀ w : T.V, w ∉ R → T.adj v w →
      ∀ y ∈ T.facet v w, φ.normed volume (x - y) = 0)
    (u v : Euc (n + 1)) :
    fderiv ℝ (T.meshOnlyMollifiedPowerForm R φ) x u v =
      fderiv ℝ (T.meshOnlyMollifiedPowerForm R φ) x v u := by
  have hZ := ((T.meshOnlyMollifiedDisplacement_contDiff R φ).differentiable (by simp)) x
  have hD := (innerSL ℝ (E := Euc (n + 1))).hasFDerivAt.comp x hZ.hasFDerivAt
  apply meshOnly_bilinear_symmetric_of_coordinates
  intro i j
  change (fderiv ℝ (fun y => innerSL ℝ (T.meshOnlyMollifiedDisplacement R φ y)) x)
      (coordinateAxis i) (coordinateAxis j) =
    (fderiv ℝ (fun y => innerSL ℝ (T.meshOnlyMollifiedDisplacement R φ y)) x)
      (coordinateAxis j) (coordinateAxis i)
  have hfd := hD.fderiv
  change fderiv ℝ (fun y => innerSL ℝ (T.meshOnlyMollifiedDisplacement R φ y)) x = _ at hfd
  simp only [hfd]
  change inner ℝ
      (fderiv ℝ (T.meshOnlyMollifiedDisplacement R φ) x (coordinateAxis i)) (coordinateAxis j) =
    inner ℝ (fderiv ℝ (T.meshOnlyMollifiedDisplacement R φ) x (coordinateAxis j)) (coordinateAxis i)
  simpa only [coordinateAxis, EuclideanSpace.inner_basisFun_real] using
    T.meshOnlyMollifiedDisplacement_coordinate_closed i j R φ x hcell hcut

theorem meshOnlyMollifiedPowerForm_differentiable {d : ℕ} (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (φ : ContDiffBump (0 : Euc d)) :
    Differentiable ℝ (T.meshOnlyMollifiedPowerForm R φ) :=
  (innerSL ℝ (E := Euc d)).differentiable.comp
    ((T.meshOnlyMollifiedDisplacement_contDiff R φ).differentiable (by simp))

theorem meshOnlyMollifiedPowerForm_norm_le {d : ℕ} (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (φ : ContDiffBump (0 : Euc d))
    (hmesh : T.mesh ≠ ⊤) (x : Euc d) :
    ‖T.meshOnlyMollifiedPowerForm R φ x‖ ≤ 2 * T.mesh.toReal := by
  change ‖innerSL ℝ (T.meshOnlyMollifiedDisplacement R φ x)‖ ≤ _
  rw [innerSL_apply_norm]
  exact T.meshOnlyMollifiedDisplacement_norm_le R φ hmesh x

/-- Every sufficiently small actual mollifier has a normalized primitive on
the inner ball, with the exact mesh Lipschitz bound, derived from the tiling. -/
theorem exists_meshOnly_mollified_primitive {n : ℕ} (T : OrthogonalTiling (n + 1))
    (z : Euc (n + 1)) (r ρ : ℝ)
    [Fintype (T.meshOnlyBallCells z r)]
    (hmesh : T.mesh ≠ ⊤)
    (hcollar : Metric.closedBall z (r + T.mesh.toReal) ⊆ interior T.domain)
    (φ : ContDiffBump (0 : Euc (n + 1))) (hφ : φ.rOut + ρ ≤ r) :
    ∃ ψ : Euc (n + 1) → ℝ, ψ z = 0 ∧
      (∀ x ∈ Metric.ball z ρ,
        HasFDerivAt ψ (T.meshOnlyMollifiedPowerForm (T.meshOnlyBallCells z r) φ x) x) ∧
      (∀ x ∈ Metric.ball z ρ, ∀ y ∈ Metric.ball z ρ,
        |ψ y - ψ x| ≤ (2 * T.mesh.toReal) * ‖y - x‖) := by
  have hcell (v : T.meshOnlyBallCells z r) :
      (T.cell v).carrier ⊆ interior T.domain :=
    (T.meshOnlyBallCells_cell_subset v.property hmesh).trans hcollar
  have hclosed (x : Euc (n + 1)) (hx : x ∈ Metric.ball z ρ) (u v : Euc (n + 1)) :=
    T.meshOnlyMollifiedPowerForm_closed (T.meshOnlyBallCells z r) φ x hcell
      (fun a w hw _ => T.meshOnlyBallCells_contact_cutoff
        (fun y => φ.normed volume (x - y)) (by
          intro y hy
          have hxy : ‖x - y‖ < φ.rOut := by
            have h := φ.support_normed_eq.subset hy
            simpa only [Metric.mem_ball, dist_zero_right] using h
          apply Metric.mem_closedBall.mpr
          calc
            dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
            _ ≤ φ.rOut + ρ := add_le_add
              (by simpa only [dist_eq_norm, norm_sub_rev] using hxy.le)
              (Metric.mem_ball.mp hx).le
            _ ≤ r := hφ) a w hw) u v
  exact meshOnly_exists_smooth_normalized_primitive Metric.isOpen_ball (convex_ball z ρ)
    (T.meshOnlyMollifiedPowerForm (T.meshOnlyBallCells z r) φ)
    (T.meshOnlyMollifiedPowerForm_differentiable _ φ).differentiableOn hclosed
    (2 * T.mesh.toReal) (fun x _ => T.meshOnlyMollifiedPowerForm_norm_le _ φ hmesh x) z

end OrthogonalTiling

end BouRabeeGwynne
