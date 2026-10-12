import MeshOnly.MeshOnlyPowerGeometry
import BouRabeeGwynne.PolytopeGaussGreen
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Exact contact flux for the corrected squared-distance potential. Existence
of compatible local weights is deliberately not asserted by these lemmas. -/

open scoped BigOperators ENNReal MeasureTheory
open MeasureTheory Laplacian InnerProductSpace

namespace BouRabeeGwynne

lemma meshOnly_hasFDerivAt_sqDist {d : ℕ} (z x : Euc d) :
    HasFDerivAt (fun y : Euc d => ‖y - z‖ ^ 2) (2 • innerSL ℝ (x - z)) x := by
  simpa using ((hasFDerivAt_id x).sub_const z).norm_sq

lemma meshOnly_fderiv_sqDist {d : ℕ} (z x : Euc d) :
    fderiv ℝ (fun y : Euc d => ‖y - z‖ ^ 2) x = 2 • innerSL ℝ (x - z) :=
  (meshOnly_hasFDerivAt_sqDist z x).fderiv

lemma meshOnly_fderiv_fderiv_sqDist {d : ℕ} (z x : Euc d) :
    fderiv ℝ (fderiv ℝ (fun y : Euc d => ‖y - z‖ ^ 2)) x =
      2 • (innerSL ℝ (E := Euc d)) := by
  have hfun : fderiv ℝ (fun y : Euc d => ‖y - z‖ ^ 2) =
      fun y => 2 • innerSL ℝ (y - z) := funext (meshOnly_fderiv_sqDist z)
  rw [hfun]
  have h := (((innerSL ℝ (E := Euc d)).hasFDerivAt).comp x
    ((hasFDerivAt_id x).sub_const z)).fun_const_smul (2 : ℕ)
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using h.fderiv

/-- Squared Euclidean distance has Laplacian 2d with the project's normalization. -/
theorem meshOnly_laplacian_sqDist {d : ℕ} (z x : Euc d) :
    Δ (fun y : Euc d => ‖y - z‖ ^ 2) x = 2 * (d : ℝ) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  simp only [iteratedFDeriv_two_apply, meshOnly_fderiv_fderiv_sqDist, two_smul,
    add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    innerSL_apply_apply]
  change (∑ i : Fin d, (inner ℝ
    (EuclideanSpace.basisFun (Fin d) ℝ i) (EuclideanSpace.basisFun (Fin d) ℝ i) +
    inner ℝ (EuclideanSpace.basisFun (Fin d) ℝ i)
      (EuclideanSpace.basisFun (Fin d) ℝ i))) = _
  simp only [real_inner_self_eq_norm_sq, OrthonormalBasis.norm_eq_one, one_pow,
    mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

namespace OrthogonalTiling

variable {d : ℕ} (T : OrthogonalTiling d)

/-- A compatible power correction makes its discrete increment equal to the
actual quadratic outward flux on each contact. -/
theorem conductance_correctedSquare_eq_surfaceFlux {v w : T.V} (hvw : T.adj v w)
    (ω : T.V → ℝ) (hω : ω w - ω v = T.powerEdgeGap v w) (z : Euc d) :
    T.conductanceReal v w *
      ((‖T.pos w - z‖ ^ 2 - ω w) - (‖T.pos v - z‖ ^ 2 - ω v)) =
        T.surfaceFlux (fun y => ‖y - z‖ ^ 2) v w := by
  let c := (‖T.pos w - z‖ ^ 2 - ω w) - (‖T.pos v - z‖ ^ 2 - ω v)
  have hpoint : ∀ y ∈ T.facet v w,
      (fderiv ℝ (fun x : Euc d => ‖x - z‖ ^ 2) y) (T.unitEdgeDirection v w) =
        c / ‖T.pos w - T.pos v‖ := by
    intro y hy
    have hc := T.correctedSquare_increment hvw ω hω z hy
    change c = _ at hc
    rw [hc, meshOnly_fderiv_sqDist]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul,
      unitEdgeDirection, inner_smul_right]
    rw [real_inner_comm (y - z) (T.pos w - T.pos v)]
    ring
  change T.conductanceReal v w * c = _
  unfold surfaceFlux
  rw [setIntegral_congr_fun (T.toTilingData.facet_compact v w).measurableSet hpoint,
    setIntegral_const]
  rw [T.conductanceReal_of_adj hvw]
  change (T.facetVolume v w).toReal / ‖T.pos w - T.pos v‖ * c =
    (T.facetVolume v w).toReal • (c / ‖T.pos w - T.pos v‖)
  simp only [smul_eq_mul]
  ring

/-- The exact unnormalized clock identity, with every neighboring contact in
the sum. This consumes compatibility with the geometry-derived edge increments;
it is not an existence theorem for the still-to-be-constructed local weights. -/
theorem discreteLaplacian_correctedSquare (hd : 1 ≤ d) (v : T.V)
    (hvD : (T.cell v).carrier ⊆ interior T.domain) (hv : (T.neighbors v).Finite)
    (ω : T.V → ℝ)
    (hω : ∀ w, T.adj v w → ω w - ω v = T.powerEdgeGap v w) (z : Euc d) :
    T.discreteLaplacian (fun u => ‖T.pos u - z‖ ^ 2 - ω u) v hv =
      2 * (d : ℝ) * (T.cell v).volume.toReal := by
  have hflux : T.discreteLaplacian (fun u => ‖T.pos u - z‖ ^ 2 - ω u) v hv =
      ∑ w ∈ T.neighborFinset v hv, T.surfaceFlux (fun y => ‖y - z‖ ^ 2) v w := by
    apply Finset.sum_congr rfl
    intro w hw
    have hadj := (T.mem_neighborFinset hv).mp hw
    exact T.conductance_correctedSquare_eq_surfaceFlux hadj ω (hω w hadj) z
  have hcont : ContDiff ℝ 2 (fun y : Euc d => ‖y - z‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  rw [hflux, T.sum_surfaceFlux_eq_integral_laplacian hd v hvD hv isOpen_univ
    (Set.subset_univ _) hcont.contDiffOn]
  simp only [meshOnly_laplacian_sqDist, setIntegral_const, smul_eq_mul]
  have hvol : (T.cell v).volume.toReal = volume.real (T.cell v).carrier := by
    simp only [ConvexPolytope.volume, Euc,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.real]
  rw [hvol]
  ring

end OrthogonalTiling

end BouRabeeGwynne
