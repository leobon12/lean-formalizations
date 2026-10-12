import MeshOnly.MeshOnlySobolevCells
import MeshOnly.MeshOnlySobolevFlux
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Mollification of the actual finite cellwise extension and its exact
derivative as a sum of contact jumps. -/

open scoped BigOperators Classical ENNReal MeasureTheory Convolution
open MeasureTheory ContinuousLinearMap

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

lemma meshOnlyCellFunction_convolution_contDiff
    (R : Set T.V) [Fintype R] (c : R → ℝ)
    (ρ : Euc (n + 1) → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcompact : HasCompactSupport ρ) :
    ContDiff ℝ 1 (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) :=
  hcompact.contDiff_convolution_right (lsmul ℝ ℝ)
    (T.meshOnlyCellFunction_integrable R c).locallyIntegrable hρ

lemma meshOnlyCellFunction_convolution_compact
    (R : Set T.V) [Fintype R] (c : R → ℝ)
    (ρ : Euc (n + 1) → ℝ) (hcompact : HasCompactSupport ρ) :
    HasCompactSupport (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) :=
  (T.meshOnlyCellFunction_hasCompactSupport R c).convolution (lsmul ℝ ℝ) hcompact

/-- Each coordinate of the derivative of the mollification is the exact
sum of the corresponding derivatives integrated over the cells. -/
theorem meshOnlyCellFunction_convolution_partial
    (i : Fin (n + 1)) (R : Set T.V) [Fintype R] (c : R → ℝ)
    (ρ : Euc (n + 1) → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcompact : HasCompactSupport ρ)
    (x : Euc (n + 1)) :
    (fderiv ℝ (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) x)
        (coordinateAxis i) =
      ∑ v : R, (∫ y in (T.cell v).carrier,
        (fderiv ℝ ρ (x - y)) (coordinateAxis i) ∂volume) * c v := by
  have hF := (T.meshOnlyCellFunction_integrable R c).locallyIntegrable
  rw [(hcompact.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hF hρ x).fderiv,
    convolution_precompR_apply (lsmul ℝ ℝ) hF (hcompact.fderiv ℝ)
      (hρ.continuous_fderiv one_ne_zero)]
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  apply T.meshOnlyCellFunction_integral_mul
  exact ((hρ.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).clm_apply
    continuous_const

/-- Integration by parts converts the derivative of a genuine mollified
cell function into facet jumps. Only neighbors of active coefficients must
belong to the finite region. -/
theorem meshOnlyCellFunction_convolution_partial_eq_jumps
    (i : Fin (n + 1)) (R : Set T.V) [Fintype R] (c : R → ℝ)
    (hcell : ∀ v : R, c v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, c v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R)
    (ρ : Euc (n + 1) → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcompact : HasCompactSupport ρ)
    (x : Euc (n + 1)) :
    (fderiv ℝ (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) x)
        (coordinateAxis i) =
      (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        T.meshOnlyCoordinateContactFlux i (fun y => ρ (x - y)) v w * (c w - c v) := by
  have htrans : ContDiff ℝ 1 (fun y => ρ (x - y)) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hpartial (y : Euc (n + 1)) :
      (fderiv ℝ (fun z => ρ (x - z)) y) (coordinateAxis i) =
        -(fderiv ℝ ρ (x - y)) (coordinateAxis i) := by
    have hderiv := ((hρ.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    have hfd := hderiv.fderiv
    change fderiv ℝ (fun z => ρ (x - z)) y = _ at hfd
    rw [hfd]
    simp
  have hIBP := T.meshOnly_sum_cell_partial_by_parts i R c
    (fun y => ρ (x - y)) htrans hcell
    (fun v hv w hw hadj => False.elim (hw (hneighbors v hv w hadj)))
  simp_rw [hpartial, integral_neg, neg_mul, Finset.sum_neg_distrib] at hIBP
  rw [T.meshOnlyCellFunction_convolution_partial i R c ρ hρ hcompact x]
  linarith

end BouRabeeGwynne.OrthogonalTiling
