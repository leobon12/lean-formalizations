import HigherDimLQGMetric.Metric.Internal
import LQGMetric.Metric.InternalOps

/-!
# Length and internal distance under metric scaling

The elementary metric transformations used to read the centred normalized
observables as continuous length metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

namespace ContMetric

variable {d : ℕ}

theorem isLength_smul {C : ℝ} (hC : 0 < C) {D : ContMetric d}
    (hD : D.IsLength) : (D.smul C hC).IsLength := by
  intro x y ε hε
  let f : D.Space → (D.smul C hC).Space := fun z => z
  have hf : ∀ a b, edist (f a) (f b) = ENNReal.ofReal C * edist a b :=
    fun a b => D.edist_smul C hC a b
  have hfc : Continuous f :=
    (show LipschitzWith (Real.toNNReal C) f from fun a b => (hf a b).le).continuous
  let x' : D.Space := x
  let y' : D.Space := y
  obtain ⟨γ, hγ⟩ := hD x' y' (ε / C) (div_pos hε hC)
  refine ⟨γ.map hfc, ?_⟩
  calc
    pathLength (γ.map hfc) = ENNReal.ofReal C * pathLength γ :=
      pathLength_map_of_edist_eq hf hfc γ
    _ ≤ ENNReal.ofReal C * (edist x' y' + ENNReal.ofReal (ε / C)) := by gcongr
    _ = edist (f x') (f y') + ENNReal.ofReal ε := by
      rw [mul_add, ← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ _ hC.ne', ← hf]

theorem internal_smul {C : ℝ} (hC : 0 < C) (D : ContMetric d)
    (U : Set (Rd d)) (z w : Rd d) :
    (D.smul C hC).internal U z w = ENNReal.ofReal C * D.internal U z w := by
  have h := internalEDist_image_of_edist_eq (X := D.Space)
    (Z := (D.smul C hC).Space) (Equiv.refl (Rd d)) (c := ENNReal.ofReal C)
    (ENNReal.ofReal_pos.2 hC).ne' ENNReal.ofReal_ne_top
    (fun a b => D.edist_smul C hC a b) (D.pt '' U) z w
  unfold ContMetric.internal
  convert h using 2
  all_goals first | rfl | (ext x; exact ⟨fun hx => ⟨x, hx, rfl⟩,
    fun ⟨y, hy, hyx⟩ => hyx ▸ hy⟩)

theorem isLength_affine {r : ℝ} (hr : r ≠ 0) (a : Rd d)
    {D : ContMetric d} (hD : D.IsLength) :
    (D.affine r hr a).IsLength := by
  let f : D.Space → (D.affine r hr a).Space :=
    fun x => (D.affine r hr a).pt (r⁻¹ • (D.unpt x - a))
  have hf : ∀ x y, edist (f x) (f y) = 1 * edist x y := by
    intro x y
    rw [one_mul, edist_dist, edist_dist]
    congr 1
    show D.1 (r • (r⁻¹ • (D.unpt x - a)) + a,
      r • (r⁻¹ • (D.unpt y - a)) + a) = D.1 (D.unpt x, D.unpt y)
    simp [smul_smul, hr]
  have hfc : Continuous f :=
    (show LipschitzWith 1 f from fun x y => by rw [hf, one_mul]; simp).continuous
  intro x y ε hε
  let x' : D.Space := D.pt (r • (D.affine r hr a).unpt x + a)
  let y' : D.Space := D.pt (r • (D.affine r hr a).unpt y + a)
  have hx : f x' = x := by simp [f, x', smul_smul, hr]
  have hy : f y' = y := by simp [f, y', smul_smul, hr]
  obtain ⟨γ, hγ⟩ := hD x' y' ε hε
  rw [← hx, ← hy]
  refine ⟨γ.map hfc, ?_⟩
  rw [pathLength_map_of_edist_eq hf hfc γ, one_mul, hf, one_mul]
  exact hγ

/-- An affine change of coordinates transports the internal distance. -/
theorem internal_affine {r : ℝ} (hr : r ≠ 0) (a : Rd d)
    (D : ContMetric d) (U : Set (Rd d)) (x y : Rd d) :
    (D.affine r hr a).internal U x y =
      D.internal ((fun u => r • u + a) '' U) (r • x + a) (r • y + a) := by
  let A := D.affine r hr a
  let e : A.Space ≃ D.Space :=
    { toFun := fun x => D.pt (r • A.unpt x + a)
      invFun := fun y => A.pt (r⁻¹ • (D.unpt y - a))
      left_inv := by
        intro x
        change A.pt (r⁻¹ • (r • A.unpt x + a - a)) = x
        simp [smul_smul, hr]
      right_inv := by
        intro y
        change D.pt (r • (r⁻¹ • (D.unpt y - a)) + a) = y
        simp [smul_smul, hr] }
  have he : ∀ x y, edist (e x) (e y) = 1 * edist x y := by
    intro x y
    rw [one_mul, edist_dist, edist_dist]
    rfl
  have h := internalEDist_image_of_edist_eq (X := A.Space) (Z := D.Space)
    e (c := 1) (by norm_num) (by norm_num) he (A.pt '' U) (A.pt x) (A.pt y)
  rw [one_mul] at h
  have himage : e '' (A.pt '' U) = D.pt '' ((fun u => r • u + a) '' U) := by
    ext w
    constructor
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨r • u + a, ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨A.pt u, ⟨u, hu, rfl⟩, rfl⟩
  rw [himage] at h
  exact h.symm

end ContMetric
end HigherDimLQGMetric
