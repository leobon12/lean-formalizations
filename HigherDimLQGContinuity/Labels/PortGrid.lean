import HigherDimLQGContinuity.Labels.OrderBasic

/-!
# Site ports on the rational lead grid

The dyadic mesh and the denominator in (O3) make both ports grid points.
-/

set_option autoImplicit false

noncomputable section

open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem sitePortDenom_delta_mul {d : ℕ} (S : SiteData d) :
    S.mesh.δm * (sitePortDenom S : ℝ) = 128 * d := by
  rw [S.mesh.δm_eq]
  unfold sitePortDenom
  push_cast
  rw [pow_add]
  have h : (1 / 2 : ℝ) ^ S.mesh.kMesh * 2 ^ S.mesh.kMesh = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((1 / 2 : ℝ) ^ S.mesh.kMesh * 2 ^ S.mesh.kMesh) *
        (128 * (d : ℝ)) := by ring
    _ = 128 * (d : ℝ) := by rw [h]; ring

/-- The integer coordinate of a left or right site port at denominator `q₀`. -/
private def portIndex {d : ℕ} (S : SiteData d) (e : S.Edge) (j : Fin 2) :
    Fin d → ℤ := fun i =>
  64 * (d : ℤ) * ((S.edgeLeft e).1 i + (S.edgeRight e).1 i) +
    (if j = 0 then -2 else 2) * ((S.edgeRight e).1 i - (S.edgeLeft e).1 i)

theorem sitePortDenom_port_coord {d : ℕ} (S : SiteData d) (hd : 1 ≤ d) (e : S.Edge)
    (j : Fin 2) (i : Fin d) :
    (sitePortDenom S : ℝ) * S.port e j i = (portIndex S e j i : ℝ) := by
  have hδ := sitePortDenom_delta_mul S
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  let a : ℝ := ((S.edgeLeft e).1 i : ℤ)
  let b : ℝ := ((S.edgeRight e).1 i : ℤ)
  have hmid : (S.edgeCenter e) i = S.mesh.δm * (a + b) / 2 := by
    simp [SiteData.edgeCenter, midpoint_eq_smul_add, SiteData.vertexPoint,
      HigherDimLQGMetric.Topology.latticePoint, a, b]
    ring
  have hunit : (S.edgeUnit e) i = b - a := by
    simp [SiteData.edgeUnit, SiteData.vertexPoint,
      HigherDimLQGMetric.Topology.latticePoint, a, b]
    field_simp [S.mesh.δm_pos.ne']
  by_cases hj : j = 0
  · have hport : S.port e j i =
        S.mesh.δm * (a + b) / 2 - S.mesh.δm / (64 * d) * (b - a) := by
      simp [SiteData.port, hj, SiteData.boxHalfSide, hmid, hunit]
    rw [hport]
    simp only [portIndex, hj, ↓reduceIte, Int.cast_add, Int.cast_sub,
      Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_neg]
    change (sitePortDenom S : ℝ) *
      (S.mesh.δm * (a + b) / 2 - S.mesh.δm / (64 * d) * (b - a)) =
        64 * d * (a + b) + -2 * (b - a)
    calc
      _ = (S.mesh.δm * (sitePortDenom S : ℝ)) *
          ((a + b) / 2 - (b - a) / (64 * d)) := by ring
      _ = (128 * d) * ((a + b) / 2 - (b - a) / (64 * d)) := by rw [hδ]
      _ = _ := by field_simp; ring
  · have hport : S.port e j i =
        S.mesh.δm * (a + b) / 2 + S.mesh.δm / (64 * d) * (b - a) := by
      simp [SiteData.port, hj, SiteData.boxHalfSide, hmid, hunit]
    rw [hport]
    simp only [portIndex, hj, ↓reduceIte, Int.cast_add, Int.cast_sub,
      Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    change (sitePortDenom S : ℝ) *
      (S.mesh.δm * (a + b) / 2 + S.mesh.δm / (64 * d) * (b - a)) =
        64 * d * (a + b) + 2 * (b - a)
    calc
      _ = (S.mesh.δm * (sitePortDenom S : ℝ)) *
          ((a + b) / 2 + (b - a) / (64 * d)) := by ring
      _ = (128 * d) * ((a + b) / 2 + (b - a) / (64 * d)) := by rw [hδ]
      _ = _ := by field_simp; ring

/-- Each site port belongs to the grid `νℤ^d` chosen in (O3). -/
theorem siteConsts_port_onGrid {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (e : S.Edge) (j : Fin 2) :
    Routing.OnGrid (siteConsts S Cnet v).ν 0 (S.port e j) := by
  let C := siteConsts S Cnet v
  let k : Fin d → ℤ := fun i => (C.Mν : ℤ) * portIndex S e j i
  refine ⟨k, fun i => ?_⟩
  have hq : 0 < (sitePortDenom S : ℝ) := by
    exact_mod_cast sitePortDenom_pos S (by omega)
  have hM : 0 < (C.Mν : ℝ) := by
    exact_mod_cast siteConsts_Mν_pos S Cnet v
  have hcoord := sitePortDenom_port_coord S (by omega) e j i
  change S.port e j i = 0 + (1 / ((sitePortDenom S : ℝ) * C.Mν)) * (k i : ℝ)
  simp only [k, Int.cast_mul, Int.cast_natCast, zero_add]
  field_simp
  nlinarith

end HigherDimLQGContinuity
