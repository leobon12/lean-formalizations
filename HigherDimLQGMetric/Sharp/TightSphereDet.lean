import HigherDimLQGMetric.Sharp.SphereChainBound
import HigherDimLQGMetric.Shell.Defs
import HigherDimLQGMetric.Metric.Internal

/-!
# Deterministic confinement of short sphere steps

The sphere diameter is controlled by a Euclidean modulus on the sphere and a
positive metric gap to the boundary of the surrounding shell.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem isConnected_unit_sphere (hd : 2 ≤ d) :
    IsConnected (sphere (0 : Rd d) 1) := by
  have hrank : 1 < Module.rank ℝ (Rd d) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (show 1 < d by omega)
  exact isConnected_sphere hrank 0 (by norm_num)

/-- Short distances on the unit sphere equal their internal distances when they are smaller
than every distance to the shell frontier. The fixed chain count is supplied separately. -/
theorem sphereDiam_le_of_modulus (N : ℕ)
    {b : ℝ}
    (hN : ∀ u ∈ sphere (0 : Rd d) 1, ∀ v ∈ sphere (0 : Rd d) 1,
      ∀ (δ : Rd d → Rd d → ℝ≥0∞),
        (∀ x ∈ sphere (0 : Rd d) 1, δ x x = 0) →
        (∀ x y z, δ x z ≤ δ x y + δ y z) →
        ∀ M : ℝ≥0∞,
          (∀ x y, sharpShortStep (sphere (0 : Rd d) 1) b x y → δ x y ≤ M) →
          δ u v ≤ (N : ℝ≥0∞) * M)
    (D : ContMetric d) (hD : D.IsLength)
    {a : ℝ} (ha : 0 < a)
    (hsep : ∀ u ∈ sphere (0 : Rd d) 1,
      ∀ v ∈ frontier (ann (0 : Rd d) (1 / 2) 2), a < D.1 (u, v))
    (hmod : ∀ u ∈ sphere (0 : Rd d) 1,
      ∀ v ∈ sphere (0 : Rd d) 1, ‖u - v‖ ≤ b → D.1 (u, v) < a) :
    sphereDiam D 0 1 ≤ (N : ℝ≥0∞) * ENNReal.ofReal a := by
  let K : Set (Rd d) := sphere 0 1
  let V : Set (Rd d) := ann 0 (1 / 2) 2
  have hV : IsOpen V := isOpen_ann _ _ _
  have hKV : K ⊆ V := by
    intro u hu
    have hnorm : ‖u - (0 : Rd d)‖ = 1 := by
      change u ∈ sphere (0 : Rd d) 1 at hu
      simpa only [Metric.mem_sphere, dist_eq_norm] using hu
    show 1 / 2 < ‖u - (0 : Rd d)‖ ∧ ‖u - (0 : Rd d)‖ < 2
    rw [hnorm]
    norm_num
  unfold sphereDiam
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv => ?_
  simp only [mul_one]
  change D.internal V u v ≤ (N : ℝ≥0∞) * ENNReal.ofReal a
  refine hN u hu v hv (D.internal V) (fun x hx => D.internal_self (hKV hx))
    (D.internal_triangle V) (ENNReal.ofReal a) ?_
  intro x y hxy
  have hxV : x ∈ V := hKV hxy.1
  have hxylt : edist (D.pt x) (D.pt y) < ENNReal.ofReal a := by
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).2 (hmod x hxy.1 y hxy.2.1 hxy.2.2.le)
  have hfront : ENNReal.ofReal a ≤
      Metric.infEDist (D.pt x) (D.pt '' frontier V) := by
    apply Metric.le_infEDist.2
    rintro _ ⟨w, hw, rfl⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (hsep x hxy.1 w hw).le
  have hint := (ContMetric.internal_eq_of_lt_infEDist_frontier hD hV hxV
    (hxylt.trans_le hfront)).2
  rw [hint, edist_dist]
  exact ENNReal.ofReal_le_ofReal (hmod x hxy.1 y hxy.2.1 hxy.2.2.le).le

end HigherDimLQGMetric
