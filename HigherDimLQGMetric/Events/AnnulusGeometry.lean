import HigherDimLQGMetric.Events.RatioMeas
import HigherDimLQGMetric.Sharp.SphereChainBound
import HigherDimLQGMetric.Sharp.TightSphereDet
import HigherDimLQGMetric.Sharp.ShellScaling
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connected closed annuli in dimension at least two

This supplies the compact connected chain input for the internal-diameter
part of Lemma R.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A closed annulus of positive inner radius is connected in dimension at
least two. It is the continuous image of an interval times the unit sphere. -/
theorem isConnected_annCl (hd : 2 ≤ d) (z : Rd d) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : IsConnected (annCl z a b) := by
  let S : Set (Rd d) := sphere 0 1
  let I : Set ℝ := Icc a b
  have himage : annCl z a b =
      (fun p : ℝ × Rd d => p.1 • p.2 + z) '' (I ×ˢ S) := by
    ext x
    constructor
    · intro hx
      have hn : 0 < ‖x - z‖ := lt_of_lt_of_le ha hx.1
      let v : Rd d := ‖x - z‖⁻¹ • (x - z)
      have hv : v ∈ S := by
        rw [mem_sphere, dist_eq_norm, sub_zero]
        dsimp [v]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn]
        exact inv_mul_cancel₀ hn.ne'
      refine ⟨(‖x - z‖, v), ⟨hx, hv⟩, ?_⟩
      dsimp [v]
      simp [smul_smul, hn.ne']
    · rintro ⟨⟨t, v⟩, ⟨ht, hv⟩, rfl⟩
      have htpos : 0 < t := ha.trans_le ht.1
      have hvnorm : ‖v‖ = 1 := by
        simpa only [S, mem_sphere, dist_eq_norm, sub_zero] using hv
      change a ≤ ‖t • v + z - z‖ ∧ ‖t • v + z - z‖ ≤ b
      rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, hvnorm, mul_one]
      exact ht
  rw [himage]
  have hS : IsConnected S := isConnected_unit_sphere hd
  exact ((isConnected_Icc hab).prod hS).image _
    (by fun_prop : ContinuousOn (fun p : ℝ × Rd d => p.1 • p.2 + z) (I ×ˢ S))

/-- The buffered compact annulus used for the regular-event diameter proof. -/
theorem isCompact_bufferAnn :
    IsCompact (annCl (0 : Rd d) (7 / 8) (5 / 2)) := by
  refine isCompact_of_isClosed_isBounded (isClosed_annCl _ _ _) ?_
  apply (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : Rd d) (5 / 2))).subset
  intro x hx
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hx.2

theorem isConnected_bufferAnn (hd : 2 ≤ d) :
    IsConnected (annCl (0 : Rd d) (7 / 8) (5 / 2)) :=
  isConnected_annCl hd 0 (by norm_num) (by norm_num)

/-- The affine image of a closed annulus. -/
theorem image_annCl_affine {r : ℝ} (hr : 0 < r) (z : Rd d) (a b : ℝ) :
    (fun x : Rd d => r • x + z) '' annCl 0 a b = annCl z (r * a) (r * b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change r * a ≤ ‖r • x + z - z‖ ∧ ‖r • x + z - z‖ ≤ r * b
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact ⟨mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using hx.1) hr.le,
      mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using hx.2) hr.le⟩
  · intro hy
    refine ⟨r⁻¹ • (y - z), ?_, ?_⟩
    · change a ≤ ‖r⁻¹ • (y - z) - 0‖ ∧ ‖r⁻¹ • (y - z) - 0‖ ≤ b
      simp only [sub_zero]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      rw [show r⁻¹ * ‖y - z‖ = ‖y - z‖ / r by ring]
      exact ⟨(le_div_iff₀ hr).2 (by nlinarith [hy.1]),
        (div_le_iff₀ hr).2 (by nlinarith [hy.2])⟩
    · simp [smul_smul, hr.ne']

end HigherDimLQGMetric
