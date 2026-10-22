import HigherDimLQGMetric.Events.ShellCoverIndex

/-!
# Locality after rounding shell centres
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt roundLat)

variable {d : ℕ}

theorem shellCover_fieldSigma0_mono {Ω : Type*} (h : Ω → DistRd d)
    {V U : Set (Rd d)} (hVU : V ⊆ U) : fieldSigma0 h V ≤ fieldSigma0 h U := by
  refine @Measurable.comap_le _ _ (fieldSigma0 h U) _ _
    (@measurable_pi_iff Ω _ _ (fieldSigma0 h U) _ _ |>.2 fun ψ => ?_)
  exact (measurable_pi_apply (⟨ψ.1, ψ.2.trans hVU⟩ :
    {φ : TestRd0 d // tsupport (φ.1 : Rd d → ℝ) ⊆ U})).comp
    (comap_measurable (fun ω (φ : {φ : TestRd0 d // tsupport (φ.1 : Rd d → ℝ) ⊆ U}) =>
      h ω φ.1.1))

theorem shellCover_ann_subset {r : ℝ} (hr : 0 < r) (x z : Rd d)
    (hxz : ‖x - z‖ ≤ r / 100) : ann z (r / 2) (5 * r) ⊆
      ann x (r / 4) (8 * r) := by
  intro y hy
  have h1 : ‖y - z‖ ≤ ‖y - x‖ + ‖x - z‖ := by
    calc ‖y - z‖ = ‖(y - x) + (x - z)‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖x - z‖ := norm_add_le _ _
  have h2 : ‖y - x‖ ≤ ‖y - z‖ + ‖x - z‖ := by
    calc ‖y - x‖ = ‖(y - z) + (z - x)‖ := by congr 1; abel
      _ ≤ ‖y - z‖ + ‖z - x‖ := norm_add_le _ _
      _ = ‖y - z‖ + ‖x - z‖ := by rw [norm_sub_rev z x]
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem shellCover_round_ann (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r)
    (x : Rd d) :
    ann (latPt (r / (100 * d)) (roundLat (r / (100 * d)) x)) (r / 2) (5 * r) ⊆
      ann x (r / 4) (8 * r) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hs : 0 < r / (100 * (d : ℝ)) := by positivity
  apply shellCover_ann_subset hr
  have h := shellCover_roundLat_dist_le_dim hd hs x
  have heq : (d : ℝ) * (r / (100 * d)) = r / 100 := by field_simp
  exact heq ▸ h

end HigherDimLQGMetric
