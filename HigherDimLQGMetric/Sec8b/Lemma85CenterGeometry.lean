import HigherDimLQGMetric.Sec8b.Lemma85OneWindow

/-! Separation of all candidate centres in one lattice colour. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ}

theorem s7b_good_centers_sep (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r) (colour : Fin d → ℤ)
    (good : Finset (Rd d × ℕ))
    (hgeom : ∀ site ∈ good, ∃ index : Fin d → ℤ,
      site.1 = latPt (r / (100 * d)) index ∧
        sec8Color d index = colour)
    {z z' : Rd d}
    (hz : z ∈ good.image Prod.fst)
    (hz' : z' ∈ good.image Prod.fst)
    (hne : z ≠ z') :
    10 * r ≤ ‖z - z'‖ := by
  obtain ⟨site, hsite, hsz⟩ := Finset.mem_image.mp hz
  obtain ⟨site', hsite', hsz'⟩ := Finset.mem_image.mp hz'
  obtain ⟨i, hi, hci⟩ := hgeom site hsite
  obtain ⟨i', hi', hci'⟩ := hgeom site' hsite'
  have hii : i ≠ i' := by
    intro heq
    apply hne
    rw [← hsz, ← hsz', hi, hi', heq]
  have hdist := sec8_sameColor_dist hd hr hii (hci.trans hci'.symm)
  simpa only [← hsz, ← hsz', hi, hi'] using hdist

theorem s7b_good_centers_balls_disjoint (hd : 1 ≤ d)
    {r : ℝ} (hr : 0 < r) (colour : Fin d → ℤ)
    (good : Finset (Rd d × ℕ))
    (hgeom : ∀ site ∈ good, ∃ index : Fin d → ℤ,
      site.1 = latPt (r / (100 * d)) index ∧
        sec8Color d index = colour) :
    ((good.image Prod.fst : Finset (Rd d)) : Set (Rd d)).Pairwise
      (fun z z' => Disjoint (ball z (4 * r)) (ball z' (4 * r))) := by
  intro z hz z' hz' hne
  apply Metric.ball_disjoint_ball
  have hdist := s7b_good_centers_sep hd hr colour good hgeom hz hz' hne
  rw [dist_eq_norm]
  nlinarith only [hdist, hr]

end HigherDimLQGMetric
