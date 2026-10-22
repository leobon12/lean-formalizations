import HigherDimLQGMetric.Sec8b.Sites
import HigherDimLQGMetric.Sec8b.BinIndex
import HigherDimLQGMetric.Sec9.Interfaces

/-! One sampled path point produces a correctly binned labeled trap site. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric unitInterval
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ}

/-- A point on the selected geodesic in the prescribed annular range gives
one labeled site satisfying (C2) and (C3), with its color and bin indices. -/
theorem s7b_sample_site {ξ Q cs Cs B ε R η θ : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt) (g : DistRd d)
    (hR : 0 < R) (hε : 0 < ε) (hεθ : ε < θ / 18)
    (hθ : 0 < θ) (hθη : θ ≤ η) (hθ1 : θ ≤ 1)
    (x y : Rd d) (hx : ‖x‖ < 3 * R) (hxy : η * R ≤ ‖x - y‖)
    (P : C(unitInterval, Rd d)) (t : unitInterval)
    (hpLo : θ * R / 4 ≤ ‖P t - x‖)
    (hpHi : ‖P t - x‖ ≤ θ * R / 2)
    (hcover : g ∈ sec8CoverEvent D Dt ξ Q T.J T.N ε R)
    (hbin : g ∈ sec8BinEvent d ξ Q B ε R) :
    ∃ j ∈ scaleWin ε R, ∃ k : Fin d → ℤ, ∃ label < T.J,
      ∃ i ∈ s7b_binIndices (ε ^ B) (ε ^ (-B)),
        let r := (64 : ℝ) ^ j
        let z := latPt (r / (100 * d)) k
        let q := (2 : ℝ) ^ i
        ‖P t - z‖ < r / 2 ∧ ‖z‖ < 5 * R ∧
          x ∉ closedBall z (4 * r) ∧ y ∉ closedBall z (4 * r) ∧
          config (D g) (Dt g) (sNorm ξ Q g r z) r z ∈ T.N label ∧
          q * macroS ξ Q g R ≤ sNorm ξ Q g r z ∧
          sNorm ξ Q g r z ≤ 2 * q * macroS ξ Q g R := by
  have hpMacro : P t ∈ ball (0 : Rd d) (5 * R) := by
    have htri : ‖P t‖ ≤ ‖P t - x‖ + ‖x‖ := by
      calc
        ‖P t‖ = ‖(P t - x) + x‖ := by congr 1; abel
        _ ≤ ‖P t - x‖ + ‖x‖ := norm_add_le _ _
    rw [mem_ball, dist_zero_right]
    have hθR : θ * R ≤ R := by nlinarith [hθ1, hR]
    linarith only [htri, hpHi, hx, hθR, hR]
  obtain ⟨j, hj, k, hclose, hsite⟩ := hcover (P t) hpMacro
  obtain ⟨label, hlabel, hcfg⟩ := hsite
  let r : ℝ := (64 : ℝ) ^ j
  let z : Rd d := latPt (r / (100 * d)) k
  have hrlo : ε ^ 2 * R ≤ r := hj.1
  have hrhi : r ≤ ε * R := hj.2
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hε) hR) hrlo
  have hgeom := s7b_sampled_center_bounds hR hθ hθη hθ1 hε hεθ
    hr hrhi hx (by simpa only [norm_sub_rev] using hxy)
    hpLo hpHi hclose
  obtain ⟨hzNorm, hxout, hyout⟩ := hgeom
  have hbin' := hbin r ⟨j, rfl⟩ hrlo hrhi z hzNorm
    ⟨k, s7b_latPt_coordinates r k⟩
  let S := macroS ξ Q g R
  have hS : 0 < S := by dsimp [S, macroS]; positivity
  have hs : 0 < sNorm ξ Q g r z := sNorm_pos ξ Q g hr z
  have htpos : 0 < sNorm ξ Q g r z / S := div_pos hs hS
  have hlo : 0 < ε ^ B := by positivity
  have hhi : 0 < ε ^ (-B) := by positivity
  obtain ⟨i, hi, hqpos, hqlo, hqhi⟩ :=
    s7b_exists_bin hlo hhi hbin'
  refine ⟨j, hj, k, label, hlabel, i, hi, ?_⟩
  dsimp only
  refine ⟨hclose, hzNorm, hxout, hyout, hcfg, ?_, ?_⟩
  · exact (le_div_iff₀ hS).mp hqlo |>.trans_eq (by ring)
  · have h := (div_le_iff₀ hS).mp hqhi
    nlinarith only [h]

end HigherDimLQGMetric
