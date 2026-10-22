import HigherDimLQGContinuity.Network.BallCore
import HigherDimLQGContinuity.Network.Global

/-! # Internal diameter through the network overlap graph -/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric

namespace HigherDimLQGContinuity

theorem openBallSpecs_eq_subtype_iUnion {d : ℕ} (F : Finset (Rd d × ℝ)) :
    openBallSpecs F = ⋃ p : F, ball p.1.1 p.1.2 := by
  ext x
  simp only [openBallSpecs, mem_iUnion, Subtype.exists]

/-- The metric part of (4.7), after the finite ball containment check. -/
theorem q4_labelNet_internal_of_ball_bounds {d : ℕ}
    (S : SiteData d) (hd : 2 ≤ d) (Cnet v : ℝ)
    (hv : 0 < v) (hv1 : v ≤ 1) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (D : ContMetric d) (_hD : D.IsLength)
    {W : Set (Rd d)} {H : ℝ} (hup : DUpper D W H S.s)
    (hW : ∀ p ∈ labelBallSpecs ℓ (siteConsts S Cnet v).g
      (siteConsts S Cnet v).ω,
      closedBall p.1 p.2 ⊆ W)
    (x y : Rd d)
    (hx : x ∈ (labelNet S (siteConsts S Cnet v) ℓ).Uo)
    (hy : y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Uo) :
    let C := siteConsts S Cnet v
    let F := labelBallSpecs ℓ C.g C.ω
    D.internal (labelNet S C ℓ).Uo x y ≤
      ENNReal.ofReal ((4 / (1 - (1 / 2 : ℝ) ^ S.s)) * H *
        ∑ p : F, p.1.2 ^ S.s) := by
  let C := siteConsts S Cnet v
  let F := labelBallSpecs ℓ C.g C.ω
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega)) (pow_pos hν _)
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    positivity
  have hpos : ∀ p : F, 0 < p.1.2 := fun p =>
    labelBallSpecs_radius_pos ℓ hg hω p.1 p.2
  have hclosed : ∀ p : F, closedBall p.1.1 p.1.2 ⊆ W :=
    fun p => hW p.1 p.2
  have hconn := labelNet_overlap_connected S hd Cnet v hv hv1 ℓ hreal
  have hU : (labelNet S C ℓ).Uo = ⋃ p : F, ball p.1.1 p.1.2 :=
    openBallSpecs_eq_subtype_iUnion F
  change D.internal (labelNet S C ℓ).Uo x y ≤
    ENNReal.ofReal ((4 / (1 - (1 / 2 : ℝ) ^ S.s)) * H *
      ∑ p : F, p.1.2 ^ S.s)
  rw [hU] at hx hy ⊢
  exact q4_internal_le_fintype_balls S.s_pos D hup
    (fun p : F => p.1.1) (fun p : F => p.1.2)
    hpos hclosed hconn x y hx hy

end HigherDimLQGContinuity
