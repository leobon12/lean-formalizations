import HigherDimLQGMetric.Thm13.ConfinedLower
import HigherDimLQGMetric.Metric.WeylCompose

/-! Bounded replacements of continuous perturbations on compact balls. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Every continuous function has a globally bounded continuous replacement
which agrees with it on a prescribed compact ball. -/
theorem l8_exists_bounded_agree_ball (f : C(Rd d, ℝ)) (z : Rd d) (R : ℝ) :
    ∃ f' : C(Rd d, ℝ), (∃ M : ℝ, ∀ x, |f' x| ≤ M) ∧
      EqOn (⇑f) (⇑f') (Metric.closedBall z R) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall z R).exists_bound_of_continuousOn
    f.continuous.continuousOn
  let M : ℝ := max C 0
  let f' : C(Rd d, ℝ) :=
    ⟨fun x => max (-M) (min M (f x)), by fun_prop⟩
  refine ⟨f', ⟨M, ?_⟩, ?_⟩
  · intro x
    have hM : 0 ≤ M := le_max_right _ _
    exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · intro x hx
    have h := hC x hx
    rw [Real.norm_eq_abs, abs_le] at h
    change f x = max (-M) (min M (f x))
    rw [min_eq_right (by dsimp [M]; linarith [le_max_left C 0]),
      max_eq_right (by dsimp [M]; linarith [le_max_left C 0])]

/-- On a ball where two perturbations agree, their Weyl metrics have the
same internal distances. -/
theorem l8_weyl_internal_congr (ξ : ℝ) (D : ContMetric d) (hD : D.IsLength)
    (f f' : C(Rd d, ℝ)) {U : Set (Rd d)} (hU : IsOpen U)
    (hff' : EqOn (⇑f) (⇑f') U) (u v : Rd d) :
    (weylMetric ξ f D hD).internal U u v =
      (weylMetric ξ f' D hD).internal U u v := by
  rw [weylMetric_internal hD hU, weylMetric_internal hD hU]
  exact weylScaleOn_congr fun x hx => by rw [hff' hx]

/-- An edge whose second endpoint is outside its localization ball has
infinite cost. -/
theorem l8_localEdge_eq_top_of_far {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (u v : Rd d) (hv : v ∉ Metric.ball u 1) :
    l8_localEdge hd hκ ξ εs hεs g u v = ⊤ := by
  unfold l8_localEdge
  have htop (n : ℕ) :
      (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal (Metric.ball u 1) u v = ⊤ :=
    (l8_truncScaledMetric hd hκ ξ (hεs n) g).internal_eq_top_of_notMem_right hv
  simp only [htop, liminf_const]

/-- The local edge dominates the Weyl distance for every continuous
perturbation, using bounded perturbation limits only. -/
theorem l8_localEdge_ge_weyl_of_bounded_limits
    {κ : Rd d → ℝ} (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hB : ∀ f' : C(Rd d, ℝ), (∃ M : ℝ, ∀ x, |f' x| ≤ M) →
      Tendsto (fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')).1)
        atTop (𝓝 (weylMetric ξ f' D hD).1))
    (f : C(Rd d, ℝ)) (u v : Rd d) :
    ENNReal.ofReal ((weylMetric ξ f D hD).1 (u,v)) ≤
      l8_localEdge hd hκ ξ εs hεs (addFun g f) u v := by
  by_cases hv : v ∈ Metric.ball u 1
  · obtain ⟨f', hf'bd, hff'⟩ := l8_exists_bounded_agree_ball f u 2
    have heq : EqOn (⇑f) (⇑f') (Metric.ball u 2) :=
      hff'.mono Metric.ball_subset_closedBall
    have hlow := l8_localEdge_ge_internal_of_local_bounded_limit
      hd hκ ξ εs hεs hεt g f f' u v hv heq
      (weylMetric ξ f' D hD) (weylMetric_isLength hD) (hB f' hf'bd)
    calc
      ENNReal.ofReal ((weylMetric ξ f D hD).1 (u,v))
          ≤ (weylMetric ξ f D hD).internal (Metric.ball u 2) u v :=
        (weylMetric ξ f D hD).ofReal_le_internal (Metric.ball u 2) u v
      _ = (weylMetric ξ f' D hD).internal (Metric.ball u 2) u v :=
        l8_weyl_internal_congr ξ D hD f f' Metric.isOpen_ball heq u v
      _ ≤ l8_localEdge hd hκ ξ εs hεs (addFun g f) u v := hlow
  · rw [l8_localEdge_eq_top_of_far hd hκ ξ εs hεs (addFun g f) u v hv]
    exact le_top

end HigherDimLQGMetric
