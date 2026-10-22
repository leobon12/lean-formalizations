import HigherDimLQGMetric.Thm13.UniformEdges

/-!
# Weyl identity for the measurable patch

The bounded-perturbation convergence input is exactly the samplewise
consequence of Lemma 3.6. The conclusion applies simultaneously to every
continuous perturbation, including unbounded ones.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- A common bounded replacement on a large ball gives the compact-local
short-edge upper estimate needed by the rational-chain patch. -/
theorem l8_localEdge_le_weyl_on_compact_of_bounded_limits
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hB : ∀ f' : C(Rd d, ℝ), (∃ M : ℝ, ∀ x, |f' x| ≤ M) →
      Tendsto (fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')).1)
        atTop (𝓝 (weylMetric ξ f' D hD).1))
    (f : C(Rd d, ℝ)) (R : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ∀ y ∈ Metric.closedBall (0 : Rd d) R,
        dist x y < r →
        l8_localEdge hd hκ ξ εs hεs (addFun g f) x y ≤
          edist ((weylMetric ξ f D hD).pt x) ((weylMetric ξ f D hD).pt y) := by
  let S : ℝ := max R 0 + 5
  let T : ℝ := max R 0 + 3
  obtain ⟨f', hf'bd, hff'⟩ :=
    l8_exists_bounded_agree_ball f (0 : Rd d) S
  let Df : ContMetric d := weylMetric ξ f D hD
  let Df' : ContMetric d := weylMetric ξ f' D hD
  obtain ⟨r₁, hr₁, hloc⟩ := l8_localEdge_eq_on_short_pairs
    hd hκ ξ εs hεs (addFun g f') Df' (hB f' hf'bd) R
  obtain ⟨r₂, hr₂, hstay⟩ :=
    l8_internal_eq_ambient_on_short_pairs Df (weylMetric_isLength hD) R
  let r : ℝ := min r₁ r₂
  refine ⟨r, lt_min hr₁ hr₂, ?_⟩
  intro x hx y hy hxy
  have hlocEq : EqOn (⇑f) (⇑f') (Metric.ball x 2) := by
    intro z hz
    apply hff'
    rw [Metric.mem_closedBall, dist_zero_right]
    have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall] using hx
    have hzx : dist z x < 2 := by simpa [Metric.mem_ball] using hz
    have htri := dist_triangle z x 0
    rw [dist_zero_right] at htri
    rw [dist_zero_right] at htri
    dsimp [S]
    linarith [le_max_left R 0]
  have hTEq : EqOn (⇑f) (⇑f') (Metric.ball (0 : Rd d) T) := by
    intro z hz
    apply hff'
    rw [Metric.mem_closedBall]
    have hz' : dist z (0 : Rd d) < T := by simpa [Metric.mem_ball] using hz
    dsimp [S, T]
    linarith
  have hcmp := l8_weyl_internal_congr ξ D hD f f' Metric.isOpen_ball hTEq x y
  have hxy₁ : dist x y < r₁ := hxy.trans_le (min_le_left _ _)
  have hxy₂ : dist x y < r₂ := hxy.trans_le (min_le_right _ _)
  calc
    l8_localEdge hd hκ ξ εs hεs (addFun g f) x y
        = l8_localEdge hd hκ ξ εs hεs (addFun g f') x y :=
      l8_localEdge_addFun_congr hd hκ ξ εs hεs hεt g f f' x y hlocEq
    _ = ENNReal.ofReal (Df'.1 (x,y)) := hloc x hx y hy hxy₁
    _ ≤ Df'.internal (Metric.ball (0 : Rd d) T) x y :=
      Df'.ofReal_le_internal _ x y
    _ = Df.internal (Metric.ball (0 : Rd d) T) x y := hcmp.symm
    _ = ENNReal.ofReal (Df.1 (x,y)) := hstay x hx y hy hxy₂
    _ = edist (Df.pt x) (Df.pt y) := (Df.edist_pt x y).symm

/-- A21(4): the measurable chain-infimum patch satisfies Weyl scaling
simultaneously for every continuous perturbation of one good field. -/
theorem l8_patch_addFun_eq_weyl_of_bounded_limits
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (hB : ∀ f' : C(Rd d, ℝ), (∃ M : ℝ, ∀ x, |f' x| ≤ M) →
      Tendsto (fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')).1)
        atTop (𝓝 (weylMetric ξ f' D hD).1))
    (f : C(Rd d, ℝ)) :
    l8_patch hd hκ ξ εs hεs (addFun g f) = weylMetric ξ f D hD := by
  let Df : ContMetric d := weylMetric ξ f D hD
  have hlow : ∀ u v : Rd d,
      ENNReal.ofReal (Df.1 (u,v)) ≤
        l8_localEdge hd hκ ξ εs hεs (addFun g f) u v :=
    l8_localEdge_ge_weyl_of_bounded_limits hd hκ ξ εs hεs hεt g D hD hB f
  have hupp : ∀ R : ℝ, ∃ r : ℝ, 0 < r ∧
      ∀ x ∈ Metric.closedBall (0 : Rd d) R,
      ∀ y ∈ Metric.closedBall (0 : Rd d) R,
        dist x y < r →
        l8_localEdge hd hκ ξ εs hεs (addFun g f) x y ≤
          edist (Df.pt x) (Df.pt y) :=
    l8_localEdge_le_weyl_on_compact_of_bounded_limits
      hd hκ ξ εs hεs hεt g D hD hB f
  apply l8_patch_eq_of_patchInf hd hκ ξ εs hεs (addFun g f) Df
  intro m u v
  exact le_antisymm
    (l8_patchInf_le_of_local_edges hd hκ ξ εs hεs
      (addFun g f) Df (weylMetric_isLength hD) hupp m u v)
    (l8_patchInf_lower hd hκ ξ εs hεs (addFun g f) Df hlow m u v)

end HigherDimLQGMetric
