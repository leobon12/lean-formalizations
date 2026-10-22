import HigherDimLQGMetric.Thm13.BddLimit

/-! The samplewise part of MA5 A21: Lemma 3.6 supplies one event on which
the patch has the Weyl identity for every continuous perturbation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The truncated conclusion of Lemma 3.6, stated at one sample point. -/
def L8Lemma36Event (κ : Rd d → ℝ) (ξ : ℝ) (εs : ℕ → ℝ)
    (g : DistRd d) (D : ContMetric d) : Prop :=
  ∀ (fn : ℕ → C(Rd d, ℝ)) (f : C(Rd d, ℝ)) (M : ℝ),
    (∀ n z, |fn n z| ≤ M) →
    (∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop
        (Metric.closedBall (0 : Rd d) R)) →
    ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun n (p : Rd d × Rd d) =>
          (aEps κ ξ (εs n))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs n) (addFun g (fn n))) p)
        (fun p => (weylScale ξ f D p.1 p.2).toReal)
        atTop (Metric.closedBall (0 : Rd d) R ×ˢ
          Metric.closedBall (0 : Rd d) R)

/-- Lemma 3.6 and length of the base limit imply simultaneous Weyl scaling
of the globally defined measurable patch. -/
theorem l8_patch_addFun_eq_weyl_of_lemma36_event
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0))
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (h36 : L8Lemma36Event κ ξ εs g D)
    (f : C(Rd d, ℝ)) :
    l8_patch hd hκ ξ εs hεs (addFun g f) = weylMetric ξ f D hD := by
  exact l8_patch_addFun_eq_weyl_of_bounded_limits hd hκ ξ εs hεs hεt
    g D hD (l8_bounded_limits_of_lemma36_event hd hκ ξ εs hεs g D hD h36) f

end HigherDimLQGMetric
