import SupercriticalLQGUniqueness.B2.PfeWeyl.W2Gamma
import SupercriticalLQGUniqueness.B2.PfeWeyl.CircleLiminf
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength

 










set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 
theorem exists_weyl_lscMetric {D : LSCMetric} (hDlen : D.IsLengthSpace)
    (hDforget : Continuous (euclidForget D)) (hacross : AcrossUnbounded D)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (M : ℝ) (hfM : ∀ z, |f z| ≤ M) :
    ∃ E : LSCMetric, ∀ p, E p = weylScale ξ f D p := by
  have hext := Uniqueness.Toolkit.WeylLength.weylScale_isExtMetric D ξ f hDforget
  have hlsc : LowerSemicontinuous (fun p : ℂ × ℂ => weylScale ξ f D p) := by
    rw [lowerSemicontinuous_iff_seq]
    intro u x hu
    exact weyl_gamma_liminf (G := fun _ => D) tendsto_const_nhds ξ hξ f (fun _ => f)
      (fun _ _ ε hε => Eventually.of_forall fun _ y _ => by simpa using hε) M
      (fun _ => hfM) (fun _ => hDforget) hDlen hDforget hacross hu
  exact ⟨⟨fun p => weylScale ξ f D p, hext, hlsc⟩, fun _ => rfl⟩

 

theorem weyl_tendsto_lscMetric
    {G : ℕ → LSCMetric} {D : LSCMetric} (hG : Tendsto G atTop (𝓝 D))
    (hGlen : ∀ n, (G n).IsLengthSpace)
    (hGforget : ∀ n, Continuous (euclidForget (G n)))
    (ξ : ℝ) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ K : Set ℂ, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    (M : ℝ) (hfM : ∀ z, |f z| ≤ M) (hfnM : ∀ n z, |fn n z| ≤ M)
    (hDlen : D.IsLengthSpace) (hDforget : Continuous (euclidForget D))
    (hacross : AcrossUnbounded D)
    (W : ℕ → LSCMetric)
    (hW : ∀ n x y, W n (x, y) = weylScale ξ (fn n) (G n) (x, y))
    (hWforget : ∀ n, Continuous (euclidForget (W n)))
    (hsmall : ∀ k : ℕ,
      SmallAnnulusCosts G D (Metric.closedBall 0 k) (Metric.ball 0 ((k : ℝ) + 1))) :
    ∃ E : LSCMetric, (∀ p, E p = weylScale ξ f D p) ∧ Tendsto W atTop (𝓝 E) := by
  obtain ⟨E, hE⟩ := exists_weyl_lscMetric hDlen hDforget hacross ξ hξ f M hfM
  obtain ⟨h1, h2⟩ := weyl_lsc_convergence hG hGlen hGforget ξ hξ f fn hfn M hfM hfnM
    hDlen hDforget hacross W hW hWforget hsmall
  refine ⟨E, hE, LSCMetric.tendsto_iff.2 ⟨fun p q hp => ?_, fun q => ?_⟩⟩
  · rw [hE]
    exact h1 p q hp
  · obtain ⟨p, hp, hlim⟩ := h2 q
    exact ⟨p, hp, by rw [hE]; exact hlim⟩

end SupercriticalLQGUniqueness.B2.PfeWeyl
