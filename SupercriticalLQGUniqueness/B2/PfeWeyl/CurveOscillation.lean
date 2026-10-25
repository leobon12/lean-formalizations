import SupercriticalLQGUniqueness.B2.PfeWeyl.Diameter

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

private theorem curve_oscillation_of_bound (E : LSCMetric) (g : C(ℂ, ℝ))
    {K : Set ℂ} {δ θ : ℝ}
    (hmod : ∀ u ∈ K, ∀ v ∈ K,
      E (u, v) ≤ ENNReal.ofReal δ → |g u - g v| < θ)
    {P : ℝ → ℂ} {a b : ℝ}
    (_hP : E.IsCurve P a b)
    (hK : ∀ t ∈ Icc a b, P t ∈ K)
    (hlen : E.len P a b ≤ ENNReal.ofReal δ) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |g (P s) - g (P t)| < θ := by
  intro s hs t ht
  have hdist : E (P s, P t) ≤ E.len P a b :=
    eVariationOn.edist_le (E.pt ∘ P) hs ht
  exact hmod (P s) (hK s hs) (P t) (hK t ht) (hdist.trans hlen)

 

theorem eventual_short_curve_oscillation {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {K : Set ℂ} (hK : IsCompact K)
    (f : C(ℂ, ℝ)) (fn : ℕ → C(ℂ, ℝ))
    (hfn : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ x ∈ K, |fn n x - f x| < ε)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b →
        (∀ t ∈ Icc a b, P t ∈ K) →
        D.len P a b ≤ ENNReal.ofReal δ →
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          |f (P s) - f (P t)| < θ) ∧
      (∀ᶠ n in atTop, ∀ (P : ℝ → ℂ) (a b : ℝ),
        (G n).IsCurve P a b →
        (∀ t ∈ Icc a b, P t ∈ K) →
        (G n).len P a b ≤ ENNReal.ofReal δ →
        ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
          |fn n (P s) - fn n (P t)| < θ) := by
  obtain ⟨δ, hδ, hD, hGn⟩ :=
    eventual_compact_oscillation hG hK f fn hfn hθ
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro P a b hP hPK hlen
    exact curve_oscillation_of_bound D f hD hP hPK hlen
  · filter_upwards [hGn] with n hn P a b hP hPK hlen
    exact curve_oscillation_of_bound (G n) (fn n) hn hP hPK hlen

 


def LocalizedNearMinPaths (E : LSCMetric) (ξ : ℝ) (g : C(ℂ, ℝ))
    (K K' : Set ℂ) : Prop :=
  ∀ z ∈ K, ∀ w ∈ K, ∀ (P : ℝ → ℂ) (L : ℝ),
    E.IsCurve P 0 L →
    HasUnitSpeedOn (E.pt ∘ P) (Icc 0 L) →
    P 0 = z → P L = w →
    (E.len P 0 L < E (z, w) + 1 ∨
      (∫⁻ t in Icc 0 L,
        ENNReal.ofReal (Real.exp (ξ * g (P t)))) <
        weylScale ξ g E (z, w) + 1) →
    P '' Icc 0 L ⊆ K'

 
def EndpointLocalization (G : ℕ → LSCMetric) (D : LSCMetric)
    (ξ : ℝ) (fn : ℕ → C(ℂ, ℝ)) (f : C(ℂ, ℝ))
    (K K' K'' : Set ℂ) : Prop :=
  K ⊆ K' ∧ K' ⊆ K'' ∧
    LocalizedNearMinPaths D ξ f K K' ∧
    LocalizedNearMinPaths D ξ f K' K'' ∧
    (∀ᶠ n in atTop,
      LocalizedNearMinPaths (G n) ξ (fn n) K K' ∧
      LocalizedNearMinPaths (G n) ξ (fn n) K' K'')

end SupercriticalLQGUniqueness.B2.PfeWeyl
