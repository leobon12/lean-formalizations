import SupercriticalConformalCovariance.Good.CoverBridge
import SupercriticalConformalCovariance.GoodAnnulus.GeneralGFF

/-!
The probability union step in Lemma 5.1 (paper line 439). Proposition 4.3's
uniform bad-pair probability remains a separate source input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.Good

open LQGMetric (DistC)
open SupercriticalLQGUniqueness (LSCMetric)

/-- The bad regular-pair event estimated by Proposition 4.3. It omits (9),
so its complement gives the literal G5 clause. -/
def RegularBadEvent {Ω : Type} (h : Ω → DistC) (D : Ω → LSCMetric)
    (e : Ω → ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1)
    (θ : Ioi (0 : ℝ)) (η : ℝ)
    (z : ℂ) (r : Ioi (0 : ℝ)) : Set Ω :=
  {ω | ∃ c : ℝ, SupercriticalLQGUniqueness.IsCircleAverage (h ω) r z c ∧
    ∃ u v : ℂ,
    SupercriticalConformalCovariance.Regular.SourceRegularPair (D ω) z u v r a θ
      ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) ∧
    ENNReal.ofReal (1 + η) * D ω (u, v) ≤ e ω (u, v)}

/-- Pointwise event inclusion: source clauses plus no regular-pair failure
give G1–G5. The two extra restrictions in (9) are retained in G5 but are not
needed when the stronger no-failure event holds. -/
theorem sourceEvent_subset_goodEvent_union_bad
    {Ω : Type} (h : Ω → DistC) (D : DistC → LSCMetric)
    (e : Ω → ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η : ℝ)
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    h ⁻¹' SupercriticalConformalCovariance.GoodAnnulus.SourceEvent D ξ Q z r q a K θ k ⊆
      GoodEvent h (D ∘ h) e ξ Q q a K θ k η z r ∪
        RegularBadEvent h (D ∘ h) e ξ Q q a θ η z r := by
  intro ω hω
  by_cases hb : ω ∈ RegularBadEvent h (D ∘ h) e ξ Q q a θ η z r
  · exact Or.inr hb
  · left
    obtain ⟨c', hc', hsource⟩ := hω
    refine ⟨r.2, c', hc',
      SupercriticalConformalCovariance.GoodAnnulus.sourceGood_implies_literal (D (h ω))
        ξ Q z r q a K θ k c' hsource, ?_⟩
    intro u v hreg _ _
    have hnot : ¬ ENNReal.ofReal (1 + η) * D (h ω) (u, v) ≤ e ω (u, v) := by
      intro hle
      apply hb
      exact ⟨c', hc', u, v, hreg, hle⟩
    exact (lt_of_not_ge hnot).le

/-- The union bound spends delta of the source-event probability on the
Proposition 4.3 failures. No measurability of the uncountable event is needed:
Measure is used as outer measure. -/
theorem goodEvent_probability
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → DistC) (D : DistC → LSCMetric)
    (e : Ω → ℂ × ℂ → ℝ≥0∞)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (k η : ℝ)
    (z : ℂ) (r : Ioi (0 : ℝ))
    {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hsource : ENNReal.ofReal (p + δ) ≤
      P (h ⁻¹' SupercriticalConformalCovariance.GoodAnnulus.SourceEvent D ξ Q z r q a K θ k))
    (hbad : P (RegularBadEvent h (D ∘ h) e ξ Q q a θ η z r) ≤
      ENNReal.ofReal δ) :
    ENNReal.ofReal p ≤
      P (GoodEvent h (D ∘ h) e ξ Q q a K θ k η z r) := by
  let A := h ⁻¹' SupercriticalConformalCovariance.GoodAnnulus.SourceEvent D ξ Q z r q a K θ k
  let G := GoodEvent h (D ∘ h) e ξ Q q a K θ k η z r
  let B := RegularBadEvent h (D ∘ h) e ξ Q q a θ η z r
  have hsub : A ⊆ G ∪ B :=
    sourceEvent_subset_goodEvent_union_bad h D e ξ Q q a K θ k η z r
  have hle : P A ≤ P G + P B :=
    (measure_mono hsub).trans (measure_union_le G B)
  have hmain : ENNReal.ofReal (p + δ) ≤ P G + ENNReal.ofReal δ :=
    hsource.trans (hle.trans (add_le_add_right hbad _))
  rw [ENNReal.ofReal_add hp hδ] at hmain
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp
    (by simpa only [add_comm] using hmain)

/-- Lemma 5.1's compact-uniform probability claim, conditional on the
Proposition 4.3 estimate for all source-regular failures. For the transported
metric, `Root.forward_wholePlane` supplies this premise from `Root.Prop43Input`,
proved by `P43Final.prop43Input_proved` and applied via `P43Final.prop43_input_slot`.
The source parameters are chosen before η and are therefore independent of it. -/
theorem goodEvent_uniform_probability_of_prop43
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric)
    (hD : SupercriticalLQGUniqueness.IsStrongLQGMetric ξ Q D) :
    ∃ θ : Ioi (0 : ℝ), ∀ (k p : ℝ), 0 < k → 0 < p → p < 1 →
      ∃ (n : ℕ) (q : Ioo (0 : ℝ) (1 / 100))
        (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
        (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
          [IsProbabilityMeasure P] (h : Ω → DistC),
          LQGMetric.IsWholePlaneGFF h P →
          ∀ (e : Ω → ℂ × ℂ → ℝ≥0∞) (η : ℝ) (L : Set ℂ),
            0 < η → IsCompact L →
            (∃ r₀ : ℝ, 0 < r₀ ∧
              ∀ z ∈ L, ∀ r : Ioi (0 : ℝ), (r : ℝ) ≤ r₀ →
                P (RegularBadEvent h (D ∘ h) e ξ Q q a θ η z r) ≤
                  ENNReal.ofReal ((1 - p) / 2)) →
            ∃ r₀ : ℝ, 0 < r₀ ∧
              ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
                ENNReal.ofReal p ≤
                  P (GoodEvent h (D ∘ h) e ξ Q q a K θ k η z r) := by
  obtain ⟨θ, hθ⟩ :=
    SupercriticalConformalCovariance.GoodAnnulus.wholePlane_literalGood_high_probability ξ Q hQ D hD
  refine ⟨θ, ?_⟩
  intro k p hk hp0 hp1
  let δ : ℝ := (1 - p) / 2
  have hδ : 0 ≤ δ := by dsimp [δ]; linarith
  have hpplus : p + δ < 1 := by dsimp [δ]; linarith
  obtain ⟨n, q, a, K, hqd, hsource⟩ := hθ k (p + δ) hk hpplus
  refine ⟨n, q, a, K, hqd, ?_⟩
  intro Ω _ P _ h hh e η L _ _ hbad
  obtain ⟨r₀, hr₀, hbad⟩ := hbad
  refine ⟨r₀, hr₀, ?_⟩
  intro z hz r hr
  have hs := (hsource P h hh z ⟨r, hr.1⟩).2.1
  exact goodEvent_probability P h D e ξ Q q a K θ k η z ⟨r, hr.1⟩
    hp0.le hδ hs (hbad z hz ⟨r, hr.1⟩ hr.2)

end SupercriticalConformalCovariance.Good
