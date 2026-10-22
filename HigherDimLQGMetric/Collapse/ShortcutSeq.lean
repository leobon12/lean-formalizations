import HigherDimLQGMetric.Collapse.Shortcut

/-! # Shortcut transfer along a convergent weighted-geodesic sequence -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- A marked arc in the limit geodesic transfers to a uniformly long shortcut
on every sufficiently late approximating weighted geodesic. The two connection
estimates are precisely the fixed-time consequences of Lemma 3.1′(b), (3). -/
theorem lemma32_shortcut_along_marked_limit {X : Type*} [MetricSpace X]
    {Y K : Set X} {E : X → X → ℝ≥0∞}
    {M c₀ c₁ a₁ T ℓ s t : ℝ} {u v : X} {σ : ℝ → X}
    (hM : 0 < M) (hc₀ : 0 ≤ c₀) (hgap₀ : c₀ < c₁) (ha₁ : 0 < a₁)
    (hEtri : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y,
      E x z ≤ E x y + E y z)
    (hEM : ∀ x ∈ Y, ∀ y ∈ Y, E x y ≤ ENNReal.ofReal M * edist x y)
    (hKY : K ⊆ Y) (hσc : ContinuousOn σ (Icc 0 1))
    (hσ0 : σ 0 = u) (hσ1 : σ 1 = v)
    (hσK : MapsTo σ (Icc 0 1) K)
    (hσlen : curveLengthWith E σ 0 1 ≤ ENNReal.ofReal c₀ * edist u v)
    (hd : a₁ ≤ dist u v) (hdu : dist u v ≤ t - s)
    (hs : 0 ≤ s) (htℓ : t ≤ ℓ) (hℓT : ℓ ≤ T)
    {lam : ℕ → ℝ} (hlam : ∀ n, 0 < lam n)
    {w : ℕ → X → ℝ} (hwK : ∀ n, ∀ z ∈ K, w n z = lam n)
    {P : ℕ → ℝ → X} {L : ℕ → ℝ}
    (hL : Tendsto L atTop (𝓝 ℓ))
    (hLT : ∀ n, L n ≤ T)
    (hparam : ∀ n a b, 0 ≤ a → a ≤ b → b ≤ L n →
      weightedLength (w n) (P n) a b = ENNReal.ofReal (lam n * (b - a)))
    (hconst : ∀ n r, L n ≤ r → r ≤ T → P n r = P n (L n))
    (hconn₀ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (ENNReal.ofReal (lam n))⁻¹ *
        weylDistOn (w n) Y (P n s) u < ENNReal.ofReal ε)
    (hconn₁ : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      (ENNReal.ofReal (lam n))⁻¹ *
        weylDistOn (w n) Y v (P n t) < ENNReal.ofReal ε) :
    ∀ᶠ n in atTop, ∃ τ : ℝ, s ≤ τ ∧ τ ≤ L n ∧ τ ≤ T ∧
      ENNReal.ofReal (lam n * (a₁ / 2)) ≤
        weightedLength (w n) (P n) s τ ∧
      ∃ S : ℝ → X, ContinuousOn S (Icc 0 1) ∧
        S 0 = P n s ∧ S 1 = P n τ ∧ MapsTo S (Icc 0 1) Y ∧
        weightedLengthWith E (w n) S 0 1 <
          ENNReal.ofReal c₁ * weightedLength (w n) (P n) s τ := by
  have hspan : a₁ ≤ t - s := hd.trans hdu
  have htime : s < ℓ := by linarith
  have hright : 0 < c₁ := lt_of_le_of_lt hc₀ hgap₀
  have hmargin : 0 < c₁ * (t - s) - c₀ * dist u v := by
    have hprod : c₀ * dist u v ≤ c₀ * (t - s) :=
      mul_le_mul_of_nonneg_left hdu hc₀
    have hstrict : c₀ * (t - s) < c₁ * (t - s) :=
      mul_lt_mul_of_pos_right hgap₀ (by linarith)
    linarith
  let ε : ℝ := (c₁ * (t - s) - c₀ * dist u v) / (4 * M)
  have hε : 0 < ε := div_pos hmargin (by positivity)
  have hgapLim : 2 * M * ε + c₀ * dist u v < c₁ * (t - s) := by
    dsimp [ε]
    field_simp
    nlinarith [hmargin]
  have hτlim : Tendsto (fun n => min t (L n)) atTop (𝓝 t) := by
    simpa [min_eq_left htℓ] using (tendsto_const_nhds.min hL :
      Tendsto (fun n => min t (L n)) atTop (𝓝 (min t ℓ)))
  have hgapT : Tendsto (fun n => c₁ * (min t (L n) - s)) atTop
      (𝓝 (c₁ * (t - s))) := by
    simpa using tendsto_const_nhds.mul (hτlim.sub tendsto_const_nhds)
  have hlarge := hτlim.eventually (eventually_gt_nhds (by linarith : s + a₁ / 2 < t))
  have hmarginEv := hgapT.eventually (eventually_gt_nhds hgapLim)
  filter_upwards [hlarge, hmarginEv, hconn₀ ε hε, hconn₁ ε hε]
    with n hnspan hngap hnconn₀ hnconn₁
  let τ := min t (L n)
  have hsτ : s ≤ τ := by dsimp [τ] at hnspan ⊢; linarith
  have hτL : τ ≤ L n := min_le_right _ _
  have hτT : τ ≤ T := hτL.trans (hLT n)
  have hτspan : a₁ / 2 ≤ τ - s := by dsimp [τ] at hnspan ⊢; linarith
  have hPt : P n τ = P n t := by
    by_cases htL : t ≤ L n
    · simp [τ, min_eq_left htL]
    · have hLt : L n ≤ t := le_of_not_ge htL
      have htT : t ≤ T := htℓ.trans hℓT
      rw [hconst n t hLt htT]
      simp [τ, min_eq_right hLt]
  have hconn₁' : (ENNReal.ofReal (lam n))⁻¹ *
      weylDistOn (w n) Y v (P n τ) < ENNReal.ofReal ε := by
    rwa [hPt]
  obtain ⟨hcost, S, hSc, hS0, hS1, hSY, hSbudget⟩ :=
    shortcut_at_marked_times hM (hlam n) hc₀ hright.le hε.le
      hEtri hEM hKY hσc hσ0 hσ1 hσK (hwK n) hσlen
      hnconn₀ hconn₁' hngap hτspan
      (hparam n s τ hs hsτ hτL)
  exact ⟨τ, hsτ, hτL, hτT, hcost, S, hSc, hS0, hS1, hSY, hSbudget⟩

end HigherDimLQGMetric
