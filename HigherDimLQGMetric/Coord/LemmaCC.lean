import HigherDimLQGMetric.Coord.WeightedLimit

/-!
# MA1 Lemma CC: curves under converging coordinates

The coordinate distances are real valued functions on a common carrier.  The carrier can be
an open set subtype `U`; the compact set `L` is a subset of that subtype.  The uniform lower
modulus is stated in its equivalent implication form, which is exactly the form used by
Arzelà–Ascoli.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

/-- MA1 A3, Lemma CC: compactness, the limiting speed bound, and lower
semicontinuity of both length and weighted length on every subinterval. -/
theorem lemmaCC
    {X : Type*} [MetricSpace X] {a b : ℝ} (hab : a ≤ b)
    {L : Set X} (hL : IsCompact L)
    (ρ : ℕ → X × X → ℝ) (ρlim : X × X → ℝ)
    (hρcont : ∀ n, ContinuousOn (ρ n) (L ×ˢ L))
    (hρlim : TendstoUniformlyOn ρ ρlim atTop (L ×ˢ L))
    (A : ℝ) (P : ℕ → Icc a b →ᵇ X)
    (hPL : ∀ n t, P n t ∈ L)
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ x ∈ L, ∀ y ∈ L, ρ n (x, y) < δ → dist x y < ε)
    (hspeed : ∀ n : ℕ, ∀ s t : Icc a b,
      ρ n (P n s, P n t) ≤ A * dist s t) :
    ∃ Q : Icc a b →ᵇ X, (∀ t, Q t ∈ L) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n t => P (φ n) t) Q atTop ∧
        (∀ s t : Icc a b, ρlim (Q s, Q t) ≤ A * dist s t) ∧
        (∀ {c d : ℝ}, a ≤ c → c ≤ d → d ≤ b →
          curveLengthWith (fun x y => ENNReal.ofReal (ρlim (x, y)))
              (Set.IccExtend hab Q) c d ≤
            liminf (fun n => curveLengthWith
              (fun x y => ENNReal.ofReal (ρ (φ n) (x, y)))
              (Set.IccExtend hab (P (φ n))) c d) atTop) ∧
        (∀ (w : X → ℝ), ContinuousOn w L →
          ∀ {c d : ℝ}, a ≤ c → c ≤ d → d ≤ b →
          weightedLengthWith (fun x y => ENNReal.ofReal (ρlim (x, y))) w
              (Set.IccExtend hab Q) c d ≤
            liminf (fun n => weightedLengthWith
              (fun x y => ENNReal.ofReal (ρ (φ n) (x, y))) w
              (Set.IccExtend hab (P (φ n))) c d) atTop) := by
  have hρc : ContinuousOn ρlim (L ×ˢ L) :=
    hρlim.continuousOn (Frequently.of_forall hρcont)
  obtain ⟨Q, hQL, φ, hφ, hlim⟩ :=
    exists_curve_subseq_of_uniform_lower_modulus hL
      (fun n x y => ρ n (x, y)) A P hPL hmod hspeed
  refine ⟨Q, hQL, φ, hφ, hlim, ?_, ?_, ?_⟩
  · exact coordinate_speed_limit ρlim ρ hρc hρlim A P Q φ hφ hPL hQL hlim hspeed
  · intro c d hac hcd hdb
    exact coordinate_curveLength_le_liminf hab hρc hρlim P Q φ hφ hPL hQL hlim
      hac hcd hdb
  · intro w hw c d hac hcd hdb
    exact coordinate_weightedLength_le_liminf hL hab hρc hρlim P Q φ hφ hPL hQL
      hlim w hw hac hcd hdb

end HigherDimLQGMetric
