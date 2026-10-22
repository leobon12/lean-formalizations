import HigherDimLQGMetric.Sec8b.Lemma85VeryGood
import HigherDimLQGMetric.Sec8.Lemma82

/-! Lemma 8.2 applied to shifted favorable sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- On one almost-sure event, all labels of a fixed shifted favorable set
are very good for the unshifted selected geodesic. -/
theorem s7b_shifted_fav_sites_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d)
    {ξ Q cs Cs q R r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hr : 0 < r) (hR : 0 < R) (hrR : 3 * r ≤ R)
    (x y : Rd d) (colour : Fin d → ℤ)
    (Z : Finset (Rd d × ℕ))
    (hZ : IsSec8LabeledSet d T.J r R x y colour Z) :
    ∀ᵐ ω ∂P,
      addFun (h ω) (F_Z T.f r Z) ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z →
      ∀ site ∈ Z, S7bVeryGood T Q q R r x y (h ω) site := by
  classical
  have hsupp : ∀ j < T.J,
      tsupport (T.f j) ⊆ ann (0 : Rd d) 1 3 :=
    fun j hj => (T.bumps j hj).2.2.1
  have hJ : ∀ site ∈ Z, site.2 < T.J := by
    intro site hsite
    obtain ⟨_, _, _, _, _, _, hj⟩ := hZ.1 site hsite
    exact hj
  have hsep : ∀ site ∈ Z, ∀ q ∈ Z, q ≠ site →
      10 * r ≤ ‖q.1 - site.1‖ := by
    intro site hsite q hq hne
    exact hZ.separated (by omega : 1 ≤ d) hr hq hsite hne
  have hmain := lemma82 P h hd hh hD hDt hsupp hr hR hrR hZ
  have hint : ∀ᵐ ω ∂P,
      ∀ site ∈ Z, ∀ u v : Rd d,
        (D (addFun (h ω) (F_Z T.f r Z))).internal
            (ball site.1 (4 * r)) u v =
          (D (addFun (h ω) (bumpAt (T.f site.2) r site.1))).internal
            (ball site.1 (4 * r)) u v := by
    apply (Filter.eventually_all_finset Z).2
    intro site hsite
    have hsiteAe := lemma82_internal P h hh hD hDt hsupp hr hsite hJ
      (hsep site hsite)
    filter_upwards [hsiteAe] with ω hω u v
    have hball : ball site.1 (4 * r) ⊆ ball site.1 (7 * r) := by
      intro w hw
      exact Metric.ball_subset_ball (by nlinarith only [hr]) hw
    exact (hω _ isOpen_ball hball u v).1
  filter_upwards [hmain, hint] with ω hω hInt hFav site hsite
  obtain ⟨hmacro, hsiteEq, _⟩ := hω
  obtain ⟨hnorm, hsingle, hconfig0⟩ := hsiteEq site hsite
  have hconfig : config (D (addFun (h ω) (F_Z T.f r Z)))
      (Dt (addFun (h ω) (F_Z T.f r Z)))
      (sNorm ξ Q (addFun (h ω) (F_Z T.f r Z)) r site.1) r site.1 =
    config (D (addFun (h ω) (bumpAt (T.f site.2) r site.1)))
      (Dt (addFun (h ω) (bumpAt (T.f site.2) r site.1)))
      (sNorm ξ Q (h ω) r site.1) r site.1 := by
    rw [hconfig0, hsingle]
  exact s7b_shifted_fav_site_very_good T (h ω) x y Z site hsite
    hFav hmacro hnorm hconfig (hInt site hsite)

end HigherDimLQGMetric
