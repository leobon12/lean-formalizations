import HigherDimLQGMetric.Sec8.Const

/-! Single-site reduction of a shifted favorable event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The three properties of a label used in the counting proof of Lemma 8.5. -/
def S7bVeryGood {ξ cs Cs : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (Q q R r : ℝ) (x y : Rd d) (g : DistRd d)
    (site : Rd d × ℕ) : Prop :=
  let one := addFun g (bumpAt (T.f site.2) r site.1)
  config (D one) (Dt one) (sNorm ξ Q g r site.1) r site.1 ∈ T.N site.2 ∧
    q * macroS ξ Q g R ≤ sNorm ξ Q g r site.1 ∧
    sNorm ξ Q g r site.1 ≤ 2 * q * macroS ξ Q g R ∧
    Exc (sec8Sel x y (D g).1) (D one)
      (sec8Collector T.V r site.1) site.1 r
      (T.b * sNorm ξ Q g r site.1)

theorem s7b_Exc_congr (η : C(unitInterval, Rd d))
    (D E : ContMetric d) (V : Set (Rd d)) (z : Rd d)
    (r θ : ℝ)
    (hInt : ∀ u v : Rd d,
      D.internal (ball z (4 * r)) u v =
        E.internal (ball z (4 * r)) u v) :
    Exc η D V z r θ ↔ Exc η E V z r θ := by
  unfold Exc
  simp only [hInt]

/-- Lemma 8.2 turns a shifted favorable set into very-good labels for the
unshifted selected geodesic. The three equalities are exactly its normalizer,
local-configuration, and local-internal-metric conclusions. -/
theorem s7b_shifted_fav_site_very_good {ξ Q cs Cs q R r : ℝ}
    {D Dt : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (g : DistRd d) (x y : Rd d)
    (Z : Finset (Rd d × ℕ)) (site : Rd d × ℕ)
    (hsite : site ∈ Z)
    (hFav : addFun g (F_Z T.f r Z) ∈
      FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z)
    (hmacro : macroS ξ Q (addFun g (F_Z T.f r Z)) R = macroS ξ Q g R)
    (hnorm : sNorm ξ Q (addFun g (F_Z T.f r Z)) r site.1 =
      sNorm ξ Q g r site.1)
    (hconfig : config (D (addFun g (F_Z T.f r Z)))
        (Dt (addFun g (F_Z T.f r Z)))
        (sNorm ξ Q (addFun g (F_Z T.f r Z)) r site.1) r site.1 =
      config (D (addFun g (bumpAt (T.f site.2) r site.1)))
        (Dt (addFun g (bumpAt (T.f site.2) r site.1)))
        (sNorm ξ Q g r site.1) r site.1)
    (hInt : ∀ u v : Rd d,
      (D (addFun g (F_Z T.f r Z))).internal (ball site.1 (4 * r)) u v =
        (D (addFun g (bumpAt (T.f site.2) r site.1))).internal
          (ball site.1 (4 * r)) u v) :
    S7bVeryGood T Q q R r x y g site := by
  rcases hFav with ⟨_, hC2, _, hC4⟩
  obtain ⟨_, hcfg, hlo, hhi⟩ := hC2 site hsite
  have hpath :
      sec8Sel x y (D (addFun (addFun g (F_Z T.f r Z))
        (-F_Z T.f r Z))).1 = sec8Sel x y (D g).1 :=
    lemma82_selector_cancel D T.f r Z g x y
  have hExc := hC4 site hsite
  dsimp only [S7bVeryGood]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hconfig]
    exact hcfg
  · rw [← hmacro, ← hnorm]
    exact hlo
  · rw [← hmacro, ← hnorm]
    exact hhi
  · rw [hpath] at hExc
    rw [hnorm] at hExc
    exact (s7b_Exc_congr _ _ _ _ _ _ _ hInt).mp hExc

end HigherDimLQGMetric
