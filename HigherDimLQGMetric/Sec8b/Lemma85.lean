import HigherDimLQGMetric.Sec8b.Lemma85Selected
import HigherDimLQGMetric.Sec8b.Lemma85AE

/-! [S] Lemma 8.5: one common full-probability event for every class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The corrected bound `K₀^k` on shifted favorable sets. The family `S`
is any finite family of geometrically valid sets with at most `k` labels;
the statement is simultaneous for all such families and all lattice classes. -/
theorem lemma85 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs R : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hcs : 0 ≤ cs) (hCs : 0 < Cs)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (hR : 0 < R) (x y : Rd d) :
    ∀ᵐ ω ∂P,
      ∀ j i : ℤ, ∀ colour : Fin d → ℤ,
      ∀ k : ℕ, 1 ≤ k →
      let r := (64 : ℝ) ^ j
      let q := (2 : ℝ) ^ i
      3 * r ≤ R →
      ∀ S : Finset (Finset (Rd d × ℕ)),
        (∀ Z ∈ S,
          IsSec8LabeledSet d T.J r R x y colour Z ∧ Z.card ≤ k) →
        (S.filter fun Z => addFun (h ω) (F_Z T.f r Z) ∈
          FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z).card ≤
          (2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
            ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k := by
  classical
  filter_upwards [s7b_shifted_metric_ae P h hh hD hDt hcs hCs hcomp,
    s7b_selected_geod_ae P h hh hd hξ hQ hD x y,
    s7b_shifted_macro_ae_all_indexed P h hh hd hD hDt T hR x y,
    s7b_shifted_fav_sites_ae_all_indexed P h hh hd hD hDt T hR x y]
    with ω hmetric hgeod hmacro hvery
  intro j i colour k hk
  dsimp only
  intro hrR S hS
  let r : ℝ := (64 : ℝ) ^ j
  let q : ℝ := (2 : ℝ) ^ i
  have hr : 0 < r := by dsimp [r]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hmacroS : ∀ Z ∈ S,
      macroS ξ Q (addFun (h ω) (F_Z T.f r Z)) R =
        macroS ξ Q (h ω) R := by
    intro Z hZS
    obtain ⟨W, hW⟩ := s7b_labeled_index_rep (hS Z hZS).1
    have hZidx : IsSec8LabeledSet d T.J r R x y colour
        (s7b_indexSites r W) := by
      rw [hW]
      exact (hS Z hZS).1
    have hm := hmacro j colour W hrR hZidx
    simpa only [r, hW] using hm
  have hveryS : ∀ Z ∈ S,
      addFun (h ω) (F_Z T.f r Z) ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z →
      ∀ site ∈ Z, S7bVeryGood T Q q R r x y (h ω) site := by
    intro Z hZS hFav
    obtain ⟨W, hW⟩ := s7b_labeled_index_rep (hS Z hZS).1
    have hZidx : IsSec8LabeledSet d T.J r R x y colour
        (s7b_indexSites r W) := by
      rw [hW]
      exact (hS Z hZS).1
    have hf := hvery j i colour W hrR hZidx
    have hfavIdx : addFun (h ω) (F_Z T.f r (s7b_indexSites r W)) ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y
          (s7b_indexSites r W) := by
      rw [hW]
      exact hFav
    simpa only [r, q, hW] using hf hfavIdx
  let path := s7b_realPath (sec8Sel x y (D (h ω)).1)
  exact s7b_few_shifted_fav_deterministic T hd hξ hCs hq hR hr
    (h ω) x y colour k hk S hS hmacroS hveryS hmetric path
    hgeod.1 rfl hgeod.2.1 hgeod.2.2

end HigherDimLQGMetric
