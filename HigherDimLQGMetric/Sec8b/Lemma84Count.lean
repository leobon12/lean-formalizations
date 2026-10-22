import HigherDimLQGMetric.Sec8b.Lemma83
import HigherDimLQGMetric.Count.ImageOut

/-! The finite pruning count in Lemma 8.4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical
open Set Metric MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A labeled subset inherits its color, location, and separation data. -/
theorem s7b_labeled_subset {J : ℕ} {r R : ℝ} {x y : Rd d}
    {colour : Fin d → ℤ} {s t : Finset (Rd d × ℕ)}
    (hs : IsSec8LabeledSet d J r R x y colour s) (ht : t ⊆ s) :
    IsSec8LabeledSet d J r R x y colour t :=
  ⟨(fun q hq => hs.1 q (ht hq)),
    (fun q hq q' hq' heq => hs.2 q (ht hq) q' (ht hq') heq)⟩

/-- All `k`-subsets of one class can be pruned on a single full-probability
event. The image count is the bound `(N/k)^m` in (28). -/
theorem lemma84_class {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs q R r : ℝ}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hq : 0 < q) (hR : 0 < R) (hr : 0 < r)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (colour : Fin d → ℤ)
    (s : Finset (Rd d × ℕ))
    (hs : IsSec8LabeledSet d T.J r R x y colour s)
    {k m : ℕ} (hmpos : 1 ≤ m) (hmk : m ≤ k) (hks : k ≤ s.card)
    (hm : ∀ n : ℕ, T.g / (4 * T.H) * k ≤ n → m ≤ n) :
    ∀ᵐ ω ∂P,
      sec8C1 D Dt ξ Q Cs q R x y (h ω) →
      sec8C2 D Dt ξ Q q R r T.J T.N s (h ω) →
      sec8C3 D x y r s (h ω) →
      ((s.card : ℝ) / k) ^ m ≤
        (((s.powerset.filter fun t =>
          1 ≤ t.card ∧ t.card ≤ k ∧
            h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t).card : ℕ) : ℝ) := by
  classical
  have hprune : ∀ᵐ ω ∂P, ∀ t ∈ s.powersetCard k,
      sec8C1 D Dt ξ Q Cs q R x y (h ω) →
      sec8C2 D Dt ξ Q q R r T.J T.N t (h ω) →
      sec8C3 D x y r t (h ω) →
      ∃ u ⊆ t,
        T.g / (4 * T.H) * t.card ≤ u.card ∧
        h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y u := by
    refine (Filter.eventually_all_finset (s.powersetCard k)).2 ?_
    intro t ht
    exact lemma83_ae P h hh hd hξ hQ hq hR hr hD hDt hcomp T x y colour t
      (s7b_labeled_subset hs (Finset.mem_powersetCard.mp ht).1)
  filter_upwards [hprune] with ω hpr hC1 hC2 hC3
  let out : Finset (Rd d × ℕ) → Finset (Rd d × ℕ) :=
    fun t => if ht : ∃ u ⊆ t,
        T.g / (4 * T.H) * t.card ≤ u.card ∧
        h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y u
      then Classical.choose ht else ∅
  have hout : ∀ t ∈ s.powersetCard k,
      out t ⊆ t ∧ m ≤ (out t).card ∧
      h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y (out t) := by
    intro t ht
    have htC2 : sec8C2 D Dt ξ Q q R r T.J T.N t (h ω) :=
      fun site hsite => hC2 site ((Finset.mem_powersetCard.mp ht).1 hsite)
    have htC3 : sec8C3 D x y r t (h ω) :=
      fun site hsite => hC3 site ((Finset.mem_powersetCard.mp ht).1 hsite)
    have hex := hpr t ht hC1 htC2 htC3
    have hspec := Classical.choose_spec hex
    have houtEq : out t = Classical.choose hex := by simp only [out, dite_eq_left hex]
    rw [houtEq]
    refine ⟨hspec.1, ?_, hspec.2.2⟩
    apply hm
    simpa only [(Finset.mem_powersetCard.mp ht).2] using hspec.2.1
  have hcount := card_image_out_ge s hmk hks out
    (fun t ht => ⟨(hout t ht).1, (hout t ht).2.1⟩)
  have hsub : (s.powersetCard k).image out ⊆
      s.powerset.filter (fun t =>
        1 ≤ t.card ∧ t.card ≤ k ∧
          h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t) := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    have houtt := hout t ht
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr
        (houtt.1.trans (Finset.mem_powersetCard.mp ht).1)
    · exact ⟨hmpos.trans houtt.2.1,
        (Finset.card_le_card houtt.1).trans_eq
          (Finset.mem_powersetCard.mp ht).2, houtt.2.2⟩
  exact hcount.trans (by exact_mod_cast Finset.card_le_card hsub)

end HigherDimLQGMetric
