import HigherDimLQGMetric.Sec8b.Prop86Lemma84Fixed

/-! The near-extreme event forces many normalized Borel events in one class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_many_classes_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs B η ε R : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : 0 < ε) (hR : 0 < R)
    (hεη : ε < η / 18) (hεhalf : ε ≤ 1 / 2)
    (hclass : (s7b_classSet d hε hR B).card *
      ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ ≤ s7b_sampleCount η ε)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (hx : ‖x‖ < 3 * R) (hy : ‖y‖ < 3 * R)
    (hxy : η * R ≤ ‖x - y‖)
    (k : ℕ) (hk : 1 ≤ k)
    (hkup : (k : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ)) :
    ∀ᵐ ω ∂P,
      h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
      sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω) →
      ∃ c ∈ s7b_classSet d hε hR B,
        (((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
            ⌈T.g / (4 * T.H) * k⌉₊ ≤
          (((s7b_candidateFamily d T.J ((64 : ℝ) ^ c.1) R x y
              c.2.1 k).filter fun Z =>
            (s7b_normalizedField h) ω ∈
              FavEventBorel D Dt ξ Q Cs ((2 : ℝ) ^ c.2.2) R
                ((64 : ℝ) ^ c.1) T.b T.J T.N T.V T.f x y Z).card : ℕ) := by
  classical
  have hmany := s7b_lemma84_fixed P h hh hd hξ hQ hη hη1
    hε hR hεη hεhalf hclass hD hDt hcomp T x y hx hy hxy k hk hkup
  have hnorm := s7b_all_candidate_counts_normalize_ae P h hh hd hξ hQ
    hR hD hDt T x y
  filter_upwards [hmany, hnorm] with ω hm hn hEvent
  obtain ⟨c, hc, s, hZs, hcount⟩ := hm hEvent
  let r : ℝ := (64 : ℝ) ^ c.1
  let q : ℝ := (2 : ℝ) ^ c.2.2
  let S := s7b_candidateFamily d T.J r R x y c.2.1 k
  have hr : 0 < r := by dsimp [r]; positivity
  have hsubset :
      (s.powerset.filter fun t => 1 ≤ t.card ∧ t.card ≤ k ∧
        h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t) ⊆
      (S.filter fun t => h ω ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t) := by
    intro t ht
    obtain ⟨htpow, htpos, htk, hFav⟩ := Finset.mem_filter.mp ht
    have htZ : IsSec8LabeledSet d T.J r R x y c.2.1 t :=
      s7b_labeled_subset hZs (Finset.mem_powerset.mp htpow)
    have htS : t ∈ S := s7b_candidate_mem d T.J
      (by omega : 1 ≤ d) hr hR x y c.2.1 k htZ htpos htk
    exact Finset.mem_filter.mpr ⟨htS, hFav⟩
  have hcard := Finset.card_le_card hsubset
  have hnormEq := hn c.1 c.2.2 c.2.1 k
  refine ⟨c, hc, ?_⟩
  calc
    (((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
        ⌈T.g / (4 * T.H) * k⌉₊ ≤
      (((s.powerset.filter fun t => 1 ≤ t.card ∧ t.card ≤ k ∧
        h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t).card : ℕ) : ℝ) := hcount
    _ ≤ ((S.filter fun t => h ω ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t).card : ℕ) := by
      exact_mod_cast hcard
    _ = ((S.filter fun t => (s7b_normalizedField h) ω ∈
        FavEventBorel D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y t).card : ℕ) := by
      exact_mod_cast hnormEq

end HigherDimLQGMetric
