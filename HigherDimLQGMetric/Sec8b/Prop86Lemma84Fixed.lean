import HigherDimLQGMetric.Sec8b.Prop86ClassMarkov

/-! Lemma 8.4 at the explicit deterministic sampling threshold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_lemma84_fixed {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : IsWholeSpaceLGF h P)
    {ξ Q cs Cs B η ε R : ℝ}
    (hd : 3 ≤ d) (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
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
        let r := (64 : ℝ) ^ c.1
        let q := (2 : ℝ) ^ c.2.2
        ∃ s : Finset (Rd d × ℕ),
          IsSec8LabeledSet d T.J r R x y c.2.1 s ∧
          (((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
              ⌈T.g / (4 * T.H) * k⌉₊ ≤
            (((s.powerset.filter fun t =>
              1 ≤ t.card ∧ t.card ≤ k ∧
                h ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N
                  T.V T.f x y t).card : ℕ) : ℝ) := by
  by_cases hJ : 0 < T.J
  · let κ := T.g / (4 * T.H)
    let n := ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊
    let m := ⌈κ * k⌉₊
    obtain ⟨hκpos, hκle⟩ := s7b_pruning_fraction_bounds T hξ hJ
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
    have hmpos : 1 ≤ m := by
      have h : 0 < κ * (k : ℝ) := mul_pos hκpos hkpos
      change 0 < ⌈κ * (k : ℝ)⌉₊
      exact Nat.ceil_pos.mpr h
    have hnpos : 1 ≤ n := by
      have h : 0 < (ε⁻¹) ^ (1 / 2 : ℝ) := by positivity
      change 0 < ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊
      exact Nat.ceil_pos.mpr h
    have hmk : m ≤ k := by
      apply Nat.ceil_le.mpr
      have hmul := mul_le_mul_of_nonneg_right hκle
        (show 0 ≤ (k : ℝ) by positivity)
      simpa only [one_mul] using hmul
    have hkn : k ≤ n := by
      have hn := Nat.le_ceil ((ε⁻¹) ^ (1 / 2 : ℝ))
      exact_mod_cast le_trans hkup hn
    have hm : ∀ t : ℕ, κ * k ≤ t → m ≤ t := by
      intro t ht
      exact Nat.ceil_le.mpr ht
    have hcount := lemma84_of_class_count P h hh hd hξ hQ hR hη hη1
      hε hεη hεhalf hD hDt hcomp T x y hx hy hxy
      hnpos hmpos hmk hkn hm hclass
    filter_upwards [hcount] with ω hω hevent
    obtain ⟨c, hc, s, hns, hZs, hbound⟩ := hω hevent
    have hdiv : ((ε⁻¹) ^ (1 / 2 : ℝ)) / k ≤ (n : ℝ) / k := by
      have hn := Nat.le_ceil ((ε⁻¹) ^ (1 / 2 : ℝ))
      exact div_le_div_of_nonneg_right hn (by positivity)
    have hpow : (((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^ m ≤
        ((n : ℝ) / k) ^ m :=
      pow_le_pow_left₀ (by positivity) hdiv m
    exact ⟨c, hc, s, hZs, hpow.trans hbound⟩
  · filter_upwards [] with ω hevent
    have hJ' := s7b_cover_implies_Jpos hR (h ω) hevent.1.1
    exact False.elim (hJ hJ')

end HigherDimLQGMetric
