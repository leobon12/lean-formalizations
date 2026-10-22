import HigherDimLQGMetric.Sec8b.Prop86Normalize

/-! Markov's inequality for the normalized favorable count in one class. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_class_markov_bound
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
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
    (hR : 0 < R) (x y : Rd d)
    (j i : ℤ) (colour : Fin d → ℤ)
    (hrR : 3 * (64 : ℝ) ^ j ≤ R)
    (k : ℕ) (hk : 1 ≤ k)
    (S : Finset (Finset (Rd d × ℕ)))
    (hS : ∀ Z ∈ S,
      IsSec8LabeledSet d T.J ((64 : ℝ) ^ j) R x y colour Z ∧
        Z.card ≤ k)
    {M0 : ℝ} (hM0 : 0 ≤ M0)
    (hcm : ∀ label < T.J, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      IsCMBounded (bumpAt (T.f label) r z) M0)
    {pH : ℝ} (hpH : 1 < pH)
    (t : ℝ) (ht : 0 < t) :
    P {ω | t ≤ ((S.filter fun Z => h ω ∈
      FavEventBorel D Dt ξ Q Cs ((2 : ℝ) ^ i) R ((64 : ℝ) ^ j)
        T.b T.J T.N T.V T.f x y Z).card : ℝ)} ≤
      ENNReal.ofReal
        (Real.exp ((pH - 1) / 2 * (k * M0) ^ 2) *
          (S.card : ℝ) ^ pH⁻¹ *
          (((2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
            ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k : ℕ) : ℝ) ^
              (1 - pH⁻¹) / t) := by
  let E : Finset (Rd d × ℕ) → Set Ω := fun Z =>
    {ω | h ω ∈ FavEventBorel D Dt ξ Q Cs ((2 : ℝ) ^ i) R
      ((64 : ℝ) ^ j) T.b T.J T.N T.V T.f x y Z}
  have hr : 0 < (64 : ℝ) ^ j := by positivity
  have hEm : ∀ Z ∈ S, MeasurableSet (E Z) := by
    intro Z _
    exact (measurableSet_FavEventBorel hD.measurable hDt.measurable
      ξ Q Cs ((2 : ℝ) ^ i) R ((64 : ℝ) ^ j) T.b hr T.J
      T.N T.measurableN T.V T.openV T.f x y Z).preimage
      hh.1.measurable
  have hmarkov := s7b_markov_count P S E hEm t
  have hsum := s7b_cm_class_bound P h hh hd hξ hQ hcs hCs
    hD hDt hcomp T hR x y j i colour hrR k hk S hS hM0 hcm hpH
  have hreal : P.real {ω | t ≤ ((S.filter fun Z => ω ∈ E Z).card : ℝ)} ≤
      (Real.exp ((pH - 1) / 2 * (k * M0) ^ 2) *
        (S.card : ℝ) ^ pH⁻¹ *
        (((2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
          ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k : ℕ) : ℝ) ^
            (1 - pH⁻¹)) / t := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm, E] using hmarkov.trans hsum
  have hfin : P {ω | t ≤ ((S.filter fun Z => ω ∈ E Z).card : ℝ)} ≠ ⊤ :=
    measure_ne_top P _
  rw [show {ω | t ≤ ((S.filter fun Z => h ω ∈
      FavEventBorel D Dt ξ Q Cs ((2 : ℝ) ^ i) R ((64 : ℝ) ^ j)
        T.b T.J T.N T.V T.f x y Z).card : ℝ)} =
      {ω | t ≤ ((S.filter fun Z => ω ∈ E Z).card : ℝ)} from rfl]
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hreal

end HigherDimLQGMetric
