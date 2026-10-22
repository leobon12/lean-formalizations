import HigherDimLQGMetric.Sec8b.Prop86RateAlgebra
import HigherDimLQGMetric.Sec8b.Prop86ClassMarkov

/-! A fixed class has a polynomial probability bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

def s7b_oneClassConst (d J k : ℕ) (Cs H c' c g M0 pH : ℝ) : ℝ :=
  Real.exp ((pH - 1) / 2 * (k * M0) ^ 2) *
    (s7b_candidateConst d J k) ^ pH⁻¹ *
    (((2 ^ (J * (1 + ⌈(2 * Cs * H + 1) /
      ((Cs - max c' 0) * c)⌉₊))) ^ k : ℕ) : ℝ) ^ (1 - pH⁻¹) * k ^
        ⌈g / (4 * H) * k⌉₊

theorem s7b_one_class_rate
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs B ε R : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hcs : 0 ≤ cs) (hCs : 0 < Cs)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 3) (hR : 0 < R)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ᵐ ω ∂P, ∀ u v : Rd d,
      cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v) ∧
      (Dt (h ω)).1 (u, v) ≤ Cs * (D (h ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (c : ℤ × (Fin d → ℤ) × ℤ)
    (hc : c ∈ s7b_classSet d hε hR B)
    (k : ℕ) (hk : 1 ≤ k)
    {M0 pH : ℝ} (hM0 : 0 ≤ M0)
    (hcm : ∀ label < T.J, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      IsCMBounded (bumpAt (T.f label) r z) M0)
    (hpH : 1 < pH) :
    P (s7b_manyFavEvent h D Dt ξ Q Cs R T.J T.N T.b T.V T.f x y k
      ((((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
        ⌈T.g / (4 * T.H) * k⌉₊) c) ≤
      ENNReal.ofReal (s7b_oneClassConst d T.J k Cs T.H T.c' T.c T.g M0 pH *
        (ε⁻¹) ^ ((2 * d * k : ℕ) * pH⁻¹ -
          (⌈T.g / (4 * T.H) * k⌉₊ : ℝ) / 2)) := by
  let r : ℝ := (64 : ℝ) ^ c.1
  let S := s7b_candidateFamily d T.J r R x y c.2.1 k
  let m : ℕ := ⌈T.g / (4 * T.H) * k⌉₊
  let t : ℝ := (((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^ m
  let E : ℝ := Real.exp ((pH - 1) / 2 * (k * M0) ^ 2)
  let K : ℝ := (((2 ^ (T.J * (1 + ⌈(2 * Cs * T.H + 1) /
      ((Cs - max T.c' 0) * T.c)⌉₊))) ^ k : ℕ) : ℝ) ^ (1 - pH⁻¹)
  let A : ℝ := s7b_candidateConst d T.J k
  have hε1' : ε ≤ 1 := by linarith only [hε1]
  have hc' : c.1 ∈ scaleWin ε R := by
    have hmem := (Finset.mem_product.mp hc).1
    exact (s4c_scaleWin_finite hε hR).mem_toFinset.mp hmem
  have hrlo : ε ^ 2 * R ≤ r := hc'.1
  have hrhi : r ≤ ε * R := hc'.2
  have hrR : 3 * r ≤ R := by
    have hmul := mul_le_mul_of_nonneg_right hε1 hR.le
    nlinarith only [hrhi, hmul]
  have hr : 0 < r := lt_of_lt_of_le (mul_pos (pow_pos hε _) hR) hrlo
  have hSa : (S.card : ℝ) ≤ A * (ε⁻¹) ^ (2 * d * k) :=
    s7b_candidate_power_bound d T.J k (by omega : 1 ≤ d)
      hε hε1' hR hrlo x y c.2.1
  have hS : ∀ Z ∈ S,
      IsSec8LabeledSet d T.J r R x y c.2.1 Z ∧ Z.card ≤ k :=
    fun Z hZ => ⟨(s7b_candidate_valid d T.J r R x y c.2.1 k hZ).1,
      (s7b_candidate_valid d T.J r R x y c.2.1 k hZ).2.2⟩
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hmarkov := s7b_class_markov_bound P h hh hd hξ hQ hcs hCs
    hD hDt hcomp T hR x y c.1 c.2.2 c.2.1 hrR k hk S hS
    hM0 hcm hpH t ht
  have ha : 0 ≤ pH⁻¹ := by
    have hp : 0 < pH := by linarith only [hpH]
    positivity
  have hrate := s7b_rate_algebra
    (show 0 < ε⁻¹ by positivity)
    (s7b_candidateConst_pos d T.J k)
    (by dsimp [E]; positivity)
    (by dsimp [K]; positivity)
    (by positivity : (0 : ℝ) ≤ S.card) hSa
    ha
    hk
    (s := ε⁻¹) (A := A) (E := E) (K := K) (S := S.card)
    (a := pH⁻¹) (n := 2 * d * k) (m := m) (k := k)
  have hbound : P (s7b_manyFavEvent h D Dt ξ Q Cs R T.J T.N T.b T.V T.f
      x y k t c) ≤ ENNReal.ofReal (E * (S.card : ℝ) ^ pH⁻¹ * K / t) := by
    simpa only [s7b_manyFavEvent, S, r, E, K] using hmarkov
  exact hbound.trans (by
    simpa only [s7b_oneClassConst, E, K, A, t, m] using
      ENNReal.ofReal_le_ofReal hrate)

end HigherDimLQGMetric
