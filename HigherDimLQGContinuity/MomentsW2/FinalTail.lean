import HigherDimLQGContinuity.MomentsW2.ScaleTail

/-!
# Uniform geometric crossing tails
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP
open HigherDimLFPP.DGZ (cbox)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The direct crossing argument applies at all cutoff depths below the target scale. -/
theorem w2_late_geom (hκ : IsLFPPKernel κ) (hCr : CrudeLowerShape d κ)
    {r₁ r₂ c b μ : ℝ} (hr₂ : 0 ≤ r₂) (hr : r₂ < r₁)
    (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : ℝ, 2 * b * (Real.sqrt (2 * d) + 2 * C / Real.log 2) ≤ A →
        ∀ ξ : ℝ, UHyp d κ b μ ξ →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
          DGZ.IsDyadicRealization κ P W H → ∀ m n : ℕ, n < m →
            c * (2 : ℝ)⁻¹ ^ m ≤ r₁ - r₂ →
            P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
              DGZ.aQ P H ξ n 2⁻¹ <
                (c / 4) * (2 : ℝ) ^ (-((A + 1 + b ^ 2 / 2) * m))} ≤
                  ENNReal.ofReal (2 * (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m))) := by
  obtain ⟨C, hC, hfield⟩ := w2_coarse_late_geom hκ (R := r₁) (by linarith)
  refine ⟨C, hC, ?_⟩
  intro A hA ξ hξ Ω _ P W H hH m n hnm hsmall
  let t : ℝ := A * m * Real.log 2
  have hsmall' :
      (c / 4) * (2 : ℝ) ^ (-((A + 1 + b ^ 2 / 2) * m)) ≤
        (r₁ - r₂) * Real.exp (-t) / (4 * (2 : ℝ) ^ (b ^ 2 * n / 2)) :=
    w2_late_threshold_le (by linarith) hnm.le hsmall
  have hdirect := w2_direct_tail hκ hCr hξ hH hr₂ hr n t
  have hP : P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
      DGZ.aQ P H ξ n 2⁻¹ <
        (c / 4) * (2 : ℝ) ^ (-((A + 1 + b ^ 2 / 2) * m))} ≤
      P {ω | ∃ z ∈ cbox (0 : Rd d) r₁, t < -(ξ * H n z ω)} :=
    (measure_mono fun ω hω => lt_of_lt_of_le hω hsmall').trans hdirect
  by_cases hn : n = 0
  · subst n
    have hA0 : 0 ≤ A := by
      have h0 : 0 ≤ 2 * b * (Real.sqrt (2 * d) + 2 * C / Real.log 2) := by positivity
      exact h0.trans hA
    have ht : 0 ≤ t := by dsimp [t]; positivity
    rw [w2_coarse_zero hκ hH ξ t r₁ ht] at hP
    exact hP.trans (by positivity)
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    exact hP.trans (hfield hb hξ hA Ω P W H hH m n hn1 hnm.le)

/-- Choose the Gaussian threshold so its squared exponent dominates the requested moment. -/
theorem w2_choose_A {b q C₁ C₂ : ℝ}
    (hb : 0 < b) (hq : 0 < q) :
    ∃ A : ℝ,
      2 * b * (Real.sqrt (2 * d) + 2 * C₁ / Real.log 2) ≤ A ∧
      2 * b * (Real.sqrt (2 * d) + 2 * C₂ / Real.log 2) ≤ A ∧
      0 < A + 1 + b ^ 2 / 2 ∧
      q * (A + 1 + b ^ 2 / 2) + 1 ≤ A ^ 2 / (8 * b ^ 2) := by
  let A : ℝ := max (2 * b * (Real.sqrt (2 * d) + 2 * C₁ / Real.log 2))
    (max (2 * b * (Real.sqrt (2 * d) + 2 * C₂ / Real.log 2))
      (max (16 * b ^ 2 * (q + 1)) (q * (1 + b ^ 2 / 2) + 1)))
  have hA₁ : 2 * b * (Real.sqrt (2 * d) + 2 * C₁ / Real.log 2) ≤ A :=
    le_max_left _ _
  have hA₂ : 2 * b * (Real.sqrt (2 * d) + 2 * C₂ / Real.log 2) ≤ A :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hAb : 16 * b ^ 2 * (q + 1) ≤ A :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hAc : q * (1 + b ^ 2 / 2) + 1 ≤ A :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hA0 : 0 ≤ A := (by positivity : 0 ≤ q * (1 + b ^ 2 / 2) + 1).trans hAc
  have hq1 : 0 ≤ q + 1 := by linarith
  have hAprod := mul_le_mul_of_nonneg_right hAb hA0
  have hlinear : q * (A + 1 + b ^ 2 / 2) + 1 ≤ (q + 1) * A := by
    nlinarith only [hAc]
  have hmult := mul_le_mul_of_nonneg_right hlinear
    (by positivity : 0 ≤ 8 * b ^ 2)
  have hnonneg : 0 ≤ 8 * b ^ 2 * ((q + 1) * A) := by positivity
  have hb2 : 0 < 8 * b ^ 2 := by positivity
  refine ⟨A, hA₁, hA₂, by positivity, ?_⟩
  apply (le_div_iff₀ hb2).2
  nlinarith only [hAprod, hmult, hnonneg]

/-- Both the Gaussian and Peierls terms are bounded by one chosen geometric rate. -/
theorem w2_two_terms_le {r₁ A b E : ℝ} {d L m : ℕ}
    (hr₁ : 0 ≤ r₁)
    (hE₁ : E ≤ A ^ 2 / (8 * b ^ 2))
    (hE₂ : E ≤ (L : ℝ) - d) :
    ENNReal.ofReal (2 * (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m))) +
      ENNReal.ofReal ((2 * r₁ + 3) ^ d *
        (2 : ℝ) ^ (((d : ℝ) - L) * m)) ≤
      ENNReal.ofReal ((2 + (2 * r₁ + 3) ^ d) *
        (2 : ℝ) ^ (-(E * m))) := by
  let K : ℝ := (2 * r₁ + 3) ^ d
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpow₁ : (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m)) ≤
      (2 : ℝ) ^ (-(E * m)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith only [hE₁, hm]
  have hpow₂ : (2 : ℝ) ^ (((d : ℝ) - L) * m) ≤
      (2 : ℝ) ^ (-(E * m)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith only [hE₂, hm]
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m)))
    (by positivity : 0 ≤ K * (2 : ℝ) ^ (((d : ℝ) - L) * m))]
  apply ENNReal.ofReal_le_ofReal
  have h₁ := mul_le_mul_of_nonneg_left hpow₁ (by norm_num : (0 : ℝ) ≤ 2)
  have h₂ := mul_le_mul_of_nonneg_left hpow₂ hK
  dsimp [K] at *
  nlinarith only [h₁, h₂]

/-- One uniform geometric lower tail, with any requested inverse-moment order. -/
theorem w2_uniform_geom_tail (hd : 2 ≤ d) (hκ : IsLFPPKernel κ)
    (hCr : CrudeLowerShape d κ) (hN : UNondegShape d κ) (hQ : UQuantCompShape d κ)
    {b μ r₁ r₂ q : ℝ} (hb : 0 < b) (hμ : 0 < μ)
    (hr₂ : 0 < r₂) (hr : r₂ < r₁) (hq : 0 < q) :
    ∃ c B E C : ℝ, 0 < c ∧ 0 < B ∧ q * B < E ∧ 0 ≤ C ∧
      ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
        DGZ.IsDyadicRealization κ P W H → ∀ n m : ℕ,
          P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
            DGZ.aQ P H ξ n 2⁻¹ < c * (2 : ℝ) ^ (-(B * m))} ≤
              ENNReal.ofReal (C * (2 : ℝ) ^ (-(E * m))) := by
  let w : ℝ := r₁ - r₂
  have hw : 0 < w := by dsimp [w]; linarith
  obtain ⟨c₀, hc₀, C₁, hC₁, hmiddle⟩ :=
    w2_middle_geom hd hκ hCr hN hQ hb hμ hr₂ hr
  let c : ℝ := c₀ / 4
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨C₂, hC₂, hlate⟩ :=
    w2_late_geom hκ hCr hr₂.le hr hb (c := c₀) (b := b) (μ := μ)
  obtain ⟨A, hA₁, hA₂, hB, hAexp⟩ :=
    w2_choose_A (d := d) (C₁ := C₁) (C₂ := C₂) hb hq
  let B : ℝ := A + 1 + b ^ 2 / 2
  let E : ℝ := q * B + 1
  have hE : 0 < E := by dsimp [E]; positivity
  have hAE : E ≤ A ^ 2 / (8 * b ^ 2) := hAexp
  let L : ℕ := ⌈(d : ℝ) + E⌉₊
  have hLE : E ≤ (L : ℝ) - d := by
    have hceil := Nat.le_ceil ((d : ℝ) + E)
    dsimp [L]
    linarith only [hceil]
  let w₀ : ℝ := min w (8 * w / c₀)
  have hw₀ : 0 < w₀ := by dsimp [w₀]; positivity
  obtain ⟨m₀, hm₀, hgeom⟩ := w2_exists_geom_start hw₀ L
  let K : ℝ := 2 + (2 * r₁ + 3) ^ d
  have hK : 0 ≤ K := by
    dsimp [K]
    have hr1 : 0 ≤ r₁ := by linarith
    positivity
  let C : ℝ := K * (2 : ℝ) ^ (E * m₀)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨c, B, E, C, hc, hB, ?_, hC, ?_⟩
  · dsimp [E]; linarith
  intro ξ hξ Ω _ P W H hH n m
  have hprob : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  have hpowpos : 0 < (2 : ℝ) ^ (-(E * m)) := by positivity
  have hrate : 1 ≤ (2 : ℝ) ^ (E * m₀) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hm : m₀ ≤ m
  · have hm1 : 1 ≤ m := hm₀.trans hm
    have hgeom' := (hgeom m hm).2
    have hwidth : ((2 * L * m : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ m +
        8 * (2 : ℝ)⁻¹ ^ m ≤ r₁ - r₂ := hgeom'.trans (min_le_left _ _)
    have hsmall : c₀ * (2 : ℝ)⁻¹ ^ m ≤ r₁ - r₂ := by
      have h₁ : 8 * (2 : ℝ)⁻¹ ^ m ≤ w₀ := by
        have hfirst : 0 ≤ ((2 * L * m : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ m := by positivity
        linarith only [hgeom', hfirst]
      have h₂ : w₀ ≤ 8 * w / c₀ := min_le_right _ _
      have hc0 : 0 < c₀ := hc₀
      apply (le_div_iff₀ hc0).1 at h₂
      dsimp [w] at h₂
      nlinarith only [h₁, h₂, hc0]
    have hbase : P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
        DGZ.aQ P H ξ n 2⁻¹ < c * (2 : ℝ) ^ (-(B * m))} ≤
        ENNReal.ofReal (K * (2 : ℝ) ^ (-(E * m))) := by
      by_cases hmn : m ≤ n
      · have hmid := hmiddle A hA₁ L ξ hξ Ω P W H hH m n hm1 hmn hwidth
        exact hmid.trans (w2_two_terms_le (d := d) (L := L) (m := m)
          (A := A) (b := b) (E := E) (by linarith : 0 ≤ r₁) hAE hLE)
      · have hnm : n < m := Nat.lt_of_not_ge hmn
        have hdir := hlate A hA₂ ξ hξ Ω P W H hH m n hnm hsmall
        have hpow : (2 : ℝ) ^ (-(A ^ 2 / (8 * b ^ 2) * m)) ≤
            (2 : ℝ) ^ (-(E * m)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
          nlinarith only [hAE, hmnonneg]
        exact hdir.trans (ENNReal.ofReal_le_ofReal (by
          have hp := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2)
          have hr1 : 0 ≤ r₁ := by linarith
          have hK0 : 0 ≤ (2 * r₁ + 3) ^ d := by positivity
          nlinarith only [hp, hpowpos, hK0]))
    apply hbase.trans (ENNReal.ofReal_le_ofReal ?_)
    dsimp [C]
    have hfactor := mul_le_mul_of_nonneg_left hrate hK
    have hlast := mul_le_mul_of_nonneg_right hfactor hpowpos.le
    nlinarith only [hlast]
  · have hmn : m ≤ m₀ := Nat.le_of_lt (Nat.lt_of_not_ge hm)
    have hmreal : (m : ℝ) ≤ m₀ := by exact_mod_cast hmn
    have hgap : 0 ≤ E * ((m₀ : ℝ) - m) := mul_nonneg hE.le (sub_nonneg.mpr hmreal)
    have hunit : 1 ≤ (2 : ℝ) ^ (E * ((m₀ : ℝ) - m)) :=
      Real.one_le_rpow (by norm_num) hgap
    have heq : (2 : ℝ) ^ (E * ((m₀ : ℝ) - m)) =
        (2 : ℝ) ^ (E * m₀) * (2 : ℝ) ^ (-(E * m)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [heq] at hunit
    have hbound : 1 ≤ C * (2 : ℝ) ^ (-(E * m)) := by
      dsimp [C]
      have hK1 : 1 ≤ K := by
        dsimp [K]
        have hr1 : 0 ≤ r₁ := by linarith
        have hk : 0 ≤ (2 * r₁ + 3) ^ d := by positivity
        linarith
      have hh := mul_le_mul_of_nonneg_right hK1 (by positivity : 0 ≤
        (2 : ℝ) ^ (E * m₀) * (2 : ℝ) ^ (-(E * m)))
      nlinarith only [hunit, hh]
    calc
      P {ω | DGZ.acrossDist ξ (fun z => H n z ω) 0 r₁ r₂ /
          DGZ.aQ P H ξ n 2⁻¹ < c * (2 : ℝ) ^ (-(B * m))}
          ≤ 1 := by rw [← @IsProbabilityMeasure.measure_univ _ _ P hprob]; exact measure_mono (subset_univ _)
      _ ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(E * m))) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hbound

end HigherDimLQGContinuity
