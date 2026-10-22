import HigherDimLQGMetric.Sec8b.Prop86RateChoice

/-! The full proposition estimate with fixed moment and sample-size parameters. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_prop86_fixed_rate
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs B η ε R N : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hcs : 0 < cs) (hCs : cs ≤ Cs)
    (hB : 0 < B) (hη : 0 < η) (hη1 : η ≤ 1)
    (hε : 0 < ε) (hεη : ε < η / 18)
    (hεhalf : ε ≤ 1 / 2) (hεthird : ε ≤ 1 / 3)
    (hR : 0 < R)
    (hclass : (s7b_classSet d hε hR B).card *
      ⌈(ε⁻¹) ^ (1 / 2 : ℝ)⌉₊ ≤ s7b_sampleCount η ε)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (hcomp : ∀ {Ω' : Type} [MeasurableSpace Ω']
      (P' : Measure Ω') [IsProbabilityMeasure P']
      (h' : Ω' → DistRd d), IsWholeSpaceLGF h' P' →
        ∀ᵐ ω ∂P', ∀ u v : Rd d,
          cs * (D (h' ω)).1 (u, v) ≤ (Dt (h' ω)).1 (u, v) ∧
          (Dt (h' ω)).1 (u, v) ≤ Cs * (D (h' ω)).1 (u, v))
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (hx : ‖x‖ < 3 * R) (hy : ‖y‖ < 3 * R)
    (hxy : η * R ≤ ‖x - y‖)
    (k : ℕ) (hk : 1 ≤ k)
    (hkup : (k : ℝ) ≤ (ε⁻¹) ^ (1 / 2 : ℝ))
    {M0 pH : ℝ} (hM0 : 0 ≤ M0)
    (hcm : ∀ label < T.J, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      IsCMBounded (bumpAt (T.f label) r z) M0)
    (hpH : 1 < pH)
    (he : (1 / 4 : ℝ) + (2 * d * k : ℕ) * pH⁻¹ -
      (⌈T.g / (4 * T.H) * k⌉₊ : ℝ) / 2 ≤ -N) :
    P {ω | h ω ∈ sec8AEvent D Dt ξ Q T.J T.N B ε R ∧
      sec8C1 D Dt ξ Q Cs (ε ^ (B + 1)) R x y (h ω)} ≤
      ENNReal.ofReal (s7b_classConst d B *
        s7b_oneClassConst d T.J k Cs T.H T.c' T.c T.g M0 pH * ε ^ N) := by
  let hn := s7b_normalizedField h
  let classes := s7b_classSet d hε hR B
  let C0 := s7b_oneClassConst d T.J k Cs T.H T.c' T.c T.g M0 pH
  let e : ℝ := (2 * d * k : ℕ) * pH⁻¹ -
    (⌈T.g / (4 * T.H) * k⌉₊ : ℝ) / 2
  let X : ℝ := C0 * (ε⁻¹) ^ e
  have hε1 : ε ≤ 1 := by linarith only [hεthird]
  have hCspos : 0 < Cs := lt_of_lt_of_le hcs hCs
  have hhn : IsNormalizedLGF hn P := s7b_normalized_lgf P h hh hd
  have hcompRaw := hcomp P h hh
  have hcompN := hcomp P hn hhn.1
  have hclassBound : ((classes.card : ℕ) : ℝ) ≤
      s7b_classConst d B * ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ) :=
    s7b_classSet_power_bound hε hε1 hR hB.le
  have hC0 : 0 ≤ C0 := by
    dsimp [C0, s7b_oneClassConst]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.exp_nonneg _)
          (Real.rpow_nonneg (s7b_candidateConst_pos d T.J k).le _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg (Nat.cast_nonneg k) _)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hK : 0 ≤ s7b_classConst d B :=
    (s7b_classConst_pos d hB.le).le
  have he' : (1 / 4 : ℝ) + e ≤ -N := by
    dsimp [e]
    linarith only [he]
  have hunion := s7b_prop86_union_bound P h hh hd hξ hQ
    hη hη1 hε hR hεη hεhalf hclass hD hDt hcompRaw
    T x y hx hy hxy k hk hkup
  have hrate : ∀ c ∈ classes,
      P (s7b_manyFavEvent hn D Dt ξ Q Cs R T.J T.N T.b T.V T.f
        x y k ((((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
          ⌈T.g / (4 * T.H) * k⌉₊) c) ≤ ENNReal.ofReal X := by
    intro c hc
    simpa only [hn, X, C0, e] using
      s7b_one_class_rate P hn hhn hd hξ hQ hcs.le hCspos
        hε hεthird hR hD hDt hcompN T x y c hc k hk hM0 hcm hpH
  have hsum :
      ∑ c ∈ classes,
        P (s7b_manyFavEvent hn D Dt ξ Q Cs R T.J T.N T.b T.V T.f
          x y k ((((ε⁻¹) ^ (1 / 2 : ℝ)) / k) ^
            ⌈T.g / (4 * T.H) * k⌉₊) c) ≤
      ENNReal.ofReal ((classes.card : ℝ) * X) := by
    calc
      _ ≤ ∑ _c ∈ classes, ENNReal.ofReal X := by
        apply Finset.sum_le_sum
        intro c hc
        exact hrate c hc
      _ = ENNReal.ofReal ((classes.card : ℝ) * X) := by
        rw [Finset.sum_const, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ classes.card)]
        simp
  have hreal : (classes.card : ℝ) * X ≤
      s7b_classConst d B * C0 * ε ^ N := by
    calc
      (classes.card : ℝ) * X ≤
          (s7b_classConst d B * ((ε⁻¹) ^ (1 / 8 : ℝ)) ^ (2 : ℕ)) * X :=
        mul_le_mul_of_nonneg_right hclassBound hX
      _ ≤ s7b_classConst d B * C0 * ε ^ N := by
        simpa only [X, e] using
          s7b_final_power hε hε1 hK hC0 he'
  exact hunion.trans (hsum.trans (by
    simpa only [classes, C0] using ENNReal.ofReal_le_ofReal hreal))

end HigherDimLQGMetric
