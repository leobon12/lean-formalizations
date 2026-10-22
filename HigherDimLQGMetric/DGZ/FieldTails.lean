import HigherDimLQGMetric.DGZ.ConcentrationQuantile
import HigherDimLFPP.Field.SupBounds
import HigherDimLFPP.Exist.Discretize

/-!
# Field tails I: point values and sharp suprema on boxes (packet L3b2; MA7 `𝒢_n`)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 2.3 (1), (3), (4) and the event `𝒢_n`
of (4.6) with its bound in Lemma 4.2(1); planning audit `planning/audits/MA7-ref2-sections-4-6.md`,
§2.4 ("Lemma 2.3(3)–(4) with the sharp constant `√(2d) log 2` … `bandSup_bounds` … is sharp to
first order"), Details (a) D-4.2 (first paragraph) and the §5 row L3b2.

* `measure_abs_ge_le_of_isBandVersion` (Lemma 2.3 (1)): `P[|X g| ≥ t] ≤ 2 exp(-t²/(2 log(b/a)))`
  for a continuous version `X` of `H_{a,b}`; a corollary of the concentration theorem of
  `Concentration.lean` (evaluation at `g` is `1`-Lipschitz for the sup norm on `{g}`).
* `exists_sup_cbox_gaussian_tail` (Lemma 2.3 (3)–(4), sharp to first order): there is `C ≥ 0`
  (depending on `d`, `κ`, `R`) with
  `P[∃ z ∈ B̄_{Rb}(c), √(2d) v + C √v + C + u < |X z|] ≤ 2 exp(-u²/(2v))`, `v = log(b/a)`.
* `exists_sup_cbox_tail`: for `A > √(2d)`, `P[∃ z ∈ B̄_{Rb}(c), A v < |X z|] ≤ C e^{-v/C}`.
* **`prob_sharpSup_compl_le`** (target; DGZ (4.6), Lemma 4.2(1), first inequality): for
  `ξ > 0` and `η < ξ(Q - √(2d))` there is `C` with
  `P[∃ z ∈ B̄₃(0), n (Q - η/ξ) log 2 < h_n(z)] ≤ C e^{-n/C}` for every continuous version `h_n` of
  `H_{2^{-n},1}` and every `n`.

**Proof of the sharp bound** (MA7 D-4.2): HigherDimLFPP's `exists_bandSup_bounds` gives
`E sup_B H ≤ supMean d L V ℓ` and the Borell–TIS tail with `V = v`, `B = B̄_{Rb}(c)` and
`ℓ = d log(2Rb/a + 1) ≤ d v + d log(2R + 1)` (`log_two_mul_div_add_one_le`); then
`supMean d L v (d v + c₂) ≤ √(2d) v + c₅ √v + c₆` (`supMean_le_sharp`:
`√(2v(dv + c₃)) ≤ √(2d) v + √(2c₃ v)` and `√(dv + c₃) ≤ √d √v + √c₃`). For `A > √(2d)`,
`g := A - √(2d)` and `v ≥ v₀`, the excess `u = A v - (√(2d) v + C √v + C) ≥ g v / 2`, so the tail
is `≤ 2 exp(-g² v / 8)`; for `v < v₀` the probability is at most `1`. Dimension `0` is covered by
the point bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ### Point values (DGZ Lemma 2.3 (1)) -/

/-- Evaluation at a point is `1`-Lipschitz for the sup norm on `{g}`. -/
theorem isSupLipschitzOn_eval (g : Rd d) : IsSupLipschitzOn {g} 1 fun φ => φ g :=
  fun _φ _ψ _ _ _M _ hM => by
    rw [one_mul]
    exact hM g (mem_singleton g)

section Point

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}
  {a b : ℝ} {X : Rd d → Ω → ℝ}

/-- **Gaussian tail at a point** (DGZ Lemma 2.3 (1): `h_{m,n}(x) ∼ N(0, (n - m) log 2)`): for a
continuous version `X` of `H_{a,b}` (`0 < a ≤ b`) and `t ≥ 0`,
`P[|X g| ≥ t] ≤ 2 exp(-t²/(2 log(b/a)))`. -/
theorem measure_abs_ge_le_of_isBandVersion (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    (ha : 0 < a) (hab : a ≤ b) (hX : IsBandVersion P W κ a b X) (g : Rd d) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | t ≤ |X g ω|} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * Real.log (b / a)))) := by
  have h := measure_abs_sub_integral_ge_le_of_isSupLipschitzOn (F := fun φ => φ g) hκ hW ha hab
    hX isCompact_singleton (isSupLipschitzOn_eval g) ht
  simp only [hX.integral_eq_zero hW g, sub_zero, one_pow, mul_one] at h
  exact h

end Point

/-! ### The sharp first-order bound on `supMean` -/

/-- `log(2 R b/a + 1) ≤ log(b/a) + log(2R + 1)` for `0 < a ≤ b` and `R ≥ 0`. -/
theorem log_two_mul_div_add_one_le {a b R : ℝ} (ha : 0 < a) (hab : a ≤ b) (hR : 0 ≤ R) :
    Real.log (2 * (R * b) / a + 1) ≤ Real.log (b / a) + Real.log (2 * R + 1) := by
  have hba : 1 ≤ b / a := (one_le_div ha).2 hab
  have hb : 0 < b := ha.trans_le hab
  rw [← Real.log_mul (div_pos hb ha).ne' (by positivity : (0 : ℝ) < 2 * R + 1).ne']
  refine Real.log_le_log (by positivity) ?_
  have e1 : 2 * (R * b) / a = 2 * R * (b / a) := by ring
  have e2 : b / a * (2 * R + 1) = 2 * R * (b / a) + b / a := by ring
  rw [e1, e2]
  linarith

/-- **Sharp first-order bound on `supMean`** (MA7 §2.4: `supMean = √(2V(1+ℓ)) + O(1) + O(√ℓ)`): for
`L, v, c₂ ≥ 0`,
`supMean d L v (d v + c₂) ≤ √(2d) v + (√(2(1+c₂)) + 2 c₄ √d) √v + (B + 2 c₄ √(1+c₂))` with
`c₄ = √(π² (√d)² L / 8)` and `B = blockConst d L √d`. -/
theorem supMean_le_sharp (d : ℕ) {L v c₂ : ℝ} (hv : 0 ≤ v) (hc₂ : 0 ≤ c₂) :
    SupB.supMean d L v (d * v + c₂) ≤
      √(2 * d) * v +
        (√(2 * (1 + c₂)) + 2 * √(Real.pi ^ 2 * (√(d : ℝ) ^ 2 * L) / 8) * √(d : ℝ)) * √v +
        (Osc.blockConst d L √(d : ℝ) +
          2 * √(Real.pi ^ 2 * (√(d : ℝ) ^ 2 * L) / 8) * √(1 + c₂)) := by
  unfold SupB.supMean
  set c₄ : ℝ := √(Real.pi ^ 2 * (√(d : ℝ) ^ 2 * L) / 8) with hc₄
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hc₄0 : 0 ≤ c₄ := Real.sqrt_nonneg _
  have e1 : 1 + ((d : ℝ) * v + c₂) = (d : ℝ) * v + (1 + c₂) := by ring
  rw [e1]
  set s : ℝ := √((d : ℝ) * v + (1 + c₂)) with hsdef
  have hs : s ^ 2 = (d : ℝ) * v + (1 + c₂) := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- the Gaussian part
  have h1 : 2 * s * √(v / 2) ≤ √(2 * d) * v + √(2 * (1 + c₂)) * √v := by
    have ht : √(v / 2) ^ 2 = v / 2 := Real.sq_sqrt (by positivity)
    have hp : √(2 * (d : ℝ)) ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
    have hq : √(2 * (1 + c₂)) ^ 2 = 2 * (1 + c₂) := Real.sq_sqrt (by positivity)
    have hw : √v ^ 2 = v := Real.sq_sqrt hv
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero]
    have lhs : (2 * s * √(v / 2)) ^ 2 = 2 * d * v ^ 2 + 2 * (1 + c₂) * v := by
      rw [mul_pow, mul_pow, hs, ht]
      ring
    have rhs : (√(2 * d) * v + √(2 * (1 + c₂)) * √v) ^ 2 =
        2 * d * v ^ 2 + 2 * (1 + c₂) * v + 2 * (√(2 * d) * v * (√(2 * (1 + c₂)) * √v)) := by
      rw [add_sq, mul_pow, mul_pow, hp, hq, hw]
      ring
    have hcross : 0 ≤ √(2 * (d : ℝ)) * v * (√(2 * (1 + c₂)) * √v) := by positivity
    rw [lhs, rhs]
    linarith
  -- the chaining part
  have h3 : s ≤ √(d : ℝ) * √v + √(1 + c₂) := by
    rw [hsdef, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [add_sq, mul_pow, Real.sq_sqrt hd0, Real.sq_sqrt hv, Real.sq_sqrt (by positivity)]
    have : 0 ≤ 2 * (√(d : ℝ) * √v) * √(1 + c₂) := by positivity
    linarith
  have h3' : 2 * s * c₄ ≤ 2 * c₄ * (√(d : ℝ) * √v + √(1 + c₂)) := by
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * c₄)
    linarith
  calc 2 * s * √(v / 2) + Osc.blockConst d L √(d : ℝ) + 2 * s * c₄
      ≤ (√(2 * d) * v + √(2 * (1 + c₂)) * √v) + Osc.blockConst d L √(d : ℝ) +
          2 * c₄ * (√(d : ℝ) * √v + √(1 + c₂)) := add_le_add (add_le_add h1 le_rfl) h3'
    _ = √(2 * d) * v + (√(2 * (1 + c₂)) + 2 * c₄ * √(d : ℝ)) * √v +
          (Osc.blockConst d L √(d : ℝ) + 2 * c₄ * √(1 + c₂)) := by ring

/-- `B̄_r(c)` (`cbox`) is HigherDimLFPP's `Osc.box c r`. -/
theorem cbox_eq_box (c : Rd d) (r : ℝ) : cbox c r = Osc.box c r := rfl

/-! ### Sharp suprema on boxes -/

/-- **Sharp supremum of a band field on a box, Gaussian form** (DGZ Lemma 2.3 (3)–(4), MA7 D-4.2):
there is `C ≥ 0`, depending only on `d`, `κ` and `R`, such that for every white noise, every
continuous version `X` of `H_{a,b}` (`0 < a ≤ b`, `v = log(b/a)`), every centre `c` and `u ≥ 0`,
`P[∃ z ∈ B̄_{R b}(c), √(2d) v + C √v + C + u < |X z|] ≤ 2 exp(-u²/(2v))`. -/
theorem exists_sup_cbox_gaussian_tail {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {R : ℝ}
    (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ (c : Rd d) {u : ℝ}, 0 ≤ u →
        P {ω | ∃ z ∈ cbox c (R * b),
            √(2 * d) * Real.log (b / a) + C * √(Real.log (b / a)) + C + u < |X z ω|} ≤
          ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * Real.log (b / a)))) := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · -- dimension `0`: the box is a point
    subst hd
    refine ⟨0, le_rfl, fun {Ω} _ {P} {W} hW {a b} ha hab {X} hX c {u} hu => ?_⟩
    have hv0 : 0 ≤ Real.log (b / a) := Real.log_nonneg ((one_le_div ha).2 hab)
    refine (measure_mono fun ω hω => ?_).trans (measure_abs_ge_le_of_isBandVersion hκ hW ha hab
      hX c hu)
    obtain ⟨z, -, hz⟩ := hω
    have hzc : z = c := by
      ext i
      exact i.elim0
    rw [hzc] at hz
    show u ≤ |X c ω|
    have : 0 ≤ √(2 * ((0 : ℕ) : ℝ)) * Real.log (b / a) := by positivity
    linarith
  · have : NeZero d := ⟨hd.ne'⟩
    obtain ⟨L, hL0, hbs⟩ := exists_bandSup_bounds (d := d) hκ
    set c₂ : ℝ := d * Real.log (2 * R + 1) with hc₂
    have hc₂0 : 0 ≤ c₂ := mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by linarith))
    set c₅ : ℝ := √(2 * (1 + c₂)) + 2 * √(Real.pi ^ 2 * (√(d : ℝ) ^ 2 * L) / 8) * √(d : ℝ) with hc₅
    set c₆ : ℝ := Osc.blockConst d L √(d : ℝ) + 2 * √(Real.pi ^ 2 * (√(d : ℝ) ^ 2 * L) / 8) *
      √(1 + c₂) with hc₆
    have hc₅0 : 0 ≤ c₅ := by positivity
    have hc₆0 : 0 ≤ c₆ := by
      have := Osc.blockConst_nonneg d (L := L) (Real.sqrt_nonneg (d : ℝ))
      positivity
    refine ⟨c₅ + c₆, by positivity, fun {Ω} _ {P} {W} hW {a b} ha hab {X} hX c {u} hu => ?_⟩
    have := hW.isProbabilityMeasure
    set v : ℝ := Real.log (b / a) with hvdef
    have hv0 : 0 ≤ v := Real.log_nonneg ((one_le_div ha).2 hab)
    rcases hv0.eq_or_lt with hv | hv
    · -- `v = 0`: the bound is `2`
      have e : 2 * Real.exp (-u ^ 2 / (2 * v)) = 2 := by
        rw [← hv]
        simp
      rw [e]
      refine prob_le_one.trans ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    · have hb : 0 < b := ha.trans_le hab
      obtain ⟨-, -, -, htail⟩ := hbs hW ha hab hX hv le_rfl c (R := R * b) (by positivity)
      set M : ℝ := SupB.supMean d L v (d * Real.log (2 * (R * b) / a + 1)) with hM
      have hMle : M ≤ √(2 * d) * v + c₅ * √v + c₆ := by
        have hℓ : (d : ℝ) * Real.log (2 * (R * b) / a + 1) ≤ d * v + c₂ := by
          have h := log_two_mul_div_add_one_le ha hab hR
          have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          calc (d : ℝ) * Real.log (2 * (R * b) / a + 1)
              ≤ d * (v + Real.log (2 * R + 1)) := mul_le_mul_of_nonneg_left h hd0
            _ = d * v + c₂ := by rw [hc₂]; ring
        exact (SupB.supMean_mono d le_rfl hℓ).trans (supMean_le_sharp d hv0 hc₂0)
      have hsq : 0 ≤ √v := Real.sqrt_nonneg v
      set u' : ℝ := u + (√(2 * d) * v + (c₅ + c₆) * √v + (c₅ + c₆) - M) with hu'
      have hc6le : c₆ ≤ c₆ * √v + (c₅ + c₆) := by nlinarith
      have huu' : u ≤ u' := by
        rw [hu']
        nlinarith
      have h := htail (u := u') (hu.trans huu')
      have hthr : M + u' = √(2 * d) * v + (c₅ + c₆) * √v + (c₅ + c₆) + u := by
        rw [hu']
        ring
      calc P {ω | ∃ z ∈ cbox c (R * b), √(2 * d) * v + (c₅ + c₆) * √v + (c₅ + c₆) + u < |X z ω|}
          = P {ω | ∃ z ∈ Osc.box c (R * b), M + u' < |X z ω|} := by rw [hthr]; rfl
        _ ≤ ENNReal.ofReal (2 * Real.exp (-u' ^ 2 / (2 * v))) := h
        _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * v))) :=
            ENNReal.ofReal_le_ofReal (two_mul_exp_neg_sq_div_le hv0 hu huu')

/-- **Exponential tail of the sharp supremum** (DGZ Lemma 2.3 (3)–(4), MA7 D-4.2): for every
`A > √(2d)` and `R ≥ 0` there is `C > 0`, depending only on `d`, `κ`, `A` and `R`, such that for
every continuous version `X` of `H_{a,b}` (`0 < a ≤ b`, `v = log(b/a)`) and every centre `c`,
`P[∃ z ∈ B̄_{R b}(c), A v < |X z|] ≤ C e^{-v/C}`. -/
theorem exists_sup_cbox_tail {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {A : ℝ}
    (hA : √(2 * d) < A) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ a b X → ∀ c : Rd d,
        P {ω | ∃ z ∈ cbox c (R * b), A * Real.log (b / a) < |X z ω|} ≤
          ENNReal.ofReal (C * Real.exp (-Real.log (b / a) / C)) := by
  obtain ⟨C₁, hC₁, htail⟩ := exists_sup_cbox_gaussian_tail (d := d) hκ hR
  set g : ℝ := A - √(2 * d) with hg
  have hg0 : 0 < g := by rw [hg]; linarith
  set v₀ : ℝ := (4 * C₁ / g) ^ 2 + 4 * C₁ / g + 1 with hv₀
  have hv₀0 : 0 < v₀ := by positivity
  set C : ℝ := max (max 2 (8 / g ^ 2)) (v₀ + 1) with hC
  have hC2 : 2 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCg : 8 / g ^ 2 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCv : v₀ + 1 ≤ C := le_max_right _ _
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC0, fun {Ω} _ {P} {W} hW {a b} ha hab {X} hX c => ?_⟩
  have := hW.isProbabilityMeasure
  set v : ℝ := Real.log (b / a) with hvdef
  have hv0 : 0 ≤ v := Real.log_nonneg ((one_le_div ha).2 hab)
  rcases lt_or_ge v v₀ with hvv | hvv
  · -- small `v`: the bound is at least `1`
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := Real.add_one_le_exp (-v / C)
    have h2 : C * (-v / C + 1) = C - v := by field_simp; ring
    nlinarith
  · -- large `v`: Gaussian tail with excess `≥ g v / 2`
    have hvpos : 0 < v := hv₀0.trans_le hvv
    have hsq : 0 ≤ √v := Real.sqrt_nonneg v
    have hsqv : √v * √v = v := Real.mul_self_sqrt hv0
    have hq0 : 0 ≤ 4 * C₁ / g := by positivity
    have hvv' : (4 * C₁ / g) ^ 2 + 4 * C₁ / g + 1 ≤ v := by rw [← hv₀]; exact hvv
    have hs1 : 4 * C₁ / g ≤ √v := by
      rw [← Real.sqrt_sq hq0]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hC1v : C₁ * √v ≤ g * v / 4 := by
      have h := mul_le_mul_of_nonneg_right hs1 hsq
      rw [hsqv, div_mul_eq_mul_div, div_le_iff₀ hg0] at h
      nlinarith
    have hC1 : C₁ ≤ g * v / 4 := by
      have h : 4 * C₁ / g ≤ v := by nlinarith
      rw [div_le_iff₀ hg0] at h
      linarith
    set u : ℝ := A * v - (√(2 * d) * v + C₁ * √v + C₁) with hu
    have hu2 : g * v / 2 ≤ u := by rw [hu, hg]; nlinarith
    have hu0 : 0 ≤ u := le_trans (by positivity) hu2
    have h := htail hW ha hab hX c hu0
    have hthr : √(2 * d) * v + C₁ * √v + C₁ + u = A * v := by rw [hu]; ring
    rw [hthr] at h
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 := two_mul_exp_neg_sq_div_le hv0 (by positivity) hu2
    have e : -(g * v / 2) ^ 2 / (2 * v) = -(g ^ 2 / 8) * v := by
      field_simp
      ring
    rw [e] at h3
    refine h3.trans ?_
    have h4 : -(g ^ 2 / 8) * v ≤ -v / C := by
      have h5 : 1 / C ≤ g ^ 2 / 8 := by
        rw [div_le_iff₀ hC0]
        rw [div_le_iff₀ (by positivity)] at hCg
        nlinarith
      have h6 : v / C ≤ g ^ 2 / 8 * v := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right h5 hv0
      have e2 : -v / C = -(v / C) := by ring
      rw [e2]
      linarith
    calc 2 * Real.exp (-(g ^ 2 / 8) * v) ≤ 2 * Real.exp (-v / C) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h4) (by norm_num)
      _ ≤ C * Real.exp (-v / C) := mul_le_mul_of_nonneg_right hC2 (Real.exp_pos _).le

/-- `log(1 / 2^{-n}) = n log 2`. -/
theorem log_one_div_inv_two_pow (n : ℕ) : Real.log (1 / (2 : ℝ)⁻¹ ^ n) = n * Real.log 2 := by
  rw [one_div, inv_pow, inv_inv, Real.log_pow]

/-- **The event `𝒢_n` of DGZ (4.6) is likely** (DGZ Lemma 4.2(1), first inequality; MA7 D-4.2,
§5 row L3b2): for `ξ > 0` and `η < ξ (Q - √(2d))` (DGZ (4.3)) there is `C > 0`, depending only on
`d`, `κ`, `ξ`, `Q` and `η`, such that for every white noise, every `n` and every continuous version
`h_n` of `H_{2^{-n},1}`,
`P[sup_{z ∈ B̄₃(0)} h_n(z) > n (Q - η/ξ) log 2] ≤ C e^{-n/C}`. -/
theorem prob_sharpSup_compl_le {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ Q η : ℝ} (hξ : 0 < ξ)
    (hη : η < ξ * (Q - √(2 * d))) :
    ∃ C > 0, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
      IsWhiteNoise P W → ∀ (n : ℕ) {X : Rd d → Ω → ℝ},
      IsBandVersion P W κ ((2 : ℝ)⁻¹ ^ n) 1 X →
        P {ω | ∃ z ∈ cbox (0 : Rd d) 3, (n : ℝ) * (Q - η / ξ) * Real.log 2 < X z ω} ≤
          ENNReal.ofReal (C * Real.exp (-(n : ℝ) / C)) := by
  have hA : √(2 * d) < Q - η / ξ := by
    have h : η / ξ < Q - √(2 * d) := by
      rw [div_lt_iff₀ hξ]
      linarith
    linarith
  obtain ⟨C, hC0, htail⟩ := exists_sup_cbox_tail (d := d) hκ hA (R := 3) (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C / Real.log 2, by positivity, fun {Ω} _ {P} {W} hW n {X} hX => ?_⟩
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hab : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h := htail hW ha hab hX 0
  rw [log_one_div_inv_two_pow, mul_one] at h
  refine (measure_mono fun ω hω => ?_).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  · obtain ⟨z, hz, hlt⟩ := hω
    refine ⟨z, hz, ?_⟩
    have e : (Q - η / ξ) * ((n : ℝ) * Real.log 2) = (n : ℝ) * (Q - η / ξ) * Real.log 2 := by ring
    rw [e]
    exact hlt.trans_le (le_abs_self _)
  · have e : -((n : ℝ) * Real.log 2) / C = -(n : ℝ) / (C / Real.log 2) := by
      field_simp
    rw [e]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [le_div_iff₀ hlog2]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    nlinarith

end HigherDimLQGMetric.DGZ
