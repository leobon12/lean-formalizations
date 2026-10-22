import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Signed box indicators (packet F2, target 1, part 2)

Elementary real analysis for the antiderivative field of the white-noise realization of the LGF
(port of LQGMetric's `Field/ExistRect.lean`, `sgnInd`/`rectInd`, from rectangles in `ℂ` to boxes in
`ℝ^n`):

* `sgnInd a t = 1_{t ≤ a} − 1_{t ≤ 0}`, the oriented indicator of `t` between `0` and `a`
  (`= 1_{(0,a]}(t)` for `a ≥ 0`, `= −1_{(a,0]}(t)` for `a ≤ 0`): `sgnInd_sub_sgnInd`
  (`sgnInd b − sgnInd a = 1_{(a,b]}` for `a ≤ b`), `integral_sgnInd` (`∫ sgnInd a = a`),
  `integral_abs_sgnInd_sub` (`∫ |sgnInd a − sgnInd b| = |a − b|`);
* `boxIndF q u = ∏ᵢ sgnInd (q i) (u i)` on `Fin n → ℝ`: `integral_boxIndF` (`∫ boxIndF q = ∏ᵢ qᵢ`),
  the support bound `boxIndF_eq_zero`, and the `L¹` increment bound `integral_abs_boxIndF_sub_le`
  (`∫ |boxIndF q − boxIndF q'| ≤ max (2R) 1 ^ n ∑ᵢ |qᵢ − q'ᵢ|` when `|qᵢ|, |q'ᵢ| ≤ R`);
* `abs_prod_sub_prod_le_pow`: `|∏ aᵢ − ∏ bᵢ| ≤ max C 1 ^ |s| ∑ |aᵢ − bᵢ|` when `|aᵢ|, |bᵢ| ≤ C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace HigherDimLQGMetric

/-! ## A telescoping bound for products -/

/-- `|∏ aᵢ − ∏ bᵢ| ≤ max C 1 ^ |s| ∑ᵢ |aᵢ − bᵢ|` when all `|aᵢ|, |bᵢ| ≤ C`. -/
theorem abs_prod_sub_prod_le_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ) {C : ℝ}
    (ha : ∀ i ∈ s, |a i| ≤ C) (hb : ∀ i ∈ s, |b i| ≤ C) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ max C 1 ^ s.card * ∑ i ∈ s, |a i - b i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have ha' : ∀ i ∈ s, |a i| ≤ C := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hb' : ∀ i ∈ s, |b i| ≤ C := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hC1 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
    have hC0 : (0 : ℝ) ≤ max C 1 := zero_le_one.trans hC1
    have hA : |∏ i ∈ s, a i| ≤ max C 1 ^ s.card := by
      rw [Finset.abs_prod]
      calc ∏ i ∈ s, |a i| ≤ ∏ _i ∈ s, max C 1 :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i hi => (ha' i hi).trans
              (le_max_left _ _)
        _ = max C 1 ^ s.card := Finset.prod_const _
    have hbk : |b k| ≤ max C 1 := (hb k (Finset.mem_insert_self k s)).trans (le_max_left _ _)
    have hsum : 0 ≤ ∑ i ∈ s, |a i - b i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.sum_insert hk,
      Finset.card_insert_of_notMem hk]
    have e : a k * ∏ i ∈ s, a i - b k * ∏ i ∈ s, b i =
        (a k - b k) * ∏ i ∈ s, a i + b k * (∏ i ∈ s, a i - ∏ i ∈ s, b i) := by ring
    rw [e]
    calc |(a k - b k) * ∏ i ∈ s, a i + b k * (∏ i ∈ s, a i - ∏ i ∈ s, b i)|
        ≤ |a k - b k| * |∏ i ∈ s, a i| + |b k| * |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |a k - b k| * max C 1 ^ s.card + max C 1 * (max C 1 ^ s.card * ∑ i ∈ s, |a i - b i|) :=
          add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _))
            (mul_le_mul hbk (ih ha' hb') (abs_nonneg _) hC0)
      _ ≤ max C 1 ^ (s.card + 1) * (|a k - b k| + ∑ i ∈ s, |a i - b i|) := by
          rw [pow_succ, mul_add]
          have hX := pow_nonneg hC0 s.card
          have hD := abs_nonneg (a k - b k)
          have h1 : |a k - b k| * max C 1 ^ s.card ≤
              max C 1 ^ s.card * max C 1 * |a k - b k| := by
            have := mul_nonneg (sub_nonneg.2 hC1) (mul_nonneg hX hD)
            nlinarith
          have h2 : max C 1 * (max C 1 ^ s.card * ∑ i ∈ s, |a i - b i|) =
              max C 1 ^ s.card * max C 1 * ∑ i ∈ s, |a i - b i| := by ring
          linarith

/-! ## Signed indicators on the line -/

/-- `sgnInd a t = 1_{t ≤ a} − 1_{t ≤ 0}`: the oriented indicator of `t` between `0` and `a`. -/
def sgnInd (a t : ℝ) : ℝ := (Iic a).indicator 1 t - (Iic 0).indicator 1 t

theorem measurable_sgnInd₂ : Measurable fun p : ℝ × ℝ => sgnInd p.1 p.2 := by
  have e : (fun p : ℝ × ℝ => sgnInd p.1 p.2) =
      {p : ℝ × ℝ | p.2 ≤ p.1}.indicator 1 - {p : ℝ × ℝ | p.2 ≤ 0}.indicator 1 := by
    funext p
    simp only [sgnInd, Pi.sub_apply, indicator, mem_Iic, mem_ofPred_eq, Pi.one_apply]
  rw [e]
  exact (measurable_one.indicator (measurableSet_le measurable_snd measurable_fst)).sub
    (measurable_one.indicator (measurableSet_le measurable_snd measurable_const))

theorem measurable_sgnInd (a : ℝ) : Measurable (sgnInd a) := by
  have h := measurable_sgnInd₂.comp ((measurable_const (a := a)).prodMk (measurable_id (α := ℝ)))
  exact h

theorem sgnInd_zero_left (t : ℝ) : sgnInd 0 t = 0 := sub_self _

/-- `sgnInd b − sgnInd a = 1_{(a, b]}` for `a ≤ b`. -/
theorem sgnInd_sub_sgnInd {a b : ℝ} (hab : a ≤ b) (t : ℝ) :
    sgnInd b t - sgnInd a t = (Ioc a b).indicator 1 t := by
  simp only [sgnInd, indicator, mem_Iic, mem_Ioc, Pi.one_apply]
  by_cases h1 : t ≤ a
  · have h2 : t ≤ b := h1.trans hab
    have h3 : ¬a < t := not_lt.2 h1
    simp only [h1, h2, h3, false_and, ite_true, ite_false]
    ring
  · have h3 : a < t := not_le.1 h1
    by_cases h2 : t ≤ b
    · simp only [h1, h2, h3, and_self, ite_true, ite_false]
      ring
    · simp only [h1, h2, h3, and_false, ite_false]
      ring

theorem sgnInd_of_nonneg {a : ℝ} (ha : 0 ≤ a) (t : ℝ) : sgnInd a t = (Ioc 0 a).indicator 1 t := by
  rw [← sgnInd_sub_sgnInd ha t, sgnInd_zero_left, sub_zero]

theorem sgnInd_of_nonpos {a : ℝ} (ha : a ≤ 0) (t : ℝ) :
    sgnInd a t = -(Ioc a 0).indicator 1 t := by
  rw [← sgnInd_sub_sgnInd ha t, sgnInd_zero_left, zero_sub, neg_neg]

theorem abs_sgnInd_le_one (a t : ℝ) : |sgnInd a t| ≤ 1 := by
  rcases le_total 0 a with ha | ha
  · rw [sgnInd_of_nonneg ha]
    by_cases ht : t ∈ Ioc 0 a
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]
  · rw [sgnInd_of_nonpos ha, abs_neg]
    by_cases ht : t ∈ Ioc a 0
    · simp [indicator_of_mem ht]
    · simp [indicator_of_notMem ht]

/-- `sgnInd a t = 0` when `|a| < |t|`. -/
theorem sgnInd_eq_zero_of_abs_lt {a t : ℝ} (h : |a| < |t|) : sgnInd a t = 0 := by
  rcases le_total 0 a with ha | ha
  · rw [sgnInd_of_nonneg ha, indicator_of_notMem]
    rintro ⟨h1, h2⟩
    rw [abs_of_nonneg ha, abs_of_pos h1] at h
    exact absurd h2 (not_le.2 h)
  · rw [sgnInd_of_nonpos ha, indicator_of_notMem, neg_zero]
    rintro ⟨h1, h2⟩
    rw [abs_of_nonpos ha, abs_of_nonpos h2] at h
    linarith

theorem integrable_sgnInd (a : ℝ) : Integrable (sgnInd a) := by
  rcases le_total 0 a with ha | ha
  · rw [show sgnInd a = (Ioc 0 a).indicator 1 from funext (sgnInd_of_nonneg ha)]
    exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const measure_Ioc_lt_top.ne)
  · rw [show sgnInd a = -(Ioc a 0).indicator 1 from funext fun t => by
      rw [sgnInd_of_nonpos ha]; rfl]
    exact ((integrable_indicator_iff measurableSet_Ioc).2
      (integrableOn_const measure_Ioc_lt_top.ne)).neg

/-- `∫ sgnInd a = a`. -/
theorem integral_sgnInd (a : ℝ) : ∫ t, sgnInd a t = a := by
  rcases le_total 0 a with ha | ha
  · simp_rw [sgnInd_of_nonneg ha]
    rw [integral_indicator_one measurableSet_Ioc, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), sub_zero]
  · simp_rw [sgnInd_of_nonpos ha]
    rw [integral_neg, integral_indicator_one measurableSet_Ioc, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    ring

/-- `∫ |sgnInd a − sgnInd b| = |a − b|`. -/
theorem integral_abs_sgnInd_sub (a b : ℝ) : ∫ t, |sgnInd a t - sgnInd b t| = |a - b| := by
  rcases le_total a b with hab | hab
  · have e : ∀ t, |sgnInd a t - sgnInd b t| = (Ioc a b).indicator 1 t := fun t => by
      rw [abs_sub_comm, sgnInd_sub_sgnInd hab]
      by_cases ht : t ∈ Ioc a b
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    simp_rw [e]
    rw [integral_indicator_one measurableSet_Ioc, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
  · have e : ∀ t, |sgnInd a t - sgnInd b t| = (Ioc b a).indicator 1 t := fun t => by
      rw [sgnInd_sub_sgnInd hab]
      by_cases ht : t ∈ Ioc b a
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht]
    simp_rw [e]
    rw [integral_indicator_one measurableSet_Ioc, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), abs_of_nonneg (by linarith)]

/-! ## Box indicators on `Fin n → ℝ` -/

variable {n : ℕ}

/-- The signed indicator of the box between `0` and `q`: `∏ᵢ sgnInd (q i) (u i)`. -/
def boxIndF (q u : Fin n → ℝ) : ℝ := ∏ i, sgnInd (q i) (u i)

theorem measurable_boxIndF₂ :
    Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => boxIndF p.1 p.2 := by
  have h : ∀ i : Fin n, Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) => (p.1 i, p.2 i) :=
    fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_sgnInd₂.comp (h i) : Measurable fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      sgnInd (p.1 i) (p.2 i))

theorem measurable_boxIndF (q : Fin n → ℝ) : Measurable (boxIndF q) := by
  have h := (measurable_boxIndF₂ (n := n)).comp
    ((measurable_const (a := q)).prodMk (measurable_id (α := Fin n → ℝ)))
  exact h

theorem measurable_boxIndF_left (u : Fin n → ℝ) : Measurable fun q : Fin n → ℝ => boxIndF q u := by
  have h := (measurable_boxIndF₂ (n := n)).comp
    ((measurable_id (α := Fin n → ℝ)).prodMk (measurable_const (a := u)))
  exact h

theorem abs_boxIndF_le_one (q u : Fin n → ℝ) : |boxIndF q u| ≤ 1 := by
  rw [boxIndF, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => abs_sgnInd_le_one _ _

theorem boxIndF_eq_zero {q u : Fin n → ℝ} {i : Fin n} (h : |q i| < |u i|) : boxIndF q u = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ i) (sgnInd_eq_zero_of_abs_lt h)

/-- `∫ boxIndF q = ∏ᵢ qᵢ`. -/
theorem integral_boxIndF (q : Fin n → ℝ) : ∫ u, boxIndF q u = ∏ i, q i := by
  unfold boxIndF
  rw [volume_pi, integral_fintype_prod_eq_prod (f := fun i t => sgnInd (q i) t)]
  simp only [integral_sgnInd]

/-- The indicator of `[-R, R]`. -/
def cutInd (R : ℝ) : ℝ → ℝ := (Icc (-R) R).indicator 1

theorem cutInd_nonneg (R t : ℝ) : 0 ≤ cutInd R t := by
  unfold cutInd
  by_cases ht : t ∈ Icc (-R) R
  · rw [indicator_of_mem ht]; exact zero_le_one
  · rw [indicator_of_notMem ht]

theorem cutInd_of_abs_le {R t : ℝ} (ht : |t| ≤ R) : cutInd R t = 1 := by
  unfold cutInd
  rw [indicator_of_mem (show t ∈ Icc (-R) R from abs_le.1 ht)]
  rfl

theorem integrable_cutInd (R : ℝ) : Integrable (cutInd R) :=
  (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const measure_Icc_lt_top.ne)

theorem integral_cutInd_le (R : ℝ) : ∫ t, cutInd R t ≤ max (2 * R) 1 := by
  unfold cutInd
  rw [integral_indicator_one measurableSet_Icc, Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal']
  exact max_le (le_max_of_le_left (by linarith)) (le_max_of_le_right zero_le_one)

/-- The dominating product functions: coordinate `i` carries `|sgnInd qᵢ − sgnInd q'ᵢ|`, the other
coordinates the cutoff `1_{[-R,R]}`. -/
def boxDom (R : ℝ) (q q' : Fin n → ℝ) (i : Fin n) : Fin n → ℝ → ℝ :=
  Function.update (fun _ => cutInd R) i fun t => |sgnInd (q i) t - sgnInd (q' i) t|

theorem boxDom_nonneg (R : ℝ) (q q' : Fin n → ℝ) (i j : Fin n) (t : ℝ) :
    0 ≤ boxDom R q q' i j t := by
  unfold boxDom
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; exact abs_nonneg _
  · rw [Function.update_of_ne hj]; exact cutInd_nonneg R t

theorem integrable_boxDom (R : ℝ) (q q' : Fin n → ℝ) (i j : Fin n) :
    Integrable (boxDom R q q' i j) := by
  unfold boxDom
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]
    exact ((integrable_sgnInd _).sub (integrable_sgnInd _)).abs
  · rw [Function.update_of_ne hj]; exact integrable_cutInd R

theorem prod_integral_boxDom_le (R : ℝ) (q q' : Fin n → ℝ) (i : Fin n) :
    ∏ j, ∫ t, boxDom R q q' i j t ≤ max (2 * R) 1 ^ n * |q i - q' i| := by
  classical
  have e : (fun j => ∫ t, boxDom R q q' i j t) = Function.update (fun _ => ∫ t, cutInd R t) i
      (∫ t, |sgnInd (q i) t - sgnInd (q' i) t|) := by
    funext j
    unfold boxDom
    by_cases hj : j = i
    · subst hj; simp only [Function.update_self]
    · simp only [Function.update_of_ne hj]
  rw [e, Finset.prod_update_of_mem (Finset.mem_univ i), integral_abs_sgnInd_sub,
    Finset.prod_const, mul_comm]
  have hI0 : 0 ≤ ∫ t, cutInd R t := integral_nonneg (cutInd_nonneg R)
  have hcard : (Finset.univ \ {i}).card ≤ n := by
    calc (Finset.univ \ {i}).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card Finset.sdiff_subset
      _ = n := Finset.card_fin n
  gcongr
  calc (∫ t, cutInd R t) ^ (Finset.univ \ {i}).card ≤ max (2 * R) 1 ^ (Finset.univ \ {i}).card :=
        pow_le_pow_left₀ hI0 (integral_cutInd_le R) _
    _ ≤ max (2 * R) 1 ^ n := pow_le_pow_right₀ (le_max_right _ _) hcard

theorem abs_boxIndF_sub_le_sum {q q' : Fin n → ℝ} {R : ℝ} (hq : ∀ i, |q i| ≤ R)
    (hq' : ∀ i, |q' i| ≤ R) (u : Fin n → ℝ) :
    |boxIndF q u - boxIndF q' u| ≤ ∑ i, ∏ j, boxDom R q q' i j (u j) := by
  classical
  by_cases hu : ∃ j, R < |u j|
  · obtain ⟨j, hj⟩ := hu
    rw [boxIndF_eq_zero ((hq j).trans_lt hj), boxIndF_eq_zero ((hq' j).trans_lt hj), sub_self,
      abs_zero]
    exact Finset.sum_nonneg fun i _ => Finset.prod_nonneg fun j _ => boxDom_nonneg R q q' i j _
  · have hu' : ∀ j, |u j| ≤ R := fun j => not_lt.1 fun h => hu ⟨j, h⟩
    have hprod : ∀ i, ∏ j, boxDom R q q' i j (u j) =
        |sgnInd (q i) (u i) - sgnInd (q' i) (u i)| := by
      intro i
      have e : (fun j => boxDom R q q' i j (u j)) = Function.update (fun _ => (1 : ℝ)) i
          (|sgnInd (q i) (u i) - sgnInd (q' i) (u i)|) := by
        funext j
        unfold boxDom
        by_cases hj : j = i
        · subst hj; simp only [Function.update_self]
        · simp only [Function.update_of_ne hj, cutInd_of_abs_le (hu' j)]
      rw [e, Finset.prod_update_of_mem (Finset.mem_univ i), Finset.prod_const_one, mul_one]
    simp only [hprod]
    have h := abs_prod_sub_prod_le_pow Finset.univ (fun i => sgnInd (q i) (u i))
      (fun i => sgnInd (q' i) (u i)) (C := 1) (fun i _ => abs_sgnInd_le_one _ _)
      (fun i _ => abs_sgnInd_le_one _ _)
    rw [max_self, one_pow, one_mul] at h
    exact h

theorem integrable_prod_boxDom (R : ℝ) (q q' : Fin n → ℝ) (i : Fin n) :
    Integrable fun u : Fin n → ℝ => ∏ j, boxDom R q q' i j (u j) := by
  rw [volume_pi]
  exact Integrable.fintype_prod (integrable_boxDom R q q' i)

/-- The `L¹` increment bound for box indicators. -/
theorem integral_abs_boxIndF_sub_le {q q' : Fin n → ℝ} {R : ℝ} (hq : ∀ i, |q i| ≤ R)
    (hq' : ∀ i, |q' i| ≤ R) :
    ∫ u, |boxIndF q u - boxIndF q' u| ≤ max (2 * R) 1 ^ n * ∑ i, |q i - q' i| := by
  have hint : Integrable fun u : Fin n → ℝ => ∑ i, ∏ j, boxDom R q q' i j (u j) :=
    integrable_finsetSum _ fun i _ => integrable_prod_boxDom R q q' i
  calc ∫ u, |boxIndF q u - boxIndF q' u|
      ≤ ∫ u : Fin n → ℝ, ∑ i, ∏ j, boxDom R q q' i j (u j) :=
        integral_mono_of_nonneg (ae_of_all _ fun u => abs_nonneg _) hint
          (ae_of_all _ (abs_boxIndF_sub_le_sum hq hq'))
    _ = ∑ i, ∏ j, ∫ t, boxDom R q q' i j t := by
        rw [integral_finsetSum _ fun i _ => integrable_prod_boxDom R q q' i]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [volume_pi, integral_fintype_prod_eq_prod (f := boxDom R q q' i)]
    _ ≤ ∑ i, max (2 * R) 1 ^ n * |q i - q' i| :=
        Finset.sum_le_sum fun i _ => prod_integral_boxDom_le R q q' i
    _ = max (2 * R) 1 ^ n * ∑ i, |q i - q' i| := by rw [Finset.mul_sum]

end HigherDimLQGMetric
