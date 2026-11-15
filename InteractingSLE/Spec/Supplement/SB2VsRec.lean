/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VrStopAe
import InteractingSLE.Spec.Supplement.GW2BhRule

/-!
# A record encoding a function on the closed upper half-plane (D19, step 4's record)

Packet PROVE-AUX61-NOJUMP (decision D19). SB2(1)'s stops are record-path rules; the record carries one function `φ` on
the closed upper half-plane (the stop gauge), encoded by its values at the rational grid points of `ℍ`:

* `gridPt`, `gridCode`, **`recFun φ`**: the grid values of `φ` as a rational code `ℚ → ℝ`; `recFun_code`;
  `measurable_recFun` (pointwise measurable families give measurable codes);
* `approx n z`: a grid point of `ℍ` within `2/(n+1)` of `z` (above it); **`decode r z`**: the limit of the code along
  the approximants; **`measurable_decode`** (jointly in record and point);
* **`decode_recFun`**: for `φ` continuous at `z` within the closed half-plane, `decode (recFun φ) z = φ z`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vs

open Exist.StagedLaw

/-- The grid point of a pair of rationals. -/
def gridPt (p : ℚ × ℚ) : ℂ := ((p.1 : ℝ) : ℂ) + ((p.2 : ℝ) : ℂ) * Complex.I

/-- The rational code of a grid point. -/
def gridCode (p : ℚ × ℚ) : ℚ := (Encodable.encode p : ℚ)

theorem gridCode_injective : Function.Injective gridCode := fun p p' h => by
  unfold gridCode at h
  exact Encodable.encode_injective (by exact_mod_cast h)

open Classical in
/-- **The grid code of a function.** -/
def recFun (φ : ℂ → ℝ) (q : ℚ) : ℝ := if h : ∃ p, gridCode p = q then φ (gridPt h.choose) else 0

theorem recFun_code (φ : ℂ → ℝ) (p : ℚ × ℚ) : recFun φ (gridCode p) = φ (gridPt p) := by
  have h : ∃ p', gridCode p' = gridCode p := ⟨p, rfl⟩
  simp only [recFun, h, dite_true]
  rw [gridCode_injective h.choose_spec]

theorem measurable_recFun {Ω : Type*} {m : MeasurableSpace Ω} {φ : Ω → ℂ → ℝ}
    (hφ : ∀ z, Measurable fun ω => φ ω z) : Measurable fun ω => recFun (φ ω) := by
  classical
  refine measurable_pi_iff.mpr fun q => ?_
  by_cases h : ∃ p, gridCode p = q
  · simp only [recFun, h, dite_true]
    exact hφ _
  · simp only [recFun, h, dite_false]
    exact measurable_const

/-- The approximant of `z` at level `n`: a grid point of `ℍ` above and near `z`. -/
def approx (n : ℕ) (z : ℂ) : ℚ × ℚ :=
  ((⌊((n : ℝ) + 1) * z.re⌋ : ℚ) / ((n : ℚ) + 1), ((⌊((n : ℝ) + 1) * z.im⌋ : ℚ) + 1) / ((n : ℚ) + 1))

/-- **The decoder**: the limit of the code along the approximants. -/
def decode (r : RecData) (z : ℂ) : ℝ := limUnder atTop fun n => r.1 (gridCode (approx n z))

theorem gridPt_re (p : ℚ × ℚ) : (gridPt p).re = (p.1 : ℝ) := by
  simp only [gridPt, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]

theorem gridPt_im (p : ℚ × ℚ) : (gridPt p).im = (p.2 : ℝ) := by
  simp only [gridPt, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]

theorem approx_re (n : ℕ) (z : ℂ) :
    (gridPt (approx n z)).re = (⌊((n : ℝ) + 1) * z.re⌋ : ℝ) / ((n : ℝ) + 1) := by
  rw [gridPt_re]; simp only [approx]; push_cast; ring

theorem approx_im (n : ℕ) (z : ℂ) :
    (gridPt (approx n z)).im = ((⌊((n : ℝ) + 1) * z.im⌋ : ℝ) + 1) / ((n : ℝ) + 1) := by
  rw [gridPt_im]; simp only [approx]; push_cast; ring

theorem approx_snd_pos {n : ℕ} {z : ℂ} (hz : 0 ≤ z.im) : (0 : ℝ) < ((approx n z).2 : ℝ) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h0 : (0 : ℤ) ≤ ⌊((n : ℝ) + 1) * z.im⌋ := Int.floor_nonneg.2 (by positivity)
  have : ((approx n z).2 : ℝ) = ((⌊((n : ℝ) + 1) * z.im⌋ : ℝ) + 1) / ((n : ℝ) + 1) := by
    simp only [approx]; push_cast; ring
  rw [this]
  have h0' : (0 : ℝ) ≤ (⌊((n : ℝ) + 1) * z.im⌋ : ℝ) := by exact_mod_cast h0
  positivity

/-- A floor quotient is within `1/N` below its argument. -/
theorem floor_div_near {N x : ℝ} (hN : 0 < N) : |(⌊N * x⌋ : ℝ) / N - x| ≤ 1 / N := by
  have h1 := Int.floor_le (N * x)
  have h2 := Int.lt_floor_add_one (N * x)
  have e1 : (⌊N * x⌋ : ℝ) / N ≤ x := by rw [div_le_iff₀ hN]; linarith
  have e2 : x ≤ (⌊N * x⌋ : ℝ) / N + 1 / N := by rw [← add_div, le_div_iff₀ hN]; linarith
  have e3 : 0 < 1 / N := by positivity
  rw [abs_le]; constructor <;> linarith

theorem dist_approx_le (n : ℕ) (z : ℂ) : dist (gridPt (approx n z)) z ≤ 2 / ((n : ℝ) + 1) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hre : |(gridPt (approx n z)).re - z.re| ≤ 1 / ((n : ℝ) + 1) := by
    rw [approx_re]; exact floor_div_near hN
  have him : |(gridPt (approx n z)).im - z.im| ≤ 1 / ((n : ℝ) + 1) := by
    rw [approx_im, add_div]
    have h := floor_div_near (x := z.im) hN
    have e : (⌊((n : ℝ) + 1) * z.im⌋ : ℝ) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) - z.im =
        ((⌊((n : ℝ) + 1) * z.im⌋ : ℝ) / ((n : ℝ) + 1) - z.im) + 1 / ((n : ℝ) + 1) := by ring
    rw [e]
    have h1 := Int.floor_le (((n : ℝ) + 1) * z.im)
    have e1 : (⌊((n : ℝ) + 1) * z.im⌋ : ℝ) / ((n : ℝ) + 1) ≤ z.im := by rw [div_le_iff₀ hN]; linarith
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  rw [Complex.dist_eq]
  calc ‖gridPt (approx n z) - z‖ ≤ |(gridPt (approx n z) - z).re| + |(gridPt (approx n z) - z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
        simp only [Complex.sub_re, Complex.sub_im]; exact add_le_add hre him
    _ = 2 / ((n : ℝ) + 1) := by ring

theorem tendsto_approx {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto (fun n => gridPt (approx n z)) atTop (𝓝[{w | 0 ≤ w.im}] z) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (dist_approx_le · z) ?_)
    have h := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 1)
    refine h.congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  · show 0 ≤ (gridPt (approx n z)).im
    rw [gridPt_im]; exact (approx_snd_pos hz).le

/-- **Decoding a continuous function from its grid code.** -/
theorem decode_eq {φ : ℂ → ℝ} {r : RecData} {z : ℂ} (hz : 0 ≤ z.im)
    (hφ : ContinuousWithinAt φ {w | 0 ≤ w.im} z) (hr : ∀ p : ℚ × ℚ, (0 : ℝ) < p.2 → r.1 (gridCode p) = φ (gridPt p)) :
    decode r z = φ z := by
  have hseq : (fun n => r.1 (gridCode (approx n z))) = fun n => φ (gridPt (approx n z)) :=
    funext fun n => hr _ (approx_snd_pos hz)
  unfold decode
  rw [hseq]
  exact (hφ.tendsto.comp (tendsto_approx hz)).limUnder_eq

theorem decode_recFun {φ : ℂ → ℝ} {z : ℂ} (hz : 0 ≤ z.im) (hφ : ContinuousWithinAt φ {w | 0 ≤ w.im} z)
    (e : ℝ≥0∞ × Bool) : decode (recFun φ, e) z = φ z :=
  decode_eq hz hφ fun p _ => recFun_code φ p

theorem measurable_approx (n : ℕ) : Measurable (approx n) := by
  unfold approx
  refine Measurable.prodMk ?_ ?_
  · exact (measurable_of_countable (fun k : ℤ => (k : ℚ) / ((n : ℚ) + 1))).comp
      ((measurable_const.mul Complex.measurable_re).floor)
  · exact (measurable_of_countable (fun k : ℤ => ((k : ℚ) + 1) / ((n : ℚ) + 1))).comp
      ((measurable_const.mul Complex.measurable_im).floor)

theorem measurable_decode : Measurable fun x : RecData × ℂ => decode x.1 x.2 := by
  have hF : Measurable fun y : RecData × (ℚ × ℚ) => y.1.1 (gridCode y.2) :=
    measurable_from_prod_countable_left fun p => (measurable_pi_apply (gridCode p)).comp measurable_fst
  have hseq : ∀ n, Measurable fun x : RecData × ℂ => x.1.1 (gridCode (approx n x.2)) := fun n =>
    hF.comp (measurable_fst.prodMk ((measurable_approx n).comp measurable_snd))
  exact (StronglyMeasurable.limUnder fun n => (hseq n).stronglyMeasurable).measurable

end InteractingSLE.Theorem14.SB.Vs
