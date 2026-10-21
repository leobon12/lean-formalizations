import SmallGammaGeodesics.Upper.Interfaces
import SmallGammaGeodesics.Probes.Basic
import LQGMetric.Gaussian.SupTailField
import LQGMetric.Gaussian.FerniqueFinite
import GaussianLQG.Energy.LogPotential
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lemma 4.2′, Step 5: the supremum bound (b4) (blueprint `lem:coupling`)

Let `K : Ω → ℂ → ℝ` be jointly measurable, continuous on `U_j` for every `ω`, with `K(1/2) = 0`,
whose increments on `U_j` form a centred Gaussian process with
`E(K z − K w)² ≤ B min(|z − w|/s, 1 + log(1 + |z − w|/s))` whenever the closed `s`-balls about `z`
and `w` lie in `U_j` (the form delivered by `CC.NICInput`). Then `sup_{V_j} |K|` is measurable and
`E sup_{V_j} K² ≤ 10⁵ B (1 + log(1/ℓ_j))²` (`sup_bound`).

Proof (a simplification of the blueprint's Step 5, with the same ingredients):
* `V_j` is covered by the `N = 5·2^j` closed squares `Q_i` of side `ℓ/4` centred on `[-1/8, 9/8]`
  (`probeRectV_subset_iUnion_sq`); the closed `ℓ/16`-balls about points of `Q_i` and about `1/2` lie
  in `U_j`.
* On `Q_i` the process `t ↦ K(t) = K(t) − K(1/2)` is centred Gaussian with
  `E(K t − K t')² ≤ (32B/ℓ) ‖t − t'‖_∞` and `Var K(t) ≤ 4B L`, `L = 1 + log(1/ℓ)`. Dudley chaining
  (`LQGMetric.SupTail.integral_iSup_family_le`, `d = 2`, diameter `ℓ/4`) gives
  `E sup_{Q_i} (±K) ≤ M = 20√5 √(24 B)`, and Borell–TIS (`LQGMetric.SupTail.tail_iSup_abs_le`) gives
  `P(sup_{Q_i} |K| ≥ M + u) ≤ 2 exp(−u²/(8BL))`. (Chaining applies to `K` itself: Dudley's bound
  only uses the increments of a centred process, so no separate bound for the centres is needed.)
* A union bound over the `N` squares and the layer-cake lemma `lintegral_sq_le_of_tail`
  (`E A² ≤ 2m² + 6c(1 + log D)` when `P(A ≥ m + √t) ≤ D e^{−t/c}`) give the claim, since
  `1 + log(2N) ≤ 4L`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace SmallGammaGeodesics

namespace Coupling42

open LQGMetric

/-! ## A layer-cake bound for second moments -/

theorem min_one_le_rpow {x θ : ℝ} (hx : 0 ≤ x) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    min 1 x ≤ x ^ θ := by
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]
    rcases hx.lt_or_eq with hx' | hx'
    · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ x ^ θ := Real.rpow_le_rpow_of_exponent_ge hx' h hθ1
    · rw [← hx', Real.zero_rpow hθ0.ne']
  · rw [min_eq_left h]
    exact Real.one_le_rpow h hθ0.le

/-- **Second moment from a sub-Gaussian tail**: if `A ≥ 0` and `P(A ≥ m + √t) ≤ D e^{−t/c}` for
`t > 0` (`m ≥ 0`, `c > 0`, `D ≥ 1`), then `E A² ≤ 2m² + 6c(1 + log D)`. Proof: with
`Z = (A − m)⁺`, `A² ≤ 2m² + 2Z²`, `P(Z² > t) ≤ min(1, D e^{−t/c}) ≤ D^θ e^{−θt/c}` with
`θ = 1/(1 + log D)`, and `∫₀^∞ D^θ e^{−θt/c} dt = D^θ c/θ ≤ 3c(1 + log D)`. -/
theorem lintegral_sq_le_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Ω → ℝ} (hA : AEMeasurable A P) (hA0 : ∀ ω, 0 ≤ A ω)
    {m c D : ℝ} (hc : 0 < c) (hD : 1 ≤ D)
    (htail : ∀ t : ℝ, 0 < t →
      P {ω | m + Real.sqrt t ≤ A ω} ≤ ENNReal.ofReal (D * Real.exp (-t / c))) :
    ∫⁻ ω, ENNReal.ofReal (A ω ^ 2) ∂P ≤
      ENNReal.ofReal (2 * m ^ 2 + 6 * c * (1 + Real.log D)) := by
  set Z : Ω → ℝ := fun ω => max (A ω - m) 0 with hZ
  have hZ0 : ∀ ω, 0 ≤ Z ω := fun ω => le_max_right _ _
  have hZm : AEMeasurable (fun ω => Z ω ^ 2) P :=
    ((hA.sub_const m).max aemeasurable_const).pow_const 2
  have hpt : ∀ ω, ENNReal.ofReal (A ω ^ 2) ≤
      ENNReal.ofReal (2 * m ^ 2) + 2 * ENNReal.ofReal (Z ω ^ 2) := by
    intro ω
    have h1 : A ω ≤ m + Z ω := by
      have := le_max_left (A ω - m) 0
      simp only [hZ]
      linarith
    have h2 : A ω ^ 2 ≤ 2 * m ^ 2 + 2 * Z ω ^ 2 := by
      nlinarith [hA0 ω, hZ0 ω, sq_nonneg (m - Z ω)]
    calc ENNReal.ofReal (A ω ^ 2) ≤ ENNReal.ofReal (2 * m ^ 2 + 2 * Z ω ^ 2) :=
          ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (2 * m ^ 2) + 2 * ENNReal.ofReal (Z ω ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := 2) (q := Z ω ^ 2) (by norm_num), ENNReal.ofReal_ofNat]
  set θ : ℝ := 1 / (1 + Real.log D) with hθ
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one (by positivity)]
    linarith
  have hZ2 : ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂P ≤ ENNReal.ofReal (3 * c * (1 + Real.log D)) := by
    rw [lintegral_eq_lintegral_meas_lt P (Eventually.of_forall fun ω => sq_nonneg (Z ω)) hZm]
    have hbd : ∀ t ∈ Ioi (0 : ℝ),
        P {ω | t < Z ω ^ 2} ≤ ENNReal.ofReal (D ^ θ * Real.exp (-(θ / c) * t)) := by
      intro t ht
      have hsub : {ω | t < Z ω ^ 2} ⊆ {ω | m + Real.sqrt t ≤ A ω} := by
        intro ω hω
        have hω' : t < Z ω ^ 2 := hω
        show m + Real.sqrt t ≤ A ω
        have hs : Real.sqrt t < Z ω := by
          rw [← Real.sqrt_sq (hZ0 ω)]
          exact Real.sqrt_lt_sqrt (le_of_lt ht) hω'
        have hZpos : 0 < Z ω := (Real.sqrt_nonneg t).trans_lt hs
        have hZe : Z ω = A ω - m := by
          rcases le_total (A ω - m) 0 with h | h
          · exfalso
            have : Z ω = 0 := max_eq_right h
            linarith
          · exact max_eq_left h
        linarith
      have h1 : P {ω | t < Z ω ^ 2} ≤ 1 := prob_le_one
      have h2 : P {ω | t < Z ω ^ 2} ≤ ENNReal.ofReal (D * Real.exp (-t / c)) :=
        (measure_mono hsub).trans (htail t ht)
      have hx : 0 ≤ D * Real.exp (-t / c) := by positivity
      calc P {ω | t < Z ω ^ 2} ≤ min 1 (ENNReal.ofReal (D * Real.exp (-t / c))) := le_min h1 h2
        _ = ENNReal.ofReal (min 1 (D * Real.exp (-t / c))) := by
            rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
        _ ≤ ENNReal.ofReal ((D * Real.exp (-t / c)) ^ θ) :=
            ENNReal.ofReal_le_ofReal (min_one_le_rpow hx hθ0 hθ1)
        _ = ENNReal.ofReal (D ^ θ * Real.exp (-(θ / c) * t)) := by
            congr 1
            rw [Real.mul_rpow (by linarith) (Real.exp_pos _).le, ← Real.exp_mul]
            congr 2
            ring
    calc ∫⁻ t in Ioi 0, P {ω | t < Z ω ^ 2}
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (D ^ θ * Real.exp (-(θ / c) * t)) :=
          setLIntegral_mono' measurableSet_Ioi hbd
      _ = ENNReal.ofReal (D ^ θ / (θ / c)) :=
          GaussianLQG.lintegral_ofReal_mul_exp_Ioi (by positivity) (by positivity)
      _ ≤ ENNReal.ofReal (3 * c * (1 + Real.log D)) := by
          apply ENNReal.ofReal_le_ofReal
          have hDθ : D ^ θ ≤ 3 := by
            rw [Real.rpow_def_of_pos (by linarith)]
            have hle : Real.log D * θ ≤ 1 := by
              rw [hθ, mul_one_div, div_le_one (by positivity)]
              linarith
            calc Real.exp (Real.log D * θ) ≤ Real.exp 1 := Real.exp_le_exp.mpr hle
              _ ≤ 3 := Real.exp_one_lt_three.le
          have e : D ^ θ / (θ / c) = D ^ θ * (c * (1 + Real.log D)) := by
            rw [hθ]
            field_simp
          rw [e]
          have hc' : 0 ≤ c * (1 + Real.log D) := by positivity
          calc D ^ θ * (c * (1 + Real.log D)) ≤ 3 * (c * (1 + Real.log D)) :=
                mul_le_mul_of_nonneg_right hDθ hc'
            _ = 3 * c * (1 + Real.log D) := by ring
  calc ∫⁻ ω, ENNReal.ofReal (A ω ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * m ^ 2) + 2 * ENNReal.ofReal (Z ω ^ 2)) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * m ^ 2) + 2 * ∫⁻ ω, ENNReal.ofReal (Z ω ^ 2) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (by simp)]
    _ ≤ ENNReal.ofReal (2 * m ^ 2) + 2 * ENNReal.ofReal (3 * c * (1 + Real.log D)) := by
        gcongr
    _ = ENNReal.ofReal (2 * m ^ 2 + 6 * c * (1 + Real.log D)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        ring_nf

/-! ## The squares -/

/-- the number `N = 5·2^j` of squares -/
def nSq (j : ℕ) : ℕ := 5 * 2 ^ j

/-- the centre `x_i = -1/8 + (i + 1/2) ℓ_j/4` of the `i`th square -/
def sqC (j i : ℕ) : ℝ := -1 / 8 + ((i : ℝ) + 1 / 2) * (ell j / 4)

/-- the closed square `Q_i = [x_i − ℓ/8, x_i + ℓ/8] × [−ℓ/8, ℓ/8]` -/
def sq (j i : ℕ) : Set ℂ :=
  Icc (sqC j i - ell j / 8) (sqC j i + ell j / 8) ×ℂ Icc (-(ell j / 8)) (ell j / 8)

theorem nSq_mul_ell (j : ℕ) : (nSq j : ℝ) * (ell j / 4) = 5 / 4 := by
  have h := ell_mul_pow j
  unfold nSq
  push_cast
  linear_combination (5 / 4 : ℝ) * h

theorem sqC_bounds {j i : ℕ} (hi : i < nSq j) :
    -1 / 8 + ell j / 8 ≤ sqC j i ∧ sqC j i ≤ 9 / 8 - ell j / 8 := by
  have hℓ := ell_pos j
  have hN := nSq_mul_ell j
  have hi' : (i : ℝ) + 1 ≤ nSq j := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  unfold sqC
  constructor
  · nlinarith
  · nlinarith

theorem mem_sq {j i : ℕ} {z : ℂ} :
    z ∈ sq j i ↔ |z.re - sqC j i| ≤ ell j / 8 ∧ |z.im| ≤ ell j / 8 := by
  rw [sq, Complex.mem_reProdIm, mem_Icc, mem_Icc, abs_le, abs_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩

theorem isCompact_sq (j i : ℕ) : IsCompact (sq j i) :=
  isCompact_Icc.reProdIm isCompact_Icc

theorem sqC_mem_sq (j i : ℕ) : ((sqC j i : ℝ) : ℂ) ∈ sq j i := by
  rw [mem_sq, Complex.ofReal_re, Complex.ofReal_im, sub_self, abs_zero]
  have := ell_pos j
  constructor <;> positivity

/-- closed `ℓ/16`-balls about points of `Q_i` lie in `U_j` -/
theorem closedBall_sq_subset {j i : ℕ} (hi : i < nSq j) {z : ℂ} (hz : z ∈ sq j i) :
    closedBall z (ell j / 16) ⊆ probeRectU j := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre : |w.re - z.re| ≤ ell j / 16 := by
    rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans hw
  have him : |w.im - z.im| ≤ ell j / 16 := by
    rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans hw
  rw [mem_sq] at hz
  obtain ⟨hc1, hc2⟩ := sqC_bounds hi
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  obtain ⟨hzr, hzi⟩ := hz
  rw [abs_le] at hre him hzr hzi
  obtain ⟨hz1, hz2⟩ := hzr
  obtain ⟨hz3, hz4⟩ := hzi
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

theorem sq_subset_probeRectU {j i : ℕ} (hi : i < nSq j) : sq j i ⊆ probeRectU j := fun z hz =>
  closedBall_sq_subset hi hz (mem_closedBall_self (by have := ell_pos j; positivity))

theorem closedBall_half_subset (j : ℕ) : closedBall (1 / 2 : ℂ) (ell j / 16) ⊆ probeRectU j := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre : |w.re - 1 / 2| ≤ ell j / 16 := by
    have : (w - 1 / 2).re = w.re - 1 / 2 := by simp
    rw [← this]; exact (Complex.abs_re_le_norm _).trans hw
  have him : |w.im| ≤ ell j / 16 := by
    have : (w - 1 / 2).im = w.im := by simp
    rw [← this]; exact (Complex.abs_im_le_norm _).trans hw
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  rw [abs_le] at hre him
  refine ⟨⟨by linarith, by linarith⟩, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

theorem half_mem_probeRectU (j : ℕ) : (1 / 2 : ℂ) ∈ probeRectU j :=
  closedBall_half_subset j (mem_closedBall_self (by have := ell_pos j; positivity))

/-- `V_j ⊆ ⋃_{i < N} Q_i` -/
theorem probeRectV_subset_iUnion_sq (j : ℕ) {z : ℂ} (hz : z ∈ probeRectV j) :
    ∃ i : Fin (nSq j), z ∈ sq j i := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  have hℓ := ell_pos j
  have hN := nSq_mul_ell j
  set t : ℝ := (z.re + 1 / 8) / (ell j / 4) with ht
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (by positivity)
  have htN : t < nSq j := by
    rw [ht, div_lt_iff₀ (by positivity)]
    linarith
  set i : ℕ := ⌊t⌋₊ with hi
  have hiN : i < nSq j := by
    rw [hi]; exact (Nat.floor_lt ht0).mpr htN
  have hfl : (i : ℝ) ≤ t := Nat.floor_le ht0
  have hfl' : t < (i : ℝ) + 1 := Nat.lt_floor_add_one t
  refine ⟨⟨i, hiN⟩, ?_⟩
  rw [mem_sq]
  refine ⟨?_, by rw [abs_lt] at h3; rw [abs_le]; constructor <;> linarith⟩
  have hre : z.re = -1 / 8 + t * (ell j / 4) := by
    rw [ht]; field_simp; ring
  show |z.re - sqC j i| ≤ ell j / 8
  rw [hre, sqC, abs_le]
  constructor <;> nlinarith

/-- points of `Q_i` are within `3/4` of `1/2` -/
theorem norm_sub_half_le {j i : ℕ} (hi : i < nSq j) {z : ℂ} (hz : z ∈ sq j i) :
    ‖z - 1 / 2‖ ≤ 3 / 4 := by
  rw [mem_sq] at hz
  obtain ⟨hc1, hc2⟩ := sqC_bounds hi
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (z - 1 / 2).re = z.re - 1 / 2 := by simp
  have e2 : (z - 1 / 2).im = z.im := by simp
  rw [e1, e2]
  obtain ⟨hzr, hzi⟩ := hz
  rw [abs_le] at hzr hzi
  have h1 : |z.re - 1 / 2| ≤ 5 / 8 := by
    rw [abs_le]; constructor <;> linarith [hzr.1, hzr.2]
  have h2 : |z.im| ≤ 1 / 8 := by
    rw [abs_le]; constructor <;> linarith [hzi.1, hzi.2]
  linarith

/-! ## Logarithmic constants -/

/-- `L_j = 1 + log(1/ℓ_j)` -/
def Lj (j : ℕ) : ℝ := 1 + Real.log (1 / ell j)

theorem log_one_div_ell (j : ℕ) : Real.log (1 / ell j) = j * Real.log 2 := by
  rw [one_div, inv_ell, Real.log_pow]

theorem log_one_div_ell_nonneg (j : ℕ) : 0 ≤ Real.log (1 / ell j) := by
  rw [log_one_div_ell]; exact mul_nonneg (Nat.cast_nonneg j) (Real.log_nonneg one_le_two)

theorem one_le_Lj (j : ℕ) : 1 ≤ Lj j := by
  unfold Lj; linarith [log_one_div_ell_nonneg j]

theorem log_two_le : Real.log 2 ≤ 7 / 10 := by
  have := Real.log_two_lt_d9; linarith

/-- `1 + log(1 + 12/ℓ) ≤ 4 L_j` -/
theorem one_add_log_le_Lj (j : ℕ) : 1 + Real.log (1 + 12 / ell j) ≤ 4 * Lj j := by
  have hℓ := ell_pos j
  have hℓ1 := ell_le_one j
  have h1 : 1 + 12 / ell j ≤ 16 * (1 / ell j) := by
    rw [mul_one_div, le_div_iff₀ hℓ, add_mul, div_mul_cancel₀ _ hℓ.ne']
    linarith
  have h2 : Real.log (1 + 12 / ell j) ≤ Real.log 16 + Real.log (1 / ell j) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) h1
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have h0 := log_one_div_ell_nonneg j
  have := log_two_le
  unfold Lj
  linarith

/-- `1 + log(2N) ≤ 4 L_j` -/
theorem one_add_log_two_nSq_le (j : ℕ) : 1 + Real.log (2 * nSq j) ≤ 4 * Lj j := by
  have e : (2 * (nSq j : ℝ)) = 10 * (1 / ell j) := by
    unfold nSq; rw [one_div, inv_ell]; push_cast; ring
  have h10 : Real.log 10 ≤ 4 * Real.log 2 := by
    have e4 : (4 : ℝ) * Real.log 2 = Real.log (2 ^ 4) := by rw [Real.log_pow]; norm_num
    rw [e4]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hℓ := ell_pos j
  rw [e, Real.log_mul (by norm_num) (by positivity)]
  have h0 := log_one_div_ell_nonneg j
  have := log_two_le
  unfold Lj
  linarith

/-! ## Borell–TIS on one square -/

section square

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {j : ℕ} {K : Ω → ℂ → ℝ} {B : ℝ}

/-- the chaining bound `M = 20√5 √(24B)` for `E sup_{Q_i} (±K)` -/
def Msq (B : ℝ) : ℝ := 20 * √5 * √(24 * B)

theorem Msq_nonneg (B : ℝ) : 0 ≤ Msq B := by unfold Msq; positivity

theorem Msq_sq {B : ℝ} (hB : 0 ≤ B) : Msq B ^ 2 = 48000 * B := by
  unfold Msq
  rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
  ring

/-- the parametrization `t ↦ (Re t, Im t) ∈ ℝ²` (sup norm) -/
def par (t : ℂ) : Fin 2 → ℝ := ![t.re, t.im]

theorem norm_sub_le_two_par (t t' : ℂ) : ‖t - t'‖ ≤ 2 * ‖par t - par t'‖ := by
  have h0 : |t.re - t'.re| ≤ ‖par t - par t'‖ := by
    have := norm_le_pi_norm (par t - par t') 0
    simpa [par] using this
  have h1 : |t.im - t'.im| ≤ ‖par t - par t'‖ := by
    have := norm_le_pi_norm (par t - par t') 1
    simpa [par] using this
  calc ‖t - t'‖ ≤ |(t - t').re| + |(t - t').im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |t.re - t'.re| + |t.im - t'.im| := by rw [Complex.sub_re, Complex.sub_im]
    _ ≤ 2 * ‖par t - par t'‖ := by linarith

theorem norm_par_sub_le {i : ℕ} {t t' : ℂ} (ht : t ∈ sq j i) (ht' : t' ∈ sq j i) :
    ‖par t - par t'‖ ≤ ell j / 4 := by
  have hℓ := ell_pos j
  rw [mem_sq] at ht ht'
  obtain ⟨h1, h2⟩ := ht
  obtain ⟨h3, h4⟩ := ht'
  rw [abs_le] at h1 h2 h3 h4
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  fin_cases k
  · show ‖t.re - t'.re‖ ≤ ell j / 4
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
  · show ‖t.im - t'.im‖ ≤ ell j / 4
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith

/-- the increment bound in Hölder form on `Q_i` -/
theorem integral_sq_sub_le_sq (hB : 0 ≤ B)
    (hinc : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ probeRectU j →
      closedBall w s ⊆ probeRectU j →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤ B * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s)))
    {i : ℕ} (hi : i < nSq j) {t t' : ℂ} (ht : t ∈ sq j i) (ht' : t' ∈ sq j i) :
    ∫ ω, (K ω t - K ω t') ^ 2 ∂P ≤ √(32 * B / ell j) ^ 2 * ‖par t - par t'‖ := by
  have hℓ := ell_pos j
  have h := hinc t t' (ell j / 16) (by positivity) (closedBall_sq_subset hi ht)
    (closedBall_sq_subset hi ht')
  rw [Real.sq_sqrt (by positivity)]
  refine h.trans ?_
  calc B * min (‖t - t'‖ / (ell j / 16)) (1 + Real.log (1 + ‖t - t'‖ / (ell j / 16)))
      ≤ B * (‖t - t'‖ / (ell j / 16)) := mul_le_mul_of_nonneg_left (min_le_left _ _) hB
    _ ≤ B * (2 * ‖par t - par t'‖ / (ell j / 16)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (norm_sub_le_two_par t t')
          (by positivity)) hB
    _ = 32 * B / ell j * ‖par t - par t'‖ := by field_simp; ring

/-- the variance bound `E K(t)² ≤ 4 B L_j` on `Q_i` -/
theorem integral_sq_le_sq (hB : 0 ≤ B) (hK : ∀ ω, K ω (1 / 2) = 0)
    (hinc : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ probeRectU j →
      closedBall w s ⊆ probeRectU j →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤ B * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s)))
    {i : ℕ} (hi : i < nSq j) {t : ℂ} (ht : t ∈ sq j i) :
    ∫ ω, (K ω t) ^ 2 ∂P ≤ 4 * B * Lj j := by
  have hℓ := ell_pos j
  have h := hinc t (1 / 2) (ell j / 16) (by positivity) (closedBall_sq_subset hi ht)
    (closedBall_half_subset j)
  simp only [hK, sub_zero] at h
  refine h.trans ?_
  have hd : ‖t - 1 / 2‖ / (ell j / 16) ≤ 12 / ell j := by
    rw [div_le_div_iff₀ (by positivity) hℓ]
    have := norm_sub_half_le hi ht
    nlinarith
  calc B * min (‖t - 1 / 2‖ / (ell j / 16)) (1 + Real.log (1 + ‖t - 1 / 2‖ / (ell j / 16)))
      ≤ B * (1 + Real.log (1 + 12 / ell j)) := by
        refine mul_le_mul_of_nonneg_left ((min_le_right _ _).trans ?_) hB
        have h0 : 0 ≤ ‖t - 1 / 2‖ / (ell j / 16) := by positivity
        have := Real.log_le_log (by positivity) (by linarith : 1 + ‖t - 1 / 2‖ / (ell j / 16) ≤
          1 + 12 / ell j)
        linarith
    _ ≤ B * (4 * Lj j) := mul_le_mul_of_nonneg_left (one_add_log_le_Lj j) hB
    _ = 4 * B * Lj j := by ring

/-- **Borell–TIS on one square**: `P(sup_{Q_i} |K| ≥ M + u) ≤ 2 exp(−u²/(8 B L_j))`. -/
theorem sq_tail [IsProbabilityMeasure P] (hB : 0 ≤ B)
    (hcont : ∀ ω, ContinuousOn (K ω) (probeRectU j))
    (hG : IsGaussianProcess (fun (p : probeRectU j × probeRectU j) (ω : Ω) => K ω p.1 - K ω p.2) P)
    (h0 : ∀ p : probeRectU j × probeRectU j, ∫ ω, (K ω p.1 - K ω p.2) ∂P = 0)
    (hK : ∀ ω, K ω (1 / 2) = 0)
    (hinc : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ probeRectU j →
      closedBall w s ⊆ probeRectU j →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤ B * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s)))
    (i : Fin (nSq j)) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | Msq B + u ≤ ⨆ t : sq j i, |K ω t|} ≤
      2 * Real.exp (-u ^ 2 / (2 * √(4 * B * Lj j) ^ 2)) := by
  have hiN : (i : ℕ) < nSq j := i.2
  have : CompactSpace (sq j i) := isCompact_iff_compactSpace.mp (isCompact_sq j i)
  have : Nonempty (sq j i) := ⟨⟨_, sqC_mem_sq j i⟩⟩
  have hQU := sq_subset_probeRectU hiN
  set X : sq j i → Ω → ℝ := fun t ω => K ω t with hXdef
  -- the Gaussian process
  have hX : IsGaussianProcess X P := by
    have h1 := hG.comp_right (fun t : sq j i =>
      ((⟨t, hQU t.2⟩ : probeRectU j), (⟨1 / 2, half_mem_probeRectU j⟩ : probeRectU j)))
    have e : ((fun (p : probeRectU j × probeRectU j) (ω : Ω) => K ω p.1 - K ω p.2) ∘
        (fun t : sq j i =>
          ((⟨t, hQU t.2⟩ : probeRectU j), (⟨1 / 2, half_mem_probeRectU j⟩ : probeRectU j)))) =
        X := by
      funext t ω
      simp only [Function.comp_apply, hK, sub_zero, hXdef]
    rwa [e] at h1
  have hX0 : ∀ t, ∫ ω, X t ω ∂P = 0 := by
    intro t
    have h1 := h0 ((⟨t, hQU t.2⟩ : probeRectU j), (⟨1 / 2, half_mem_probeRectU j⟩ : probeRectU j))
    simpa only [hK, sub_zero] using h1
  have hc : ∀ ω, Continuous fun t => X t ω := fun ω =>
    ((hcont ω).mono hQU).domRestrict
  -- the chaining bound
  have hℓ := ell_pos j
  have hL : (0 : ℝ) ≤ √(32 * B / ell j) := Real.sqrt_nonneg _
  have hM : 20 * √5 * √(32 * B / ell j) * √((((2 : ℕ) : ℝ) + 1) * (ell j / 4)) = Msq B := by
    unfold Msq
    rw [mul_assoc (20 * √5), ← Real.sqrt_mul (by positivity)]
    congr 2
    push_cast
    field_simp
    ring
  have hfin : ∀ (n : ℕ) (t : Fin (n + 1) → sq j i), ∫ ω, (⨆ k, X (t k) ω) ∂P ≤ Msq B := by
    intro n t
    rw [← hM]
    refine LQGMetric.SupTail.integral_iSup_family_le hX hX0 (Nat.succ_pos n) t
      (fun t : sq j i => par t) hL (fun a b => norm_par_sub_le (t a).2 (t b).2) (fun a b => ?_)
    exact integral_sq_sub_le_sq hB hinc hiN (t a).2 (t b).2
  have hXn : IsGaussianProcess (fun t ω => -X t ω) P :=
    LQGMetric.SupTail.isGaussianProcess_neg hX
  have hXn0 : ∀ t, ∫ ω, -X t ω ∂P = 0 := fun t => by rw [integral_neg, hX0 t, neg_zero]
  have hfin' : ∀ (n : ℕ) (t : Fin (n + 1) → sq j i), ∫ ω, (⨆ k, -X (t k) ω) ∂P ≤ Msq B := by
    intro n t
    rw [← hM]
    refine LQGMetric.SupTail.integral_iSup_family_le hXn hXn0 (Nat.succ_pos n) t
      (fun t : sq j i => par t) hL (fun a b => norm_par_sub_le (t a).2 (t b).2) (fun a b => ?_)
    have e : ∀ ω, (-X (t a) ω - -X (t b) ω) ^ 2 = (K ω (t a) - K ω (t b)) ^ 2 := fun ω => by
      simp only [hXdef]; ring
    simp only [e]
    exact integral_sq_sub_le_sq hB hinc hiN (t a).2 (t b).2
  obtain ⟨hint, hE⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hX hc hfin
  obtain ⟨hint', hE'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hXn
    (fun ω => (hc ω).neg) hfin'
  have hvar : ∀ t, Var[X t; P] ≤ √(4 * B * Lj j) ^ 2 := by
    intro t
    rw [Real.sq_sqrt (by have := one_le_Lj j; positivity)]
    refine (variance_le_expectation_sq (hX.aemeasurable t).aestronglyMeasurable).trans ?_
    have := integral_sq_le_sq hB hK hinc hiN t.2
    simpa only [Pi.pow_apply, hXdef] using this
  exact LQGMetric.SupTail.tail_iSup_abs_le hX hX0 hc hint hint' hE hE' hvar hu

end square

/-! ## The supremum over `V_j` -/

section supV

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {j : ℕ} {K : Ω → ℂ → ℝ} {B : ℝ}
  {ω : Ω}

/-- the closed box `[-1/8, 9/8] × [-ℓ/8, ℓ/8] ⊇ V_j` -/
def boxV (j : ℕ) : Set ℂ := Icc (-1 / 8 : ℝ) (9 / 8) ×ℂ Icc (-(ell j / 8)) (ell j / 8)

theorem isCompact_boxV (j : ℕ) : IsCompact (boxV j) := isCompact_Icc.reProdIm isCompact_Icc

theorem probeRectV_subset_boxV (j : ℕ) : probeRectV j ⊆ boxV j := by
  rintro z ⟨⟨h1, h2⟩, h3⟩
  rw [boxV, Complex.mem_reProdIm, mem_Icc, mem_Icc]
  rw [abs_lt] at h3
  exact ⟨⟨h1.le, h2.le⟩, h3.1.le, h3.2.le⟩

theorem boxV_subset_probeRectU (j : ℕ) : boxV j ⊆ probeRectU j := by
  intro z hz
  rw [boxV, Complex.mem_reProdIm, mem_Icc, mem_Icc] at hz
  have hℓ := ell_pos j
  refine ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, ?_⟩
  rw [abs_lt]; constructor <;> linarith [hz.2.1, hz.2.2]

theorem half_mem_probeRectV (j : ℕ) : (1 / 2 : ℂ) ∈ probeRectV j := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  have : (1 / 2 : ℂ).im = 0 := by simp
  rw [this, abs_zero]; have := ell_pos j; positivity

omit [MeasurableSpace Ω] in
theorem exists_bound_box (hcont : ContinuousOn (K ω) (probeRectU j)) :
    ∃ C, ∀ w ∈ boxV j, |K ω w| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_boxV j).exists_bound_of_continuousOn
    (hcont.mono (boxV_subset_probeRectU j))
  exact ⟨C, fun w hw => by simpa [Real.norm_eq_abs] using hC w hw⟩

omit [MeasurableSpace Ω] in
theorem bddAbove_sq (hcont : ContinuousOn (K ω) (probeRectU j)) {i : ℕ} (hi : i < nSq j) :
    BddAbove (range fun t : sq j i => |K ω t|) := by
  obtain ⟨C, hC⟩ := (isCompact_sq j i).exists_bound_of_continuousOn
    (hcont.mono (sq_subset_probeRectU hi))
  exact ⟨C, by rintro _ ⟨t, rfl⟩; simpa [Real.norm_eq_abs] using hC t t.2⟩

omit [MeasurableSpace Ω] in
/-- the supremum over `V_j` is the supremum over the subtype -/
theorem iSup_mem_eq_iSup_subtype (hcont : ContinuousOn (K ω) (probeRectU j)) :
    (⨆ w ∈ probeRectV j, |K ω w|) = ⨆ w : probeRectV j, |K ω w| := by
  have : Nonempty (probeRectV j) := ⟨⟨_, half_mem_probeRectV j⟩⟩
  obtain ⟨C, hC⟩ := exists_bound_box (ω := ω) hcont
  have hb : BddAbove (range fun w : probeRectV j => |K ω w|) :=
    ⟨C, by rintro _ ⟨w, rfl⟩; exact hC w (probeRectV_subset_boxV j w.2)⟩
  have hb' : BddAbove (range fun w : ℂ => ⨆ (_ : w ∈ probeRectV j), |K ω w|) := by
    refine ⟨max C 0, ?_⟩
    rintro _ ⟨w, rfl⟩
    dsimp only
    by_cases hw : w ∈ probeRectV j
    · rw [ciSup_pos hw]; exact (hC w (probeRectV_subset_boxV j hw)).trans (le_max_left _ _)
    · have : IsEmpty (w ∈ probeRectV j) := ⟨hw⟩
      rw [Real.iSup_of_isEmpty]; exact le_max_right _ _
  refine le_antisymm (ciSup_le fun w => ?_) (ciSup_le fun w => ?_)
  · by_cases hw : w ∈ probeRectV j
    · rw [ciSup_pos hw]; exact le_ciSup hb ⟨w, hw⟩
    · have : IsEmpty (w ∈ probeRectV j) := ⟨hw⟩
      rw [Real.iSup_of_isEmpty]
      exact Real.iSup_nonneg fun _ => abs_nonneg _
  · refine le_trans ?_ (le_ciSup hb' (w : ℂ))
    rw [ciSup_pos w.2]

/-- **Measurability of `sup_{V_j} |K|`** (a supremum over a dense sequence of `V_j`). -/
theorem measurable_iSup_probeRectV (hmeas : Measurable fun p : Ω × ℂ => K p.1 p.2)
    (hcont : ∀ ω, ContinuousOn (K ω) (probeRectU j)) :
    Measurable fun ω => ⨆ w ∈ probeRectV j, |K ω w| := by
  have : Nonempty (probeRectV j) := ⟨⟨_, half_mem_probeRectV j⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (probeRectV j)
  have e : (fun ω => ⨆ w ∈ probeRectV j, |K ω w|) = fun ω => ⨆ n, |K ω (u n)| := by
    funext ω
    rw [iSup_mem_eq_iSup_subtype (hcont ω)]
    obtain ⟨C, hC⟩ := exists_bound_box (ω := ω) (hcont ω)
    have hb : BddAbove (range fun w : probeRectV j => |K ω w|) :=
      ⟨C, by rintro _ ⟨w, rfl⟩; exact hC w (probeRectV_subset_boxV j w.2)⟩
    have hc : Continuous fun w : probeRectV j => |K ω w| :=
      continuous_abs.comp ((hcont ω).mono ((probeRectV_subset_boxV j).trans
        (boxV_subset_probeRectU j))).domRestrict
    exact LQGMetric.SupTail.iSup_eq_iSup_denseSeq hc hu hb
  rw [e]
  refine Measurable.iSup fun n => ?_
  exact continuous_abs.measurable.comp (hmeas.comp (measurable_id.prodMk measurable_const))

omit [MeasurableSpace Ω] in
/-- `sup_{V_j} |K| ≤ max_i sup_{Q_i} |K|` -/
theorem iSup_probeRectV_le (hcont : ContinuousOn (K ω) (probeRectU j)) :
    (⨆ w ∈ probeRectV j, |K ω w|) ≤ ⨆ i : Fin (nSq j), ⨆ t : sq j i, |K ω t| := by
  have : Nonempty (Fin (nSq j)) := ⟨⟨0, by unfold nSq; positivity⟩⟩
  have hnn : ∀ i : Fin (nSq j), 0 ≤ ⨆ t : sq j i, |K ω t| := fun i =>
    Real.iSup_nonneg fun _ => abs_nonneg _
  refine ciSup_le fun w => ?_
  by_cases hw : w ∈ probeRectV j
  · rw [ciSup_pos hw]
    obtain ⟨i, hi⟩ := probeRectV_subset_iUnion_sq j hw
    calc |K ω w| ≤ ⨆ t : sq j i, |K ω t| := le_ciSup (bddAbove_sq hcont i.2) ⟨w, hi⟩
      _ ≤ ⨆ i : Fin (nSq j), ⨆ t : sq j i, |K ω t| :=
          le_ciSup (f := fun i : Fin (nSq j) => ⨆ t : sq j i, |K ω t|)
            (Finite.bddAbove_range _) i
  · have : IsEmpty (w ∈ probeRectV j) := ⟨hw⟩
    rw [Real.iSup_of_isEmpty]
    exact Real.iSup_nonneg hnn

/-- **(b4) for `B > 0`.** -/
theorem sup_bound_pos [IsProbabilityMeasure P] (hB : 0 < B)
    (hmeas : Measurable fun p : Ω × ℂ => K p.1 p.2)
    (hcont : ∀ ω, ContinuousOn (K ω) (probeRectU j))
    (hG : IsGaussianProcess (fun (p : probeRectU j × probeRectU j) (ω : Ω) => K ω p.1 - K ω p.2) P)
    (h0 : ∀ p : probeRectU j × probeRectU j, ∫ ω, (K ω p.1 - K ω p.2) ∂P = 0)
    (hK : ∀ ω, K ω (1 / 2) = 0)
    (hinc : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ probeRectU j →
      closedBall w s ⊆ probeRectU j →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤ B * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s))) :
    ∫⁻ ω, ENNReal.ofReal ((⨆ w ∈ probeRectV j, |K ω w|) ^ 2) ∂P ≤
      ENNReal.ofReal (100000 * B * Lj j ^ 2) := by
  have hL1 := one_le_Lj j
  have hσ : 0 < 8 * B * Lj j := by positivity
  have hN : (1 : ℝ) ≤ 2 * nSq j := by
    have : (1 : ℝ) ≤ nSq j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by unfold nSq; positivity)
    linarith
  have hA0 : ∀ ω, 0 ≤ ⨆ w ∈ probeRectV j, |K ω w| := fun ω =>
    Real.iSup_nonneg fun w => Real.iSup_nonneg fun _ => abs_nonneg _
  have htail : ∀ t : ℝ, 0 < t → P {ω | Msq B + Real.sqrt t ≤ ⨆ w ∈ probeRectV j, |K ω w|} ≤
      ENNReal.ofReal (2 * nSq j * Real.exp (-t / (8 * B * Lj j))) := by
    intro t ht
    have hsub : {ω | Msq B + Real.sqrt t ≤ ⨆ w ∈ probeRectV j, |K ω w|} ⊆
        ⋃ i : Fin (nSq j), {ω | Msq B + Real.sqrt t ≤ ⨆ s : sq j i, |K ω s|} := by
      intro ω hω
      have h1 : Msq B + Real.sqrt t ≤ ⨆ i : Fin (nSq j), ⨆ s : sq j i, |K ω s| :=
        le_trans hω (iSup_probeRectV_le (hcont ω))
      have : Nonempty (Fin (nSq j)) := ⟨⟨0, by unfold nSq; positivity⟩⟩
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (nSq j) =>
        ⨆ s : sq j i, |K ω s|)
      have h2 : Msq B + Real.sqrt t ≤ ⨆ s : sq j i, |K ω s| := by rw [hi]; exact h1
      exact mem_iUnion.mpr ⟨i, h2⟩
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
    have hone : ∀ i : Fin (nSq j), P {ω | Msq B + Real.sqrt t ≤ ⨆ s : sq j i, |K ω s|} ≤
        ENNReal.ofReal (2 * Real.exp (-t / (8 * B * Lj j))) := by
      intro i
      rw [← ofReal_measureReal]
      refine ENNReal.ofReal_le_ofReal ((sq_tail hB.le hcont hG h0 hK hinc i
        (Real.sqrt_nonneg t)).trans (le_of_eq ?_))
      rw [hsq, Real.sq_sqrt (by positivity)]
      congr 2
      ring
    calc P {ω | Msq B + Real.sqrt t ≤ ⨆ w ∈ probeRectV j, |K ω w|}
        ≤ P (⋃ i : Fin (nSq j), {ω | Msq B + Real.sqrt t ≤ ⨆ s : sq j i, |K ω s|}) :=
          measure_mono hsub
      _ ≤ ∑ i : Fin (nSq j), P {ω | Msq B + Real.sqrt t ≤ ⨆ s : sq j i, |K ω s|} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : Fin (nSq j), ENNReal.ofReal (2 * Real.exp (-t / (8 * B * Lj j))) :=
          Finset.sum_le_sum fun i _ => hone i
      _ = ENNReal.ofReal (2 * nSq j * Real.exp (-t / (8 * B * Lj j))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1; ring
  have h := lintegral_sq_le_of_tail (measurable_iSup_probeRectV hmeas hcont).aemeasurable hA0
    hσ hN htail
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [Msq_sq hB.le]
  have hlog := one_add_log_two_nSq_le j
  have h2 : 6 * (8 * B * Lj j) * (1 + Real.log (2 * nSq j)) ≤ 192 * B * Lj j ^ 2 := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 6 * (8 * B * Lj j))
    nlinarith
  have h3 : B ≤ B * Lj j ^ 2 := by nlinarith
  nlinarith

/-- **(b4)**: measurability of `sup_{V_j} |K|` and `E sup_{V_j} K² ≤ 10⁵ B L_j²`. -/
theorem sup_bound [IsProbabilityMeasure P] (hB : 0 ≤ B)
    (hmeas : Measurable fun p : Ω × ℂ => K p.1 p.2)
    (hcont : ∀ ω, ContinuousOn (K ω) (probeRectU j))
    (hG : IsGaussianProcess (fun (p : probeRectU j × probeRectU j) (ω : Ω) => K ω p.1 - K ω p.2) P)
    (h0 : ∀ p : probeRectU j × probeRectU j, ∫ ω, (K ω p.1 - K ω p.2) ∂P = 0)
    (hK : ∀ ω, K ω (1 / 2) = 0)
    (hinc : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ probeRectU j →
      closedBall w s ⊆ probeRectU j →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤ B * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s))) :
    Measurable (fun ω => ⨆ w ∈ probeRectV j, |K ω w|) ∧
      ∫⁻ ω, ENNReal.ofReal ((⨆ w ∈ probeRectV j, |K ω w|) ^ 2) ∂P ≤
        ENNReal.ofReal (100000 * B * Lj j ^ 2) := by
  refine ⟨measurable_iSup_probeRectV hmeas hcont, ?_⟩
  have hL := one_le_Lj j
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set B' : ℝ := B + δ / (100000 * Lj j ^ 2) with hB'
  have hB'pos : 0 < B' := by positivity
  have hinc' : ∀ z w : ℂ, ∀ s : ℝ, 0 < s → closedBall z s ⊆ probeRectU j →
      closedBall w s ⊆ probeRectU j →
        ∫ ω, (K ω z - K ω w) ^ 2 ∂P ≤ B' * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s)) := by
    intro z w s hs hz hw
    have hδ' : 0 ≤ (δ : ℝ) / (100000 * Lj j ^ 2) := by positivity
    refine (hinc z w s hs hz hw).trans (mul_le_mul_of_nonneg_right (by linarith [hB']
      : B ≤ B') ?_)
    have h1 : 0 ≤ ‖z - w‖ / s := by positivity
    have h2 : 0 ≤ Real.log (1 + ‖z - w‖ / s) := Real.log_nonneg (by linarith)
    exact le_min h1 (by linarith)
  refine (sup_bound_pos hB'pos hmeas hcont hG h0 hK hinc').trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add (by positivity) (NNReal.coe_nonneg δ)]
  congr 1
  rw [hB']
  field_simp

end supV

end Coupling42

end SmallGammaGeodesics
