import SmallGammaGeodesics.Probes.Kernel
import SmallGammaGeodesics.Probes.Bands
import SmallGammaGeodesics.Probes.LowPass
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Convex.Basic

/-!
# Lemma 4.1: envelopes, real-line probe bounds, and the geometry of the probe map

* `envelope_bounds`: `E_{j,a} ≤ 2` and `∫₀¹ E_{j,a} ≤ 6πℓ_j` (via three Lorentzians,
  `envelope_le_lorentz`, and `integral_lorentz_le`).
* `envelope_le_four_mul`: shift stability `E(x) ≤ 4 E(x')` for `|x - x'| ≤ ℓ_j`.
* `lemma41_probe_real`: `‖H‖_{L∞(ℝ)} ≤ C`, `∫₀¹ |H| ≤ Cℓ`, `∫₀¹ |H'|² ≤ C/ℓ`.
* `probeMap_geometry` (target T9): for `|θ| ≤ ε₀ ℓ_j`, `ϕ = z + iθH_{j,a}` is holomorphic and
  injective on the strip `|Im z| < ℓ_j`, maps `U_j` into it, and `‖ϕ' - 1‖ ≤ 1/2` there.

`envelope` is the junk-free envelope of the authorized correction (see `Probes/Defs.lean` and
`Probes/Erratum.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped Real

namespace SmallGammaGeodesics

/-- The lattice `2ℤ ⊆ ℝ`. -/
abbrev twoZ : Set ℝ := Set.range fun m : ℤ => (2 * m : ℝ)

theorem twoZ_nonempty : twoZ.Nonempty := ⟨0, 0, by simp⟩

/-! ### Distances to `2ℤ` -/

theorem abs_le_infDist_twoZ {y : ℝ} (hy : |y| ≤ 1) : |y| ≤ Metric.infDist y twoZ := by
  rw [Metric.le_infDist twoZ_nonempty]
  rintro _ ⟨m, rfl⟩
  rw [Real.dist_eq]
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hm
    have h := le_abs_self (y - 2 * m)
    have h' := abs_le.mp hy
    linarith
  · simp [hm]
  · have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have h := neg_abs_le (y - 2 * m)
    have h' := abs_le.mp hy
    rw [abs_sub_comm] at h
    have h'' := neg_le_abs (y - 2 * m)
    linarith

theorem two_sub_le_infDist_twoZ {y : ℝ} (h1 : 1 ≤ y) :
    2 - y ≤ Metric.infDist y twoZ := by
  rw [Metric.le_infDist twoZ_nonempty]
  rintro _ ⟨m, rfl⟩
  rw [Real.dist_eq]
  rcases lt_trichotomy m 1 with hm | hm | hm
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast Int.lt_add_one_iff.mp hm
    have h := le_abs_self (y - 2 * m)
    linarith
  · subst hm
    rw [abs_sub_comm]
    simp only [Int.cast_one, mul_one]
    exact le_abs_self _
  · have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have h := neg_le_abs (y - 2 * m)
    linarith

/-! ### Comparison with Lorentzians -/

/-- `(ℓ / max(ℓ, D))² ≤ 2 ℓ²/(ℓ² + D²)`. -/
theorem sq_div_max_le {ℓ D : ℝ} (hℓ : 0 < ℓ) (hD : 0 ≤ D) :
    (ℓ / max ℓ D) ^ 2 ≤ 2 * (ℓ ^ 2 / (ℓ ^ 2 + D ^ 2)) := by
  have hM : 0 < max ℓ D := lt_of_lt_of_le hℓ (le_max_left _ _)
  rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ℓ ^ 2 ≤ max ℓ D ^ 2 := pow_le_pow_left₀ hℓ.le (le_max_left _ _) 2
  have h2 : D ^ 2 ≤ max ℓ D ^ 2 := pow_le_pow_left₀ hD (le_max_right _ _) 2
  nlinarith [sq_nonneg ℓ]

/-- `D ↦ (ℓ / max(ℓ, D))²` is antitone. -/
theorem sq_div_max_anti {ℓ D D' : ℝ} (hℓ : 0 < ℓ) (h : D' ≤ D) :
    (ℓ / max ℓ D) ^ 2 ≤ (ℓ / max ℓ D') ^ 2 := by
  have hM' : 0 < max ℓ D' := lt_of_lt_of_le hℓ (le_max_left _ _)
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  exact div_le_div_of_nonneg_left hℓ.le hM' (max_le_max le_rfl h)

theorem sq_div_max_le_one {ℓ D : ℝ} (hℓ : 0 < ℓ) : (ℓ / max ℓ D) ^ 2 ≤ 1 := by
  have hM : 0 < max ℓ D := lt_of_lt_of_le hℓ (le_max_left _ _)
  rw [div_pow, div_le_one (by positivity)]
  exact pow_le_pow_left₀ hℓ.le (le_max_left _ _) 2

/-! ### The envelopes -/

theorem envelope_nonneg (j : ℕ) (a x : ℝ) : 0 ≤ envelope j a x := by
  unfold envelope
  positivity

theorem envelope_le_two (j : ℕ) (a x : ℝ) : envelope j a x ≤ 2 := by
  unfold envelope
  have := sq_div_max_le_one (D := Metric.infDist (x - a) twoZ) (ell_pos j)
  have := sq_div_max_le_one (D := Metric.infDist (x + a) twoZ) (ell_pos j)
  linarith

theorem continuous_envelope (j : ℕ) (a : ℝ) : Continuous (envelope j a) := by
  have hℓ := ell_pos j
  unfold envelope
  refine Continuous.add ?_ ?_
  · refine (continuous_const.div (continuous_const.max
      ((Metric.continuous_infDist_pt _).comp (continuous_id.sub continuous_const)))
      (fun x => (lt_of_lt_of_le hℓ (le_max_left _ _)).ne')).pow 2
  · refine (continuous_const.div (continuous_const.max
      ((Metric.continuous_infDist_pt _).comp (continuous_id.add continuous_const)))
      (fun x => (lt_of_lt_of_le hℓ (le_max_left _ _)).ne')).pow 2

/-- On `[0,1]²`, the envelope is dominated by three Lorentzians. -/
theorem envelope_le_lorentz (j : ℕ) {a x : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    envelope j a x ≤ 2 * (ell j ^ 2 / (ell j ^ 2 + (x - a) ^ 2)) +
      2 * (ell j ^ 2 / (ell j ^ 2 + (x - -a) ^ 2)) +
        2 * (ell j ^ 2 / (ell j ^ 2 + (x - (2 - a)) ^ 2)) := by
  have hℓ := ell_pos j
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hx0, hx1⟩ := hx
  unfold envelope
  have hL₂ : 0 ≤ ell j ^ 2 / (ell j ^ 2 + (x - (2 - a)) ^ 2) := by positivity
  have hL₁ : 0 ≤ ell j ^ 2 / (ell j ^ 2 + (x - -a) ^ 2) := by positivity
  have t1 : (ell j / max (ell j) (Metric.infDist (x - a) twoZ)) ^ 2 ≤
      2 * (ell j ^ 2 / (ell j ^ 2 + (x - a) ^ 2)) := by
    have hd := abs_le_infDist_twoZ (y := x - a) (by rw [abs_le]; constructor <;> linarith)
    refine (sq_div_max_anti hℓ hd).trans ?_
    have := sq_div_max_le (D := |x - a|) hℓ (abs_nonneg _)
    rwa [sq_abs] at this
  have t2 : (ell j / max (ell j) (Metric.infDist (x + a) twoZ)) ^ 2 ≤
      2 * (ell j ^ 2 / (ell j ^ 2 + (x - -a) ^ 2)) +
        2 * (ell j ^ 2 / (ell j ^ 2 + (x - (2 - a)) ^ 2)) := by
    rcases le_total (x + a) 1 with h | h
    · have hd := abs_le_infDist_twoZ (y := x + a) (by rw [abs_le]; constructor <;> linarith)
      refine (sq_div_max_anti hℓ hd).trans ?_
      have := sq_div_max_le (D := |x + a|) hℓ (abs_nonneg _)
      have e : (x + a) ^ 2 = (x - -a) ^ 2 := by ring
      rw [sq_abs, e] at this
      linarith
    · have hd := two_sub_le_infDist_twoZ (y := x + a) h
      refine (sq_div_max_anti hℓ hd).trans ?_
      have := sq_div_max_le (D := 2 - (x + a)) hℓ (by linarith)
      rw [show (2 - (x + a)) ^ 2 = (x - (2 - a)) ^ 2 by ring] at this
      linarith
  linarith

/-- `∫₀¹ E_{j,a} ≤ 6πℓ_j` for the corrected envelope. -/
theorem integral_envelope_le (j : ℕ) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ∫ x in (0 : ℝ)..1, envelope j a x ≤ 6 * π * ell j := by
  have hℓ := ell_pos j
  have hc := fun c => (continuous_lorentz hℓ c).intervalIntegrable (μ := volume) 0 1
  calc ∫ x in (0 : ℝ)..1, envelope j a x
      ≤ ∫ x in (0 : ℝ)..1, (2 * (ell j ^ 2 / (ell j ^ 2 + (x - a) ^ 2)) +
          2 * (ell j ^ 2 / (ell j ^ 2 + (x - -a) ^ 2)) +
            2 * (ell j ^ 2 / (ell j ^ 2 + (x - (2 - a)) ^ 2))) := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((continuous_envelope j a).intervalIntegrable 0 1) ?_ ?_
        · exact (((hc a).const_mul 2).add ((hc (-a)).const_mul 2)).add ((hc (2 - a)).const_mul 2)
        · intro x hx
          exact envelope_le_lorentz j ha hx
    _ = 2 * (∫ x in (0 : ℝ)..1, ell j ^ 2 / (ell j ^ 2 + (x - a) ^ 2)) +
          2 * (∫ x in (0 : ℝ)..1, ell j ^ 2 / (ell j ^ 2 + (x - -a) ^ 2)) +
            2 * (∫ x in (0 : ℝ)..1, ell j ^ 2 / (ell j ^ 2 + (x - (2 - a)) ^ 2)) := by
        rw [intervalIntegral.integral_add (((hc a).const_mul 2).add ((hc (-a)).const_mul 2))
          ((hc (2 - a)).const_mul 2), intervalIntegral.integral_add ((hc a).const_mul 2)
          ((hc (-a)).const_mul 2), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * (π * ell j) + 2 * (π * ell j) + 2 * (π * ell j) := by
        have h1 := integral_lorentz_le hℓ a 0 1
        have h2 := integral_lorentz_le hℓ (-a) 0 1
        have h3 := integral_lorentz_le hℓ (2 - a) 0 1
        linarith
    _ = 6 * π * ell j := by ring

/-- The bounds of Lemma 4.1 for the corrected envelope. -/
theorem envelope_bounds :
    ∃ C : ℝ, ∀ j : ℕ, ∀ a ∈ Set.Icc (0 : ℝ) 1, (∀ x, envelope j a x ≤ 2) ∧
      (∫ x in (0 : ℝ)..1, envelope j a x) ≤ C * ell j :=
  ⟨6 * π, fun j a ha => ⟨envelope_le_two j a, integral_envelope_le j ha⟩⟩

/-- **Shift stability**: `E_{j,a}(x) ≤ 4 E_{j,a}(x')` for `|x - x'| ≤ ℓ_j`. -/
theorem envelope_le_four_mul (j : ℕ) (a : ℝ) {x x' : ℝ} (h : |x - x'| ≤ ell j) :
    envelope j a x ≤ 4 * envelope j a x' := by
  have hℓ := ell_pos j
  have key : ∀ y y' : ℝ, |y - y'| ≤ ell j →
      (ell j / max (ell j) (Metric.infDist y twoZ)) ^ 2 ≤
        4 * (ell j / max (ell j) (Metric.infDist y' twoZ)) ^ 2 := by
    intro y y' hyy
    have hd : Metric.infDist y' twoZ ≤ Metric.infDist y twoZ + ell j := by
      have := Metric.infDist_le_infDist_add_dist (x := y') (y := y) (s := twoZ)
      rw [Real.dist_eq, abs_sub_comm] at this
      linarith
    have hM : 0 < max (ell j) (Metric.infDist y twoZ) := lt_of_lt_of_le hℓ (le_max_left _ _)
    have hM' : 0 < max (ell j) (Metric.infDist y' twoZ) := lt_of_lt_of_le hℓ (le_max_left _ _)
    have hmax : max (ell j) (Metric.infDist y' twoZ) ≤ 2 * max (ell j) (Metric.infDist y twoZ) := by
      refine max_le ?_ ?_
      · linarith [le_max_left (ell j) (Metric.infDist y twoZ)]
      · linarith [le_max_left (ell j) (Metric.infDist y twoZ),
          le_max_right (ell j) (Metric.infDist y twoZ)]
    rw [div_pow, div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ hM'.le hmax 2
    nlinarith [sq_nonneg (ell j)]
  unfold envelope
  have h1 := key (x - a) (x' - a) (by rw [show x - a - (x' - a) = x - x' by ring]; exact h)
  have h2 := key (x + a) (x' + a) (by rw [show x + a - (x' + a) = x - x' by ring]; exact h)
  linarith

theorem envelope_pos (j : ℕ) (a x : ℝ) : 0 < envelope j a x := by
  have hℓ := ell_pos j
  have h1 : 0 < max (ell j) (Metric.infDist (x - a) twoZ) := lt_of_lt_of_le hℓ (le_max_left _ _)
  have h2 : 0 < max (ell j) (Metric.infDist (x + a) twoZ) := lt_of_lt_of_le hℓ (le_max_left _ _)
  unfold envelope
  positivity

/-- `|y - 2m| ≤ dist(y, 2ℤ)` whenever `|y - 2m| ≤ 1`. -/
theorem le_infDist_twoZ_of_abs_sub_le {y : ℝ} {m : ℤ} (h : |y - 2 * m| ≤ 1) :
    |y - 2 * m| ≤ Metric.infDist y twoZ := by
  rw [Metric.le_infDist twoZ_nonempty]
  rintro _ ⟨m', rfl⟩
  rw [Real.dist_eq]
  rcases eq_or_ne m' m with hm | hm
  · rw [hm]
  · have h1 : (1 : ℝ) ≤ |(m : ℝ) - m'| := by
      have : 1 ≤ |m - m'| := Int.one_le_abs (sub_ne_zero.mpr hm.symm)
      exact_mod_cast this
    have h3 : |(y - 2 * m') - (y - 2 * m)| ≤ |y - 2 * m'| + |y - 2 * m| := abs_sub _ _
    rw [show (y - 2 * m') - (y - 2 * m) = 2 * ((m : ℝ) - m') by ring, abs_mul, abs_two] at h3
    linarith

/-- On two adjacent cells `[2m - 1, 2m + 3]` of `2ℤ`, each envelope summand is dominated by two
Lorentzians. -/
theorem sq_div_max_infDist_le {ℓ : ℝ} (hℓ : 0 < ℓ) {y : ℝ} {m : ℤ} (h1 : 2 * m - 1 ≤ y)
    (h2 : y ≤ 2 * m + 3) :
    (ℓ / max ℓ (Metric.infDist y twoZ)) ^ 2 ≤
      2 * (ℓ ^ 2 / (ℓ ^ 2 + (y - 2 * m) ^ 2)) + 2 * (ℓ ^ 2 / (ℓ ^ 2 + (y - 2 * (m + 1)) ^ 2)) := by
  have hL1 : 0 ≤ ℓ ^ 2 / (ℓ ^ 2 + (y - 2 * m) ^ 2) := by positivity
  have hL2 : 0 ≤ ℓ ^ 2 / (ℓ ^ 2 + (y - 2 * (m + 1)) ^ 2) := by positivity
  rcases le_total y (2 * m + 1) with h | h
  · have hd := le_infDist_twoZ_of_abs_sub_le (y := y) (m := m)
      (by rw [abs_le]; constructor <;> linarith)
    have := (sq_div_max_anti hℓ hd).trans (sq_div_max_le hℓ (abs_nonneg _))
    rw [sq_abs] at this
    linarith
  · have hd := le_infDist_twoZ_of_abs_sub_le (y := y) (m := m + 1)
      (by push_cast; rw [abs_le]; constructor <;> linarith)
    have := (sq_div_max_anti hℓ hd).trans (sq_div_max_le hℓ (abs_nonneg _))
    push_cast at this
    rw [sq_abs] at this
    linarith

/-- **Lemma 4.1, envelope integrals on intervals of length `≤ 2`** (blueprint
`lem:probe-envelope` (d); e.g. `[-1/2, 3/2]`): `∫_α^β E_{j,a} ≤ 8πℓ_j`. -/
theorem integral_envelope_le_of_le_two (j : ℕ) (a : ℝ) {α β : ℝ} (hαβ : α ≤ β)
    (hβ : β ≤ α + 2) : ∫ x in α..β, envelope j a x ≤ 8 * π * ell j := by
  have hℓ := ell_pos j
  set m₁ : ℤ := ⌊(α - a + 1) / 2⌋ with hm₁
  set m₂ : ℤ := ⌊(α + a + 1) / 2⌋ with hm₂
  have f1 := Int.floor_le ((α - a + 1) / 2)
  have f2 := Int.lt_floor_add_one ((α - a + 1) / 2)
  have g1 := Int.floor_le ((α + a + 1) / 2)
  have g2 := Int.lt_floor_add_one ((α + a + 1) / 2)
  rw [← hm₁] at f1 f2
  rw [← hm₂] at g1 g2
  set c₁ : ℝ := a + 2 * m₁
  set c₂ : ℝ := a + 2 * (m₁ + 1)
  set c₃ : ℝ := -a + 2 * m₂
  set c₄ : ℝ := -a + 2 * (m₂ + 1)
  have hpt : ∀ x ∈ Set.Icc α β, envelope j a x ≤
      2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₁) ^ 2)) + 2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₂) ^ 2)) +
      (2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₃) ^ 2)) +
        2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₄) ^ 2))) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    unfold envelope
    have t1 := sq_div_max_infDist_le (y := x - a) (m := m₁) hℓ (by linarith) (by linarith)
    have t2 := sq_div_max_infDist_le (y := x + a) (m := m₂) hℓ (by linarith) (by linarith)
    have e1 : x - a - 2 * (m₁ : ℝ) = x - c₁ := by ring
    have e2 : x - a - 2 * ((m₁ : ℝ) + 1) = x - c₂ := by ring
    have e3 : x + a - 2 * (m₂ : ℝ) = x - c₃ := by ring
    have e4 : x + a - 2 * ((m₂ : ℝ) + 1) = x - c₄ := by ring
    rw [e1, e2] at t1
    rw [e3, e4] at t2
    exact add_le_add t1 t2
  have hc := fun c => (continuous_lorentz hℓ c).intervalIntegrable (μ := volume) α β
  have hsum : IntervalIntegrable (fun x => 2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₁) ^ 2)) +
      2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₂) ^ 2)) +
      (2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₃) ^ 2)) +
        2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₄) ^ 2)))) volume α β :=
    (((hc c₁).const_mul 2).add ((hc c₂).const_mul 2)).add
      (((hc c₃).const_mul 2).add ((hc c₄).const_mul 2))
  calc ∫ x in α..β, envelope j a x
      ≤ ∫ x in α..β, (2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₁) ^ 2)) +
          2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₂) ^ 2)) +
          (2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₃) ^ 2)) +
            2 * (ell j ^ 2 / (ell j ^ 2 + (x - c₄) ^ 2)))) :=
        intervalIntegral.integral_mono_on hαβ
          ((continuous_envelope j a).intervalIntegrable α β) hsum hpt
    _ = 2 * (∫ x in α..β, ell j ^ 2 / (ell j ^ 2 + (x - c₁) ^ 2)) +
          2 * (∫ x in α..β, ell j ^ 2 / (ell j ^ 2 + (x - c₂) ^ 2)) +
          (2 * (∫ x in α..β, ell j ^ 2 / (ell j ^ 2 + (x - c₃) ^ 2)) +
            2 * (∫ x in α..β, ell j ^ 2 / (ell j ^ 2 + (x - c₄) ^ 2))) := by
        rw [intervalIntegral.integral_add (((hc c₁).const_mul 2).add ((hc c₂).const_mul 2))
          (((hc c₃).const_mul 2).add ((hc c₄).const_mul 2)),
          intervalIntegral.integral_add ((hc c₁).const_mul 2) ((hc c₂).const_mul 2),
          intervalIntegral.integral_add ((hc c₃).const_mul 2) ((hc c₄).const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 8 * π * ell j := by
        have i1 := integral_lorentz_le hℓ c₁ α β
        have i2 := integral_lorentz_le hℓ c₂ α β
        have i3 := integral_lorentz_le hℓ c₃ α β
        have i4 := integral_lorentz_le hℓ c₄ α β
        linarith

/-! ### Real-line probe bounds -/

theorem continuous_deriv_probeH (j : ℕ) (a : ℝ) : Continuous (deriv (probeH j a)) := by
  have h : deriv (probeH j a) = fun z => probeG j 1 (z - a) - probeG j 1 (z + a) := by
    funext z
    rw [← iteratedDeriv_one, iteratedDeriv_probeH]
  rw [h]
  exact ((differentiable_probeG j 1).continuous.comp (continuous_id.sub continuous_const)).sub
    ((differentiable_probeG j 1).continuous.comp (continuous_id.add continuous_const))

/-- **Lemma 4.1, probe bounds** (real line). -/
theorem lemma41_probe_real :
    ∃ C : ℝ, ∀ j : ℕ, ∀ a ∈ Set.Icc (0 : ℝ) 1,
      (∀ x : ℝ, ‖probeH j a x‖ ≤ C) ∧
      (∫ x in (0 : ℝ)..1, ‖probeH j a x‖) ≤ C * ell j ∧
      (∫ x in (0 : ℝ)..1, ‖deriv (probeH j a) x‖ ^ 2) ≤ C / ell j := by
  obtain ⟨C, hC⟩ := lemma41_envelope 1 one_pos
  set C' := |C| with hC'
  have hC'0 : 0 ≤ C' := abs_nonneg C
  refine ⟨2 * C' + 6 * π * C' + 12 * π * C' ^ 2, fun j a ha => ?_⟩
  have hℓ := ell_pos j
  have hreal : ∀ x : ℝ, |((x : ℂ)).im| ≤ 1 * ell j := by
    intro x
    simp only [Complex.ofReal_im, abs_zero, one_mul]
    exact hℓ.le
  have h0 : ∀ x : ℝ, ‖probeH j a x‖ ≤ C' * envelope j a x := by
    intro x
    have := hC j a ha 0 (by norm_num) x (hreal x)
    rw [iteratedDeriv_zero, pow_zero, mul_one, Complex.ofReal_re] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (envelope_nonneg j a x))
  have h1 : ∀ x : ℝ, ‖deriv (probeH j a) x‖ ≤ C' * (ell j)⁻¹ * envelope j a x := by
    intro x
    have := hC j a ha 1 (by norm_num) x (hreal x)
    rw [iteratedDeriv_one, pow_one, Complex.ofReal_re] at this
    refine this.trans (mul_le_mul_of_nonneg_right ?_ (envelope_nonneg j a x))
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr hℓ.le)
  have hEint := integral_envelope_le j ha
  have hEii : IntervalIntegrable (envelope j a) volume 0 1 :=
    (continuous_envelope j a).intervalIntegrable 0 1
  have hHc : Continuous fun x : ℝ => ‖probeH j a x‖ :=
    ((differentiable_probeH j a).continuous.comp Complex.continuous_ofReal).norm
  have hDc : Continuous fun x : ℝ => ‖deriv (probeH j a) x‖ ^ 2 :=
    (((continuous_deriv_probeH j a).comp Complex.continuous_ofReal).norm).pow 2
  refine ⟨fun x => ?_, ?_, ?_⟩
  · calc ‖probeH j a x‖ ≤ C' * envelope j a x := h0 x
      _ ≤ C' * 2 := mul_le_mul_of_nonneg_left (envelope_le_two j a x) hC'0
      _ ≤ 2 * C' + 6 * π * C' + 12 * π * C' ^ 2 := by nlinarith [Real.pi_pos]
  · calc ∫ x in (0 : ℝ)..1, ‖probeH j a x‖ ≤ ∫ x in (0 : ℝ)..1, C' * envelope j a x :=
          intervalIntegral.integral_mono_on zero_le_one (hHc.intervalIntegrable 0 1)
            (hEii.const_mul C') (fun x _ => h0 x)
      _ = C' * ∫ x in (0 : ℝ)..1, envelope j a x := intervalIntegral.integral_const_mul _ _
      _ ≤ C' * (6 * π * ell j) := mul_le_mul_of_nonneg_left hEint hC'0
      _ ≤ (2 * C' + 6 * π * C' + 12 * π * C' ^ 2) * ell j := by
          have : 0 ≤ (2 * C' + 12 * π * C' ^ 2) * ell j :=
            mul_nonneg (by positivity) hℓ.le
          nlinarith
  · have hpt : ∀ x : ℝ, ‖deriv (probeH j a) x‖ ^ 2 ≤
        2 * C' ^ 2 * (ell j)⁻¹ ^ 2 * envelope j a x := by
      intro x
      have hb := h1 x
      have hE0 := envelope_nonneg j a x
      have hE2 := envelope_le_two j a x
      have hn := norm_nonneg (deriv (probeH j a) x)
      have hinv : 0 ≤ (ell j)⁻¹ := inv_nonneg.mpr hℓ.le
      calc ‖deriv (probeH j a) x‖ ^ 2 ≤ (C' * (ell j)⁻¹ * envelope j a x) ^ 2 :=
            pow_le_pow_left₀ hn hb 2
        _ = C' ^ 2 * (ell j)⁻¹ ^ 2 * envelope j a x * envelope j a x := by ring
        _ ≤ C' ^ 2 * (ell j)⁻¹ ^ 2 * envelope j a x * 2 :=
            mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ = 2 * C' ^ 2 * (ell j)⁻¹ ^ 2 * envelope j a x := by ring
    calc ∫ x in (0 : ℝ)..1, ‖deriv (probeH j a) x‖ ^ 2
        ≤ ∫ x in (0 : ℝ)..1, 2 * C' ^ 2 * (ell j)⁻¹ ^ 2 * envelope j a x :=
          intervalIntegral.integral_mono_on zero_le_one (hDc.intervalIntegrable 0 1)
            (hEii.const_mul _) (fun x _ => hpt x)
      _ = 2 * C' ^ 2 * (ell j)⁻¹ ^ 2 * ∫ x in (0 : ℝ)..1, envelope j a x :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ 2 * C' ^ 2 * (ell j)⁻¹ ^ 2 * (6 * π * ell j) :=
          mul_le_mul_of_nonneg_left hEint (by positivity)
      _ = 12 * π * C' ^ 2 / ell j := by
          field_simp
          ring
      _ ≤ (2 * C' + 6 * π * C' + 12 * π * C' ^ 2) / ell j := by
          rw [div_le_div_iff_of_pos_right hℓ]
          have : 0 ≤ 2 * C' + 6 * π * C' := by positivity
          linarith

/-! ### Geometry of the probe map (target T9) -/

theorem convex_probeStrip (j : ℕ) : Convex ℝ (probeStrip j) := by
  have : probeStrip j = Complex.imLm ⁻¹' Set.Ioo (-ell j) (ell j) := by
    ext z
    show |z.im| < ell j ↔ -ell j < z.im ∧ z.im < ell j
    exact abs_lt
  rw [this]
  exact (convex_Ioo _ _).linear_preimage _

theorem hasDerivAt_probeMap (j : ℕ) (a θ : ℝ) (z : ℂ) :
    HasDerivAt (probeMap j a θ) (1 + Complex.I * θ * deriv (probeH j a) z) z := by
  unfold probeMap
  exact (hasDerivAt_id z).add (((differentiable_probeH j a) z).hasDerivAt.const_mul _)

/-- **Target T9 (geometry of the probe map).** There is `ε₀ > 0` such that for every real `a` and
`|θ| ≤ ε₀ ℓ_j`, the map `ϕ(z) = z + iθH_{j,a}(z)` is holomorphic and injective on the strip
`S_j = {|Im z| < ℓ_j}`, maps `U_j` into `S_j`, and satisfies `‖ϕ'(z) - 1‖ ≤ 1/2` on `S_j`. -/
theorem probeMap_geometry :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (j : ℕ) (a θ : ℝ), |θ| ≤ ε₀ * ell j →
      DifferentiableOn ℂ (probeMap j a θ) (probeStrip j) ∧
      Set.InjOn (probeMap j a θ) (probeStrip j) ∧
      Set.MapsTo (probeMap j a θ) (probeRectU j) (probeStrip j) ∧
      ∀ z ∈ probeStrip j, ‖deriv (probeMap j a θ) z - 1‖ ≤ 1 / 2 := by
  obtain ⟨C, -, hC⟩ := norm_iteratedDeriv_probeH_le 1 one_pos
  set C' := 2 * |C| + 1 with hC'
  have hC'pos : 0 < C' := by positivity
  refine ⟨1 / (4 * C'), by positivity, fun j a θ hθ => ?_⟩
  have hℓ := ell_pos j
  -- bounds on the closed strip of height `ℓ_j`
  have hH : ∀ z : ℂ, |z.im| ≤ ell j → ‖probeH j a z‖ ≤ C' := by
    intro z hz
    have := hC j a 0 (by norm_num) z (by rw [one_mul]; exact hz)
    rw [iteratedDeriv_zero, pow_zero, mul_one] at this
    have hE := envelope_le_two j a z.re
    have hE0 := envelope_nonneg j a z.re
    calc ‖probeH j a z‖ ≤ C * envelope j a z.re := this
      _ ≤ |C| * 2 := by
          calc C * envelope j a z.re ≤ |C| * envelope j a z.re :=
                mul_le_mul_of_nonneg_right (le_abs_self C) hE0
            _ ≤ |C| * 2 := mul_le_mul_of_nonneg_left hE (abs_nonneg C)
      _ ≤ C' := by rw [hC']; linarith
  have hH' : ∀ z : ℂ, |z.im| ≤ ell j → ‖deriv (probeH j a) z‖ ≤ C' * (ell j)⁻¹ := by
    intro z hz
    have := hC j a 1 (by norm_num) z (by rw [one_mul]; exact hz)
    rw [iteratedDeriv_one, pow_one] at this
    have hE := envelope_le_two j a z.re
    have hE0 := envelope_nonneg j a z.re
    have hinv : 0 < (ell j)⁻¹ := inv_pos.mpr hℓ
    calc ‖deriv (probeH j a) z‖ ≤ C * (ell j)⁻¹ * envelope j a z.re := this
      _ ≤ |C| * (ell j)⁻¹ * 2 := by
          calc C * (ell j)⁻¹ * envelope j a z.re
              ≤ |C| * (ell j)⁻¹ * envelope j a z.re :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hinv.le) hE0
            _ ≤ |C| * (ell j)⁻¹ * 2 := mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ C' * (ell j)⁻¹ := by
          rw [hC']
          nlinarith [abs_nonneg C]
  have hθC : |θ| * C' ≤ ell j / 4 := by
    calc |θ| * C' ≤ 1 / (4 * C') * ell j * C' := mul_le_mul_of_nonneg_right hθ hC'pos.le
      _ = ell j / 4 := by field_simp
  -- the derivative bound
  have hder : ∀ z ∈ probeStrip j, ‖deriv (probeMap j a θ) z - 1‖ ≤ 1 / 2 := by
    intro z hz
    rw [(hasDerivAt_probeMap j a θ z).deriv, add_sub_cancel_left, norm_mul, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hz' : |z.im| ≤ ell j := le_of_lt hz
    calc |θ| * ‖deriv (probeH j a) z‖ ≤ |θ| * (C' * (ell j)⁻¹) :=
          mul_le_mul_of_nonneg_left (hH' z hz') (abs_nonneg θ)
      _ = |θ| * C' * (ell j)⁻¹ := by ring
      _ ≤ ell j / 4 * (ell j)⁻¹ := mul_le_mul_of_nonneg_right hθC (inv_nonneg.mpr hℓ.le)
      _ ≤ 1 / 2 := by
          rw [div_mul_eq_mul_div, mul_inv_cancel₀ hℓ.ne']
          norm_num
  refine ⟨fun z _ => (hasDerivAt_probeMap j a θ z).differentiableAt.differentiableWithinAt,
    ?_, ?_, hder⟩
  · -- injectivity: `ϕ - id` is `1/2`-Lipschitz on the convex strip
    intro z hz w hw hzw
    have hg : ∀ x ∈ probeStrip j, DifferentiableAt ℂ (fun x => probeMap j a θ x - x) x :=
      fun x _ => (hasDerivAt_probeMap j a θ x).differentiableAt.sub differentiableAt_id
    have hgb : ∀ x ∈ probeStrip j, ‖deriv (fun x => probeMap j a θ x - x) x‖ ≤ 1 / 2 := by
      intro x hx
      have hd : HasDerivAt (fun x => probeMap j a θ x - x)
          (1 + Complex.I * θ * deriv (probeH j a) x - 1) x :=
        (hasDerivAt_probeMap j a θ x).sub (hasDerivAt_id' x)
      rw [hd.deriv]
      have := hder x hx
      rwa [(hasDerivAt_probeMap j a θ x).deriv] at this
    have hlip := (convex_probeStrip j).norm_image_sub_le_of_norm_deriv_le hg hgb hw hz
    rw [hzw] at hlip
    have : ‖z - w‖ ≤ 1 / 2 * ‖z - w‖ := by
      have heq : probeMap j a θ w - z - (probeMap j a θ w - w) = -(z - w) := by ring
      calc ‖z - w‖ = ‖probeMap j a θ w - z - (probeMap j a θ w - w)‖ := by rw [heq, norm_neg]
        _ ≤ 1 / 2 * ‖z - w‖ := hlip
    have hzw0 : ‖z - w‖ = 0 := by linarith [norm_nonneg (z - w)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzw0)
  · -- `ϕ(U_j) ⊆ S_j`
    intro z hz
    have hzim : |z.im| < ell j / 4 := hz.2
    have hφ : ‖probeMap j a θ z - z‖ ≤ ell j / 4 := by
      unfold probeMap
      rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      calc |θ| * ‖probeH j a z‖ ≤ |θ| * C' :=
            mul_le_mul_of_nonneg_left (hH z (by linarith)) (abs_nonneg θ)
        _ ≤ ell j / 4 := hθC
    show |(probeMap j a θ z).im| < ell j
    have him : |(probeMap j a θ z).im - z.im| ≤ ell j / 4 := by
      rw [← Complex.sub_im]
      exact (Complex.abs_im_le_norm _).trans hφ
    have := abs_sub_abs_le_abs_sub (probeMap j a θ z).im z.im
    linarith

/-- `ϕ(0) = 0`. -/
theorem probeMap_zero (j : ℕ) (a θ : ℝ) : probeMap j a θ 0 = 0 := by
  unfold probeMap
  rw [probeH_zero, mul_zero, add_zero]

/-- `ϕ(1) = 1`. -/
theorem probeMap_one (j : ℕ) (a θ : ℝ) : probeMap j a θ 1 = 1 := by
  unfold probeMap
  rw [probeH_one, mul_zero, add_zero]

/-- Quantitative form of GA2 D5 (a): on the closed strip `|Im z| ≤ ℓ_j`,
`‖ϕ(z) - z‖ ≤ C|θ|` and `‖ϕ'(z) - 1‖ ≤ C|θ|/ℓ_j`, for every `j`, `a`, `θ`. -/
theorem probeMap_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (a θ : ℝ) (z : ℂ), |z.im| ≤ ell j →
      ‖probeMap j a θ z - z‖ ≤ C * |θ| ∧ ‖deriv (probeMap j a θ) z - 1‖ ≤ C * |θ| / ell j := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedDeriv_probeH_le 1 one_pos
  refine ⟨2 * C, by positivity, fun j a θ z hz => ⟨?_, ?_⟩⟩
  · have := hC j a 0 (by norm_num) z (by rw [one_mul]; exact hz)
    rw [iteratedDeriv_zero, pow_zero, mul_one] at this
    unfold probeMap
    rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    calc |θ| * ‖probeH j a z‖ ≤ |θ| * (C * 2) := by
          refine mul_le_mul_of_nonneg_left (this.trans ?_) (abs_nonneg θ)
          exact mul_le_mul_of_nonneg_left (envelope_le_two j a z.re) hC0
      _ = 2 * C * |θ| := by ring
  · have := hC j a 1 (by norm_num) z (by rw [one_mul]; exact hz)
    rw [iteratedDeriv_one, pow_one] at this
    have hℓ := ell_pos j
    rw [(hasDerivAt_probeMap j a θ z).deriv, add_sub_cancel_left, norm_mul, norm_mul,
      Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |θ| * ‖deriv (probeH j a) z‖ ≤ |θ| * (C * (ell j)⁻¹ * 2) := by
          refine mul_le_mul_of_nonneg_left (this.trans ?_) (abs_nonneg θ)
          exact mul_le_mul_of_nonneg_left (envelope_le_two j a z.re)
            (mul_nonneg hC0 (inv_nonneg.mpr hℓ.le))
      _ = 2 * C * |θ| / ell j := by field_simp

end SmallGammaGeodesics
