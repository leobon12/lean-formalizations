/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath
import InteractingSLE.Stochastic.Bessel.Uniqueness

/-!
# One force point: the Bessel construction (2.3), pathwise

Packet PROVE-SEC2-ONE. Specification pp. 19–21 (`source/spec/p001-048.md` L427–L447, (2.3), and the
first sentence of the proof of Theorem 2.2, L484): with a single force point the evolution of
Definition 2.1 is the Bessel construction

  `V_t = x₀ + ∫₀ᵗ 2 / (V_s − W_s) ds`,  `W_t = V_t ∓ √κ X_t`,

where `X = |V − W| / √κ` solves `X_t = x + b_t + ∫₀ᵗ c / X_s ds` with `c = (ρ + 2)/κ`,
`x = |x₀|/√κ` and `b = ±B`. Everything in this file is deterministic (one path at a time).

* `IsKilledPath c x b X ζ`: `X` solves the Bessel-type equation before the lifetime `ζ`, is
  nonnegative and continuous there, has a locally integrable reciprocal and a null zero set.
* `leftV`, `leftW`: the construction (2.3) for a force point on the left (`x₀ ≤ 0`).
* `isIntegratedSLEPath_left`: (2.3) is an integrated path of Definition 2.1 (the frozen
  `IsIntegratedSLEPath`, with `nL = 1`, `nR = 0`), given the threshold behaviour of `X`.
* `IsIntegratedSLEPath.isKilledPath_left`: conversely, every integrated path with one left force
  point is (2.3) for the killed path `X = (W − V) / √κ`.

Time integrals are interval integrals over `ℝ` of `s ↦ f s.toNNReal`, as in `IsIntegratedSLEPath`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace OneForce

/-! ### Killed Bessel-type paths -/

/-- `X` is a **killed Bessel-type path** with drift coefficient `c`, initial value `x`, driving
path `b` and lifetime `ζ`: `X 0 = x`, and before `ζ` the path is continuous and nonnegative, its
zero set is Lebesgue-null, `X⁻¹` is integrable on every `[0, t]`, and
`X t = x + b t + ∫₀ᵗ c / X s ds` (Specification (2.2), p. 19, up to the lifetime). -/
structure IsKilledPath (c x : ℝ) (b X : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop where
  zero : X 0 = x
  continuousOn : ContinuousOn X {t | (t : ℝ≥0∞) < ζ}
  nonneg : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → 0 ≤ X t
  volume_zero : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ X s.toNNReal = 0} = 0
  integrable : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
    IntervalIntegrable (fun s : ℝ => (X s.toNNReal)⁻¹) volume 0 t
  eq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → X t = x + b t + ∫ s in (0 : ℝ)..t, c / X s.toNNReal

/-- A global Bessel path (PROVE-BESSEL) started from `b 0 = 0` is a killed path with infinite
lifetime. -/
theorem _root_.InteractingSLE.Bessel.IsBesselPath.isKilledPath {c x : ℝ} {b X : ℝ≥0 → ℝ}
    (h : Bessel.IsBesselPath c x b X) (hb0 : b 0 = 0) : IsKilledPath c x b X ⊤ where
  zero := by rw [h.2.2.2.2 0, hb0]; simp
  continuousOn := h.1.continuousOn
  nonneg t _ := h.2.1 t
  volume_zero := by
    refine measure_mono_null (fun s hs => ?_) h.2.2.1
    exact ⟨hs.1, hs.2.2⟩
  integrable t _ := h.2.2.2.1 t
  eq t _ := h.2.2.2.2 t

/-! ### Threshold condition with one force point -/

/-- With one force point on the left, the continuation-threshold condition says that the force
point sits on the driver and its weight is at most `−2`. -/
theorem thresholdCondition_left_iff {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} {w : ℝ} {vL : Fin 1 → ℝ}
    {vR : Fin 0 → ℝ} :
    ForceWord.ThresholdCondition ρL ρR w vL vR ↔ vL 0 = w ∧ ρL 0 ≤ -2 := by
  unfold ForceWord.ThresholdCondition
  simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty, Finset.sum_filter,
    Fin.sum_univ_one]
  constructor
  · rintro (h | h)
    · split_ifs at h with hv
      · exact ⟨hv, h⟩
      · norm_num at h
    · norm_num at h
  · rintro ⟨hv, hρ⟩
    left
    simpa [hv] using hρ

/-- With one force point on the right, the continuation-threshold condition says that the force
point sits on the driver and its weight is at most `−2`. -/
theorem thresholdCondition_right_iff {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} {w : ℝ} {vL : Fin 0 → ℝ}
    {vR : Fin 1 → ℝ} :
    ForceWord.ThresholdCondition ρL ρR w vL vR ↔ vR 0 = w ∧ ρR 0 ≤ -2 := by
  unfold ForceWord.ThresholdCondition
  simp only [Finset.univ_eq_empty, Finset.filter_empty, Finset.sum_empty, Finset.sum_filter,
    Fin.sum_univ_one]
  constructor
  · rintro (h | h)
    · norm_num at h
    · split_ifs at h with hv
      · exact ⟨hv, h⟩
      · norm_num at h
  · rintro ⟨hv, hρ⟩
    right
    simpa [hv] using hρ


/-! ### Primitives before the lifetime -/

/-- A primitive `t ↦ ∫₀ᵗ g` of a function integrable on every `[0, t]`, `t < ζ`, is continuous
on `{t < ζ}`. -/
theorem continuousOn_primitive {g : ℝ → ℝ} {ζ : ℝ≥0∞}
    (hg : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → IntervalIntegrable g volume 0 t) :
    ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, g s) {t | (t : ℝ≥0∞) < ζ} := by
  intro t₀ ht₀
  obtain ⟨T, hT₀, hTζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
  have hT₀' : t₀ < T := by exact_mod_cast hT₀
  have hprim := intervalIntegral.continuousOn_primitive_interval' (hg T hTζ)
    (left_mem_uIcc (a := (0 : ℝ)) (b := (T : ℝ)))
  have hcomp : ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, g s) (Iic T) := by
    refine hprim.comp NNReal.continuous_coe.continuousOn fun t ht => ?_
    rw [uIcc_of_le T.coe_nonneg]
    exact ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  exact (hcomp.continuousAt (Iic_mem_nhds hT₀')).continuousWithinAt

/-- `∫₀ᵗ k / X = k · ∫₀ᵗ X⁻¹` (no integrability needed). -/
theorem integral_div_eq_mul (k : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, k / X s.toNNReal = k * ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹ := by
  rw [← intervalIntegral.integral_const_mul]
  simp only [div_eq_mul_inv]

/-- `k / (r · y) = (k / r) · y⁻¹`, also for `y = 0`. -/
theorem div_mul_eq_div_mul_inv (k r y : ℝ) : k / (r * y) = k / r * y⁻¹ := by
  rw [div_eq_mul_inv, mul_inv, div_eq_mul_inv]
  ring

/-- The algebra behind the driving equation of (2.3). -/
theorem driver_algebra {r : ℝ} (hr : r ≠ 0) (x₀ B I ρ : ℝ) :
    x₀ - 2 / r * I + r * (-x₀ / r + B + (ρ + 2) / r ^ 2 * I) = r * B + ρ / r * I := by
  field_simp
  ring

/-! ### The construction (2.3) with the force point on the left -/

/-- The left force point of (2.3): `V_t = x₀ + ∫₀ᵗ 2 / (−√a X_s) ds`. -/
def leftV (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  x₀ + ∫ s in (0 : ℝ)..t, 2 / -(Real.sqrt a * X s.toNNReal)

/-- The driver of (2.3) with the force point on the left: `W_t = V_t + √a X_t`. -/
def leftW (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := leftV a x₀ X t + Real.sqrt a * X t

theorem leftW_sub_leftV (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) :
    leftW a x₀ X t - leftV a x₀ X t = Real.sqrt a * X t := by
  simp only [leftW, add_sub_cancel_left]

theorem leftV_sub_leftW (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) :
    leftV a x₀ X t - leftW a x₀ X t = -(Real.sqrt a * X t) := by
  simp only [leftW, sub_add_cancel_left]

theorem leftV_eq_sub (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) :
    leftV a x₀ X t = x₀ - 2 / Real.sqrt a * ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹ := by
  rw [leftV, ← intervalIntegral.integral_const_mul, sub_eq_add_neg,
    ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [div_neg, div_mul_eq_div_mul_inv]

theorem leftV_zero (a x₀ : ℝ) (X : ℝ≥0 → ℝ) : leftV a x₀ X 0 = x₀ := by
  simp [leftV]

theorem continuousOn_leftV {a x₀ : ℝ} {X : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hX : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => (X s.toNNReal)⁻¹) volume 0 t) :
    ContinuousOn (leftV a x₀ X) {t | (t : ℝ≥0∞) < ζ} := by
  have h := continuousOn_primitive (g := fun s : ℝ => 2 / -(Real.sqrt a * X s.toNNReal))
    (ζ := ζ) fun t ht => ((hX t ht).const_mul (-(2 / Real.sqrt a))).congr fun s _ => by
      simp only [div_neg, div_mul_eq_div_mul_inv, neg_mul]
  exact continuousOn_const.add h

/-- **The construction (2.3), one force point on the left, is an integrated path of
Definition 2.1** (the frozen `IsIntegratedSLEPath` with `nL = 1`, `nR = 0`). The hypotheses on
`X` are the killed Bessel equation with `c = (ρ + 2)/a`, `x = −x₀/√a`, and the threshold
behaviour: `X` does not vanish before `ζ` when `ρ ≤ −2`; `ζ = 0` only when the seed already
satisfies the threshold condition; a finite positive `ζ` only when `ρ ≤ −2` and `X_t → 0`. -/
theorem isIntegratedSLEPath_left {a : ℝ} (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} {b X : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hX : IsKilledPath ((ρL 0 + 2) / a) (-xL 0 / Real.sqrt a) b X ζ)
    (hpos : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ρL 0 ≤ -2 → X t ≠ 0)
    (hζ0 : ζ = 0 → xL 0 = 0 ∧ ρL 0 ≤ -2)
    (hζT : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ρL 0 ≤ -2 ∧ Tendsto X (𝓝[<] T) (𝓝 0))
    (vR : Fin 0 → ℝ≥0 → ℝ) :
    IsIntegratedSLEPath a xL xR ρL ρR (leftW a (xL 0) X) (fun _ => leftV a (xL 0) X) vR b ζ := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr0 : Real.sqrt a ≠ 0 := hr.ne'
  have hra : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hxL : ∀ i : Fin 1, xL i = xL 0 := fun i => by rw [Fin.fin_one_eq_zero i]
  have hW0 : leftW a (xL 0) X 0 = 0 := by
    rw [leftW, leftV_zero, hX.zero]
    field_simp
    ring
  -- collisions are the zeros of `X`
  have hcoll : ∀ t : ℝ≥0, leftW a (xL 0) X t = leftV a (xL 0) X t ↔ X t = 0 := fun t => by
    rw [← sub_eq_zero, leftW_sub_leftV, mul_eq_zero, or_iff_right hr0]
  refine ⟨hW0, fun i => by show leftV a (xL 0) X 0 = xL i; rw [leftV_zero, hxL i],
    fun i => i.elim0, ?_, fun _ =>
    continuousOn_leftV hX.integrable, fun i => i.elim0, fun t _ => Subsingleton.antitone _,
    fun t ht _ => ?_, fun t _ i => i.elim0, fun t _ => Subsingleton.monotone _,
    fun t ht _ => ?_, fun t _ i => i.elim0, fun t ht => ?_, fun t ht i => ?_, fun _ _ i => i.elim0,
    fun _ => ?_, fun i => i.elim0, fun t ht => ?_, fun h => ?_, ?_⟩
  · -- continuity of `W`
    exact (continuousOn_leftV hX.integrable).add (continuousOn_const.mul hX.continuousOn)
  · -- `V ≤ W`
    rw [leftW]
    linarith [mul_nonneg hr.le (hX.nonneg t ht)]
  · -- integrability of the reciprocal gap
    refine ((hX.integrable t ht).const_mul (Real.sqrt a)⁻¹).congr fun s _ => ?_
    simp only [leftW_sub_leftV, mul_inv]
  · -- the driving equation
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.sum_univ_one,
      leftW_sub_leftV]
    rw [show (fun s : ℝ => ρL 0 / (Real.sqrt a * X s.toNNReal))
        = fun s : ℝ => ρL 0 / Real.sqrt a * (X s.toNNReal)⁻¹ from
        funext fun s => div_mul_eq_div_mul_inv _ _ _,
      intervalIntegral.integral_const_mul, leftW, leftV_eq_sub, hX.eq t ht,
      integral_div_eq_mul]
    have key := driver_algebra hr0 (xL 0) (b t) (∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹) (ρL 0)
    rw [hra] at key
    exact key
  · -- the force-point equation
    show leftV a (xL 0) X t = xL i + ∫ s in (0 : ℝ)..t,
      2 / (leftV a (xL 0) X s.toNNReal - leftW a (xL 0) X s.toNNReal)
    rw [hxL i, leftV]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [leftV_sub_leftW]
  · -- collisions are null
    refine measure_mono_null (fun s hs => ?_) hX.volume_zero
    exact ⟨hs.1, hs.2.1, (hcoll _).1 hs.2.2⟩
  · -- the threshold condition fails before `ζ`
    rw [thresholdCondition_left_iff]
    rintro ⟨hv, hρ⟩
    exact hpos t ht hρ ((hcoll t).1 hv.symm)
  · -- the seed when `ζ = 0`
    rw [thresholdCondition_left_iff]
    exact ⟨(hζ0 h).1, (hζ0 h).2⟩
  · -- a finite positive lifetime
    intro T hT hTζ w₀ vL₀ vR₀ hlim
    rw [thresholdCondition_left_iff]
    obtain ⟨hρ, hXT⟩ := hζT T hT hTζ
    refine ⟨?_, hρ⟩
    have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
    have hw : Tendsto (leftW a (xL 0) X) (𝓝[<] T) (𝓝 w₀) :=
      (continuous_fst.tendsto _).comp hlim
    have hv : Tendsto (leftV a (xL 0) X) (𝓝[<] T) (𝓝 (vL₀ 0)) :=
      ((continuous_apply 0).tendsto _).comp ((continuous_fst.tendsto _).comp
        ((continuous_snd.tendsto _).comp hlim))
    have h1 : Tendsto (fun t => leftW a (xL 0) X t - leftV a (xL 0) X t) (𝓝[<] T)
        (𝓝 (w₀ - vL₀ 0)) := hw.sub hv
    have h2 : Tendsto (fun t => leftW a (xL 0) X t - leftV a (xL 0) X t) (𝓝[<] T)
        (𝓝 (Real.sqrt a * 0)) := by
      simp only [leftW_sub_leftV]
      exact hXT.const_mul _
    have := tendsto_nhds_unique h1 h2
    rw [mul_zero, sub_eq_zero] at this
    exact this.symm


/-! ### The construction (2.3) with the force point on the right -/

/-- The algebra behind the driving equation of (2.3), right force point. -/
theorem driver_algebra_right {r : ℝ} (hr : r ≠ 0) (x₀ B I ρ : ℝ) :
    x₀ + 2 / r * I - r * (x₀ / r + -B + (ρ + 2) / r ^ 2 * I) = r * B + -ρ / r * I := by
  field_simp
  ring

/-- The right force point of (2.3): `V_t = x₀ + ∫₀ᵗ 2 / (√a X_s) ds`. -/
def rightV (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  x₀ + ∫ s in (0 : ℝ)..t, 2 / (Real.sqrt a * X s.toNNReal)

/-- The driver of (2.3) with the force point on the right: `W_t = V_t − √a X_t`. -/
def rightW (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := rightV a x₀ X t - Real.sqrt a * X t

theorem rightV_sub_rightW (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) :
    rightV a x₀ X t - rightW a x₀ X t = Real.sqrt a * X t := by
  simp only [rightW, sub_sub_cancel]

theorem rightW_sub_rightV (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) :
    rightW a x₀ X t - rightV a x₀ X t = -(Real.sqrt a * X t) := by
  simp only [rightW, sub_sub_cancel_left]

theorem rightV_eq_add (a x₀ : ℝ) (X : ℝ≥0 → ℝ) (t : ℝ≥0) :
    rightV a x₀ X t = x₀ + 2 / Real.sqrt a * ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹ := by
  rw [rightV, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [div_mul_eq_div_mul_inv]

theorem rightV_zero (a x₀ : ℝ) (X : ℝ≥0 → ℝ) : rightV a x₀ X 0 = x₀ := by
  simp [rightV]

theorem continuousOn_rightV {a x₀ : ℝ} {X : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hX : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun s : ℝ => (X s.toNNReal)⁻¹) volume 0 t) :
    ContinuousOn (rightV a x₀ X) {t | (t : ℝ≥0∞) < ζ} := by
  have h := continuousOn_primitive (g := fun s : ℝ => 2 / (Real.sqrt a * X s.toNNReal))
    (ζ := ζ) fun t ht => ((hX t ht).const_mul (2 / Real.sqrt a)).congr fun s _ => by
      simp only [div_mul_eq_div_mul_inv]
  exact continuousOn_const.add h

/-- **The construction (2.3), one force point on the right, is an integrated path of
Definition 2.1** (the frozen `IsIntegratedSLEPath` with `nL = 0`, `nR = 1`): the standard
single-force-point `SLE_a(ρ)`. The killed path `X = (V − W)/√a` is driven by `−b`, with
`c = (ρ + 2)/a` and `x = x₀/√a`; the threshold hypotheses are as in `isIntegratedSLEPath_left`. -/
theorem isIntegratedSLEPath_right {a : ℝ} (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} {b X : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hX : IsKilledPath ((ρR 0 + 2) / a) (xR 0 / Real.sqrt a) (fun t => -b t) X ζ)
    (hpos : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ρR 0 ≤ -2 → X t ≠ 0)
    (hζ0 : ζ = 0 → xR 0 = 0 ∧ ρR 0 ≤ -2)
    (hζT : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ρR 0 ≤ -2 ∧ Tendsto X (𝓝[<] T) (𝓝 0))
    (vL : Fin 0 → ℝ≥0 → ℝ) :
    IsIntegratedSLEPath a xL xR ρL ρR (rightW a (xR 0) X) vL (fun _ => rightV a (xR 0) X) b ζ := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr0 : Real.sqrt a ≠ 0 := hr.ne'
  have hra : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hxR : ∀ i : Fin 1, xR i = xR 0 := fun i => by rw [Fin.fin_one_eq_zero i]
  have hW0 : rightW a (xR 0) X 0 = 0 := by
    rw [rightW, rightV_zero, hX.zero]
    field_simp
    ring
  have hcoll : ∀ t : ℝ≥0, rightW a (xR 0) X t = rightV a (xR 0) X t ↔ X t = 0 := fun t => by
    rw [← sub_eq_zero, rightW_sub_rightV, neg_eq_zero, mul_eq_zero, or_iff_right hr0]
  refine ⟨hW0, fun i => i.elim0, fun i => by
    show rightV a (xR 0) X 0 = xR i; rw [rightV_zero, hxR i], ?_, fun i => i.elim0,
    fun _ => continuousOn_rightV hX.integrable, fun t _ => Subsingleton.antitone _,
    fun t _ i => i.elim0, fun t ht _ => ?_, fun t _ => Subsingleton.monotone _,
    fun t _ i => i.elim0, fun t ht _ => ?_, fun t ht => ?_, fun _ _ i => i.elim0, fun t ht i => ?_,
    fun i => i.elim0, fun _ => ?_, fun t ht => ?_, fun h => ?_, ?_⟩
  · -- continuity of `W`
    exact (continuousOn_rightV hX.integrable).sub (continuousOn_const.mul hX.continuousOn)
  · -- `W ≤ V`
    rw [rightW]
    linarith [mul_nonneg hr.le (hX.nonneg t ht)]
  · -- integrability of the reciprocal gap
    refine (((hX.integrable t ht).const_mul (Real.sqrt a)⁻¹).neg).congr fun s _ => ?_
    simp only [rightW_sub_rightV, inv_neg, mul_inv, Pi.neg_apply]
  · -- the driving equation
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.sum_univ_one,
      rightW_sub_rightV]
    rw [show (fun s : ℝ => ρR 0 / -(Real.sqrt a * X s.toNNReal))
        = fun s : ℝ => -ρR 0 / Real.sqrt a * (X s.toNNReal)⁻¹ from
        funext fun s => by rw [div_neg, div_mul_eq_div_mul_inv, neg_div, neg_mul],
      intervalIntegral.integral_const_mul, rightW, rightV_eq_add, hX.eq t ht,
      integral_div_eq_mul]
    have key := driver_algebra_right hr0 (xR 0) (b t)
      (∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹) (ρR 0)
    rw [hra] at key
    exact key
  · -- the force-point equation
    show rightV a (xR 0) X t = xR i + ∫ s in (0 : ℝ)..t,
      2 / (rightV a (xR 0) X s.toNNReal - rightW a (xR 0) X s.toNNReal)
    rw [hxR i, rightV]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [rightV_sub_rightW]
  · -- collisions are null
    refine measure_mono_null (fun s hs => ?_) hX.volume_zero
    exact ⟨hs.1, hs.2.1, (hcoll _).1 hs.2.2⟩
  · -- the threshold condition fails before `ζ`
    rw [thresholdCondition_right_iff]
    rintro ⟨hv, hρ⟩
    exact hpos t ht hρ ((hcoll t).1 hv.symm)
  · -- the seed when `ζ = 0`
    rw [thresholdCondition_right_iff]
    exact ⟨(hζ0 h).1, (hζ0 h).2⟩
  · -- a finite positive lifetime
    intro T hT hTζ w₀ vL₀ vR₀ hlim
    rw [thresholdCondition_right_iff]
    obtain ⟨hρ, hXT⟩ := hζT T hT hTζ
    refine ⟨?_, hρ⟩
    have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
    have hw : Tendsto (rightW a (xR 0) X) (𝓝[<] T) (𝓝 w₀) :=
      (continuous_fst.tendsto _).comp hlim
    have hv : Tendsto (rightV a (xR 0) X) (𝓝[<] T) (𝓝 (vR₀ 0)) :=
      ((continuous_apply 0).tendsto _).comp ((continuous_snd.tendsto _).comp
        ((continuous_snd.tendsto _).comp hlim))
    have h1 : Tendsto (fun t => rightV a (xR 0) X t - rightW a (xR 0) X t) (𝓝[<] T)
        (𝓝 (vR₀ 0 - w₀)) := hv.sub hw
    have h2 : Tendsto (fun t => rightV a (xR 0) X t - rightW a (xR 0) X t) (𝓝[<] T)
        (𝓝 (Real.sqrt a * 0)) := by
      simp only [rightV_sub_rightW]
      exact hXT.const_mul _
    have := tendsto_nhds_unique h1 h2
    rw [mul_zero, sub_eq_zero] at this
    exact this


/-! ### Every integrated path with one force point is (2.3) -/

/-- **Left force point, converse of `isIntegratedSLEPath_left`.** For an integrated path of
Definition 2.1 with one left force point, `X = (W − V)/√a` is a killed path with
`c = (ρ + 2)/a`, `x = −x₀/√a` and driving path `b`, and `(V, W)` is the construction (2.3) from `X`
before the lifetime. -/
theorem isKilledPath_left {a : ℝ} (ha : 0 < a) {xL : Fin 1 → ℝ} {xR : Fin 0 → ℝ}
    {ρL : Fin 1 → ℝ} {ρR : Fin 0 → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 1 → ℝ≥0 → ℝ}
    {vR : Fin 0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    IsKilledPath ((ρL 0 + 2) / a) (-xL 0 / Real.sqrt a) b
        (fun t => (w t - vL 0 t) / Real.sqrt a) ζ ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
        vL 0 t = leftV a (xL 0) (fun t => (w t - vL 0 t) / Real.sqrt a) t ∧
        w t = leftW a (xL 0) (fun t => (w t - vL 0 t) / Real.sqrt a) t := by
  obtain ⟨hw0, hvL0, -, hwc, hvLc, -, -, hvw, -, -, hgap, -, hweq, hvLeq, -, hcoll, -, -, -, -⟩ := h
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr0 : Real.sqrt a ≠ 0 := hr.ne'
  have hra : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  set X : ℝ≥0 → ℝ := fun t => (w t - vL 0 t) / Real.sqrt a with hXdef
  have hG : ∀ t, w t - vL 0 t = Real.sqrt a * X t := fun t => by
    simp only [hXdef]; field_simp
  -- the force point is `leftV` of `X`
  have hV : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vL 0 t = leftV a (xL 0) X t := fun t ht => by
    rw [hvLeq t ht 0, leftV]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← neg_sub, hG]
  refine ⟨⟨?_, ?_, fun t ht => ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩, fun t ht =>
    ⟨hV t ht, ?_⟩⟩
  · simp only [hXdef, hw0, hvL0 0, zero_sub]
  · exact ((hwc.sub (hvLc 0)).div_const _)
  · exact div_nonneg (sub_nonneg.2 (hvw t ht 0)) hr.le
  · refine measure_mono_null (fun s hs => ?_) (hcoll 0)
    refine ⟨hs.1, hs.2.1, ?_⟩
    have := hs.2.2
    simp only [hXdef, div_eq_zero_iff, hr0, or_false, sub_eq_zero] at this
    exact this
  · refine ((hgap t ht 0).const_mul (Real.sqrt a)).congr fun s _ => ?_
    simp only [hG, mul_inv, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  · -- the Bessel-type equation for `X`
    have hw := hweq t ht
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.sum_univ_one] at hw
    have hwI : ∫ s in (0 : ℝ)..t, ρL 0 / (w s.toNNReal - vL 0 s.toNNReal)
        = ρL 0 / Real.sqrt a * ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [hG, div_mul_eq_div_mul_inv]
    have hvI := hV t ht
    rw [leftV_eq_sub] at hvI
    rw [hwI] at hw
    rw [integral_div_eq_mul]
    have key : Real.sqrt a * X t = Real.sqrt a * (-xL 0 / Real.sqrt a + b t
        + (ρL 0 + 2) / a * ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹) := by
      rw [← hG, hw, hvI, show (ρL 0 + 2) / a = (ρL 0 + 2) / Real.sqrt a ^ 2 by rw [hra]]
      field_simp
      ring
    exact mul_left_cancel₀ hr0 key
  · rw [leftW, ← hV t ht, ← hG]
    ring

/-- **Right force point, converse of `isIntegratedSLEPath_right`.** For an integrated path of
Definition 2.1 with one right force point, `X = (V − W)/√a` is a killed path with
`c = (ρ + 2)/a`, `x = x₀/√a` and driving path `−b`, and `(V, W)` is the construction (2.3) from
`X` before the lifetime. -/
theorem isKilledPath_right {a : ℝ} (ha : 0 < a) {xL : Fin 0 → ℝ} {xR : Fin 1 → ℝ}
    {ρL : Fin 0 → ℝ} {ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ}
    {vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    IsKilledPath ((ρR 0 + 2) / a) (xR 0 / Real.sqrt a) (fun t => -b t)
        (fun t => (vR 0 t - w t) / Real.sqrt a) ζ ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ →
        vR 0 t = rightV a (xR 0) (fun t => (vR 0 t - w t) / Real.sqrt a) t ∧
        w t = rightW a (xR 0) (fun t => (vR 0 t - w t) / Real.sqrt a) t := by
  obtain ⟨hw0, -, hvR0, hwc, -, hvRc, -, -, hwv, -, -, hgap, hweq, -, hvReq, -, hcoll, -, -, -⟩ := h
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hr0 : Real.sqrt a ≠ 0 := hr.ne'
  have hra : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  set X : ℝ≥0 → ℝ := fun t => (vR 0 t - w t) / Real.sqrt a with hXdef
  have hG : ∀ t, vR 0 t - w t = Real.sqrt a * X t := fun t => by
    simp only [hXdef]; field_simp
  have hV : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → vR 0 t = rightV a (xR 0) X t := fun t ht => by
    rw [hvReq t ht 0, rightV]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [hG]
  refine ⟨⟨?_, ?_, fun t ht => ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩, fun t ht =>
    ⟨hV t ht, ?_⟩⟩
  · simp only [hXdef, hw0, hvR0 0, sub_zero]
  · exact (((hvRc 0).sub hwc).div_const _)
  · exact div_nonneg (sub_nonneg.2 (hwv t ht 0)) hr.le
  · refine measure_mono_null (fun s hs => ?_) (hcoll 0)
    refine ⟨hs.1, hs.2.1, ?_⟩
    have := hs.2.2
    simp only [hXdef, div_eq_zero_iff, hr0, or_false, sub_eq_zero] at this
    exact this.symm
  · refine (((hgap t ht 0).const_mul (Real.sqrt a)).neg).congr fun s _ => ?_
    simp only [Pi.neg_apply]
    rw [← neg_sub, hG, inv_neg, mul_neg, neg_neg, mul_inv, ← mul_assoc, mul_inv_cancel₀ hr0,
      one_mul]
  · have hw := hweq t ht
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.sum_univ_one] at hw
    have hwI : ∫ s in (0 : ℝ)..t, ρR 0 / (w s.toNNReal - vR 0 s.toNNReal)
        = -ρR 0 / Real.sqrt a * ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [← neg_sub, hG, div_neg, div_mul_eq_div_mul_inv, neg_div, neg_mul]
    have hvI := hV t ht
    rw [rightV_eq_add] at hvI
    rw [hwI] at hw
    rw [integral_div_eq_mul]
    have key : Real.sqrt a * X t = Real.sqrt a * (xR 0 / Real.sqrt a + -b t
        + (ρR 0 + 2) / a * ∫ s in (0 : ℝ)..t, (X s.toNNReal)⁻¹) := by
      rw [← hG, hw, hvI, show (ρR 0 + 2) / a = (ρR 0 + 2) / Real.sqrt a ^ 2 by rw [hra]]
      field_simp
      ring
    exact mul_left_cancel₀ hr0 key
  · rw [rightW, ← hV t ht, ← hG]
    ring


/-! ### Pathwise uniqueness before the lifetime when `c > 0` -/

namespace IsKilledPath

variable {c x : ℝ} {b X Y : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}

/-- A time in `[0, t]` with `t < ζ` is before `ζ`. -/
theorem toNNReal_lt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    (s.toNNReal : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht

theorem continuousOn_real (hX : IsKilledPath c x b X ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ContinuousOn (fun s : ℝ => X s.toNNReal) (Icc 0 t) :=
  hX.continuousOn.comp continuous_real_toNNReal.continuousOn fun _ hs => toNNReal_lt ht hs

theorem intervalIntegrable_div (hX : IsKilledPath c x b X ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun s : ℝ => c / X s.toNNReal) volume 0 t :=
  ((hX.integrable t ht).const_mul c).congr fun s _ => by simp only [div_eq_mul_inv]

/-- Almost every time before the lifetime is not a zero of `X`. -/
theorem ae_pos (hX : IsKilledPath c x b X ζ) :
    ∀ᵐ s : ℝ ∂volume, 0 ≤ s → (s.toNNReal : ℝ≥0∞) < ζ → 0 < X s.toNNReal := by
  have h0 := measure_eq_zero_iff_ae_notMem.1 hX.volume_zero
  filter_upwards [h0] with s hs hs0 hsζ
  rcases (hX.nonneg _ hsζ).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ⟨hs0, hsζ, heq.symm⟩ hs

/-- **Comparison before the lifetime** (`c > 0`): two killed paths with the same data are
ordered at every common time before both lifetimes. -/
theorem le_of_pos (hc : 0 < c) (hX : IsKilledPath c x b X ζ) (hY : IsKilledPath c x b Y ζ')
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (ht' : (t : ℝ≥0∞) < ζ') : X t ≤ Y t := by
  have key := Bessel.le_of_sub_eq_integral (T := t) (X := fun s : ℝ => X s.toNNReal)
    (Y := fun s : ℝ => Y s.toNNReal) (f := fun s => c / X s.toNNReal)
    (h := fun s => c / Y s.toNNReal) (hX.continuousOn_real ht) (hY.continuousOn_real ht')
    (hX.intervalIntegrable_div ht) (hY.intervalIntegrable_div ht') ?_ ?_ ?_ t
    ⟨t.coe_nonneg, le_rfl⟩
  · simpa using key
  · simp only [Real.toNNReal_zero, hX.zero, hY.zero, le_refl]
  · intro s hs
    have hsX := toNNReal_lt ht hs
    have hsY := toNNReal_lt ht' hs
    have hint := hX.intervalIntegrable_div hsX
    have hint' := hY.intervalIntegrable_div hsY
    rw [Real.coe_toNNReal s hs.1] at hint hint'
    simp only [Real.toNNReal_zero, hX.zero, hY.zero, sub_self, zero_add]
    rw [hX.eq _ hsX, hY.eq _ hsY, Real.coe_toNNReal s hs.1,
      intervalIntegral.integral_sub hint hint']
    ring
  · filter_upwards [hY.ae_pos] with s hYpos hs hlt
    have hYs := hYpos hs.1 (toNNReal_lt ht' hs)
    exact div_le_div_of_nonneg_left hc.le hYs hlt.le

/-- **Pathwise uniqueness before the lifetime** (`c > 0`). -/
theorem eq_of_pos (hc : 0 < c) (hX : IsKilledPath c x b X ζ) (hY : IsKilledPath c x b Y ζ')
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (ht' : (t : ℝ≥0∞) < ζ') : X t = Y t :=
  le_antisymm (hX.le_of_pos hc hY ht ht') (hY.le_of_pos hc hX ht' ht)

end IsKilledPath

end OneForce

end InteractingSLE
