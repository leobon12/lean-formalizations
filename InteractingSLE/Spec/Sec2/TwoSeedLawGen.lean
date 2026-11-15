/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedAngle
import InteractingSLE.Spec.Sec2.JacobiMoments
import InteractingSLE.Spec.Ito.Observable

/-!
# Two seeds: the Itô generator of the angle in physical time

Packet PROVE-SEC2-JAC2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md`, L540–L546):
"the change of clock `u = log ℓ_t` transforms `X` into precisely the Jacobi diffusion above". This file is
the deterministic (pathwise) half of that identification, for a path of the frozen `IsIntegratedSLEPath`
with one force point on each side, both at `0` (`0⁻, 0⁺`).

Write `X = W − V^L`, `Y = V^R − W`, `ℓ = X + Y` (`gapLR`, `gapRR`, `sepN`). The pair

`Λ_t = (W_t − √κ b_t − V^L_t, ℓ_t)` (`acCoord`)

is absolutely continuous, with density `λ = ((ρ_L+2)/X − ρ_R/Y, 2/X + 2/Y)` (`acDens`,
`acCoord_eq_integral`), and of total variation at most `C ℓ_t` (`integral_norm_acDens_le`). The angle
`A = X/ℓ = (√κ b + Λ¹)/Λ²` is the smooth function `angleObs` of `(Λ, b)` (with the denominator cut off
below the level `c/2`), and its Itô generator `∂_Λ A^n · λ + ½ ∂²_b A^n` is (`itoGen_angleObs_path`)

`ℓ'_t / ℓ_t · L(x ↦ x^n)(A_t)`,  `L` the Jacobi generator with `a = ρ_L + 2`, `b = ρ_R + 2`

(`Jacobi.gen`), wherever both gaps are positive. Since `du = dℓ/ℓ` in the logarithmic clock, the
separation's push-forward identity of `TwoSeedLogClock` turns the time integral of this generator between
the hitting times of the levels `e^w` and `e^v` into `∫_w^v L(x^n)(U_x) dx` (`integral_itoGen_angleObs`),
`U` the logarithmic-clock angle (`logAngle`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

/-! ### The absolutely continuous coordinates -/

/-- The absolutely continuous coordinates `Λ_t = (W_t − √κ b_t − V^L_t, ℓ_t)` of a two-seed path. -/
def acCoord (κ : ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ × ℝ :=
  (w t - Real.sqrt κ * b t - vL 0 t, sepN vL vR t)

/-- The density `λ_s = ((ρ_L + 2)/X_s − ρ_R/Y_s, 2/X_s + 2/Y_s)` of `acCoord`. -/
def acDens (ρL ρR : Fin 1 → ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (s : ℝ) : ℝ × ℝ :=
  ((ρL 0 + 2) / gapLR w vL s - ρR 0 / gapRR w vR s, sepRate w vL vR s)

/-- The interval integral of a pair is the pair of interval integrals. -/
theorem intervalIntegral_prodMk {f g : ℝ → ℝ} {a c : ℝ} (hf : IntervalIntegrable f volume a c)
    (hg : IntervalIntegrable g volume a c) :
    ∫ s in a..c, ((f s, g s) : ℝ × ℝ) = (∫ s in a..c, f s, ∫ s in a..c, g s) := by
  have hfg : IntervalIntegrable (fun s => ((f s, g s) : ℝ × ℝ)) volume a c :=
    ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩
  refine Prod.ext ?_ ?_
  · exact ((ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hfg).symm
  · exact ((ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hfg).symm

section Path

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

theorem path_w_eq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    w t = Real.sqrt κ * b t
      + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := h; exact h t ht

theorem intervalIntegrable_div_gapLR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (c : ℝ) :
    IntervalIntegrable (fun s => c / gapLR w vL s) volume 0 t := by
  simpa only [gapLR, div_eq_mul_inv] using (path_integrable_gapL h ht).const_mul c

theorem intervalIntegrable_div_gapRR {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (c : ℝ) :
    IntervalIntegrable (fun s => c / gapRR w vR s) volume 0 t := by
  refine ((path_integrable_gapR h ht).const_mul (-c)).congr fun s _ => ?_
  simp only [gapRR]
  rw [← neg_sub, inv_neg, div_eq_mul_inv]
  ring

/-- The first coordinate: `W_t − √κ b_t − V^L_t = ∫_0^t ((ρ_L + 2)/X − ρ_R/Y)`. -/
theorem acCoord_fst_eq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    w t - Real.sqrt κ * b t - vL 0 t =
      ∫ s in (0 : ℝ)..t, ((ρL 0 + 2) / gapLR w vL s - ρR 0 / gapRR w vR s) := by
  have hw := path_w_eq h ht
  simp only [Fin.sum_univ_one] at hw
  have hR : ∫ s in (0 : ℝ)..t, ρR 0 / (w s.toNNReal - vR 0 s.toNNReal) =
      -∫ s in (0 : ℝ)..t, ρR 0 / gapRR w vR s := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [gapRR]
    rw [← neg_sub, div_neg]
  have hL : ∫ s in (0 : ℝ)..t, ρL 0 / (w s.toNNReal - vL 0 s.toNNReal) =
      ∫ s in (0 : ℝ)..t, ρL 0 / gapLR w vL s := rfl
  rw [intervalIntegral.integral_sub ((intervalIntegrable_div_gapLR h ht _))
    (intervalIntegrable_div_gapRR h ht _), hw, hR, hL, vL_eq_neg_integral h ht]
  have hsplit : ∫ s in (0 : ℝ)..t, (ρL 0 + 2) / gapLR w vL s =
      (∫ s in (0 : ℝ)..t, ρL 0 / gapLR w vL s) + ∫ s in (0 : ℝ)..t, 2 / gapLR w vL s := by
    rw [← intervalIntegral.integral_add (intervalIntegrable_div_gapLR h ht _)
      (intervalIntegrable_div_gapLR h ht _)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [add_div]
  rw [hsplit]
  ring

theorem intervalIntegrable_acDens {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (acDens ρL ρR w vL vR) volume 0 t := by
  have h1 := (intervalIntegrable_div_gapLR h ht (ρL 0 + 2)).sub
    (intervalIntegrable_div_gapRR h ht (ρR 0))
  have h2 := intervalIntegrable_sepRate h ht
  exact ⟨h1.1.prodMk h2.1, h1.2.prodMk h2.2⟩

/-- **`Λ` is absolutely continuous**: `Λ_t = ∫_0^t λ`. -/
theorem acCoord_eq_integral {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    acCoord κ w vL vR b t = ∫ s in (0 : ℝ)..t, acDens ρL ρR w vL vR s := by
  simp only [acDens]
  rw [intervalIntegral_prodMk ((intervalIntegrable_div_gapLR h ht _).sub
    (intervalIntegrable_div_gapRR h ht _)) (intervalIntegrable_sepRate h ht), acCoord,
    acCoord_fst_eq h ht, sepN_eq_integral h ht]

theorem acCoord_zero (hζ : 0 < ζ) : acCoord κ w vL vR b 0 = 0 := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := by simpa using hζ
  rw [acCoord_eq_integral h h0, NNReal.coe_zero, intervalIntegral.integral_same]

/-- `Λ_t = Λ_0 + ∫_0^t λ` (the form used by the localized Itô formula). -/
theorem acCoord_eq_add_integral {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    acCoord κ w vL vR b t = acCoord κ w vL vR b 0 + ∫ s in (0 : ℝ)..t, acDens ρL ρR w vL vR s := by
  rw [acCoord_zero h (lt_of_le_of_lt bot_le ht), zero_add, acCoord_eq_integral h ht]

/-- **Bounded variation**: `∫_0^t ‖λ‖ ≤ C ℓ_t / 2`, `C = |ρ_L + 2| + |ρ_R| + 2`. -/
theorem integral_norm_acDens_le {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    ∫ s in (0 : ℝ)..t, ‖acDens ρL ρR w vL vR s‖ ≤
      (|ρL 0 + 2| + |ρR 0| + 2) / 2 * sepN vL vR t := by
  rw [sepN_eq_integral h ht, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on t.coe_nonneg (intervalIntegrable_acDens h ht).norm
    ((intervalIntegrable_sepRate h ht).const_mul _) fun s hs => ?_
  have hX := gapLR_nonneg h ht hs.2
  have hY := gapRR_nonneg h ht hs.2
  set X := gapLR w vL s
  set Y := gapRR w vR s
  have hXi : 0 ≤ X⁻¹ := inv_nonneg.2 hX
  have hYi : 0 ≤ Y⁻¹ := inv_nonneg.2 hY
  simp only [acDens, sepRate]
  rw [Prod.norm_def]
  have h1 : ‖(ρL 0 + 2) / X - ρR 0 / Y‖ ≤ |ρL 0 + 2| * X⁻¹ + |ρR 0| * Y⁻¹ := by
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_div, abs_of_nonneg hX, abs_of_nonneg hY, div_eq_mul_inv, div_eq_mul_inv]
  have h2 : ‖2 / X + 2 / Y‖ = 2 * X⁻¹ + 2 * Y⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (div_nonneg zero_le_two hX)
      (div_nonneg zero_le_two hY)), div_eq_mul_inv, div_eq_mul_inv]
  have hA := abs_nonneg (ρL 0 + 2)
  have hB := abs_nonneg (ρR 0)
  refine max_le (h1.trans ?_) (h2.le.trans ?_)
  · rw [div_eq_mul_inv 2 X, div_eq_mul_inv 2 Y]; nlinarith
  · rw [div_eq_mul_inv 2 X, div_eq_mul_inv 2 Y]; nlinarith

end Path

/-! ### The smooth angle observable -/

/-- A smooth lower cut-off of the denominator: `cutψ c y = y` for `y ≥ c/2` and `cutψ c y ≥ c/4`. -/
def cutψ (c y : ℝ) : ℝ := c / 4 + (y - c / 4) * Real.smoothTransition ((y - c / 4) / (c / 4))

theorem contDiff_cutψ (c : ℝ) : ContDiff ℝ 3 (cutψ c) := by
  unfold cutψ
  exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
    ((Real.smoothTransition.contDiff (n := 3)).comp ((contDiff_id.sub contDiff_const).div_const _)))

theorem cutψ_of_le {c y : ℝ} (hc : 0 < c) (hy : c / 2 ≤ y) : cutψ c y = y := by
  unfold cutψ
  rw [Real.smoothTransition.one_of_one_le, mul_one]
  · ring
  · rw [le_div_iff₀ (by positivity)]; linarith

theorem le_cutψ {c : ℝ} (hc : 0 < c) (y : ℝ) : c / 4 ≤ cutψ c y := by
  unfold cutψ
  rcases le_or_gt y (c / 4) with hy | hy
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
      (by positivity)), mul_zero, add_zero]
  · have := Real.smoothTransition.nonneg ((y - c / 4) / (c / 4))
    nlinarith

theorem cutψ_pos {c : ℝ} (hc : 0 < c) (y : ℝ) : 0 < cutψ c y :=
  lt_of_lt_of_le (by positivity) (le_cutψ hc y)

theorem cutψ_eventuallyEq {c y : ℝ} (hc : 0 < c) (hy : c / 2 < y) : cutψ c =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem (Ioi_mem_nhds hy) fun _ hz => cutψ_of_le hc (le_of_lt hz)

/-- The angle `A^n = ((√κ x + Λ¹)/Λ²)^n` as a smooth function of `(Λ, x)`, the denominator cut off below
`c/2`. -/
def angleObs (κ c : ℝ) (n : ℕ) (p : (ℝ × ℝ) × ℝ) : ℝ :=
  ((Real.sqrt κ * p.2 + p.1.1) / cutψ c p.1.2) ^ n

theorem contDiff_angleObs (κ : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) : ContDiff ℝ 3 (angleObs κ c n) := by
  unfold angleObs
  refine ContDiff.pow ?_ n
  refine ContDiff.div ((contDiff_const.mul contDiff_snd).add (contDiff_fst.comp contDiff_fst))
    ((contDiff_cutψ c).comp (contDiff_snd.comp contDiff_fst)) fun p => (cutψ_pos hc _).ne'

/-- **The Itô generator of the angle observable** above the cut-off level. -/
theorem itoGen_angleObs (κ : ℝ) {c : ℝ} (hc : 0 < c) (n : ℕ) {p : (ℝ × ℝ) × ℝ}
    (hp : c / 2 < p.1.2) (v : ℝ × ℝ) :
    Ito.itoGen (angleObs κ c n) p v =
      n * ((Real.sqrt κ * p.2 + p.1.1) / p.1.2) ^ (n - 1) *
          ((v.1 * p.1.2 - (Real.sqrt κ * p.2 + p.1.1) * v.2) / p.1.2 ^ 2) +
        1 / 2 * (n * ((n - 1 : ℕ) * ((Real.sqrt κ * p.2 + p.1.1) / p.1.2) ^ (n - 1 - 1) *
          (Real.sqrt κ / p.1.2)) * (Real.sqrt κ / p.1.2)) := by
  have hF := contDiff_angleObs κ hc n
  have hℓ : p.1.2 ≠ 0 := (lt_trans (by positivity) hp).ne'
  set r := Real.sqrt κ * p.2 + p.1.1 with hr
  set ℓ := p.1.2 with hℓdef
  -- the first-order part, along the line `t ↦ (Λ + t v, x)`
  have hfst : Ito.partialFst (angleObs κ c n) p v =
      n * (r / ℓ) ^ (n - 1) * ((v.1 * ℓ - r * v.2) / ℓ ^ 2) := by
    refine Ito.partialFst_eq_of_hasDerivAt (hF.differentiable (by norm_num)).differentiableAt ?_
    have hg : HasDerivAt (fun t : ℝ => (r + t * v.1) / (ℓ + t * v.2))
        ((v.1 * ℓ - r * v.2) / ℓ ^ 2) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => r + t * v.1) v.1 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.1).const_add r
      have h2 : HasDerivAt (fun t : ℝ => ℓ + t * v.2) v.2 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.2).const_add ℓ
      have := h1.div h2 (by simpa using hℓ)
      have e : (v.1 * (ℓ + 0 * v.2) - (r + 0 * v.1) * v.2) / (ℓ + 0 * v.2) ^ 2 =
          (v.1 * ℓ - r * v.2) / ℓ ^ 2 := by simp
      rw [e] at this
      exact this
    have hgn := hg.pow n
    simp only [zero_mul, add_zero] at hgn
    refine hgn.congr_of_eventuallyEq ?_
    have hcont : Continuous fun t : ℝ => ℓ + t * v.2 := by fun_prop
    have hev : ∀ᶠ t in 𝓝 (0 : ℝ), c / 2 < ℓ + t * v.2 :=
      hcont.continuousAt.eventually (Ioi_mem_nhds (by simpa using hp))
    filter_upwards [hev] with t ht
    simp only [angleObs, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [cutψ_of_le hc ht.le]
    congr 2
    ring
  -- the second-order part, along the line `y ↦ (Λ, y)`
  have hsnd : ∀ y : ℝ, Ito.partialSnd (angleObs κ c n) (p.1, y) =
      n * ((Real.sqrt κ * y + p.1.1) / ℓ) ^ (n - 1) * (Real.sqrt κ / ℓ) := by
    intro y
    refine Ito.partialSnd_eq_of_hasDerivAt (hF.differentiable (by norm_num)).differentiableAt ?_
    have h1 : HasDerivAt (fun y : ℝ => (Real.sqrt κ * y + p.1.1) / ℓ) (Real.sqrt κ / ℓ) y := by
      simpa using (((hasDerivAt_id y).const_mul (Real.sqrt κ)).add_const p.1.1).div_const ℓ
    have := h1.pow n
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
    simp only [angleObs]
    rw [cutψ_of_le hc hp.le]
    rfl
  have hsndsnd : Ito.partialSndSnd (angleObs κ c n) p =
      n * ((n - 1 : ℕ) * (r / ℓ) ^ (n - 1 - 1) * (Real.sqrt κ / ℓ)) * (Real.sqrt κ / ℓ) := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt (hF.contDiffAt.of_le (by norm_num))
      (Eventually.of_forall fun y => hsnd y) ?_
    have h1 : HasDerivAt (fun y : ℝ => (Real.sqrt κ * y + p.1.1) / ℓ) (Real.sqrt κ / ℓ) p.2 := by
      simpa using (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const p.1.1).div_const ℓ
    exact ((h1.pow (n - 1)).const_mul (n : ℝ)).mul_const (Real.sqrt κ / ℓ)
  rw [Ito.itoGen, hfst, hsndsnd]

/-- The algebra behind "`u = log ℓ` turns `X/ℓ` into the Jacobi diffusion": with `ℓ = X + Y`, `A = X/ℓ`,
the Itô generator of `A^n` equals `(2/X + 2/Y)/ℓ · L(x^n)(A)`. -/
theorem angle_gen_identity {κ : ℝ} (hκ : 0 ≤ κ) (a ρR : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (n : ℕ) :
    n * (X / (X + Y)) ^ (n - 1) *
        (((a / X - ρR / Y) * (X + Y) - X * (2 / X + 2 / Y)) / (X + Y) ^ 2) +
      1 / 2 * (n * ((n - 1 : ℕ) * (X / (X + Y)) ^ (n - 1 - 1) * (Real.sqrt κ / (X + Y))) *
        (Real.sqrt κ / (X + Y))) =
    (2 / X + 2 / Y) / (X + Y) * Jacobi.gen κ a (ρR + 2) (fun y => y ^ n) (X / (X + Y)) := by
  rw [Jacobi.gen_pow]
  simp only [Jacobi.dcoef, Jacobi.ccoef]
  obtain ⟨k, hk⟩ : ∃ k, Real.sqrt κ = k := ⟨_, rfl⟩
  have hκk : κ = k ^ 2 := by rw [← hk, Real.sq_sqrt hκ]
  rw [hk]
  subst hκk
  have hXY : X + Y ≠ 0 := (add_pos hX hY).ne'
  have hX0 : X ≠ 0 := hX.ne'
  have hY0 : Y ≠ 0 := hY.ne'
  rcases n with _ | _ | m
  · simp
  · simp only [Nat.sub_self, pow_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.cast_one,
      pow_one, one_mul, mul_one, sub_self, add_zero]
    rw [div_add_div _ _ hX0 hY0, div_div, div_mul_eq_mul_div, eq_div_iff (by positivity)]
    field_simp
    ring
  · simp only [show m + 1 + 1 - 1 = m + 1 by omega]
    push_cast
    rw [pow_succ, pow_succ (X / (X + Y)) (m + 1), pow_succ (X / (X + Y)) m]
    field_simp
    ring

/-- **The generator along a two-seed path**: wherever both gaps are positive and `ℓ > c/2`,
`∂_Λ A^n · λ + ½ ∂²_b A^n = ℓ'/ℓ · L(x^n)(X/ℓ)`. -/
theorem itoGen_angleObs_path (hκ : 0 ≤ κ) {c : ℝ} (hc : 0 < c) (n : ℕ) {s : ℝ}
    (hX : 0 < gapLR w vL s) (hY : 0 < gapRR w vR s) (hcs : c / 2 < sepN vL vR s.toNNReal) :
    Ito.itoGen (angleObs κ c n) (acCoord κ w vL vR b s.toNNReal, b s.toNNReal)
        (acDens ρL ρR w vL vR s) =
      sepRate w vL vR s / sepN vL vR s.toNNReal *
        Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n) (gapLR w vL s / sepN vL vR s.toNNReal) := by
  rw [itoGen_angleObs κ hc n hcs]
  have hr : Real.sqrt κ * b s.toNNReal + (acCoord κ w vL vR b s.toNNReal).1 = gapLR w vL s := by
    simp only [acCoord, gapLR]; ring
  have hℓ : (acCoord κ w vL vR b s.toNNReal).2 = gapLR w vL s + gapRR w vR s := by
    simp only [acCoord, sepN, gapLR, gapRR]; ring
  have hℓ' : sepN vL vR s.toNNReal = gapLR w vL s + gapRR w vR s := hℓ
  simp only [hr, hℓ]
  rw [hℓ']
  exact angle_gen_identity hκ (ρL 0 + 2) (ρR 0) hX hY n

theorem continuous_gen_pow (κ a c : ℝ) (n : ℕ) :
    Continuous fun x => Jacobi.gen κ a c (fun y => y ^ n) x := by
  simp_rw [Jacobi.gen_pow]
  fun_prop

/-! ### From physical time to the logarithmic clock -/

section Clock

variable (h : IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
include h

/-- **Change of variables along the separation**, Bochner form:
`∫_{(0, t₀]} ℓ'(s) G(ℓ_s) ds = ∫_{(0, ℓ_{t₀}]} G`. -/
theorem integral_comp_sepC {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (G : ℝ → ℝ)
    (hG : AEStronglyMeasurable G (volume.restrict (Ioc 0 (sepN vL vR t₀)))) :
    ∫ s in Ioc 0 (t₀ : ℝ), sepRate w vL vR s * G (sepC vL vR t₀ s) =
      ∫ y in Ioc 0 (sepN vL vR t₀), G y := by
  have hc := continuous_sepC h ht₀
  have hf : AEMeasurable (fun s => ENNReal.ofReal (sepRate w vL vR s))
      (volume.restrict (Ioc (0 : ℝ) t₀)) :=
    (intervalIntegrable_sepRate h ht₀).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  rw [← map_sepC_withDensity h ht₀] at hG ⊢
  rw [integral_map hc.aemeasurable hG, integral_withDensity_eq_integral_toReal_smul₀ hf
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  rw [smul_eq_mul, ENNReal.toReal_ofReal (sepRate_nonneg h ht₀ hs.2)]

/-- **The clock change for the generator.** Between the hitting times of `e^{u₁}` and `e^{u₂}`, the time
integral of the Itô generator of `A^n` (cut off at `c = e^{u₁}`) is `∫_{u₁}^{u₂} L(x^n)(U_x) dx`. -/
theorem integral_itoGen_angleObs (hκ : 0 ≤ κ) {u₁ u₂ : ℝ} (hu : u₁ ≤ u₂) {t₀ : ℝ≥0}
    (ht₀ : (t₀ : ℝ≥0∞) < ζ) (hu₂ : exp u₂ ≤ sepN vL vR t₀) (hUc : Continuous (logAngle w vL vR ζ))
    (n : ℕ) :
    ∫ s in (hitTime vL vR ζ u₁ : ℝ)..(hitTime vL vR ζ u₂ : ℝ),
        Ito.itoGen (angleObs κ (exp u₁) n) (acCoord κ w vL vR b s.toNNReal, b s.toNNReal)
          (acDens ρL ρR w vL vR s) =
      ∫ x in u₁..u₂, Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n) (logAngle w vL vR ζ x) := by
  set U := logAngle w vL vR ζ with hU
  set t₁ := hitTime vL vR ζ u₁ with ht₁
  set t₂ := hitTime vL vR ζ u₂ with ht₂
  have hu₁ : exp u₁ ≤ sepN vL vR t₀ := (exp_le_exp.2 hu).trans hu₂
  obtain ⟨h1t, h1e⟩ := hitTime_spec h ht₀ hu₁
  obtain ⟨h2t, h2e⟩ := hitTime_spec h ht₀ hu₂
  have ht₂ζ : (t₂ : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast h2t) ht₀
  have h12 : t₁ ≤ t₂ := (sepN_le_sepN_iff h ht₀ h1t h2t).1 (by rw [h1e, h2e]; exact exp_le_exp.2 hu)
  set g : ℝ → ℝ := fun y => Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n) (U (log y)) / y
    with hg
  set G : ℝ → ℝ := (Ioi (exp u₁)).indicator g with hG
  have hgm : Measurable g :=
    ((continuous_gen_pow κ _ _ n).comp hUc).measurable.comp measurable_log |>.div measurable_id
  -- Step A: the generator integral as a separation integral
  have hA : ∫ s in (t₁ : ℝ)..(t₂ : ℝ), Ito.itoGen (angleObs κ (exp u₁) n)
        (acCoord κ w vL vR b s.toNNReal, b s.toNNReal) (acDens ρL ρR w vL vR s) =
      ∫ s in Ioc 0 (t₂ : ℝ), sepRate w vL vR s * G (sepC vL vR t₂ s) := by
    rw [intervalIntegral.integral_of_le (by exact_mod_cast h12)]
    have hsub : Ioc (t₁ : ℝ) t₂ = Ioc 0 (t₂ : ℝ) ∩ Ioc (t₁ : ℝ) t₂ := by
      rw [Ioc_inter_Ioc, max_eq_right t₁.coe_nonneg, min_self]
    rw [hsub, ← setIntegral_indicator measurableSet_Ioc]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [ae_gaps_pos h ht₂ζ] with s hpos hs
    have hst : s ≤ t₂ := hs.2
    have hsC : sepC vL vR t₂ s = sepN vL vR s.toNNReal := sepC_of_le hst
    by_cases hs1 : s ≤ t₁
    · have hle : sepN vL vR s.toNNReal ≤ exp u₁ := by
        rw [← h1e]
        exact le_sepN_of_le h ht₂ζ (Real.toNNReal_le_iff_le_coe.2 hs1) h12
      rw [indicator_of_notMem (fun hm => (not_le.2 hm.1) hs1), hG, hsC,
        indicator_of_notMem (show sepN vL vR s.toNNReal ∉ Ioi (exp u₁) from
          fun hm => not_lt.2 hle hm), mul_zero]
    · have hs1' : (t₁ : ℝ) < s := not_le.1 hs1
      have hlt : exp u₁ < sepN vL vR s.toNNReal := by
        rw [← h1e]
        exact sepN_lt_sepN h ht₂ζ (Real.lt_toNNReal_iff_coe_lt.2 hs1')
          (Real.toNNReal_le_iff_le_coe.2 hst)
      obtain ⟨hX, hY⟩ := hpos hs
      have hℓpos : 0 < sepN vL vR s.toNNReal := (exp_pos _).trans hlt
      rw [indicator_of_mem (show s ∈ Ioc (t₁ : ℝ) t₂ from ⟨hs1', hst⟩), hG, hsC,
        indicator_of_mem (show sepN vL vR s.toNNReal ∈ Ioi (exp u₁) from hlt),
        itoGen_angleObs_path hκ (exp_pos u₁) n hX hY (by linarith [exp_pos u₁])]
      have hUs : U (log (sepN vL vR s.toNNReal)) = gapLR w vL s / sepN vL vR s.toNNReal := by
        have := logAngle_log_sepC h ht₂ζ hs
        rwa [hsC] at this
      simp only [hg, hUs]
      ring
  -- Step B: the separation integral as an integral over levels
  have hB : ∫ s in Ioc 0 (t₂ : ℝ), sepRate w vL vR s * G (sepC vL vR t₂ s) =
      ∫ y in Ioc (exp u₁) (exp u₂), g y := by
    rw [integral_comp_sepC h ht₂ζ G ((hgm.indicator measurableSet_Ioi).aestronglyMeasurable), h2e,
      hG, setIntegral_indicator measurableSet_Ioi]
    have hset : Ioc 0 (exp u₂) ∩ Ioi (exp u₁) = Ioc (exp u₁) (exp u₂) := by
      ext y
      simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
      constructor
      · rintro ⟨⟨-, h2⟩, h1⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨(exp_pos _).trans h1, h2⟩, h1⟩
    rw [hset]
  -- Step C: substitution `y = e^x`
  have hC : ∫ y in Ioc (exp u₁) (exp u₂), g y =
      ∫ x in u₁..u₂, Jacobi.gen κ (ρL 0 + 2) (ρR 0 + 2) (fun y => y ^ n) (U x) := by
    rw [← intervalIntegral.integral_of_le (exp_le_exp.2 hu)]
    have hgc : ContinuousOn g (Ioi 0) :=
      (((continuous_gen_pow κ _ _ n).comp hUc).comp_continuousOn
        (Real.continuousOn_log.mono fun y hy => ne_of_gt hy)).div continuousOn_id
        fun y hy => ne_of_gt hy
    have hsub := intervalIntegral.integral_comp_mul_deriv' (a := u₁) (b := u₂) (f := exp)
      (f' := exp) (g := g) (fun x _ => hasDerivAt_exp x) continuous_exp.continuousOn
      (hgc.mono fun y hy => by obtain ⟨x, _, rfl⟩ := hy; exact exp_pos x)
    rw [← hsub]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [Function.comp_apply, hg, log_exp]
    field_simp
  rw [hA, hB, hC]

end Clock

end TwoSeed

end Sec2

end InteractingSLE
