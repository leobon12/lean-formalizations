/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Spec.ZhanGT4.TwoTime2Param

/-!
# The Loewner flow near an alive point: holomorphy and the time derivatives of `g', g'', g'''`

Packet PROVE-ZHAN-GT4-A4. Source: Astra, *Follow-up proofs and dependency audit*, Part A.1.1
(`source/external/AstraIG1/ig1_followup_proofs.txt` L245–L275, ruling R38) and the additional note §2.1
(`ig1_additional_proofs.txt` L725–L742, R39): "The first five identities follow by differentiating the composition
`g = ψ_j ∘ g_j` and the Loewner equation … Direct differentiation of the other Loewner equation gives
`∂_{t_i} Sψ_j(W_j) = −12 A₁² A₂²/(a₁ − a₂)⁴`."

These are statements about **one** Loewner chain at a point `p ∈ ℂ` (real or not) that is alive on `[0, T]`, i.e. has
a solution `u` of QuantumZipper's centred flow (`IsForwardSol W p T u`). We prove:

* `exists_isForwardSol_near`: every point `z` with `‖z − p‖ e^{2T/δ²} < δ` (where `2δ ≤ ‖u‖` on `[0, T]`) is alive on
  `[0, T]` — for `z ∈ ℍ` this is `not_mem_fwdHull_of_isForwardSol`, for `Im z < 0` conjugation, and for real `z` a
  uniform limit of the solutions from `z + iε`;
* on the **alive disc** `B(p, δ e^{−2T/δ²})`: `f_t = fwdMap W t` is holomorphic with `f_t' = exp L_t`,
  `L_t = logDerivFwd W t = −∫₀ᵗ 2/f_s²` (`hasDerivAt_fwdMap_aliveDisc`); `(t, z) ↦ f_t(z)` is jointly continuous;
* the higher logarithmic derivatives `L_t' = logDeriv1 W t`, `L_t'' = logDeriv2 W t` as explicit time integrals,
  hence `f_t'' = e^{L} L'`, `f_t''' = e^{L}(L'' + L'²)`, and the Schwarzian `S f_t = L'' − L'²/2`;
* the time derivatives (within `[0, T]`): `∂_t L = −2/f²`, `∂_t L' = 4 f'/f³`, `∂_t L'' = 4 f''/f³ − 12 f'²/f⁴`, and
  **`∂_t S f_t = −12 f_t'²/f_t⁴`** (`hasDerivWithinAt_schwarzFwd`).

The centred map `f_t = g_t − W_t` has the same `z`-derivatives as the uncentred `g_t`, and `f_t(z) = g_t(z) − W_t` is
the denominator of the Loewner equation `∂_t g_t = 2/(g_t − W_t)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped ComplexConjugate Interval

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull logDerivFwd)

variable {W : ℝ → ℝ}

/-! ### Alive points near an alive point -/

/-- Points of `ℍ` near an alive point are alive. -/
theorem exists_isForwardSol_near_of_im_pos (hW : Continuous W) {p z : ℂ} {T δ : ℝ} {u : ℝ → ℂ}
    (hT : 0 ≤ T) (hu : IsForwardSol W p T u) (hδ : 0 < δ) (hlow : ∀ r ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u r‖)
    (hz : 0 < z.im) (hzp : ‖z - p‖ * Real.exp (2 / δ ^ 2 * T) < δ) : ∃ v, IsForwardSol W z T v :=
  QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT hz
    (InteractingSLE.not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hz hzp)

/-- Points of the open lower half-plane near an alive point are alive (conjugation). -/
theorem exists_isForwardSol_near_of_im_ne (hW : Continuous W) {p z : ℂ} {T δ : ℝ} {u : ℝ → ℂ}
    (hT : 0 ≤ T) (hu : IsForwardSol W p T u) (hδ : 0 < δ) (hlow : ∀ r ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u r‖)
    (hz : z.im ≠ 0) (hzp : ‖z - p‖ * Real.exp (2 / δ ^ 2 * T) < δ) : ∃ v, IsForwardSol W z T v := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hu' := InteractingSLE.isForwardSol_conj hu
    have hlow' : ∀ r ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖conj (u r)‖ := fun r hr => by
      rw [Complex.norm_conj]; exact hlow r hr
    have hzp' : ‖conj z - conj p‖ * Real.exp (2 / δ ^ 2 * T) < δ := by
      rw [← map_sub, Complex.norm_conj]; exact hzp
    have him : 0 < (conj z).im := by rw [Complex.conj_im]; linarith
    obtain ⟨v, hv⟩ := exists_isForwardSol_near_of_im_pos hW hT hu' hδ hlow' him hzp'
    have hv' := InteractingSLE.isForwardSol_conj hv
    rw [Complex.conj_conj] at hv'
    exact ⟨_, hv'⟩
  · exact exists_isForwardSol_near_of_im_pos hW hT hu hδ hlow hpos hzp

/-- **Every point near an alive point is alive**: if `2δ ≤ ‖u‖` on `[0, T]` and `‖z − p‖ e^{2T/δ²} < δ`, the flow from
`z` exists on `[0, T]`. For real `z` the solution is the uniform limit of the solutions from `z + iε`. -/
theorem exists_isForwardSol_near (hW : Continuous W) {p z : ℂ} {T δ : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W p T u) (hδ : 0 < δ) (hlow : ∀ r ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u r‖)
    (hzp : ‖z - p‖ * Real.exp (2 / δ ^ 2 * T) < δ) : ∃ v, IsForwardSol W z T v := by
  by_cases hT : 0 ≤ T
  swap
  · refine ⟨u, ?_, fun t ht => absurd (ht.1.trans ht.2) hT⟩
    rw [Icc_eq_empty (by linarith)]
    exact continuousOn_empty _
  by_cases hz : z.im ≠ 0
  · exact exists_isForwardSol_near_of_im_ne hW hT hu hδ hlow hz hzp
  push Not at hz
  set E := Real.exp (2 / δ ^ 2 * T) with hE
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hE0 : 0 < E := by linarith
  -- a margin `ε₀` and the approximating points `z_n = z + i ε₀/(n+1)`
  set ε₀ := (δ - ‖z - p‖ * E) / (2 * E) with hε₀
  have hε₀pos : 0 < ε₀ := div_pos (by linarith) (by positivity)
  set c : ℕ → ℝ := fun n => ε₀ / (n + 1) with hc
  have hcpos : ∀ n, 0 < c n := fun n => div_pos hε₀pos (by positivity)
  have hcle : ∀ n, c n ≤ ε₀ := fun n => div_le_self hε₀pos.le (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  have hcanti : ∀ n m, n ≤ m → c m ≤ c n := fun n m hnm => by
    simp only [hc]
    exact div_le_div_of_nonneg_left hε₀pos.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  set zn : ℕ → ℂ := fun n => z + (c n : ℂ) * I with hzn
  have hzn_im : ∀ n, 0 < (zn n).im := fun n => by
    simp only [hzn, add_im, hz, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, zero_add, mul_one]
    linarith [hcpos n]
  have hzn_z : ∀ n, ‖zn n - z‖ = c n := fun n => by
    simp only [hzn, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hcpos n)]
  have hznp : ∀ n, ‖zn n - p‖ * E < δ := fun n => by
    have h1 : ‖zn n - p‖ ≤ ‖z - p‖ + c n := by
      calc ‖zn n - p‖ = ‖(zn n - z) + (z - p)‖ := by ring_nf
        _ ≤ ‖zn n - z‖ + ‖z - p‖ := norm_add_le _ _
        _ = ‖z - p‖ + c n := by rw [hzn_z]; ring
    have h2 : ε₀ * E = (δ - ‖z - p‖ * E) / 2 := by
      rw [hε₀]; field_simp
    nlinarith [hcle n]
  choose v hv using fun n => exists_isForwardSol_near_of_im_pos hW hT hu hδ hlow (hzn_im n) (hznp n)
  -- lower bounds and the Cauchy estimate
  have hvu : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, ‖v n t - u t‖ < δ := fun n t ht => by
    have h := InteractingSLE.norm_sub_le_of_isForwardSol hW hu (hv n) hδ hT le_rfl hlow (hznp n) t ht
    refine lt_of_le_of_lt (h.trans ?_) (hznp n)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity)))
      (norm_nonneg _)
  have hvlow : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, δ ≤ ‖v n t‖ := fun n t ht => by
    have h1 := hlow t ht
    have h2 := norm_sub_norm_le (u t) (v n t)
    rw [norm_sub_rev] at h2
    linarith [hvu n t ht]
  have hcauchy : ∀ n m, n ≤ m → ∀ t ∈ Icc (0 : ℝ) T, ‖v m t - v n t‖ ≤ c n * E := by
    intro n m hnm t ht
    have h := InteractingSLE.norm_sub_le_of_isForwardSol_of_le_norm hW (hv n) (hv m) hδ hT le_rfl
      (fun r hr => hvlow n r (Ico_subset_Icc_self hr)) (fun r hr => hvlow m r (Ico_subset_Icc_self hr)) t ht
    refine h.trans (mul_le_mul ?_ (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity)))
      (Real.exp_pos _).le (hcpos n).le)
    calc ‖zn m - zn n‖ = |c m - c n| := by
          simp only [hzn, add_sub_add_left_eq_sub, ← sub_mul, ← ofReal_sub, norm_mul, Complex.norm_I,
            mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ c n := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hcanti n m hnm])]
          linarith [hcpos m]
  -- the pointwise limit
  have hcs : ∀ t ∈ Icc (0 : ℝ) T, CauchySeq fun n => v n t := by
    intro t ht
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (ε₀ * E / ε)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    refine (hcauchy N n hn t ht).trans_lt ?_
    have hN' : ε₀ * E < ε * (N + 1) := by
      rw [div_lt_iff₀ hε] at hN; nlinarith
    simp only [hc]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith
  set w : ℝ → ℂ := fun t => limUnder atTop fun n => v n t with hw
  have hlim : ∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun n => v n t) atTop (𝓝 (w t)) := fun t ht =>
    (hcs t ht).tendsto_limUnder
  have hbound : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, ‖w t - v n t‖ ≤ c n * E := fun n t ht => by
    refine le_of_tendsto ((continuous_norm.tendsto _).comp ((hlim t ht).sub_const (v n t))) ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hcauchy n m hm t ht
  have hc0 : Tendsto (fun n => c n * E) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε₀).mul_const E
    rw [mul_zero, zero_mul] at this
    refine this.congr fun n => ?_
    simp only [hc]
    ring
  have hwlow : ∀ t ∈ Icc (0 : ℝ) T, δ ≤ ‖w t‖ := fun t ht =>
    ge_of_tendsto ((continuous_norm.tendsto _).comp (hlim t ht)) (Eventually.of_forall fun n => hvlow n t ht)
  have hwne : ∀ t ∈ Icc (0 : ℝ) T, w t ≠ 0 := fun t ht h => by
    have := hwlow t ht; rw [h, norm_zero] at this; linarith
  have hwc : ContinuousOn w (Icc 0 T) := by
    refine TendstoUniformlyOn.continuousOn (F := v) (p := atTop) ?_ (Frequently.of_forall fun n => (hv n).1)
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [(hc0.eventually (gt_mem_nhds hε))] with n hn t ht
    rw [dist_eq_norm]
    exact (hbound n t ht).trans_lt hn
  refine ⟨w, hwc, fun t ht => ⟨hwne t ht, ?_⟩⟩
  -- the integral equation, from the bound `‖w t − (z − W t + ∫ 2/w)‖ ≤ c_n E (2 + 2T/δ²)`
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hint : ∀ f : ℝ → ℂ, ContinuousOn f (Icc 0 T) → (∀ s ∈ Icc (0 : ℝ) T, f s ≠ 0) →
      IntervalIntegrable (fun s => 2 / f s) volume 0 t := fun f hf hf0 => by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le ht.1]
    exact (continuousOn_const.div hf hf0).mono hsub
  have hkey : ∀ n, ‖w t - (z - W t + ∫ s in (0 : ℝ)..t, 2 / w s)‖ ≤ c n * E * (2 + 2 * T / δ ^ 2) := by
    intro n
    have heq := ((hv n).2 t ht).2
    have hI : ‖(∫ s in (0 : ℝ)..t, 2 / v n s) - ∫ s in (0 : ℝ)..t, 2 / w s‖ ≤ 2 * (c n * E) / δ ^ 2 * T := by
      rw [← intervalIntegral.integral_sub (hint _ (hv n).1 fun s hs => ((hv n).2 s hs).1) (hint _ hwc hwne)]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
        (C := 2 * (c n * E) / δ ^ 2) (f := fun s => 2 / v n s - 2 / w s) (fun s hs => by
          rw [uIoc_of_le ht.1] at hs
          have hs' : s ∈ Icc (0 : ℝ) T := hsub (Ioc_subset_Icc_self hs)
          have h1 := hvlow n s hs'
          have h2 := hwlow s hs'
          have hv0 : v n s ≠ 0 := ((hv n).2 s hs').1
          have hw0 := hwne s hs'
          rw [div_sub_div _ _ hv0 hw0, show (2 : ℂ) * w s - v n s * 2 = 2 * (w s - v n s) by ring,
            norm_div, norm_mul, norm_mul, Complex.norm_two]
          rw [div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by positivity)]
          have h3 := hbound n s hs'
          have h4 : δ ^ 2 ≤ ‖v n s‖ * ‖w s‖ := by nlinarith
          nlinarith [norm_nonneg (w s - v n s)])
      rw [sub_zero, abs_of_nonneg ht.1] at this
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
    have hzz : ‖zn n - z‖ ≤ c n * E := by rw [hzn_z]; nlinarith [hcpos n]
    have e : w t - (z - W t + ∫ s in (0 : ℝ)..t, 2 / w s) =
        (w t - v n t) + (zn n - z) + ((∫ s in (0 : ℝ)..t, 2 / v n s) - ∫ s in (0 : ℝ)..t, 2 / w s) := by
      rw [heq]; ring
    rw [e]
    calc ‖(w t - v n t) + (zn n - z) + ((∫ s in (0 : ℝ)..t, 2 / v n s) - ∫ s in (0 : ℝ)..t, 2 / w s)‖
        ≤ ‖w t - v n t‖ + ‖zn n - z‖ + ‖(∫ s in (0 : ℝ)..t, 2 / v n s) - ∫ s in (0 : ℝ)..t, 2 / w s‖ :=
          norm_add₃_le
      _ ≤ c n * E + c n * E + 2 * (c n * E) / δ ^ 2 * T := add_le_add (add_le_add (hbound n t ht) hzz) hI
      _ = c n * E * (2 + 2 * T / δ ^ 2) := by field_simp; ring
  have hlim0 : Tendsto (fun n => c n * E * (2 + 2 * T / δ ^ 2)) atTop (𝓝 0) := by
    simpa using hc0.mul_const (2 + 2 * T / δ ^ 2)
  have h0 := ge_of_tendsto' hlim0 hkey
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

/-- `(c / g^{n+1})' = −c (n+1) g' / g^{n+2}`. -/
theorem hasDerivAt_const_div_pow {g : ℂ → ℂ} {g' z : ℂ} (c : ℂ) (n : ℕ) (hg : HasDerivAt g g' z)
    (h0 : g z ≠ 0) :
    HasDerivAt (fun w => c / g w ^ (n + 1)) (-(c * ((n : ℂ) + 1) * g') / g z ^ (n + 2)) z := by
  have h := ((hg.pow (n + 1)).inv (pow_ne_zero _ h0)).const_mul c
  have hf : (fun w => c / g w ^ (n + 1)) = fun y => c * (g ^ (n + 1))⁻¹ y := by
    funext w; simp [div_eq_mul_inv]
  rw [hf]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

/-- The fundamental theorem of calculus within `[0, T]` for an integrand continuous on `[0, T]`. -/
theorem hasDerivWithinAt_integral_Icc {f : ℝ → ℂ} {T t : ℝ} (hf : ContinuousOn f (Icc 0 T))
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ∫ r in (0 : ℝ)..s, f r) (f t) (Icc 0 T) t := by
  have : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  have hint : IntervalIntegrable f volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hf.mono (Icc_subset_Icc_right ht.2)
  exact intervalIntegral.integral_hasDerivWithinAt_right hint
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hf t ht)

/-- The first logarithmic derivative `L_t' = (log f_t')'` as a time integral: `∫₀ᵗ 4 f_s'/f_s³`. -/
def logDeriv1 (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..t, 4 * Complex.exp (logDerivFwd W s z) / fwdMap W s z ^ 3

/-- The second logarithmic derivative `L_t''`: `∫₀ᵗ (4 f_s''/f_s³ − 12 f_s'²/f_s⁴)`, with `f'' = e^{L} L'`. -/
def logDeriv2 (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..t, (4 * Complex.exp (logDerivFwd W s z) * logDeriv1 W s z / fwdMap W s z ^ 3 -
    12 * Complex.exp (logDerivFwd W s z) ^ 2 / fwdMap W s z ^ 4)

/-- The Schwarzian derivative of the Loewner map, `S f_t = f‴/f′ − (3/2)(f″/f′)² = L″ − L′²/2`. -/
def schwarzFwd (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ := logDeriv2 W t z - logDeriv1 W t z ^ 2 / 2

/-! ### The alive disc -/

/-- The radius `δ e^{−2T/δ²}` of the alive disc around a point whose flow stays at norm `≥ 2δ` on `[0, T]`. -/
def aliveRad (T δ : ℝ) : ℝ := δ / Real.exp (2 / δ ^ 2 * T)

theorem aliveRad_pos {T δ : ℝ} (hδ : 0 < δ) : 0 < aliveRad T δ := div_pos hδ (Real.exp_pos _)

theorem lt_of_mem_aliveDisc {p z : ℂ} {T δ : ℝ} (hz : z ∈ ball p (aliveRad T δ)) :
    ‖z - p‖ * Real.exp (2 / δ ^ 2 * T) < δ := by
  rw [mem_ball, dist_eq_norm, aliveRad, lt_div_iff₀ (Real.exp_pos _)] at hz
  exact hz

section AliveDisc

variable (hW : Continuous W) {p : ℂ} {T δ : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W p T u) (hδ : 0 < δ)
  (hlow : ∀ r ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u r‖)
include hW hu hδ hlow

/-- On the alive disc: a solution, equal to `f_t`, within `δ` of `u`. -/
theorem exists_sol_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) :
    ∃ v, IsForwardSol W z T v ∧ ∀ t ∈ Icc (0 : ℝ) T, fwdMap W t z = v t ∧ δ ≤ ‖v t‖ := by
  have hzp := lt_of_mem_aliveDisc hz
  obtain ⟨v, hv⟩ := exists_isForwardSol_near hW hu hδ hlow hzp
  refine ⟨v, hv, fun t ht => ⟨InteractingSLE.fwdMap_eq_of_isForwardSol hW hv ht, ?_⟩⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h := InteractingSLE.norm_sub_le_of_isForwardSol hW hu hv hδ hT le_rfl hlow hzp t ht
  have h1 : ‖v t - u t‖ < δ := lt_of_le_of_lt (h.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))) (norm_nonneg _))) hzp
  have h2 := norm_sub_norm_le (u t) (v t)
  rw [norm_sub_rev] at h2
  linarith [hlow t ht]

theorem le_norm_fwdMap_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    δ ≤ ‖fwdMap W t z‖ := by
  obtain ⟨v, -, hv⟩ := exists_sol_aliveDisc hW hu hδ hlow hz
  rw [(hv t ht).1]; exact (hv t ht).2

theorem fwdMap_ne_zero_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap W t z ≠ 0 := fun h => by
  have := le_norm_fwdMap_aliveDisc hW hu hδ hlow hz ht
  rw [h, norm_zero] at this; linarith

/-- Lipschitz dependence on the starting point. -/
theorem norm_fwdMap_sub_le_aliveDisc {z w : ℂ} (hz : z ∈ ball p (aliveRad T δ)) (hw : w ∈ ball p (aliveRad T δ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ‖fwdMap W t w - fwdMap W t z‖ ≤ ‖w - z‖ * Real.exp (2 / δ ^ 2 * T) := by
  obtain ⟨v, hv, hve⟩ := exists_sol_aliveDisc hW hu hδ hlow hz
  obtain ⟨v', hv', hve'⟩ := exists_sol_aliveDisc hW hu hδ hlow hw
  have hT : 0 ≤ T := ht.1.trans ht.2
  rw [(hve t ht).1, (hve' t ht).1]
  refine (InteractingSLE.norm_sub_le_of_isForwardSol_of_le_norm hW hv hv' hδ hT le_rfl
    (fun r hr => (hve r (Ico_subset_Icc_self hr)).2) (fun r hr => (hve' r (Ico_subset_Icc_self hr)).2) t ht).trans ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity)))
    (norm_nonneg _)

/-- **Joint continuity** of `(t, z) ↦ f_t(z)` on `[0, T] × B(p, aliveRad)`. -/
theorem continuousOn_fwdMap_aliveDisc :
    ContinuousOn (fun q : ℝ × ℂ => fwdMap W q.1 q.2) (Icc 0 T ×ˢ ball p (aliveRad T δ)) := by
  rintro ⟨t₀, z₀⟩ ⟨ht₀, hz₀⟩
  obtain ⟨v, hv, hve⟩ := exists_sol_aliveDisc hW hu hδ hlow hz₀
  have hvc : ContinuousWithinAt v (Icc 0 T) t₀ := hv.1 t₀ ht₀
  set E := Real.exp (2 / δ ^ 2 * T)
  have hE : 0 < E := Real.exp_pos _
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨η, hη, hηv⟩ := Metric.continuousWithinAt_iff.1 hvc (ε / 2) (by positivity)
  refine ⟨min η (ε / (2 * E)), by positivity, ?_⟩
  rintro ⟨t, z⟩ ⟨ht, hz⟩ hdist
  have hdt : dist t t₀ < min η (ε / (2 * E)) :=
    lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hdist
  have hdz : dist z z₀ < min η (ε / (2 * E)) :=
    lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _) hdist
  simp only [lt_min_iff] at hdt hdz
  have h1 := norm_fwdMap_sub_le_aliveDisc hW hu hδ hlow hz₀ hz ht
  have h2 := hηv ht hdt.1
  rw [dist_eq_norm] at h2 hdz ⊢
  rw [← (hve t ht).1, ← (hve t₀ ht₀).1] at h2
  dsimp only at h1 h2 hdz ⊢
  calc ‖fwdMap W t z - fwdMap W t₀ z₀‖
      ≤ ‖fwdMap W t z - fwdMap W t z₀‖ + ‖fwdMap W t z₀ - fwdMap W t₀ z₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / (2 * E) * E + ε / 2 := by
        refine add_lt_add_of_le_of_lt (h1.trans ?_) h2
        exact mul_le_mul_of_nonneg_right hdz.2.le hE.le
    _ = ε := by field_simp; ring

/-- **The linear identity** `f_t(w) − f_t(z) = (w − z) exp(−∫₀ᵗ 2/(f_s(w) f_s(z)))` on the alive disc. -/
theorem fwdMap_sub_eq_aliveDisc {z w : ℂ} (hz : z ∈ ball p (aliveRad T δ)) (hw : w ∈ ball p (aliveRad T δ))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap W t w - fwdMap W t z =
      (w - z) * Complex.exp (-∫ s in (0 : ℝ)..t, 2 / (fwdMap W s w * fwdMap W s z)) := by
  obtain ⟨v, hv, hve⟩ := exists_sol_aliveDisc hW hu hδ hlow hz
  obtain ⟨v', hv', hve'⟩ := exists_sol_aliveDisc hW hu hδ hlow hw
  have h := QuantumZipper.FwdHolo.sol_sub_eq hv hv' t ht
  rw [(hve t ht).1, (hve' t ht).1, h]
  congr 3
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  simp only [(hve s hs').1, (hve' s hs').1]

/-- Joint continuity of `(s, w) ↦ 2/(f_s(w) f_s(z))`. -/
theorem continuousOn_two_div_mul_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) :
    ContinuousOn (fun q : ℝ × ℂ => 2 / (fwdMap W q.1 q.2 * fwdMap W q.1 z))
      (Icc 0 T ×ˢ ball p (aliveRad T δ)) := by
  have hc := continuousOn_fwdMap_aliveDisc hW hu hδ hlow
  have hcz : ContinuousOn (fun q : ℝ × ℂ => fwdMap W q.1 z) (Icc 0 T ×ˢ ball p (aliveRad T δ)) :=
    hc.comp (continuous_fst.prodMk continuous_const).continuousOn (fun _ hq => ⟨hq.1, hz⟩)
  refine continuousOn_const.div (hc.mul hcz) fun _ hq => mul_ne_zero ?_ ?_
  · exact fwdMap_ne_zero_aliveDisc hW hu hδ hlow hq.2 hq.1
  · exact fwdMap_ne_zero_aliveDisc hW hu hδ hlow hz hq.1

/-- **Holomorphy of the Loewner map on the alive disc**: `f_t' = exp L_t`, `L_t = logDerivFwd W t`. -/
theorem hasDerivAt_fwdMap_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (fwdMap W t) (Complex.exp (logDerivFwd W t z)) z := by
  set F : ℝ → ℂ → ℂ := fun s w => 2 / (fwdMap W s w * fwdMap W s z) with hF
  have hI := continuousOn_integral_of_holo (F := F) (continuousOn_two_div_mul_aliveDisc hW hu hδ hlow hz)
  have hcont : ContinuousAt (fun w => ∫ s in (0 : ℝ)..t, F s w) z := by
    have h1 := (hI (t, z) ⟨ht, hz⟩).comp (continuous_const.prodMk continuous_id).continuousWithinAt
      (x := z) (s := ball p (aliveRad T δ)) (fun w hw => ⟨ht, hw⟩)
    exact h1.continuousAt (isOpen_ball.mem_nhds hz)
  have hE : ContinuousAt (fun w => Complex.exp (-∫ s in (0 : ℝ)..t, F s w)) z :=
    Complex.continuous_exp.continuousAt.comp hcont.neg
  have hval : Complex.exp (-∫ s in (0 : ℝ)..t, F s z) = Complex.exp (logDerivFwd W t z) := by
    simp only [hF, logDerivFwd, sq]
  rw [hasDerivAt_iff_tendsto_slope, ← hval]
  refine (hE.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz), self_mem_nhdsWithin] with w hw hne
  have hne' : w - z ≠ 0 := sub_ne_zero.2 hne
  rw [slope_def_field, fwdMap_sub_eq_aliveDisc hW hu hδ hlow hz hw ht, hF]
  field_simp

theorem differentiableOn_fwdMap_aliveDisc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    DifferentiableOn ℂ (fwdMap W t) (ball p (aliveRad T δ)) := fun _ hz =>
  (hasDerivAt_fwdMap_aliveDisc hW hu hδ hlow hz ht).differentiableAt.differentiableWithinAt

theorem deriv_fwdMap_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    deriv (fwdMap W t) z = Complex.exp (logDerivFwd W t z) :=
  (hasDerivAt_fwdMap_aliveDisc hW hu hδ hlow hz ht).deriv

theorem continuousOn_two_div_sq_aliveDisc :
    ContinuousOn (fun q : ℝ × ℂ => 2 / fwdMap W q.1 q.2 ^ 2) (Icc 0 T ×ˢ ball p (aliveRad T δ)) :=
  continuousOn_const.div ((continuousOn_fwdMap_aliveDisc hW hu hδ hlow).pow 2) fun _ hq =>
    pow_ne_zero 2 (fwdMap_ne_zero_aliveDisc hW hu hδ hlow hq.2 hq.1)

/-- Joint continuity of `(t, z) ↦ L_t(z) = log f_t'(z)`. -/
theorem continuousOn_logDerivFwd_aliveDisc :
    ContinuousOn (fun q : ℝ × ℂ => logDerivFwd W q.1 q.2) (Icc 0 T ×ˢ ball p (aliveRad T δ)) :=
  (continuousOn_integral_of_holo (F := fun s w => 2 / fwdMap W s w ^ 2)
    (continuousOn_two_div_sq_aliveDisc hW hu hδ hlow)).neg

/-- **`(log f_t')' = L_t'`**: `logDerivFwd W t` is holomorphic on the alive disc with derivative `logDeriv1 W t`. -/
theorem hasDerivAt_logDerivFwd_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt (logDerivFwd W t) (logDeriv1 W t z) z := by
  set F₀ : ℝ → ℂ → ℂ := fun s w => 2 / fwdMap W s w ^ 2 with hF₀
  have hder : ∀ s ∈ Icc (0 : ℝ) T, ∀ w ∈ ball p (aliveRad T δ),
      HasDerivAt (F₀ s) (-(4 * Complex.exp (logDerivFwd W s w) / fwdMap W s w ^ 3)) w := by
    intro s hs w hw
    have h := hasDerivAt_const_div_pow 2 1 (hasDerivAt_fwdMap_aliveDisc hW hu hδ hlow hw hs)
      (fwdMap_ne_zero_aliveDisc hW hu hδ hlow hw hs)
    norm_num at h
    refine h.congr_deriv ?_
    ring
  have hd : ∀ s ∈ Icc (0 : ℝ) T, DifferentiableOn ℂ (F₀ s) (ball p (aliveRad T δ)) := fun s hs w hw =>
    (hder s hs w hw).differentiableAt.differentiableWithinAt
  have h := (hasDerivAt_integral_of_holo hd (continuousOn_two_div_sq_aliveDisc hW hu hδ hlow) hz ht).neg
  refine h.congr_deriv ?_
  rw [← intervalIntegral.integral_neg, logDeriv1]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  simp only [(hder s ⟨hs.1, hs.2.trans ht.2⟩ z hz).deriv, neg_neg]

theorem continuousOn_four_mul_exp_div_aliveDisc :
    ContinuousOn (fun q : ℝ × ℂ => 4 * Complex.exp (logDerivFwd W q.1 q.2) / fwdMap W q.1 q.2 ^ 3)
      (Icc 0 T ×ˢ ball p (aliveRad T δ)) :=
  (continuousOn_const.mul (continuous_exp.comp_continuousOn
    (continuousOn_logDerivFwd_aliveDisc hW hu hδ hlow))).div
    ((continuousOn_fwdMap_aliveDisc hW hu hδ hlow).pow 3) fun _ hq =>
      pow_ne_zero 3 (fwdMap_ne_zero_aliveDisc hW hu hδ hlow hq.2 hq.1)

/-- Joint continuity of `(t, z) ↦ L_t'(z)`. -/
theorem continuousOn_logDeriv1_aliveDisc :
    ContinuousOn (fun q : ℝ × ℂ => logDeriv1 W q.1 q.2) (Icc 0 T ×ˢ ball p (aliveRad T δ)) :=
  continuousOn_integral_of_holo (F := fun s w => 4 * Complex.exp (logDerivFwd W s w) / fwdMap W s w ^ 3)
    (continuousOn_four_mul_exp_div_aliveDisc hW hu hδ hlow)

/-- **`(L_t')' = L_t''`**: `logDeriv1 W t` is holomorphic on the alive disc with derivative `logDeriv2 W t`. -/
theorem hasDerivAt_logDeriv1_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt (logDeriv1 W t) (logDeriv2 W t z) z := by
  set F₁ : ℝ → ℂ → ℂ := fun s w => 4 * Complex.exp (logDerivFwd W s w) / fwdMap W s w ^ 3 with hF₁
  have hder : ∀ s ∈ Icc (0 : ℝ) T, ∀ w ∈ ball p (aliveRad T δ),
      HasDerivAt (F₁ s) (4 * Complex.exp (logDerivFwd W s w) * logDeriv1 W s w / fwdMap W s w ^ 3 -
        12 * Complex.exp (logDerivFwd W s w) ^ 2 / fwdMap W s w ^ 4) w := by
    intro s hs w hw
    have hf0 := fwdMap_ne_zero_aliveDisc hW hu hδ hlow hw hs
    have h := (((hasDerivAt_logDerivFwd_aliveDisc hW hu hδ hlow hw hs).cexp).const_mul 4).div
      ((hasDerivAt_fwdMap_aliveDisc hW hu hδ hlow hw hs).pow 3) (pow_ne_zero 3 hf0)
    refine h.congr_deriv ?_
    simp only [Pi.pow_apply]
    field_simp
    ring
  have hd : ∀ s ∈ Icc (0 : ℝ) T, DifferentiableOn ℂ (F₁ s) (ball p (aliveRad T δ)) := fun s hs w hw =>
    (hder s hs w hw).differentiableAt.differentiableWithinAt
  have h := hasDerivAt_integral_of_holo hd (continuousOn_four_mul_exp_div_aliveDisc hW hu hδ hlow) hz ht
  refine h.congr_deriv ?_
  rw [logDeriv2]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht.1] at hs
  simp only [(hder s ⟨hs.1, hs.2.trans ht.2⟩ z hz).deriv]

/-- **`f_t'' = e^{L_t} L_t'`.** -/
theorem hasDerivAt_deriv_fwdMap_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (deriv (fwdMap W t)) (Complex.exp (logDerivFwd W t z) * logDeriv1 W t z) z := by
  refine (hasDerivAt_logDerivFwd_aliveDisc hW hu hδ hlow hz ht).cexp.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw using deriv_fwdMap_aliveDisc hW hu hδ hlow hw ht

/-- **`f_t''' = e^{L_t} (L_t'' + L_t'²)`.** -/
theorem hasDerivAt_deriv_deriv_fwdMap_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivAt (deriv (deriv (fwdMap W t)))
      (Complex.exp (logDerivFwd W t z) * (logDeriv2 W t z + logDeriv1 W t z ^ 2)) z := by
  have h := ((hasDerivAt_logDerivFwd_aliveDisc hW hu hδ hlow hz ht).cexp).mul
    (hasDerivAt_logDeriv1_aliveDisc hW hu hδ hlow hz ht)
  refine (h.congr_of_eventuallyEq ?_).congr_deriv (by ring)
  filter_upwards [isOpen_ball.mem_nhds hz] with w hw using
    (hasDerivAt_deriv_fwdMap_aliveDisc hW hu hδ hlow hw ht).deriv

/-- `schwarzFwd` is the Schwarzian `f‴/f′ − (3/2)(f″/f′)²` of the Loewner map on the alive disc. -/
theorem schwarzFwd_eq_aliveDisc {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    schwarzFwd W t z = deriv (deriv (deriv (fwdMap W t))) z / deriv (fwdMap W t) z -
      3 / 2 * (deriv (deriv (fwdMap W t)) z / deriv (fwdMap W t) z) ^ 2 := by
  rw [(hasDerivAt_deriv_deriv_fwdMap_aliveDisc hW hu hδ hlow hz ht).deriv,
    (hasDerivAt_deriv_fwdMap_aliveDisc hW hu hδ hlow hz ht).deriv, deriv_fwdMap_aliveDisc hW hu hδ hlow hz ht,
    schwarzFwd]
  have he := Complex.exp_ne_zero (logDerivFwd W t z)
  field_simp
  ring

/-! #### Time derivatives at a fixed point of the alive disc -/

/-- **`∂_t L_t(z) = −2/f_t(z)²`** (the variational equation `∂_t log g_t' = −2/(g_t − W_t)²`). -/
theorem hasDerivWithinAt_logDerivFwd_time {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => logDerivFwd W s z) (-(2 / fwdMap W t z ^ 2)) (Icc 0 T) t := by
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hc :=
    (continuousOn_two_div_sq_aliveDisc hW hu hδ hlow).comp
      hcl.continuousOn (fun s hs => (⟨hs, hz⟩ : (s, z) ∈ Icc 0 T ×ˢ ball p (aliveRad T δ)))
  simp only [Function.comp_def] at hc
  exact (hasDerivWithinAt_integral_Icc hc ht).neg

/-- **`∂_t L_t'(z) = 4 f_t'(z)/f_t(z)³`.** -/
theorem hasDerivWithinAt_logDeriv1_time {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => logDeriv1 W s z)
      (4 * Complex.exp (logDerivFwd W t z) / fwdMap W t z ^ 3) (Icc 0 T) t := by
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hc :=
    (continuousOn_four_mul_exp_div_aliveDisc hW hu hδ hlow).comp
      hcl.continuousOn (fun s hs => (⟨hs, hz⟩ : (s, z) ∈ Icc 0 T ×ˢ ball p (aliveRad T δ)))
  simp only [Function.comp_def] at hc
  exact hasDerivWithinAt_integral_Icc hc ht

/-- **`∂_t L_t''(z) = 4 f_t''/f_t³ − 12 f_t'²/f_t⁴`.** -/
theorem hasDerivWithinAt_logDeriv2_time {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => logDeriv2 W s z)
      (4 * Complex.exp (logDerivFwd W t z) * logDeriv1 W t z / fwdMap W t z ^ 3 -
        12 * Complex.exp (logDerivFwd W t z) ^ 2 / fwdMap W t z ^ 4) (Icc 0 T) t := by
  have hmaps : MapsTo (fun s : ℝ => (s, z)) (Icc 0 T) (Icc 0 T ×ˢ ball p (aliveRad T δ)) :=
    fun s hs => ⟨hs, hz⟩
  have hcl : Continuous fun s : ℝ => (s, z) := continuous_id.prodMk continuous_const
  have hL := (continuousOn_logDerivFwd_aliveDisc hW hu hδ hlow).comp hcl.continuousOn hmaps
  have hL1 := (continuousOn_logDeriv1_aliveDisc hW hu hδ hlow).comp hcl.continuousOn hmaps
  have hf := (continuousOn_fwdMap_aliveDisc hW hu hδ hlow).comp hcl.continuousOn hmaps
  have hne : ∀ s ∈ Icc (0 : ℝ) T, fwdMap W s z ≠ 0 := fun s hs =>
    fwdMap_ne_zero_aliveDisc hW hu hδ hlow hz hs
  refine hasDerivWithinAt_integral_Icc ?_ ht
  refine ((continuousOn_const.mul (continuous_exp.comp_continuousOn hL)).mul hL1).div (hf.pow 3)
    (fun s hs => pow_ne_zero 3 (hne s hs)) |>.sub ?_
  exact (continuousOn_const.mul ((continuous_exp.comp_continuousOn hL).pow 2)).div (hf.pow 4)
    (fun s hs => pow_ne_zero 4 (hne s hs))

/-- **The Schwarzian of a Loewner map evolves by `∂_t S f_t(z) = −12 f_t'(z)²/f_t(z)⁴`** (the identity behind (D5):
"direct differentiation of the other Loewner equation gives `∂ Sψ(W) = −12 A₁² A₂²/(a₁ − a₂)⁴`"). -/
theorem hasDerivWithinAt_schwarzFwd_time {z : ℂ} (hz : z ∈ ball p (aliveRad T δ)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => schwarzFwd W s z)
      (-(12 * Complex.exp (logDerivFwd W t z) ^ 2 / fwdMap W t z ^ 4)) (Icc 0 T) t := by
  have h2 := hasDerivWithinAt_logDeriv2_time hW hu hδ hlow hz ht
  have h1 := hasDerivWithinAt_logDeriv1_time hW hu hδ hlow hz ht
  refine (h2.sub ((h1.pow 2).div_const 2)).congr_deriv ?_
  have hf0 := fwdMap_ne_zero_aliveDisc hW hu hδ hlow hz ht
  field_simp
  ring

end AliveDisc

end InteractingSLE.ZhanGT4
