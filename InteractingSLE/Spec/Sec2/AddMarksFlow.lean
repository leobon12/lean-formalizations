/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForceLip
import InteractingSLE.Spec.Sec2.GirsanovCut
import InteractingSLE.Stochastic.Bessel.Regularized

/-!
# The added marks: solving their force-point equations pathwise, with adaptedness

Packet PROVE-SEC2-GIR2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md` L486): the
marks added by the Girsanov step move by the Loewner flow of the driver,
`U_t = y + ∫₀ᵗ 2 / (U_s − W_s) ds`, until they come close to `W`. While the gap is at least `δ` this
is the equation `U' = F(U − W)` with the bounded Lipschitz cut drift `F = 2 r_δ` (right marks:
`F x = 2 / max x δ`, left marks: `F x = −2 / max (−x) δ`; Bessel's `regDrift`).

The driver `W` of an evolution is only adapted before its lifetime `ζ` and only almost surely
continuous, while adaptedness (`AdaptedBefore`) must hold exactly (no usual augmentation, ruling R15
Q2). The mark is therefore *defined* by a formula that is measurable for every `ω`: the `limsup` of
the Euler approximations with step `2⁻ⁿ` driven by the killed driver at the dyadic times; on every
path along which `W` is continuous before `ζ`, the Euler scheme converges to the solution of the
integral equation (a discrete Grönwall argument, `tendsto_eulerAt`).

* `eulerSeq`, `eulerAt`: the Euler scheme; `tendsto_eulerAt`: convergence to any continuous solution
  of `u = y + ∫ F(u − w)` (`F` Lipschitz, `w` continuous on `[0, t]`);
* `markFlow F y ζ W`: the mark; `measurable_markFlow` (each `markFlow … t` is `𝓕_t`-measurable) and
  `adaptedBefore_markFlow`;
* `markFlow_eq_of_continuousOn`: on a path along which `W` is continuous before `ζ`, the mark is
  continuous before `ζ` and solves `U t = y + ∫₀ᵗ F(U − W)` for `t < ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-! ### The Euler scheme and its convergence (deterministic) -/

/-- The Euler values `e₀ = y`, `e_{k+1} = e_k + h F(e_k − w_k)`. -/
def eulerSeq (F : ℝ → ℝ) (y h : ℝ) (wk : ℕ → ℝ) : ℕ → ℝ
  | 0 => y
  | k + 1 => eulerSeq F y h wk k + h * F (eulerSeq F y h wk k - wk k)

/-- The Euler approximation with step `2⁻ⁿ` at the real time `t`, interpolated linearly in the last
cell. -/
def eulerAt (F : ℝ → ℝ) (y : ℝ) (n : ℕ) (wk : ℕ → ℝ) (t : ℝ) : ℝ :=
  eulerSeq F y (1 / 2 ^ n) wk (Girsanov.stepIdx n t)
    + (t - (Girsanov.grid n (Girsanov.stepIdx n t) : ℝ))
      * F (eulerSeq F y (1 / 2 ^ n) wk (Girsanov.stepIdx n t) - wk (Girsanov.stepIdx n t))

section Euler

variable {F : ℝ → ℝ} {K : ℝ≥0} {y t h ε : ℝ} {w u : ℝ → ℝ}

/-- **One Euler step.** If `u = y + ∫ F(u − w)` on `[0, t]` and `F(u − w)` oscillates by at most `ε`
over time lags `≤ h`, a step of length `s₁ − s₀ ≤ h` from a value `e` makes the error grow at most
to `(1 + hK)|e − u s₀| + hε`. -/
theorem abs_euler_step_le (hF : LipschitzWith K F)
    (hu : ∀ s ∈ Icc (0 : ℝ) t, u s = y + ∫ r in (0 : ℝ)..s, F (u r - w r))
    (hint : IntervalIntegrable (fun r => F (u r - w r)) volume 0 t)
    (hmod : ∀ r ∈ Icc (0 : ℝ) t, ∀ r' ∈ Icc (0 : ℝ) t, |r - r'| ≤ h →
      |F (u r - w r) - F (u r' - w r')| ≤ ε)
    {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ ≤ s₁) (h1h : s₁ - s₀ ≤ h) (h1t : s₁ ≤ t) (e : ℝ) :
    |e + (s₁ - s₀) * F (e - w s₀) - u s₁| ≤ (1 + h * K) * |e - u s₀| + h * ε := by
  set g : ℝ → ℝ := fun r => F (u r - w r) with hg
  have hs₀ : s₀ ∈ Icc (0 : ℝ) t := ⟨h0, h01.trans h1t⟩
  have hs₁ : s₁ ∈ Icc (0 : ℝ) t := ⟨h0.trans h01, h1t⟩
  have hε : 0 ≤ ε := by
    have := hmod s₀ hs₀ s₀ hs₀ (by rw [sub_self, abs_zero]; linarith)
    simpa using this
  have ht0 : 0 ≤ t := h0.trans (h01.trans h1t)
  have hsub0 : uIcc (0 : ℝ) s₀ ⊆ uIcc 0 t := by
    rw [uIcc_of_le h0, uIcc_of_le ht0]; exact Icc_subset_Icc le_rfl (h01.trans h1t)
  have hsub1 : uIcc (0 : ℝ) s₁ ⊆ uIcc 0 t := by
    rw [uIcc_of_le (h0.trans h01), uIcc_of_le ht0]; exact Icc_subset_Icc le_rfl h1t
  have hint0 : IntervalIntegrable g volume 0 s₀ := hint.mono_set hsub0
  have hint1 : IntervalIntegrable g volume 0 s₁ := hint.mono_set hsub1
  have hint01 : IntervalIntegrable g volume s₀ s₁ := hint0.symm.trans hint1
  have hdiff : u s₁ - u s₀ = ∫ r in s₀..s₁, g r := by
    rw [hu s₁ hs₁, hu s₀ hs₀, ← intervalIntegral.integral_interval_sub_left hint1 hint0]
    ring
  have hloc : ∫ r in s₀..s₁, (g s₀ - g r) = (s₁ - s₀) * g s₀ - ∫ r in s₀..s₁, g r := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint01,
      intervalIntegral.integral_const, smul_eq_mul]
  have hbound1 : |∫ r in s₀..s₁, (g s₀ - g r)| ≤ ε * |s₁ - s₀| := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s₀) (b := s₁)
      (f := fun r => g s₀ - g r) (C := ε) fun r hr => by
        rw [uIoc_of_le h01] at hr
        have hr' : r ∈ Icc (0 : ℝ) t := ⟨h0.trans hr.1.le, hr.2.trans h1t⟩
        rw [Real.norm_eq_abs]
        refine hmod s₀ hs₀ r hr' ?_
        rw [abs_sub_comm, abs_of_nonneg (by linarith [hr.1])]
        linarith [hr.2]
    simpa [Real.norm_eq_abs] using this
  have hLip : |F (e - w s₀) - g s₀| ≤ K * |e - u s₀| := by
    have := hF.dist_le_mul (e - w s₀) (u s₀ - w s₀)
    rw [Real.dist_eq, Real.dist_eq, show e - w s₀ - (u s₀ - w s₀) = e - u s₀ by ring] at this
    exact this
  have hkey : e + (s₁ - s₀) * F (e - w s₀) - u s₁
      = (e - u s₀) + (s₁ - s₀) * (F (e - w s₀) - g s₀) + ∫ r in s₀..s₁, (g s₀ - g r) := by
    rw [hloc]
    linarith [hdiff]
  rw [hkey]
  have hd : 0 ≤ s₁ - s₀ := sub_nonneg.2 h01
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  calc |(e - u s₀) + (s₁ - s₀) * (F (e - w s₀) - g s₀) + ∫ r in s₀..s₁, (g s₀ - g r)|
      ≤ |e - u s₀| + (s₁ - s₀) * (K * |e - u s₀|) + ε * (s₁ - s₀) := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_))
          ?_)
        · rw [abs_mul, abs_of_nonneg hd]
          exact mul_le_mul_of_nonneg_left hLip hd
        · rw [← abs_of_nonneg hd]; exact hbound1
    _ ≤ (1 + h * K) * |e - u s₀| + h * ε := by
        have h1 : (s₁ - s₀) * (K * |e - u s₀|) ≤ h * (K * |e - u s₀|) :=
          mul_le_mul_of_nonneg_right h1h (mul_nonneg hK (abs_nonneg _))
        have h2 : ε * (s₁ - s₀) ≤ h * ε := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right h1h hε
        nlinarith [abs_nonneg (e - u s₀)]

/-- **Discrete Grönwall bound for the Euler values**: `|e_k − u(kh)| ≤ k h ε (1 + hK)^k` while
`kh ≤ t`. -/
theorem abs_eulerSeq_sub_le (hF : LipschitzWith K F)
    (hu : ∀ s ∈ Icc (0 : ℝ) t, u s = y + ∫ r in (0 : ℝ)..s, F (u r - w r))
    (hint : IntervalIntegrable (fun r => F (u r - w r)) volume 0 t)
    (hmod : ∀ r ∈ Icc (0 : ℝ) t, ∀ r' ∈ Icc (0 : ℝ) t, |r - r'| ≤ h →
      |F (u r - w r) - F (u r' - w r')| ≤ ε)
    (hh : 0 < h) (hε : 0 ≤ ε) {wk : ℕ → ℝ} (hwk : ∀ k : ℕ, (k : ℝ) * h ≤ t → wk k = w (k * h)) :
    ∀ k : ℕ, (k : ℝ) * h ≤ t →
      |eulerSeq F y h wk k - u (k * h)| ≤ k * h * ε * (1 + h * K) ^ k := by
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  intro k
  induction k with
  | zero =>
    intro ht
    simp only [Nat.cast_zero, zero_mul] at ht ⊢
    rw [hu 0 ⟨le_rfl, ht⟩]
    simp [eulerSeq]
  | succ k ih =>
    intro hk1
    have hk : (k : ℝ) * h ≤ t := by
      have : (k : ℝ) * h ≤ ((k + 1 : ℕ) : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hh.le
      linarith
    have hstep := abs_euler_step_le (y := y) hF hu hint hmod (s₀ := k * h) (s₁ := (k + 1 : ℕ) * h)
      (mul_nonneg k.cast_nonneg hh.le) (by push_cast; linarith) (by push_cast; linarith) hk1
      (eulerSeq F y h wk k)
    have hdef : eulerSeq F y h wk (k + 1)
        = eulerSeq F y h wk k + ((k + 1 : ℕ) * h - k * h) * F (eulerSeq F y h wk k - w (k * h)) := by
      rw [eulerSeq, hwk k hk]
      push_cast
      ring
    rw [hdef]
    refine hstep.trans ?_
    have hpow : 1 ≤ (1 + h * K) ^ (k + 1) := one_le_pow₀ (by nlinarith)
    have h1 : (1 + h * K) * |eulerSeq F y h wk k - u (k * h)|
        ≤ (1 + h * K) * (k * h * ε * (1 + h * K) ^ k) :=
      mul_le_mul_of_nonneg_left (ih hk) (by nlinarith)
    have h2 : h * ε ≤ h * ε * (1 + h * K) ^ (k + 1) := le_mul_of_one_le_right (by positivity) hpow
    calc (1 + h * K) * |eulerSeq F y h wk k - u (k * h)| + h * ε
        ≤ (1 + h * K) * (k * h * ε * (1 + h * K) ^ k) + h * ε * (1 + h * K) ^ (k + 1) :=
          add_le_add h1 h2
      _ = ((k + 1 : ℕ) : ℝ) * h * ε * (1 + h * K) ^ (k + 1) := by push_cast; ring

/-- **Convergence of the Euler scheme.** Let `F` be Lipschitz, `w` and `u` continuous on `[0, t]`
with `u = y + ∫ F(u − w)` there, and let the Euler scheme of level `n` read `w` at the dyadic times
`k / 2ⁿ ≤ t`. Then the Euler approximations at time `t` converge to `u t`. -/
theorem tendsto_eulerAt (hF : LipschitzWith K F) (ht : 0 ≤ t) (hwc : ContinuousOn w (Icc 0 t))
    (huc : ContinuousOn u (Icc 0 t))
    (hu : ∀ s ∈ Icc (0 : ℝ) t, u s = y + ∫ r in (0 : ℝ)..s, F (u r - w r))
    {wk : ℕ → ℕ → ℝ} (hwk : ∀ n k : ℕ, (k : ℝ) / 2 ^ n ≤ t → wk n k = w (k / 2 ^ n)) :
    Tendsto (fun n => eulerAt F y n (wk n) t) atTop (𝓝 (u t)) := by
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  have hgc : ContinuousOn (fun r => F (u r - w r)) (Icc 0 t) :=
    hF.continuous.comp_continuousOn (huc.sub hwc)
  have hint : IntervalIntegrable (fun r => F (u r - w r)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact hgc
  have huc' := isCompact_Icc.uniformContinuousOn_of_continuous hgc
  rw [Metric.uniformContinuousOn_iff_le] at huc'
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  set C : ℝ := (t + 1) * Real.exp (K * (t + 1)) with hC
  have hCpos : 0 < C := by positivity
  set ε : ℝ := ε' / (2 * C) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨η, hη, hmodη⟩ := huc' ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (lt_min hη one_pos) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun n hn => ?_⟩
  set h : ℝ := 1 / 2 ^ n with hhdef
  have hh : 0 < h := by positivity
  have hhN : h ≤ min η 1 := by
    have : h ≤ (1 / 2 : ℝ) ^ N := by
      rw [hhdef, ← one_div_pow]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    exact this.trans hN.le
  have hmod : ∀ r ∈ Icc (0 : ℝ) t, ∀ r' ∈ Icc (0 : ℝ) t, |r - r'| ≤ h →
      |F (u r - w r) - F (u r' - w r')| ≤ ε := fun r hr r' hr' hrr' => by
    have := hmodη r hr r' hr' (by rw [Real.dist_eq]; exact hrr'.trans (hhN.trans (min_le_left _ _)))
    rwa [Real.dist_eq] at this
  set j := Girsanov.stepIdx n t with hj
  have hs₀ : ((Girsanov.grid n j : ℝ≥0) : ℝ) = j * h := by
    rw [Girsanov.coe_grid, hhdef]; ring
  have hs₀t : (j : ℝ) * h ≤ t := hs₀ ▸ Girsanov.coe_grid_stepIdx_le ht
  have hts₀ : t - j * h ≤ h := by
    have := Girsanov.lt_coe_grid_stepIdx_add (n := n) t
    rw [← hj, hs₀] at this
    linarith
  have hwk' : ∀ k : ℕ, (k : ℝ) * h ≤ t → wk n k = w (k * h) := fun k hk => by
    have e : (k : ℝ) / 2 ^ n = k * h := by rw [hhdef]; ring
    rw [hwk n k (e ▸ hk), e]
  have hd := abs_eulerSeq_sub_le (y := y) hF hu hint hmod hh hε.le hwk' j hs₀t
  have hstep := abs_euler_step_le (y := y) hF hu hint hmod (s₀ := j * h) (s₁ := t)
    (mul_nonneg j.cast_nonneg hh.le) hs₀t hts₀ le_rfl (eulerSeq F y h (wk n) j)
  have heq : eulerAt F y n (wk n) t
      = eulerSeq F y h (wk n) j + (t - j * h) * F (eulerSeq F y h (wk n) j - w (j * h)) := by
    rw [eulerAt, ← hj, hs₀, hwk' j hs₀t]
  rw [Real.dist_eq, heq]
  have hpow : (1 + h * K) ^ (j + 1) ≤ Real.exp (K * (t + 1)) := by
    calc (1 + h * K) ^ (j + 1) ≤ Real.exp (h * K) ^ (j + 1) := by
          gcongr
          linarith [Real.add_one_le_exp (h * K)]
      _ = Real.exp ((j + 1) * h * K) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ ≤ Real.exp (K * (t + 1)) := by
          apply Real.exp_le_exp.2
          have : (j + 1 : ℝ) * h ≤ t + 1 := by nlinarith [hhN.trans (min_le_right _ _)]
          nlinarith
  have hj1 : ((j : ℝ) + 1) * h ≤ t + 1 := by nlinarith [hhN.trans (min_le_right _ _)]
  calc |eulerSeq F y h (wk n) j + (t - j * h) * F (eulerSeq F y h (wk n) j - w (j * h)) - u t|
      ≤ (1 + h * K) * |eulerSeq F y h (wk n) j - u (j * h)| + h * ε := hstep
    _ ≤ (1 + h * K) * (j * h * ε * (1 + h * K) ^ j) + h * ε * (1 + h * K) ^ (j + 1) := by
        have h1K : 0 ≤ 1 + h * K := add_nonneg zero_le_one (mul_nonneg hh.le hK)
        exact add_le_add (mul_le_mul_of_nonneg_left hd h1K)
          (le_mul_of_one_le_right (mul_nonneg hh.le hε.le)
            (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hh.le hK))))
    _ = ((j : ℝ) + 1) * h * ε * (1 + h * K) ^ (j + 1) := by ring
    _ ≤ (t + 1) * ε * Real.exp (K * (t + 1)) := by
        have h1 : 0 ≤ (1 + h * K) ^ (j + 1) := by positivity
        calc ((j : ℝ) + 1) * h * ε * (1 + h * K) ^ (j + 1)
            ≤ (t + 1) * ε * (1 + h * K) ^ (j + 1) := by
              have := mul_le_mul_of_nonneg_right hj1 hε.le
              nlinarith
          _ ≤ (t + 1) * ε * Real.exp (K * (t + 1)) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ε' / 2 := by rw [hεdef, hC]; field_simp
    _ < ε' := by linarith

end Euler

/-! ### Measurability of the Euler scheme -/

section AuxMeas

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_eulerSeq_aux {F : ℝ → ℝ} (hF : Measurable F) (y h : ℝ) {X : ℕ → Ω → ℝ} :
    ∀ k : ℕ, (∀ j < k, Measurable (X j)) → Measurable fun ω => eulerSeq F y h (fun j => X j ω) k
  | 0, _ => measurable_const
  | k + 1, hX => by
    have ih := measurable_eulerSeq_aux hF y h k fun j hj => hX j (hj.trans (Nat.lt_succ_self k))
    exact ih.add (measurable_const.mul (hF.comp (ih.sub (hX k (Nat.lt_succ_self k)))))

theorem measurable_eulerAt_aux {F : ℝ → ℝ} (hF : Measurable F) (y : ℝ) (n : ℕ) (t : ℝ)
    {X : ℕ → Ω → ℝ} (hX : ∀ j ≤ Girsanov.stepIdx n t, Measurable (X j)) :
    Measurable fun ω => eulerAt F y n (fun j => X j ω) t := by
  have h1 := measurable_eulerSeq_aux (X := X) hF y (1 / 2 ^ n) (Girsanov.stepIdx n t)
    fun j hj => hX j hj.le
  exact h1.add (measurable_const.mul (hF.comp (h1.sub (hX _ le_rfl))))

theorem measurable_limsup_aux {G : ℕ → Ω → ℝ} (hG : ∀ n, Measurable (G n)) :
    Measurable fun ω => limsup (fun n => G n ω) atTop :=
  Measurable.limsup hG

end AuxMeas

/-! ### The mark driven by a killed driver -/

section Process

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The Euler approximation of level `n` of the mark `U' = F(U − W)`, `U 0 = y`, reading the killed
driver at the dyadic times. -/
def markEuler (F : ℝ → ℝ) (y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  eulerAt F y n (fun k => Girsanov.killed ζ W (Girsanov.grid n k) ω) t

/-- **The mark** `U' = F(U − W)`, `U 0 = y`, driven by `W` before `ζ`: the `limsup` of the Euler
approximations (measurable for every `ω`; the solution on every continuous path,
`markFlow_eq_of_continuousOn`). -/
def markFlow (F : ℝ → ℝ) (y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  limsup (fun n => markEuler F y ζ W n t ω) atTop

variable {F : ℝ → ℝ} {y : ℝ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

/-- Each value `markFlow F y ζ W t` is `𝓕_t`-measurable. -/
theorem measurable_markFlow (hF : Measurable F) (hW : AdaptedBefore 𝓕 ζ W) (t : ℝ≥0) :
    Measurable[𝓕 t] (markFlow F y ζ W t) := by
  refine @measurable_limsup_aux Ω (𝓕 t) _ fun n => ?_
  refine @measurable_eulerAt_aux Ω (𝓕 t) F hF y n t _ fun j hj => ?_
  refine (Girsanov.measurable_killed hW _).mono (𝓕.mono ?_) le_rfl
  exact (Girsanov.grid_mono n hj).trans (Girsanov.grid_stepIdx_le n t)

/-- The mark is adapted before `ζ`. -/
theorem adaptedBefore_markFlow (hF : Measurable F) (hW : AdaptedBefore 𝓕 ζ W) :
    AdaptedBefore 𝓕 ζ (markFlow F y ζ W) := by
  intro t A hA
  have hζ : MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hW t Set.univ MeasurableSet.univ
  exact hζ.inter (measurable_markFlow hF hW t hA)

/-- On a path along which `W` is continuous before `ζ`, for every `t₁ < ζ` the mark agrees on
`[0, t₁]` with a continuous solution of `u = y + ∫ F(u − W)`. -/
theorem exists_markFlow_eq {K : ℝ≥0} (hF : LipschitzWith K F) {M : ℝ} (hM : ∀ x, |F x| ≤ M)
    {ω : Ω} (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) {t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < ζ ω) :
    ∃ u : ℝ → ℝ, ContinuousOn u (Icc 0 t₁) ∧
      (∀ s ∈ Icc (0 : ℝ) t₁, u s = y + ∫ r in (0 : ℝ)..s, F (u r - W r.toNNReal ω)) ∧
      ∀ s ∈ Icc (0 : ℝ) t₁, markFlow F y ζ W s.toNNReal ω = u s := by
  set wt : ℝ → ℝ := fun s => W (min s.toNNReal t₁) ω with hwt
  have hwtc : Continuous wt := by
    refine hWc.comp_continuous (continuous_real_toNNReal.min continuous_const) fun s => ?_
    exact lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) ht₁
  have hwt_eq : ∀ s ∈ Icc (0 : ℝ) t₁, wt s = W s.toNNReal ω := fun s hs => by
    simp only [hwt, min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  have hLD : OneForce.LipData F (fun s => -wt s) := ⟨⟨K, hF⟩, ⟨M, hM⟩, hwtc.neg⟩
  set G := OneForce.lipSol F y (fun s => -wt s) with hG
  set u : ℝ → ℝ := fun s => G s + wt s with hu
  have huc : ContinuousOn u (Icc 0 t₁) :=
    (OneForce.continuousOn_lipSol hLD t₁.coe_nonneg y).add hwtc.continuousOn
  have hueq : ∀ s ∈ Icc (0 : ℝ) t₁, u s = y + ∫ r in (0 : ℝ)..s, F (u r - wt r) := by
    intro s hs
    have := OneForce.lipSol_eq hLD y hs.1
    simp only [hu, add_sub_cancel_right]
    rw [← hG] at this
    rw [this]
    ring
  have hconv : ∀ s ∈ Icc (0 : ℝ) t₁, markFlow F y ζ W s.toNNReal ω = u s := by
    intro s hs
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1
    have hT := tendsto_eulerAt (y := y) (t := s) hF hs.1 hwtc.continuousOn
      (huc.mono (Icc_subset_Icc le_rfl hs.2))
      (fun r hr => hueq r ⟨hr.1, hr.2.trans hs.2⟩)
      (wk := fun n k => Girsanov.killed ζ W (Girsanov.grid n k) ω) fun n k hk => by
        have hgk : ((Girsanov.grid n k : ℝ≥0) : ℝ) = k / 2 ^ n := Girsanov.coe_grid n k
        have hle : Girsanov.grid n k ≤ t₁ := by
          rw [← NNReal.coe_le_coe, hgk]; exact hk.trans hs.2
        rw [Girsanov.killed_of_lt (lt_of_le_of_lt (by exact_mod_cast hle) ht₁), hwt]
        simp only
        congr 1
        rw [← hgk, Real.toNNReal_coe, min_eq_left hle]
    unfold markFlow markEuler
    rw [hs']
    exact hT.limsup_eq
  refine ⟨u, huc, fun s hs => ?_, hconv⟩
  rw [hueq s hs]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  simp only [hwt_eq r ⟨hr.1, hr.2.trans hs.2⟩]

/-- **The mark solves its equation.** On a path along which `W` is continuous before `ζ`, the mark
is continuous before `ζ` and `U t = y + ∫₀ᵗ F(U − W)` for every `t < ζ`. -/
theorem markFlow_eq_of_continuousOn {K : ℝ≥0} (hF : LipschitzWith K F) {M : ℝ}
    (hM : ∀ x, |F x| ≤ M) {ω : Ω}
    (hWc : ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    ContinuousOn (fun s => markFlow F y ζ W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      markFlow F y ζ W t ω
        = y + ∫ s in (0 : ℝ)..t, F (markFlow F y ζ W s.toNNReal ω - W s.toNNReal ω) := by
  constructor
  · intro t₀ ht₀
    obtain ⟨t₁, h01, h1ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht₀
    have h01' : t₀ < t₁ := by exact_mod_cast h01
    obtain ⟨u, huc, -, hconv⟩ := exists_markFlow_eq (y := y) hF hM hWc h1ζ
    have hcont : ContinuousOn (fun s : ℝ≥0 => u s) (Iic t₁) :=
      huc.comp NNReal.continuous_coe.continuousOn fun s hs => ⟨s.coe_nonneg, by exact_mod_cast hs⟩
    have hca : ContinuousAt (fun s : ℝ≥0 => u s) t₀ :=
      hcont.continuousAt (Iic_mem_nhds h01')
    have heq : (fun s : ℝ≥0 => u s) =ᶠ[𝓝 t₀] fun s => markFlow F y ζ W s ω := by
      filter_upwards [Iic_mem_nhds h01'] with s hs
      have := hconv s ⟨s.coe_nonneg, by exact_mod_cast hs⟩
      rw [Real.toNNReal_coe] at this
      exact this.symm
    exact (hca.congr heq).continuousWithinAt
  · intro t ht
    obtain ⟨u, -, hueq, hconv⟩ := exists_markFlow_eq (y := y) hF hM hWc ht
    have htt : (t : ℝ) ∈ Icc (0 : ℝ) t := ⟨t.coe_nonneg, le_rfl⟩
    have h1 := hconv t htt
    rw [Real.toNNReal_coe] at h1
    rw [h1, hueq t htt]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    simp only [hconv r hr]

end Process

/-! ### Right and left marks -/

/-- The cut drift of a mark on the right of the driver: `F x = 2 / max x δ`, equal to `2 / x` for
`x ≥ δ` (Bessel's `regDrift 2 δ`). -/
def rightMarkDrift (δ : ℝ) : ℝ → ℝ := Bessel.regDrift 2 δ

/-- The cut drift of a mark on the left of the driver: `F x = −2 / max (−x) δ`, equal to `2 / x` for
`x ≤ −δ`. -/
def leftMarkDrift (δ : ℝ) (x : ℝ) : ℝ := -Bessel.regDrift 2 δ (-x)

theorem lipschitzWith_rightMarkDrift {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal (2 / δ ^ 2)) (rightMarkDrift δ) :=
  Bessel.lipschitzWith_regDrift (by norm_num) hδ

theorem lipschitzWith_leftMarkDrift {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (Real.toNNReal (2 / δ ^ 2)) (leftMarkDrift δ) := by
  have h := (Bessel.lipschitzWith_regDrift (c := 2) (by norm_num) hδ).comp
    (LipschitzWith.id.neg (α := ℝ))
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  have := h.dist_le_mul x x'
  simp only [Function.comp_apply, mul_one] at this
  rw [leftMarkDrift, leftMarkDrift, dist_neg_neg]
  simpa using this

theorem abs_rightMarkDrift_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |rightMarkDrift δ x| ≤ 2 / δ :=
  Bessel.abs_regDrift_le (by norm_num) hδ x

theorem abs_leftMarkDrift_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |leftMarkDrift δ x| ≤ 2 / δ := by
  rw [leftMarkDrift, abs_neg]
  exact Bessel.abs_regDrift_le (by norm_num) hδ _

theorem rightMarkDrift_of_le {δ x : ℝ} (hx : δ ≤ x) : rightMarkDrift δ x = 2 / x := by
  rw [rightMarkDrift, Bessel.regDrift, max_eq_left hx]

theorem leftMarkDrift_of_le {δ x : ℝ} (hx : δ ≤ -x) : leftMarkDrift δ x = 2 / x := by
  rw [leftMarkDrift, Bessel.regDrift, max_eq_left hx, div_neg, neg_neg]

/-- The mark starts at its initial position (for every `ω`). -/
theorem markFlow_zero {Ω : Type*} (F : ℝ → ℝ) (y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (ω : Ω) : markFlow F y ζ W 0 ω = y := by
  have h : ∀ n, markEuler F y ζ W n 0 ω = y := fun n => by
    simp [markEuler, eulerAt, Girsanov.stepIdx, eulerSeq, Girsanov.grid_zero]
  unfold markFlow
  simp only [h]
  exact limsup_const y

end Sec2

end InteractingSLE
