/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB7aCmpLoewner

/-!
# Lemma GB1: the passive-gap estimate at a new real swallow

Packet PROVE-RLC-G. Supplement §8.1, Lemma GB1 (`source/spec/p481-528.md` L710–L740, pp. 510–511): for a chordal
Loewner chain with continuous driver `W` before `U < ∞`, an active coordinate `b_u < W_u` of a retained tip and a right
real-base junction `v_u ≥ W_u` with the characteristic equations `db = 2/(b − W) du`, `dv = 2/(v − W) du`, and an
original real point `x` that survives until `U` with `W_u ≤ v_u ≤ g_u(x)` and has an upper half-neighbourhood in the
completed hull `K_U`,
`liminf_{u ↑ U} (v_u − W_u)/(W_u − b_u) = 0`, and the limit is `0` when `W` extends continuously through `U`.

**Lean form.** Centred coordinates: the passive gap `g_u(x) − W_u` is `X_u = Re f_u(x)` with `f_u = fwdMap W u`
(the centred forward flow). The driver is a continuous `W : ℝ → ℝ` with `W 0 = 0` (the existing forward-flow API is
stated for a driver on `ℝ`; in G8's application the joint driver is continuous through the swallow time because the
curve continues). The hull hypothesis enters only through "`x` is not alive at `U`" (`GB1.not_alive_of_hull`: an
alive real point has a neighbourhood off the hull, `GB7a.exists_ball_notMem_fwdHull`).

**Proof.** (1) `liminf X = 0` (`GB1.frequently_fwdMap_re_lt`): otherwise `X ≥ δ > 0` on a final interval and `x` stays
alive through `U` (`GB7a.exists_isForwardSol_of_le`). (2) `D = v − b` is nondecreasing (its derivative
`2/(v − W) + 2/(W − b)` is nonnegative), so `D ≥ D₀ > 0`; with `a = v − W ≤ X`, the ratio `a/(D − a) ≤ 2a/D₀` is small
whenever `X` is (`GB1.frequently_ratio_lt`). (3) With `W` continuous at `U`, `X → 0` (`GB1.tendsto_fwdMap_re`): after a
late time `s₁` with `X(s₁) < ε/4`, an excursion of `X` to `ε` would have to climb from its last value `≤ ε/4`, which
the equation `dX = −dW + 2/X du` forbids (oscillation of `W` near `U` plus `2(U − s₁)/(ε/4)`); hence the ratio tends to
`0` (`GB1.tendsto_ratio`).

Main results: **`GB1.frequently_ratio_lt`** (GB1, liminf form), **`GB1.tendsto_ratio`** (the limit form),
`GB1.frequently_ratio_lt_of_hull`, `GB1.tendsto_ratio_of_hull` (with the source's hull hypothesis).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB1

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open Aux25 (exists_real_of_isForwardSol pos_of_ne_zero_of_pos)

variable {W : ℝ → ℝ}

/-- **The real flow of an alive point, read through `fwdMap`.** If `x > 0` is alive on `[0, s]`, the centred real flow
`r ↦ Re f_r(x)` is, on `[0, s]`, a continuous positive solution of the centred real Loewner equation from `x`. -/
theorem exists_pkg (hW : Continuous W) (hW0 : W 0 = 0) {x s : ℝ} (hx : 0 < x) (hs : 0 ≤ s)
    (halive : ∃ v, IsForwardSol W (x : ℂ) s v) :
    ContinuousOn (fun r => (fwdMap W r (x : ℂ)).re) (Icc 0 s) ∧
      (∀ r ∈ Icc (0 : ℝ) s, 0 < (fwdMap W r (x : ℂ)).re) ∧ (fwdMap W 0 (x : ℂ)).re = x ∧
      (∀ s₁ ∈ Icc (0 : ℝ) s, ∀ s₂ ∈ Icc (0 : ℝ) s, s₁ ≤ s₂ →
        (fwdMap W s₂ (x : ℂ)).re - (fwdMap W s₁ (x : ℂ)).re =
          -(W s₂ - W s₁) + ∫ r in s₁..s₂, 2 / (fwdMap W r (x : ℂ)).re) ∧
      IntervalIntegrable (fun r => 2 / (fwdMap W r (x : ℂ)).re) volume 0 s := by
  obtain ⟨v, hv⟩ := halive
  obtain ⟨X, hXc, hXv, hX0, hXeq, hXint⟩ := exists_real_of_isForwardSol hW hs hv
  rw [hW0, sub_zero] at hX0
  have hXpos := pos_of_ne_zero_of_pos hXc (fun r hr => (hXv r hr).1) (by rw [hX0]; exact hx)
  have hf : ∀ r ∈ Icc (0 : ℝ) s, (fwdMap W r (x : ℂ)).re = X r := fun r hr => by
    rw [fwdMap_eq_of_isForwardSol hW hv hr, (hXv r hr).2, Complex.ofReal_re]
  refine ⟨hXc.congr hf, fun r hr => by rw [hf r hr]; exact hXpos r hr, by rw [hf 0 ⟨le_rfl, hs⟩, hX0],
    fun s₁ h₁ s₂ h₂ h₁₂ => ?_, ?_⟩
  · rw [hf s₁ h₁, hf s₂ h₂, hXeq s₁ h₁ s₂ h₂ h₁₂]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    simp only [hf r (uIcc_subset_Icc h₁ h₂ hr)]
  · rw [intervalIntegrable_iff] at hXint ⊢
    refine hXint.congr_fun (fun r hr => ?_) measurableSet_uIoc
    rw [uIoc_of_le hs] at hr
    simp only [hf r ⟨hr.1.le, hr.2⟩]

/-- **The source's hull hypothesis gives death at `U`**: a real point with an upper half-neighbourhood in the hull
`K_U` is not alive at `U`. -/
theorem not_alive_of_hull (hW : Continuous W) {U x : ℝ} (hU : 0 ≤ U)
    (hhull : ∃ r > 0, ∀ z : ℂ, 0 < z.im → ‖z - x‖ < r → z ∈ fwdHull W U) :
    ¬ ∃ v, IsForwardSol W (x : ℂ) U v := by
  rintro ⟨v, hv⟩
  obtain ⟨r, hr, hsub⟩ := hhull
  obtain ⟨r', hr', hnot⟩ := GB7a.exists_ball_notMem_fwdHull hW hU hv
  set ρ := min r r' / 2 with hρ
  have hρ0 : 0 < ρ := half_pos (lt_min hr hr')
  have hnorm : ‖((x : ℂ) + ρ * Complex.I) - x‖ = ρ := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ0]
  have hlt : ρ < min r r' := half_lt_self (lt_min hr hr')
  have him : 0 < ((x : ℂ) + ρ * Complex.I).im := by simpa using hρ0
  exact hnot _ (by rw [hnorm]; exact hlt.trans_le (min_le_right _ _))
    (hsub _ him (by rw [hnorm]; exact hlt.trans_le (min_le_left _ _)))

/-- **Step 1 of GB1: `liminf (g_u(x) − W_u) = 0`.** If `x > 0` is alive on `[0, s]` for every `s < U` but not at `U`,
the centred passive gap is frequently below every `δ > 0` as `u ↑ U`. -/
theorem frequently_fwdMap_re_lt (hW : Continuous W) (hW0 : W 0 = 0) {U x : ℝ} (hU : 0 < U) (hx : 0 < x)
    (halive : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol W (x : ℂ) s v) (hdead : ¬ ∃ v, IsForwardSol W (x : ℂ) U v)
    {δ : ℝ} (hδ : 0 < δ) : ∃ᶠ s in 𝓝[<] U, (fwdMap W s (x : ℂ)).re < δ := by
  intro hev
  simp only [not_lt] at hev
  obtain ⟨q₁, hq₁, hq₁sub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
  set q := (max q₁ 0 + U) / 2 with hqdef
  have hmax : max q₁ 0 < U := max_lt hq₁ hU
  have hq₁q : q₁ < q := by have := le_max_left q₁ 0; rw [hqdef]; linarith
  have hq0 : 0 < q := by have := le_max_right q₁ 0; rw [hqdef]; linarith
  have hqU : q < U := by rw [hqdef]; linarith
  set f : ℝ → ℝ := fun s => (fwdMap W s (x : ℂ)).re with hfdef
  obtain ⟨vq, hvq⟩ := halive q ⟨hq0.le, hqU⟩
  have hu' : ∀ s ∈ Ico q U, ContinuousOn f (Icc q s) ∧
      (∀ s₁ ∈ Icc q s, ∀ s₂ ∈ Icc q s, s₁ ≤ s₂ → f s₂ - f s₁ = -(W s₂ - W s₁) + ∫ r in s₁..s₂, 2 / f r) ∧
      IntervalIntegrable (fun r => 2 / f r) volume q s := by
    intro s hs
    have hs0 : 0 ≤ s := hq0.le.trans hs.1
    obtain ⟨hc, -, -, heq, hint⟩ := exists_pkg hW hW0 hx hs0 (halive s ⟨hs0, hs.2⟩)
    have hsub : Icc q s ⊆ Icc 0 s := Icc_subset_Icc_left hq0.le
    refine ⟨hc.mono hsub, fun s₁ h₁ s₂ h₂ h₁₂ => heq s₁ (hsub h₁) s₂ (hsub h₂) h₁₂, ?_⟩
    exact hint.mono_set (by rw [uIcc_of_le hs.1, uIcc_of_le hs0]; exact hsub)
  have hcf : ∀ s ∈ Ico q U, δ ≤ f s := fun s hs => hq₁sub ⟨hq₁q.trans_le hs.1, hs.2⟩
  have huq : f q ≤ (vq q).re := by
    simp only [hfdef]
    rw [fwdMap_eq_of_isForwardSol hW hvq ⟨hq0.le, le_rfl⟩]
  exact hdead (GB7a.exists_isForwardSol_of_le hW hW0 hx hq0.le hqU.le hvq hδ hu' hcf huq)

/-- The junction-to-tip gap `D = v − b` is nondecreasing from `u₀`: its increments are integrals of
`2/(v − W) − 2/(b − W) ≥ 0`. -/
theorem le_sub_of_char {b v : ℝ → ℝ} {u₀ U : ℝ}
    (hbW : ∀ s ∈ Ico u₀ U, b s < W s) (hWv : ∀ s ∈ Ico u₀ U, W s ≤ v s)
    (hb : ∀ s ∈ Ico u₀ U, b s - b u₀ = ∫ r in u₀..s, 2 / (b r - W r))
    (hv : ∀ s ∈ Ico u₀ U, v s - v u₀ = ∫ r in u₀..s, 2 / (v r - W r))
    (hbi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (b r - W r)) volume u₀ s)
    (hvi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (v r - W r)) volume u₀ s) :
    ∀ s ∈ Ico u₀ U, v u₀ - b u₀ ≤ v s - b s := by
  intro s hs
  have hnn : 0 ≤ ∫ r in u₀..s, (2 / (v r - W r) - 2 / (b r - W r)) := by
    refine intervalIntegral.integral_nonneg hs.1 fun r hr => ?_
    have hr' : r ∈ Ico u₀ U := ⟨hr.1, hr.2.trans_lt hs.2⟩
    have h1 : 0 ≤ 2 / (v r - W r) := div_nonneg (by norm_num) (sub_nonneg.2 (hWv r hr'))
    have h2 : 2 / (b r - W r) < 0 := div_neg_of_pos_of_neg (by norm_num) (sub_neg.2 (hbW r hr'))
    linarith
  rw [intervalIntegral.integral_sub (hvi s hs) (hbi s hs), ← hb s hs, ← hv s hs] at hnn
  linarith

/-- **Lemma GB1** (passive-gap estimate at a new real swallow; liminf form). In centred coordinates: let the real point
`x > 0` be alive on `[0, s]` for every `s < U` and not alive at `U`; let `b < W ≤ v` on `[u₀, U)` with the
characteristic equations `b(s) − b(u₀) = ∫ 2/(b − W)`, `v(s) − v(u₀) = ∫ 2/(v − W)` (integrable), and the sandwich
`v − W ≤ X = Re f(x)`. Then `liminf_{u ↑ U} (v − W)/(W − b) = 0`: the ratio is frequently below every `ε > 0`. -/
theorem frequently_ratio_lt (hW : Continuous W) (hW0 : W 0 = 0) {U x : ℝ} (hU : 0 < U) (hx : 0 < x)
    (halive : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol W (x : ℂ) s v) (hdead : ¬ ∃ v, IsForwardSol W (x : ℂ) U v)
    {b v : ℝ → ℝ} {u₀ : ℝ} (hu₀U : u₀ < U)
    (hbW : ∀ s ∈ Ico u₀ U, b s < W s) (hWv : ∀ s ∈ Ico u₀ U, W s ≤ v s)
    (hvx : ∀ s ∈ Ico u₀ U, v s - W s ≤ (fwdMap W s (x : ℂ)).re)
    (hb : ∀ s ∈ Ico u₀ U, b s - b u₀ = ∫ r in u₀..s, 2 / (b r - W r))
    (hv : ∀ s ∈ Ico u₀ U, v s - v u₀ = ∫ r in u₀..s, 2 / (v r - W r))
    (hbi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (b r - W r)) volume u₀ s)
    (hvi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (v r - W r)) volume u₀ s)
    {ε : ℝ} (hε : 0 < ε) : ∃ᶠ s in 𝓝[<] U, (v s - W s) / (W s - b s) < ε := by
  have hu₀ : u₀ ∈ Ico u₀ U := ⟨le_rfl, hu₀U⟩
  set D₀ := v u₀ - b u₀ with hD₀
  have hD₀pos : 0 < D₀ := by have := hbW u₀ hu₀; have := hWv u₀ hu₀; rw [hD₀]; linarith
  have hD := le_sub_of_char hbW hWv hb hv hbi hvi
  set δ := min (D₀ / 2) (ε * D₀ / 4) with hδ
  have hδ0 : 0 < δ := lt_min (half_pos hD₀pos) (by positivity)
  have hfreq := frequently_fwdMap_re_lt hW hW0 hU hx halive hdead hδ0
  refine (hfreq.and_eventually (Ico_mem_nhdsLT hu₀U)).mono fun s ⟨hfs, hs⟩ => ?_
  have ha0 : 0 ≤ v s - W s := sub_nonneg.2 (hWv s hs)
  have haδ : v s - W s < δ := (hvx s hs).trans_lt hfs
  have hDs := hD s hs
  have hden : D₀ / 2 ≤ W s - b s := by
    have := min_le_left (D₀ / 2) (ε * D₀ / 4)
    linarith
  have hden0 : 0 < W s - b s := (half_pos hD₀pos).trans_le hden
  rw [div_lt_iff₀ hden0]
  have h1 : v s - W s < ε * D₀ / 4 := haδ.trans_le (min_le_right _ _)
  have h2 : ε * D₀ / 4 < ε * (W s - b s) := by nlinarith
  linarith

/-- **The passive gap tends to `0`** when the driver is continuous through `U`: after a late time where it is below
`ε/4`, the equation `dX = −dW + 2/X du` keeps it below `ε` up to `U`. -/
theorem tendsto_fwdMap_re (hW : Continuous W) (hW0 : W 0 = 0) {U x : ℝ} (hU : 0 < U) (hx : 0 < x)
    (halive : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol W (x : ℂ) s v) (hdead : ¬ ∃ v, IsForwardSol W (x : ℂ) U v) :
    Tendsto (fun s => (fwdMap W s (x : ℂ)).re) (𝓝[<] U) (𝓝 0) := by
  set f : ℝ → ℝ := fun s => (fwdMap W s (x : ℂ)).re with hfdef
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  -- the oscillation of `W` near `U`
  obtain ⟨ρ₁, hρ₁, hW₁⟩ := Metric.continuousAt_iff.1 (hW.continuousAt (x := U)) (ε / 8) (by positivity)
  set ρ := min (min ρ₁ U) (ε * η / 8) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₁ hU) (by positivity)
  have hfreq := frequently_fwdMap_re_lt hW hW0 hU hx halive hdead hη0
  obtain ⟨s₁, hs₁f, hs₁I⟩ := (hfreq.and_eventually (Ioo_mem_nhdsLT (by linarith : U - ρ < U))).exists
  have hs₁0 : 0 ≤ s₁ := by
    have : ρ ≤ U := (min_le_left _ _).trans (min_le_right _ _)
    linarith [hs₁I.1]
  have hosc : ∀ r ∈ Icc s₁ U, |W r - W U| < ε / 8 := fun r hr => by
    have h := hW₁ (x := r) (by
      rw [Real.dist_eq, abs_lt]
      have : ρ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
      constructor <;> linarith [hs₁I.1, hr.1, hr.2])
    rwa [Real.dist_eq] at h
  have hlen : U - s₁ ≤ ε * η / 8 := by
    have : ρ ≤ ε * η / 8 := min_le_right _ _
    linarith [hs₁I.1]
  filter_upwards [Ioo_mem_nhdsLT hs₁I.2] with s hs
  have hs0 : 0 ≤ s := hs₁0.trans hs.1.le
  obtain ⟨hc, hpos, -, heq, hint⟩ := exists_pkg hW hW0 hx hs0 (halive s ⟨hs0, hs.2⟩)
  have hsub : Icc s₁ s ⊆ Icc 0 s := Icc_subset_Icc_left hs₁0
  rw [Real.dist_eq, sub_zero, abs_of_pos (hpos s ⟨hs0, le_rfl⟩)]
  by_contra hge
  rw [not_lt] at hge
  -- the last time `s₂ ∈ [s₁, s]` with `f ≤ η`
  set S := {r ∈ Icc s₁ s | f r ≤ η} with hS
  have hSc : IsClosed S := (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨s₁, ⟨le_rfl, hs.1.le⟩, hs₁f.le⟩
  have hSbdd : BddAbove S := ⟨s, fun r hr => hr.1.2⟩
  set s₂ := sSup S with hs₂
  have hs₂S : s₂ ∈ S := hSc.csSup_mem hSne hSbdd
  have hs₂s : s₂ < s := by
    rcases lt_or_eq_of_le hs₂S.1.2 with h | h
    · exact h
    · exfalso
      have := hs₂S.2
      rw [h] at this
      linarith
  have habove : ∀ r ∈ Ioo s₂ s, η < f r := fun r hr => by
    by_contra hle
    rw [not_lt] at hle
    have : r ≤ s₂ := le_csSup hSbdd ⟨⟨hs₂S.1.1.trans hr.1.le, hr.2.le⟩, hle⟩
    linarith [hr.1]
  have hs₂0 : s₂ ∈ Icc (0 : ℝ) s := ⟨hs₁0.trans hs₂S.1.1, hs₂s.le⟩
  have hincr := heq s₂ hs₂0 s ⟨hs0, le_rfl⟩ hs₂s.le
  have hint₂ : IntervalIntegrable (fun r => 2 / f r) volume s₂ s :=
    hint.mono_set (by rw [uIcc_of_le hs₂s.le, uIcc_of_le hs0]; exact Icc_subset_Icc_left hs₂0.1)
  have hbound : (∫ r in s₂..s, 2 / f r) ≤ ∫ r in s₂..s, (2 / η : ℝ) := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hs₂s.le hint₂ intervalIntegrable_const fun r hr => ?_
    have hr0 : 0 < f r := hη0.trans (habove r hr)
    exact div_le_div_of_nonneg_left (by norm_num) hη0 (habove r hr).le
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hW2 := hosc s₂ ⟨hs₂S.1.1, hs₂s.le.trans hs.2.le⟩
  have hW3 := hosc s ⟨hs.1.le, hs.2.le⟩
  have hlen' : (s - s₂) * (2 / η) ≤ ε / 4 := by
    have h1 : s - s₂ ≤ ε * η / 8 := by linarith [hs₂S.1.1, hs.2]
    have h2 : (s - s₂) * (2 / η) ≤ ε * η / 8 * (2 / η) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : ε * η / 8 * (2 / η) = ε / 4 := by field_simp; ring
    linarith
  have hf2 : f s₂ ≤ η := hs₂S.2
  rw [abs_lt] at hW2 hW3
  have : f s ≤ η + ε / 4 + ε / 4 := by
    have e : f s = f s₂ + (-(W s - W s₂) + ∫ r in s₂..s, 2 / f r) := by rw [← hincr]; ring
    rw [e]
    linarith [hW2.1, hW2.2, hW3.1, hW3.2]
  rw [hη] at this
  linarith

/-- **Lemma GB1, limit form** (driver continuous through `U`): `(v − W)/(W − b) → 0` as `u ↑ U`. -/
theorem tendsto_ratio (hW : Continuous W) (hW0 : W 0 = 0) {U x : ℝ} (hU : 0 < U) (hx : 0 < x)
    (halive : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol W (x : ℂ) s v) (hdead : ¬ ∃ v, IsForwardSol W (x : ℂ) U v)
    {b v : ℝ → ℝ} {u₀ : ℝ} (hu₀U : u₀ < U)
    (hbW : ∀ s ∈ Ico u₀ U, b s < W s) (hWv : ∀ s ∈ Ico u₀ U, W s ≤ v s)
    (hvx : ∀ s ∈ Ico u₀ U, v s - W s ≤ (fwdMap W s (x : ℂ)).re)
    (hb : ∀ s ∈ Ico u₀ U, b s - b u₀ = ∫ r in u₀..s, 2 / (b r - W r))
    (hv : ∀ s ∈ Ico u₀ U, v s - v u₀ = ∫ r in u₀..s, 2 / (v r - W r))
    (hbi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (b r - W r)) volume u₀ s)
    (hvi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (v r - W r)) volume u₀ s) :
    Tendsto (fun s => (v s - W s) / (W s - b s)) (𝓝[<] U) (𝓝 0) := by
  have hu₀ : u₀ ∈ Ico u₀ U := ⟨le_rfl, hu₀U⟩
  set D₀ := v u₀ - b u₀ with hD₀
  have hD₀pos : 0 < D₀ := by have := hbW u₀ hu₀; have := hWv u₀ hu₀; rw [hD₀]; linarith
  have hD := le_sub_of_char hbW hWv hb hv hbi hvi
  have hX := tendsto_fwdMap_re hW hW0 hU hx halive hdead
  have hup : Tendsto (fun s => 2 / D₀ * (fwdMap W s (x : ℂ)).re) (𝓝[<] U) (𝓝 0) := by
    simpa using hX.const_mul (2 / D₀)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Ico_mem_nhdsLT hu₀U] with s hs
    exact div_nonneg (sub_nonneg.2 (hWv s hs)) (sub_pos.2 (hbW s hs)).le
  · filter_upwards [Ico_mem_nhdsLT hu₀U, hX (gt_mem_nhds (half_pos hD₀pos))] with s hs hXs
    have hvs := hvx s hs
    have hDs := hD s hs
    have hXs' : (fwdMap W s (x : ℂ)).re < D₀ / 2 := hXs
    have hden : D₀ / 2 ≤ W s - b s := by linarith
    have hden0 : 0 < W s - b s := (half_pos hD₀pos).trans_le hden
    rw [div_le_iff₀ hden0]
    have ha0 : 0 ≤ v s - W s := sub_nonneg.2 (hWv s hs)
    have hX0 : 0 ≤ (fwdMap W s (x : ℂ)).re := ha0.trans hvs
    calc v s - W s ≤ (fwdMap W s (x : ℂ)).re := hvs
      _ = 2 / D₀ * (fwdMap W s (x : ℂ)).re * (D₀ / 2) := by field_simp
      _ ≤ 2 / D₀ * (fwdMap W s (x : ℂ)).re * (W s - b s) :=
          mul_le_mul_of_nonneg_left hden (by positivity)

/-- **Lemma GB1 with the source's hull hypothesis** (liminf form): an upper half-neighbourhood of `x` in the completed
hull `K_U`. -/
theorem frequently_ratio_lt_of_hull (hW : Continuous W) (hW0 : W 0 = 0) {U x : ℝ} (hU : 0 < U) (hx : 0 < x)
    (halive : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol W (x : ℂ) s v)
    (hhull : ∃ r > 0, ∀ z : ℂ, 0 < z.im → ‖z - x‖ < r → z ∈ fwdHull W U)
    {b v : ℝ → ℝ} {u₀ : ℝ} (hu₀U : u₀ < U)
    (hbW : ∀ s ∈ Ico u₀ U, b s < W s) (hWv : ∀ s ∈ Ico u₀ U, W s ≤ v s)
    (hvx : ∀ s ∈ Ico u₀ U, v s - W s ≤ (fwdMap W s (x : ℂ)).re)
    (hb : ∀ s ∈ Ico u₀ U, b s - b u₀ = ∫ r in u₀..s, 2 / (b r - W r))
    (hv : ∀ s ∈ Ico u₀ U, v s - v u₀ = ∫ r in u₀..s, 2 / (v r - W r))
    (hbi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (b r - W r)) volume u₀ s)
    (hvi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (v r - W r)) volume u₀ s)
    {ε : ℝ} (hε : 0 < ε) : ∃ᶠ s in 𝓝[<] U, (v s - W s) / (W s - b s) < ε :=
  frequently_ratio_lt hW hW0 hU hx halive (not_alive_of_hull hW hU.le hhull) hu₀U hbW hWv hvx hb hv hbi hvi hε

/-- **Lemma GB1 with the source's hull hypothesis** (limit form). -/
theorem tendsto_ratio_of_hull (hW : Continuous W) (hW0 : W 0 = 0) {U x : ℝ} (hU : 0 < U) (hx : 0 < x)
    (halive : ∀ s ∈ Ico 0 U, ∃ v, IsForwardSol W (x : ℂ) s v)
    (hhull : ∃ r > 0, ∀ z : ℂ, 0 < z.im → ‖z - x‖ < r → z ∈ fwdHull W U)
    {b v : ℝ → ℝ} {u₀ : ℝ} (hu₀U : u₀ < U)
    (hbW : ∀ s ∈ Ico u₀ U, b s < W s) (hWv : ∀ s ∈ Ico u₀ U, W s ≤ v s)
    (hvx : ∀ s ∈ Ico u₀ U, v s - W s ≤ (fwdMap W s (x : ℂ)).re)
    (hb : ∀ s ∈ Ico u₀ U, b s - b u₀ = ∫ r in u₀..s, 2 / (b r - W r))
    (hv : ∀ s ∈ Ico u₀ U, v s - v u₀ = ∫ r in u₀..s, 2 / (v r - W r))
    (hbi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (b r - W r)) volume u₀ s)
    (hvi : ∀ s ∈ Ico u₀ U, IntervalIntegrable (fun r => 2 / (v r - W r)) volume u₀ s) :
    Tendsto (fun s => (v s - W s) / (W s - b s)) (𝓝[<] U) (𝓝 0) :=
  tendsto_ratio hW hW0 hU hx halive (not_alive_of_hull hW hU.le hhull) hu₀U hbW hWv hvx hb hv hbi hvi

end GB1

end InteractingSLE
