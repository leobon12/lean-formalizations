/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi3Tight
import InteractingSLE.Spec.Sec7.TrialsHi3Merge
import InteractingSLE.Spec.Supplement.LP4HalfBallFuture

/-!
# The low-sector trial bound: steering into a tight configuration

Packet PROVE-TRIALS-HI3. The first phase of the low-sector trial: from a normalized word (nearest marks at `∓1`, all
marks in `[−M, M]`), if the driver stays within `a = 1/8` of the line `c t` with a small speed `c` up to a time `T`,
then (deterministically, `steer_det`) all gaps stay at least `7/8`, the right marks have moved out to a far gap
`X ≥ ℓ₂ − a` (so the right spread, which never increases, is a small fraction of `X`), and the left marks are far
behind (`L₀ ≥ c T + 7/8`). The comparison with ordinary `SLE_κ` and the support theorem give this event a probability
bounded below uniformly over the family (`TrialsHi3Assembly`).

The barrier arguments are made on the integral equations of the marks, without derivatives (`le_of_barrier`).

## Main results

* `le_of_barrier`, `le_of_barrier'` (lower and upper barriers with a rate);
* **`steer_det`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi3

/-! ### A barrier lemma for integral equations -/

section Barrier

/-- **A lower barrier with a rate, for an integral equation.** If `g t − g s = ∫ₛᵗ φ` on `[0, T]`, `ℓ' < ℓ`,
`ℓ' < g 0`, and `φ ≥ r ≥ 0` wherever `ℓ' ≤ g ≤ ℓ`, then `g t ≥ min(ℓ, g 0 + r t)` on `[0, T]`. -/
theorem le_of_barrier {g φ : ℝ → ℝ} {T ℓ ℓ' r : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hφ : IntervalIntegrable φ volume 0 T)
    (hint : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → g t - g s = ∫ u in s..t, φ u)
    (hℓ' : ℓ' < ℓ) (h0 : ℓ' < g 0) (hr : 0 ≤ r)
    (hcond : ∀ s ∈ Icc (0 : ℝ) T, ℓ' ≤ g s → g s ≤ ℓ → r ≤ φ s) :
    ∀ t ∈ Icc (0 : ℝ) T, min ℓ (g 0 + r * t) ≤ g t := by
  have hφs : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable φ volume s t := fun s hs t ht =>
    hφ.mono_set ((uIcc_subset_Icc hs ht).trans (by rw [uIcc_of_le (hs.1.trans hs.2)]))
  -- the claim on `[0, t]`, assuming `g ≥ ℓ'` there
  have hmain : ∀ t ∈ Icc (0 : ℝ) T, (∀ s ∈ Icc (0 : ℝ) t, ℓ' ≤ g s) → min ℓ (g 0 + r * t) ≤ g t := by
    intro t ht hlow
    by_contra hcon
    rw [not_le] at hcon
    have ht0 : (0 : ℝ) ≤ t := ht.1
    set C : Set ℝ := Icc 0 t ∩ g ⁻¹' Ici ℓ with hC
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    by_cases hne : C.Nonempty
    · have hCc : IsClosed C := (hg.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hbdd : BddAbove C := ⟨t, fun s hs => hs.1.2⟩
      set s₀ := sSup C with hs₀
      have hs₀C : s₀ ∈ C := hCc.csSup_mem hne hbdd
      have hgs₀ : ℓ ≤ g s₀ := hs₀C.2
      have hgt : g t < ℓ := hcon.trans_le (min_le_left _ _)
      have hs₀t : s₀ ≤ t := hs₀C.1.2
      have hafter : ∀ s ∈ Ioc s₀ t, g s < ℓ := fun s hs => by
        by_contra h
        rw [not_lt] at h
        have : s ≤ s₀ := le_csSup hbdd ⟨⟨hs₀C.1.1.trans hs.1.le, hs.2⟩, h⟩
        exact absurd hs.1 (not_lt.2 this)
      have hs₀T : s₀ ∈ Icc (0 : ℝ) T := hsub hs₀C.1
      have hI := hint s₀ hs₀T t ht hs₀t
      have hmono : ∫ u in s₀..t, (fun _ => r) u ≤ ∫ u in s₀..t, φ u := by
        refine intervalIntegral.integral_mono_ae_restrict hs₀t intervalIntegrable_const (hφs s₀ hs₀T t ht) ?_
        refine (ae_restrict_iff' measurableSet_Icc).2 ((Measure.ae_ne volume s₀).mono fun s hne hs => ?_)
        have hs' : s ∈ Ioc s₀ t := ⟨lt_of_le_of_ne hs.1 (Ne.symm hne), hs.2⟩
        exact hcond s (hsub ⟨hs₀C.1.1.trans hs.1, hs.2⟩) (hlow s ⟨hs₀C.1.1.trans hs.1, hs.2⟩)
          (hafter s hs').le
      simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
      have : 0 ≤ (t - s₀) * r := mul_nonneg (sub_nonneg.2 hs₀t) hr
      linarith
    · have hall : ∀ s ∈ Icc (0 : ℝ) t, g s < ℓ := fun s hs => by
        by_contra h
        exact hne ⟨s, hs, not_lt.1 h⟩
      have hI := hint 0 ⟨le_rfl, ht0.trans ht.2⟩ t ht ht0
      have hmono : ∫ u in (0 : ℝ)..t, (fun _ => r) u ≤ ∫ u in (0 : ℝ)..t, φ u := by
        refine intervalIntegral.integral_mono_on ht0 intervalIntegrable_const
          (hφs 0 ⟨le_rfl, ht0.trans ht.2⟩ t ht) fun s hs => ?_
        exact hcond s (hsub hs) (hlow s hs) (hall s hs).le
      simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
      have : g 0 + r * t ≤ g t := by linarith
      exact absurd (this.trans_lt' (hcon.trans_le (min_le_right _ _))) (lt_irrefl _)
  -- bootstrap: `g ≥ min(ℓ, g 0) > ℓ'` everywhere
  have hT0 : ∀ t ∈ Icc (0 : ℝ) T, (0 : ℝ) ∈ Icc 0 T := fun t ht => ⟨le_rfl, ht.1.trans ht.2⟩
  have hboot := LP.LP4HB.forall_le_of_bootstrap (g := g) (τ := T) (c := min ℓ (g 0)) (δ := ℓ') hg (lt_min hℓ' h0)
    (min_le_right _ _) fun t ht hlow => by
      have := hmain t ht hlow
      have h2 : min ℓ (g 0) ≤ min ℓ (g 0 + r * t) := min_le_min le_rfl (by nlinarith [ht.1])
      linarith
  intro t ht
  refine hmain t ht fun s hs => ?_
  have := hboot s ⟨hs.1, hs.2.trans ht.2⟩
  exact (lt_min hℓ' h0).le.trans this

/-- **An upper barrier** (the lower barrier for `−g`). -/
theorem le_of_barrier' {g φ : ℝ → ℝ} {T ℓ ℓ' : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (hφ : IntervalIntegrable φ volume 0 T)
    (hint : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → g t - g s = ∫ u in s..t, φ u)
    (hℓ' : ℓ < ℓ') (h0 : g 0 < ℓ') (hcond : ∀ s ∈ Icc (0 : ℝ) T, ℓ ≤ g s → g s ≤ ℓ' → φ s ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) T, g t ≤ max ℓ (g 0) := by
  have h := le_of_barrier (g := fun s => -g s) (φ := fun s => -φ s) (T := T) (ℓ := -ℓ) (ℓ' := -ℓ') (r := 0)
    hg.neg hφ.neg (fun s hs t ht hst => by
      rw [intervalIntegral.integral_neg, ← hint s hs t ht hst]; ring)
    (by linarith) (by linarith) le_rfl fun s hs h1 h2 => by
      have := hcond s hs (by linarith) (by linarith)
      linarith
  intro t ht
  have := h t ht
  simp only [zero_mul, add_zero] at this
  rcases le_total ℓ (g 0) with hle | hle
  · rw [max_eq_right hle]
    rw [min_eq_right (by linarith)] at this
    linarith
  · rw [max_eq_left hle]
    rw [min_eq_left (by linarith)] at this
    linarith

end Barrier

/-! ### One right mark under a driver tube -/

section Mark

variable {w v : ℝ≥0 → ℝ} {y c a T : ℝ}

/-- The integral identity of `g(s) = v(s) − c s` on `[0, T]`. -/
theorem mark_int (hv : ∀ t : ℝ, t ∈ Icc (0 : ℝ) T →
      v t.toNNReal = y + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hint : IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 T) :
    ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t →
      (v t.toNNReal - c * t) - (v s.toNNReal - c * s) =
        ∫ u in s..t, (2 / (v u.toNNReal - w u.toNNReal) - c) := by
  intro s hs t ht hst
  have hT0 : (0 : ℝ) ≤ T := hs.1.trans hs.2
  have hi : ∀ x ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal))
      volume 0 x := fun x hx =>
    hint.mono_set (by rw [uIcc_of_le hx.1, uIcc_of_le hT0]; exact Icc_subset_Icc le_rfl hx.2)
  have hst' : IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume s t :=
    (hi s hs).symm.trans (hi t ht)
  rw [intervalIntegral.integral_sub hst' intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul, hv t ht, hv s hs, ← intervalIntegral.integral_interval_sub_left (hi t ht) (hi s hs)]
  ring

variable (hv : ∀ t : ℝ, t ∈ Icc (0 : ℝ) T →
      v t.toNNReal = y + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
  (hvc : ContinuousOn (fun s : ℝ => v s.toNNReal) (Icc 0 T))
  (hint : IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 T)
  (htube : ∀ s ∈ Icc (0 : ℝ) T, |w s.toNNReal - c * s| ≤ a)

include hv hvc hint htube

omit hv hvc hint in
/-- The gap `v − w` in terms of `g = v − c s`. -/
theorem mark_gap {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    (v s.toNNReal - c * s) - a ≤ v s.toNNReal - w s.toNNReal ∧
      v s.toNNReal - w s.toNNReal ≤ (v s.toNNReal - c * s) + a := by
  have := abs_le.1 (htube s hs)
  constructor <;> linarith

/-- **The lower barrier with a rate**: for `a > 0`, `1 ≤ y`, `ℓ ≥ 1`, `0 < r` with `2/(ℓ + a) − c ≥ r` and
`4a < 1`: `v(t) − c t ≥ min(ℓ, y + r t)` on `[0, T]`. -/
theorem mark_lower (ha : 0 < a) (ha4 : 4 * a < 1) (hy : 1 ≤ y) {ℓ r : ℝ} (hℓ : 1 ≤ ℓ) (hr : 0 ≤ r)
    (hrc : r ≤ 2 / (ℓ + a) - c) (hy0 : v 0 = y) :
    ∀ t ∈ Icc (0 : ℝ) T, min ℓ (y + r * t) ≤ v t.toNNReal - c * t := by
  have hcont : ContinuousOn (fun s : ℝ => v s.toNNReal - c * s) (Icc 0 T) :=
    hvc.sub (continuousOn_const.mul continuousOn_id)
  have h0 : v (Real.toNNReal 0) - c * 0 = y := by simp [hy0]
  have h := le_of_barrier (g := fun s : ℝ => v s.toNNReal - c * s)
    (φ := fun u => 2 / (v u.toNNReal - w u.toNNReal) - c) (ℓ := ℓ) (ℓ' := 2 * a) (r := r) hcont
    (hint.sub intervalIntegrable_const) (mark_int hv hint) (by linarith) (by rw [h0]; linarith) hr
    fun s hs h1 h2 => by
      obtain ⟨hg1, hg2⟩ := mark_gap htube hs
      have hR : a ≤ v s.toNNReal - w s.toNNReal := by linarith
      have hRpos : 0 < v s.toNNReal - w s.toNNReal := ha.trans_le hR
      have hRle : v s.toNNReal - w s.toNNReal ≤ ℓ + a := by linarith
      have : 2 / (ℓ + a) ≤ 2 / (v s.toNNReal - w s.toNNReal) :=
        div_le_div_of_nonneg_left (by norm_num) hRpos hRle
      linarith
  intro t ht
  have := h t ht
  rwa [h0] at this

/-- **The upper barrier**: with `ℓ ≥ 2/c + a` (`c > 0`): `v(t) − c t ≤ max(ℓ, y)` on `[0, T]`. -/
theorem mark_upper (hc : 0 < c) {ℓ : ℝ} (hℓ : 2 / c + a ≤ ℓ) (hy0 : v 0 = y) :
    ∀ t ∈ Icc (0 : ℝ) T, v t.toNNReal - c * t ≤ max ℓ y := by
  have hcont : ContinuousOn (fun s : ℝ => v s.toNNReal - c * s) (Icc 0 T) :=
    hvc.sub (continuousOn_const.mul continuousOn_id)
  have h0 : v (Real.toNNReal 0) - c * 0 = y := by simp [hy0]
  have h := le_of_barrier' (g := fun s : ℝ => v s.toNNReal - c * s)
    (φ := fun u => 2 / (v u.toNNReal - w u.toNNReal) - c) (ℓ := ℓ) (ℓ' := max ℓ y + 1) hcont
    (hint.sub intervalIntegrable_const) (mark_int hv hint) (by linarith [le_max_left ℓ y])
    (by rw [h0]; linarith [le_max_right ℓ y]) fun s hs h1 _ => by
      obtain ⟨hg1, hg2⟩ := mark_gap htube hs
      have hR : 2 / c ≤ v s.toNNReal - w s.toNNReal := by linarith
      have hRpos : 0 < v s.toNNReal - w s.toNNReal := (by positivity : (0 : ℝ) < 2 / c).trans_le hR
      have : 2 / (v s.toNNReal - w s.toNNReal) ≤ 2 / (2 / c) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) hR
      rw [div_div_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)] at this
      linarith
  intro t ht
  have := h t ht
  rwa [h0] at this

end Mark

/-! ### The deterministic steering stage -/

section Det

variable {nL nR : ℕ} {κ : ℝ} {yL : Fin (nL + 1) → ℝ} {yR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The deterministic steering stage.** For a path from a word with left marks `≤ −1` and right marks in
`[1, M]`, whose driver stays within `1/8` of `c t` on `[0, T]` (`T < ζ`), with `0 < c ≤ 1/(ℓ₂ + 1/8)`, `ℓ₂ ≥ 1` and
`ℓ₂ ≤ c T`: every gap is at least `7/8` on `[0, T]`; at `T` the nearest right gap is at least `ℓ₂ − 1/8`, the far
right gap at most `max(2/c + 1/8, M) + 1/8`, and the nearest left gap at least `c T + 7/8`. -/
theorem steer_det (hp : IsIntegratedSLEPath κ yL yR ρL ρR w vL vR b ζ) {M ℓ₂ c : ℝ} {T : ℝ≥0}
    (hTζ : (T : ℝ≥0∞) < ζ) (hyL : ∀ i, yL i ≤ -1) (hyR : ∀ j, 1 ≤ yR j ∧ yR j ≤ M)
    (htube : ∀ s ∈ Icc (0 : ℝ) T, |w s.toNNReal - c * s| ≤ 1 / 8) (hc : 0 < c) (hℓ₂ : 1 ≤ ℓ₂)
    (hcℓ : c ≤ 1 / (ℓ₂ + 1 / 8)) (hT : ℓ₂ ≤ c * T) :
    (∀ t : ℝ≥0, t ≤ T → ∀ j, 7 / 8 ≤ vR j t - w t) ∧ (∀ t : ℝ≥0, t ≤ T → ∀ i, 7 / 8 ≤ w t - vL i t) ∧
      ℓ₂ - 1 / 8 ≤ vR 0 T - w T ∧ vR (Fin.last nR) T - w T ≤ max (2 / c + 1 / 8) M + 1 / 8 ∧
      c * T + 7 / 8 ≤ w T - vL 0 T := by
  have hf := hp.isForcePath
  have ha : (0 : ℝ) < 1 / 8 := by norm_num
  have ha4 : 4 * (1 / 8 : ℝ) < 1 := by norm_num
  have hTmem : ((T : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) T := ⟨T.coe_nonneg, le_rfl⟩
  have hTT : Real.toNNReal T = T := Real.toNNReal_coe
  -- the hypotheses of the mark lemmas for the right mark `j`
  have hv : ∀ j, ∀ t : ℝ, t ∈ Icc (0 : ℝ) T →
      vR j t.toNNReal = yR j + ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal) := fun j t ht => by
    have htζ := Sec2.toNNReal_lt_of_mem_Icc hTζ ht
    rw [hf.vR_eq htζ j, Real.coe_toNNReal _ ht.1]
  have hvc : ∀ j, ContinuousOn (fun s : ℝ => vR j s.toNNReal) (Icc 0 T) := fun j =>
    (hf.continuousOn_vR j).comp continuous_real_toNNReal.continuousOn (Clock.mapsTo_toNNReal hTζ)
  have hint : ∀ j, IntervalIntegrable (fun s : ℝ => 2 / (vR j s.toNNReal - w s.toNNReal)) volume 0 T :=
    fun j => hf.intervalIntegrable_forceR hTζ j
  have hy0 : ∀ j, vR j 0 = yR j := fun j => hf.vR_zero j
  have hc1 : c ≤ 2 / (1 + 1 / 8) - c := by
    have h1 : 1 / (ℓ₂ + 1 / 8) ≤ 1 / (1 + 1 / 8) := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : 2 / (1 + 1 / 8 : ℝ) = 2 * (1 / (1 + 1 / 8)) := by ring
    linarith
  have hlow : ∀ j, ∀ t : ℝ≥0, t ≤ T → 7 / 8 ≤ vR j t - w t := by
    intro j t htT
    have htm : ((t : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.coe_nonneg, by exact_mod_cast htT⟩
    have h1 := mark_lower (hv j) (hvc j) (hint j) htube ha ha4 (hyR j).1 le_rfl hc.le hc1 (hy0 j) _ htm
    have h2 := (mark_gap (v := vR j) htube htm).1
    rw [Real.toNNReal_coe] at h1 h2
    have : min 1 (yR j + c * t) = 1 := min_eq_left (by nlinarith [(hyR j).1, t.coe_nonneg])
    rw [this] at h1
    linarith
  refine ⟨fun t ht j => hlow j t ht, fun t htT i => ?_, ?_, ?_, ?_⟩
  · have htζ : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast htT) hTζ
    have h1 := hf.vL_le_xL htζ i
    have htm : ((t : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.coe_nonneg, by exact_mod_cast htT⟩
    have h2 := abs_le.1 (htube _ htm)
    rw [Real.toNNReal_coe] at h2
    have h3 := hyL i
    have : 0 ≤ c * t := mul_nonneg hc.le t.coe_nonneg
    linarith
  · have hrc : c ≤ 2 / (ℓ₂ + 1 / 8) - c := by
      have : 2 / (ℓ₂ + 1 / 8) = 2 * (1 / (ℓ₂ + 1 / 8)) := by ring
      linarith
    have h1 := mark_lower (hv 0) (hvc 0) (hint 0) htube ha ha4 (hyR 0).1 hℓ₂ hc.le hrc (hy0 0) _ hTmem
    have h2 := (mark_gap (v := vR 0) htube hTmem).1
    rw [hTT] at h1 h2
    have : min ℓ₂ (yR 0 + c * T) = ℓ₂ := min_eq_left (by linarith [(hyR 0).1])
    rw [this] at h1
    linarith
  · have h1 := mark_upper (hv (Fin.last nR)) (hvc _) (hint _) htube hc le_rfl (hy0 _) _ hTmem
    have h2 := (mark_gap (v := vR (Fin.last nR)) htube hTmem).2
    rw [hTT] at h1 h2
    have : max (2 / c + 1 / 8) (yR (Fin.last nR)) ≤ max (2 / c + 1 / 8) M :=
      max_le_max le_rfl (hyR _).2
    linarith
  · have h1 := hf.vL_le_xL hTζ 0
    have h2 := abs_le.1 (htube _ hTmem)
    rw [hTT] at h2
    have h3 := hyL 0
    linarith

end Det

end TrialsHi3

end Sec7

end InteractingSLE
