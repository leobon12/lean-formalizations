/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Zhan's A.1.6, the stochastic part III: localization and the passage to time zero

Packet PROVE-ZHAN-GT4-A19. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L489–L500, R38): "At positive own time, differentiating (D13)–(D15) by Itô and the force ODE is
the same cancelled calculation leading to (D8). The identity extends to time zero by bounded convergence on a protected
rectangle."

The martingale identity of the seeded density is proved after a positive time `ε` and up to a localization `τ_k`
(the force gaps stay `≥ 1/k`, so the drift and the field are bounded: `DualSeedDrift`). Two bounded-convergence steps
remove the restrictions, for a bounded process `M`:

* **`integral_mul_sub_eq_zero_of_tendsto`** (localization): if bounded processes `M_k` converge pointwise to `M` and
  each satisfies `E[ξ (M_k(t) − M_k(s))] = 0`, so does `M`;
* **`integral_mul_sub_eq_zero_of_pos`** (time zero): if `M` is right-continuous at `0` and the identity holds for all
  `0 < s ≤ t` (with `ξ` bounded and `𝓕_s`-measurable), it holds for `s = 0` too (`𝓕_0 ⊆ 𝓕_ε`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

section Ext

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- A bounded measurable multiplier times a bounded a.e.-strongly measurable function is integrable. -/
theorem integrable_mul_of_abs_le {ξ f : Ω → ℝ} {C : ℝ} (hξ : Measurable ξ) (hξb : ∀ ω, |ξ ω| ≤ 1)
    (hf : AEStronglyMeasurable f P) (hfb : ∀ ω, |f ω| ≤ C) : Integrable (fun ω => ξ ω * f ω) P :=
  (integrable_const C).mono' (hξ.aestronglyMeasurable.mul hf) (Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_mul]
    calc |ξ ω| * |f ω| ≤ 1 * C := mul_le_mul (hξb ω) (hfb ω) (abs_nonneg _) zero_le_one
      _ = C := one_mul C)

/-- **Localization by bounded convergence**: if the bounded processes `M_k` converge pointwise to `M` at the times
`s, t` and `E[ξ (M_k(t) − M_k(s))] = 0` for every `k`, then `E[ξ (M(t) − M(s))] = 0`. -/
theorem integral_mul_sub_eq_zero_of_tendsto {ι : Type*} {M : ι → Ω → ℝ} {Mk : ℕ → ι → Ω → ℝ} {C : ℝ} {s t : ι}
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) (hkm : ∀ k r, AEStronglyMeasurable (Mk k r) P)
    (hkb : ∀ k r ω, |Mk k r ω| ≤ C) (hlim : ∀ r ω, Tendsto (fun k => Mk k r ω) atTop (𝓝 (M r ω)))
    (hk : ∀ k, ∫ ω, ξ ω * (Mk k t ω - Mk k s ω) ∂P = 0) :
    ∫ ω, ξ ω * (M t ω - M s ω) ∂P = 0 := by
  have hT : Tendsto (fun k => ∫ ω, ξ ω * (Mk k t ω - Mk k s ω) ∂P) atTop
      (𝓝 (∫ ω, ξ ω * (M t ω - M s ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 2 * C) (fun k => ?_) (integrable_const _)
      (fun k => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · exact hξ.aestronglyMeasurable.mul ((hkm k t).sub (hkm k s))
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Mk k t ω - Mk k s ω| ≤ 2 * C := by
        have := abs_sub (Mk k t ω) (Mk k s ω)
        linarith [hkb k t ω, hkb k s ω]
      calc |ξ ω| * |Mk k t ω - Mk k s ω| ≤ 1 * (2 * C) :=
            mul_le_mul (hξb ω) h1 (abs_nonneg _) zero_le_one
        _ = 2 * C := one_mul _
    · exact tendsto_const_nhds.mul ((hlim t ω).sub (hlim s ω))
  simp only [hk] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

/-- **Passage to time zero by bounded convergence**: let `M` be bounded, each `M r` a.e.-strongly measurable, and
right-continuous at `0` pathwise. If `E[ξ (M(t) − M(s))] = 0` for all `0 < s ≤ t` and bounded `𝓕_s`-measurable `ξ`,
then also for `s = 0`. -/
theorem integral_mul_sub_eq_zero_of_pos {𝓕 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hm : ∀ r, AEStronglyMeasurable (M r) P) (hb : ∀ r ω, |M r ω| ≤ C)
    (hc : ∀ ω, Tendsto (fun r => M r ω) (𝓝[>] 0) (𝓝 (M 0 ω)))
    (hpos : ∀ s t : ℝ≥0, 0 < s → s ≤ t → ∀ ξ : Ω → ℝ, Measurable[𝓕 s] ξ → (∀ ω, |ξ ω| ≤ 1) →
      ∫ ω, ξ ω * (M t ω - M s ω) ∂P = 0)
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (M t ω - M s ω) ∂P = 0 := by
  rcases eq_or_lt_of_le (zero_le (a := s)) with hs | hs
  swap
  · exact hpos s t hs hst ξ hξ hξb
  subst hs
  rcases eq_or_lt_of_le hst with ht | ht
  · subst ht; simp
  have hξm : Measurable ξ := hξ.mono (𝓕.le 0) le_rfl
  -- the times `ε_k = t/(k+2) ↓ 0`
  set ε : ℕ → ℝ≥0 := fun k => t / (k + 2) with hε
  have hεpos : ∀ k, 0 < ε k := fun k => div_pos ht (by positivity)
  have hεle : ∀ k, ε k ≤ t := fun k => by
    rw [hε]
    refine div_le_self (le_of_lt ht) ?_
    have : (0 : ℝ≥0) ≤ k := zero_le (a := (k : ℝ≥0))
    calc (1 : ℝ≥0) ≤ 2 := by norm_num
      _ ≤ (k : ℝ≥0) + 2 := le_add_of_nonneg_left this
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    refine NNReal.tendsto_coe.1 ?_
    have h := (tendsto_const_div_atTop_nhds_zero_nat (t : ℝ)).comp (tendsto_add_atTop_nat 2)
    refine (h.congr fun k => ?_)
    simp only [Function.comp_apply, hε, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, Nat.cast_add,
      Nat.cast_ofNat, NNReal.coe_ofNat]
  have hεlim : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hε0, Eventually.of_forall hεpos⟩
  -- each identity on `[ε_k, t]`
  have hk : ∀ k, ∫ ω, ξ ω * (M t ω - M (ε k) ω) ∂P = 0 := fun k =>
    hpos (ε k) t (hεpos k) (hεle k) ξ (hξ.mono (𝓕.mono (zero_le (a := ε k))) le_rfl) hξb
  -- the identity at `0` is the limit of `E[ξ (M(ε_k) − M(0))]`
  have hT : Tendsto (fun k => ∫ ω, ξ ω * (M (ε k) ω - M 0 ω) ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (F := fun k ω => ξ ω * (M (ε k) ω - M 0 ω))
      (f := fun _ => (0 : ℝ)) (fun _ => 2 * C) (fun k => hξm.aestronglyMeasurable.mul ((hm _).sub (hm 0)))
      (integrable_const _) (fun k => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · simpa using this
    · rw [Real.norm_eq_abs, abs_mul]
      have h1 : |M (ε k) ω - M 0 ω| ≤ 2 * C := by
        have := abs_sub (M (ε k) ω) (M 0 ω)
        linarith [hb (ε k) ω, hb 0 ω]
      calc |ξ ω| * |M (ε k) ω - M 0 ω| ≤ 1 * (2 * C) := mul_le_mul (hξb ω) h1 (abs_nonneg _) zero_le_one
        _ = 2 * C := one_mul _
    · have h1 : Tendsto (fun k => M (ε k) ω - M 0 ω) atTop (𝓝 0) := by
        have := ((hc ω).comp hεlim).sub (tendsto_const_nhds (x := M 0 ω))
        simpa using this
      simpa using (tendsto_const_nhds (x := ξ ω)).mul h1
  have hsplit : ∀ k, ∫ ω, ξ ω * (M t ω - M 0 ω) ∂P = ∫ ω, ξ ω * (M (ε k) ω - M 0 ω) ∂P := fun k => by
    have hi : ∀ a b : ℝ≥0, Integrable (fun ω => ξ ω * (M a ω - M b ω)) P := fun a b =>
      integrable_mul_of_abs_le hξm hξb ((hm a).sub (hm b)) (C := 2 * C) fun ω => by
        have := abs_sub (M a ω) (M b ω)
        linarith [hb a ω, hb b ω]
    have e : (fun ω => ξ ω * (M t ω - M 0 ω)) =
        fun ω => ξ ω * (M t ω - M (ε k) ω) + ξ ω * (M (ε k) ω - M 0 ω) := by
      funext ω; ring
    rw [e, integral_add (hi t (ε k)) (hi (ε k) 0), hk k, zero_add]
  have hconst : Tendsto (fun k => ∫ ω, ξ ω * (M (ε k) ω - M 0 ω) ∂P) atTop
      (𝓝 (∫ ω, ξ ω * (M t ω - M 0 ω) ∂P)) := by
    simp only [← hsplit]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst hT

end Ext

end InteractingSLE.ZhanGT4
