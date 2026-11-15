/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath

/-!
# Integrated `SLE_κ(ρ)` paths before a time, and changes of the weights of separated marks

Packet PROVE-SEC2-GIR2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md` L486–L490):
the Girsanov steps "adding" and "removing" force points are both a change of the weights of marks
that stay away from the driver. This file holds the deterministic (pathwise) part.

* `Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ`: every condition of Definition 2.1 (the frozen
  `IsIntegratedSLEPath`) at times `t < τ`, without the two maximality clauses (a local solution of
  the integrated equations, as produced by one stage of the local construction);
* `IsIntegratedSLEPath.isSLEPathUpTo`: an integrated path is such a path before every `τ ≤ ζ`;
  `IsSLEPathUpTo.mono`: restriction to an earlier time;
* `IsSLEPathUpTo.changeWeights`: if the weights change only on marks that do not meet the driver
  before `τ`, and the new driving path `b'` absorbs the change of drift
  (`√a b' = √a b + ∑ ∫ (ρ − ρ')/(w − v)`), the path is a local path of the new force word.
  Adding marks is the case `ρ = 0` on the added marks, removing them the case `ρ' = 0`;
* `IsSLEPathUpTo.le_of_vR_le` / `le_of_vL_le`: two marks on the same side solving the force-point
  equation keep their order (the source: "the side ordering is preserved").

Time integrals are interval integrals over `ℝ` of `s ↦ f s.toNNReal`, as in `IsIntegratedSLEPath`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- **An integrated `SLE_a(ρ)` path before the time `τ`**: every condition of Definition 2.1 (the
frozen `IsIntegratedSLEPath`, Specification p. 20) at the times `t < τ`, without the two maximality
clauses `threshold_of_eq_zero`, `threshold_of_tendsto` (so `τ` need not be the continuation
threshold). The fields are the frozen conjuncts in their order. -/
structure IsSLEPathUpTo (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop where
  w_zero : w 0 = 0
  vL_zero : ∀ i, vL i 0 = xL i
  vR_zero : ∀ i, vR i 0 = xR i
  continuousOn_w : ContinuousOn w {t | (t : ℝ≥0∞) < τ}
  continuousOn_vL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < τ}
  continuousOn_vR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < τ}
  antitone_vL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → Antitone fun i => vL i t
  vL_le_w : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i, vL i t ≤ w t
  w_le_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i, w t ≤ vR i t
  monotone_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → Monotone fun i => vR i t
  integrable_gapL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t
  integrable_gapR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR i s.toNNReal)⁻¹) volume 0 t
  w_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    w t = Real.sqrt a * b t
      + (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal))
  vL_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i,
    vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal)
  vR_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i,
    vR i t = xR i + ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal)
  volume_collisionL : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = vL i s.toNNReal} = 0
  volume_collisionR : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = vR i s.toNNReal} = 0
  not_threshold : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
    ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun i => vR i t)

end Sec2

open Sec2

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ τ : ℝ≥0∞}

/-- An integrated path of Definition 2.1 is a local path before every time `τ ≤ ζ`. -/
theorem IsIntegratedSLEPath.isSLEPathUpTo (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hτ : τ ≤ ζ) : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, -⟩ := h
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → (t : ℝ≥0∞) < ζ := fun ht => ht.trans_le hτ
  have hsub : {t : ℝ≥0 | (t : ℝ≥0∞) < τ} ⊆ {t | (t : ℝ≥0∞) < ζ} := fun t ht => hlt ht
  refine ⟨h0, h1, h2, h3.mono hsub, fun i => (h4 i).mono hsub, fun i => (h5 i).mono hsub,
    fun ht => h6 _ (hlt ht), fun ht => h7 _ (hlt ht), fun ht => h8 _ (hlt ht),
    fun ht => h9 _ (hlt ht), fun ht => h10 _ (hlt ht), fun ht => h11 _ (hlt ht),
    fun ht => h12 _ (hlt ht), fun ht => h13 _ (hlt ht), fun ht => h14 _ (hlt ht),
    fun i => measure_mono_null ?_ (h15 i), fun i => measure_mono_null ?_ (h16 i),
    fun ht => h17 _ (hlt ht)⟩
  · exact fun s ⟨hs0, hs, he⟩ => ⟨hs0, hs.trans_le hτ, he⟩
  · exact fun s ⟨hs0, hs, he⟩ => ⟨hs0, hs.trans_le hτ, he⟩

namespace Sec2.IsSLEPathUpTo

/-- Restriction of a local path to an earlier time. -/
theorem mono (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {τ' : ℝ≥0∞} (hτ : τ' ≤ τ) :
    IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ' := by
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ' → (t : ℝ≥0∞) < τ := fun ht => ht.trans_le hτ
  have hsub : {t : ℝ≥0 | (t : ℝ≥0∞) < τ'} ⊆ {t | (t : ℝ≥0∞) < τ} := fun t ht => hlt ht
  refine ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w.mono hsub,
    fun i => (h.continuousOn_vL i).mono hsub, fun i => (h.continuousOn_vR i).mono hsub,
    fun ht => h.antitone_vL (hlt ht), fun ht => h.vL_le_w (hlt ht), fun ht => h.w_le_vR (hlt ht),
    fun ht => h.monotone_vR (hlt ht), fun ht => h.integrable_gapL (hlt ht),
    fun ht => h.integrable_gapR (hlt ht), fun ht => h.w_eq (hlt ht), fun ht => h.vL_eq (hlt ht),
    fun ht => h.vR_eq (hlt ht), fun i => measure_mono_null ?_ (h.volume_collisionL i),
    fun i => measure_mono_null ?_ (h.volume_collisionR i), fun ht => h.not_threshold (hlt ht)⟩
  · exact fun s ⟨hs0, hs, he⟩ => ⟨hs0, hs.trans_le hτ, he⟩
  · exact fun s ⟨hs0, hs, he⟩ => ⟨hs0, hs.trans_le hτ, he⟩

end Sec2.IsSLEPathUpTo

/-! ### Changing the weights of separated marks -/

namespace Sec2

/-- `∫ c / g = c * ∫ g⁻¹` (no integrability needed). -/
theorem integral_div_eq_mul_integral_inv (c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, c / g s = c * ∫ s in (0 : ℝ)..t, (g s)⁻¹ := by
  rw [← intervalIntegral.integral_const_mul]
  rfl

/-- A sum of weighted drift integrals is linear in the weights. -/
theorem sum_integral_div_eq {n : ℕ} (ρ : Fin n → ℝ) (g : Fin n → ℝ → ℝ) (t : ℝ) :
    ∑ i, ∫ s in (0 : ℝ)..t, ρ i / g i s = ∑ i, ρ i * ∫ s in (0 : ℝ)..t, (g i s)⁻¹ :=
  Finset.sum_congr rfl fun _ _ => integral_div_eq_mul_integral_inv _ _ _

/-- The threshold condition only sees the weights of the marks that meet the driver. -/
theorem thresholdCondition_congr {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ} {w₀ : ℝ}
    {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ} (hL : ∀ i, vL₀ i = w₀ → ρL' i = ρL i)
    (hR : ∀ i, vR₀ i = w₀ → ρR' i = ρR i) :
    ForceWord.ThresholdCondition ρL' ρR' w₀ vL₀ vR₀ ↔
      ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  unfold ForceWord.ThresholdCondition
  rw [Finset.sum_congr rfl fun i hi => hL i (Finset.mem_filter.1 hi).2,
    Finset.sum_congr rfl fun i hi => hR i (Finset.mem_filter.1 hi).2]

end Sec2

namespace Sec2.IsSLEPathUpTo

/-- **Changing the weights of separated marks** (pathwise part of the Girsanov steps, Specification
L486–L488). Let `(w, v, b)` be a local path of the force word with weights `(ρL; ρR)` before `τ`,
and let `(ρL'; ρR')` be new weights that differ from the old ones only on marks that do not meet the
driver before `τ`. If the new driving path `b'` satisfies
`√a b' = √a b + ∑ ∫ (ρL − ρL')/(w − vL) + ∑ ∫ (ρR − ρR')/(w − vR)` before `τ`, then `(w, v, b')`
is a local path of the force word with weights `(ρL'; ρR')` before `τ`. -/
theorem changeWeights (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) (ρL' : Fin nL → ℝ)
    (ρR' : Fin nR → ℝ) {b' : ℝ≥0 → ℝ}
    (hsepL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i, ρL' i ≠ ρL i → vL i t ≠ w t)
    (hsepR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i, ρR' i ≠ ρR i → vR i t ≠ w t)
    (hb : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      Real.sqrt a * b' t = Real.sqrt a * b t
        + (∑ i, ∫ s in (0 : ℝ)..t, (ρL i - ρL' i) / (w s.toNNReal - vL i s.toNNReal))
        + (∑ i, ∫ s in (0 : ℝ)..t, (ρR i - ρR' i) / (w s.toNNReal - vR i s.toNNReal))) :
    IsSLEPathUpTo a xL xR ρL' ρR' w vL vR b' τ := by
  refine ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w, h.continuousOn_vL,
    h.continuousOn_vR, h.antitone_vL, h.vL_le_w, h.w_le_vR, h.monotone_vR, h.integrable_gapL,
    h.integrable_gapR, fun {t} ht => ?_, h.vL_eq, h.vR_eq, h.volume_collisionL,
    h.volume_collisionR, fun {t} ht => ?_⟩
  · have hw := h.w_eq ht
    have hb' := hb ht
    simp only [sum_integral_div_eq] at hw hb' ⊢
    simp only [sub_mul, Finset.sum_sub_distrib] at hb'
    linarith
  · rw [thresholdCondition_congr (ρL := ρL) (ρR := ρR)]
    · exact h.not_threshold ht
    · intro i hi
      by_contra hne
      exact hsepL ht i hne hi
    · intro i hi
      by_contra hne
      exact hsepR ht i hne hi

end Sec2.IsSLEPathUpTo

/-! ### Two marks on the same side keep their order -/

namespace Sec2

/-- A continuous function with `D 0 ≥ 0` whose increments are integrals of a density that is
nonnegative wherever `D < 0` stays nonnegative. -/
theorem nonneg_of_integral_eq {D φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hD : ContinuousOn D (Icc 0 T))
    (hD0 : 0 ≤ D 0) (hφ : IntervalIntegrable φ volume 0 T)
    (hinc : ∀ s ∈ Icc (0 : ℝ) T, D s = D 0 + ∫ r in (0 : ℝ)..s, φ r)
    (hpos : ∀ᵐ r ∂volume, r ∈ Icc (0 : ℝ) T → D r < 0 → 0 ≤ φ r) : 0 ≤ D T := by
  by_contra hneg0
  have hneg : D T < 0 := lt_of_not_ge hneg0
  set S : Set ℝ := Icc 0 T ∩ D ⁻¹' Ici 0 with hS
  have hSc : IsClosed S := hD.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hT⟩, hD0⟩
  have hSb : BddAbove S := ⟨T, fun s hs => hs.1.2⟩
  set t₁ := sSup S with ht₁
  have ht₁S : t₁ ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSb
  have ht₁T : t₁ < T := by
    refine lt_of_le_of_ne ht₁S.1.2 fun h => ?_
    have := ht₁S.2
    rw [h] at this
    exact (not_le.2 hneg) this
  have hneg' : ∀ r ∈ Ioc t₁ T, D r < 0 := by
    intro r hr
    by_contra hr0
    have hr' : 0 ≤ D r := le_of_not_gt hr0
    have hrS : r ∈ S := ⟨⟨(ht₁S.1.1).trans hr.1.le, hr.2⟩, hr'⟩
    exact (not_le.2 hr.1) (le_csSup hSb hrS)
  have hφ₁ : IntervalIntegrable φ volume 0 t₁ :=
    hφ.mono_set (by rw [uIcc_of_le ht₁S.1.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht₁T.le)
  have hdiff : D T - D t₁ = ∫ r in t₁..T, φ r := by
    rw [hinc T ⟨hT, le_rfl⟩, hinc t₁ ht₁S.1, ← intervalIntegral.integral_interval_sub_left hφ hφ₁]
    ring
  have hint : 0 ≤ ∫ r in t₁..T, φ r := by
    rw [intervalIntegral.integral_of_le ht₁T.le]
    refine setIntegral_nonneg_of_ae_restrict ?_
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hpos] with r hr hrI
    exact hr ⟨(ht₁S.1.1).trans hrI.1.le, hrI.2⟩ (hneg' r hrI)
  have := ht₁S.2
  simp only [mem_preimage, mem_Ici] at this
  linarith

/-- A path continuous before `τ` is continuous on `[0, t]` in real time, for `t < τ`. -/
theorem continuousOn_toNNReal {f : ℝ≥0 → ℝ} (hf : ContinuousOn f {s | (s : ℝ≥0∞) < τ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : ContinuousOn (fun r : ℝ => f r.toNNReal) (Icc 0 t) := by
  refine hf.comp continuous_real_toNNReal.continuousOn fun r hr => ?_
  show ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < τ
  refine lt_of_le_of_lt ?_ ht
  exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2

/-- **Two marks on the right of the driver keep their order.** If `u` and `v` solve the force-point
equations `u = y + ∫ 2/(u − w)`, `v = x + ∫ 2/(v − w)` before `τ`, stay at or right of `w`, and
`u` meets `w` only on a Lebesgue-null set of times, then `x ≤ y` gives `v ≤ u` before `τ`
(only `w ≤ u` is needed). -/
theorem le_of_forceEq_right {w u v : ℝ≥0 → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (huc : ContinuousOn u {s | (s : ℝ≥0∞) < τ})
    (hvc : ContinuousOn v {s | (s : ℝ≥0∞) < τ})
    (hueq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      u t = y + ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal))
    (hveq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (huint : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      IntervalIntegrable (fun s : ℝ => 2 / (u s.toNNReal - w s.toNNReal)) volume 0 t)
    (hvint : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 t)
    (hwu : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → w t ≤ u t)
    (hcoll : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = u s.toNNReal} = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : v t ≤ u t := by
  have hlt : ∀ {r : ℝ}, r ∈ Icc (0 : ℝ) t → (r.toNNReal : ℝ≥0∞) < τ := fun hr =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) ht
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < τ := lt_of_le_of_lt (by simp) ht
  have hu0 : u 0 = y := by rw [hueq h0]; simp
  have hv0 : v 0 = x := by rw [hveq h0]; simp
  have key := nonneg_of_integral_eq (D := fun r : ℝ => u r.toNNReal - v r.toNNReal)
    (φ := fun r : ℝ => 2 / (u r.toNNReal - w r.toNNReal) - 2 / (v r.toNNReal - w r.toNNReal))
    (T := t) t.coe_nonneg ((continuousOn_toNNReal huc ht).sub (continuousOn_toNNReal hvc ht))
    (by simp only [Real.toNNReal_zero, hu0, hv0]; linarith) ((huint ht).sub (hvint ht)) ?_ ?_
  · simpa using key
  · intro s hs
    have hsl := hlt hs
    simp only [Real.toNNReal_zero, hu0, hv0]
    have hs' : s = (s.toNNReal : ℝ) := (Real.coe_toNNReal s hs.1).symm
    have hsub : uIcc (0 : ℝ) s ⊆ uIcc 0 t := by
      rw [uIcc_of_le hs.1, uIcc_of_le t.coe_nonneg]; exact Icc_subset_Icc le_rfl hs.2
    rw [intervalIntegral.integral_sub ((huint ht).mono_set hsub) ((hvint ht).mono_set hsub),
      hueq hsl, hveq hsl, ← hs']
    ring
  · have hnull : ∀ᵐ r : ℝ ∂volume, ¬ (0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < τ ∧
        w r.toNNReal = u r.toNNReal) := measure_eq_zero_iff_ae_notMem.1 hcoll
    filter_upwards [hnull] with r hr hrI hD
    have hrl := hlt hrI
    have hne : w r.toNNReal ≠ u r.toNNReal := fun he => hr ⟨hrI.1, hrl, he⟩
    have hpos : 0 < u r.toNNReal - w r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (hwu hrl) hne)
    have hle : u r.toNNReal - w r.toNNReal ≤ v r.toNNReal - w r.toNNReal := by
      have hD' : u r.toNNReal - v r.toNNReal < 0 := hD
      linarith
    simp only [sub_nonneg]
    exact div_le_div_of_nonneg_left (by norm_num) hpos hle

/-- **Two marks on the left of the driver keep their order.** If `u` and `v` solve the force-point
equations before `τ`, stay at or left of `w`, and `v` meets `w` only on a Lebesgue-null set of
times, then `x ≤ y` gives `v ≤ u` before `τ` (only `v ≤ w` is needed). -/
theorem le_of_forceEq_left {w u v : ℝ≥0 → ℝ} {x y : ℝ} (hxy : x ≤ y)
    (huc : ContinuousOn u {s | (s : ℝ≥0∞) < τ})
    (hvc : ContinuousOn v {s | (s : ℝ≥0∞) < τ})
    (hueq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      u t = y + ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal))
    (hveq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (huint : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      IntervalIntegrable (fun s : ℝ => 2 / (u s.toNNReal - w s.toNNReal)) volume 0 t)
    (hvint : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ →
      IntervalIntegrable (fun s : ℝ => 2 / (v s.toNNReal - w s.toNNReal)) volume 0 t)
    (hvw : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → v t ≤ w t)
    (hcoll : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = v s.toNNReal} = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) : v t ≤ u t := by
  have hlt : ∀ {r : ℝ}, r ∈ Icc (0 : ℝ) t → (r.toNNReal : ℝ≥0∞) < τ := fun hr =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hr.2) ht
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < τ := lt_of_le_of_lt (by simp) ht
  have hu0 : u 0 = y := by rw [hueq h0]; simp
  have hv0 : v 0 = x := by rw [hveq h0]; simp
  have key := nonneg_of_integral_eq (D := fun r : ℝ => u r.toNNReal - v r.toNNReal)
    (φ := fun r : ℝ => 2 / (u r.toNNReal - w r.toNNReal) - 2 / (v r.toNNReal - w r.toNNReal))
    (T := t) t.coe_nonneg ((continuousOn_toNNReal huc ht).sub (continuousOn_toNNReal hvc ht))
    (by simp only [Real.toNNReal_zero, hu0, hv0]; linarith) ((huint ht).sub (hvint ht)) ?_ ?_
  · simpa using key
  · intro s hs
    have hsl := hlt hs
    simp only [Real.toNNReal_zero, hu0, hv0]
    have hs' : s = (s.toNNReal : ℝ) := (Real.coe_toNNReal s hs.1).symm
    have hsub : uIcc (0 : ℝ) s ⊆ uIcc 0 t := by
      rw [uIcc_of_le hs.1, uIcc_of_le t.coe_nonneg]; exact Icc_subset_Icc le_rfl hs.2
    rw [intervalIntegral.integral_sub ((huint ht).mono_set hsub) ((hvint ht).mono_set hsub),
      hueq hsl, hveq hsl, ← hs']
    ring
  · have hnull : ∀ᵐ r : ℝ ∂volume, ¬ (0 ≤ r ∧ (r.toNNReal : ℝ≥0∞) < τ ∧
        w r.toNNReal = v r.toNNReal) := measure_eq_zero_iff_ae_notMem.1 hcoll
    filter_upwards [hnull] with r hr hrI hD
    have hrl := hlt hrI
    have hne : w r.toNNReal ≠ v r.toNNReal := fun he => hr ⟨hrI.1, hrl, he⟩
    have hpos : 0 < w r.toNNReal - v r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (hvw hrl) (Ne.symm hne))
    have hle : w r.toNNReal - v r.toNNReal ≤ w r.toNNReal - u r.toNNReal := by
      have hD' : u r.toNNReal - v r.toNNReal < 0 := hD
      linarith
    have e1 : 2 / (u r.toNNReal - w r.toNNReal) = -(2 / (w r.toNNReal - u r.toNNReal)) := by
      rw [← neg_sub, div_neg]
    have e2 : 2 / (v r.toNNReal - w r.toNNReal) = -(2 / (w r.toNNReal - v r.toNNReal)) := by
      rw [← neg_sub, div_neg]
    rw [e1, e2, sub_nonneg, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by norm_num) hpos hle

end Sec2

end InteractingSLE
