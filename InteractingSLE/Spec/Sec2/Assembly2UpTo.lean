/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyLocal
import InteractingSLE.Spec.Sec2.AssemblyPathwise
import InteractingSLE.Spec.Sec2.PatchingNonaccum

/-!
# Theorem 2.2 assembly: local pathwise uniqueness for local solutions

Packet PROVE-SEC2-PATCH2. PROVE-SEC2-PATCH's local uniqueness (`Sec2.Assembly.LocalPair`,
`AssemblyLocal.lean`) is stated for solutions with a maximal lifetime (`Sec2.IsForcePath`), but its
proofs only use the conditions of Definition 2.1 *before* the lifetime. This file restates it, with
the same proofs, for **local solutions** `Sec2.IsSLEPathUpTo` (PROVE-SEC2-GIR2: every condition of
Definition 2.1 before a time `τ`, no maximality), which is what a stage of the construction of
Theorem 2.2 is (the solution before the first time a further mark comes close to the driver):

* `Sec2.IsSLEPathUpTo.vL_sub`, `vR_sub`, `reflect`: the API the proofs use;
* `Sec2.UpTo.vR_eq_of_eq`: coincident right marks stay together;
* `Sec2.UpTo.LocalPair.eq_of_rightGroup`, `eq_of_leftGroup`: two local solutions driven by the
  same path, equal at `t₀`, agree on `[t₀, t₁]` when one contact group of total weight `> −2`
  sits at the driver at `t₀` and every other mark stays at distance `≥ ε` from the driver.

The body below (from "Coincident marks stay together" on) is `AssemblyLocal.lean` L205–L882 with
`IsForcePath xL xR ρL ρR w vL vR ζ` replaced by `IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

theorem vL_sub (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : (t : ℝ≥0∞) < τ) (i : Fin nL) :
    vL i t - vL i s = ∫ r in (s : ℝ)..t, 2 / (vL i r.toNNReal - w r.toNNReal) := by
  have hs : (s : ℝ≥0∞) < τ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  rw [h.vL_eq ht i, h.vL_eq hs i, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_forceL ht i)
      (h.intervalIntegrable_forceL hs i)]

theorem vR_sub (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {s t : ℝ≥0} (hst : s ≤ t)
    (ht : (t : ℝ≥0∞) < τ) (i : Fin nR) :
    vR i t - vR i s = ∫ r in (s : ℝ)..t, 2 / (vR i r.toNNReal - w r.toNNReal) := by
  have hs : (s : ℝ≥0∞) < τ := lt_of_le_of_lt (by exact_mod_cast hst) ht
  rw [h.vR_eq ht i, h.vR_eq hs i, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (h.intervalIntegrable_forceR ht i)
      (h.intervalIntegrable_forceR hs i)]

theorem intervalIntegrable_driftL (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ) (i : Fin nL) :
    IntervalIntegrable (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := by
  simpa only [div_eq_mul_inv] using (h.integrable_gapL ht i).const_mul (ρL i)

theorem intervalIntegrable_driftR (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ) (i : Fin nR) :
    IntervalIntegrable (fun s : ℝ => ρR i / (w s.toNNReal - vR i s.toNNReal)) volume 0 t := by
  simpa only [div_eq_mul_inv] using (h.integrable_gapR ht i).const_mul (ρR i)

theorem intervalIntegrable_sum_driftL (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ) :
    IntervalIntegrable (fun s : ℝ => ∑ i, ρL i / (w s.toNNReal - vL i s.toNNReal)) volume 0 t := by
  have := IntervalIntegrable.sum Finset.univ fun i _ => h.intervalIntegrable_driftL ht i
  rwa [Finset.sum_fn] at this

theorem intervalIntegrable_sum_driftR (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < τ) :
    IntervalIntegrable (fun s : ℝ => ∑ i, ρR i / (w s.toNNReal - vR i s.toNNReal)) volume 0 t := by
  have := IntervalIntegrable.sum Finset.univ fun i _ => h.intervalIntegrable_driftR ht i
  rwa [Finset.sum_fn] at this

theorem vL_le_xL (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ)
    (i : Fin nL) : vL i t ≤ xL i := by
  rw [← h.vL_zero i]; exact h.vL_le_of_le (zero_le : (0 : ℝ≥0) ≤ t) ht i

theorem xR_le_vR (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ)
    (i : Fin nR) : xR i ≤ vR i t := by
  rw [← h.vR_zero i]; exact h.le_vR_of_le (zero_le : (0 : ℝ≥0) ≤ t) ht i

/-- The driving equation of a local solution, as `Sec2.DriverEq`. -/
theorem driverEq (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) : DriverEq a ρL ρR w vL vR b τ :=
  fun _ ht => h.w_eq ht

/-- **Reflection** `x ↦ −x` (sides exchanged) of a local solution. -/
theorem reflect (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) :
    IsSLEPathUpTo a (-xR) (-xL) ρR ρL (-w) (fun i => -vR i) (fun i => -vL i) (-b) τ where
  w_zero := by simp [h.w_zero]
  vL_zero i := by simp [h.vR_zero i]
  vR_zero i := by simp [h.vL_zero i]
  continuousOn_w := h.continuousOn_w.neg
  continuousOn_vL i := (h.continuousOn_vR i).neg
  continuousOn_vR i := (h.continuousOn_vL i).neg
  antitone_vL ht _ _ hij := neg_le_neg (h.monotone_vR ht hij)
  vL_le_w ht i := neg_le_neg (h.w_le_vR ht i)
  w_le_vR ht i := neg_le_neg (h.vL_le_w ht i)
  monotone_vR ht _ _ hij := neg_le_neg (h.antitone_vL ht hij)
  integrable_gapL {t} ht i := by
    have e : (fun s : ℝ => ((-w) s.toNNReal - (fun i => -vR i) i s.toNNReal)⁻¹) =
        fun s => -(w s.toNNReal - vR i s.toNNReal)⁻¹ := by
      funext s
      simp only [Pi.neg_apply]
      rw [neg_sub_neg, ← inv_neg, neg_sub]
    rw [e]
    exact (h.integrable_gapR ht i).neg
  integrable_gapR {t} ht i := by
    have e : (fun s : ℝ => ((-w) s.toNNReal - (fun i => -vL i) i s.toNNReal)⁻¹) =
        fun s => -(w s.toNNReal - vL i s.toNNReal)⁻¹ := by
      funext s
      simp only [Pi.neg_apply]
      rw [neg_sub_neg, ← inv_neg, neg_sub]
    rw [e]
    exact (h.integrable_gapL ht i).neg
  w_eq {t} ht := h.driverEq.reflect t ht
  vL_eq {t} ht i := by
    have e : (fun s : ℝ => 2 / ((fun i => -vR i) i s.toNNReal - (-w) s.toNNReal)) =
        fun s => -(2 / (vR i s.toNNReal - w s.toNNReal)) := by
      funext s
      simp only [Pi.neg_apply]
      exact div_neg_sub_neg _ _ _
    simp only [Pi.neg_apply] at e ⊢
    rw [e, intervalIntegral.integral_neg, h.vR_eq ht i]
    ring
  vR_eq {t} ht i := by
    have e : (fun s : ℝ => 2 / ((fun i => -vL i) i s.toNNReal - (-w) s.toNNReal)) =
        fun s => -(2 / (vL i s.toNNReal - w s.toNNReal)) := by
      funext s
      simp only [Pi.neg_apply]
      exact div_neg_sub_neg _ _ _
    simp only [Pi.neg_apply] at e ⊢
    rw [e, intervalIntegral.integral_neg, h.vL_eq ht i]
    ring
  volume_collisionL i := by simpa [neg_inj] using h.volume_collisionR i
  volume_collisionR i := by simpa [neg_inj] using h.volume_collisionL i
  not_threshold {t} ht := by
    have := h.not_threshold ht
    rwa [← thresholdCondition_neg_iff] at this

end IsSLEPathUpTo

namespace UpTo

open Sec2.Assembly (eq_zero_of_le_mul_integral nonneg_of_integral_eq_Icc le_integral_of_sign
  abs_div_sub_div_le toNNReal_mem_Icc coe_toNNReal_of_mem_Icc toNNReal_lt_of_mem_Icc'
  continuousOn_real intervalIntegrable_mono_Icc)


variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}

/-! ### Coincident marks stay together -/

/-- Two right marks that coincide at `t₀` satisfy `vR j ≤ vR k` afterwards. -/
theorem vR_le_of_eq (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ) {t₀ t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < ζ) {j k : Fin nR} (hjk : vR j t₀ = vR k t₀) {t : ℝ≥0}
    (ht : t ∈ Icc t₀ t₁) : vR j t ≤ vR k t := by
  have htζ : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast ht.2) ht₁
  have key := le_integral_of_sign (D := fun r : ℝ => vR j r.toNNReal - vR k r.toNNReal)
    (φ := fun r : ℝ =>
      2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR k r.toNNReal - w r.toNNReal))
    (ψ := fun _ => 0) (t₀ := t₀) (t₁ := t) (by exact_mod_cast ht.1)
    ((continuousOn_real (h.continuousOn_vR j) htζ).sub
      (continuousOn_real (h.continuousOn_vR k) htζ))
    (by simp [hjk])
    (intervalIntegrable_mono_Icc ((h.intervalIntegrable_forceR htζ j).sub
      (h.intervalIntegrable_forceR htζ k)) ht.1 le_rfl)
    intervalIntegrable_const (fun _ _ => le_rfl) ?_ ?_
  · simpa using key
  · intro s hs
    have hsN := toNNReal_mem_Icc hs
    have hsl : (s.toNNReal : ℝ≥0∞) < ζ := toNNReal_lt_of_mem_Icc' htζ hs
    have e1 := h.vR_sub hsN.1 hsl j
    have e2 := h.vR_sub hsN.1 hsl k
    rw [coe_toNNReal_of_mem_Icc hs] at e1 e2
    have hsub : uIcc (t₀ : ℝ) s ⊆ uIcc 0 t := by
      rw [uIcc_of_le hs.1, uIcc_of_le t.coe_nonneg]
      exact Icc_subset_Icc t₀.coe_nonneg hs.2
    rw [intervalIntegral.integral_sub ((h.intervalIntegrable_forceR htζ j).mono_set hsub)
      ((h.intervalIntegrable_forceR htζ k).mono_set hsub), ← e1, ← e2, hjk]
    ring
  · have hnull := measure_eq_zero_iff_ae_notMem.1 (h.volume_collisionR k)
    filter_upwards [hnull] with r hr hrI hD
    have hr0 : 0 ≤ r := t₀.coe_nonneg.trans hrI.1
    have hrl : (r.toNNReal : ℝ≥0∞) < ζ := toNNReal_lt_of_mem_Icc' htζ hrI
    have hne : w r.toNNReal ≠ vR k r.toNNReal := fun he => hr ⟨hr0, hrl, he⟩
    have hpos : 0 < vR k r.toNNReal - w r.toNNReal :=
      sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hrl k) hne)
    have hD' : 0 < vR j r.toNNReal - vR k r.toNNReal := hD
    have hle : vR k r.toNNReal - w r.toNNReal ≤ vR j r.toNNReal - w r.toNNReal := by linarith
    have := div_le_div_of_nonneg_left (a := (2 : ℝ)) (by norm_num) hpos hle
    show 2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR k r.toNNReal - w r.toNNReal) ≤ 0
    linarith

/-- **Coincident right marks stay together**: if `vR j t₀ = vR k t₀` then `vR j = vR k` on
`[t₀, t₁]`, `t₁ < ζ`. -/
theorem vR_eq_of_eq (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ) {t₀ t₁ : ℝ≥0}
    (ht₁ : (t₁ : ℝ≥0∞) < ζ) {j k : Fin nR} (hjk : vR j t₀ = vR k t₀) {t : ℝ≥0}
    (ht : t ∈ Icc t₀ t₁) : vR j t = vR k t :=
  le_antisymm (vR_le_of_eq h ht₁ hjk ht) (vR_le_of_eq h ht₁ hjk.symm ht)

/-! ### Two solutions driven by the same path -/

/-- Two solutions of the integrated equations for the same force word and the same driving path
`b`, both alive on `[t₀, t₁]` and equal at `t₀`. -/
structure LocalPair (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (w' : ℝ≥0 → ℝ) (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ)
    (ζ ζ' : ℝ≥0∞) (t₀ t₁ : ℝ≥0) : Prop where
  path : IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ
  drv : DriverEq a ρL ρR w vL vR b ζ
  path' : IsSLEPathUpTo a xL xR ρL ρR w' vL' vR' b ζ'
  drv' : DriverEq a ρL ρR w' vL' vR' b ζ'
  le : t₀ ≤ t₁
  lt : (t₁ : ℝ≥0∞) < ζ
  lt' : (t₁ : ℝ≥0∞) < ζ'
  w₀ : w t₀ = w' t₀
  vL₀ : ∀ i, vL i t₀ = vL' i t₀
  vR₀ : ∀ j, vR j t₀ = vR' j t₀

namespace LocalPair

variable {t₀ t₁ : ℝ≥0}
  (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
include hP

theorem lt_of_mem {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) : (t : ℝ≥0∞) < ζ :=
  lt_of_le_of_lt (by exact_mod_cast ht.2) hP.lt

theorem lt'_of_mem {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) : (t : ℝ≥0∞) < ζ' :=
  lt_of_le_of_lt (by exact_mod_cast ht.2) hP.lt'

/-- The driver difference is the integral of the drift difference. -/
theorem w_sub_w' {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    w t - w' t = ∫ r in (t₀ : ℝ)..t,
      (driverDrift ρL ρR w vL vR r - driverDrift ρL ρR w' vL' vR' r) := by
  have e1 := hP.path.w_sub ht.1 (hP.lt_of_mem ht)
  have e2 := hP.path'.w_sub ht.1 (hP.lt'_of_mem ht)
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_mono_Icc (hP.path.intervalIntegrable_driverDrift (hP.lt_of_mem ht))
      ht.1 le_rfl)
    (intervalIntegrable_mono_Icc (hP.path'.intervalIntegrable_driverDrift (hP.lt'_of_mem ht))
      ht.1 le_rfl)]
  linarith [hP.w₀]

/-- A left force difference is the integral of the force-integrand difference. -/
theorem vL_sub_vL' {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) (i : Fin nL) :
    vL i t - vL' i t = ∫ r in (t₀ : ℝ)..t,
      (2 / (vL i r.toNNReal - w r.toNNReal) - 2 / (vL' i r.toNNReal - w' r.toNNReal)) := by
  have e1 := hP.path.vL_sub ht.1 (hP.lt_of_mem ht) i
  have e2 := hP.path'.vL_sub ht.1 (hP.lt'_of_mem ht) i
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_mono_Icc (hP.path.intervalIntegrable_forceL (hP.lt_of_mem ht) i)
      ht.1 le_rfl)
    (intervalIntegrable_mono_Icc (hP.path'.intervalIntegrable_forceL (hP.lt'_of_mem ht) i)
      ht.1 le_rfl)]
  linarith [hP.vL₀ i]

/-- A right force difference is the integral of the force-integrand difference. -/
theorem vR_sub_vR' {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) (j : Fin nR) :
    vR j t - vR' j t = ∫ r in (t₀ : ℝ)..t,
      (2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR' j r.toNNReal - w' r.toNNReal)) := by
  have e1 := hP.path.vR_sub ht.1 (hP.lt_of_mem ht) j
  have e2 := hP.path'.vR_sub ht.1 (hP.lt'_of_mem ht) j
  rw [intervalIntegral.integral_sub
    (intervalIntegrable_mono_Icc (hP.path.intervalIntegrable_forceR (hP.lt_of_mem ht) j)
      ht.1 le_rfl)
    (intervalIntegrable_mono_Icc (hP.path'.intervalIntegrable_forceR (hP.lt'_of_mem ht) j)
      ht.1 le_rfl)]
  linarith [hP.vR₀ j]

end LocalPair

/-! ### Separated marks and the contact group -/

/-- Drift from the left marks and from the right marks outside `A`, at real time `r`. -/
def sepDrift (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (A : Finset (Fin nR)) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  ∑ i, ρL i / (w r.toNNReal - vL i r.toNNReal) +
    ∑ j ∈ Aᶜ, ρR j / (w r.toNNReal - vR j r.toNNReal)

/-- Drift from the right marks in `A`, at real time `r`. -/
def grpDrift (ρR : Fin nR → ℝ) (A : Finset (Fin nR)) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (r : ℝ) : ℝ :=
  ∑ j ∈ A, ρR j / (w r.toNNReal - vR j r.toNNReal)

theorem driverDrift_eq_sep_add_grp (A : Finset (Fin nR)) (r : ℝ) :
    driverDrift ρL ρR w vL vR r = sepDrift ρL ρR A w vL vR r + grpDrift ρR A w vR r := by
  unfold driverDrift sepDrift grpDrift
  rw [add_assoc, Finset.sum_compl_add_sum]

theorem intervalIntegrable_sepDrift (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ) (A : Finset (Fin nR))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (sepDrift ρL ρR A w vL vR) volume 0 t := by
  have hR := IntervalIntegrable.sum Aᶜ fun j _ => h.intervalIntegrable_driftR ht j
  rw [Finset.sum_fn] at hR
  exact (h.intervalIntegrable_sum_driftL ht).add hR

/-- The total error of the separated coordinates at real time `r`. -/
def errN (A : Finset (Fin nR)) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (w' : ℝ≥0 → ℝ) (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  |w r.toNNReal - w' r.toNNReal| + ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| +
    ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal|

theorem errN_nonneg (A : Finset (Fin nR)) (r : ℝ) : 0 ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN; positivity

theorem abs_w_le_errN (A : Finset (Fin nR)) (r : ℝ) :
    |w r.toNNReal - w' r.toNNReal| ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h1 : 0 ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| := by positivity
  have h2 : 0 ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| := by positivity
  linarith

theorem abs_vL_le_errN (A : Finset (Fin nR)) (r : ℝ) (i : Fin nL) :
    |vL i r.toNNReal - vL' i r.toNNReal| ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h1 : |vL i r.toNNReal - vL' i r.toNNReal| ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| :=
    Finset.single_le_sum (f := fun i => |vL i r.toNNReal - vL' i r.toNNReal|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : 0 ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| := by positivity
  have h3 : 0 ≤ |w r.toNNReal - w' r.toNNReal| := abs_nonneg _
  linarith

theorem abs_vR_le_errN {A : Finset (Fin nR)} (r : ℝ) {j : Fin nR} (hj : j ∈ Aᶜ) :
    |vR j r.toNNReal - vR' j r.toNNReal| ≤ errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h1 : |vR j r.toNNReal - vR' j r.toNNReal| ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| :=
    Finset.single_le_sum (f := fun j => |vR j r.toNNReal - vR' j r.toNNReal|)
      (fun _ _ => abs_nonneg _) hj
  have h2 : 0 ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| := by positivity
  have h3 : 0 ≤ |w r.toNNReal - w' r.toNNReal| := abs_nonneg _
  linarith

theorem abs_add_vL_le_errN (A : Finset (Fin nR)) (r : ℝ) (i : Fin nL) :
    |w r.toNNReal - w' r.toNNReal| + |vL i r.toNNReal - vL' i r.toNNReal| ≤
      errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h3 : 0 ≤ ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| := by positivity
  have h4 : |vL i r.toNNReal - vL' i r.toNNReal| ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| :=
    Finset.single_le_sum (f := fun i => |vL i r.toNNReal - vL' i r.toNNReal|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  linarith

theorem abs_add_vR_le_errN {A : Finset (Fin nR)} (r : ℝ) {j : Fin nR} (hj : j ∈ Aᶜ) :
    |w r.toNNReal - w' r.toNNReal| + |vR j r.toNNReal - vR' j r.toNNReal| ≤
      errN A w vL vR w' vL' vR' r := by
  unfold errN
  have h3 : 0 ≤ ∑ i, |vL i r.toNNReal - vL' i r.toNNReal| := by positivity
  have h4 : |vR j r.toNNReal - vR' j r.toNNReal| ≤
      ∑ j ∈ Aᶜ, |vR j r.toNNReal - vR' j r.toNNReal| :=
    Finset.single_le_sum (f := fun j => |vR j r.toNNReal - vR' j r.toNNReal|)
      (fun _ _ => abs_nonneg _) hj
  linarith

/-- On `[t₀, t₁]` every left mark and every right mark outside `A` is at distance `≥ ε` from the
driver. -/
def Separated (A : Finset (Fin nR)) (ε : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (t₀ t₁ : ℝ≥0) : Prop :=
  ∀ s ∈ Icc t₀ t₁, (∀ i, ε ≤ w s - vL i s) ∧ ∀ j ∈ Aᶜ, ε ≤ vR j s - w s

section Lipschitz

variable {A : Finset (Fin nR)} {ε : ℝ} {t₀ t₁ : ℝ≥0}

theorem abs_sepDrift_sub_le (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {r : ℝ} (hr : r ∈ Icc (t₀ : ℝ) t₁) :
    |sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r| ≤
      (∑ i, |ρL i| + ∑ j, |ρR j|) / ε ^ 2 * errN A w vL vR w' vL' vR' r := by
  set s := r.toNNReal
  have hs := toNNReal_mem_Icc hr
  obtain ⟨hL, hR⟩ := hS s hs
  obtain ⟨hL', hR'⟩ := hS' s hs
  set E := errN A w vL vR w' vL' vR' r
  have hLi : ∀ i, |ρL i / (w s - vL i s) - ρL i / (w' s - vL' i s)| ≤ |ρL i| / ε ^ 2 * E := by
    intro i
    refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
    · exact (hL i).trans (le_abs_self _)
    · exact (hL' i).trans (le_abs_self _)
    · gcongr
      calc |w s - vL i s - (w' s - vL' i s)| = |(w s - w' s) - (vL i s - vL' i s)| := by ring_nf
        _ ≤ |w s - w' s| + |vL i s - vL' i s| := abs_sub _ _
        _ ≤ E := abs_add_vL_le_errN A r i
  have hRj : ∀ j ∈ Aᶜ, |ρR j / (w s - vR j s) - ρR j / (w' s - vR' j s)| ≤
      |ρR j| / ε ^ 2 * E := by
    intro j hj
    refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
    · rw [abs_sub_comm]; exact (hR j hj).trans (le_abs_self _)
    · rw [abs_sub_comm]; exact (hR' j hj).trans (le_abs_self _)
    · gcongr
      calc |w s - vR j s - (w' s - vR' j s)| = |(w s - w' s) - (vR j s - vR' j s)| := by ring_nf
        _ ≤ |w s - w' s| + |vR j s - vR' j s| := abs_sub _ _
        _ ≤ E := abs_add_vR_le_errN r hj
  have hE : 0 ≤ E := errN_nonneg A r
  unfold sepDrift
  calc |∑ i, ρL i / (w s - vL i s) + ∑ j ∈ Aᶜ, ρR j / (w s - vR j s) -
        (∑ i, ρL i / (w' s - vL' i s) + ∑ j ∈ Aᶜ, ρR j / (w' s - vR' j s))|
      = |∑ i, (ρL i / (w s - vL i s) - ρL i / (w' s - vL' i s)) +
          ∑ j ∈ Aᶜ, (ρR j / (w s - vR j s) - ρR j / (w' s - vR' j s))| := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring_nf
    _ ≤ ∑ i, |ρL i / (w s - vL i s) - ρL i / (w' s - vL' i s)| +
          ∑ j ∈ Aᶜ, |ρR j / (w s - vR j s) - ρR j / (w' s - vR' j s)| :=
        (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
          (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, |ρL i| / ε ^ 2 * E + ∑ j ∈ Aᶜ, |ρR j| / ε ^ 2 * E :=
        add_le_add (Finset.sum_le_sum fun i _ => hLi i) (Finset.sum_le_sum fun j hj => hRj j hj)
    _ ≤ ∑ i, |ρL i| / ε ^ 2 * E + ∑ j, |ρR j| / ε ^ 2 * E := by
        gcongr
        exact Finset.subset_univ _
    _ = (∑ i, |ρL i| + ∑ j, |ρR j|) / ε ^ 2 * E := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div, ← Finset.sum_div, ← add_mul,
          add_div]

theorem abs_forceL_sub_le (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {r : ℝ} (hr : r ∈ Icc (t₀ : ℝ) t₁) (i : Fin nL) :
    |2 / (vL i r.toNNReal - w r.toNNReal) - 2 / (vL' i r.toNNReal - w' r.toNNReal)| ≤
      2 / ε ^ 2 * errN A w vL vR w' vL' vR' r := by
  set s := r.toNNReal
  have hs := toNNReal_mem_Icc hr
  refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
  · rw [abs_sub_comm]; exact ((hS s hs).1 i).trans (le_abs_self _)
  · rw [abs_sub_comm]; exact ((hS' s hs).1 i).trans (le_abs_self _)
  · rw [abs_two]
    gcongr
    calc |vL i s - w s - (vL' i s - w' s)| = |(vL i s - vL' i s) - (w s - w' s)| := by ring_nf
      _ ≤ |vL i s - vL' i s| + |w s - w' s| := abs_sub _ _
      _ ≤ errN A w vL vR w' vL' vR' r := by
        rw [add_comm]; exact abs_add_vL_le_errN A r i

theorem abs_forceR_sub_le (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {r : ℝ} (hr : r ∈ Icc (t₀ : ℝ) t₁) {j : Fin nR}
    (hj : j ∈ Aᶜ) :
    |2 / (vR j r.toNNReal - w r.toNNReal) - 2 / (vR' j r.toNNReal - w' r.toNNReal)| ≤
      2 / ε ^ 2 * errN A w vL vR w' vL' vR' r := by
  set s := r.toNNReal
  have hs := toNNReal_mem_Icc hr
  refine (abs_div_sub_div_le hε ?_ ?_).trans ?_
  · exact ((hS s hs).2 j hj).trans (le_abs_self _)
  · exact ((hS' s hs).2 j hj).trans (le_abs_self _)
  · rw [abs_two]
    gcongr
    calc |vR j s - w s - (vR' j s - w' s)| = |(vR j s - vR' j s) - (w s - w' s)| := by ring_nf
      _ ≤ |vR j s - vR' j s| + |w s - w' s| := abs_sub _ _
      _ ≤ errN A w vL vR w' vL' vR' r := by
        rw [add_comm]; exact abs_add_vR_le_errN r hj

end Lipschitz

/-! ### The contact group -/

namespace LocalPair

variable {t₀ t₁ : ℝ≥0} (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
include hP

theorem intervalIntegrable_dSep (A : Finset (Fin nR)) {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    IntervalIntegrable
      (fun r => sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r) volume t₀ t :=
  intervalIntegrable_mono_Icc ((intervalIntegrable_sepDrift hP.path A (hP.lt_of_mem ht)).sub
    (intervalIntegrable_sepDrift hP.path' A (hP.lt'_of_mem ht))) ht.1 le_rfl

/-- **The contact group bound.** If the right marks of `A` sit at the driver at `t₀` and their
total weight is `> −2`, then the driver difference and the differences of the marks of `A` are
bounded by `C ∫ |ΔF|`, where `ΔF` is the difference of the separated drifts. -/
theorem group_bound (A : Finset (Fin nR)) (hA : ∀ j ∈ A, vR j t₀ = w t₀)
    (hρA : -2 < ∑ j ∈ A, ρR j) {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    |w t - w' t| ≤ (4 / (2 + ∑ j ∈ A, ρR j) + 1) *
        ∫ r in (t₀ : ℝ)..t, |sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r| ∧
      ∀ j ∈ A, |vR j t - vR' j t| ≤ 4 / (2 + ∑ j ∈ A, ρR j) *
        ∫ r in (t₀ : ℝ)..t, |sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r| := by
  set ρA := ∑ j ∈ A, ρR j with hρAdef
  set ΔF : ℝ → ℝ := fun r => sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r
    with hΔF
  have ht0 : (t₀ : ℝ) ≤ t := by exact_mod_cast ht.1
  have hΔFi : IntervalIntegrable ΔF volume t₀ t := hP.intervalIntegrable_dSep A ht
  set I := ∫ r in (t₀ : ℝ)..t, |ΔF r| with hIdef
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht0 fun _ _ => abs_nonneg _
  have hIabs : |∫ r in (t₀ : ℝ)..t, ΔF r| ≤ I := intervalIntegral.abs_integral_le_integral_abs ht0
  have h2ρ : 0 < 2 + ρA := by linarith
  have hC4 : 0 ≤ 4 / (2 + ρA) := by positivity
  rcases A.eq_empty_or_nonempty with hAe | ⟨j₀, hj₀⟩
  · have hw := hP.w_sub_w' ht
    have hint : (∫ r in (t₀ : ℝ)..t,
        (driverDrift ρL ρR w vL vR r - driverDrift ρL ρR w' vL' vR' r)) =
        ∫ r in (t₀ : ℝ)..t, ΔF r := by
      congr 1
      funext r
      simp only [hΔF, driverDrift_eq_sep_add_grp A, grpDrift, hAe, Finset.sum_empty, add_zero]
    refine ⟨?_, fun j hj => by simp [hAe] at hj⟩
    rw [hw, hint]
    calc |∫ r in (t₀ : ℝ)..t, ΔF r| ≤ I := hIabs
      _ ≤ (4 / (2 + ρA) + 1) * I := le_mul_of_one_le_left hI0 (by linarith)
  · have hA' : ∀ j ∈ A, vR' j t₀ = w' t₀ := fun j hj => by
      rw [← hP.vR₀ j, ← hP.w₀]; exact hA j hj
    have hm : ∀ j ∈ A, ∀ s ∈ Icc t₀ t₁, vR j s = vR j₀ s := fun j hj s hs =>
      vR_eq_of_eq hP.path hP.lt ((hA j hj).trans (hA j₀ hj₀).symm) hs
    have hm' : ∀ j ∈ A, ∀ s ∈ Icc t₀ t₁, vR' j s = vR' j₀ s := fun j hj s hs =>
      vR_eq_of_eq hP.path' hP.lt' ((hA' j hj).trans (hA' j₀ hj₀).symm) hs
    set σ : ℝ → ℝ := fun r =>
      2 / (vR j₀ r.toNNReal - w r.toNNReal) - 2 / (vR' j₀ r.toNNReal - w' r.toNNReal) with hσ
    have hgrp : ∀ r ∈ Icc (t₀ : ℝ) t₁,
        grpDrift ρR A w vR r - grpDrift ρR A w' vR' r = -(ρA / 2) * σ r := by
      intro r hr
      have hs := toNNReal_mem_Icc hr
      have e1 : grpDrift ρR A w vR r = ρA / (w r.toNNReal - vR j₀ r.toNNReal) := by
        unfold grpDrift
        rw [hρAdef, Finset.sum_div]
        exact Finset.sum_congr rfl fun j hj => by rw [hm j hj _ hs]
      have e2 : grpDrift ρR A w' vR' r = ρA / (w' r.toNNReal - vR' j₀ r.toNNReal) := by
        unfold grpDrift
        rw [hρAdef, Finset.sum_div]
        exact Finset.sum_congr rfl fun j hj => by rw [hm' j hj _ hs]
      rw [e1, e2]
      simp only [hσ]
      rw [show w r.toNNReal - vR j₀ r.toNNReal = -(vR j₀ r.toNNReal - w r.toNNReal) by ring,
        show w' r.toNNReal - vR' j₀ r.toNNReal = -(vR' j₀ r.toNNReal - w' r.toNNReal) by ring,
        div_neg, div_neg]
      ring
    have hσi : ∀ s ∈ Icc t₀ t₁, IntervalIntegrable σ volume t₀ s := fun s hs =>
      intervalIntegrable_mono_Icc ((hP.path.intervalIntegrable_forceR (hP.lt_of_mem hs) j₀).sub
        (hP.path'.intervalIntegrable_forceR (hP.lt'_of_mem hs) j₀)) hs.1 le_rfl
    have hew : ∀ s ∈ Icc t₀ t₁, w s - w' s =
        (∫ r in (t₀ : ℝ)..s, ΔF r) - ρA / 2 * ∫ r in (t₀ : ℝ)..s, σ r := by
      intro s hs
      have hs0 : (t₀ : ℝ) ≤ s := by exact_mod_cast hs.1
      rw [hP.w_sub_w' hs]
      have hcongr : EqOn
          (fun r => driverDrift ρL ρR w vL vR r - driverDrift ρL ρR w' vL' vR' r)
          (fun r => ΔF r + -(ρA / 2) * σ r) (uIcc (t₀ : ℝ) s) := by
        intro r hr
        rw [uIcc_of_le hs0] at hr
        have hr' : r ∈ Icc (t₀ : ℝ) t₁ := ⟨hr.1, hr.2.trans (by exact_mod_cast hs.2)⟩
        simp only [driverDrift_eq_sep_add_grp A, hΔF]
        rw [← hgrp r hr']
        ring
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_add (hP.intervalIntegrable_dSep A hs)
          ((hσi s hs).const_mul _), intervalIntegral.integral_const_mul]
      ring
    set u : ℝ → ℝ := fun r =>
      (vR j₀ r.toNNReal - w r.toNNReal) - (vR' j₀ r.toNNReal - w' r.toNNReal) with hu
    set k := 1 + ρA / 2 with hkdef
    have hk : 0 < k := by linarith
    set φ : ℝ → ℝ := fun r => k * σ r - ΔF r with hφ
    have htt : (t : ℝ) ∈ Icc (t₀ : ℝ) t₁ := ⟨ht0, by exact_mod_cast ht.2⟩
    have hu_eq : ∀ s ∈ Icc (t₀ : ℝ) t, u s = ∫ r in (t₀ : ℝ)..s, φ r := by
      intro s hs
      have hs' : s ∈ Icc (t₀ : ℝ) t₁ := ⟨hs.1, hs.2.trans htt.2⟩
      have hsN : s.toNNReal ∈ Icc t₀ t₁ := toNNReal_mem_Icc hs'
      have h1 := hP.vR_sub_vR' hsN j₀
      have h2 := hew _ hsN
      rw [coe_toNNReal_of_mem_Icc hs'] at h1 h2
      have hsub : s.toNNReal ∈ Icc t₀ t := toNNReal_mem_Icc hs
      rw [intervalIntegral.integral_sub ((hσi _ hsN).const_mul k |>.mono_set (by
          rw [coe_toNNReal_of_mem_Icc hs'])) (hP.intervalIntegrable_dSep A hsN |>.mono_set (by
          rw [coe_toNNReal_of_mem_Icc hs'])), intervalIntegral.integral_const_mul]
      have h1' : vR j₀ s.toNNReal - vR' j₀ s.toNNReal = ∫ r in (t₀ : ℝ)..s, σ r := h1
      simp only [hu, hkdef]
      linarith
    have hcu : ContinuousOn u (Icc (t₀ : ℝ) t) :=
      ((continuousOn_real (hP.path.continuousOn_vR j₀) (hP.lt_of_mem ht)).sub
        (continuousOn_real hP.path.continuousOn_w (hP.lt_of_mem ht))).sub
        ((continuousOn_real (hP.path'.continuousOn_vR j₀) (hP.lt'_of_mem ht)).sub
        (continuousOn_real hP.path'.continuousOn_w (hP.lt'_of_mem ht)))
    have hu0 : u t₀ = 0 := by
      simp only [hu, Real.toNNReal_coe, hP.vR₀ j₀, hP.w₀, sub_self]
    have hφi : IntervalIntegrable φ volume t₀ t := ((hσi t ht).const_mul k).sub hΔFi
    have hnull := measure_eq_zero_iff_ae_notMem.1 (hP.path.volume_collisionR j₀)
    have hnull' := measure_eq_zero_iff_ae_notMem.1 (hP.path'.volume_collisionR j₀)
    have hgpos : ∀ᵐ r ∂volume, r ∈ Icc (t₀ : ℝ) t →
        0 < vR j₀ r.toNNReal - w r.toNNReal ∧ 0 < vR' j₀ r.toNNReal - w' r.toNNReal := by
      filter_upwards [hnull, hnull'] with r h1 h2 hr
      have hr' : r ∈ Icc (t₀ : ℝ) t₁ := ⟨hr.1, hr.2.trans htt.2⟩
      have hr0 : 0 ≤ r := t₀.coe_nonneg.trans hr.1
      have hl := toNNReal_lt_of_mem_Icc' hP.lt hr'
      have hl' := toNNReal_lt_of_mem_Icc' hP.lt' hr'
      exact ⟨sub_pos.2 (lt_of_le_of_ne (hP.path.w_le_vR hl j₀) fun he => h1 ⟨hr0, hl, he⟩),
        sub_pos.2 (lt_of_le_of_ne (hP.path'.w_le_vR hl' j₀) fun he => h2 ⟨hr0, hl', he⟩)⟩
    have hup := le_integral_of_sign ht0 hcu hu0 hφi hΔFi.abs (fun _ _ => abs_nonneg _) hu_eq
      (by
        filter_upwards [hgpos] with r hr hrI hpos
        obtain ⟨hg, hg'⟩ := hr hrI
        have hle : vR' j₀ r.toNNReal - w' r.toNNReal ≤ vR j₀ r.toNNReal - w r.toNNReal := by
          have : 0 < u r := hpos
          simp only [hu] at this
          linarith
        have hσ0 : σ r ≤ 0 := by
          have := div_le_div_of_nonneg_left (a := (2 : ℝ)) (by norm_num) hg' hle
          simp only [hσ]
          linarith
        have : k * σ r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk.le hσ0
        show k * σ r - ΔF r ≤ |ΔF r|
        linarith [neg_le_abs (ΔF r)])
    have hun := le_integral_of_sign (D := fun r => -u r) (φ := fun r => -φ r) ht0 hcu.neg
      (by simp [hu0]) hφi.neg hΔFi.abs (fun _ _ => abs_nonneg _)
      (fun s hs => by rw [hu_eq s hs, intervalIntegral.integral_neg])
      (by
        filter_upwards [hgpos] with r hr hrI hpos
        obtain ⟨hg, hg'⟩ := hr hrI
        have hle : vR j₀ r.toNNReal - w r.toNNReal ≤ vR' j₀ r.toNNReal - w' r.toNNReal := by
          have : 0 < -u r := hpos
          simp only [hu] at this
          linarith
        have hσ0 : 0 ≤ σ r := by
          have := div_le_div_of_nonneg_left (a := (2 : ℝ)) (by norm_num) hg hle
          simp only [hσ]
          linarith
        have : 0 ≤ k * σ r := mul_nonneg hk.le hσ0
        show -(k * σ r - ΔF r) ≤ |ΔF r|
        linarith [le_abs_self (ΔF r)])
    have hun' : -u t ≤ I := hun
    have hUabs : |u t| ≤ I := abs_le.2 ⟨by linarith, hup⟩
    have h1 := hP.vR_sub_vR' ht j₀
    have h2 := hew t ht
    have hut : u t = (vR j₀ t - w t) - (vR' j₀ t - w' t) := by simp [hu]
    set S := ∫ r in (t₀ : ℝ)..t, σ r
    set F := ∫ r in (t₀ : ℝ)..t, ΔF r
    have hkS : k * S = u t + F := by
      rw [hut]; simp only [hkdef]; linarith
    have hSabs : |S| ≤ 4 / (2 + ρA) * I := by
      have hS : S = (u t + F) / k := by rw [← hkS]; field_simp
      rw [hS, abs_div, abs_of_pos hk, div_le_iff₀ hk]
      have hk4 : 4 / (2 + ρA) * I * k = 2 * I := by
        rw [hkdef]; field_simp; ring
      rw [hk4]
      calc |u t + F| ≤ |u t| + |F| := abs_add_le _ _
        _ ≤ I + I := add_le_add hUabs hIabs
        _ = 2 * I := by ring
    have hwt : w t - w' t = S - u t := by rw [hut]; linarith
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hwt]
      calc |S - u t| ≤ |S| + |u t| := abs_sub _ _
        _ ≤ 4 / (2 + ρA) * I + I := add_le_add hSabs hUabs
        _ = (4 / (2 + ρA) + 1) * I := by ring
    · rw [hm j hj t ht, hm' j hj t ht, h1]
      exact hSabs

end LocalPair

/-! ### Local uniqueness -/

namespace LocalPair

variable {t₀ t₁ : ℝ≥0} (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
include hP

theorem continuousOn_errN (A : Finset (Fin nR)) :
    ContinuousOn (errN A w vL vR w' vL' vR') (Icc (t₀ : ℝ) t₁) := by
  have cw := continuousOn_real (t₀ := t₀) hP.path.continuousOn_w hP.lt
  have cw' := continuousOn_real (t₀ := t₀) hP.path'.continuousOn_w hP.lt'
  unfold errN
  refine ((cw.sub cw').abs.add ?_).add ?_
  · exact continuousOn_finsetSum _ fun i _ =>
      ((continuousOn_real (hP.path.continuousOn_vL i) hP.lt).sub
        (continuousOn_real (hP.path'.continuousOn_vL i) hP.lt')).abs
  · exact continuousOn_finsetSum _ fun j _ =>
      ((continuousOn_real (hP.path.continuousOn_vR j) hP.lt).sub
        (continuousOn_real (hP.path'.continuousOn_vR j) hP.lt')).abs

/-- **Local pathwise uniqueness, right contact group.** Two solutions for the same word and the
same driving path `b` that agree at `t₀` agree on `[t₀, t₁]` if, on `[t₀, t₁]`, every left mark
and every right mark outside `A` stays at distance `≥ ε` from the driver (for both solutions),
the marks of `A` sit at the driver at `t₀`, and the total weight of `A` is `> −2`. `A = ∅` is
allowed (all marks separated). -/
theorem eq_of_rightGroup (A : Finset (Fin nR)) (hA : ∀ j ∈ A, vR j t₀ = w t₀)
    (hρA : -2 < ∑ j ∈ A, ρR j) {ε : ℝ} (hε : 0 < ε) (hS : Separated A ε w vL vR t₀ t₁)
    (hS' : Separated A ε w' vL' vR' t₀ t₁) {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := by
  set N := errN A w vL vR w' vL' vR' with hNdef
  set ΔF : ℝ → ℝ := fun r => sepDrift ρL ρR A w vL vR r - sepDrift ρL ρR A w' vL' vR' r
    with hΔF
  set L := (∑ i, |ρL i| + ∑ j, |ρR j|) / ε ^ 2 with hLdef
  set C := 4 / (2 + ∑ j ∈ A, ρR j) + 1 with hCdef
  have hL0 : 0 ≤ L := by positivity
  have h2ρ : 0 < 2 + ∑ j ∈ A, ρR j := by linarith
  have hC0 : 0 ≤ C := by positivity
  set K := C * L + ((nL : ℝ) + nR) * (2 / ε ^ 2) with hKdef
  have hNc := hP.continuousOn_errN A
  have hΔFle : ∀ r ∈ Icc (t₀ : ℝ) t₁, |ΔF r| ≤ L * N r := fun r hr =>
    abs_sepDrift_sub_le hε hS hS' hr
  have hint : ∀ s ∈ Icc (t₀ : ℝ) t₁, IntervalIntegrable N volume t₀ s := fun s hs =>
    (hNc.mono (Icc_subset_Icc le_rfl hs.2)).intervalIntegrable_of_Icc hs.1
  have hFI : ∀ s ∈ Icc (t₀ : ℝ) t₁, ∫ r in (t₀ : ℝ)..s, |ΔF r| ≤ L * ∫ r in (t₀ : ℝ)..s, N r := by
    intro s hs
    have hsN := toNNReal_mem_Icc hs
    have hΔFi := hP.intervalIntegrable_dSep A hsN
    rw [coe_toNNReal_of_mem_Icc hs] at hΔFi
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hs.1 hΔFi.abs ((hint s hs).const_mul L)
      fun r hr => hΔFle r ⟨hr.1, hr.2.trans hs.2⟩
  have hNle : ∀ s ∈ Icc (t₀ : ℝ) t₁, N s ≤ K * ∫ r in (t₀ : ℝ)..s, N r := by
    intro s hs
    have hsN := toNNReal_mem_Icc hs
    have hcoe := coe_toNNReal_of_mem_Icc hs
    have hJ0 : 0 ≤ ∫ r in (t₀ : ℝ)..s, N r :=
      intervalIntegral.integral_nonneg hs.1 fun r _ => errN_nonneg A r
    have hw := (hP.group_bound A hA hρA hsN).1
    rw [hcoe] at hw
    have hw' : |w s.toNNReal - w' s.toNNReal| ≤ C * L * ∫ r in (t₀ : ℝ)..s, N r := by
      calc _ ≤ C * ∫ r in (t₀ : ℝ)..s, |ΔF r| := hw
        _ ≤ C * (L * ∫ r in (t₀ : ℝ)..s, N r) := mul_le_mul_of_nonneg_left (hFI s hs) hC0
        _ = C * L * ∫ r in (t₀ : ℝ)..s, N r := by ring
    have hLi : ∀ i, |vL i s.toNNReal - vL' i s.toNNReal| ≤
        2 / ε ^ 2 * ∫ r in (t₀ : ℝ)..s, N r := by
      intro i
      rw [hP.vL_sub_vL' hsN i, hcoe]
      refine (intervalIntegral.abs_integral_le_integral_abs hs.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      have hfi := intervalIntegrable_mono_Icc
        ((hP.path.intervalIntegrable_forceL (hP.lt_of_mem hsN) i).sub
          (hP.path'.intervalIntegrable_forceL (hP.lt'_of_mem hsN) i)) hsN.1 le_rfl
      rw [hcoe] at hfi
      exact intervalIntegral.integral_mono_on hs.1 hfi.abs ((hint s hs).const_mul _)
        fun r hr => abs_forceL_sub_le hε hS hS' ⟨hr.1, hr.2.trans hs.2⟩ i
    have hRj : ∀ j ∈ Aᶜ, |vR j s.toNNReal - vR' j s.toNNReal| ≤
        2 / ε ^ 2 * ∫ r in (t₀ : ℝ)..s, N r := by
      intro j hj
      rw [hP.vR_sub_vR' hsN j, hcoe]
      refine (intervalIntegral.abs_integral_le_integral_abs hs.1).trans ?_
      rw [← intervalIntegral.integral_const_mul]
      have hfi := intervalIntegrable_mono_Icc
        ((hP.path.intervalIntegrable_forceR (hP.lt_of_mem hsN) j).sub
          (hP.path'.intervalIntegrable_forceR (hP.lt'_of_mem hsN) j)) hsN.1 le_rfl
      rw [hcoe] at hfi
      exact intervalIntegral.integral_mono_on hs.1 hfi.abs ((hint s hs).const_mul _)
        fun r hr => abs_forceR_sub_le hε hS hS' ⟨hr.1, hr.2.trans hs.2⟩ hj
    set J := ∫ r in (t₀ : ℝ)..s, N r
    have hsumL : ∑ i, |vL i s.toNNReal - vL' i s.toNNReal| ≤ (nL : ℝ) * (2 / ε ^ 2 * J) := by
      calc _ ≤ ∑ _i : Fin nL, 2 / ε ^ 2 * J := Finset.sum_le_sum fun i _ => hLi i
        _ = (nL : ℝ) * (2 / ε ^ 2 * J) := by simp
    have hsumR : ∑ j ∈ Aᶜ, |vR j s.toNNReal - vR' j s.toNNReal| ≤ (nR : ℝ) * (2 / ε ^ 2 * J) := by
      calc _ ≤ ∑ _j ∈ Aᶜ, 2 / ε ^ 2 * J := Finset.sum_le_sum fun j hj => hRj j hj
        _ = (Aᶜ.card : ℝ) * (2 / ε ^ 2 * J) := by simp
        _ ≤ (nR : ℝ) * (2 / ε ^ 2 * J) := by
          gcongr
          have := Finset.card_le_univ Aᶜ
          simpa using this
    show |w s.toNNReal - w' s.toNNReal| + ∑ i, |vL i s.toNNReal - vL' i s.toNNReal| +
        ∑ j ∈ Aᶜ, |vR j s.toNNReal - vR' j s.toNNReal| ≤ K * J
    rw [hKdef]
    nlinarith
  have hN0 := eq_zero_of_le_mul_integral (fun r _ => errN_nonneg A r) hNc hNle
  have htt : (t : ℝ) ∈ Icc (t₀ : ℝ) t₁ := ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  have hNt : N t = 0 := hN0 t htt
  have hJ : ∫ r in (t₀ : ℝ)..t, N r = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun r hr => by
      rw [uIcc_of_le htt.1] at hr; exact hN0 r ⟨hr.1, hr.2.trans htt.2⟩]
    simp
  have hzero : ∀ {x : ℝ}, 0 ≤ x → x ≤ 0 → x = 0 := fun h1 h2 => le_antisymm h2 h1
  refine ⟨?_, fun i => ?_, fun j => ?_⟩
  · have := abs_w_le_errN (w := w) (vL := vL) (vR := vR) (w' := w') (vL' := vL') (vR' := vR')
      A (t : ℝ)
    rw [Real.toNNReal_coe] at this
    rw [← sub_eq_zero, ← abs_eq_zero]
    exact hzero (abs_nonneg _) (this.trans hNt.le)
  · have := abs_vL_le_errN (w := w) (vL := vL) (vR := vR) (w' := w') (vL' := vL') (vR' := vR')
      A (t : ℝ) i
    rw [Real.toNNReal_coe] at this
    rw [← sub_eq_zero, ← abs_eq_zero]
    exact hzero (abs_nonneg _) (this.trans hNt.le)
  · by_cases hj : j ∈ A
    · have h := (hP.group_bound A hA hρA ht).2 j hj
      have hF := hFI t htt
      rw [hJ, mul_zero] at hF
      have hpos : 0 ≤ 4 / (2 + ∑ j ∈ A, ρR j) := by positivity
      rw [← sub_eq_zero, ← abs_eq_zero]
      refine hzero (abs_nonneg _) (h.trans ?_)
      exact mul_nonpos_of_nonneg_of_nonpos hpos hF
    · have := abs_vR_le_errN (w := w) (vL := vL) (vR := vR) (w' := w') (vL' := vL') (vR' := vR')
        (A := A) (t : ℝ) (Finset.mem_compl.2 hj)
      rw [Real.toNNReal_coe] at this
      rw [← sub_eq_zero, ← abs_eq_zero]
      exact hzero (abs_nonneg _) (this.trans hNt.le)

end LocalPair

/-! ### Left contact group (by reflection) -/

namespace LocalPair

variable {t₀ t₁ : ℝ≥0}

/-- The reflection `x ↦ −x` (sides exchanged) of a pair of solutions. -/
theorem reflect (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁) :
    LocalPair a (-xR) (-xL) ρR ρL (-w) (fun i => -vR i) (fun i => -vL i) (-w')
      (fun i => -vR' i) (fun i => -vL' i) (-b) ζ ζ' t₀ t₁ where
  path := hP.path.reflect
  drv := hP.drv.reflect
  path' := hP.path'.reflect
  drv' := hP.drv'.reflect
  le := hP.le
  lt := hP.lt
  lt' := hP.lt'
  w₀ := by simp [hP.w₀]
  vL₀ i := by simp [hP.vR₀ i]
  vR₀ j := by simp [hP.vL₀ j]

/-- **Local pathwise uniqueness, left contact group** (the reflection of `eq_of_rightGroup`). -/
theorem eq_of_leftGroup (hP : LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁)
    (A : Finset (Fin nL)) (hA : ∀ i ∈ A, vL i t₀ = w t₀) (hρA : -2 < ∑ i ∈ A, ρL i) {ε : ℝ}
    (hε : 0 < ε)
    (hS : ∀ s ∈ Icc t₀ t₁, (∀ i ∈ Aᶜ, ε ≤ w s - vL i s) ∧ ∀ j, ε ≤ vR j s - w s)
    (hS' : ∀ s ∈ Icc t₀ t₁, (∀ i ∈ Aᶜ, ε ≤ w' s - vL' i s) ∧ ∀ j, ε ≤ vR' j s - w' s)
    {t : ℝ≥0} (ht : t ∈ Icc t₀ t₁) :
    w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t := by
  have key := hP.reflect.eq_of_rightGroup A (fun i hi => by simp [hA i hi]) hρA hε
    (fun s hs => ⟨fun j => by have := (hS s hs).2 j; simp only [Pi.neg_apply]; linarith,
      fun i hi => by have := (hS s hs).1 i hi; simp only [Pi.neg_apply]; linarith⟩)
    (fun s hs => ⟨fun j => by have := (hS' s hs).2 j; simp only [Pi.neg_apply]; linarith,
      fun i hi => by have := (hS' s hs).1 i hi; simp only [Pi.neg_apply]; linarith⟩) ht
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨by simpa using h1, fun i => by simpa using h3 i, fun j => by simpa using h2 j⟩

end LocalPair

/-! ### Continuous induction (copied from `AssemblyPathwise.lean`) -/

open Sec2.Assembly (exists_pos_forall_lt eq_of_eqOn_Iio)

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ ζ' : ℝ≥0∞}

/-- The two states agree at time `t`. -/
def Agree (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (w' : ℝ≥0 → ℝ)
    (vL' : Fin nL → ℝ≥0 → ℝ) (vR' : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t

section Step

variable (hsep : ∀ i j, xL i < xR j) (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ)
  (hw : DriverEq a ρL ρR w vL vR b ζ) (h' : IsSLEPathUpTo a xL xR ρL ρR w' vL' vR' b ζ')
  (hw' : DriverEq a ρL ρR w' vL' vR' b ζ')
include hsep h hw h' hw'

omit hw h' hw' in
/-- At a time before the lifetime, no left mark and no right mark both touch the driver. -/
theorem not_two_sided {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) (j : Fin nR)
    (hi : vL i t = w t) (hj : vR j t = w t) : False := by
  have h1 := h.vL_le_xL ht i
  have h2 := h.xR_le_vR ht j
  have := hsep i j
  linarith

/-- **One step of the continuous induction.** If the solutions agree at `t₀ < min ζ ζ'`, they
agree on a right neighbourhood `[t₀, u)`. -/
theorem exists_agree_Ico {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < min ζ ζ')
    (hag : Agree w vL vR w' vL' vR' t₀) :
    ∃ u > t₀, ∀ t ∈ Ico t₀ u, Agree w vL vR w' vL' vR' t := by
  obtain ⟨hw₀, hL₀, hR₀⟩ := hag
  have hζ : (t₀ : ℝ≥0∞) < ζ := lt_of_lt_of_le ht₀ (min_le_left _ _)
  have hζ' : (t₀ : ℝ≥0∞) < ζ' := lt_of_lt_of_le ht₀ (min_le_right _ _)
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < min ζ ζ'} :=
    isOpen_lt ENNReal.continuous_coe continuous_const
  have hca : ∀ {f : ℝ≥0 → ℝ} {ξ : ℝ≥0∞}, ContinuousOn f {t | (t : ℝ≥0∞) < ξ} →
      (t₀ : ℝ≥0∞) < ξ → ContinuousAt f t₀ := fun hf hξ =>
    hf.continuousAt ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hξ)
  -- the threshold condition fails at `t₀`
  have hnt := h.not_threshold hζ
  unfold ForceWord.ThresholdCondition at hnt
  simp only [not_or, not_le] at hnt
  obtain ⟨hρL, hρR⟩ := hnt
  -- reduce to a statement on `Ico t₀ u` from an eventual separation
  have finish : ∀ (P : ℝ≥0 → Prop), (∀ᶠ s in 𝓝 t₀, P s) →
      (∀ t₁, t₀ ≤ t₁ → (t₁ : ℝ≥0∞) < min ζ ζ' → (∀ s ∈ Icc t₀ t₁, P s) →
        Agree w vL vR w' vL' vR' t₁) →
      ∃ u > t₀, ∀ t ∈ Ico t₀ u, Agree w vL vR w' vL' vR' t := by
    intro P hP hstep
    have hP' : ∀ᶠ s in 𝓝[≥] t₀, P s ∧ (s : ℝ≥0∞) < min ζ ζ' :=
      ((hP.and (hopen.mem_nhds ht₀))).filter_mono nhdsWithin_le_nhds
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (lt_add_one t₀)).1 hP'
    refine ⟨u, hu, fun t ht => hstep t ht.1 (hsub ht).2 fun s hs => (hsub ⟨hs.1, ?_⟩).1⟩
    exact lt_of_le_of_lt hs.2 ht.2
  by_cases hRc : ∃ j, vR j t₀ = w t₀
  · -- right contact group
    set A := Finset.univ.filter fun j => vR j t₀ = w t₀ with hAdef
    have hA : ∀ j ∈ A, vR j t₀ = w t₀ := fun j hj => (Finset.mem_filter.1 hj).2
    have hgL : ∀ i, 0 < w t₀ - vL i t₀ := by
      intro i
      obtain ⟨j, hj⟩ := hRc
      refine sub_pos.2 (lt_of_le_of_ne (h.vL_le_w hζ i) fun he => ?_)
      exact not_two_sided hsep h hζ i j he hj
    have hgR : ∀ j, 0 < if j ∈ A then 1 else vR j t₀ - w t₀ := by
      intro j
      split_ifs with hjA
      · exact one_pos
      · refine sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hζ j) fun he => hjA ?_)
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, he.symm⟩
    obtain ⟨ε₁, hε₁, hε₁'⟩ := exists_pos_forall_lt _ hgL
    obtain ⟨ε₂, hε₂, hε₂'⟩ := exists_pos_forall_lt _ hgR
    set ε := min ε₁ ε₂
    have hε : 0 < ε := lt_min hε₁ hε₂
    have hev : ∀ᶠ s in 𝓝 t₀, (∀ i, ε < w s - vL i s ∧ ε < w' s - vL' i s) ∧
        ∀ j ∈ Aᶜ, ε < vR j s - w s ∧ ε < vR' j s - w' s := by
      refine Filter.Eventually.and (Filter.eventually_all.2 fun i => ?_)
        (Filter.eventually_all.2 fun j => ?_)
      · have hlt : ε < w t₀ - vL i t₀ := lt_of_le_of_lt (min_le_left _ _) (hε₁' i)
        have hlt' : ε < w' t₀ - vL' i t₀ := by rw [← hw₀, ← hL₀ i]; exact hlt
        exact (continuousAt_const.eventually_lt ((hca h.continuousOn_w hζ).sub
          (hca (h.continuousOn_vL i) hζ)) hlt).and
          (continuousAt_const.eventually_lt ((hca h'.continuousOn_w hζ').sub
          (hca (h'.continuousOn_vL i) hζ')) hlt')
      · by_cases hjA : j ∈ A
        · exact Filter.Eventually.of_forall fun s hs => absurd hjA (Finset.mem_compl.1 hs)
        · have hlt : ε < vR j t₀ - w t₀ := by
            have := hε₂' j
            simp only [hjA, ↓reduceIte] at this
            exact lt_of_le_of_lt (min_le_right _ _) this
          have hlt' : ε < vR' j t₀ - w' t₀ := by rw [← hw₀, ← hR₀ j]; exact hlt
          have e1 := continuousAt_const.eventually_lt ((hca (h.continuousOn_vR j) hζ).sub
            (hca h.continuousOn_w hζ)) hlt
          have e2 := continuousAt_const.eventually_lt ((hca (h'.continuousOn_vR j) hζ').sub
            (hca h'.continuousOn_w hζ')) hlt'
          filter_upwards [e1, e2] with s hs1 hs2 _ using ⟨hs1, hs2⟩
    refine finish _ hev fun t₁ h01 ht₁ hsep₁ => ?_
    have hP : UpTo.LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁ :=
      { path := h, drv := hw, path' := h', drv' := hw', le := h01,
        lt := lt_of_lt_of_le ht₁ (min_le_left _ _), lt' := lt_of_lt_of_le ht₁ (min_le_right _ _),
        w₀ := hw₀, vL₀ := hL₀, vR₀ := hR₀ }
    have hρA : -2 < ∑ j ∈ A, ρR j := hρR
    exact hP.eq_of_rightGroup A hA hρA hε
      (fun s hs => ⟨fun i => ((hsep₁ s hs).1 i).1.le, fun j hj => ((hsep₁ s hs).2 j hj).1.le⟩)
      (fun s hs => ⟨fun i => ((hsep₁ s hs).1 i).2.le, fun j hj => ((hsep₁ s hs).2 j hj).2.le⟩)
      ⟨h01, le_rfl⟩
  · -- left contact group (possibly empty)
    simp only [not_exists] at hRc
    set A := Finset.univ.filter fun i => vL i t₀ = w t₀ with hAdef
    have hA : ∀ i ∈ A, vL i t₀ = w t₀ := fun i hi => (Finset.mem_filter.1 hi).2
    have hgR : ∀ j, 0 < vR j t₀ - w t₀ := fun j =>
      sub_pos.2 (lt_of_le_of_ne (h.w_le_vR hζ j) fun he => hRc j he.symm)
    have hgL : ∀ i, 0 < if i ∈ A then 1 else w t₀ - vL i t₀ := by
      intro i
      split_ifs with hiA
      · exact one_pos
      · refine sub_pos.2 (lt_of_le_of_ne (h.vL_le_w hζ i) fun he => hiA ?_)
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩
    obtain ⟨ε₁, hε₁, hε₁'⟩ := exists_pos_forall_lt _ hgL
    obtain ⟨ε₂, hε₂, hε₂'⟩ := exists_pos_forall_lt _ hgR
    set ε := min ε₁ ε₂
    have hε : 0 < ε := lt_min hε₁ hε₂
    have hev : ∀ᶠ s in 𝓝 t₀, (∀ i ∈ Aᶜ, ε < w s - vL i s ∧ ε < w' s - vL' i s) ∧
        ∀ j, ε < vR j s - w s ∧ ε < vR' j s - w' s := by
      refine Filter.Eventually.and (Filter.eventually_all.2 fun i => ?_)
        (Filter.eventually_all.2 fun j => ?_)
      · by_cases hiA : i ∈ A
        · exact Filter.Eventually.of_forall fun s hs => absurd hiA (Finset.mem_compl.1 hs)
        · have hlt : ε < w t₀ - vL i t₀ := by
            have := hε₁' i
            simp only [hiA, ↓reduceIte] at this
            exact lt_of_le_of_lt (min_le_left _ _) this
          have hlt' : ε < w' t₀ - vL' i t₀ := by rw [← hw₀, ← hL₀ i]; exact hlt
          have e1 := continuousAt_const.eventually_lt ((hca h.continuousOn_w hζ).sub
            (hca (h.continuousOn_vL i) hζ)) hlt
          have e2 := continuousAt_const.eventually_lt ((hca h'.continuousOn_w hζ').sub
            (hca (h'.continuousOn_vL i) hζ')) hlt'
          filter_upwards [e1, e2] with s hs1 hs2 _ using ⟨hs1, hs2⟩
      · have hlt : ε < vR j t₀ - w t₀ := lt_of_le_of_lt (min_le_right _ _) (hε₂' j)
        have hlt' : ε < vR' j t₀ - w' t₀ := by rw [← hw₀, ← hR₀ j]; exact hlt
        exact (continuousAt_const.eventually_lt ((hca (h.continuousOn_vR j) hζ).sub
          (hca h.continuousOn_w hζ)) hlt).and
          (continuousAt_const.eventually_lt ((hca (h'.continuousOn_vR j) hζ').sub
          (hca h'.continuousOn_w hζ')) hlt')
    refine finish _ hev fun t₁ h01 ht₁ hsep₁ => ?_
    have hP : UpTo.LocalPair a xL xR ρL ρR w vL vR w' vL' vR' b ζ ζ' t₀ t₁ :=
      { path := h, drv := hw, path' := h', drv' := hw', le := h01,
        lt := lt_of_lt_of_le ht₁ (min_le_left _ _), lt' := lt_of_lt_of_le ht₁ (min_le_right _ _),
        w₀ := hw₀, vL₀ := hL₀, vR₀ := hR₀ }
    have hρA : -2 < ∑ i ∈ A, ρL i := hρL
    exact hP.eq_of_leftGroup A hA hρA hε
      (fun s hs => ⟨fun i hi => ((hsep₁ s hs).1 i hi).1.le, fun j => ((hsep₁ s hs).2 j).1.le⟩)
      (fun s hs => ⟨fun i hi => ((hsep₁ s hs).1 i hi).2.le, fun j => ((hsep₁ s hs).2 j).2.le⟩)
      ⟨h01, le_rfl⟩

/-- **Agreement before both lifetimes.** -/
theorem agree_of_lt_min {t : ℝ≥0} (ht : (t : ℝ≥0∞) < min ζ ζ') :
    Agree w vL vR w' vL' vR' t := by
  by_contra hcon
  set S := {s : ℝ≥0 | (s : ℝ≥0∞) < min ζ ζ' ∧ ¬ Agree w vL vR w' vL' vR' s} with hSdef
  have hSne : S.Nonempty := ⟨t, ht, hcon⟩
  set t₀ := sInf S with ht₀def
  have hbdd : BddBelow S := OrderBot.bddBelow S
  have hle : ∀ s ∈ S, t₀ ≤ s := fun s hs => csInf_le hbdd hs
  have ht₀lt : (t₀ : ℝ≥0∞) < min ζ ζ' :=
    lt_of_le_of_lt (by exact_mod_cast hle t ⟨ht, hcon⟩) ht
  have hbefore : ∀ s < t₀, Agree w vL vR w' vL' vR' s := by
    intro s hs
    by_contra hns
    have hsl : (s : ℝ≥0∞) < min ζ ζ' := lt_trans (by exact_mod_cast hs) ht₀lt
    exact (not_le.2 hs) (hle s ⟨hsl, hns⟩)
  have hζ : (t₀ : ℝ≥0∞) < ζ := lt_of_lt_of_le ht₀lt (min_le_left _ _)
  have hζ' : (t₀ : ℝ≥0∞) < ζ' := lt_of_lt_of_le ht₀lt (min_le_right _ _)
  have hIic : ∀ {ξ : ℝ≥0∞}, (t₀ : ℝ≥0∞) < ξ → Iic t₀ ⊆ {s : ℝ≥0 | (s : ℝ≥0∞) < ξ} :=
    fun hξ s hs => lt_of_le_of_lt (by exact_mod_cast hs) hξ
  have hat : Agree w vL vR w' vL' vR' t₀ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h0 | h0
    · rw [← h0]
      refine ⟨by rw [h.w_zero, h'.w_zero], fun i => by rw [h.vL_zero, h'.vL_zero],
        fun j => by rw [h.vR_zero, h'.vR_zero]⟩
    · refine ⟨eq_of_eqOn_Iio h0 (h.continuousOn_w.mono (hIic hζ))
          (h'.continuousOn_w.mono (hIic hζ')) fun s hs => (hbefore s hs).1,
        fun i => eq_of_eqOn_Iio h0 ((h.continuousOn_vL i).mono (hIic hζ))
          ((h'.continuousOn_vL i).mono (hIic hζ')) fun s hs => (hbefore s hs).2.1 i,
        fun j => eq_of_eqOn_Iio h0 ((h.continuousOn_vR j).mono (hIic hζ))
          ((h'.continuousOn_vR j).mono (hIic hζ')) fun s hs => (hbefore s hs).2.2 j⟩
  obtain ⟨u, hu, hagree⟩ := exists_agree_Ico hsep h hw h' hw' ht₀lt hat
  obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hSne hu
  exact hsS.2 (hagree s ⟨hle s hsS, hsu⟩)


end Step

end UpTo

end Sec2

end InteractingSLE
