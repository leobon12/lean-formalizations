/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalScale
import InteractingSLE.Spec.Sec2.AddMarksPath

/-!
# Brownian scaling of local integrated paths

Packet PROVE-STAGED-NODE. The node candidates of Proposition 5.9 are the undilated tree candidates scaled by the
node factor `c` (`Prop59NodeTree.scalePiece`: `t ↦ c X(t/c²)`, lifetime `c² ζ`). Clause 1 of their killed law is a
local integrated path (`Sec2.IsSLEPathUpTo`), so it must pass through Brownian scaling:

* `IsSLEPathUpTo.scalePath`: the frozen-path scaling `isIntegratedSLEPath_scale` for the local form (`t ↦ a f(ct)`,
  `a² c = 1`, lifetime `τ / c`);
* **`IsSLEPathUpTo.dilate`**: the node form `t ↦ c f(t/c²)` with lifetime `c² τ`, for `c > 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.IsSLEPathUpTo

open ZhanGT4.UpMark

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **Brownian scaling of a local integrated path**: `t ↦ a f(c t)` with `a² c = 1` before `τ / c`. -/
theorem scalePath (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR b τ) {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ} (ha : 0 < a)
    (hac : a ^ 2 * c = 1) :
    IsSLEPathUpTo κ (fun i => a * xL i) (fun j => a * xR j) ρL ρR (ZhanGT4.UpMark.scalePath a c w)
      (fun i => ZhanGT4.UpMark.scalePath a c (vL i)) (fun j => ZhanGT4.UpMark.scalePath a c (vR j))
      (ZhanGT4.UpMark.scalePath a c b) (τ / c) := by
  obtain ⟨hw0, hvL0, hvR0, hcw, hcvL, hcvR, hantiL, hleL, hleR, hmonoR, hintL, hintR, hweq, hvLeq, hvReq,
    hcolL, hcolR, hnth⟩ := hp
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ / c → ((c * t : ℝ≥0) : ℝ≥0∞) < τ := fun ht => (coe_lt_div_iff hc).1 ht
  have hcolset : ∀ f g : ℝ≥0 → ℝ, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ f s.toNNReal = g s.toNNReal} = 0 →
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ / c ∧
        ZhanGT4.UpMark.scalePath a c f s.toNNReal = ZhanGT4.UpMark.scalePath a c g s.toNNReal} = 0 := by
    intro f g h0
    have hc' : (c : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hc
    refine measure_mono_null (fun s hs => ?_) ((Real.volume_preimage_mul_left hc' _).trans (by rw [h0, mul_zero]))
    obtain ⟨hs0, hsζ, hfg⟩ := hs
    simp only [ZhanGT4.UpMark.scalePath, mul_right_inj' ha.ne'] at hfg
    refine ⟨mul_nonneg c.coe_nonneg hs0, ?_, ?_⟩
    · rw [← nnreal_mul_toNNReal]; exact hlt hsζ
    · rw [← nnreal_mul_toNNReal]; exact hfg
  refine ⟨by simp [ZhanGT4.UpMark.scalePath, hw0], fun i => by simp [ZhanGT4.UpMark.scalePath, hvL0],
    fun j => by simp [ZhanGT4.UpMark.scalePath, hvR0],
    continuousOn_scalePath hc a hcw, fun i => continuousOn_scalePath hc a (hcvL i),
    fun j => continuousOn_scalePath hc a (hcvR j),
    fun ht i j hij => mul_le_mul_of_nonneg_left (hantiL (hlt ht) hij) ha.le,
    fun ht i => mul_le_mul_of_nonneg_left (hleL (hlt ht) i) ha.le,
    fun ht i => mul_le_mul_of_nonneg_left (hleR (hlt ht) i) ha.le,
    fun ht i j hij => mul_le_mul_of_nonneg_left (hmonoR (hlt ht) hij) ha.le,
    fun ht i => intervalIntegrable_scale_inv c hc w (vL i) (hintL (hlt ht) i),
    fun ht j => intervalIntegrable_scale_inv c hc w (vR j) (hintR (hlt ht) j),
    fun ht => ?_, fun ht i => ?_, fun ht j => ?_, fun i => hcolset w (vL i) (hcolL i),
    fun j => hcolset w (vR j) (hcolR j), fun ht => ?_⟩
  · simp_rw [integral_scale_div c hc ha.ne' hac]
    simp only [ZhanGT4.UpMark.scalePath]
    rw [hweq (hlt ht), ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  · rw [integral_scale_div c hc ha.ne' hac]
    simp only [ZhanGT4.UpMark.scalePath]
    rw [hvLeq (hlt ht) i]
    ring
  · rw [integral_scale_div c hc ha.ne' hac]
    simp only [ZhanGT4.UpMark.scalePath]
    rw [hvReq (hlt ht) j]
    ring
  · simp only [ZhanGT4.UpMark.scalePath]
    rw [thresholdCondition_smul ρL ρR ha.ne']
    exact hnth (hlt ht)

/-- **The node dilation of a local integrated path**: `t ↦ c f(t/c²)` before `c² τ`, for `c > 0`. -/
theorem dilate (hp : IsSLEPathUpTo κ xL xR ρL ρR w vL vR b τ) {c : ℝ≥0} (hc : 0 < c) :
    IsSLEPathUpTo κ (fun i => (c : ℝ) * xL i) (fun j => (c : ℝ) * xR j) ρL ρR (fun t => (c : ℝ) * w (t / c ^ 2))
      (fun i t => (c : ℝ) * vL i (t / c ^ 2)) (fun j t => (c : ℝ) * vR j (t / c ^ 2))
      (fun t => (c : ℝ) * b (t / c ^ 2)) (((c ^ 2 : ℝ≥0) : ℝ≥0∞) * τ) := by
  have hc2 : (c ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hc.ne')
  have hac : (c : ℝ) ^ 2 * (((c ^ 2)⁻¹ : ℝ≥0) : ℝ) = 1 := by
    rw [NNReal.coe_inv, NNReal.coe_pow]
    exact mul_inv_cancel₀ (pow_ne_zero 2 (NNReal.coe_ne_zero.2 hc.ne'))
  have h := hp.scalePath hc2 (NNReal.coe_pos.2 hc) hac
  have e : ∀ f : ℝ≥0 → ℝ, ZhanGT4.UpMark.scalePath (c : ℝ) (c ^ 2)⁻¹ f = fun t => (c : ℝ) * f (t / c ^ 2) :=
    fun f => funext fun t => by rw [ZhanGT4.UpMark.scalePath, div_eq_inv_mul]
  have eτ : τ / (((c ^ 2)⁻¹ : ℝ≥0) : ℝ≥0∞) = ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * τ := by
    rw [ENNReal.coe_inv (pow_ne_zero 2 hc.ne'), div_eq_mul_inv, inv_inv, mul_comm]
  simp only [e, eτ] at h
  exact h

end InteractingSLE.Sec2.IsSLEPathUpTo
