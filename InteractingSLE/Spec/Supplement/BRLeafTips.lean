/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6Past

/-!
# Tips of a counterflow read through the flow's own Loewner chart and the inversion

Packet PROVE-T14-BR (for `Theorem14.GW2Later.GB6PrefixPairStatement`). Deterministic: let `U` be a continuous driver
from `0` whose inverse Loewner map at `T` has boundary limits, and `W₂` a continuous driver from `0` with a complete
continuous generating trace `Γ` whose interior times are dense. If, at every interior time, the point `Γ(u)` read
through the chart `(Chart.id.loewner U T).trans infinitySourceChart` lies in a closed set `R`, then so does every
physical tip of `W₂` read through that chart (**`mem_of_tipAt_loewner_inf`**). At a real trace point the tip is the
boundary value of the chart at that point, a limit of interior chart values; at a trace point `0` there is no finite
tip (the chart moves points by a bounded amount; the argument of `GW2Later.mem_of_tipAt_loewner_trans`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE

namespace Theorem14

namespace BRLeaf

open GW2Later

/-- The identity chart has a proper boundary extension. -/
theorem hasProperBdryExt_id : GW1P.HasProperBdryExt Chart.id :=
  ⟨fun z => z, 0, fun _ _ => tendsto_nhdsWithin_of_tendsto_nhds tendsto_id, fun p _ => by simp⟩

/-- **Interior times of a transient trace with dense interior rational times are dense.** -/
theorem mem_closure_setOf_mem_H {Γ : ℝ≥0 → ℂ} (hΓ : Supp8.GB6.TransientDenseQ Γ) (r : ℝ≥0) :
    r ∈ closure {u : ℝ≥0 | Γ u ∈ H} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨a, hra, haε⟩ := exists_rat_btwn (show (r : ℝ) < r + ε by linarith)
  obtain ⟨b, hab, hbε⟩ := exists_rat_btwn haε
  have ha0 : (0 : ℝ) ≤ a := le_trans r.coe_nonneg hra.le
  obtain ⟨q, haq, hqb, hqH⟩ := hΓ.2 a b (by exact_mod_cast ha0) (by exact_mod_cast hab)
  refine ⟨(q : ℝ).toNNReal, hqH, ?_⟩
  have hq0 : (0 : ℝ) ≤ q := le_trans ha0 (by exact_mod_cast haq.le)
  rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_lt]
  have h1 : (a : ℝ) < q := by exact_mod_cast haq
  have h2 : (q : ℝ) < b := by exact_mod_cast hqb
  constructor <;> linarith

/-- **Tips through the flow's own chart and the inversion lie in a closed set containing the interior values.** -/
theorem mem_of_tipAt_loewner_inf {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : HasBdryLimits (fwdMapInv U T)) {W₂ : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace W₂ ⊤ Γ)
    (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = 0) (hdense : ∀ r : ℝ≥0, r ∈ closure {u : ℝ≥0 | Γ u ∈ H})
    {R : Set ℂ} (hR : IsClosed R) (hin : ∀ u : ℝ≥0, Γ u ∈ H → (Chart.id.loewner U T).2.1 (-(Γ u)⁻¹) ∈ R) :
    ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt W₂ r z → z ∈ R := by
  have hext := hasProperBdryExt_id.loewner hU hU0 hT hB
  have hcF : ∀ p ∈ Hbar, Tendsto (Chart.id.loewner U T).2.1 (𝓝[H] p)
      (𝓝 (extendFrom H (fwdMapInv U T) p)) := fun p hp => hB.tendsto hp
  intro r z hz
  by_cases hr : Γ r = 0
  · exfalso
    obtain ⟨f, C, hf, hC⟩ := hext
    have hU₂ : Continuous fun s : ℝ => W₂ s.toNNReal := hW₂.comp continuous_real_toNNReal
    have hU₂0 : (fun s : ℝ => W₂ s.toNNReal) 0 = 0 := by simpa using hW₂0
    have hF := hΓ.tendsto_fwdMapInv_mul_I hW₂.continuousOn hW₂0 (ENNReal.coe_lt_top (r := r))
    rw [hr] at hF
    set a : ℝ → ℂ := fun y => -(fwdMapInv (fun s : ℝ => W₂ s.toNNReal) r ((y : ℂ) * Complex.I))⁻¹ with ha
    have hmemH : ∀ y : ℝ, 0 < y → fwdMapInv (fun s : ℝ => W₂ s.toNNReal) r ((y : ℂ) * Complex.I) ∈ H :=
      fun y hy => QuantumZipper.RS.fwdMapInv_mem_H hU₂ hU₂0 (NNReal.coe_nonneg r)
        (show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)
    have haH : ∀ y : ℝ, 0 < y → a y ∈ H := fun y hy => GW2aPiece.neg_inv_mem_H (hmemH y hy)
    have hnorm0 : Tendsto (fun y : ℝ => ‖fwdMapInv (fun s : ℝ => W₂ s.toNNReal) r ((y : ℂ) * Complex.I)‖)
        (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using hF.norm
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact norm_pos_iff.2 (fun h0 => by
          have := hmemH y hy
          rw [h0] at this
          exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from this)))
    have hanorm : Tendsto (fun y => ‖a y‖) (𝓝[>] 0) atTop := by
      have := tendsto_inv_nhdsGT_zero.comp hnorm0
      refine this.congr fun y => ?_
      simp only [Function.comp_apply, ha, norm_neg, norm_inv]
    have hval : ∀ y : ℝ, 0 < y → (Chart.id.loewner U T).2.1 (a y) = f (a y) := fun y hy =>
      eq_of_tendsto_nhdsWithin_H (haH y hy) (hf _ (QuantumZipper.H_subset_Hbar (haH y hy)))
    have hbig : Tendsto (fun y => ‖(Chart.id.loewner U T).2.1 (a y)‖) (𝓝[>] 0) atTop := by
      refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C) hanorm)
      filter_upwards [self_mem_nhdsWithin] with y hy
      rw [hval y hy]
      have h1 := hC (a y) (QuantumZipper.H_subset_Hbar (haH y hy))
      have h2 : ‖a y‖ ≤ ‖f (a y)‖ + ‖f (a y) - a y‖ := by
        calc ‖a y‖ = ‖f (a y) - (f (a y) - a y)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖f (a y)‖ + ‖f (a y) - a y‖ := norm_sub_le _ _
      linarith
    exact not_tendsto_atTop_of_tendsto_nhds hz.norm hbig
  · have h1 := GW2aPiece.tipAt_trans_of_ne_zero hcF hΓ hW₂ hW₂0 hr
    rw [Chart.tipAt_unique hz h1]
    have hfc := GW1P.continuousOn_of_tendsto hcF
    have hΓc : Continuous Γ := by
      have := hΓ.2.1
      simp only [le_top, ofPred_true] at this
      exact continuousOn_univ.1 this
    have hmem : ∀ u, -(Γ u)⁻¹ ∈ Hbar := fun u =>
      GW2aPiece.neg_inv_mem_Hbar (GW2aPiece.trace_mem_Hbar hΓ hW₂ hW₂0 u)
    have hgc : ContinuousAt (fun u => -(Γ u)⁻¹) r := (hΓc.continuousAt.inv₀ hr).neg
    have hlim : Tendsto (fun u => extendFrom H (fwdMapInv U T) (-(Γ u)⁻¹)) (𝓝 r)
        (𝓝 (extendFrom H (fwdMapInv U T) (-(Γ r)⁻¹))) :=
      (hfc _ (hmem r)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hgc, Eventually.of_forall hmem⟩)
    have hNe : (𝓝[{u : ℝ≥0 | Γ u ∈ H}] r).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hdense r)
    refine hR.mem_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s := {u : ℝ≥0 | Γ u ∈ H}))) ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have huH : -(Γ u)⁻¹ ∈ H := GW2aPiece.neg_inv_mem_H hu
    rw [← eq_of_tendsto_nhdsWithin_H huH (hcF _ (QuantumZipper.H_subset_Hbar huH))]
    exact hin u hu

end BRLeaf

end Theorem14

end InteractingSLE
