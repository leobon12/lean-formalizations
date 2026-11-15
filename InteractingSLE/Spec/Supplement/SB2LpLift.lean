/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LuLift
import InteractingSLE.Spec.Supplement.SB2LkDom

/-!
# SB2(2)'s lift relation in intrinsic form (independent of the parametrization and the lift curve)

Packet PROVE-SB2-LIFTSET (round 2). `SB2LowerRelWalkRangeStatement` asks for ONE measurable family of relative drivers
`EL` that works for **every** proper parametrization `β₀` of the actual walk and **every** lift curve `γ` of its tail.
The per-launch lift relation `LiftRel β₀ t_L γ` of `SB2LuLift` mentions `β₀` and `γ`. This file removes them: through
the chart `c` (domain `D = c⁻¹ '' ℍ = ℍ ∖ fill A`) a physical point `p ∈ D` has the intrinsic lift
`liftPt c m p = c.1 p + m` in the relative frame, and

* **`lift_mem_H_iff`**: the lift curve satisfies `β₀ (t_L + s) ∈ D ↔ γ s − m ∈ ℍ`, and then
  `γ s = liftPt c m (β₀ (t_L + s))` (continuity of `c⁻¹` on `ℍ`, its left inverse `c.1`, and **`BdryOff`**: boundary
  values of `c⁻¹` at real points lie off `D`, from `ext_notMem_image` via `bdryOff_of_ext`);
* **`liftImage_eq_closure`**: if the tail times in `S` are compact (`isCompact_tail_times` for compact `S`) and the
  times in `S ∩ D` are dense among them, the lift image of `S` is `closure (liftPt c m '' (S ∩ D ∩ β₀ '' [t_L, ∞)))`;
* **`liftRel_of_closure`**: hence `LiftRel β₀ t_L γ q₁ q₂` holds as soon as the relative piece's physical points are
  the closure of the intrinsic lift of the actual piece's points in `D` on the tail.

For the actual pieces after the start (which lie on the tail) the target of the construction of `EL` is therefore the
intrinsic identity `tipSet q₂ = closure (liftPt c m '' (tipSet q₁ ∩ D))`, the same for every `β₀` and `γ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

/-- **Boundary values of `c⁻¹` at real points lie off its image** `D = c⁻¹ '' ℍ`. -/
def BdryOff (c : Chart) : Prop :=
  ∀ w : ℂ, w.im = 0 → ∀ z : ℂ, Tendsto c.2.1 (𝓝[H] w) (𝓝 z) → z ∉ c.2.1 '' H

/-- `BdryOff` for a conformal chart with a continuous boundary extension (`ext_notMem_image`). -/
theorem bdryOff_of_ext {c : Chart} {ĝ : ℂ → ℂ} (hc : c.IsConformal) (hĝ : ContinuousOn ĝ Hbar)
    (hgg : EqOn ĝ c.2.1 H) (hlim : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q))) : BdryOff c := by
  intro w hw z hz
  have hwH : w ∈ Hbar := show 0 ≤ w.im by rw [hw]
  have : (𝓝[H] w).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
    exact hwH
  have hzw : ĝ w = z := tendsto_nhds_unique (hlim w hwH) hz
  have hinj : InjOn c.2.1 H := fun a ha a' ha' e => by rw [← hc.2.2 a ha, e, hc.2.2 a' ha']
  rw [← hzw]
  exact ext_notMem_image hc.1 hinj hĝ hgg hwH (fun h => by
    have : (0 : ℝ) < w.im := h
    rw [hw] at this
    exact lt_irrefl _ this)

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- The intrinsic lift of a physical point through the chart, read in the relative frame. -/
def liftPt (c : Chart) (m : ℝ) (p : ℂ) : ℂ := c.1 p + (m : ℂ)

/-- **The lift curve is the intrinsic lift exactly where the tail is in `D = c⁻¹ '' ℍ`**: `β₀ (t_L + s) ∈ D` iff
`γ s − m ∈ ℍ`, and then `γ s = c.1 (β₀ (t_L + s)) + m`. -/
theorem lift_mem_H_iff (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) (s : ℝ≥0) :
    (β₀ (tL + s) ∈ c.2.1 '' H ↔ γ s - m ∈ H) ∧ (γ s - m ∈ H → γ s = liftPt c m (β₀ (tL + s))) := by
  have hT := hγ.2.2.2 s
  have hw : 0 ≤ (γ s - (m : ℂ)).im := by simpa using hγ.2.1.2.2.1 s
  have hin : γ s - m ∈ H → β₀ (tL + s) = c.2.1 (γ s - m) := fun hH => by
    have : (𝓝[H] (γ s - (m : ℂ))).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot]; exact subset_closure hH
    exact tendsto_nhds_unique hT ((hcH _ hH).mono_left le_rfl)
  refine ⟨⟨fun hD => ?_, fun hH => ⟨_, hH, (hin hH).symm⟩⟩, fun hH => ?_⟩
  · by_contra hnot
    have him : (γ s - (m : ℂ)).im = 0 := le_antisymm (not_lt.1 hnot) hw
    exact hoff _ him _ hT hD
  · rw [liftPt, hin hH, hc1 _ hH, sub_add_cancel]

/-- **The lift image as the closure of the intrinsic lift** (independent of `β₀`, `γ`): if the tail times in `S` form
a compact set in whose closure the times in `S ∩ D` are dense, the lift image of `S` is the closure of the intrinsic
lift of the points of `S ∩ D` on the tail. -/
theorem liftImage_eq_closure (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {S : Set ℂ}
    (hTc : IsCompact {s | β₀ (tL + s) ∈ S})
    (hdense : {s | β₀ (tL + s) ∈ S} ⊆ closure {s | β₀ (tL + s) ∈ S ∩ c.2.1 '' H}) :
    liftImage β₀ tL γ S = closure (liftPt c m '' (S ∩ c.2.1 '' H ∩ β₀ '' Ici tL)) := by
  set T := {s | β₀ (tL + s) ∈ S} with hTdef
  set G := {s | β₀ (tL + s) ∈ S ∩ c.2.1 '' H} with hGdef
  have hγc : Continuous γ := hγ.2.1.1
  have hGT : G ⊆ T := fun s hs => hs.1
  have hGimg : γ '' G = liftPt c m '' (S ∩ c.2.1 '' H ∩ β₀ '' Ici tL) := by
    ext z
    constructor
    · rintro ⟨s, ⟨hsS, hsD⟩, rfl⟩
      have hH := (lift_mem_H_iff hγ hcH hc1 hoff s).1.1 hsD
      refine ⟨β₀ (tL + s), ⟨⟨hsS, hsD⟩, tL + s, mem_Ici.2 (le_add_of_nonneg_right zero_le), rfl⟩, ?_⟩
      exact ((lift_mem_H_iff hγ hcH hc1 hoff s).2 hH).symm
    · rintro ⟨_, ⟨⟨hpS, hpD⟩, t, ht, rfl⟩, rfl⟩
      obtain ⟨s, rfl⟩ : ∃ s, t = tL + s := ⟨t - tL, (add_tsub_cancel_of_le (mem_Ici.1 ht)).symm⟩
      have hH := (lift_mem_H_iff hγ hcH hc1 hoff s).1.1 hpD
      exact ⟨s, ⟨hpS, hpD⟩, (lift_mem_H_iff hγ hcH hc1 hoff s).2 hH⟩
  unfold liftImage
  rw [← hGimg]
  refine Subset.antisymm ?_ ((hTc.image hγc).isClosed.closure_subset_iff.2 (image_mono hGT))
  calc γ '' T ⊆ γ '' closure G := image_mono hdense
    _ ⊆ closure (γ '' G) := image_closure_subset_closure_image hγc

/-- **The lift relation from the intrinsic lift**: the relative piece is the closure of the intrinsic lift of the
actual piece's points in `D` on the tail, the tail times of the actual piece are compact and the times in `D` dense
among them. -/
theorem liftRel_of_closure (hγ : IsTailLiftCurve c R m β₀ tL γ) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {q₁ q₂ : Pc}
    (hTc : IsCompact {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2})
    (hdense : {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2} ⊆
      closure {s | β₀ (tL + s) ∈ q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H})
    (hq : q₂.1.tipSet q₂.2.1 q₂.2.2 =
      closure (liftPt c m '' (q₁.1.tipSet q₁.2.1 q₁.2.2 ∩ c.2.1 '' H ∩ β₀ '' Ici tL))) :
    LiftRel β₀ tL γ q₁ q₂ := by
  unfold LiftRel
  rw [hq, liftImage_eq_closure hγ hcH hc1 hoff hTc hdense]

/-- The tail times of a compact set are compact (`β₀` proper). -/
theorem isCompact_tail_times (hβ : Supp9B.IsProperCurve β₀) {S : Set ℂ} (hS : IsCompact S) :
    IsCompact {s | β₀ (tL + s) ∈ S} := by
  have he := isClosedEmbedding_of_isProperCurve hβ
  have hK := he.isCompact_preimage hS
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact hS.isClosed.preimage (hβ.1.comp (continuous_const.add continuous_id))
  · refine (Metric.isBounded_closedBall (x := (0 : ℝ≥0)) (r := M)).subset fun s hs => ?_
    have h1 := hM (show tL + s ∈ β₀ ⁻¹' S from hs)
    simp only [Metric.mem_closedBall, NNReal.dist_eq, NNReal.coe_zero, sub_zero, NNReal.abs_eq] at h1 ⊢
    have : (s : ℝ) ≤ (tL : ℝ) + s := le_add_of_nonneg_left tL.2
    push_cast at h1
    linarith

end InteractingSLE.Theorem14.SB.Lk
