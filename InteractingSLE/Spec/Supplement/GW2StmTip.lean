/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1DetWitness
import InteractingSLE.Spec.Supplement.BRLeafTips
import InteractingSLE.Spec.Supplement.BW1DetPhys
import InteractingSLE.Spec.Supplement.GB6Past

/-!
# GW2's stage step, part 7: GB6's interior identity gives the tip relation of the launch datum

Packet PROVE-GW2-STAGEMEAN, round 2. GB6's chart continuation (`GW2Stm.exists_prefixPairEq`) identifies the physical
counterflow with the conditional one at the relative times whose relative trace point is interior. The launch datum
`GW2TipSystem.HasLaunchPairEq` asks the tip relation at EVERY time, through the piece's Loewner chart and the
inversion. Interior times are dense (`BRLeaf.mem_closure_setOf_mem_H`), and the relation passes to limits for a chart
with a proper boundary extension (the argument of `BW1Det.tipRel_of_rat`, on a dense set of times instead of the
rational ones):

* **`tipRel_of_dense`**: `BW1Det.tipRel_of_rat` with an arbitrary dense set of times;
* **`tipAt_loewner_iff_of_interior`**: for the Loewner chart `Chart.id.loewner U T` of a piece with boundary limits,
  if `−1/γ(ℓ u) = c⁻¹(−1/Γ(u))` at every `u` with `Γ u ∈ ℍ` (GB6's identity), interior times are dense and `ℓ` is
  continuous, then the tips of the new driver through the chart and the inversion are exactly the tips of the old
  counterflow at the changed times;
* **`tipAt_loewner_trans_iff`**: the relation composes through a launch chart `d` with a proper boundary extension:
  if the tips of `W₂` through the piece's Loewner chart are those of `Wk` at `ℓ₂`, and the tips of `Wk` through `d`
  are those of `W'` at `ℓk`, then the tips of `W₂` through `d.loewner U T` are those of `W'` at `ℓk ∘ ℓ₂` (the launch
  chart of the next piece; `BW1Det.tipAt_trans_trans_iff`).

Deterministic. Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.GW2Stm

open WangWu (negInv)

/-- **The tip relation on a dense set of times extends to every time** (`BW1Det.tipRel_of_rat` with a dense set). -/
theorem tipRel_of_dense {f : ℂ → ℂ} {C : ℝ} (hfc : ContinuousOn f Hbar) (hC : ∀ p ∈ Hbar, ‖f p - p‖ ≤ C)
    {Γ δ : ℝ≥0 → ℂ} (hΓc : Continuous Γ) (hδc : Continuous δ) (hΓH : ∀ r, Γ r ∈ Hbar) {D : Set ℝ≥0}
    (hD : ∀ r, r ∈ closure D)
    (h : ∀ q ∈ D, (Γ q = 0 ↔ δ q = 0) ∧ (Γ q ≠ 0 → f (negInv (Γ q)) = negInv (δ q))) (r : ℝ≥0) :
    (Γ r = 0 ↔ δ r = 0) ∧ (Γ r ≠ 0 → f (negInv (Γ r)) = negInv (δ r)) := by
  obtain ⟨qs, hqsD, hqs⟩ := mem_closure_iff_seq_limit.1 (hD r)
  have hΓlim : Tendsto (fun m => Γ (qs m)) atTop (𝓝 (Γ r)) := (hΓc.tendsto r).comp hqs
  have hδlim : Tendsto (fun m => δ (qs m)) atTop (𝓝 (δ r)) := (hδc.tendsto r).comp hqs
  have hnegH : ∀ m, negInv (Γ (qs m)) ∈ Hbar := fun m => GW4Traverse.negInv_mem_Hbar (hΓH _)
  have hlow : ∀ m, ‖negInv (Γ (qs m))‖ - C ≤ ‖f (negInv (Γ (qs m)))‖ := fun m => by
    have h1 := hC _ (hnegH m)
    have h2 := norm_sub_norm_le (negInv (Γ (qs m))) (f (negInv (Γ (qs m))))
    rw [norm_sub_rev] at h2
    linarith
  by_cases ha : Γ r = 0
  · have hb : δ r = 0 := by
      by_contra hb
      have hev : ∀ᶠ m in atTop, δ (qs m) ≠ 0 := hδlim.eventually_ne hb
      have hev' : ∀ᶠ m in atTop, Γ (qs m) ≠ 0 :=
        hev.mono fun m hm h0 => hm ((h (qs m) (hqsD m)).1.1 h0)
      have hconv : Tendsto (fun m => f (negInv (Γ (qs m)))) atTop (𝓝 (negInv (δ r))) := by
        refine ((hδlim.inv₀ hb).neg).congr' ?_
        filter_upwards [hev'] with m hm
        exact ((h (qs m) (hqsD m)).2 hm).symm
      have h1 := BW1Det.tendsto_norm_negInv_atTop (by rwa [ha] at hΓlim) hev'
      have hinf : Tendsto (fun m => ‖f (negInv (Γ (qs m)))‖) atTop atTop :=
        tendsto_atTop_mono hlow (tendsto_atTop_add_const_right _ (-C) h1)
      exact not_tendsto_atTop_of_tendsto_nhds hconv.norm hinf
    exact ⟨iff_of_true ha hb, fun h' => absurd ha h'⟩
  · have hev : ∀ᶠ m in atTop, Γ (qs m) ≠ 0 := hΓlim.eventually_ne ha
    have hconv : Tendsto (fun m => f (negInv (Γ (qs m)))) atTop (𝓝 (f (negInv (Γ r)))) :=
      (hfc _ (GW4Traverse.negInv_mem_Hbar (hΓH r))).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨(hΓlim.inv₀ ha).neg, Eventually.of_forall hnegH⟩)
    have hconv' : Tendsto (fun m => negInv (δ (qs m))) atTop (𝓝 (f (negInv (Γ r)))) := by
      refine hconv.congr' ?_
      filter_upwards [hev] with m hm
      exact (h (qs m) (hqsD m)).2 hm
    have hb : δ r ≠ 0 := by
      intro hb
      have hev2 : ∀ᶠ m in atTop, δ (qs m) ≠ 0 :=
        hev.mono fun m hm h0 => hm ((h (qs m) (hqsD m)).1.2 h0)
      have hinf := BW1Det.tendsto_norm_negInv_atTop (by rwa [hb] at hδlim) hev2
      exact not_tendsto_atTop_of_tendsto_nhds hconv'.norm hinf
    exact ⟨iff_of_false ha hb, fun _ => tendsto_nhds_unique hconv' (hδlim.inv₀ hb).neg⟩

/-- **GB6's interior identity gives the launch datum's tip relation** through the piece's Loewner chart and the
inversion, at every time. -/
theorem tipAt_loewner_iff_of_interior {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hB : HasBdryLimits (fwdMapInv U T)) {W₂ Wk : ℝ≥0 → ℝ} {Γ γ : ℝ≥0 → ℂ}
    (hΓ : IsGeneratingTrace W₂ ⊤ Γ) (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = 0)
    (hγ : IsGeneratingTrace Wk ⊤ γ) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0)
    (hdense : ∀ r : ℝ≥0, r ∈ closure {u : ℝ≥0 | Γ u ∈ H}) {ℓ : ℝ≥0 → ℝ≥0} (hℓ : Continuous ℓ)
    (hid : ∀ u : ℝ≥0, Γ u ∈ H →
      Supp8.GB6.sphereInv (γ (ℓ u) : OnePoint ℂ) = (((Chart.id.loewner U T).2.1 (-(Γ u)⁻¹) : ℂ) : OnePoint ℂ)) :
    ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt W₂ r z ↔
      infinitySourceChart.tipAt Wk (ℓ r) z := by
  obtain ⟨f, C, hf, hC⟩ := BRLeaf.hasProperBdryExt_id.loewner hU hU0 hT hB
  have hΓc : Continuous Γ := by
    have := hΓ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  intro r z
  revert z
  refine (BW1Det.tipRel_iff_traces hf hC hΓ hW₂ hW₂0 hγ hWk hWk0 r (ℓ r)).2 ?_
  refine tipRel_of_dense (δ := fun u => γ (ℓ u)) (GW1P.continuousOn_of_tendsto hf) hC hΓc (hγc.comp hℓ)
    (GW2aPiece.trace_mem_Hbar hΓ hW₂ hW₂0) hdense (fun q hq => ?_) r
  have hq0 : Γ q ≠ 0 := Supp8.GB6.ne_zero_of_mem_H hq
  have hnH : negInv (Γ q) ∈ H := GW2aPiece.neg_inv_mem_H hq
  have hfq : f (negInv (Γ q)) = (Chart.id.loewner U T).2.1 (-(Γ q)⁻¹) :=
    (GW2Later.eq_of_tendsto_nhdsWithin_H hnH (hf _ (QuantumZipper.H_subset_Hbar hnH))).symm
  have hidq := hid q hq
  by_cases hγ0 : γ (ℓ q) = 0
  · exfalso
    rw [hγ0] at hidq
    simp only [Supp8.GB6.sphereInv_coe, ↓reduceIte] at hidq
    exact OnePoint.infty_ne_coe _ hidq
  rw [Supp8.GB6.sphereInv_coe_of_ne hγ0] at hidq
  refine ⟨iff_of_false hq0 hγ0, fun _ => ?_⟩
  rw [hfq]
  exact (OnePoint.coe_injective hidq).symm

/-- **The tip relation composes through a launch chart with a proper boundary extension.** -/
theorem tipAt_loewner_trans_iff {d : Chart} (hd : GW1P.HasProperBdryExt d) {U : ℝ → ℝ} (hU : Continuous U)
    (hU0 : U 0 = 0) {T : ℝ} (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv U T)) {W₂ Wk W' : ℝ≥0 → ℝ}
    {Γ γk : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace W₂ ⊤ Γ) (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = 0)
    (hγk : IsGeneratingTrace Wk ⊤ γk) (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) {ℓ₂ ℓk : ℝ≥0 → ℝ≥0}
    (h₂ : ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner U T).trans infinitySourceChart).tipAt W₂ r z ↔
      infinitySourceChart.tipAt Wk (ℓ₂ r) z)
    (hk : ∀ (r : ℝ≥0) (z : ℂ), (d.trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓk r) z) :
    ∀ (r : ℝ≥0) (z : ℂ), ((d.loewner U T).trans infinitySourceChart).tipAt W₂ r z ↔
      infinitySourceChart.tipAt W' (ℓk (ℓ₂ r)) z := by
  obtain ⟨f, C, hf, hC⟩ := hd
  obtain ⟨g, C', hg, hC'⟩ := BRLeaf.hasProperBdryExt_id.loewner hU hU0 hT hB
  have heH : ∀ w ∈ H, (Chart.id.loewner U T).2.1 w ∈ H := fun w hw =>
    QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hT hw
  intro r z
  rw [Chart.loewner_eq_trans, BW1Det.tipAt_trans_trans_iff hf hC hg hC' heH hΓ hW₂ hW₂0, ← hk,
    GW1Det.tipAt_trans_iff_exists hf hC hγk hWk hWk0]
  simp_rw [h₂]

end InteractingSLE.Theorem14.GW2Stm
