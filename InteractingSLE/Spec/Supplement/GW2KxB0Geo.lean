/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxGeom
import InteractingSLE.Spec.Supplement.GW2KbNil
import InteractingSLE.Spec.Supplement.GW2KbRead

/-!
# The root piece's stage geometry at a root `x`, from the root's start (launch chart `recenter x`)

Packet PROVE-GW2-GEOM2, round 14 (D49), for the base of Claim(k) at a root `x`. The root piece is launched at index `0`
in the chart `Chart.id.recenter x` (`w ↦ w + x`), with BR4a's datum (the counterflow targeted at `x`, `Wk`, and the
clock `ℓ` up to the first tip at `x`). Its stage is read from the root's start: the stage chart is
`stgChart (relChartX x s rec) R 0` and the union at stage time `u` is RELDET's `schedUnionX c r [] a 0 u` (the
counterflow's retained hull and the explored hull up to `u`, translated by `x`).

* `den_of_lt_firstTipTime_pt`, `pole_of_lt_firstTipTime_pt`: before the first tip at `x`, the counterflow is off the
  pole `−1/x`, and so is its closed hull (with the visit);
* `coe_dom_recenter_id`, **`cont_root0X`**: the continuation `cL⁻¹ '' invHull Wk q = invHull W' (ℓ q)` at every `q`
  (round 11's `GW2Xk.chartInv_image_invHullX` with the zero driver at time `0`);
* `union_root0X`: the launch image of the stage union is `invHull Wk t₀ ∪ K^{expl}_u`;
* **`sample_stage_geom0X`**: the dilation `relMap (Wk, t₀) ∘ cL.1 = λ · cs.1` on `cs.dom = ℍ ∖ B 0`, `cs.dom ⊆ ℍ`,
  `cL.1` off the retained hull, and the driver relation (`GW2Omx.kernel_dilation`, `GW2Omx.sample_driver_scale`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean GW2Xk GW2Kb
open Supp8.GB6 (relMap gb6Rec relClock)
open Supp8.Q3Rel (invHull)
open Sec5.CrossRestart (mobPole)

/-- **Before the first tip at `x`, the counterflow is off `−1/x`.** -/
theorem den_of_lt_firstTipTime_pt {W' : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace W' ⊤ η)
    (hc : Continuous W') (h0 : W' 0 = 0) {x : ℝ} {σ : ℝ≥0}
    (hσ : (σ : ℝ≥0∞) < firstTipTime infinitySourceChart W' {(x : ℂ)}) : ∀ u ≤ σ, (x : ℂ) * η u + 1 ≠ 0 := by
  intro u hu hzero
  have hγt : η u ≠ 0 := by
    intro h0'
    rw [h0', mul_zero, zero_add] at hzero
    exact one_ne_zero hzero
  refine noContact_of_lt_firstTipTime hη hc h0 hσ hu hγt (Set.mem_singleton_iff.2 ?_)
  have e : (x : ℂ) * η u = -1 := eq_neg_of_add_eq_zero_left hzero
  calc -(η u)⁻¹ = -(η u)⁻¹ * 1 := by ring
    _ = -(η u)⁻¹ * (-((x : ℂ) * η u)) := by rw [e]; ring
    _ = (x : ℂ) * ((η u)⁻¹ * η u) := by ring
    _ = (x : ℂ) := by rw [inv_mul_cancel₀ hγt, mul_one]

/-- **With the visit to `x > 0`, before the first tip at `x` the pole `−1/x` is off the closed counterflow hull.** -/
theorem pole_of_lt_firstTipTime_pt {W' : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace W' ⊤ η)
    (hc : Continuous W') (h0 : W' 0 = 0) {x : ℝ} {σ : ℝ≥0}
    (hσ : (σ : ℝ≥0∞) < firstTipTime infinitySourceChart W' {(x : ℂ)})
    (hvis : 0 < x → ∃ τ, (x : ℂ) * η τ + 1 = 0) :
    0 < x → ((mobPole x 1 : ℝ) : ℂ) ∉ closure (fwdHull (fun r : ℝ => W' r.toNNReal) (σ : ℝ)) := by
  intro hx
  obtain ⟨τ, hτ⟩ := hvis hx
  exact pole_notMem_closure_of_visit hη hc h0 hx (den_of_lt_firstTipTime_pt hη hc h0 hσ) hτ

/-- `Chart.id.recenter x` has domain `ℍ`. -/
theorem coe_dom_recenter_id (x : ℝ) : ((Chart.id.recenter x).dom : Set ℂ) = H := by
  rw [(Chart.isConformal_id.recenter x).coe_dom]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change 0 < (w + (x : ℂ)).im
    have : 0 < w.im := hw
    simpa using this
  · intro hz
    refine ⟨z - (x : ℂ), ?_, ?_⟩
    · change 0 < (z - (x : ℂ)).im
      have : 0 < z.im := hz
      simpa using this
    · change z - (x : ℂ) + (x : ℂ) = z
      ring

/-- **The continuation through `recenter x` at every `q`** (from the clock's range up to the first tip at `x`). -/
theorem cont_root0X {x : ℝ} (hx0 : 0 ≤ x) {Wk W' : ℝ≥0 → ℝ} {γk γ' : ℝ≥0 → ℂ} (hWk : Continuous Wk)
    (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk) (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hγ' : IsGeneratingTrace W' ⊤ γ') {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart W' {(x : ℂ)}})
    (hvis : 0 < x → ∃ τ, (x : ℂ) * γ' τ + 1 = 0)
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.recenter x).trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z) (q : ℝ≥0) :
    (Chart.id.recenter x).2.1 '' invHull (fun r : ℝ => Wk r.toNNReal) (q : ℝ) =
      invHull (fun r : ℝ => W' r.toNNReal) (ℓ q : ℝ) := by
  have hσ : ((ℓ q : ℝ≥0) : ℝ≥0∞) < firstTipTime infinitySourceChart W' {(x : ℂ)} := by
    have h : ℓ q ∈ range ℓ := ⟨q, rfl⟩
    rw [hℓr] at h
    exact h
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  have hinv : ∀ w ∈ H, (Chart.id.recenter x).2.1 w = (x : ℂ) + fwdMapInv (fun _ : ℝ => (0 : ℝ)) 0 w := by
    intro w hw
    rw [fwdMapInv_zero_time continuous_const rfl hw]
    change w + (x : ℂ) = _
    ring
  refine chartInv_image_invHullX hx0 continuous_const rfl le_rfl hinv (GW1P.hasProperBdryExt_recenter_id x) hWk
    hWk0 hγk hW' hW'0 hγ' hℓc hℓm.monotone hℓ0 hiff (den_of_lt_firstTipTime_pt hγ' hW' hW'0 hσ)
    (pole_of_lt_firstTipTime_pt hγ' hW' hW'0 hσ hvis) ?_
  rw [fwdHull_zero_eq_empty continuous_const rfl, image_empty, closure_empty]
  exact Set.empty_disjoint _

/-- **The launch image of the root piece's stage union** (on the history's success). -/
theorem union_root0X {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)
    {ω : Ω} (hold : oldSuccess c r [] ω) (hW'0 : c.W 0 ω = 0) (hW'c : Continuous fun u => c.W u ω)
    (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) {Wk : ℝ≥0 → ℝ} (hWk : Continuous Wk) {t₀ : ℝ≥0}
    (hcont : (Chart.id.recenter (rootPt r.1)).2.1 '' invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) =
      invHull (fun u : ℝ => c.W u.toNNReal ω) c.s) (u : ℝ≥0) :
    (Chart.id.recenter (rootPt r.1)).1 '' (GW2Rd.schedUnionX c r [] a 0 u ω ∩
        ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ)) =
      invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) ∪ fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) u := by
  set x := rootPt r.1 with hx
  set cL := Chart.id.recenter x with hcL
  have hconf : cL.IsConformal := Chart.isConformal_id.recenter x
  have hWkc : Continuous fun r : ℝ => Wk r.toNNReal := hWk.comp continuous_real_toNNReal
  have e1 : GW2Rd.schedUnionX c r [] a 0 u ω = invHull (fun u : ℝ => c.W u.toNNReal ω) c.s ∪
      (fun z : ℂ => (x : ℂ) + z) '' fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) u := by
    rw [← Supp8.RelSafeS.invHull_record_eq hW'0 hW'c.continuousOn hsζ]
    simp only [GW2Rd.schedUnionX, GW2Rd.schedHullX, hold, ↓reduceIte, GW2Rd.schedHull, zero_add]
    rfl
  have hBH : GW2Rd.schedUnionX c r [] a 0 u ω ⊆ H := (GW2Rd.schedUnionX_subset_isOpen c r [] a 0 u ω).1
  rw [coe_dom_recenter_id x, inter_eq_left.2 hBH, e1, image_union]
  congr 1
  · rw [← hcont, image_image]
    have hsub : invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) ⊆ H := GW2Shr.invHull_subset_H hWkc t₀.coe_nonneg
    conv_rhs => rw [← image_id (invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ))]
    exact image_congr fun w hw => hconf.2.2 w (hsub hw)
  · rw [image_image]
    conv_rhs => rw [← image_id (fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) u)]
    refine image_congr fun z _ => ?_
    change (x : ℂ) + z - (x : ℂ) = z
    ring

end InteractingSLE.Theorem14.GW2Kx
