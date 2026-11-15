/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdsTip
import InteractingSLE.Spec.Supplement.GW2NtInt

/-!
# The near structure (N3), step G: interior physical tips give strict junctions in the root-`x` chart

Packet PROVE-GW2-SDE (round 18). One sample, at a root `x`, with a root-`x` version `R` (`GW2Rz.VersionAtX`). The
version is generated up to the clock of a time before the contact and below its stop by the re-centred relative image
of the explored trace (NOTHR's `GW2Nt.isGeneratingTrace_versionX`, `capacityTip_clock_eq`). Hence:

* **`junctions_strict_versionX`**: if the explored point `γ T` is in `ℍ`, the record `recOf (clock T) (R, ⊤)` has both
  junctions strictly off the tip;
* **`relTip_mem_diff_versionX`**: if `γ τ` is an interior point of `ℍ \ K_T` (`T < τ`), the relative tip at the clock
  of `τ` is an interior point of `ℍ \ K'_{clock T}` (the relative hull at the clock of `T` is the chart image of the
  physical hull, the chart is injective on its domain; NOTHR's argument);
* **`junctions_strict_stgRec_versionX`**: then the stage piece of `R` between the two clocks has both junctions off the
  tip.

Deterministic, one sample; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Sds

open Restart Exist Exist.StagedLaw Supp8.GB6 Supp8.GB6.CoordB GW2TipSystem GW2Rz MartChar.RealFlow

section Interior

variable {Ω : Type*} {x : ℝ} {s : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {w : ℝ≥0 → Ω → ℝ}
  {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} (hGT : ∀ ω ∈ GT, PhysGoodX x s W' ζ' w γ α ω) (hs : 0 < s) (hx : 0 ≤ x)

include hGT hs hx

/-- **The relative tip at the clock of `τ` is in `ℍ`** when the explored point `γ τ` is. -/
theorem relTip_mem_H_versionX {ω : Ω} (hω : ω ∈ GT) {τ : ℝ≥0} (hτc : (τ : ℝ≥0∞) < contactX x s γ α ω)
    (hH : γ ω τ ∈ H) :
    RootI30.capacityTipRead x s τ (clockX x s W' ζ' w τ ω).toNNReal (recPair s W' ζ' w τ ω) ∈ H := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  have he := Gm.isRegularDriver_top hwc hw0
  have hv : (τ : ℝ≥0∞) < min (contactX x s γ α ω) ((fun t => w t ω), (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]; exact hτc
  set U := rdrv (cfRec s W' ζ' ω) with hU
  have hUc : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hsafe := RootH29.trace_mem_record_relSafe W' ζ' ω hα hW hW0 hζ hx harc he hγ hv le_rfl
  have hsafe0 := RootH29.trace_mem_record_relSafe W' ζ' ω hα hW hW0 hζ hx harc he hγ hv (t := 0) zero_le
  rw [hγ.1, add_zero] at hsafe0
  have hzH : (x : ℂ) + γ ω τ ∈ H := by
    change 0 < (γ ω τ).im at hH
    change 0 < ((x : ℂ) + γ ω τ).im
    simpa using hH
  have hbx : (relBdry U s x).im = 0 := im_relBdry_of_real hUc hU0 s.coe_nonneg hsafe0.2
  rw [GW2Nt.capacityTip_clock_eq hGT hs hx hω hτc le_rfl]
  have h1 := (relBdry_mem_H_iff hUc hU0 s.coe_nonneg hsafe).2 hzH
  change 0 < (relBdry U s ((x : ℂ) + γ ω τ) - relBdry U s x).im
  rw [Complex.sub_im, hbx, sub_zero]
  exact h1

/-- **An explored point in `ℍ` gives strict junctions of the version's record at its clock.** -/
theorem junctions_strict_versionX {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT)
    (hR : VersionAtX x s W' ζ' w γ α R V ω) {T : ℝ≥0} (hTc : (T : ℝ≥0∞) < contactX x s γ α ω)
    (hTV : ENNReal.ofReal (clockX x s W' ζ' w T ω) ≤ V ω) (hH : γ ω T ∈ H) :
    markPosL (rdrv (recOf (((clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, ⊤)))
        (rtime (recOf (((clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, ⊤))) 0 < 0 ∧
      0 < markPos (rdrv (recOf (((clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, ⊤)))
        (rtime (recOf (((clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) : ℝ≥0∞) (fun u => R u ω, ⊤))) 0 := by
  have hB := GW2Nt.isGeneratingTrace_versionX hGT hs hx hω hR hTc hTV
  obtain ⟨hRc, hR0, -⟩ := hR
  exact junctions_strict_recOf hRc hR0 hB (relTip_mem_H_versionX hGT hs hx hω hTc hH)

/-- **The relative tip over an interior point of the physical `ℍ \ K_T`** is an interior point of the relative
`ℍ \ K'` at the clock of `T`. -/
theorem relTip_mem_diff_versionX {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT)
    (hR : VersionAtX x s W' ζ' w γ α R V ω) {T τ : ℝ≥0} (hTτ : T < τ) (hτc : (τ : ℝ≥0∞) < contactX x s γ α ω)
    (hτV : ENNReal.ofReal (clockX x s W' ζ' w τ ω) ≤ V ω)
    (hmem : γ ω τ ∈ H \ fwdHull (fun r : ℝ => w r.toNNReal ω) T) :
    RootI30.capacityTipRead x s τ (clockX x s W' ζ' w τ ω).toNNReal (recPair s W' ζ' w τ ω) ∈
      H \ fwdHull (fun r : ℝ => R r.toNNReal ω) ((clockX x s W' ζ' w T ω).toNNReal : ℝ) := by
  refine ⟨relTip_mem_H_versionX hGT hs hx hω hτc hmem.1, fun hK => ?_⟩
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  obtain ⟨-, -, hhull⟩ := hR
  have he := Gm.isRegularDriver_top hwc hw0
  have hv : (τ : ℝ≥0∞) < min (contactX x s γ α ω) ((fun t => w t ω), (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]; exact hτc
  obtain ⟨-, hmono, -⟩ := clock_props W' ζ' ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hTc : (T : ℝ≥0∞) < contactX x s γ α ω := (ENNReal.coe_lt_coe.2 hTτ).trans hτc
  have hTτ' : clockX x s W' ζ' w T ω < clockX x s W' ζ' w τ ω := hmono hTc hτc hTτ
  have hT0 : 0 ≤ clockX x s W' ζ' w T ω := RootH29.forwardCapacity_nonneg _ _ _ _
  have hTV : ENNReal.ofReal (clockX x s W' ζ' w T ω) ≤ V ω :=
    (ENNReal.ofReal_le_ofReal hTτ'.le).trans hτV
  set U := rdrv (cfRec s W' ζ' ω) with hU
  have hUc : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hsafe := RootH29.trace_mem_record_relSafe W' ζ' ω hα hW hW0 hζ hx harc he hγ hv le_rfl
  have hsafe0 := RootH29.trace_mem_record_relSafe W' ζ' ω hα hW hW0 hζ hx harc he hγ hv (t := 0) zero_le
  rw [hγ.1, add_zero] at hsafe0
  have hzH : (x : ℂ) + γ ω τ ∈ H := by
    have h := hmem.1
    change 0 < (γ ω τ).im at h
    change 0 < ((x : ℂ) + γ ω τ).im
    simpa using h
  have hbx : (relBdry U s x).im = 0 := im_relBdry_of_real hUc hU0 s.coe_nonneg hsafe0.2
  rw [GW2Nt.capacityTip_clock_eq hGT hs hx hω hτc le_rfl] at hK
  rw [Real.coe_toNNReal _ hT0, hhull T hTc hTV] at hK
  unfold hullX recPair at hK
  rw [forwardHull_prefix_eq he _ ENNReal.coe_lt_top hTτ.le le_rfl] at hK
  obtain ⟨z, hz, hzeq⟩ := hK
  unfold RootH29.forwardHull at hz
  obtain ⟨y, ⟨hyK, hyD⟩, rfl⟩ := hz
  have hcre : ((GW2Bf.relBase x s (cfRec s W' ζ' ω, recOf (T : ℝ≥0∞) ((fun t => w t ω), ⊤)) : ℝ) : ℂ) =
      relBdry U s x := Complex.ext (by simp only [GW2Bf.relBase, Complex.ofReal_re]; rfl) (by simp [hbx])
  rw [Complex.ofReal_neg, hcre] at hzeq
  have heq : relMap U s y = relMap U s ((x : ℂ) + γ ω τ) := by
    rw [← relBdry_eq hUc s.coe_nonneg hzH hsafe.2]
    linear_combination hzeq
  have hzD : (x : ℂ) + γ ω τ ∈ relDomain U s := ⟨hzH, fun h => hsafe.2 (subset_closure h)⟩
  have hyz := GW2Nt.injOn_relMap hUc s.coe_nonneg hyD hzD heq
  obtain ⟨q, hq, hqy⟩ := hyK
  rw [RootZ21.fwdHull_record_of_le_of_live he ENNReal.coe_lt_top hTτ.le] at hq
  have hqγ : q = γ ω τ := by
    have := hqy.trans hyz
    linear_combination this
  exact hmem.2 (hqγ ▸ hq)

/-- **An explored point interior to `ℍ \ K_T` gives strict junctions of the version's stage piece** between the
clocks of `T` and `τ`. -/
theorem junctions_strict_stgRec_versionX {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT)
    (hR : VersionAtX x s W' ζ' w γ α R V ω) {T τ : ℝ≥0} (hTτ : T < τ) (hτc : (τ : ℝ≥0∞) < contactX x s γ α ω)
    (hτV : ENNReal.ofReal (clockX x s W' ζ' w τ ω) ≤ V ω)
    (hmem : γ ω τ ∈ H \ fwdHull (fun r : ℝ => w r.toNNReal ω) T) :
    markPosL (rdrv (recOf (((clockX x s W' ζ' w τ ω).toNNReal - (clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) :
        ℝ≥0∞) (fun u => GW2Rd.stgDrv (fun t => R t ω) (clockX x s W' ζ' w T ω).toNNReal u, ⊤)))
        (rtime (recOf (((clockX x s W' ζ' w τ ω).toNNReal - (clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) :
        ℝ≥0∞) (fun u => GW2Rd.stgDrv (fun t => R t ω) (clockX x s W' ζ' w T ω).toNNReal u, ⊤))) 0 < 0 ∧
      0 < markPos (rdrv (recOf (((clockX x s W' ζ' w τ ω).toNNReal - (clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) :
        ℝ≥0∞) (fun u => GW2Rd.stgDrv (fun t => R t ω) (clockX x s W' ζ' w T ω).toNNReal u, ⊤)))
        (rtime (recOf (((clockX x s W' ζ' w τ ω).toNNReal - (clockX x s W' ζ' w T ω).toNNReal : ℝ≥0) :
        ℝ≥0∞) (fun u => GW2Rd.stgDrv (fun t => R t ω) (clockX x s W' ζ' w T ω).toNNReal u, ⊤))) 0 := by
  have hB := GW2Nt.isGeneratingTrace_versionX hGT hs hx hω hR hτc hτV
  have hdiff := relTip_mem_diff_versionX hGT hs hx hω hR hTτ hτc hτV hmem
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ω hω
  obtain ⟨-, hmono, -⟩ := clock_props W' ζ' ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hTc : (T : ℝ≥0∞) < contactX x s γ α ω := (ENNReal.coe_lt_coe.2 hTτ).trans hτc
  have hTτ' : clockX x s W' ζ' w T ω < clockX x s W' ζ' w τ ω := hmono hTc hτc hTτ
  have hab : (clockX x s W' ζ' w T ω).toNNReal < (clockX x s W' ζ' w τ ω).toNNReal :=
    (Real.toNNReal_lt_toNNReal_iff (lt_of_le_of_lt (RootH29.forwardCapacity_nonneg _ _ _ _) hTτ')).2 hTτ'
  obtain ⟨hRc, hR0, -⟩ := hR
  exact junctions_strict_stgRec hRc hR0 hab hB hdiff

end Interior

end InteractingSLE.Theorem14.GW2Sds
