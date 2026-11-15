/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbFlow
import InteractingSLE.Spec.Supplement.GW2SdgNear
import InteractingSLE.Spec.Supplement.GB6LifeBase
import InteractingSLE.Spec.Sec7.StripDet
import InteractingSLE.Spec.Sec5.Prop59NodeTreeWord
import InteractingSLE.Spec.Theorem15Inputs
import InteractingSLE.Spec.Supplement.G12RemPassiveWord
import InteractingSLE.Spec.Supplement.GB6RestartProofWord

/-!
# The far right mark of a flow line is swallowed on an infinite lifetime (D76, RELDET's piece (2) for STAGEMEAN)

Packet PROVE-GW2-STAGEMEAN, R126 round (D78: STAGEMEAN proves RELDET's `GW2Rd.FlowSwallowStatement`, `GW2UbFlow`,
"For STAGEMEAN (2)"). From RELDET's generic `GW2Rd.ae_exists_swallow_of_top` (target change and G12, `GW2UbSep`):

* **`ae_exists_swallow_idx`**: the generic swallowing at any right mark of index `≥ 1` (re-indexing the right list as
  `Fin (j + 1 + m)` by `subst`, the mark being `LP.retargetIdx j m`);
* `ae_rightImg_of_vR`: a swallowed mark is the swallowed real flow image of its position
  (`GW2Sdg.vR_eq_rightImg_upTo`, `Supp8.GB6.rightImg_congr`);
* **`ae_swallow_point`**: every point `y > 0` above a right mark is swallowed: a mark directly, otherwise inserted as
  a passive mark of weight `0` after the last mark below it (`Supp7.G12.isIntegratedSLEEvolution_insertPassive`; the
  extended word is distinct and has the same total right weight);
* **`flowSwallowStatement_of_thm13`**: `FlowSwallowStatement` from Theorem 1.3 (the flow-line word is distinct,
  `isOrderedForceWord_flowLine`, `strictAnti_flowLineXL`, `strictMono_flowLineXR`, with the left seed mark and the
  right seed mark `0 < y`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Pr

/-- **Generic swallowing at a right mark of index `≥ 1`** (RELDET's `ae_exists_swallow_of_top`, re-indexed). -/
theorem ae_exists_swallow_idx (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hD : LP.IsDistinctForceWord xL xR) (hnL : 0 < nL) (hS : ∑ i, ρR i < κ / 2 - 2)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (i : Fin nR) (hi : 1 ≤ (i : ℕ)) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ t : ℝ≥0, VR i t ω ≤ W t ω := by
  obtain ⟨j, m, e, hij⟩ : ∃ j m : ℕ, nR = j + 1 + m ∧ (i : ℕ) = j :=
    ⟨i, nR - i - 1, by have := i.isLt; omega, rfl⟩
  subst e
  have hj : 1 ≤ j := hij ▸ hi
  have hi' : i = LP.retargetIdx j m := Fin.ext (by simp [LP.retargetIdx, hij])
  subst hi'
  exact GW2Rd.ae_exists_swallow_of_top h13 hκ hκ4 hD hj hnL hS hE

/-- **The swallowing in the real flow form** (one mark): if the mark `i` is swallowed almost surely on an infinite
lifetime, so is its real flow image of `xR i`. -/
theorem ae_rightImg_of_vR {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (i : Fin nR)
    (hsw : ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ t : ℝ≥0, VR i t ω ≤ W t ω) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ t : ℝ≥0, MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal ω) (xR i) t ≤ W t ω := by
  filter_upwards [hsw, hE.2.2.2.2] with ω h1 hp hζ
  obtain ⟨t, ht⟩ := h1 hζ
  have hu := hp.isSLEPathUpTo (τ := ζ ω) le_rfl
  have htτ : (t : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hv := GW2Sdg.vR_eq_rightImg_upTo hu htτ i
  have hWc : Continuous fun s => W s ω :=
    continuousOn_univ.1 (hu.continuousOn_w.mono fun s _ => by
      show (s : ℝ≥0∞) < ζ ω
      rw [hζ]
      exact ENNReal.coe_lt_top)
  have hcongr : MartChar.RealFlow.rightImg (frozenDrive (fun s => W s ω) t) (xR i) t =
      MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal ω) (xR i) t :=
    Supp8.GB6.rightImg_congr (hWc.comp continuous_real_toNNReal) t.coe_nonneg fun r hr => frozenDrive_eq hr
  refine ⟨t, ?_⟩
  rw [← hcongr, ← hv]
  exact ht

/-- **Every point `y > 0` above a right mark is swallowed on an infinite lifetime** (an integrated `SLE_κ(ρ)`
evolution of a distinct word with a left mark and total right weight `< κ/2 − 2`; `y` a mark, or inserted as a passive
mark of weight `0`, `Supp7.G12.isIntegratedSLEEvolution_insertPassive`). -/
theorem ae_swallow_point (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hD : LP.IsDistinctForceWord xL xR) (hnL : 0 < nL) (hS : ∑ i, ρR i < κ / 2 - 2)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {y : ℝ} (hy : 0 < y) {k₀ : Fin nR}
    (hk₀ : xR k₀ < y) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ t : ℝ≥0, MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal ω) y t ≤ W t ω := by
  classical
  by_cases hm : ∃ i, xR i = y
  · obtain ⟨i, hi⟩ := hm
    have hki : k₀ < i := hD.2.2.lt_iff_lt.1 (hi ▸ hk₀)
    have hi1 : 1 ≤ (i : ℕ) := by have : (k₀ : ℕ) < i := hki; omega
    have h := ae_rightImg_of_vR hE i (ae_exists_swallow_idx h13 hκ hκ4 hD hnL hS hE i hi1)
    rwa [hi] at h
  push Not at hm
  -- the last right mark below `y`, and the passive mark after it
  set Sb : Finset (Fin nR) := Finset.univ.filter fun j => xR j < y
  have hne : Sb.Nonempty := ⟨k₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hk₀⟩⟩
  set k := Sb.max' hne
  have hk : xR k < y := (Finset.mem_filter.1 (Finset.max'_mem Sb hne)).2
  have hky : ∀ j, xR j < y → j ≤ k := fun j hj =>
    Finset.le_max' Sb j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
  have hord := hD.1
  have hE' := Supp7.G12.isIntegratedSLEEvolution_insertPassive hE hord hy hk hky
  set xR' : Fin (nR + 1) → ℝ := Fin.insertNth k.succ y xR with hxR'
  have hb : ∀ j : Fin nR, j.castSucc < k.succ → xR j ≤ y := fun j hj =>
    (hD.2.2.monotone (Fin.castSucc_lt_succ_iff.1 hj)).trans hk.le
  have ha : ∀ j : Fin nR, k.succ ≤ j.castSucc → y ≤ xR j := fun j hj => by
    by_contra hlt
    push Not at hlt
    have := hky j hlt
    exact absurd hj (not_le.2 (Fin.castSucc_lt_succ_iff.2 this))
  have hmono : Monotone xR' := Supp7.G12.monotone_insertNth hD.2.2.monotone k.succ hb ha
  have hinj : Function.Injective xR' := by
    intro i i' hii'
    rcases Fin.eq_self_or_eq_succAbove k.succ i with hi | ⟨j, hj⟩ <;>
      rcases Fin.eq_self_or_eq_succAbove k.succ i' with hi' | ⟨j', hj'⟩
    · rw [hi, hi']
    · rw [hi, hj', hxR', Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hii'
      exact absurd hii'.symm (hm j')
    · rw [hj, hi', hxR', Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hii'
      exact absurd hii' (hm j)
    · rw [hj, hj', hxR', Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at hii'
      rw [hj, hj', hD.2.2.injective hii']
  have hD' : LP.IsDistinctForceWord xL xR' := by
    refine ⟨⟨hord.1, hord.2.1, hmono, fun i => ?_⟩, hD.2.1, hmono.strictMono_of_injective hinj⟩
    rcases Fin.eq_self_or_eq_succAbove k.succ i with hi | ⟨j, hj⟩
    · rw [hi, hxR', Fin.insertNth_apply_same]; exact hy.le
    · rw [hj, hxR', Fin.insertNth_apply_succAbove]; exact hord.2.2.2 j
  have hS' : ∑ i, Fin.insertNth k.succ (0 : ℝ) ρR i < κ / 2 - 2 := by
    rw [Supp7.G12.sum_insertNth_of_eq_zero k.succ _ (by simp)]
    simpa only [Fin.insertNth_apply_succAbove] using hS
  have hsw := ae_exists_swallow_idx h13 hκ hκ4 hD' hnL hS' hE' k.succ (by simp)
  have h := ae_rightImg_of_vR hE' k.succ hsw
  have hyk : xR' k.succ = y := by rw [hxR', Fin.insertNth_apply_same]
  rwa [hyk] at h

/-- **RELDET's `FlowSwallowStatement`, from Theorem 1.3**: for a flow-line driver at angle `0` of a GFF with
piecewise-constant data whose right total weight is `< κ/2 − 2`, almost surely on an infinite lifetime the driver
meets the real flow image of every point `y > 0`. The flow-line word is distinct with the left seed mark, and its
right seed mark `0 < y` lies below `y`. -/
theorem flowSwallowStatement_of_thm13 (h13 : Exist.Theorem13Statement.{u}) : GW2Rd.FlowSwallowStatement.{u} := by
  intro κ hκ hκ4 b jumps y hy hS Ω _ P _ h W ζ hfl
  obtain ⟨_h₁, 𝓕, VL, VR, B, -, hC⟩ := hfl
  have hD : LP.IsDistinctForceWord (flowLineXL b jumps 0) (flowLineXR b jumps 0) :=
    ⟨Theorem15.isOrderedForceWord_flowLine b jumps 0, Sec7.StripDet.strictAnti_flowLineXL b jumps,
      Sec7.StripDet.strictMono_flowLineXR b jumps⟩
  have h0 : flowLineXR b jumps 0 ⟨0, Supp8.GB6.zero_lt_flowLineNR b jumps⟩ = 0 := rfl
  exact ae_swallow_point h13 hκ hκ4 hD (Sec5.Prop59NodeTree.flowLineNL_pos b jumps 0) hS hC.1 hy (h0 ▸ hy)

end InteractingSLE.Theorem14.GW2Pr
