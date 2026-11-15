/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2OmCfg
import InteractingSLE.Spec.Supplement.Q3ChainRet
import InteractingSLE.Spec.Supplement.SB2KqWord
import InteractingSLE.Spec.Supplement.SB2KcPartition
import InteractingSLE.Spec.Exist.FlowField

/-!
# SB2(2)'s line mean: the three word identities of the configuration record

Packet PROVE-GW2-GEOM2, round 9 (PROVE-SB2-LCMEAN's handoff R13.8, item 1). `Om.exists_isCfg_of_stageS2` asks for
three identities between bounded harmonic extensions:

* **retained** (`eqOn_typed_mean`): on a type cell of the retained word `β`, the extension of the type's force data
  is `β.mean + ψχ` — the type is the angle-`ψ` flow-line word of `β` (`FCDet.IsFlowType`), whose force data are
  `β + ψχ` off the jumps and `0` (`Exist.forceBoundaryData_flowLine_seed`);
* **explored** (`eqOn_explored_mean`): the extension of the flowed force data of a word's angle-`θ` flow-line type at a
  record is the record's stop word's mean plus `θχ` (`Q3Chain.eqOn_bhe_stopWord`);
* **union** (`Lv.eqOn_bheProc_of_flowedData`, used as is): the extension of the flowed type data is K2's `bheProc`.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.SB.Om

open Restart Exist.StagedLaw
open Supp8.Q3Chain (flowedData flowedJumps initJumps coe_initJumps)

/-- **The force data of a flow-line type are the word plus `θχ`**, off `0` and the word's jumps. -/
theorem forceBoundaryData_eq_of_isFlowType {κ θ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hft : FCDet.IsFlowType κ θ c xL xR ρL ρR)
    {y : ℝ} (hy0 : y ≠ 0) (hyJ : y ∉ c.jumps) : forceBoundaryData κ ρL ρR xL xR y = c.fn y + θ * chiC κ := by
  obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := hft
  subst eL eR
  simp only [Fin.cast_eq_self] at hxL hxR hρL hρR
  have hxL' : xL = flowLineXL c.fn c.jumps 0 := hxL
  have hxR' : xR = flowLineXR c.fn c.jumps 0 := hxR
  have hρL' : ρL = flowLineRhoL κ c.fn c.jumps 0 θ := hρL
  have hρR' : ρR = flowLineRhoR κ c.fn c.jumps 0 θ := hρR
  subst hxL' hxR' hρL' hρR'
  have h := Exist.forceBoundaryData_flowLine_seed hκ (BoundaryWord.isPiecewiseConstantBoundaryData c) 0 θ hy0
    (by rw [add_zero]; exact_mod_cast hyJ)
  rw [h, add_zero]

/-- **The retained identity**: on a type cell of a sorted word, every bounded harmonic extension of the type's force
data is the word's mean plus `ψχ` on `ℍ`. -/
theorem eqOn_typed_mean {Ω : Type*} {κ ψ : ℝ} (hκ : 0 < κ) {β : Ω → BoundaryWord} {F : Set Ω}
    {w : Supp8.Q3Stop.WordType} {ω : Ω} (hω : ω ∈ Lv.wordTypeCell κ ψ β F w) (hs : (β ω).IsSorted) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (forceBoundaryData κ (Supp8.Q3Stop.typedRhoL w) (Supp8.Q3Stop.typedRhoR w)
      (Lv.cellXL κ ψ β w ω) (Lv.cellXR κ ψ β w ω)) (forceJumpSet (Lv.cellXL κ ψ β w ω) (Lv.cellXR κ ψ β w ω)) G) :
    EqOn G (fun z => (β ω).mean z + ψ * chiC κ) H := by
  have hft : FCDet.IsFlowType κ ψ (β ω) (Lv.cellXL κ ψ β w ω) (Lv.cellXR κ ψ β w ω) (Supp8.Q3Stop.typedRhoL w)
      (Supp8.Q3Stop.typedRhoR w) := FCDet.isFlowType_of_mem_typeSet (Lv.mem_typeSet_of_mem_wordTypeCell hω)
  set S : Set ℝ := insert 0 ((β ω).jumps ∪ forceJumpSet (Lv.cellXL κ ψ β w ω) (Lv.cellXR κ ψ β w ω)) with hSdef
  have hSf : S.Finite := by
    refine Finite.insert 0 (Finite.union (Finset.finite_toSet _) ?_)
    exact ((Set.finite_range _).union (Set.finite_range _)).insert 0
  have hG' : IsBoundedHarmonicExtension (fun y => (β ω).fn y + ψ * chiC κ) S G := by
    obtain ⟨hh, hb, hl⟩ := hG
    refine ⟨hh, hb, fun x hx => ?_⟩
    have hx0 : x ≠ 0 := fun h => hx (Or.inl h)
    have hxJ : x ∉ (β ω).jumps := fun h => hx (Or.inr (Or.inl h))
    have hxF : x ∉ forceJumpSet (Lv.cellXL κ ψ β w ω) (Lv.cellXR κ ψ β w ω) := fun h => hx (Or.inr (Or.inr h))
    show Tendsto G (𝓝[H] (x : ℂ)) (𝓝 ((β ω).fn x + ψ * chiC κ))
    rw [← forceBoundaryData_eq_of_isFlowType hκ hft hx0 hxJ]
    exact hl x hxF
  have hm := Sec5.GlueCond.isBoundedHarmonicExtension_add_const
    (LocalExt.IsBoundedHarmonicExtension.mono_set (BoundaryWord.isBoundedHarmonicExtension_mean (β ω) hs)
      (S' := S) fun x hx => Or.inr (Or.inl hx)) (ψ * chiC κ)
  exact Impl.eqOn_of_isBoundedHarmonicExtension hSf hm hG'

/-- **The explored identity**: every bounded harmonic extension of the flowed force data of a word's angle-`θ`
flow-line type at a record is the record's stop word's mean plus `θχ` on `ℍ`. -/
theorem eqOn_explored_mean {κ θ : ℝ} (c : BoundaryWord) (r : RecData) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (flowedData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
        (flowLineXR c.fn c.jumps 0) (rdrv r) (rtime r))
      (flowedJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) (rdrv r) (rtime r)) G) :
    EqOn G (fun z => (stopWord κ (c, θ, r)).mean z + θ * chiC κ) H := by
  have hmean := BoundaryWord.isBoundedHarmonicExtension_mean (stopWord κ (c, θ, r)) (isSorted_stopWord κ (c, θ, r))
  have hG' : IsBoundedHarmonicExtension
      (forceBoundaryData κ (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ)
        (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)))
      (forceJumpSet (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j))) G := by
    have e : (flowedJumps (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0) (rdrv r) (rtime r) : Set ℝ) =
        forceJumpSet (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
          (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)) := by
      unfold flowedJumps
      rw [coe_initJumps]
    rw [← e]
    exact hG
  have h := Supp8.Q3Chain.eqOn_bhe_stopWord κ θ c r hmean hG'
  intro z hz
  have hz' := h hz
  simp only at hz' ⊢
  linarith

end InteractingSLE.Theorem14.SB.Om
