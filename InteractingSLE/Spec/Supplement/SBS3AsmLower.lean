/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AsmShift
import InteractingSLE.Spec.Supplement.SBS3AsmOld
import InteractingSLE.Spec.Supplement.SB2TcRec
import InteractingSLE.Spec.Supplement.SBLvPinch
import InteractingSLE.Spec.Supplement.SB2DrvPath

/-!
# Lemma S3 in SB2(1)'s configuration: the old side (the retained lower walk) at one sample

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 used in SB2(1), specification pp. 579–580, 632). Deterministic.

* `angle_eq_of_mem_boundaryWalkSpec`, `StageSide.sideH_walk`: a boundary walk of angle `θ` has the side heights of the
  one-step schedule `[(θ, 0)]`; for the lower walk these are `±λ + (π/2)χ`.
* **`old_sample_facts_lower`**: at a launch of the lower walk, in coordinates shifted by the seed `u`, the shifted
  launch chart (`Tc.chartClause_of_launch`), its boundary map (`Lv.finite_fibre_of_isLeftEntryChart`, linear
  growth), the hull model of the run chart translated by `u`, the stage mean of PROVE-T14-S3 read through `z ↦ z + u`
  with the canonical logarithm (`canonDerivLog_image_sub`), and the walk's side labels: exactly the old inputs of
  `exists_protectedWordComparison_upper` with the schedule `[(−π/2, 0)]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart

/-- Every ordinary instruction of a boundary walk has the walk's angle. -/
theorem angle_eq_of_mem_boundaryWalkSpec {b : ℝ → ℝ} {jumps : Finset ℝ} {θ θ' : ℝ} {r : Bool} {t : ℝ≥0∞}
    (h : (Sum.inl (θ', t) : Instr) ∈ (boundaryWalkSpec b jumps θ r).2.2) : θ' = θ := by
  simp only [boundaryWalkSpec, List.mem_flatten, List.mem_replicate] at h
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hl
  exact (Prod.mk.inj (Sum.inl.inj hl)).1

/-- The physical side heights of a boundary walk of angle `θ` are those of the one-step schedule `[(θ, 0)]`. -/
theorem StageSide.sideH_walk {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {r : Bool}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {v : ℝ}
    (hv : StageSide κ b jumps (boundaryWalkSpec b jumps θ r) D n v) : Lh.SideH κ [(θ, 0)] v := by
  obtain ⟨j, -, hl, he⟩ := hv
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hsp := (eq_launch_of_launches _ _ hcθ).1
  have hang : instrAngle (boundaryWalkSpec b jumps θ r) j = θ' := by
    unfold instrAngle
    rw [hsp]
  have hθ' : θ' = θ := angle_eq_of_mem_boundaryWalkSpec (List.mem_of_getElem? hsp)
  refine ⟨(θ, 0), List.mem_singleton_self _, ?_⟩
  rw [← hθ', ← hang]
  exact he

/-- **The old side of SB2(1)'s comparison at one sample, in coordinates shifted by the seed `u`** (deterministic).
At a launch `n` of the lower walk (regular launched pieces), with a prefix path `p` of the retained lower prefix
`A` (from `u`), a sorted word `β` with the mean formula on the run chart at `n` and physical interior side labels:
the shifted launch chart `c` is a left entry chart of `A − u`; its boundary map has finite fibres and linear growth;
`c + e₁` maps out `fill (A − u)`; the recentred word satisfies the mean formula (means read through `z ↦ z + u`) with
the canonical logarithm of `fill (A − u)`; and its unmarked interior values are lower-walk side heights
`±λ + (π/2)χ`. These are the old inputs of `exists_protectedWordComparison_upper` with the schedule `[(−π/2, 0)]`. -/
theorem old_sample_facts_lower {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {u : ℝ} {ω : Ω}
    (hreg : ∀ j c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2))
    (hF : ω ∈ Lv.launchSet κ b jumps E n) {p : ℝ → ℂ}
    (hp : Lx.IsPrefixPath p u (lowerPrefix κ b jumps E n u ω))
    {β : BoundaryWord} (hβs : β.IsSorted) {v u₀ : ℂ → ℝ}
    (hmean : EqOn (fun z => v z + u₀ z + chiC κ *
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n).2.2.2.2.1.2.2 z)
      (fun z => β.mean ((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n).2.2.2.2.1.1 z))
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n).2.2.2.2.1.dom)
    (hside : HasInteriorStageSides κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) n β) :
    ∃ (c : Chart) (g : ℂ → ℂ) (e₁ : ℝ) (word : BoundaryWord),
      IsLeftEntryChart ((fun s => p s - u) '' Icc 0 1) (realMin ((fun s => p s - u) '' Icc 0 1)) c ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g c.2.1 H ∧ (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) ∧
      (∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) ∧
      IsMapOut (fillH ((fun s => p s - u) '' Icc 0 1)) (fun z => c.1 z + (e₁ : ℂ)) ∧ word.IsSorted ∧
      EqOn (fun z => v (z + u) + u₀ (z + u) + chiC κ *
          (canonDerivLog (fillH ((fun s => p s - u) '' Icc 0 1)) z).im)
        (fun z => word.mean (c.1 z)) (H \ fillH ((fun s => p s - u) '' Icc 0 1)) ∧
      ∀ y : ℝ, y ∉ word.jumps → g y ∈ H → Lh.SideH κ [(-(Real.pi / 2), 0)] (word.fn y) := by
  set spec : ExplSpec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun i => E spec i ω with hD
  set A := lowerPrefix κ b jumps E n u ω with hAdef
  obtain ⟨hpc, hp0, hpf, hpH, hpA⟩ := hp
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hF
  have hcrun : c₀ = (ExplState.run κ b jumps spec D n).2.2.2.2.1 := (eq_launch_of_launches _ _ hl).2.2
  have hlc : Lv.launchChart κ b jumps E n ω = (ExplState.run κ b jumps spec D n).2.2.2.2.1 :=
    (Lv.launchChart_eq hl).trans hcrun
  have hnot := Lx.stStatus_ne_done_of_launches _ _ hl
  set cₙ := (ExplState.run κ b jumps spec D n).2.2.2.2.1 with hcₙ
  set m := Lv.launchEntry κ b jumps E n u ω with hm
  -- the left entry chart in shifted coordinates
  have hc := (Tc.chartClause_of_launch (u := u) hreg hF).1
  have hAcpt : IsCompact A := Lx.isCompact_lowerPrefix (u := u) hreg hF
  have huA : ((u : ℝ) : ℂ) ∈ A := hpA ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩
  have hbdd : BddBelow {x : ℝ | (x : ℂ) ∈ A} := by
    obtain ⟨R, hR⟩ := hAcpt.isBounded.subset_closedBall 0
    refine ⟨-R, fun x hx => ?_⟩
    have h1 := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at h1
    linarith [neg_abs_le x]
  have hp'A : (fun s => p s - u) '' Icc 0 1 = (fun z => z - (u : ℂ)) '' A := by
    rw [← hpA, image_image]
  have hmin : realMin ((fun s => p s - u) '' Icc 0 1) = realMin A - u := by
    rw [hp'A]; exact Lw.realMin_image_sub u ⟨u, huA⟩ hbdd
  rw [hlc] at hc
  set c := Lw.shiftChart cₙ u m with hcdef
  have hc' : IsLeftEntryChart ((fun s => p s - u) '' Icc 0 1) (realMin ((fun s => p s - u) '' Icc 0 1)) c := by
    rw [hmin, hp'A]; exact hc
  -- the boundary map
  have hcc : cₙ.IsConformal := (GW2aCont.isConformal_runChart _ _ n fun j _ => hreg j).1
  have hP : GW1P.HasProperBdryExt cₙ := hcrun ▸ GW2Later.hasProperBdryExt_of_launch hreg hl
  obtain ⟨g₀, hg₀c, hg₀i, hg₀b, hg₀t⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hP
  obtain ⟨hgc, hgi⟩ := Lw.bdryMap_shift u m hg₀c hg₀i
  have hp'f : ∀ z, ((fun s => p s - u) ⁻¹' {z} ∩ Icc 0 1).Finite := fun z => by
    have e : (fun s => p s - u) ⁻¹' {z} = p ⁻¹' {z + u} := by
      ext s; simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => by rw [← h]; ring, fun h => by rw [h]; ring⟩
    rw [e]; exact hpf (z + u)
  have hgf := Lv.finite_fibre_of_isLeftEntryChart (p := fun s => p s - u) (hpc.sub continuousOn_const)
    (by simp [hp0]) hp'f hc' hgc hgi
  -- the hull model of the run chart
  obtain ⟨M, hM⟩ := Lw.exists_hullModel_fill (κ := κ) (b := b) (jumps := jumps) spec D hreg n hnot
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D n fun j _ => hreg j
  have hMA : M.hull = fillH A := hM.trans (Lw.fillH_union_real _ _).symm
  have hKA : IsHPHull (fillH A) := hMA ▸ M.isHull
  have hfill : fillH ((fun s => p s - u) '' Icc 0 1) = (fun z => z - (u : ℂ)) '' fillH A := by
    rw [hp'A, fillH_image_sub]
  have hmemA : ∀ z, z ∈ H \ fillH ((fun s => p s - u) '' Icc 0 1) → z + (u : ℂ) ∈ H \ fillH A := by
    intro z hz
    rw [hfill] at hz
    exact ⟨(add_real_mem_H_iff' u).2 hz.1, fun h => hz.2 (mem_image_sub_iff.2 h)⟩
  refine ⟨c, fun w => g₀ (w + m) - u, M.shift - u + m, BoundaryWord.shiftW m β, hc', hgc, hgi, hgf, ?_, ?_,
    BoundaryWord.isSorted_shiftW hβs m, ?_, ?_⟩
  · obtain ⟨C₁, C₂, hC₁, hC⟩ := hg₀b
    refine ⟨C₁, C₁ * |u| + C₂ + |m|, hC₁, fun w hw => ?_⟩
    have hw' : 0 ≤ (w + (m : ℂ)).im := by simpa using hw
    have h1 := hC (w + (m : ℂ)) hw'
    have h2 : ‖w‖ ≤ ‖w + (m : ℂ)‖ + |m| := by
      calc ‖w‖ = ‖(w + (m : ℂ)) - (m : ℂ)‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖w + (m : ℂ)‖ + ‖(m : ℂ)‖ := norm_sub_le _ _
        _ = ‖w + (m : ℂ)‖ + |m| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h3 : ‖g₀ (w + (m : ℂ))‖ ≤ ‖g₀ (w + (m : ℂ)) - (u : ℂ)‖ + |u| := by
      calc ‖g₀ (w + (m : ℂ))‖ = ‖(g₀ (w + (m : ℂ)) - (u : ℂ)) + (u : ℂ)‖ := by rw [sub_add_cancel]
        _ ≤ ‖g₀ (w + (m : ℂ)) - (u : ℂ)‖ + ‖(u : ℂ)‖ := norm_add_le _ _
        _ = ‖g₀ (w + (m : ℂ)) - (u : ℂ)‖ + |u| := by rw [Complex.norm_real, Real.norm_eq_abs]
    have h4 : C₁ * ‖g₀ (w + (m : ℂ))‖ ≤ C₁ * (‖g₀ (w + (m : ℂ)) - (u : ℂ)‖ + |u|) :=
      mul_le_mul_of_nonneg_left h3 hC₁
    show ‖w‖ ≤ C₁ * ‖g₀ (w + (m : ℂ)) - (u : ℂ)‖ + (C₁ * |u| + C₂ + |m|)
    nlinarith
  · have hmo := isMapOut_image_sub M.mapOut u
    rw [hMA, ← hfill] at hmo
    convert hmo using 2 with z
    show cₙ.1 (z + (u : ℂ)) - (m : ℂ) + ((M.shift - u + m : ℝ) : ℂ) = cₙ.1 (z + (u : ℂ)) + (M.shift : ℂ) - u
    push_cast
    ring
  · intro z hz
    have hz' := hmemA z hz
    have hzd : z + (u : ℂ) ∈ (cₙ.dom : Set ℂ) := by rw [M.dom_eq, hMA]; exact hz'
    have he := hmean hzd
    have hlift := M.lift_eq_canonDerivLog hN (show z + (u : ℂ) ∈ H \ M.hull by rw [hMA]; exact hz')
    have hcan := canonDerivLog_image_sub hKA u (show z ∈ H \ (fun z => z - (u : ℂ)) '' fillH A by
      rw [← hfill]; exact hz)
    simp only at he ⊢
    rw [hfill, hcan]
    show v (z + u) + u₀ (z + u) + chiC κ * (canonDerivLog (fillH A) (z + u)).im =
      (BoundaryWord.shiftW m β).mean (cₙ.1 (z + u) - m)
    rw [RLC.OrdDet.mean_shiftW, sub_add_cancel, ← he, ← hMA]
    rw [hlift]
  · intro y hy hyH
    have hyJ : y + m ∉ β.jumps := by
      intro h
      apply hy
      rw [BoundaryWord.jumps_shiftW]
      exact Finset.mem_image.2 ⟨y + m, h, by ring⟩
    have hbd : LuM.bdVal cₙ ((y + m : ℝ) : ℂ) = g₀ ((y + m : ℝ) : ℂ) :=
      LuM.bdVal_eq_of_tendsto (by simp) (hg₀t _ (by simp [Hbar]))
    have hyH' : LuM.bdVal cₙ ((y + m : ℝ) : ℂ) ∈ H := by
      rw [hbd]
      have e : ((y + m : ℝ) : ℂ) = (y : ℂ) + (m : ℂ) := by push_cast; ring
      rw [e]
      have : g₀ ((y : ℂ) + (m : ℂ)) - (u : ℂ) ∈ H := hyH
      exact (sub_real_mem_H_iff u).1 this
    rw [BoundaryWord.fn_shiftW]
    exact StageSide.sideH_walk (hside (y + m) hyJ hyH')

end InteractingSLE.Theorem14.SB.S3.Asm
