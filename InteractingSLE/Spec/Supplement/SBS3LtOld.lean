/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AsmOld
import InteractingSLE.Spec.Supplement.SB4RFrame
import InteractingSLE.Spec.Supplement.SB2LkFF
import InteractingSLE.Spec.Supplement.SB2JRight

/-!
# Lemma S3 for SB2(2)'s lower tail: the upper schedule's inputs at one sample

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 with the roles exchanged, supplement p. 631). Deterministic.

* **`old_sample_facts_right`**: at a launch of the upper schedule from `u ≤ 0`, the run chart recentred at its right
  entry value is a right entry chart of the prefix with the bridge `[u, 0]` (`Lf.isRightEntryChart_runChart`), its
  boundary map has finite fibres (`Lk.finite_fibre_schedule`) and linear growth, the hull model maps out the fill,
  PROVE-T14-S3's retained word gives the mean formula with the canonical logarithm, and the labels are the schedule's
  side heights: the old inputs of `exists_protectedWordComparison_lower`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart

/-- **The old side of the lower-orientation comparison at one sample** (deterministic). For the schedule from a seed
`u ≤ 0` (regular launched pieces, injective launched traces) launching at `n`, whose prefix with the bridge `[u, 0]`
is a path image `A`, with a right entry value `a` of the run chart at `R = max (A ∩ ℝ)`, and a sorted word `β` whose
recentred formula holds for a harmonic representative `v` at every real recentering, with physical interior side
labels: the run chart recentred at `a` is a right entry chart `c` of `A`; its boundary map has finite fibres and
linear growth; `c + e₁` maps out `fill A`; the recentred word is sorted, satisfies the mean formula with the canonical
logarithm of `fill A`, and takes schedule side heights at unmarked interior landings. These are the old inputs of
`exists_protectedWordComparison_lower`. -/
theorem old_sample_facts_right {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {u : ℝ} (hu : u ≤ 0)
    (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (Lf.sspec u l) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (Lf.sspec u l) k) (D k).2))
    (hinj : Lk.InjLaunches κ b jumps (Lf.sspec u l) D) {n : ℕ} {c₀ : Chart} {θ₀ : ℝ}
    (hl : (ExplState.run κ b jumps (Lf.sspec u l) D (n + 1)).2.2.2.1 n = some (c₀, θ₀))
    {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1))
    (hpA : p '' Icc 0 1 = prefixPhysSet κ b jumps (Lf.sspec u l) D n ∪ ((↑) : ℝ → ℂ) '' Icc u 0)
    {a : ℝ} (hv : Lx.IsRightEntryValue (stChart (ExplState.run κ b jumps (Lf.sspec u l) D n))
      (realMax (p '' Icc 0 1)) a)
    {β : BoundaryWord} (hβs : β.IsSorted) {v u₀ : ℂ → ℝ}
    (hmean : ∀ a : ℝ, EqOn (fun z => v z + u₀ z + chiC κ *
        ((stChart (ExplState.run κ b jumps (Lf.sspec u l) D n)).recenter a).2.2 z)
      (fun z => (BoundaryWord.shiftW a β).mean
        (((stChart (ExplState.run κ b jumps (Lf.sspec u l) D n)).recenter a).1 z))
      ((stChart (ExplState.run κ b jumps (Lf.sspec u l) D n)).recenter a).dom)
    (hside : HasInteriorStageSides κ b jumps (Lf.sspec u l) D n β) :
    ∃ (c : Chart) (g : ℂ → ℂ) (e₁ : ℝ) (word : BoundaryWord),
      IsRightEntryChart (p '' Icc 0 1) (realMax (p '' Icc 0 1)) c ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g c.2.1 H ∧ (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) ∧
      (∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) ∧
      IsMapOut (fillH (p '' Icc 0 1)) (fun z => c.1 z + (e₁ : ℂ)) ∧ word.IsSorted ∧
      EqOn (fun z => v z + u₀ z + chiC κ * (canonDerivLog (fillH (p '' Icc 0 1)) z).im)
        (fun z => word.mean (c.1 z)) (H \ fillH (p '' Icc 0 1)) ∧
      ∀ y : ℝ, y ∉ word.jumps → g y ∈ H → Lh.SideH κ l (word.fn y) := by
  set s := ExplState.run κ b jumps (Lf.sspec u l) D n with hs
  set A : Set ℂ := p '' Icc 0 1 with hAdef
  have hnot : stStatus s ≠ GW1Conn.stDone := stStatus_run_sspec_ne_done u l D n
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hAf : fillH A = fillH (prefixPhysSet κ b jumps (Lf.sspec u l) D n) := by
    rw [hpA, Lw.fillH_union_real]
  have hc' : IsRightEntryChart A (realMax A) ((stChart s).recenter a) :=
    Lf.isRightEntryChart_runChart (Lf.sspec u l) D hreg n hnot hAc hAf hv
  have hcc : (stChart s).IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec u l) D n
      fun j _ c θ h => hreg j c θ h).1
  obtain ⟨g, hgc, hgi, hgb, hgt⟩ :=
    Lw.exists_bdryMap_of_hasProperBdryExt hcc (GW1P.isClosed_pieces_run (Lf.sspec u l) D hreg n).1
  have hcs : c₀ = stChart s := (eq_launch_of_launches _ D hl).2.2
  have hgf : ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite :=
    Lk.finite_fibre_schedule hu l D hreg hinj hl hgc (hcs ▸ hgi) hgb
  obtain ⟨M, hM⟩ := Lw.exists_hullModel_fill (κ := κ) (b := b) (jumps := jumps) (Lf.sspec u l) D hreg n hnot
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec u l) D n
    fun j _ c θ h => hreg j c θ h
  have hMA : M.hull = fillH A := hM.trans hAf.symm
  set g' : ℂ → ℂ := fun w => g (w + a) with hg'
  have hsh : ∀ w : ℂ, 0 ≤ w.im → 0 ≤ (w + (a : ℂ)).im := fun w hw => by simpa using hw
  refine ⟨(stChart s).recenter a, g', M.shift + a, BoundaryWord.shiftW a β, hc', ?_, ?_, ?_, ?_, ?_,
    BoundaryWord.isSorted_shiftW hβs a, ?_, ?_⟩
  · exact hgc.comp (continuous_id.add continuous_const).continuousOn fun w (hw : 0 ≤ w.im) => hsh w hw
  · intro w hw
    show g (w + (a : ℂ)) = (stChart s).2.1 (w + (a : ℂ))
    exact hgi ((Lw.add_real_mem_H_iff a).2 hw)
  · intro z
    refine ((hgf z).image fun w => w - (a : ℂ)).subset fun w hw => ?_
    refine ⟨w + (a : ℂ), ⟨hw.1, hsh w hw.2⟩, ?_⟩
    simp only [add_sub_cancel_right]
  · obtain ⟨C₁, C₂, hC₁, hC⟩ := hgb
    refine ⟨C₁, C₂ + |a|, hC₁, fun w hw => ?_⟩
    have h1 := hC (w + (a : ℂ)) (hsh w hw)
    have h2 : ‖w‖ ≤ ‖w + (a : ℂ)‖ + |a| := by
      calc ‖w‖ = ‖(w + (a : ℂ)) - (a : ℂ)‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖w + (a : ℂ)‖ + ‖(a : ℂ)‖ := norm_sub_le _ _
        _ = ‖w + (a : ℂ)‖ + |a| := by rw [Complex.norm_real, Real.norm_eq_abs]
    show ‖w‖ ≤ C₁ * ‖g (w + (a : ℂ))‖ + (C₂ + |a|)
    linarith
  · have hmo := M.mapOut
    rw [hMA] at hmo
    convert hmo using 2 with z
    show (stChart s).1 z - (a : ℂ) + ((M.shift + a : ℝ) : ℂ) = (stChart s).1 z + (M.shift : ℂ)
    push_cast
    ring
  · intro z hz
    have hzd : z ∈ ((stChart s).recenter a).dom := by
      rw [WalkSide.dom_recenter]
      show z ∈ ((stChart s).dom : Set ℂ)
      rw [M.dom_eq, hMA]
      exact hz
    have he := hmean a hzd
    have hlift := M.lift_eq_canonDerivLog hN (show z ∈ H \ M.hull by rw [hMA]; exact hz)
    rw [← hMA]
    simp only at he ⊢
    rw [← he]
    show v z + u₀ z + chiC κ * (canonDerivLog M.hull z).im = v z + u₀ z + chiC κ * (stChart s).2.2 z
    rw [hlift]
  · intro y hy hyH
    have hyJ : y + a ∉ β.jumps := by
      intro h
      apply hy
      rw [BoundaryWord.jumps_shiftW]
      exact Finset.mem_image.2 ⟨y + a, h, by ring⟩
    have hbd : LuM.bdVal (stChart s) ((y + a : ℝ) : ℂ) = g ((y + a : ℝ) : ℂ) :=
      LuM.bdVal_eq_of_tendsto (by simp) (hgt _ (by simp [Hbar]))
    have hyH' : LuM.bdVal (stChart s) ((y + a : ℝ) : ℂ) ∈ H := by
      rw [hbd]
      have : ((y + a : ℝ) : ℂ) = (y : ℂ) + (a : ℂ) := by push_cast; ring
      rw [this]
      exact hyH
    rw [BoundaryWord.fn_shiftW]
    exact (hside (y + a) hyJ hyH').sideH

end InteractingSLE.Theorem14.SB.S3.Asm
