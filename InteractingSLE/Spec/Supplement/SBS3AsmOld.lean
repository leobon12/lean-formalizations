/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AsmUpper
import InteractingSLE.Spec.Supplement.SBS3CanonOld
import InteractingSLE.Spec.Supplement.SBS3MarkedSchedule
import InteractingSLE.Spec.Supplement.WalkIntClosedRun
import InteractingSLE.Spec.Supplement.WalkIntCanonModelRun

/-!
# Lemma S3: the old history's inputs at one sample

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580). Deterministic.

* `stStatus_run_ne_done_of_flow`, `stStatus_run_sspec_ne_done`: a flow program with finite own times (in particular
  every schedule) never reaches the *done* status.
* **`old_sample_facts`**: at a schedule prefix whose physical set is a path image `A`, the run chart recentred at its
  left entry value, its boundary map, its hull model and PROVE-T14-S3's retained word give exactly the old inputs
  of `exists_protectedWordComparison_upper`: left entry chart, finite-fibre boundary map with linear growth, map-out
  of `fill A`, the mean formula with the canonical logarithm of `fill A`, and schedule side labels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.S3.Asm

open Exist.Staged Exist.StagedLaw Restart

/-- **A flow program with finite own times never finishes**: if every instruction of the program is an ordinary
piece with a finite own time, no state of the run has the *done* status. -/
theorem stStatus_run_ne_done_of_flow {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hprog : ∀ (j : ℕ) (a : Instr), spec.2.2[j]? = some a → ∃ (θ : ℝ) (t : ℝ≥0∞), a = Sum.inl (θ, t) ∧ t ≠ ⊤) (n : ℕ) :
    stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone := by
  induction n with
  | zero =>
    show stStatus (ExplState.init spec.1) ≠ _
    intro h
    cases h
  | succ n ih =>
    rw [run_succ]
    rcases hk : spec.2.2[n]? with _ | a
    · exact ih
    · obtain ⟨θ, t, rfl, ht⟩ := hprog n a hk
      show stStatus (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ t) ≠ _
      have hmin : min t (D n).2 ≠ ⊤ := ne_top_of_le_ne_top ht (min_le_left _ _)
      generalize ExplState.run κ b jumps spec D n = s at ih ⊢
      obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
      unfold ExplState.flowStep
      dsimp only
      split
      · exact WalkIntClosed.status_launch_ne_done _ _ _ _ _ hmin
      · exact WalkIntClosed.status_launch_ne_done _ _ _ _ _ hmin
      · exact ih
      · exact ih
      · split_ifs
        · intro h
          cases h
        · exact WalkIntClosed.status_launch_ne_done _ _ _ _ _ hmin
        · exact ih

/-- A schedule run never finishes. -/
theorem stStatus_run_sspec_ne_done {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (x₀ : ℝ) (l : List (ℝ × ℝ≥0))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    stStatus (ExplState.run κ b jumps (Lf.sspec x₀ l) D n) ≠ GW1Conn.stDone := by
  refine stStatus_run_ne_done_of_flow _ D (fun j a hj => ?_) n
  have hjl : j < (scheduleProgram 0 l).length := by
    by_contra hc
    have : (scheduleProgram 0 l)[j]? = none := List.getElem?_eq_none (not_lt.1 hc)
    change (scheduleProgram 0 l)[j]? = some a at hj
    rw [this] at hj
    cases hj
  have hs := GW2Schedule.isFlowProg_scheduleProgram 0 l j hjl
  change (scheduleProgram 0 l)[j]? = some a at hj
  rw [hs] at hj
  exact ⟨_, _, (Option.some.inj hj).symm, GW2Schedule.schedDelta_ne_top 0 l j⟩

open Geo in
/-- **The old side of Lemma S3 at one sample** (deterministic). For the schedule from `0` (regular launched pieces,
injective launched traces) at state `n`, whose physical prefix is a path image `A`, and a sorted word `β` whose
recentred formula holds for a harmonic representative `v` at every real recentering of the run chart, with
physical interior side labels: the run chart recentred at its left entry value is a left entry chart `c` of `A`; its
boundary map `g` is continuous on `ℍ̄`, with finite fibres and linear growth; `c + e₁` maps out `fill A`; the
recentred word is sorted, satisfies the mean formula with the canonical logarithm of `fill A` on `ℍ ∖ fill A`, and
takes schedule side heights at the unmarked interior landings of `g`. These are exactly the old inputs of
`exists_protectedWordComparison_upper`. -/
theorem old_sample_facts {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (l : List (ℝ × ℝ≥0))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (Lf.sspec 0 l) D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (Lf.sspec 0 l) k) (D k).2))
    (hinj : Lk.InjLaunches κ b jumps (Lf.sspec 0 l) D) (n : ℕ)
    {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpA : p '' Icc 0 1 = prefixPhysSet κ b jumps (Lf.sspec 0 l) D n)
    {β : BoundaryWord} (hβs : β.IsSorted) {v u₀ : ℂ → ℝ}
    (hmean : ∀ a : ℝ, EqOn (fun z => v z + u₀ z + chiC κ *
        ((stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)).recenter a).2.2 z)
      (fun z => (BoundaryWord.shiftW a β).mean
        (((stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)).recenter a).1 z))
      ((stChart (ExplState.run κ b jumps (Lf.sspec 0 l) D n)).recenter a).dom)
    (hside : HasInteriorStageSides κ b jumps (Lf.sspec 0 l) D n β) :
    ∃ (c : Chart) (g : ℂ → ℂ) (e₁ : ℝ) (word : BoundaryWord),
      IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c ∧
      ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g c.2.1 H ∧ (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) ∧
      (∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂) ∧
      IsMapOut (fillH (p '' Icc 0 1)) (fun z => c.1 z + (e₁ : ℂ)) ∧ word.IsSorted ∧
      EqOn (fun z => v z + u₀ z + chiC κ * (canonDerivLog (fillH (p '' Icc 0 1)) z).im)
        (fun z => word.mean (c.1 z)) (H \ fillH (p '' Icc 0 1)) ∧
      ∀ y : ℝ, y ∉ word.jumps → g y ∈ H → Lh.SideH κ l (word.fn y) := by
  set s := ExplState.run κ b jumps (Lf.sspec 0 l) D n with hs
  set A : Set ℂ := p '' Icc 0 1 with hAdef
  have hnot : stStatus s ≠ GW1Conn.stDone := stStatus_run_sspec_ne_done 0 l D n
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hAf : fillH A = fillH (prefixPhysSet κ b jumps (Lf.sspec 0 l) D n) := congrArg fillH hpA
  have hLA : ∀ y : ℝ, (y : ℂ) ∈ A → realMin A ≤ y := fun y hy => ((realBase_facts hp hp0).2.2.1 y hy).1
  set a : ℝ := Lx.leftEntry (stChart s) (realMin A) with ha
  have hv := Lx.isLeftEntryValue_runChart (Lf.sspec 0 l) D hreg n hnot hAc hAf hLA
  have hc' : IsLeftEntryChart A (realMin A) ((stChart s).recenter a) :=
    Lf.isLeftEntryChart_runChart (Lf.sspec 0 l) D hreg n hnot hAc hAf hv
  have hcc : (stChart s).IsConformal :=
    (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec 0 l) D n
      fun j _ c θ h => hreg j c θ h).1
  obtain ⟨g, hgc, hgi, hgb, hgt⟩ :=
    Lw.exists_bdryMap_of_hasProperBdryExt hcc (GW1P.isClosed_pieces_run (Lf.sspec 0 l) D hreg n).1
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec 0 l) D hreg n hnot
  have hgf : ∀ z, (g ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite :=
    Lk.finite_fibre_of_pinv (Lk.pinv_schedule le_rfl l D hreg hinj n) hD hgc hgi hgb
  obtain ⟨M, hM⟩ := Lw.exists_hullModel_fill (κ := κ) (b := b) (jumps := jumps) (Lf.sspec 0 l) D hreg n hnot
  have hN := WalkIntCanon.isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) (Lf.sspec 0 l) D n
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
