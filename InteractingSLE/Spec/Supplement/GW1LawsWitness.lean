/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsCanon
import InteractingSLE.Spec.Supplement.GW1ActiveLaw
import InteractingSLE.Spec.Supplement.GW1ActiveLawL
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst

/-!
# GW1's restart laws: the sorted conditional word at a later launch, with its two-sided heights

Packet PROVE-GW1-LAWS. At a later launch `k > 0` of either boundary walk, the conditional field given the retained
past, read in the launch chart, is the GFF of an explicit word (PROVE-T14-GW1W's stage witness). Its proof writes that
word as a recentred stop word (`GW1W.isStageWitness_succ_expl`), which is sorted. Here the witness is re-derived with
that sortedness exported, and its invariant gives the two-sided height bounds of `GW1Laws.ae_cfDrvOf_snd_eq_top`:

* `zero_le_stRecR_run`, `stRecL_run_nonpos`: the right record of a run from a nonnegative root stays nonnegative,
  the left record of a run from a nonpositive root stays nonpositive (deterministic, every program);
* `fn_bound_pos_of_rOrig`, `fn_bound_neg_of_lOrig`: a word that is the original word beyond the outward record (read
  through a good profile) inherits the ambient bound there (deterministic);
* **`exists_sorted_witness_right`**, **`exists_sorted_witness_left`**: the sorted stage witness at every launch
  `k > 0`, with the walk invariant;
* **`exists_next_witness`**: for either walk, at every later launch, a sorted stage witness whose word satisfies both
  height bounds of `ae_cfDrvOf_snd_eq_top`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Laws

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData

/-! ### The outward records stay on their side -/

theorem zero_le_recR_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hs : 0 ≤ stRecR s) : 0 ≤ stRecR (ExplState.launch s k D θ t) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only [stRecR] at hs ⊢
  simp only [ExplState.launch]
  split_ifs <;> (try split) <;> simp_all [GW1Conn.zero_le_sSup_insert]

theorem zero_le_recR_flowStep (κ : ℝ) (b : ℝ → ℝ) (gw2 : Bool) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (hs : 0 ≤ stRecR s) :
    0 ≤ stRecR (ExplState.flowStep κ b gw2 s k D θ t) := by
  have hl := zero_le_recR_launch s k D θ t hs
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only [stRecR] at hs hl ⊢
  simp only [ExplState.flowStep]
  split <;> (try split_ifs) <;> simp_all

theorem zero_le_recR_contStep (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (v : Option ℝ)
    (pref : Bool) (hs : 0 ≤ stRecR s) : 0 ≤ stRecR (ExplState.contStep κ b jumps s v pref) := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only [stRecR] at hs ⊢
  simp only [ExplState.contStep]
  repeat' split
  all_goals simp_all [ExplState.moveAlong, ExplState.moveToEnd]

/-- **The right record of a run from a nonnegative root is nonnegative** (every program). -/
theorem zero_le_stRecR_run (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (h0 : 0 ≤ spec.1) (k : ℕ) :
    0 ≤ stRecR (ExplState.run κ b jumps spec D k) := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [Exist.Staged.run_succ]
    cases spec.2.2[k]? with
    | none => exact ih
    | some a =>
      simp only [ExplState.step]
      split
      · exact zero_le_recR_flowStep κ b _ _ k _ _ _ ih
      · exact zero_le_recR_contStep κ b jumps _ none _ ih
      · exact zero_le_recR_contStep κ b jumps _ (some _) _ ih

theorem recL_launch_nonpos (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (hs : stRecL s ≤ 0) : stRecL (ExplState.launch s k D θ t) ≤ 0 := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only [stRecL] at hs ⊢
  simp only [ExplState.launch]
  split_ifs <;> (try split) <;> simp_all [GW1Conn.sInf_insert_nonpos]

theorem recL_flowStep_nonpos (κ : ℝ) (b : ℝ → ℝ) (gw2 : Bool) (s : ExplState) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (hs : stRecL s ≤ 0) :
    stRecL (ExplState.flowStep κ b gw2 s k D θ t) ≤ 0 := by
  have hl := recL_launch_nonpos s k D θ t hs
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only [stRecL] at hs hl ⊢
  simp only [ExplState.flowStep]
  split <;> (try split_ifs) <;> simp_all

theorem recL_contStep_nonpos (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (s : ExplState) (v : Option ℝ)
    (pref : Bool) (hs : stRecL s ≤ 0) : stRecL (ExplState.contStep κ b jumps s v pref) ≤ 0 := by
  obtain ⟨pieces, arcs, ret, lau, chart, st, pt, ang, rR, rL⟩ := s
  simp only [stRecL] at hs ⊢
  simp only [ExplState.contStep]
  repeat' split
  all_goals simp_all [ExplState.moveAlong, ExplState.moveToEnd]

/-- **The left record of a run from a nonpositive root is nonpositive** (every program). -/
theorem stRecL_run_nonpos (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (h0 : spec.1 ≤ 0) (k : ℕ) :
    stRecL (ExplState.run κ b jumps spec D k) ≤ 0 := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [Exist.Staged.run_succ]
    cases spec.2.2[k]? with
    | none => exact ih
    | some a =>
      simp only [ExplState.step]
      split
      · exact recL_flowStep_nonpos κ b _ _ k _ _ _ ih
      · exact recL_contStep_nonpos κ b jumps _ none _ ih
      · exact recL_contStep_nonpos κ b jumps _ (some _) _ ih

/-! ### Heights of a word that is original beyond the outward record -/

/-- **A word that is original right of the right record inherits the ambient right bound** (deterministic). -/
theorem fn_bound_pos_of_rOrig {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {β : BoundaryWord} {s : ExplState}
    (hP : GW1W.RProf s) (hO : GW1W.ROrig b jumps β s) (h0 : 0 ≤ stRecR s)
    (hamb : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + Real.pi / 2 * chiC κ) :
    ∀ y, 0 < y → y ∉ β.jumps → -sleLambda κ < β.fn y + Real.pi / 2 * chiC κ := by
  intro y hy hyJ
  obtain ⟨x₀, hx₀, hxy⟩ := hP.exists_eq hy
  set m := rProf (stChart s) with hm
  have hloc : ∀ᶠ z in 𝓝 y, β.fn z = β.fn y := β.isPiecewiseConstantBoundaryData y hyJ
  have hcont : ContinuousAt m x₀ := hP.2.1.2.1.continuousAt (Ioi_mem_nhds hx₀)
  have hev : ∀ᶠ x in 𝓝 x₀, stRecR s < x ∧ β.fn (m x) = β.fn y := by
    refine (eventually_gt_nhds hx₀).and ?_
    have hloc' : ∀ᶠ z in 𝓝 (m x₀), β.fn z = β.fn y := by rw [hxy]; exact hloc
    exact hcont.eventually hloc'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set T : Set ℝ := {x | stRecR s < x ∧ m x ∈ β.jumps} with hTdef
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (β.jumps.finite_toSet.subset ?_) (hP.2.1.1.injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  have hbad : ((jumps : Set ℝ) ∪ T).Finite := jumps.finite_toSet.union hT
  obtain ⟨x, hxI, hxbad⟩ := ((Set.Ioo_infinite (by linarith : x₀ < x₀ + ε)).sdiff hbad).nonempty
  have hdist : dist x x₀ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hxI.1, hxI.2]
  obtain ⟨hxR, hfx⟩ := hball hdist
  have hxJ : x ∉ jumps := fun h => hxbad (Or.inl h)
  have hmJ : m x ∉ β.jumps := fun h => hxbad (Or.inr ⟨hxR, h⟩)
  rw [← hfx, hO x hxR hxJ hmJ]
  exact hamb x (lt_of_le_of_lt h0 hxR) hxJ

/-- **A word that is original left of the left record inherits the ambient left bound** (deterministic). -/
theorem fn_bound_neg_of_lOrig {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {β : BoundaryWord} {s : ExplState}
    (hP : GW1W.LProf s) (hO : GW1W.LOrig b jumps β s) (h0 : stRecL s ≤ 0)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    ∀ y, y < 0 → y ∉ β.jumps → β.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := by
  intro y hy hyJ
  obtain ⟨x₀, hx₀, hxy⟩ := hP.exists_eq (neg_pos.2 hy)
  set g := lProf (stChart s) with hg
  have hgr : ∀ x, rProf (stChart s) (-x) = -g x := fun x => by
    rw [hg, GW1W.lProf_eq, neg_neg]
  have hloc : ∀ᶠ z in 𝓝 (-y), β.fn (-z) = β.fn y := by
    have h1 : ∀ᶠ z in 𝓝 y, β.fn z = β.fn y := β.isPiecewiseConstantBoundaryData y hyJ
    have h2 : Tendsto (fun z : ℝ => -z) (𝓝 (-y)) (𝓝 y) := by
      simpa using (continuous_neg.tendsto (-y))
    exact h2.eventually h1
  have hcont : ContinuousAt g x₀ := hP.2.1.2.1.continuousAt (Ioi_mem_nhds hx₀)
  have hev : ∀ᶠ x in 𝓝 x₀, -stRecL s < x ∧ β.fn (-g x) = β.fn y := by
    refine (eventually_gt_nhds hx₀).and ?_
    have hloc' : ∀ᶠ z in 𝓝 (g x₀), β.fn (-z) = β.fn y := by rw [hxy]; exact hloc
    exact hcont.eventually hloc'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set T : Set ℝ := {x | -stRecL s < x ∧ -g x ∈ β.jumps} with hTdef
  have hT : T.Finite := by
    have hJn : ((β.jumps.image fun z => -z : Finset ℝ) : Set ℝ).Finite := Finset.finite_toSet _
    refine Set.Finite.of_finite_image (hJn.subset ?_) (hP.2.1.1.injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨-g x, hx.2, neg_neg _⟩
  have hbad : (((jumps.image fun z => -z : Finset ℝ) : Set ℝ) ∪ T).Finite :=
    (Finset.finite_toSet _).union hT
  obtain ⟨x, hxI, hxbad⟩ := ((Set.Ioo_infinite (by linarith : x₀ < x₀ + ε)).sdiff hbad).nonempty
  have hdist : dist x x₀ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hxI.1, hxI.2]
  obtain ⟨hxR, hfx⟩ := hball hdist
  have hxJ : -x ∉ jumps := fun h => hxbad (Or.inl (by
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨-x, h, neg_neg x⟩))
  have hmJ : rProf (stChart s) (-x) ∉ β.jumps := by
    rw [hgr]
    exact fun h => hxbad (Or.inr ⟨hxR, h⟩)
  have hxL : -x < stRecL s := by linarith
  have hO' := hO (-x) hxL hxJ hmJ
  rw [hgr] at hO'
  rw [← hfx, hO']
  exact hamb (-x) (lt_of_lt_of_le hxL h0) hxJ

/-! ### The sorted stage witness at a later launch -/

section Witness

open GW1W

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The sorted stage witness of the right walk at a later launch** (PROVE-T14-GW1W's induction step, with the
sortedness of the recentred stop word exported). -/
theorem exists_sorted_witness_right (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + θ * chiC κ < sleLambda κ) {k : ℕ} (hk : 0 < k) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ true) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
          none →
        (β ω).IsSorted ∧
          RInv κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) k) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
      IsStageWitness κ b jumps P h spec E ℓ β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        RInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
          leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ) := by
    intro ℓ
    obtain ⟨β, Y, hW, hI⟩ := exists_witness_right hκ hb hh hE hreg hamb ℓ
    exact ⟨β, Y, fun _ => ⟨hW, hI⟩⟩
  choose β Y hWI using H
  obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y fun ℓ hℓ => (hWI ℓ hℓ).1
  refine ⟨βk, Yk, hWk, ?_⟩
  have hstage : ∀ ℓ, ℓ < k → ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
        ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
          rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
            -sleLambda κ) := fun ℓ hℓ =>
    ae_stage_right hκ hb hh hE hreg (hWI ℓ hℓ).1 ((hWI ℓ hℓ).2.mono fun ω hω hl => (hω hl).1)
  have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
      ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        RInv κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        RReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
          leftLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ < sleLambda κ)) ∧
      ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some false) ∧
        ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some true) →
          rightLim b (stRecR (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ ≤
            -sleLambda κ)) := by
    refine ae_all_iff.2 fun ℓ => ?_
    by_cases hℓ : ℓ < k
    · filter_upwards [(hWI ℓ hℓ).2, hstage ℓ hℓ] with ω h1 h2 _ using ⟨h1, h2⟩
    · exact Eventually.of_forall fun ω h' => absurd h' hℓ
  filter_upwards [hall] with ω hω hlk
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
  obtain ⟨ℓ, hℓk, ⟨c', θ'', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
  have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
  obtain ⟨hinv, hst⟩ := hω ℓ hℓk
  obtain ⟨hI, hR, hroot⟩ := hinv hl
  obtain ⟨hnoL, hgood, hF2⟩ := hst hl
  obtain ⟨hInv, -, ha⟩ := rInv_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω)
    hgood hnoL hF2
  have hβ := hexpl ℓ ω hℓk hlk hl hn
  rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl, ← ha] at hβ
  rw [hβ]
  exact ⟨BoundaryWord.isSorted_shiftW (isSorted_stopWord κ _) _, hInv⟩

/-- **The sorted stage witness of the left walk at a later launch** (the mirror). -/
theorem exists_sorted_witness_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ false) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + θ * chiC κ) {k : ℕ} (hk : 0 < k) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h (boundaryWalkSpec b jumps θ false) E k β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
          none →
        (β ω).IsSorted ∧
          LInv κ θ b jumps (β ω) (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) k) := by
  set spec := boundaryWalkSpec b jumps θ false with hspec
  have H : ∀ ℓ, ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens), ℓ < k →
      IsStageWitness κ b jumps P h spec E ℓ β Y ∧
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        LInv κ θ b jumps (β ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        LReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
          -sleLambda κ < rightLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ) := by
    intro ℓ
    obtain ⟨β, Y, hW, hI⟩ := exists_witness_left hκ hb hh hE hreg hamb ℓ
    exact ⟨β, Y, fun _ => ⟨hW, hI⟩⟩
  choose β Y hWI using H
  obtain ⟨βk, Yk, hWk, hexpl⟩ := isStageWitness_succ_expl (isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    hk (fun j _ => hE.1 j) (fun j _ => hreg j) (fun j _ => hE.2.2.2 j) β Y fun ℓ hℓ => (hWI ℓ hℓ).1
  refine ⟨βk, Yk, hWk, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ ℓ, ℓ < k →
      ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        LInv κ θ b jumps (β ℓ ω) (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        LReady (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) ℓ) = .inl () →
          -sleLambda κ < rightLim b (stPt (ExplState.run κ b jumps spec (fun j => E j ω) ℓ)) + θ * chiC κ)) ∧
      ((ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) ≠ stThr (some true) ∧
        ((E ℓ ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (E ℓ ω)))) ∧
        (stStatus (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)) = stThr (some false) →
          sleLambda κ ≤
            leftLim b (stRecL (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1))) + θ * chiC κ)) := by
    refine ae_all_iff.2 fun ℓ => ?_
    by_cases hℓ : ℓ < k
    · filter_upwards [(hWI ℓ hℓ).2, ae_stage_left hκ hb hh hE hreg (hWI ℓ hℓ).1
        ((hWI ℓ hℓ).2.mono fun ω hω hl => (hω hl).1)] with ω h1 h2 _ using ⟨h1, h2⟩
    · exact Eventually.of_forall fun ω h' => absurd h' hℓ
  filter_upwards [hall] with ω hω hlk
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hlk
  obtain ⟨ℓ, hℓk, ⟨c', θ'', hl'⟩, -, hn, -⟩ := exists_last_launch spec (fun j => E j ω) hk hcθ
  have hl : (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rw [hl']; simp
  obtain ⟨hinv, hst⟩ := hω ℓ hℓk
  obtain ⟨hI, hR, hroot⟩ := hinv hl
  obtain ⟨hnoR, hgood, hF2⟩ := hst hl
  obtain ⟨hInv, -, ha⟩ := lInv_walk_step (D := fun j => E j ω) hκ hb hℓk hlk hl hn hI hR hroot (hreg ℓ ω)
    hgood hnoR hF2
  have hβ := hexpl ℓ ω hℓk hlk hl hn
  rw [instrAngle_walk hl, pastMap_last_of_launch hl, instrTime_walk hl, ← ha] at hβ
  rw [hβ]
  exact ⟨BoundaryWord.isSorted_shiftW (isSorted_stopWord κ _) _, hInv⟩

end Witness

end InteractingSLE.Theorem14.GW1Laws
