/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvHead
import InteractingSLE.Spec.Supplement.SB2JyHull
import InteractingSLE.Spec.Supplement.SB2QtSets

/-!
# The lower walk's prefix through a stage `ℓ ≤ relOff` lies in the filled upper history (deterministic)

Worker REVIEW-FABLE-T14 (the head inclusion `Qt.SB2LowerBaseHeadStatement`, the named input of
`Qt.sb2LowerBaseLawStatement_of_head`).

Supplement p. 632: "Erase `B` through its unique visit to `R`"; "the erased initial portion lies in `K_A`". For the
lower walk `B` (a family `D` of drivers with LIFTSET's per-sample walk facts) and `R = max(A ∩ ℝ)`:

* `seed_of_le_relOff`: at a stage `1 ≤ ℓ ≤ relOff`, if `R` is already in `B`'s physical part then `B` is at `R`
  (`R` first enters at `entryStage`; `relOff ≤ entryStage` unless the entry is a mark, where `relOff = entryStage + 1`
  and the launch there starts from `R`, `Lk.launch_seed_of_not_zeroRoot`);
* `mem_physSet_of_relOff_pos`: `relOff ≥ 1` forces `R` onto the walk;
* **`statePhysicalSet_inter_H_subset_fillH`**: at a launching stage `ℓ ≤ relOff`, `B`'s physical part through `ℓ`
  meets `ℍ` only inside `fill A`, given that the head of every proper parametrization up to a visit of `R` lies in
  `hullK A` (S2, `Lk.sb2LowerHeadHull`'s argument): `Lk.subset_head_of_futPart` puts the prefix on the head;
* `tipSet_zero_inter_H_eq_empty`: a piece run for time `0` from a real point adds no point of `ℍ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Qu

open Exist Exist.Staged Exist.StagedLaw GW1Bookkeep GW1W Lk LuM

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **`relOff ≥ 1` puts `R` on the walk**: some stage's physical part contains `R`. -/
theorem exists_mem_of_relOff_pos {R : ℝ} (h : 0 < relOff κ θ b jumps R D) :
    ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) := by
  classical
  by_contra hno
  have he : entryStage κ θ b jumps R D = 0 := by
    unfold entryStage
    simp only [hno, ↓reduceDIte]
  have hs : startOff κ θ b jumps R D = 0 := by
    unfold startOff
    rw [he]
  have hA : ¬ ArcEntry κ θ b jumps R D := by
    unfold ArcEntry
    rw [he]
    decide
  have hM : ¬ MarkEntry κ θ b jumps R D := fun hM => hA hM.1
  rw [relOff_of_not_mark κ θ b jumps hM, hs] at h
  exact lt_irrefl _ h

/-- **The seed condition at a stage `1 ≤ ℓ ≤ relOff`**: if `R` is in the physical part through `ℓ`, the walk is at
`R` there. -/
theorem seed_of_le_relOff (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hX : RunExitData κ b jumps θ D) (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length) = stDone)
    {R : ℝ} (hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ relOff κ θ b jumps R D)
    (hRℓ : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ)) :
    stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) = R := by
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hex : ∃ n, (R : ℂ) ∈ statePhysicalSet 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) := ⟨m, hRℓ⟩
  have hem : entryStage κ θ b jumps R D ≤ m := by
    by_contra hlt
    exact (entryStage_spec κ θ b jumps hex).2 m (by omega) hRℓ
  by_cases hM : MarkEntry κ θ b jumps R D
  · have hro := relOff_of_mark κ θ b jumps hM
    have hso := (startOff_eq κ θ b jumps R D).1 hM.1
    have hrel : m + 1 = relOff κ θ b jumps R D := by omega
    have hZ : ¬ ZeroRoot κ θ b jumps R D := fun hZ => hZ.2 hM
    have hs := (launch_seed_of_not_zeroRoot hb hX hP hW hlm hlh hallow hdone hR hZ).2
    rw [hrel] at hRℓ ⊢
    exact hs hRℓ
  · have hro := relOff_of_not_mark κ θ b jumps hM
    have hle : startOff κ θ b jumps R D ≤ entryStage κ θ b jumps R D := by
      unfold startOff
      omega
    omega

/-- **The prefix through a launching stage `ℓ ≤ relOff` lies in the filled upper history** (in `ℍ`). -/
theorem statePhysicalSet_inter_H_subset_fillH (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hX : RunExitData κ b jumps θ D) (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j)
    (hallow : ∀ n, 1 ≤ n → AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hdone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D
      (boundaryWalkSpec b jumps θ true).2.2.length) = stDone)
    {β₀ : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D) {A : Set ℂ} {R : ℝ}
    (hK : ∀ tL : ℝ≥0, β₀ tL = R → β₀ '' Icc 0 tL ⊆ hullK A) {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hℓ : ℓ ≤ relOff κ θ b jumps R D) :
    statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D ℓ) ∩ H ⊆ fillH A := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ1
  · intro z hz
    have h0 : statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = {0} := by
      have e : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0 = ExplState.init 0 := rfl
      rw [e]
      exact statePhysicalSet_init
    rw [h0] at hz
    obtain ⟨hz0, hzH⟩ := hz
    rw [mem_singleton_iff] at hz0
    have hzH' : (0 : ℝ) < z.im := hzH
    rw [hz0] at hzH'
    exact absurd hzH' (lt_irrefl _)
  -- `R` is on the walk
  obtain ⟨n, hn⟩ := exists_mem_of_relOff_pos (lt_of_lt_of_le hℓ1 hℓ)
  set N := (boundaryWalkSpec b jumps θ true).2.2.length with hNdef
  have hphys : ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D =
      statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) :=
    physSet_walk_eq_of_done le_rfl hdone
  have hRphys : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D := by
    rw [hphys]
    rcases le_total (n + 1) N with hle | hle
    · exact statePhysicalSet_mono hle hn
    · rw [← Lv.run_eq_of_length_le (boundaryWalkSpec b jumps θ true) D hle]
      exact hn
  obtain ⟨tL, htL⟩ : ∃ tL, β₀ tL = R := by
    rw [← hβr] at hRphys
    exact hRphys
  -- the prefix lies on the head
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ D hcθ
  have hℓN : ℓ ≤ N := (lt_length_of_launch _ D hl).le
  obtain ⟨hPc, hqP⟩ := prefix_facts hW.1 hW.2 ℓ
  have hF := futPart_run hW.1 hW.2 (futPart_start (hqP hnd) hnd) N hℓN
  have hβr' : range β₀ = statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) := by
    rw [hβr, hphys]
  have hsub := subset_head_of_futPart hβ hβ0 hβr' hF hdone hPc (Or.inl (Or.inl rfl)) (hqP hnd) htL
    (fun hR' => by rw [seed_of_le_relOff hb hX hP hW hlm hlh hallow hdone hRphys hℓ1 hℓ hR'])
  intro z ⟨hz, hzH⟩
  obtain ⟨t, ht, rfl⟩ := hsub hz
  rcases hK tL htL ⟨t, ⟨zero_le, ht⟩, rfl⟩ with h1 | ⟨x, -, hx⟩
  · exact h1
  · exfalso
    have : (β₀ t).im = 0 := by rw [← hx]; rfl
    exact absurd hzH (by show ¬ (0 < (β₀ t).im); rw [this]; exact lt_irrefl 0)

/-- **A piece run for time `0` from a real point adds no point of `ℍ`**: if the inverse chart has the boundary limit
`f 0` at `0`, real, and the driver starts at `0`, the stage's trace set at time `0` meets `ℍ` nowhere. -/
theorem tipSet_zero_inter_H_eq_empty {c : Chart} {f : ℂ → ℂ} (hf : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (f 0)))
    {q : ℝ} (hq : f 0 = q) {W : ℝ≥0 → ℝ} (hW0 : W 0 = 0) :
    c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) 0).toNNReal) 0 ∩ H = ∅ := by
  have hα : IsGeneratingTrace W 0 (fun _ => (0 : ℂ)) :=
    ⟨rfl, continuousOn_const, fun t ht => absurd ht (not_lt.2 zero_le)⟩
  have hWc : ContinuousOn W {t : ℝ≥0 | (t : ℝ≥0∞) ≤ 0} := by
    have e : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ 0} = {0} := by ext t; simp
    rw [e]
    exact continuousOn_singleton _ _
  have hset := CounterflowRange.tipSet_stopped_eq_of_tendsto (f := f) hα hWc hW0 fun _ _ => hf
  rw [hset]
  ext z
  simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
  rintro ⟨_, ⟨t, -, rfl⟩, rfl⟩ hz
  rw [hq] at hz
  have hz' : (0 : ℝ) < ((q : ℂ)).im := hz
  simp at hz'

end InteractingSLE.Theorem14.SB.Qu
