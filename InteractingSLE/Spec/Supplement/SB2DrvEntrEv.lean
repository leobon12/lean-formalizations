/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEntr

/-!
# SB2(1)'s entrance event and the entrance union on it

Packet PROVE-T14-SB2DRV (round 3), clause (E1) of `SB2EntranceK2NStatement`. For capped versions `γ_n = γ ∘ capTime n ζ`
of a path `γ` with lifetime `ζ` and first visit `T = firstVisit γ ζ z < ζ` of `z`:

* `hitQ_capped_eq`: once `T < n`, the first hit of `z` by `γ_n` is `T`, and `γ_n([0, T]) = γ([0, T])`;
* **`iUnion_rangeUpTo_capped`**: `⋃ n γ_n([0, T_n]) = γ([0, T])` (`T_n` the first hit of `z` by `γ_n`);
* **`exists_live_iff`**: `T < ζ` iff for some `n` the first hit of `γ_n` is finite and before its killing record
  `cutLife ζ n`, an event of the killed histories through the hits.

For SB2(1) (`EntranceUnion`): the **entrance event** `D.event = launchSet ∩ ⋃ n {killed history of η_n through T_n is
live}` is an event of the entrance σ-algebra (`measurableSet_event`), lies in the launch event, and is almost surely
the entrance event `{T_L < ζ}` on the launch event (`ae_mem_event_iff`); on it the entrance union is almost surely
`A ∪ η([0, T_L])` (`ae_set_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart

/-! ### Iterated unions, pointwise -/

section Pointwise

variable {Ω : Type*} {𝒴 : Type*} {A : Ω → Set ℂ} {η : ℕ → Ω → ℝ≥0 → ℂ} {Y : Ω → 𝒴}
  {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞}

theorem mem_iterSet_iff {ω : Ω} {x : ℂ} (n : ℕ) :
    x ∈ iterSet A η Y S n ω ↔ x ∈ A ω ∨ ∃ j ≤ n, x ∈ rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω))) := by
  induction n with
  | zero =>
    simp only [iterSet, mem_union, Nat.le_zero, exists_eq_left]
  | succ n ih =>
    simp only [iterSet, mem_union, ih]
    constructor
    · rintro ((h1 | ⟨j, hj, h2⟩) | h3)
      · exact Or.inl h1
      · exact Or.inr ⟨j, hj.trans n.le_succ, h2⟩
      · exact Or.inr ⟨n + 1, le_rfl, h3⟩
    · rintro (h1 | ⟨j, hj, h2⟩)
      · exact Or.inl (Or.inl h1)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hj) with hlt | rfl
        · exact Or.inl (Or.inr ⟨j, Nat.lt_succ_iff.1 hlt, h2⟩)
        · exact Or.inr h2

/-- The limit of the iterated unions is `A ∪ ⋃ n η_n([0, τ_n])`. -/
theorem limSet_eq (ω : Ω) :
    limSet A η Y S ω = A ω ∪ ⋃ n, rangeUpTo (η n ω) (S (Y ω) (pathCoord (η n ω))) := by
  ext x
  simp only [limSet, mem_iUnion, mem_iterSet_iff, mem_union]
  constructor
  · rintro ⟨n, h1 | ⟨j, -, h2⟩⟩
    · exact Or.inl h1
    · exact Or.inr ⟨j, h2⟩
  · rintro (h1 | ⟨j, h2⟩)
    · exact ⟨0, Or.inl h1⟩
    · exact ⟨j, Or.inr ⟨j, le_rfl, h2⟩⟩

end Pointwise

/-- The killed histories through their own (finite) time that are still alive then. -/
def liveHist : Set KHist := {k | k.1.1 < ⊤ ∧ k.2 = ⊤}

theorem measurableSet_liveHist : MeasurableSet liveHist :=
  (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const).inter
    (measurable_snd (measurableSet_singleton ⊤))

theorem khistOf_mem_liveHist_iff {c : ℚ≥0 → ℂ} {ζ T : ℝ≥0∞} :
    khistOf c ζ T ∈ liveHist ↔ T < ⊤ ∧ T < ζ := by
  show T < ⊤ ∧ lifeRec ζ T = ⊤ ↔ _
  unfold lifeRec
  by_cases hζ : ζ ≤ T
  · rw [ite_eq_left hζ]
    constructor
    · rintro ⟨h1, h2⟩
      exact absurd (h2 ▸ hζ) (not_le.2 h1)
    · rintro ⟨-, h2⟩
      exact absurd hζ (not_le.2 h2)
  · rw [ite_eq_right hζ]
    exact ⟨fun h => ⟨h.1, not_le.1 hζ⟩, fun h => ⟨h.1, rfl⟩⟩

/-! ### Capped versions of one path -/

section Capped

variable {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {z : ℂ} {γc : ℕ → ℝ≥0 → ℂ}

theorem coe_cap_toNNReal (ζ : ℝ≥0∞) (m : ℝ≥0) : (((min ζ (m : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞) = min ζ m :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

theorem capTime_of_le {m : ℝ≥0} {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ min ζ m) : capTime m ζ t = t := by
  unfold capTime
  refine min_eq_left ?_
  rw [← ENNReal.coe_le_coe, coe_cap_toNNReal]
  exact ht

theorem coe_capTime_le (m : ℝ≥0) (t : ℝ≥0) : ((capTime m ζ t : ℝ≥0) : ℝ≥0∞) ≤ min ζ m := by
  rw [← coe_cap_toNNReal ζ m, ENNReal.coe_le_coe]
  exact min_le_right _ _

theorem capTime_le_self (m : ℝ≥0) (t : ℝ≥0) : capTime m ζ t ≤ t := min_le_left _ _

/-- **Once the first visit is below the cap, the capped version hits `z` first at the first visit**, and the two
ranges up to it agree. -/
theorem hitQ_capped_eq {n : ℕ} (hc : Continuous (γc n)) (hver : ∀ t, γc n t = γ (capTime (n : ℝ≥0) ζ t))
    (hT : firstVisit γ ζ z < ζ) (hTn : firstVisit γ ζ z < n) :
    hitQ z (pathCoord (γc n)) = firstVisit γ ζ z ∧
      rangeUpTo (γc n) (firstVisit γ ζ z) = rangeUpTo γ (firstVisit γ ζ z) := by
  set T := firstVisit γ ζ z with hTdef
  have hTc : T < min ζ (n : ℝ≥0) := lt_min hT (by exact_mod_cast hTn)
  refine ⟨?_, ?_⟩
  · rw [hitQ_pathCoord hc]
    refine le_antisymm ?_ ?_
    · refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
      have hlt : T < min r (min ζ (n : ℝ≥0)) := lt_min hr hTc
      obtain ⟨s, hs⟩ := iInf_lt_iff.1 hlt
      obtain ⟨⟨hsζ, hsz⟩, hs'⟩ := iInf_lt_iff.1 hs
      have hsc : (s : ℝ≥0∞) ≤ min ζ (n : ℝ≥0) := (hs'.trans_le (min_le_right _ _)).le
      have hγc : γc n s = z := by rw [hver, capTime_of_le hsc, hsz]
      exact (iInf₂_le s hγc).trans (hs'.le.trans (min_le_left _ _))
    · refine le_iInf₂ fun s hs => ?_
      rw [hver] at hs
      by_cases hsc : (s : ℝ≥0∞) ≤ min ζ (n : ℝ≥0)
      · rw [capTime_of_le hsc] at hs
        exact iInf₂_le s ⟨hsc.trans (min_le_left _ _), hs⟩
      · have h1 := coe_capTime_le (ζ := ζ) (n : ℝ≥0) s
        exact (iInf₂_le (capTime (n : ℝ≥0) ζ s) ⟨h1.trans (min_le_left _ _), hs⟩).trans
          (h1.trans (not_le.1 hsc).le)
  · ext x
    simp only [rangeUpTo, mem_inter_iff, mem_image, mem_ofPred_eq]
    refine and_congr_left fun _ => exists_congr fun t => and_congr_right fun ht => ?_
    rw [hver, capTime_of_le (ht.trans hTc.le)]

/-- Every capped range up to its first hit lies in the range up to the first visit (when the visit is live). -/
theorem rangeUpTo_capped_subset (hc : ∀ n, Continuous (γc n))
    (hver : ∀ (n : ℕ) t, γc n t = γ (capTime (n : ℝ≥0) ζ t)) (hT : firstVisit γ ζ z < ζ) (n : ℕ) :
    rangeUpTo (γc n) (hitQ z (pathCoord (γc n))) ⊆ rangeUpTo γ (firstVisit γ ζ z) := by
  by_cases hTn : firstVisit γ ζ z < n
  · rw [(hitQ_capped_eq (hc n) (hver n) hT hTn).1, (hitQ_capped_eq (hc n) (hver n) hT hTn).2]
  · rintro x ⟨⟨t, -, rfl⟩, hxH⟩
    refine ⟨⟨capTime (n : ℝ≥0) ζ t, ?_, (hver n t).symm⟩, hxH⟩
    exact ((coe_capTime_le (n : ℝ≥0) t).trans (min_le_right _ _)).trans (not_lt.1 hTn)

/-- **The capped ranges up to their first hits exhaust the range up to the first visit.** -/
theorem iUnion_rangeUpTo_capped (hc : ∀ n, Continuous (γc n))
    (hver : ∀ (n : ℕ) t, γc n t = γ (capTime (n : ℝ≥0) ζ t)) (hT : firstVisit γ ζ z < ζ) :
    (⋃ n, rangeUpTo (γc n) (hitQ z (pathCoord (γc n)))) = rangeUpTo γ (firstVisit γ ζ z) := by
  refine Subset.antisymm (iUnion_subset (rangeUpTo_capped_subset hc hver hT)) ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hT)
  rw [← (hitQ_capped_eq (hc n) (hver n) hT hn).2, ← (hitQ_capped_eq (hc n) (hver n) hT hn).1]
  exact subset_iUnion (fun n => rangeUpTo (γc n) (hitQ z (pathCoord (γc n)))) n

/-- **The live first visit is read off the killed histories of the capped versions through their first hits.** -/
theorem exists_live_iff (hc : ∀ n, Continuous (γc n))
    (hver : ∀ (n : ℕ) t, γc n t = γ (capTime (n : ℝ≥0) ζ t)) :
    (∃ n : ℕ, hitQ z (pathCoord (γc n)) < ⊤ ∧ hitQ z (pathCoord (γc n)) < cutLife ζ (n : ℝ≥0)) ↔
      firstVisit γ ζ z < ζ := by
  constructor
  · rintro ⟨n, htop, hlife⟩
    have hex : ∃ s, γc n s = z := by
      by_contra hno
      push Not at hno
      rw [hitQ_pathCoord_eq_top (hc n) hno] at htop
      exact lt_irrefl _ htop
    obtain ⟨s₀, hs₀, he, -⟩ := exists_hitQ_pathCoord (hc n) hex
    rw [he] at hlife
    rw [hver] at hs₀
    have h1 := coe_capTime_le (ζ := ζ) (n : ℝ≥0) s₀
    have hle : firstVisit γ ζ z ≤ capTime (n : ℝ≥0) ζ s₀ := iInf₂_le _ ⟨h1.trans (min_le_left _ _), hs₀⟩
    refine hle.trans_lt ?_
    unfold cutLife at hlife
    by_cases hζn : ζ ≤ (n : ℝ≥0)
    · rw [ite_eq_left hζn] at hlife
      exact (ENNReal.coe_le_coe.2 (capTime_le_self _ _)).trans_lt hlife
    · refine (h1.trans (min_le_right _ _)).trans_lt (not_le.1 hζn)
  · intro hT
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hT)
    refine ⟨n, ?_, ?_⟩ <;> rw [(hitQ_capped_eq (hc n) (hver n) hT hn).1]
    · exact lt_of_lt_of_le hT le_top
    · unfold cutLife
      by_cases hζn : ζ ≤ (n : ℝ≥0)
      · rw [ite_eq_left hζn]; exact hT
      · rw [ite_eq_right hζn]; exact lt_of_lt_of_le hT le_top

end Capped

/-! ### The marks of each capped path -/

theorem comap_ruleHist_le_iterMarks {Ω : Type*} [MeasurableSpace Ω] {𝒢 : MeasurableSpace Ω}
    {η : ℕ → Ω → ℝ≥0 → ℂ} {ζ : ℕ → Ω → ℝ≥0∞} {𝒴 : Type*} {Y : Ω → 𝒴} {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞} (n : ℕ) :
    MeasurableSpace.comap (ruleHist (η n) (ζ n) Y S) inferInstance ≤ iterMarks 𝒢 η ζ Y S n := by
  cases n with
  | zero => exact le_sup_right
  | succ n => exact le_sup_right

/-! ### SB2(1)'s entrance event -/

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

/-- **The entrance event**: a launch, and for some cap the capped upper flow hits `L` before its killing record. -/
def event : Set Ω :=
  launchSet κ b jumps E (k + 1) ∩ ⋃ n : ℕ, ruleHist (D.ηc n) (capLife ζ n) D.point hitQ ⁻¹' liveHist

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem event_subset : D.event ⊆ launchSet κ b jumps E (k + 1) := inter_subset_left

/-- **The entrance event is an event of the entrance σ-algebra.** -/
theorem measurableSet_event (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) : MeasurableSet[D.marks] D.event := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  have hl : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (launchSet κ b jumps E (k + 1)) :=
    measurableSet_launch_pastSigma HP.boundary hS.1 (HP.drivers_regular _) (k + 1)
  refine MeasurableSet.inter (D.past_le_marks _ hl) (MeasurableSet.iUnion fun n => ?_)
  exact le_iSup (iterMarks _ D.ηc (capLife ζ) D.point hitQ) n _
    (comap_ruleHist_le_iterMarks n _ ⟨liveHist, measurableSet_liveHist, rfl⟩)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **On the launch event, the entrance event is almost surely `{T_L < ζ}`.** -/
theorem ae_mem_event_iff : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
    (ω ∈ D.event ↔ firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω) := by
  filter_upwards [D.version, D.Lp_eq] with ω hv hL hl
  have hz : D.point ω = (realMin (lowerPrefix κ b jumps E (k + 1) u ω) : ℂ) := by
    simp only [point, hL hl]
  have hlive := exists_live_iff (γ := η ω) (ζ := ζ ω) (z := D.point ω) (γc := fun n => D.ηc n ω)
    (fun n => D.paths.cont n ω) hv
  rw [hz] at hlive
  rw [← hlive]
  simp only [event, mem_inter_iff, mem_iUnion, mem_preimage, hl, true_and]
  refine exists_congr fun n => ?_
  rw [← hz]
  exact khistOf_mem_liveHist_iff

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **On the entrance event, the entrance union is almost surely `A ∪ η([0, T_L])`.** -/
theorem ae_set_eq : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
    firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)) < ζ ω →
    D.set ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω ∪
      rangeUpTo (η ω) (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω))) := by
  filter_upwards [D.version, D.Lp_eq] with ω hv hL hl hT
  have hz : D.point ω = (realMin (lowerPrefix κ b jumps E (k + 1) u ω) : ℂ) := by
    simp only [point, hL hl]
  have hU := iUnion_rangeUpTo_capped (γ := η ω) (ζ := ζ ω) (z := D.point ω) (γc := fun n => D.ηc n ω)
    (fun n => D.paths.cont n ω) hv (by rw [hz]; exact hT)
  rw [set, limSet_eq, hU, hz]

end EntranceUnion

end InteractingSLE.Theorem14.SB.Lv
