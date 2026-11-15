/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux62Girsanov
import InteractingSLE.Spec.Sec2.GirsanovCut

/-!
# Aux. lemma 62, probabilistic layer: the separation time after a restart time

Packet PROVE-GB7A2. The comparison of Aux. lemma 62 starts at a deterministic own time `q` ("choose a rational own
time … and map out its prefix", GB7a's proof) and runs while the relevant marks stay at distance `> δ` from the
driver. This file defines the first time after `q` at which a process of a finite family, killed at the lifetime,
is `≤ δ` (`hitAfter`), and proves that it is a stopping time when the processes are adapted before the lifetime and
continuous on `[0, ζ)` (`measurableSet_hitAfter_le`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {K : Type*}

/-- The first time at or after `q` at which some process of the family is `≤ δ`. -/
def hitAfter (q : ℝ≥0) (X : K → ℝ≥0 → Ω → ℝ) (δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : q ≤ t ∧ ∃ k, X k t ω ≤ δ), (t : ℝ≥0∞)

/-- A family killed at `ζ` (value `0` from `ζ` on). -/
def killedF (ζ : Ω → ℝ≥0∞) (X : K → ℝ≥0 → Ω → ℝ) : K → ℝ≥0 → Ω → ℝ := fun k => Girsanov.killed ζ (X k)

variable {q : ℝ≥0} {X : K → ℝ≥0 → Ω → ℝ} {δ : ℝ} {ζ : Ω → ℝ≥0∞}

theorem le_hitAfter (ω : Ω) : (q : ℝ≥0∞) ≤ hitAfter q X δ ω :=
  le_iInf₂ fun t ht => by exact_mod_cast ht.1

theorem lt_of_lt_hitAfter {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < hitAfter q X δ ω) (hqt : q ≤ t) (k : K) :
    δ < X k t ω := by
  by_contra h
  rw [not_lt] at h
  exact absurd (iInf₂_le (f := fun (t : ℝ≥0) (_ : q ≤ t ∧ ∃ k, X k t ω ≤ δ) => (t : ℝ≥0∞)) t ⟨hqt, k, h⟩)
    (not_le.2 ht)

/-- Before the killed hitting time the evolution is alive and every process exceeds `δ` (`0 ≤ δ`). -/
theorem lt_of_lt_hitAfter_killed (hδ : 0 ≤ δ) [Nonempty K] {ω : Ω} {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < hitAfter q (killedF ζ X) δ ω) (hqt : q ≤ t) :
    (t : ℝ≥0∞) < ζ ω ∧ ∀ k, δ < X k t ω := by
  have h := lt_of_lt_hitAfter ht hqt
  have hζ : (t : ℝ≥0∞) < ζ ω := by
    by_contra hn
    have := h (Classical.arbitrary K)
    simp only [killedF, Girsanov.killed, hn, ↓reduceIte] at this
    linarith
  refine ⟨hζ, fun k => ?_⟩
  have := h k
  rwa [killedF, Girsanov.killed_of_lt hζ] at this

/-- The killed hitting time comes no later than the lifetime. -/
theorem hitAfter_killed_le (hδ : 0 ≤ δ) [Nonempty K] (ω : Ω) (hqζ : (q : ℝ≥0∞) ≤ ζ ω) :
    hitAfter q (killedF ζ X) δ ω ≤ ζ ω := by
  rcases eq_or_ne (ζ ω) ⊤ with h | h
  · rw [h]; exact le_top
  · have hq : q ≤ (ζ ω).toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h]; exact hqζ
    refine (iInf₂_le (f := fun (t : ℝ≥0) (_ : q ≤ t ∧ ∃ k, killedF ζ X k t ω ≤ δ) => (t : ℝ≥0∞))
      (ζ ω).toNNReal ⟨hq, Classical.arbitrary K, ?_⟩).trans (ENNReal.coe_toNNReal h).le
    have ht : ¬ (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by
      rw [ENNReal.coe_toNNReal h]; exact lt_irrefl _
    simp only [killedF, Girsanov.killed, ht, ↓reduceIte]
    exact hδ

/-- The hitting set of a killed family is closed. -/
theorem isClosed_killedF (hδ : 0 ≤ δ) [Finite K] {ω : Ω}
    (hc : ∀ k, ContinuousOn (X k · ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    IsClosed {t : ℝ≥0 | ∃ k, killedF ζ X k t ω ≤ δ} := by
  by_cases hK : Nonempty K
  · have hU : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := isOpen_lt ENNReal.continuous_coe continuous_const
    have e : {t : ℝ≥0 | ∃ k, killedF ζ X k t ω ≤ δ}ᶜ =
        ⋂ k, ({t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} ∩ (X k · ω) ⁻¹' Ioi δ) := by
      ext t
      simp only [mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_le, mem_iInter, mem_inter_iff,
        mem_preimage, mem_Ioi]
      constructor
      · intro h k
        have hζ : (t : ℝ≥0∞) < ζ ω := by
          by_contra hn
          have := h (Classical.arbitrary K)
          simp only [killedF, Girsanov.killed, hn, ↓reduceIte] at this
          linarith
        refine ⟨hζ, ?_⟩
        have := h k
        rwa [killedF, Girsanov.killed_of_lt hζ] at this
      · intro h k
        rw [killedF, Girsanov.killed_of_lt (h k).1]; exact (h k).2
    rw [← isOpen_compl_iff, e]
    exact isOpen_iInter_of_finite fun k => (hc k).isOpen_inter_preimage hU isOpen_Ioi
  · rw [not_nonempty_iff] at hK
    convert isClosed_empty
    ext t; simp

/-- The infimum is attained. -/
theorem hitAfter_le_iff {ω : Ω} (hcl : IsClosed {t : ℝ≥0 | ∃ k, X k t ω ≤ δ}) {s : ℝ≥0} :
    hitAfter q X δ ω ≤ s ↔ ∃ t ∈ Icc q s, ∃ k, X k t ω ≤ δ := by
  constructor
  · intro h
    set S := {t : ℝ≥0 | q ≤ t ∧ ∃ k, X k t ω ≤ δ} with hS
    have hScl : IsClosed S := isClosed_Ici.inter hcl
    by_contra hno
    push Not at hno
    -- `S` misses `[q, s]`, so its infimum exceeds `s`
    have hSs : ∀ t ∈ S, s < t := fun t ht => by
      by_contra hts
      push Not at hts
      obtain ⟨k, hk⟩ := ht.2
      exact absurd hk (not_le.2 (hno t ⟨ht.1, hts⟩ k))
    rcases S.eq_empty_or_nonempty with hSe | hSn
    · have : hitAfter q X δ ω = ⊤ := by
        refine iInf₂_eq_top.2 fun t ht => ?_
        exact absurd (show t ∈ S from ht) (by rw [hSe]; exact Set.notMem_empty t)
      rw [this] at h; exact absurd h (by simp)
    · have ht₀ : sInf S ∈ S := hScl.csInf_mem hSn (OrderBot.bddBelow S)
      set t₀ := sInf S
      have hle : (t₀ : ℝ≥0∞) ≤ hitAfter q X δ ω :=
        le_iInf₂ fun t ht => by exact_mod_cast csInf_le (OrderBot.bddBelow S) ht
      have := hSs t₀ ht₀
      have h2 := hle.trans h
      exact absurd (by exact_mod_cast h2 : t₀ ≤ s) (not_le.2 this)
  · rintro ⟨t, ht, k, hk⟩
    exact (iInf₂_le (f := fun (t : ℝ≥0) (_ : q ≤ t ∧ ∃ k, X k t ω ≤ δ) => (t : ℝ≥0∞)) t ⟨ht.1, k, hk⟩).trans
      (by exact_mod_cast ht.2)

/-- **The killed hitting time after `q` is a stopping time.** -/
theorem measurableSet_hitAfter_le [Finite K] [Nonempty K] {𝓖 : Filtration ℝ≥0 mΩ} (hδ : 0 ≤ δ)
    (hX : ∀ k, AdaptedBefore 𝓖 ζ (X k))
    (hc : ∀ k ω, ContinuousOn (X k · ω) {t | (t : ℝ≥0∞) < ζ ω}) (s : ℝ≥0) :
    MeasurableSet[𝓖 s] {ω | hitAfter q (killedF ζ X) δ ω ≤ s} := by
  by_cases hqs : q ≤ s
  swap
  · have he : {ω | hitAfter q (killedF ζ X) δ ω ≤ s} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (by exact_mod_cast not_le.1 hqs) (le_hitAfter ω)
    rw [he]; exact @MeasurableSet.empty Ω (𝓖 s)
  -- the complement: alive at `s` and every process above `δ + 1/(m+1)` on a dense set of `[q, s]`
  set D : Set ℝ≥0 := {q, s} ∪ {r | ∃ x : ℚ, (q : ℝ) < x ∧ (x : ℝ) < s ∧ r = (x : ℝ).toNNReal} with hD
  have hDc : D.Countable := by
    refine (Set.countable_insert.2 (Set.countable_singleton s)).union ?_
    have : {r : ℝ≥0 | ∃ x : ℚ, (q : ℝ) < x ∧ (x : ℝ) < s ∧ r = (x : ℝ).toNNReal} ⊆
        Set.range fun x : ℚ => (x : ℝ).toNNReal := by
      rintro r ⟨x, -, -, rfl⟩; exact ⟨x, rfl⟩
    exact (Set.countable_range _).mono this
  have hDsub : D ⊆ Icc q s := by
    rintro r (hr | ⟨x, hx1, hx2, rfl⟩)
    · rcases hr with rfl | rfl
      · exact ⟨le_rfl, hqs⟩
      · exact ⟨hqs, le_rfl⟩
    · have hx0 : (0 : ℝ) ≤ x := q.2.trans hx1.le
      constructor
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]; exact hx1.le
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx0]; exact hx2.le
  have hDdense : Icc q s ⊆ closure D := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | hqt
    · exact subset_closure (Or.inl (Or.inl rfl))
    rcases ht.2.eq_or_lt with rfl | hts
    · exact subset_closure (Or.inl (Or.inr rfl))
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hq' : (q : ℝ) < max (q : ℝ) ((t : ℝ) - ε) ⊔ q ∨ (q : ℝ) < t := Or.inr (by exact_mod_cast hqt)
    obtain ⟨x, hx1, hx2⟩ := exists_rat_btwn (max_lt (by exact_mod_cast hqt : (q : ℝ) < t)
      (sub_lt_self (t : ℝ) hε))
    have hxt : (x : ℝ) < t := hx2
    have hx0 : (0 : ℝ) ≤ x := q.2.trans (le_max_left _ _ |>.trans hx1.le)
    refine ⟨(x : ℝ).toNNReal, Or.inr ⟨x, (le_max_left _ _).trans_lt hx1, hxt.trans (by exact_mod_cast hts),
      rfl⟩, ?_⟩
    rw [NNReal.dist_eq, Real.coe_toNNReal _ hx0, abs_sub_lt_iff]
    constructor <;> linarith [le_max_right (q : ℝ) ((t : ℝ) - ε)]
  have e : {ω | hitAfter q (killedF ζ X) δ ω ≤ s} =
      ({ω | (s : ℝ≥0∞) < ζ ω} ∩ ⋂ k, ⋃ m : ℕ, ⋂ r ∈ D,
        {ω | δ + 1 / ((m : ℝ) + 1) ≤ Girsanov.killed ζ (X k) r ω})ᶜ := by
    ext ω
    rw [Set.mem_ofPred_eq, hitAfter_le_iff (isClosed_killedF hδ (hc · ω))]
    simp only [mem_compl_iff, mem_inter_iff, Set.mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨t, ht, k, hk⟩ ⟨hsζ, hall⟩
      obtain ⟨m, hm⟩ := hall k
      have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast ht.2) hsζ
      -- by density and continuity the bound holds at `t`
      have hcont : ContinuousOn (fun r => Girsanov.killed ζ (X k) r ω) (Icc q s) := by
        refine ((hc k ω).mono fun r hr => lt_of_le_of_lt (by exact_mod_cast hr.2) hsζ).congr fun r hr => ?_
        exact Girsanov.killed_of_lt (lt_of_le_of_lt (by exact_mod_cast hr.2) hsζ)
      have hclosed : IsClosed (Icc q s ∩ (fun r => Girsanov.killed ζ (X k) r ω) ⁻¹'
          Ici (δ + 1 / ((m : ℝ) + 1))) := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
      have hsubD : D ⊆ Icc q s ∩ (fun r => Girsanov.killed ζ (X k) r ω) ⁻¹'
          Ici (δ + 1 / ((m : ℝ) + 1)) := fun r hr => ⟨hDsub hr, hm r hr⟩
      have htmem := (hclosed.closure_subset_iff.2 hsubD) (hDdense ht)
      have h1 : δ + 1 / ((m : ℝ) + 1) ≤ Girsanov.killed ζ (X k) t ω := htmem.2
      have h2 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      have : killedF ζ X k t ω ≤ δ := hk
      simp only [killedF] at this
      linarith
    · intro h
      by_contra hno
      push Not at hno
      apply h
      -- alive at `s`
      have hsζ : (s : ℝ≥0∞) < ζ ω := by
        by_contra hn
        have := hno s ⟨hqs, le_rfl⟩ (Classical.arbitrary K)
        simp only [killedF, Girsanov.killed, hn, ↓reduceIte] at this
        linarith
      refine ⟨hsζ, fun k => ?_⟩
      -- a positive margin by compactness
      have hcont : ContinuousOn (fun r => X k r ω) (Icc q s) :=
        (hc k ω).mono fun r hr => lt_of_le_of_lt (by exact_mod_cast hr.2) hsζ
      obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hqs) hcont
      have hr₀ζ : (r₀ : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hr₀.2) hsζ
      have hpos : δ < X k r₀ ω := by
        have := hno r₀ hr₀ k
        rwa [killedF, Girsanov.killed_of_lt hr₀ζ] at this
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hpos)
      refine ⟨m, fun r hr => ?_⟩
      have hrI := hDsub hr
      have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hrI.2) hsζ
      rw [Girsanov.killed_of_lt hrζ]
      have := hmin hrI
      simp only [Set.mem_ofPred_eq] at this
      linarith
  rw [e]
  refine MeasurableSet.compl (MeasurableSet.inter ?_ (MeasurableSet.iInter fun k => MeasurableSet.iUnion
    fun m => MeasurableSet.biInter hDc fun r hr => ?_))
  · have := (hX (Classical.arbitrary K) s univ MeasurableSet.univ)
    simpa using this
  · have hr := (hDsub hr).2
    exact 𝓖.mono hr _ (measurableSet_le measurable_const (Girsanov.measurable_killed (hX k) r))

end GB7a

end InteractingSLE
