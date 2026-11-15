/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvAct

/-!
# SB2(2)'s v6 measurability: the actual piece at random times, and the visit time

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). For a measurable actual family `Ê`, regular with regular launches at
every sample:

* **`measurable_pcPt_at`**: the point of the launched piece `n` at a measurable random time below its lifetime
  (`measurable_at_of_dense_good` with the readings of `LuM.pfam`);
* `mem_pcPt_image_le_iff` (deterministic): a point is on the piece up to time `a` iff rational readings up to `a` come
  arbitrarily close;
* **`measurable_visitTime`**: the first visit of a fixed point by the launched piece `n` (`Lk.visitTime`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal LuM GW1W GW1Bookkeep

/-- Every rational is a value of the enumeration. -/
theorem exists_ofNat_eq (q : ℚ) : ∃ i, Denumerable.ofNat ℚ i = q :=
  ⟨@Encodable.encode ℚ Denumerable.toEncodable q, Denumerable.ofNat_encode q⟩

theorem ratPt_eq_ofNat (i : ℕ) : ratPt i = (((Denumerable.ofNat ℚ i : ℚ) : ℝ)).toNNReal := rfl

/-- **Rationals strictly inside `(0, L)` near a time `σ ≤ L`.** -/
theorem exists_rat_near_lt {σ : ℝ≥0} {L : ℝ≥0∞} (hσ : (σ : ℝ≥0∞) ≤ L) (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < L ∧ |(q : ℝ) - σ| < ε := by
  -- an upper bound `u ≤ L` above `max 0 (σ - ε)`, at distance `< ε` above `σ`
  obtain ⟨u, hu1, hu2, hu3⟩ : ∃ u : ℝ, max 0 ((σ : ℝ) - ε) < u ∧ u ≤ σ + ε ∧ ∀ q : ℝ, 0 < q → q < u →
      (((q.toNNReal : ℝ≥0)) : ℝ≥0∞) < L := by
    by_cases hLt : L = ⊤
    · exact ⟨σ + ε, max_lt (by positivity) (by linarith), le_rfl, fun q _ _ => by simp [hLt]⟩
    · set Lr : ℝ := L.toReal with hLr
      have hLr0 : 0 < Lr := ENNReal.toReal_pos hL.ne' hLt
      have hσL : (σ : ℝ) ≤ Lr := by
        have := ENNReal.toReal_mono hLt hσ; simpa using this
      refine ⟨min Lr (σ + ε), lt_min (max_lt hLr0 (by linarith)) (max_lt (by positivity) (by linarith)),
        min_le_right _ _, fun q hq hqu => ?_⟩
      have hqL : q < Lr := lt_of_lt_of_le hqu (min_le_left _ _)
      exact (ENNReal.ofReal_lt_iff_lt_toReal hq.le hLt).2 hqL
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hu1
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
  refine ⟨q, by exact_mod_cast hq0, hu3 q hq0 hq2, abs_lt.2 ⟨?_, ?_⟩⟩
  · linarith [le_max_right 0 ((σ : ℝ) - ε)]
  · linarith

/-! ### The first visit (deterministic) -/

section Visit

variable {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → Drv}

/-- `Lk.visitTime` with a complex target. -/
def visitTime' (s : ExplState) (e : Drv) (z : ℂ) : ℝ≥0 :=
  sInf {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2 ∧ pcPt s e t = z}

theorem visitTime_eq_visitTime' (s : ExplState) (e : Drv) (R : ℝ) : visitTime s e R = visitTime' s e (R : ℂ) := rfl

/-- **The first visit is at most `a`** iff the piece never visits, or visits by time `a`. -/
theorem visitTime'_le_iff (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) {n : ℕ}
    (hl : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none) (z : ℂ) (a : ℝ≥0) :
    visitTime' (wRun κ θ b J D n) (D n) z ≤ a ↔
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → pcPt (wRun κ θ b J D n) (D n) t ≠ z) ∨
        z ∈ pcPt (wRun κ θ b J D n) (D n) '' {t : ℝ≥0 | t ≤ a ∧ (t : ℝ≥0∞) ≤ (D n).2} := by
  set p := pcPt (wRun κ θ b J D n) (D n)
  set H : Set ℝ≥0 := {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2 ∧ p t = z} with hH
  have hc := continuousOn_pcPt_launch hP hl
  have hHc : IsClosed H := by
    have hS : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} := isClosed_le ENNReal.continuous_coe continuous_const
    have := hc.preimage_isClosed_of_isClosed hS (isClosed_singleton (x := z))
    convert this using 1
    ext t
    simp only [hH, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
    rfl
  have hbdd : BddBelow H := ⟨0, fun t _ => zero_le⟩
  unfold visitTime'
  rcases H.eq_empty_or_nonempty with hE | hne
  · rw [← hH, hE, NNReal.sInf_empty]
    refine ⟨fun _ => Or.inl fun t ht hpt => ?_, fun _ => zero_le⟩
    have : t ∈ H := ⟨ht, hpt⟩
    rw [hE] at this
    exact this
  · rw [← hH]
    constructor
    · intro h
      exact Or.inr ⟨sInf H, ⟨h, (hHc.csInf_mem hne hbdd).1⟩, (hHc.csInf_mem hne hbdd).2⟩
    · rintro (h | ⟨t, ⟨hta, htL⟩, hpt⟩)
      · obtain ⟨t, ht, hpt⟩ := hne
        exact absurd hpt (h t ht)
      · exact (csInf_le hbdd ⟨htL, hpt⟩).trans hta

/-- **A point is on the piece up to time `a` iff rational readings up to `a` come arbitrarily close.** -/
theorem mem_pcPt_image_le_iff (hP : RegLaunches κ b J (boundaryWalkSpec b J θ true) D) {n : ℕ}
    (hl : (wRun κ θ b J D (n + 1)).2.2.2.1 n ≠ none) {z : ℂ} {a : ℝ≥0} :
    z ∈ pcPt (wRun κ θ b J D n) (D n) '' {t : ℝ≥0 | t ≤ a ∧ (t : ℝ≥0∞) ≤ (D n).2} ↔
      ∀ k : ℕ, dist (pcPt (wRun κ θ b J D n) (D n) 0) z < 1 / ((k : ℝ) + 1) ∨
        ∃ q : ℚ, 0 < q ∧ (q : ℝ).toNNReal ≤ a ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (D n).2 ∧
          dist (pcPt (wRun κ θ b J D n) (D n) (q : ℝ).toNNReal) z < 1 / ((k : ℝ) + 1) := by
  have hc := continuousOn_pcPt_launch hP hl
  have hK : IsCompact {t : ℝ≥0 | t ≤ a ∧ (t : ℝ≥0∞) ≤ (D n).2} := by
    exact (isCompact_Icc (a := (0 : ℝ≥0)) (b := a)).of_isClosed_subset
      ((isClosed_le continuous_id continuous_const).inter (isClosed_le ENNReal.continuous_coe continuous_const))
      fun t ht => ⟨zero_le, ht.1⟩
  have hcl : IsClosed (pcPt (wRun κ θ b J D n) (D n) '' {t : ℝ≥0 | t ≤ a ∧ (t : ℝ≥0∞) ≤ (D n).2}) :=
    (hK.image_of_continuousOn (hc.mono fun t ht => ht.2)).isClosed
  constructor
  · rintro ⟨t, ⟨hta, ht⟩, rfl⟩ k
    by_cases ht0 : t = 0
    · left
      rw [ht0, dist_self]
      positivity
    · right
      have htpos : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht0)
      have hcw := hc t ht
      rw [Metric.continuousWithinAt_iff] at hcw
      obtain ⟨δ, hδ, hδc⟩ := hcw (1 / ((k : ℝ) + 1)) (by positivity)
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 ((t : ℝ) - δ) < t from max_lt htpos (by linarith))
      have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (le_max_left _ _) hq1
      have hqt : ((q : ℝ).toNNReal : ℝ≥0) < t := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0.le]; exact hq2
      refine ⟨q, by exact_mod_cast hq0, hqt.le.trans hta, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hqt) ht, ?_⟩
      have hmem : ((q : ℝ).toNNReal) ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} :=
        le_trans (ENNReal.coe_le_coe.2 hqt.le) ht
      have hd : dist ((q : ℝ).toNNReal) t < δ := by
        rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0.le, abs_lt]
        constructor <;> linarith [le_max_right 0 ((t : ℝ) - δ)]
      exact hδc hmem hd
  · intro h
    refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    rcases h k with h0 | ⟨q, -, hqa, hqL, hq⟩
    · exact ⟨_, ⟨0, ⟨zero_le, by simp⟩, rfl⟩, by rw [dist_comm]; linarith⟩
    · exact ⟨_, ⟨_, ⟨hqa, hqL.le⟩, rfl⟩, by rw [dist_comm]; linarith⟩

end Visit

section Meas

variable {Ω : Type*} [MeasurableSpace Ω] {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
  (hb : IsPiecewiseConstantBoundaryData b J) {Ê : ℕ → Ω → Drv} (hÊm : ∀ j, Measurable (Ê j))
  (hÊreg : ∀ j ω, IsRegularDriver (Ê j ω))
  (hÊP : ∀ ω, RegLaunches κ b J (boundaryWalkSpec b J θ true) fun j => Ê j ω)

include hb hÊm hÊreg hÊP in
/-- **The point of a launched piece at a measurable random time below its lifetime is measurable.** -/
theorem measurable_pcPt_at (n : ℕ) {σ : Ω → ℝ≥0} (hσ : Measurable σ)
    (hσL : ∀ ω, (wRun κ θ b J (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none → (σ ω : ℝ≥0∞) ≤ (Ê n ω).2) :
    Measurable fun ω => if ω ∈ {ω | (wRun κ θ b J (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none} then
      pcPt (wRun κ θ b J (fun j => Ê j ω) n) (Ê n ω) (σ ω) else 0 := by
  classical
  have hpf := fun i => measurable_pfam (κ := κ) (θ := θ) (right := true) hb hÊm hÊreg hÊP (n + 1) i
  set qi : ℕ → ℚ := fun i => Denumerable.ofNat ℚ i with hqi
  refine measurable_at_of_dense_good (ρ := fun ω => pcPt (wRun κ θ b J (fun j => Ê j ω) n) (Ê n ω))
    (good := fun i ω => qi i ≤ 0 ∨ (0 < qi i ∧ ((ratPt i : ℝ≥0) : ℝ≥0∞) < (Ê n ω).2))
    (V := fun i ω => if 0 < qi i then pfam κ b J θ true (fun j => Ê j ω) (n + 1) (Sum.inl (Sum.inr (n, qi i)))
      else pfam κ b J θ true (fun j => Ê j ω) (n + 1) (Sum.inl (Sum.inl n)))
    (fun i => (MeasurableSet.const _).union ((MeasurableSet.const _).inter
      (measurableSet_lt measurable_const (measurable_snd.comp (hÊm n)))))
    (fun i => Measurable.ite (MeasurableSet.const _) (hpf _) (hpf _))
    (measurableSet_launch hb hÊm hÊreg n) hσ ?_ ?_ ?_
  · -- the values at good indices
    intro ω hl i hi
    rcases hi with hq | ⟨hq, hqL⟩
    · have h0 : ratPt i = 0 := by rw [ratPt_eq_ofNat]; exact Real.toNNReal_of_nonpos (by exact_mod_cast hq)
      simp only [h0, not_lt.2 hq, ↓reduceIte]
      exact pcPt_zero_eq_pfam (hÊP ω) hl
    · simp only [hq, ↓reduceIte]
      exact pcPt_rat_eq_pfam (hÊP ω) (fun j => hÊreg j ω) hl hq hqL
  · -- good times near `σ`
    intro ω hl ε hε
    by_cases hL0 : (Ê n ω).2 = 0
    · have hσ0 : σ ω = 0 := by
        have := hσL ω hl; rw [hL0] at this; exact_mod_cast le_antisymm this zero_le
      obtain ⟨i, hi⟩ := exists_ofNat_eq 0
      refine ⟨i, Or.inl (by rw [hqi]; simp only [hi, le_refl]), ?_⟩
      rw [hσ0, ratPt_eq_ofNat, hi]
      simpa using hε
    · obtain ⟨q, hq0, hqL, hqσ⟩ := exists_rat_near_lt (hσL ω hl) (pos_iff_ne_zero.2 hL0) hε
      obtain ⟨i, hi⟩ := exists_ofNat_eq q
      refine ⟨i, Or.inr ⟨by rw [hqi]; simp only [hi]; exact hq0, by rw [ratPt_eq_ofNat, hi]; exact hqL⟩, ?_⟩
      rw [ratPt_eq_ofNat, hi, NNReal.dist_eq, Real.coe_toNNReal _ (by exact_mod_cast hq0.le)]
      exact hqσ
  · -- continuity along good times
    intro ω hl v hv hconv
    refine tendsto_of_continuousWithinAt ((continuousOn_pcPt_launch (hÊP ω) hl) _ (hσL ω hl))
      (good := fun i => qi i ≤ 0 ∨ (0 < qi i ∧ ((ratPt i : ℝ≥0) : ℝ≥0∞) < (Ê n ω).2)) (fun i hi => ?_) v hv hconv
    rcases hi with hq | ⟨-, hqL⟩
    · have h0 : ratPt i = 0 := by rw [ratPt_eq_ofNat]; exact Real.toNNReal_of_nonpos (by exact_mod_cast hq)
      show ((ratPt i : ℝ≥0) : ℝ≥0∞) ≤ _
      rw [h0]; exact zero_le
    · exact hqL.le

include hb hÊm hÊreg hÊP in
/-- **The first visit of a fixed point by a launched piece is measurable.** -/
theorem measurable_visitTime (n : ℕ) (R : ℂ) :
    Measurable fun ω => if ω ∈ {ω | (wRun κ θ b J (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none} then
      visitTime' (wRun κ θ b J (fun j => Ê j ω) n) (Ê n ω) R else 0 := by
  classical
  have hpf := fun i => measurable_pfam (κ := κ) (θ := θ) (right := true) hb hÊm hÊreg hÊP (n + 1) i
  set Ln : Set Ω := {ω | (wRun κ θ b J (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none} with hLn
  have hLnm : MeasurableSet Ln := measurableSet_launch hb hÊm hÊreg n
  refine measurable_of_Iic fun a => ?_
  have e : (fun ω => if ω ∈ Ln then visitTime' (wRun κ θ b J (fun j => Ê j ω) n) (Ê n ω) R else 0) ⁻¹' Iic a =
      Lnᶜ ∪ (Ln ∩ ({ω | R ∈ newPiece κ b J θ true (fun j => Ê j ω) n}ᶜ ∪ ⋂ k : ℕ,
        ({ω | dist (pfam κ b J θ true (fun j => Ê j ω) (n + 1) (Sum.inl (Sum.inl n))) R < 1 / ((k : ℝ) + 1)} ∪
          ⋃ q : ℚ, {ω | 0 < q ∧ (q : ℝ).toNNReal ≤ a ∧ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (Ê n ω).2 ∧
            dist (pfam κ b J θ true (fun j => Ê j ω) (n + 1) (Sum.inl (Sum.inr (n, q)))) R <
              1 / ((k : ℝ) + 1)}))) := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_union, mem_compl_iff, mem_inter_iff, mem_iInter, mem_iUnion,
      mem_ofPred_eq]
    by_cases hl : ω ∈ Ln
    · simp only [hl, ↓reduceIte, not_true_eq_false, false_or, true_and]
      have hl' : (wRun κ θ b J (fun j => Ê j ω) (n + 1)).2.2.2.1 n ≠ none := hl
      rw [visitTime'_le_iff (hÊP ω) hl', mem_pcPt_image_le_iff (hÊP ω) hl']
      have hnp : R ∈ newPiece κ b J θ true (fun j => Ê j ω) n ↔
          R ∈ pcPt (wRun κ θ b J (fun j => Ê j ω) n) (Ê n ω) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (Ê n ω).2} :=
        ⟨fun h => h.2, fun h => ⟨hl', h⟩⟩
      rw [hnp]
      refine or_congr ⟨fun h ⟨t, ht, hpt⟩ => h t ht hpt, fun h t ht hpt => h ⟨t, ht, hpt⟩⟩
        (forall_congr' fun k => or_congr ?_ (exists_congr fun q => ?_))
      · rw [pcPt_zero_eq_pfam (hÊP ω) hl']
      · constructor
        · rintro ⟨hq0, hqa, hqL, hd⟩
          exact ⟨hq0, hqa, hqL, by rwa [pcPt_rat_eq_pfam (hÊP ω) (fun j => hÊreg j ω) hl' hq0 hqL] at hd⟩
        · rintro ⟨hq0, hqa, hqL, hd⟩
          exact ⟨hq0, hqa, hqL, by rwa [pcPt_rat_eq_pfam (hÊP ω) (fun j => hÊreg j ω) hl' hq0 hqL]⟩
    · simp only [hl, ↓reduceIte, zero_le, not_false_eq_true, true_or]
  rw [e]
  refine hLnm.compl.union (hLnm.inter ((measurableSet_mem_newPiece hb hÊm hÊreg hÊP R n).compl.union
    (MeasurableSet.iInter fun k => (measurableSet_lt ((hpf _).dist measurable_const) measurable_const).union
      (MeasurableSet.iUnion fun q => ?_))))
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_lt measurable_const (measurable_snd.comp (hÊm n))).inter
      (measurableSet_lt ((hpf _).dist measurable_const) measurable_const)))

end Meas

end InteractingSLE.Theorem14.SB.Nv
