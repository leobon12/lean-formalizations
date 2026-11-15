/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G7ClockCap

/-!
# Measurability of the retained clocks

Packet PROVE-G7B. The relative capacity clocks of retained continuations (`G7ClockCap.lean`) are measurable in the
randomness:

* `measurableSet_mem_contSet`, **`measurable_contStop`**: the end of a continuation (its first new contact with a
  random union of two path prefixes, or its lifetime) is measurable;
* **`measurable_contPath`**: the chart path at a fixed time is measurable. Before the end it is a forward chart limit
  at a measurable point (`measurable_of_tendsto_nhdsWithin`); at the end it is the limit of the chart path at the
  times `min(r, θₙ V)`, `θₙ ↑ 1`, all before the end;
* **`clockData_of_measurable`**: for measurable chart paths, continuous in time, starting at `0`, whose capacity clocks
  are clocks and continuous, the chart paths read in their inverse capacity clocks and the capacity lifetimes are
  measurable, and the reparametrized paths are continuous on their lifetimes.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp7

open Restart

/-! ### The end of a continuation -/

section Stop

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {K : Set ℂ}

/-- `y < contStop` is witnessed by `a` or by a rational time of the continuation interval. -/
theorem lt_contStop_iff (ha : (a : ℝ≥0∞) ≤ ζ) (y : ℝ≥0∞) :
    y < contStop η ζ a K ↔ y < a ∨ ∃ q : ℚ, 0 ≤ q ∧ y < (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ∧
      (q : ℝ).toNNReal ∈ contSet η ζ a K := by
  constructor
  · intro hy
    by_cases hya : y < a
    · exact Or.inl hya
    · push Not at hya
      obtain ⟨q, hq0, hyq, hqs⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hy
      exact Or.inr ⟨q, hq0, hyq, mem_contSet_of_le (ENNReal.coe_le_coe.1 (hya.trans hyq.le)) hqs.le⟩
  · rintro (h | ⟨q, -, hyq, hq⟩)
    · exact h.trans_le (le_contStop (self_mem_contSet ha))
    · exact hyq.trans_le (le_contStop hq)

end Stop

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The continuation interval is measurable at a fixed time**, for a continuation of a random path and the
union of two random path prefixes. -/
theorem measurableSet_mem_contSet {G : Set Ω} (hG : MeasurableSet G) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t) {ζ : Ω → ℝ≥0∞} (hζ : Measurable ζ) (a : ℝ≥0) {f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hf₁ : ∀ t, Measurable fun ω => f₁ ω t) (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (c₁ c₂ : ℝ≥0)
    (hcη : ∀ ω ∈ G, ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω})
    (hc₁ : ∀ ω ∈ G, ContinuousOn (f₁ ω) (Iic c₁)) (hc₂ : ∀ ω ∈ G, ContinuousOn (f₂ ω) (Iic c₂)) (t : ℝ≥0) :
    MeasurableSet (G ∩ {ω | t ∈ contSet (η ω) (ζ ω) a (f₁ ω '' Icc 0 c₁ ∪ f₂ ω '' Icc 0 c₂)}) := by
  set G' : Set Ω := G ∩ {ω | (t : ℝ≥0∞) ≤ ζ ω} with hG'
  have hG'm : MeasurableSet G' := hG.inter (measurableSet_le measurable_const hζ)
  rcases lt_trichotomy a t with hat | rfl | hta
  · -- the open interval `(a, t)` is the union of the closed intervals `[a + δₙ, t − δₙ]`
    set δ : ℕ → ℝ≥0 := fun n => (t - a) / ((n : ℝ≥0) + 3) with hδ
    have hta0 : 0 < t - a := tsub_pos_of_lt hat
    have hδpos : ∀ n, 0 < δ n := fun n => div_pos hta0 (by positivity)
    have hδlt : ∀ n, 2 * δ n < t - a := fun n => by
      rw [hδ]; dsimp only
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      have : (0 : ℝ≥0) ≤ n := zero_le
      calc 2 * (t - a) < (t - a) * 3 := by
            rw [mul_comm]; exact mul_lt_mul_of_pos_left (by norm_num) hta0
        _ ≤ (t - a) * ((n : ℝ≥0) + 3) := mul_le_mul_right (le_add_of_nonneg_left this) _
    have hab : ∀ n, a + δ n ≤ t - δ n := fun n => by
      have h1 := hδlt n
      have h2 : a + δ n + δ n < t := by
        rw [add_assoc, ← two_mul]
        calc a + 2 * δ n < a + (t - a) := (add_lt_add_iff_left a).2 h1
          _ = t := add_tsub_cancel_of_le hat.le
      exact le_tsub_of_add_le_right h2.le
    set X : ℕ → (Ω → ℝ≥0 → ℂ) → ℝ≥0 → Set Ω := fun n f c =>
      G' ∩ {ω | ∃ s ≤ (t - δ n) - (a + δ n), ∃ s' ≤ c, η ω (a + δ n + s) = f ω s'} with hX
    have hXm : ∀ n (f : Ω → ℝ≥0 → ℂ), (∀ t, Measurable fun ω => f ω t) → ∀ c : ℝ≥0,
        (∀ ω ∈ G, ContinuousOn (f ω) (Iic c)) → MeasurableSet (X n f c) := by
      intro n f hf c hc
      refine measurableSet_inter_exists_eq hG'm (fun s => hη (a + δ n + s)) hf (c₁ := fun _ => _)
        (c₂ := fun _ => c) measurable_const measurable_const (fun ω hω => ?_) (fun ω hω => hc ω hω.1)
      refine (hcη ω hω.1).comp (continuous_const.add continuous_id).continuousOn fun s hs => ?_
      have h1 : a + δ n + s ≤ t := by
        have := add_le_add (le_refl (a + δ n)) (show s ≤ (t - δ n) - (a + δ n) from hs)
        rw [add_tsub_cancel_of_le (hab n)] at this
        exact this.trans tsub_le_self
      exact (ENNReal.coe_le_coe.2 h1).trans hω.2
    have heq : G ∩ {ω | t ∈ contSet (η ω) (ζ ω) a (f₁ ω '' Icc 0 c₁ ∪ f₂ ω '' Icc 0 c₂)} =
        G' ∩ ⋂ n : ℕ, ((X n f₁ c₁)ᶜ ∩ (X n f₂ c₂)ᶜ) := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_compl_iff, hX, hG']
      constructor
      · rintro ⟨hωG, -, htζ, hno⟩
        refine ⟨⟨hωG, htζ⟩, fun n => ⟨?_, ?_⟩⟩ <;>
        · rintro ⟨-, s, hs, s', hs', he⟩
          have h1 : a < a + δ n + s := lt_of_lt_of_le (lt_add_of_pos_right a (hδpos n)) le_self_add
          have h2 : a + δ n + s < t := by
            have := add_le_add (le_refl (a + δ n)) (show s ≤ (t - δ n) - (a + δ n) from hs)
            rw [add_tsub_cancel_of_le (hab n)] at this
            exact lt_of_le_of_lt this (tsub_lt_self (lt_of_le_of_lt zero_le hat) (hδpos n))
          refine hno _ h1 h2 ?_
          rw [he]
          first
          | exact Or.inl ⟨s', ⟨zero_le, hs'⟩, rfl⟩
          | exact Or.inr ⟨s', ⟨zero_le, hs'⟩, rfl⟩
      · rintro ⟨⟨hωG, htζ⟩, hall⟩
        refine ⟨hωG, hat.le, htζ, fun t' h1 h2 hK => ?_⟩
        -- choose `n` with `δₙ` below both gaps
        have hgap : 0 < min (t' - a) (t - t') := lt_min (tsub_pos_of_lt h1) (tsub_pos_of_lt h2)
        obtain ⟨n, hn⟩ : ∃ n : ℕ, δ n < min (t' - a) (t - t') := by
          obtain ⟨n, hn⟩ := exists_nat_gt ((t - a) / min (t' - a) (t - t'))
          refine ⟨n, ?_⟩
          rw [hδ]; dsimp only
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hgap] at hn
          calc t - a < (n : ℝ≥0) * min (t' - a) (t - t') := hn
            _ ≤ min (t' - a) (t - t') * ((n : ℝ≥0) + 3) := by
              rw [mul_comm]; exact mul_le_mul_right (le_add_of_nonneg_right zero_le) _
        have hn1 : δ n < t' - a := hn.trans_le (min_le_left _ _)
        have hn2 : δ n < t - t' := hn.trans_le (min_le_right _ _)
        have hlo : a + δ n ≤ t' := by
          have := (add_lt_add_iff_left a).2 hn1
          rw [add_tsub_cancel_of_le h1.le] at this
          exact this.le
        have hhi : t' ≤ t - δ n := le_tsub_of_add_le_right (by
          have := (add_lt_add_iff_left t').2 hn2
          rw [add_tsub_cancel_of_le h2.le] at this
          exact this.le)
        set s := t' - (a + δ n) with hs
        have hs' : a + δ n + s = t' := add_tsub_cancel_of_le hlo
        have hsle : s ≤ (t - δ n) - (a + δ n) := tsub_le_tsub_right hhi _
        rcases hK with ⟨s', hs'm, he⟩ | ⟨s', hs'm, he⟩
        · exact (hall n).1 ⟨⟨hωG, htζ⟩, s, hsle, s', hs'm.2, by rw [hs', he]⟩
        · exact (hall n).2 ⟨⟨hωG, htζ⟩, s, hsle, s', hs'm.2, by rw [hs', he]⟩
    rw [heq]
    exact hG'm.inter (MeasurableSet.iInter fun n =>
      (hXm n f₁ hf₁ c₁ hc₁).compl.inter (hXm n f₂ hf₂ c₂ hc₂).compl)
  · have heq : G ∩ {ω | a ∈ contSet (η ω) (ζ ω) a (f₁ ω '' Icc 0 c₁ ∪ f₂ ω '' Icc 0 c₂)} = G' := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, hG']
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.2.1⟩, fun ⟨h1, h2⟩ => ⟨h1, self_mem_contSet h2⟩⟩
    rw [heq]
    exact hG'm
  · have heq : G ∩ {ω | t ∈ contSet (η ω) (ζ ω) a (f₁ ω '' Icc 0 c₁ ∪ f₂ ω '' Icc 0 c₂)} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ h => absurd h.1 (not_le.2 hta)
    rw [heq]
    exact MeasurableSet.empty

open scoped Classical in
/-- **The end of the continuation is measurable** (on a measurable event where the start is available). -/
theorem measurable_contStop {G : Set Ω} (hG : MeasurableSet G) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t) {ζ : Ω → ℝ≥0∞} (hζ : Measurable ζ) (a : ℝ≥0) {f₁ f₂ : Ω → ℝ≥0 → ℂ}
    (hf₁ : ∀ t, Measurable fun ω => f₁ ω t) (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) (c₁ c₂ : ℝ≥0)
    (hcη : ∀ ω ∈ G, ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω})
    (hc₁ : ∀ ω ∈ G, ContinuousOn (f₁ ω) (Iic c₁)) (hc₂ : ∀ ω ∈ G, ContinuousOn (f₂ ω) (Iic c₂))
    (haζ : ∀ ω ∈ G, (a : ℝ≥0∞) ≤ ζ ω) :
    Measurable fun ω => if ω ∈ G then contStop (η ω) (ζ ω) a (f₁ ω '' Icc 0 c₁ ∪ f₂ ω '' Icc 0 c₂) else 0 := by
  classical
  refine measurable_of_Ioi fun y => ?_
  have hset := fun t => measurableSet_mem_contSet hG hη hζ a hf₁ hf₂ c₁ c₂ hcη hc₁ hc₂ t
  have heq : (fun ω => if ω ∈ G then contStop (η ω) (ζ ω) a (f₁ ω '' Icc 0 c₁ ∪ f₂ ω '' Icc 0 c₂) else 0) ⁻¹'
      Ioi y = (G ∩ {_ω | y < a}) ∪ (⋃ q : ℚ, (({_ω | 0 ≤ q ∧ y < (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞)}) ∩
        (G ∩ {ω | (q : ℝ).toNNReal ∈ contSet (η ω) (ζ ω) a (f₁ ω '' Icc 0 c₁ ∪ f₂ ω '' Icc 0 c₂)}))) ∪
      (Gᶜ ∩ {_ω | y < 0}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_preimage, hω, ↓reduceIte, mem_Ioi, mem_union, mem_inter_iff, mem_ofPred_eq, true_and,
        mem_iUnion, mem_compl_iff, not_true_eq_false, false_and, or_false]
      rw [lt_contStop_iff (haζ ω hω)]
      constructor
      · rintro (h | ⟨q, h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨q, ⟨h1, h2⟩, h3⟩
      · rintro (h | ⟨q, ⟨h1, h2⟩, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨q, h1, h2, h3⟩
    · simp [hω]
  rw [heq]
  refine ((hG.inter (MeasurableSet.const _)).union (MeasurableSet.iUnion fun q : ℚ =>
    (MeasurableSet.const _).inter (hset _))).union (hG.compl.inter (MeasurableSet.const _))

/-! ### The measurable chart path -/

/-- Times before the end of a continuation, converging to `min r V`. -/
def approxTime (V : ℝ≥0∞) (r : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  if V = ⊤ then r else min r (Real.toNNReal (V.toReal - V.toReal / ((n : ℝ) + 2)))

theorem approxTime_lt {V : ℝ≥0∞} (hV : 0 < V) (r : ℝ≥0) (n : ℕ) : (approxTime V r n : ℝ≥0∞) < V := by
  unfold approxTime
  split_ifs with h
  · rw [h]; exact ENNReal.coe_lt_top
  · have hpos : 0 < V.toReal := ENNReal.toReal_pos hV.ne' h
    have hlt : Real.toNNReal (V.toReal - V.toReal / ((n : ℝ) + 2)) < V.toNNReal := by
      have h1 : V.toReal - V.toReal / ((n : ℝ) + 2) < V.toReal := by
        have : 0 < V.toReal / ((n : ℝ) + 2) := div_pos hpos (by positivity)
        linarith
      have h2 := (Real.toNNReal_lt_toNNReal_iff hpos).2 h1
      rwa [ENNReal.toReal, Real.toNNReal_coe] at h2
    calc ((min r (Real.toNNReal (V.toReal - V.toReal / ((n : ℝ) + 2))) : ℝ≥0) : ℝ≥0∞)
        ≤ ((Real.toNNReal (V.toReal - V.toReal / ((n : ℝ) + 2)) : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.2 (min_le_right _ _)
      _ < V := by
          rw [← ENNReal.coe_toNNReal h]; exact ENNReal.coe_lt_coe.2 hlt

theorem tendsto_approxTime {V : ℝ≥0∞} (hV : V ≠ ⊤) (r : ℝ≥0) :
    Tendsto (approxTime V r) atTop (𝓝 (min r V.toNNReal)) := by
  have h1 : Tendsto (fun n : ℕ => V.toReal - V.toReal / ((n : ℝ) + 2)) atTop (𝓝 V.toReal) := by
    have h2 : Tendsto (fun n : ℕ => V.toReal / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using (tendsto_const_nhds (x := V.toReal)).sub h2
  have h3 := (continuous_real_toNNReal.tendsto _).comp h1
  rw [ENNReal.toReal, Real.toNNReal_coe] at h3
  have h4 := (tendsto_const_nhds (x := r)).min h3
  refine h4.congr fun n => ?_
  simp only [approxTime, hV, ↓reduceIte, Function.comp_apply]
  rfl

theorem measurable_approxTime {Ω : Type*} [MeasurableSpace Ω] {V : Ω → ℝ≥0∞} (hV : Measurable V) (r : ℝ≥0)
    (n : ℕ) : Measurable fun ω => approxTime (V ω) r n := by
  unfold approxTime
  refine Measurable.ite (measurableSet_eq_fun hV measurable_const) measurable_const
    (measurable_const.min (Measurable.real_toNNReal ?_))
  exact (ENNReal.measurable_toReal.comp hV).sub ((ENNReal.measurable_toReal.comp hV).div_const _)

open scoped Classical in
/-- **The chart path at a fixed time is measurable.** -/
theorem measurable_contPath {E : Set Ω} (hE : MeasurableSet E) {D : Ω → Set ℂ} (hDo : ∀ ω, IsOpen (D ω))
    (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω}) {φ : Ω → ℂ → ℂ}
    (hφm : ∀ z, Measurable ({ω | z ∈ D ω}.indicator fun ω => φ ω z)) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ t, Measurable fun ω => η ω t) (a : ℝ≥0) {V : Ω → ℝ≥0∞} (hV : Measurable V)
    (hpos : ∀ ω ∈ E, 0 < V ω)
    (hcont : ∀ ω ∈ E, ∀ r : ℝ≥0, (r : ℝ≥0∞) < V ω → ContinuousOn (η ω) (Iic (a + r)))
    (hcl : ∀ ω ∈ E, ∀ r : ℝ≥0, (r : ℝ≥0∞) < V ω → η ω (a + r) ∈ closure (D ω))
    (hlim : ∀ ω ∈ E, ∀ r : ℝ≥0, (r : ℝ≥0∞) < V ω → ∃ w, Tendsto (φ ω) (𝓝[D ω] (η ω (a + r))) (𝓝 w))
    (hΓc : ∀ ω ∈ E, Continuous (contPath (D ω) (φ ω) (η ω) a (V ω))) (r : ℝ≥0) :
    Measurable fun ω => if ω ∈ E then contPath (D ω) (φ ω) (η ω) a (V ω) r else 0 := by
  set D' : Ω → Set ℂ := fun ω => if ω ∈ E then D ω else H with hD'
  set f' : Ω → ℂ → ℂ := fun ω => if ω ∈ E then φ ω else id with hf'
  have hDo' : ∀ ω, IsOpen (D' ω) := fun ω => by
    simp only [hD']; split_ifs
    · exact hDo ω
    · exact QuantumZipper.isOpen_H
  have hDm' : ∀ z, MeasurableSet {ω | z ∈ D' ω} := fun z => by
    have : {ω | z ∈ D' ω} = (E ∩ {ω | z ∈ D ω}) ∪ (Eᶜ ∩ {_ω | z ∈ H}) := by
      ext ω; by_cases hω : ω ∈ E <;> simp [hD', hω]
    rw [this]
    exact (hE.inter (hDm z)).union (hE.compl.inter (MeasurableSet.const _))
  have hfm' : ∀ z, Measurable ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) := fun z => by
    have : ({ω | z ∈ D' ω}.indicator fun ω => f' ω z) =
        E.piecewise ({ω | z ∈ D ω}.indicator fun ω => φ ω z) (fun _ => if z ∈ H then z else 0) := by
      funext ω
      by_cases hω : ω ∈ E <;> by_cases hz : z ∈ H <;> simp [Set.indicator, Set.piecewise, hD', hf', hω, hz]
    rw [this]
    exact (hφm z).piecewise hE measurable_const
  have hg : ∀ n : ℕ, Measurable fun ω => if ω ∈ E then contPath (D ω) (φ ω) (η ω) a (V ω)
      (approxTime (V ω) r n) else 0 := by
    intro n
    set q' : Ω → ℂ := fun ω => if ω ∈ E then η ω (a + approxTime (V ω) r n) else 0 with hq'
    have hqm : Measurable q' := measurable_piecewise_eval hE hη
      (measurable_const.add (measurable_approxTime hV r n))
      fun ω hω => hcont ω hω _ (approxTime_lt (hpos ω hω) r n)
    have hqD : ∀ ω, q' ω ∈ closure (D' ω) := fun ω => by
      by_cases hω : ω ∈ E
      · simp only [hq', hD', hω, ↓reduceIte]
        exact hcl ω hω _ (approxTime_lt (hpos ω hω) r n)
      · simp only [hq', hD', hω, ↓reduceIte]
        rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
        show (0 : ℝ) ≤ (0 : ℂ).im
        simp
    refine measurable_of_tendsto_nhdsWithin hDo' hDm' hfm' hqm hqD fun ω => ?_
    by_cases hω : ω ∈ E
    · simp only [hf', hD', hq', hω, ↓reduceIte]
      have hlt := approxTime_lt (hpos ω hω) r n
      rw [contPath_of_lt hlt]
      exact tendsto_nhds_limUnder (hlim ω hω _ hlt)
    · simp only [hf', hD', hq', hω, ↓reduceIte]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
  refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ E
  · simp only [hω, ↓reduceIte]
    by_cases hVt : V ω = ⊤
    · simp only [approxTime, hVt, ↓reduceIte]
      exact tendsto_const_nhds
    · have hval : contPath (D ω) (φ ω) (η ω) a (V ω) (min r (V ω).toNNReal) =
          contPath (D ω) (φ ω) (η ω) a (V ω) r := by
        rcases le_total r (V ω).toNNReal with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h, contPath_of_le (by rw [ENNReal.coe_toNNReal hVt]),
            contPath_of_le (by rw [← ENNReal.coe_toNNReal hVt]; exact ENNReal.coe_le_coe.2 h)]
      rw [← hval]
      exact ((hΓc ω hω).tendsto _).comp (tendsto_approxTime hVt r)
  · simp only [hω, ↓reduceIte]
    exact tendsto_const_nhds

/-! ### Measurable clock data -/

/-- The capacity clock of a continuous path from `0` is the halved hitting capacity of its prefix. -/
theorem chartClock_eq_hcapHit {Γ : ℝ≥0 → ℂ} (hc : Continuous Γ) (h0 : Γ 0 = 0) (t : ℝ≥0) :
    chartClock Γ t = (WholeField.hcapHit (Γ '' Icc 0 t)).toReal / 2 := by
  have hc' := hc.continuousOn (s := Icc 0 t)
  have h0' : (Γ 0).im ≤ 0 := by rw [h0]; simp
  rw [hcapHit_image_eq hc' h0', ENNReal.toReal_ofReal]
  · rfl
  · rw [ConformalImage.hcapSet_eq (isHPHull_fillH_image hc' h0')]
    exact HPHull.hcap_nonneg _

open scoped Classical in
/-- **Measurable capacity-time clock data**: for measurable chart paths, continuous in time and starting at `0`,
whose capacity clocks are continuous clocks on `[0, V]`, the paths read in their inverse capacity clocks and the
capacity lifetimes are measurable, and each reparametrized path is continuous on its lifetime. -/
theorem clockData_of_measurable {E : Set Ω} (hE : MeasurableSet E) {Γ : Ω → ℝ≥0 → ℂ}
    (hc : ∀ ω, Continuous (Γ ω)) (hm : ∀ t, Measurable fun ω => Γ ω t) (h0 : ∀ ω ∈ E, Γ ω 0 = 0)
    {V : Ω → ℝ≥0∞} (hV : Measurable V) (hclk : ∀ ω ∈ E, IsClockOn (chartClock (Γ ω)) (V ω))
    (hclc : ∀ ω ∈ E, Continuous (chartClock (Γ ω))) :
    (∀ u, Measurable fun ω => if ω ∈ E then Γ ω (invClock (chartClock (Γ ω)) (V ω) u) else 0) ∧
      Measurable (fun ω => if ω ∈ E then capLife (chartClock (Γ ω)) (V ω) else 0) ∧
      ∀ ω ∈ E, ContinuousOn (fun u => Γ ω (invClock (chartClock (Γ ω)) (V ω) u))
        {u | (u : ℝ≥0∞) ≤ capLife (chartClock (Γ ω)) (V ω)} := by
  set cl : Ω → ℝ≥0 → ℝ := fun ω t => if ω ∈ E then chartClock (Γ ω) t else 0 with hcl
  have hclE : ∀ ω ∈ E, cl ω = chartClock (Γ ω) := fun ω hω => funext fun t => by simp [hcl, hω]
  have hclm : ∀ t, Measurable fun ω => cl ω t := fun t => by
    have : (fun ω => cl ω t) = fun ω => if ω ∈ E then (WholeField.hcapHit (Γ ω '' Icc 0 t)).toReal / 2 else 0 := by
      funext ω
      by_cases hω : ω ∈ E
      · simp only [hcl, hω, ↓reduceIte, chartClock_eq_hcapHit (hc ω) (h0 ω hω)]
      · simp [hcl, hω]
    rw [this]
    exact Measurable.ite hE ((measurable_hcapHit_image hc hm t).ennreal_toReal.div_const 2) measurable_const
  have hclcont : ∀ ω, Continuous (cl ω) := fun ω => by
    by_cases hω : ω ∈ E
    · rw [hclE ω hω]; exact hclc ω hω
    · have : cl ω = fun _ => 0 := funext fun t => by simp [hcl, hω]
      rw [this]; exact continuous_const
  have hinv : ∀ u, Measurable fun ω => invClock (cl ω) (V ω) u := by
    intro u
    refine Measurable.iSup fun q => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (MeasurableSet.const _).inter ((measurableSet_le measurable_const hV).inter
      (measurableSet_lt (hclm _) measurable_const))
  have hΓj : Measurable fun p : ℝ≥0 × Ω => Γ p.2 p.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun r ω => Γ ω r) (fun ω => hc ω) hm
  have hclj : Measurable fun p : ℝ≥0 × Ω => cl p.2 p.1 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun r ω => cl ω r) (fun ω => hclcont ω) hclm
  refine ⟨fun u => ?_, ?_, fun ω hω => ?_⟩
  · have h := hΓj.comp ((hinv u).prodMk measurable_id)
    have heq : (fun ω => if ω ∈ E then Γ ω (invClock (chartClock (Γ ω)) (V ω) u) else 0) =
        fun ω => if ω ∈ E then Γ ω (invClock (cl ω) (V ω) u) else 0 := by
      funext ω
      by_cases hω : ω ∈ E
      · simp only [hω, ↓reduceIte, hclE ω hω]
      · simp [hω]
    rw [heq]
    exact Measurable.ite hE h measurable_const
  · have hv : Measurable fun ω => cl ω (V ω).toNNReal :=
      hclj.comp ((ENNReal.measurable_toNNReal.comp hV).prodMk measurable_id)
    have hcap : Measurable fun ω => capLife (cl ω) (V ω) :=
      Measurable.ite (measurableSet_eq_fun hV measurable_const) measurable_const
        (ENNReal.measurable_ofReal.comp hv)
    have heq : (fun ω => if ω ∈ E then capLife (chartClock (Γ ω)) (V ω) else 0) =
        fun ω => if ω ∈ E then capLife (cl ω) (V ω) else 0 := by
      funext ω
      by_cases hω : ω ∈ E
      · simp only [hω, ↓reduceIte, hclE ω hω]
      · simp [hω]
    rw [heq]
    exact Measurable.ite hE hcap measurable_const
  · exact (hc ω).continuousOn.comp (hclk ω hω).continuousOn_invClock (mapsTo_univ _ _)

end Supp7

end InteractingSLE
