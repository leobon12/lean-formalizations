/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvRule

/-!
# SB2(2)'s v6 measurability: generic tools

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). Generic measurability tools for the v6 rule:

* `measurable_natIdx`, `measurableSet_natIdx`: evaluation at a measurable random index;
* `exists_ratPt_eq`, `exists_ratPt_mem_Ioo`, `exists_ratPt_near`: the enumeration `Lk.ratPt` of the nonnegative
  rationals is onto them, hence dense;
* **`measurable_at_of_dense_good`**: `Lk.measurable_of_dense_good` at a measurable random time `σ`, with the continuity
  replaced by sequential continuity along the good times;
* `tendsto_of_continuousWithinAt`: the sequential continuity from continuity within a set containing the good times;
* `measurable_stTime`: the stage time at a fixed curve time is measurable in a measurable lifetime.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Sec7.PocketTraversal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Random indices -/

/-- **Evaluation at a measurable random index.** -/
theorem measurable_natIdx {β : Type*} [MeasurableSpace β] {x : Ω → ℕ} (hx : ∀ r, MeasurableSet {ω | x ω = r})
    {g : ℕ → Ω → β} (hg : ∀ r, Measurable (g r)) : Measurable fun ω => g (x ω) ω := by
  intro s hs
  have e : (fun ω => g (x ω) ω) ⁻¹' s = ⋃ r, {ω | x ω = r} ∩ g r ⁻¹' s := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨x ω, rfl, h⟩, fun ⟨r, hr, h⟩ => hr ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun r => (hx r).inter (hg r hs)

/-- **An event at a measurable random index.** -/
theorem measurableSet_natIdx {x : Ω → ℕ} (hx : ∀ r, MeasurableSet {ω | x ω = r}) {A : ℕ → Set Ω}
    (hA : ∀ r, MeasurableSet (A r)) : MeasurableSet {ω | ω ∈ A (x ω)} := by
  have e : {ω | ω ∈ A (x ω)} = ⋃ r, {ω | x ω = r} ∩ A r := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact ⟨fun h => ⟨x ω, rfl, h⟩, fun ⟨r, hr, h⟩ => hr ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun r => (hx r).inter (hA r)

/-! ### The rational enumeration is dense -/

/-- Every nonnegative rational is a value of `ratPt`. -/
theorem exists_ratPt_eq (q : ℚ) : ∃ i, ratPt i = ((q : ℝ)).toNNReal :=
  ⟨@Encodable.encode ℚ Denumerable.toEncodable q, by unfold ratPt; rw [Denumerable.ofNat_encode]⟩

/-- `0` is a value of `ratPt`. -/
theorem exists_ratPt_zero : ∃ i, ratPt i = 0 := by
  obtain ⟨i, hi⟩ := exists_ratPt_eq 0
  exact ⟨i, by simpa using hi⟩

/-- **`ratPt` meets every open interval.** -/
theorem exists_ratPt_mem_Ioo {a b : ℝ≥0} (hab : a < b) : ∃ i, a < ratPt i ∧ ratPt i < b := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
  obtain ⟨i, hi⟩ := exists_ratPt_eq q
  have hq0 : (0 : ℝ) ≤ q := le_trans a.2 hq1.le
  refine ⟨i, ?_, ?_⟩
  · rw [hi, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq1
  · rw [hi, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]; exact hq2

/-- **`ratPt` is dense.** -/
theorem exists_ratPt_near (t : ℝ≥0) {ε : ℝ} (hε : 0 < ε) : ∃ i, dist (ratPt i) t < ε := by
  obtain ⟨i, h1, h2⟩ := exists_ratPt_mem_Ioo (show t < t + ε.toNNReal by
    simpa using Real.toNNReal_pos.2 hε)
  refine ⟨i, ?_⟩
  rw [NNReal.dist_eq, abs_lt]
  have h2' : (ratPt i : ℝ) < t + ε := by
    have := (NNReal.coe_lt_coe.2 h2)
    rwa [NNReal.coe_add, Real.coe_toNNReal _ hε.le] at this
  have h1' : (t : ℝ) < ratPt i := NNReal.coe_lt_coe.2 h1
  constructor <;> linarith

/-! ### Measurability at a random time from dense good readings -/

/-- **Measurability at a random time from dense good rational readings**: on a measurable event `M`, let the values
of `ρ ω` at the good indices `i` (an event measurable in `ω` for each `i`) be given by measurable `V i`; if on `M`
good times come arbitrarily close to the measurable random time `σ ω`, and `ρ ω` is sequentially continuous at `σ ω`
along good times, then `ω ↦ ρ ω (σ ω)` is measurable on `M`. -/
theorem measurable_at_of_dense_good {ρ : Ω → ℝ≥0 → ℂ} {V : ℕ → Ω → ℂ} {good : ℕ → Ω → Prop}
    (hgood : ∀ i, MeasurableSet {ω | good i ω}) (hV : ∀ i, Measurable (V i)) {M : Set Ω} [DecidablePred (· ∈ M)]
    (hM : MeasurableSet M) {σ : Ω → ℝ≥0} (hσ : Measurable σ) (hval : ∀ ω ∈ M, ∀ i, good i ω → ρ ω (ratPt i) = V i ω)
    (hdense : ∀ ω ∈ M, ∀ ε : ℝ, 0 < ε → ∃ i, good i ω ∧ dist (ratPt i) (σ ω) < ε)
    (hlim : ∀ ω ∈ M, ∀ v : ℕ → ℕ, (∀ n, good (v n) ω) → Tendsto (fun n => ratPt (v n)) atTop (𝓝 (σ ω)) →
      Tendsto (fun n => ρ ω (ratPt (v n))) atTop (𝓝 (ρ ω (σ ω)))) :
    Measurable fun ω => if ω ∈ M then ρ ω (σ ω) else 0 := by
  -- the window events and the measurable first good index in each window
  set win : ℕ → ℕ → Ω → Prop := fun n i ω => good i ω ∧ dist (ratPt i) (σ ω) < 1 / ((n : ℝ) + 1) with hwin
  have hwinm : ∀ n i, MeasurableSet {ω | win n i ω} := fun n i =>
    (hgood i).inter (measurableSet_lt ((measurable_const.dist hσ)) measurable_const)
  set M' : Set Ω := {ω | ∀ n, ∃ i, win n i ω} with hM'
  have hM'm : MeasurableSet M' := by
    have : M' = ⋂ n, ⋃ i, {ω | win n i ω} := by ext ω; simp [hM']
    rw [this]; exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i => hwinm n i
  have hMM' : M ⊆ M' := fun ω hω n => hdense ω hω _ (by positivity)
  set q : ℕ → Ω → ℕ → Prop := fun n ω i => ω ∉ M' ∨ win n i ω with hq
  have hqex : ∀ n ω, ∃ i, q n ω i := fun n ω => by
    by_cases hω : ω ∈ M'
    · obtain ⟨i, hi⟩ := hω n; exact ⟨i, Or.inr hi⟩
    · exact ⟨0, Or.inl hω⟩
  have hqm : ∀ n i, MeasurableSet {ω | q n ω i} := fun n i => hM'm.compl.union (hwinm n i)
  have : ∀ n ω, DecidablePred (q n ω) := fun _ _ => Classical.decPred _
  set idx : ℕ → Ω → ℕ := fun n ω => Nat.find (hqex n ω) with hidx
  have hidxm : ∀ n, Measurable (idx n) := fun n => measurable_find (hqex n) (hqm n)
  set F : ℕ → Ω → ℂ := fun n ω => V (idx n ω) ω with hF
  have hFm : ∀ n, Measurable (F n) := fun n => by
    intro s hs
    have e : F n ⁻¹' s = ⋃ i, idx n ⁻¹' {i} ∩ V i ⁻¹' s := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff, hF]
      exact ⟨fun h => ⟨idx n ω, rfl, h⟩, fun ⟨i, hi, h⟩ => hi ▸ h⟩
    rw [e]
    exact MeasurableSet.iUnion fun i => (hidxm n (measurableSet_singleton i)).inter (hV i hs)
  -- on `M`, the selected values converge to `ρ ω (σ ω)`
  have hlim' : ∀ ω ∈ M, Tendsto (fun n => F n ω) atTop (𝓝 (ρ ω (σ ω))) := by
    intro ω hω
    have hspec : ∀ n, win n (idx n ω) ω := fun n => by
      rcases Nat.find_spec (hqex n ω) with h | h
      · exact absurd (hMM' hω) h
      · exact h
    have hconv : Tendsto (fun n => ratPt (idx n ω)) atTop (𝓝 (σ ω)) := by
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun n => (hspec n).2.le) ?_)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    refine (hlim ω hω (fun n => idx n ω) (fun n => (hspec n).1) hconv).congr fun n => ?_
    exact hval ω hω _ (hspec n).1
  set Gl : Ω → ℂ := fun ω => limUnder atTop fun n => F n ω with hGl
  have hGlm : Measurable Gl :=
    (StronglyMeasurable.limUnder fun n => (hFm n).stronglyMeasurable).measurable
  have e : (fun ω => if ω ∈ M then ρ ω (σ ω) else 0) = fun ω => if ω ∈ M then Gl ω else 0 := by
    funext ω
    by_cases hω : ω ∈ M
    · simp only [hω, ↓reduceIte, hGl]
      exact ((hlim' ω hω).limUnder_eq).symm
    · simp only [hω, ↓reduceIte]
  rw [e]
  exact Measurable.ite hM hGlm measurable_const

/-- The sequential continuity along good times from continuity within a set containing them. -/
theorem tendsto_of_continuousWithinAt {f : ℝ≥0 → ℂ} {S : Set ℝ≥0} {t : ℝ≥0} (hf : ContinuousWithinAt f S t)
    {good : ℕ → Prop} (hS : ∀ i, good i → ratPt i ∈ S) (v : ℕ → ℕ) (hv : ∀ n, good (v n))
    (hconv : Tendsto (fun n => ratPt (v n)) atTop (𝓝 t)) :
    Tendsto (fun n => f (ratPt (v n))) atTop (𝓝 (f t)) :=
  hf.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hconv, Eventually.of_forall fun n => hS _ (hv n)⟩)

/-- A masked measurable value with any constant off the mask. -/
theorem measurable_ite_of_masked {β : Type*} [MeasurableSpace β] [Zero β] {M : Set Ω} [DecidablePred (· ∈ M)]
    (hM : MeasurableSet M)
    {f : Ω → β} (hf : Measurable fun ω => if ω ∈ M then f ω else 0) (v : β) :
    Measurable fun ω => if ω ∈ M then f ω else v := by
  have e : (fun ω => if ω ∈ M then f ω else v) =
      fun ω => if ω ∈ M then (if ω ∈ M then f ω else 0) else v := by
    funext ω; by_cases h : ω ∈ M <;> simp [h]
  rw [e]
  exact Measurable.ite hM hf measurable_const

/-! ### The stage time -/

/-- **The stage time at a fixed curve time is measurable in a measurable lifetime.** -/
theorem measurable_stTime {L : Ω → ℝ≥0∞} (hL : Measurable L) (u : ℝ) : Measurable fun ω => stTime (L ω) u := by
  classical
  unfold stTime
  refine Measurable.real_toNNReal (Measurable.ite (hL (measurableSet_singleton ⊤)) measurable_const ?_)
  unfold clockOf
  exact (ENNReal.measurable_toReal.comp hL).mul measurable_const

end InteractingSLE.Theorem14.SB.Nv
