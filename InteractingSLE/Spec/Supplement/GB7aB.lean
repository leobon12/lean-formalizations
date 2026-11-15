/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux62Evol
import InteractingSLE.Spec.Supplement.GB7aFlow
import InteractingSLE.Spec.Supplement.G12Statement
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Lemma GB7a from the comparison of Aux. lemmas 61–64

Packet PROVE-GB7A2. Source: Lemma GB7a and its proof (supplement §8.7, p. 523), Aux. lemmas 61–64
(`source/spec/p241-288.md`, pp. 261–265).

GB7a's proof has a pathwise half and a probabilistic half:

1. *(pathwise)* a visit of the open interval between a mark `k` and the next mark forces a final contact-free own-time
   interval before the first visit; restarting at a rational time `q` in it, the monitored marks stay off the driver
   on `[q, T)`, the repelled gap `V_k − W` tends to `0` at the first-visit time `T`, and — in the chart at `q`, by the
   energy identity of Aux. 61 (`Aux61Cutoff.exists_markDrift_energy_le`) for the comparison weight
   `S = ∑_{xᵢ ≤ x_k} ρᵢ` at `k` — the drift energy on `[q, T)` is bounded;
2. *(probabilistic)* the Girsanov comparison (`Aux62Evol.measure_eq_zero_of_evolution`): for `S ≥ κ/2 − 2` this
   picture has probability `0` for each fixed `q`.

This file proves the probabilistic half and the bookkeeping from flow lines to evolutions. The pathwise half is the
named input `GB7aCmpInput` (it is **not proved in Lean**; see the handoff `PROVE-GB7A2.md`):

* `RightCmp`: the comparison picture at the restart time `q` (right side);
* `measure_rightCmp_eq_zero` (proved): the comparison picture is null when `S ≥ κ/2 − 2`, `κ ≤ 4`;
* `GB7aCmpInput` (named input): almost surely, a visit of the interval right of the mark `k` (resp. left of a left
  mark) produces the comparison picture at some rational `q` (for the left side, of the reflected evolution);
* `gb7aEvol_right`, `gb7aEvol_left` (proved from the input): almost surely the trace avoids the interval when its
  cumulative weight is `≥ κ/2 − 2`;
* `Supp8.gb7aFlowStatement_of_cmpInput` (proved from the input): **Lemma GB7a**, `Supp8.GB7aFlowStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace GB7a

open Girsanov Sec2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- **The comparison picture at the restart time `q`** (right side): there is a time `T > q` before the lifetime such
that, on `[q, T)`, the marks of nonzero old or comparison weight (and `k`) are off the driver with bounded drift
energy, and the gap `V_k − W` tends to `0` at `T`. -/
def RightCmp (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (k : Fin nR) (k2 : Option (Fin nR)) (S : ℝ) (q : ℝ≥0)
    (ω : Ω) : Prop :=
  ∃ T : ℝ≥0, q < T ∧ (T : ℝ≥0∞) ≤ ζ ω ∧
    (∀ t : ℝ≥0, q ≤ t → t < T → (∀ i, ρL i ≠ 0 → W t ω ≠ VL i t ω) ∧
      ∀ j, (ρR j ≠ 0 ∨ refWeightR k k2 S j ≠ 0 ∨ j = k) → W t ω ≠ VR j t ω) ∧
    (∃ C : ℝ, ∀ t : ℝ≥0, q ≤ t → t < T →
      (∫ s in (q : ℝ)..t, ((∑ i, -ρL i / (W s.toNNReal ω - VL i s.toNNReal ω)) +
        ∑ j, (refWeightR k k2 S j - ρR j) / (W s.toNNReal ω - VR j s.toNNReal ω)) ^ 2) ≤ C) ∧
    Tendsto (fun t => VR k t ω - W t ω) (𝓝[<] T) (𝓝 0)

/-- **The comparison picture is null** (Aux. lemmas 62–64; `κ ≤ 4`, `S ≥ κ/2 − 2`). -/
theorem measure_rightCmp_eq_zero {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {k : Fin nR} {k2 : Option (Fin nR)} (hk2 : ∀ j, k2 = some j → k < j) {S : ℝ} (hS : κ / 2 - 2 ≤ S)
    (q : ℝ≥0) : P {ω | RightCmp ρL ρR W VL VR ζ k k2 S q ω} = 0 :=
  measure_eq_zero_of_evolution hκ hκ4 hE hk2 hS q fun _ hω => hω

end GB7a

/-- **Named input (the pathwise half of GB7a's proof; not proved in Lean).** For an integrated `SLE_κ(ρ)` evolution
(`0 < κ < 4`) of an ordered force word with an almost-sure generating trace: almost surely, if the trace visits the
open interval between a right mark `k` and the next right mark (`a'` at most the next mark position), then the
comparison picture `RightCmp` holds at some rational restart time `q`, for the comparison weight
`S = ∑_{xᵢ ≤ x_k} ρᵢ` at `k`; symmetrically on the left, for the reflected evolution. -/
def GB7a.GB7aCmpInput : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) →
    (∀ (k : Fin nR) (a' : ℝ), xR k < a' → (∀ j, xR k < xR j → a' ≤ xR j) →
      ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ ∃ y ∈ Ioo (xR k) a', η ω t = y) →
        ∃ q : ℚ, GB7a.RightCmp ρL ρR W VL VR ζ k none (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i)
          (q : ℝ).toNNReal ω) ∧
    (∀ (k : Fin nL) (a : ℝ), a < xL k → (∀ j, xL j < xL k → xL j ≤ a) →
      ∀ᵐ ω ∂P, (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ ∃ y ∈ Ioo a (xL k), η ω t = y) →
        ∃ q : ℚ, GB7a.RightCmp ρR ρL (fun t ω => -W t ω) (fun i t ω => -VR i t ω) (fun i t ω => -VL i t ω) ζ k
          none (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) (q : ℝ).toNNReal ω)

namespace GB7a

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {η : Ω → ℝ≥0 → ℂ}

/-- **GB7a for an evolution, right side** (from the named pathwise input): if the cumulative weight up to the mark
`k` is at least `κ/2 − 2`, almost surely the trace does not visit the interval between `k` and the next mark. -/
theorem gb7aEvol_right (hIn : GB7aCmpInput.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nR} {a' : ℝ} (hka : xR k < a')
    (hnext : ∀ j, xR k < xR j → a' ≤ xR j)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo (xR k) a', η ω t ≠ y := by
  have hin := (hIn κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη).1 k a' hka hnext
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρL ρR W VL VR ζ k none
      (∑ i ∈ univ.filter (fun i => xR i ≤ xR k), ρR i) (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => measure_rightCmp_eq_zero hκ hκ4.le hE (by simp) hS _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht y hy he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, y, hy, he⟩))

/-- **GB7a for an evolution, left side** (from the named pathwise input, through the reflected evolution). -/
theorem gb7aEvol_left (hIn : GB7aCmpInput.{u}) (hκ : 0 < κ) (hκ4 : κ < 4) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {k : Fin nL} {a : ℝ} (hka : a < xL k)
    (hnext : ∀ j, xL j < xL k → xL j ≤ a)
    (hS : κ / 2 - 2 ≤ ∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → ∀ y ∈ Ioo a (xL k), η ω t ≠ y := by
  have hin := (hIn κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη).2 k a hka hnext
  have hER := IsIntegratedSLEEvolution.reflect hE
  have hnull : P (⋃ q : ℚ, {ω | RightCmp ρR ρL (fun t ω => -W t ω) (fun i t ω => -VR i t ω)
      (fun i t ω => -VL i t ω) ζ k none (∑ i ∈ univ.filter (fun i => xL k ≤ xL i), ρL i)
        (q : ℝ).toNNReal ω}) = 0 :=
    measure_iUnion_null fun q => measure_rightCmp_eq_zero hκ hκ4.le hER (by simp) hS _
  filter_upwards [hin, measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω hω' t ht y hy he
  exact hω' (mem_iUnion.2 (hω ⟨t, ht, y, hy, he⟩))

end GB7a

namespace Supp8

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)
open QuantumZipper (chiC)

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-- No genuine jump inside an interval on which `b` is constant off the jump candidates; both one-sided limits are
the constant. -/
theorem notMem_jumpSet_of_eq (hb : IsPiecewiseConstantBoundaryData b J) {a a' v : ℝ}
    (hv : ∀ y ∈ Ioo a a', y ∉ J → b y = v) {z : ℝ} (hz : z ∈ Ioo a a') :
    z ∉ jumpSet b J ∧ rightLim b z = v ∧ leftLim b z = v := by
  obtain ⟨δ, hδ, h⟩ := Supp7.exists_pos_eq_lims hb z
  set ε := min (δ / 2) (min ((z - a) / 2) ((a' - z) / 2)) with hε
  have hε0 : 0 < ε := lt_min (half_pos hδ) (lt_min (by linarith [hz.1]) (by linarith [hz.2]))
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hε1 : ε ≤ (z - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ (a' - z) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨h1, h2, h3, h4⟩ := h ε hε0 hεδ
  have hr : rightLim b z = v := by
    rw [← h3]
    exact hv _ ⟨by linarith [hz.1], by linarith⟩ h1
  have hl : leftLim b z = v := by
    rw [← h4]
    exact hv _ ⟨by linarith, by linarith [hz.2]⟩ h2
  refine ⟨fun hzJ => ?_, hr, hl⟩
  simp only [PiecewiseConstantBoundaryData.jumpSet, Finset.mem_filter] at hzJ
  exact hzJ.2 (hl.trans hr.symm)

/-- The right marks of the flow-line word: the seed `0` and the genuine jumps `z > x`, at `z − x`. -/
theorem flowLineXR_cases (x : ℝ) (j : Fin (flowLineNR b J x)) :
    flowLineXR b J x j = 0 ∨ ∃ z ∈ jumpSet b J, x < z ∧ flowLineXR b J x j = z - x := by
  revert j
  unfold flowLineNR flowLineXR
  intro j
  induction j using Fin.cases with
  | zero => exact Or.inl (Fin.cons_zero _ _)
  | succ i =>
    right
    have hm := ((jumpSet b J).filter (x < ·)).orderEmbOfFin_mem rfl i
    exact ⟨_, (Finset.mem_filter.1 hm).1, (Finset.mem_filter.1 hm).2, rfl⟩

/-- The left marks of the flow-line word: the seed `0` and the genuine jumps `z < x`, at `z − x`. -/
theorem flowLineXL_cases (x : ℝ) (j : Fin (flowLineNL b J x)) :
    flowLineXL b J x j = 0 ∨ ∃ z ∈ jumpSet b J, z < x ∧ flowLineXL b J x j = z - x := by
  revert j
  unfold flowLineNL flowLineXL
  intro j
  induction j using Fin.cases with
  | zero => exact Or.inl (Fin.cons_zero _ _)
  | succ i =>
    right
    have hm := ((jumpSet b J).filter (· < x)).orderEmbOfFin_mem rfl (Fin.rev i)
    exact ⟨_, (Finset.mem_filter.1 hm).1, (Finset.mem_filter.1 hm).2, rfl⟩

/-- **The right mark before an interval of constant data**: the last right mark `k` left of `(a, a')` (`x ≤ a`),
with no mark in `(x_k, a' − x)`, and cumulative weight `cumWeightRight κ (v + θχ)` up to `k`. -/
theorem exists_mark_right {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ)
    {x a a' v : ℝ} (hxa : x ≤ a) (haa : a < a') (hv : ∀ y ∈ Ioo a a', y ∉ J → b y = v) :
    ∃ k : Fin (flowLineNR b J x), flowLineXR b J x k ≤ a - x ∧
      (∀ j, flowLineXR b J x k < flowLineXR b J x j → a' - x ≤ flowLineXR b J x j) ∧
      ∑ i ∈ univ.filter (fun i => flowLineXR b J x i ≤ flowLineXR b J x k), flowLineRhoR κ b J x θ i =
        Sec4.cumWeightRight κ (v + θ * chiC κ) := by
  have hmono : Monotone (flowLineXR b J x) := (Theorem15.isOrderedForceWord_flowLine b J x).2.2.1
  set y' := (a + a') / 2 with hy'
  have hy'I : y' ∈ Ioo a a' := ⟨by linarith, by linarith⟩
  set F := univ.filter (fun i => flowLineXR b J x i ≤ y' - x) with hF
  have h0 : flowLineXR b J x ⟨0, by unfold flowLineNR; omega⟩ = 0 := rfl
  have hFne : F.Nonempty := ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [h0]; linarith⟩⟩
  set k := F.max' hFne with hk
  have hkF : flowLineXR b J x k ≤ y' - x := (Finset.mem_filter.1 (F.max'_mem hFne)).2
  have hle : ∀ i, flowLineXR b J x i ≤ y' - x → i ≤ k := fun i hi =>
    F.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  have hA : ∀ j, y' - x < flowLineXR b J x j → a' - x ≤ flowLineXR b J x j := fun j hj => by
    rcases flowLineXR_cases x j with h | ⟨z, hzJ, -, hz⟩
    · rw [h] at hj ⊢
      linarith
    · rw [hz] at hj ⊢
      by_contra hlt
      exact (notMem_jumpSet_of_eq hb hv ⟨by linarith, by linarith⟩).1 hzJ
  have hB : ∀ j, flowLineXR b J x j ≤ y' - x → flowLineXR b J x j ≤ a - x := fun j hj => by
    rcases flowLineXR_cases x j with h | ⟨z, hzJ, -, hz⟩
    · rw [h]
      linarith
    · rw [hz] at hj ⊢
      by_contra hlt
      exact (notMem_jumpSet_of_eq hb hv ⟨by linarith, by linarith⟩).1 hzJ
  refine ⟨k, hB k hkF, fun j hj => ?_, ?_⟩
  · by_contra hlt
    have hj' : flowLineXR b J x j ≤ y' - x := by
      by_contra h
      exact hlt (hA j (not_le.1 h))
    exact absurd (hmono (hle j hj')) (not_le.2 hj)
  · have e : univ.filter (fun i => flowLineXR b J x i ≤ flowLineXR b J x k) = F :=
      Finset.filter_congr fun i _ => ⟨fun h => h.trans hkF, fun h => hmono (hle i h)⟩
    rw [e, hF, Supp7.sum_filter_flowLineXR_le hκ hb θ (show x < y' by linarith [hy'I.1]),
      (notMem_jumpSet_of_eq hb hv hy'I).2.1]

/-- **The left mark after an interval of constant data** (`a' ≤ x`), symmetric to `exists_mark_right`. -/
theorem exists_mark_left {κ : ℝ} (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ)
    {x a a' v : ℝ} (hax : a' ≤ x) (haa : a < a') (hv : ∀ y ∈ Ioo a a', y ∉ J → b y = v) :
    ∃ k : Fin (flowLineNL b J x), a' - x ≤ flowLineXL b J x k ∧
      (∀ j, flowLineXL b J x j < flowLineXL b J x k → flowLineXL b J x j ≤ a - x) ∧
      ∑ i ∈ univ.filter (fun i => flowLineXL b J x k ≤ flowLineXL b J x i), flowLineRhoL κ b J x θ i =
        Sec4.cumWeightLeft κ (v + θ * chiC κ) := by
  have hanti : Antitone (flowLineXL b J x) := (Theorem15.isOrderedForceWord_flowLine b J x).1
  set y' := (a + a') / 2 with hy'
  have hy'I : y' ∈ Ioo a a' := ⟨by linarith, by linarith⟩
  set F := univ.filter (fun i => y' - x ≤ flowLineXL b J x i) with hF
  have h0 : flowLineXL b J x ⟨0, by unfold flowLineNL; omega⟩ = 0 := rfl
  have hFne : F.Nonempty := ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [h0]; linarith⟩⟩
  set k := F.max' hFne with hk
  have hkF : y' - x ≤ flowLineXL b J x k := (Finset.mem_filter.1 (F.max'_mem hFne)).2
  have hle : ∀ i, y' - x ≤ flowLineXL b J x i → i ≤ k := fun i hi =>
    F.le_max' i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  have hA : ∀ j, flowLineXL b J x j < y' - x → flowLineXL b J x j ≤ a - x := fun j hj => by
    rcases flowLineXL_cases x j with h | ⟨z, hzJ, -, hz⟩
    · rw [h] at hj ⊢
      linarith
    · rw [hz] at hj ⊢
      by_contra hlt
      exact (notMem_jumpSet_of_eq hb hv ⟨by linarith, by linarith⟩).1 hzJ
  have hB : ∀ j, y' - x ≤ flowLineXL b J x j → a' - x ≤ flowLineXL b J x j := fun j hj => by
    rcases flowLineXL_cases x j with h | ⟨z, hzJ, hzx, hz⟩
    · rw [h]
      linarith
    · rw [hz] at hj ⊢
      by_contra hlt
      exact (notMem_jumpSet_of_eq hb hv ⟨by linarith, by linarith⟩).1 hzJ
  refine ⟨k, hB k hkF, fun j hj => ?_, ?_⟩
  · by_contra hlt
    have hj' : y' - x ≤ flowLineXL b J x j := by
      by_contra h
      exact hlt (hA j (not_le.1 h))
    exact absurd (hanti (hle j hj')) (not_le.2 hj)
  · have e : univ.filter (fun i => flowLineXL b J x k ≤ flowLineXL b J x i) = F :=
      Finset.filter_congr fun i _ => ⟨fun h => hkF.trans h, fun h => hanti (hle i h)⟩
    rw [e, hF, Supp7.sum_filter_flowLineXL_ge hκ hb θ (show y' < x by linarith [hy'I.2]),
      (notMem_jumpSet_of_eq hb hv hy'I).2.2]

/-- **Lemma GB7a for a flow line, from the named pathwise input** `GB7aCmpInput` (the comparison of Aux. lemmas
61–64 is proved: `GB7a.measure_eq_zero_of_evolution`). -/
theorem gb7aFlowStatement_of_cmpInput (hIn : GB7a.GB7aCmpInput.{u}) : GB7aFlowStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x θ a a' v hv Ω _ P _ h _ η ζ hη
  obtain ⟨_h', 𝓕, W, VL, VR, B, -, hcpl, htr⟩ := hη
  have hord := Theorem15.isOrderedForceWord_flowLine b jumps x
  have key : ∀ ω t (y : ℝ), η ω t = y → η ω t - x = ((y - x : ℝ) : ℂ) := fun ω t y he => by
    rw [he]
    push_cast
    ring
  refine ⟨fun hxa hS => ?_, fun hax hS => ?_⟩
  · rcases le_or_gt a' a with haa | haa
    · exact ae_of_all _ fun ω t _ y hy => absurd (hy.1.trans hy.2) (not_lt.2 haa)
    obtain ⟨k, hka, hnext, hsum⟩ := exists_mark_right hκ hb θ hxa haa hv
    have hgb := GB7a.gb7aEvol_right hIn hκ hκ4 hord hcpl.1 htr (k := k) (a' := a' - x) (by linarith)
      hnext (by rw [hsum]; exact hS)
    filter_upwards [hgb] with ω hω t ht y hy he
    exact hω t ht (y - x) ⟨by linarith [hy.1], by linarith [hy.2]⟩ (key ω t y he)
  · rcases le_or_gt a' a with haa | haa
    · exact ae_of_all _ fun ω t _ y hy => absurd (hy.1.trans hy.2) (not_lt.2 haa)
    obtain ⟨k, hka, hnext, hsum⟩ := exists_mark_left hκ hb θ hax haa hv
    have hgb := GB7a.gb7aEvol_left hIn hκ hκ4 hord hcpl.1 htr (k := k) (a := a - x) (by linarith)
      hnext (by rw [hsum]; exact hS)
    filter_upwards [hgb] with ω hω t ht y hy he
    exact hω t ht (y - x) ⟨by linarith [hy.1], by linarith [hy.2]⟩ (key ω t y he)

end Supp8

end InteractingSLE
