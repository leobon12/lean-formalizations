/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LinesSafe

/-!
# The physical-to-relative time change for SB2(1)'s lines

Packet PROVE-AUX61-NOJUMP (Theorem 1.4, SB2(1)'s line data, version half; interface `Lv.SB2LineVersion` of
PROVE-T14-SB2DRV). K2's filtration is indexed by the **relative** capacity time of the upper flow's remainder, while
the line σ-algebras `t ↦ D.lineMarks t` are indexed by the **physical** time after the entrance `T_L`. With a clock
`a : ℝ≥0 → Ω → ℝ≥0∞` (relative time reached at physical time `t`), adapted to the physical filtration `𝓖`, the
relative filtration is the time change

  `tcFilt 𝓖 a q = {D measurable : D ∩ {q ≤ a t} ∈ 𝓖 t for every t}`

(the σ-algebra of the first passage of `a` at `q`; `Restart.DomainMarkov.Aux79.timeChange` for `ℝ≥0`-valued clocks).
This file supplies the generic fields of the interface:

* `tcSigma`, `tcFilt`; `measurableSet_tcFilt_iff`;
* **`tcFilt_inter`**: the interface's `timeChange` field (BW1Lines' `h𝓗'`) holds by construction;
* **`le_tcFilt_zero`**: `𝒢 ≤ tcFilt 𝓖 a 0` whenever `𝒢 ≤ 𝓖 t` for every `t` (the `marks_le` field from
  `D.marks ≤ D.lineFilt t`);
* **`stronglyAdapted_tcFilt_of_read`**: a relative process whose value at relative time `q` is read, on `{q ≤ a t}`, from
  a `𝓖 t`-measurable variable is strongly adapted to the time change (the `W_adapted` field);
* `reach_of_le_clockLife`: below the clock's supremum every relative level is reached (the `reach` field when the
  lifetime is at most `BW1Lines.clockLife a`).

Deterministic in the data; nothing here replaces a source statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Tc

section Main

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The σ-algebra of the time change at relative time `q`: measurable events cut into `𝓖 t`-events by
`{q ≤ a t}` for every physical time `t`. -/
@[instance_reducible]
def tcSigma (𝓖 : Filtration ℝ≥0 mΩ) (a : ℝ≥0 → Ω → ℝ≥0∞) (ha : ∀ t, Measurable[𝓖 t] (a t)) (q : ℝ≥0) :
    MeasurableSpace Ω where
  MeasurableSet' D := MeasurableSet D ∧ ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω})
  measurableSet_empty := ⟨MeasurableSet.empty, fun t => by
    rw [empty_inter]; exact @MeasurableSet.empty Ω (𝓖 t)⟩
  measurableSet_compl D hD := ⟨hD.1.compl, fun t => by
    have hA : MeasurableSet[𝓖 t] {ω | (q : ℝ≥0∞) ≤ a t ω} := measurableSet_le measurable_const (ha t)
    have e : Dᶜ ∩ {ω | (q : ℝ≥0∞) ≤ a t ω} = {ω | (q : ℝ≥0∞) ≤ a t ω} \ (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]
    exact hA.diff (hD.2 t)⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun t => by
    rw [iUnion_inter]
    exact MeasurableSet.iUnion fun i => (hf i).2 t⟩

/-- **The time-changed filtration** of a physical filtration `𝓖` along an adapted `ℝ≥0∞`-valued clock `a`. -/
def tcFilt (𝓖 : Filtration ℝ≥0 mΩ) (a : ℝ≥0 → Ω → ℝ≥0∞) (ha : ∀ t, Measurable[𝓖 t] (a t)) :
    Filtration ℝ≥0 mΩ where
  seq := tcSigma 𝓖 a ha
  mono' q q' hqq' D hD := ⟨hD.1, fun t => by
    have hA : MeasurableSet[𝓖 t] {ω | (q' : ℝ≥0∞) ≤ a t ω} := measurableSet_le measurable_const (ha t)
    have e : D ∩ {ω | (q' : ℝ≥0∞) ≤ a t ω} =
        (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}) ∩ {ω | (q' : ℝ≥0∞) ≤ a t ω} := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨⟨h.1, (ENNReal.coe_le_coe.2 hqq').trans h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [e]
    exact (hD.2 t).inter hA⟩
  le' _ _ hD := hD.1

variable {𝓖 : Filtration ℝ≥0 mΩ} {a : ℝ≥0 → Ω → ℝ≥0∞} {ha : ∀ t, Measurable[𝓖 t] (a t)}

theorem measurableSet_tcFilt_iff {q : ℝ≥0} {D : Set Ω} :
    MeasurableSet[tcFilt 𝓖 a ha q] D ↔
      MeasurableSet D ∧ ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}) := Iff.rfl

/-- **The time-change compatibility** (the interface's `timeChange` field, BW1Lines' `h𝓗'`). -/
theorem tcFilt_inter (q : ℝ≥0) (D : Set Ω) (hD : MeasurableSet[tcFilt 𝓖 a ha q] D) (t : ℝ≥0) :
    MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}) := hD.2 t

/-- **Adaptedness through reading** (the interface's `W_adapted` field): if `W q` is measurable and, on
`{q ≤ a t}`, equals a `𝓖 t`-measurable variable `Y q t`, then `W` is strongly adapted to the time change. -/
theorem stronglyAdapted_tcFilt_of_read {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ q, Measurable (W q))
    (Y : ℝ≥0 → ℝ≥0 → Ω → ℝ) (hY : ∀ q t, Measurable[𝓖 t] (Y q t))
    (hread : ∀ (q t : ℝ≥0) (ω : Ω), (q : ℝ≥0∞) ≤ a t ω → W q ω = Y q t ω) :
    StronglyAdapted (tcFilt 𝓖 a ha) W := by
  intro q
  refine Measurable.stronglyMeasurable fun B hB => ⟨hWm q hB, fun t => ?_⟩
  have hA : MeasurableSet[𝓖 t] {ω | (q : ℝ≥0∞) ≤ a t ω} := measurableSet_le measurable_const (ha t)
  have e : W q ⁻¹' B ∩ {ω | (q : ℝ≥0∞) ≤ a t ω} = Y q t ⁻¹' B ∩ {ω | (q : ℝ≥0∞) ≤ a t ω} := by
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    exact ⟨fun h => ⟨hread q t ω h.2 ▸ h.1, h.2⟩, fun h => ⟨(hread q t ω h.2).symm ▸ h.1, h.2⟩⟩
  rw [e]
  exact (hY q t hB).inter hA

omit mΩ in
/-- **The reach of the lifetime** (the interface's `reach` field): below the clock's supremum every relative level is
reached at some physical time. -/
theorem reach_of_le_clockLife {V : Ω → ℝ≥0∞} {ω : Ω} (hV : V ω ≤ BW1Lines.clockLife a ω) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < V ω) : ∃ t, (q : ℝ≥0∞) ≤ a t ω :=
  BW1Lines.exists_le_of_lt_clockLife (hq.trans_le hV)

end Main

/-- **A σ-algebra below every physical time is below the time change at `0`** (the interface's `marks_le` field). The
extra σ-algebra is bound before the ambient instance. -/
theorem le_tcFilt_zero {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 mΩ}
    {a : ℝ≥0 → Ω → ℝ≥0∞} {ha : ∀ t, Measurable[𝓖 t] (a t)} (h𝒢 : ∀ t, 𝒢 ≤ 𝓖 t) :
    𝒢 ≤ tcFilt 𝓖 a ha 0 := by
  intro D hD
  refine ⟨𝓖.le 0 _ (h𝒢 0 _ hD), fun t => ?_⟩
  have e : D ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) ≤ a t ω} = D := inter_eq_left.2 fun ω _ => by
    simp only [ENNReal.coe_zero, mem_ofPred_eq, zero_le]
  rw [e]
  exact h𝒢 t _ hD

end InteractingSLE.Theorem14.SB.Tc
