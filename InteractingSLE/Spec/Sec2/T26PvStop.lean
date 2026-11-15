/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.T26PvIto

/-!
# Theorem 2.6, the provider, part 6: stopping times

Packet PROVE-T26-PROVIDER. Theorem 2.6 is localized "before the two stopping times specified in the theorem"
(`source/spec/p001-048.md` L986): the swallowing time `τ_z` and the continuation threshold `T_*`.

* `isStoppingTime_swallowTime`: in a right-continuous filtration to which a continuous driver is adapted, `τ_z` is a
  stopping time: `{t ≤ τ_z}` is the countable intersection over rationals `q < t` of the unions over rationals
  `r ∈ (q, t)` of the events that `z` has a forward solution on `[0, r]` (`Ito.aliveSet`, measurable at time `r`);
* `exists_pos_stop_lt`: from the localizing times of a continuous local martingale before `ζ > 0` (which are `0` or
  strictly below `ζ` and exhaust it almost surely), a finite stopping time that is everywhere positive and almost
  surely strictly below `ζ`: the first positive localizer, capped at `1`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T26Pv

open Ito

section Swallow

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {z : ℂ}

/-- A forward solution on `[0, r]` means `r ≤ τ_z`. -/
theorem le_swallowTime_of_mem_alv {ω : Ω} {r : ℝ≥0} (h : ω ∈ alv W z r) :
    (r : ℝ≥0∞) ≤ QuantumZipper.swallowTime (rpath (W · ω)) z := by
  obtain ⟨-, -, u, hu⟩ := h
  have := QuantumZipper.ofReal_le_swallowTime (W := rpath (W · ω)) (z := z) r.coe_nonneg ⟨u, hu⟩
  rwa [ENNReal.ofReal_coe_nnreal] at this

/-- **`{t ≤ τ_z}` from the alive events at rational times below `t`.** -/
theorem setOf_le_swallowTime_eq (hz : z ∈ H) (t : ℝ≥0) :
    {ω | (t : ℝ≥0∞) ≤ QuantumZipper.swallowTime (rpath (W · ω)) z} =
      ⋂ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < t), ⋃ (r : ℚ) (_ : (q : ℝ) < r ∧ (r : ℝ) < t),
        alv W z (r : ℝ).toNNReal := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, exists_prop]
  constructor
  · rintro h q ⟨hq0, hqt⟩
    obtain ⟨r, hqr, hrt⟩ := exists_rat_btwn hqt
    refine ⟨r, ⟨hqr, hrt⟩, mem_alv_of_lt hz (lt_of_lt_of_le ?_ h)⟩
    have hr0 : (0 : ℝ) ≤ r := hq0.trans hqr.le
    have : (r : ℝ).toNNReal < t := by
      rw [Real.toNNReal_lt_iff_lt_coe hr0]
      exact hrt
    exact_mod_cast this
  · intro h
    by_contra hlt
    push Not at hlt
    have hne : QuantumZipper.swallowTime (rpath (W · ω)) z ≠ ⊤ := ne_top_of_lt hlt
    set s : ℝ := (QuantumZipper.swallowTime (rpath (W · ω)) z).toReal with hs
    have hst : s < t := by
      have := (ENNReal.toReal_lt_toReal hne ENNReal.coe_ne_top).2 hlt
      simpa [hs] using this
    obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hst
    have hq0 : (0 : ℝ) ≤ q := (ENNReal.toReal_nonneg).trans hsq.le
    obtain ⟨r, ⟨hqr, -⟩, hr⟩ := h q ⟨hq0, hqt⟩
    have hle := le_swallowTime_of_mem_alv hr
    have hle' : (r : ℝ) ≤ s := by
      have h1 := (ENNReal.toReal_le_toReal ENNReal.coe_ne_top hne).2 hle
      rw [ENNReal.coe_toReal, Real.coe_toNNReal _ (hq0.trans hqr.le)] at h1
      exact h1
    linarith

/-- **`τ_z` is a stopping time** of a right-continuous filtration to which the continuous driver is adapted. -/
theorem isStoppingTime_swallowTime [𝓖.IsRightContinuous] (hWa : StronglyAdapted 𝓖 W)
    (hWc : ∀ ω, Continuous (W · ω)) (hz : z ∈ H) :
    IsStoppingTime 𝓖 fun ω => (QuantumZipper.swallowTime (rpath (W · ω)) z : WithTop ℝ≥0) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have hm : MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) ≤ QuantumZipper.swallowTime (rpath (W · ω)) z}ᶜ := by
    rw [setOf_le_swallowTime_eq hz t]
    refine MeasurableSet.compl (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq =>
      MeasurableSet.iUnion fun r => MeasurableSet.iUnion fun hr => ?_)
    have hrt : (r : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2.le
    exact 𝓖.mono hrt _ (Ito.measurableSet_aliveSet (adaptedBefore_top_of_stronglyAdapted hWa)
      (fun ω _ => (hWc ω).continuousOn) (@MeasurableSet.univ Ω (𝓖 0)) hz _)
  convert hm using 1
  ext ω
  simp only [mem_ofPred_eq, mem_compl_iff, not_le]
  rfl

end Swallow

section PosStop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}

open Classical in
/-- The first positive localizer capped at `1` (`1` if none is positive). -/
def firstPos (σ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  if h : ∃ n, 0 < σ n ω then min 1 (σ (Nat.find h) ω) else 1

theorem firstPos_le_one (σ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) : firstPos σ ω ≤ 1 := by
  classical
  unfold firstPos
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem firstPos_pos (σ : ℕ → Ω → WithTop ℝ≥0) (ω : Ω) : 0 < firstPos σ ω := by
  classical
  unfold firstPos
  split_ifs with h
  · exact lt_min (by exact_mod_cast zero_lt_one) (Nat.find_spec h)
  · exact_mod_cast zero_lt_one

theorem isStoppingTime_firstPos {σ : ℕ → Ω → WithTop ℝ≥0} (hσ : ∀ n, IsStoppingTime 𝓖 (σ n)) :
    IsStoppingTime 𝓖 (firstPos σ) := by
  classical
  intro t
  have hpos : ∀ n, MeasurableSet[𝓖 t] {ω | 0 < σ n ω} := fun n => by
    have h := (hσ n 0).compl
    have e : {ω | σ n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0)}ᶜ = {ω | 0 < σ n ω} := by
      ext ω
      simp only [mem_compl_iff, mem_ofPred_eq, not_le]
      rfl
    rw [e] at h
    exact 𝓖.mono (zero_le : (0 : ℝ≥0) ≤ t) _ h
  set A : ℕ → Set Ω := fun n => {ω | 0 < σ n ω} ∩ ⋂ m ∈ Finset.range n, {ω | 0 < σ m ω}ᶜ with hA
  have hAm : ∀ n, MeasurableSet[𝓖 t] (A n) := fun n =>
    (hpos n).inter (MeasurableSet.biInter (Finset.range n).countable_toSet fun m _ => (hpos m).compl)
  have hnone : MeasurableSet[𝓖 t] {ω | ¬ ∃ n, 0 < σ n ω} := by
    have e : {ω | ¬ ∃ n, 0 < σ n ω} = ⋂ n, {ω | 0 < σ n ω}ᶜ := by
      ext ω; simp
    rw [e]
    exact MeasurableSet.iInter fun n => (hpos n).compl
  have e : {ω | firstPos σ ω ≤ t} = (⋃ n, A n ∩ ({ω | (1 : WithTop ℝ≥0) ≤ t} ∪ {ω | σ n ω ≤ t})) ∪
      ({ω | ¬ ∃ n, 0 < σ n ω} ∩ {ω | (1 : WithTop ℝ≥0) ≤ t}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, hA, mem_iInter, mem_compl_iff,
      Finset.mem_range]
    by_cases h : ∃ n, 0 < σ n ω
    · have hf : firstPos σ ω = min 1 (σ (Nat.find h) ω) := by
        simp only [firstPos, dite_eq_left_of_eq_true (eq_true h)]
      rw [hf, min_le_iff]
      constructor
      · intro hle
        refine Or.inl ⟨Nat.find h, ⟨Nat.find_spec h, fun m hm => Nat.find_min h hm⟩, hle⟩
      · rintro (⟨n, ⟨hn, hmin⟩, hle⟩ | ⟨hno, -⟩)
        · have hn' : Nat.find h = n := (Nat.find_eq_iff h).2 ⟨hn, fun m hm => hmin m hm⟩
          rw [hn']
          exact hle
        · exact absurd h hno
    · have hf : firstPos σ ω = 1 := by
        simp only [firstPos, h, ↓reduceDIte]
      rw [hf]
      constructor
      · intro hle
        exact Or.inr ⟨h, hle⟩
      · rintro (⟨n, ⟨hn, -⟩, -⟩ | ⟨-, hle⟩)
        · exact absurd ⟨n, hn⟩ h
        · exact hle
  rw [e]
  refine (MeasurableSet.iUnion fun n => (hAm n).inter ((MeasurableSet.const _).union (hσ n t))).union
    (hnone.inter (MeasurableSet.const _))

/-- **A positive stop strictly below `ζ`.** From localizing times that are `0` or strictly below `ζ > 0` and exhaust
`ζ` almost surely: a finite stopping time, everywhere positive, almost surely strictly below `ζ`. -/
theorem exists_pos_stop_lt {ζ : Ω → WithTop ℝ≥0} (hζ0 : ∀ ω, 0 < ζ ω) {σ : ℕ → Ω → WithTop ℝ≥0}
    (hσ : ∀ n, IsStoppingTime 𝓖 (σ n)) (hσζ : ∀ n ω, σ n ω = 0 ∨ σ n ω < ζ ω)
    (hex : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < ζ ω → ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) :
    ∃ T : Ω → ℝ≥0, IsStoppingTime 𝓖 (fun ω => (T ω : WithTop ℝ≥0)) ∧ (∀ ω, 0 < T ω) ∧
      ∀ᵐ ω ∂P, (T ω : WithTop ℝ≥0) < ζ ω := by
  classical
  have hfin : ∀ ω, firstPos σ ω ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (firstPos_le_one σ ω)
  refine ⟨fun ω => (firstPos σ ω).untopA, ?_, fun ω => ?_, ?_⟩
  · have e : (fun ω => (((firstPos σ ω).untopA : ℝ≥0) : WithTop ℝ≥0)) = firstPos σ := by
      funext ω
      exact Certify2426.coe_untopA_of_ne_top (hfin ω)
    rw [e]
    exact isStoppingTime_firstPos hσ
  · have h := firstPos_pos σ ω
    rw [← Certify2426.coe_untopA_of_ne_top (hfin ω)] at h
    exact_mod_cast h
  · filter_upwards [hex] with ω hω
    rw [Certify2426.coe_untopA_of_ne_top (hfin ω)]
    have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) < ζ ω := by simpa using hζ0 ω
    obtain ⟨n, hn⟩ := (hω 0 h0).exists
    have hex' : ∃ n, 0 < σ n ω := ⟨n, by simpa using hn⟩
    have hf : firstPos σ ω = min 1 (σ (Nat.find hex') ω) := by
      simp only [firstPos, dite_eq_left_of_eq_true (eq_true hex')]
    rw [hf]
    have hp := Nat.find_spec hex'
    rcases hσζ (Nat.find hex') ω with h | h
    · rw [h] at hp; exact absurd hp (lt_irrefl _)
    · exact (min_le_right _ _).trans_lt h

end PosStop

end InteractingSLE.Sec2.T26Pv
