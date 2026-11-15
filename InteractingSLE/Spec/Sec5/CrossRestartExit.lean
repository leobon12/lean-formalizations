/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartInv
import InteractingSLE.Spec.Sec5.MarkovOther

/-!
# The exit of the counterflow in its restart chart: from a capacity clock to the chart continuation

Packet PROVE-SEC5-G (item (ii)(b) of `planning/handoffs/PROVE-SEC5-F.md`, "What remains" 1). The pathwise part of the
counterflow restart, `MarkovOther.IsCounterflowChartContinuation`, asks for an inverse chart `ψ`, an exit time `U′`
of the chart path `γ` (capacity time), a clock `c` to the physical time of the completed counterflow
`ξ = Sec4.stripCounterflowPath q γ′` and a physical exit time `s₁`. This file packages it from a **capacity clock**:
if the chart capacity `a(t)` of the counterflow hulls (counterflow time `t`) is continuous and strictly increasing
before the exit time `T` of the counterflow and **exhausts `[0, ∞)`** (the counterflow leaves the remaining domain at
the tip, which the restart chart sends to `∞`), and the chart path satisfies `ψ(γ(a t)) = M_q⁻¹(γ′ t)` before `T`,
then the continuation holds with `U′ = ∞`:

* `c(u) = r/(1 + r)` with `r = a⁻¹(u)` (`clockInv`), the physical time of `ξ` at counterflow time `r`;
* `s₁ = T/(1 + T)` (`1` if `T = ∞`).

The case of a finite chart exit time is not needed: under the conditional law of the restart (a flow line of the
mapped field, Lemma 4.5) the chart capacity is almost surely exhausted (`Lemma 4.5` gives an infinite lifetime and no
hit of the target arcs).

## Main results

* `physTime`, `physExit`: `r ↦ r/(1 + r)` and the physical exit time;
* `IsExhaustingClock`, `clockInv`: an exhausting clock before `T` and its inverse, with `clockInv_spec`,
  `clockInv_apply`, `strictMono_clockInv`, `image_clockInv`, `continuous_clockInv`;
* **`isCounterflowChartContinuation_of_clock`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

/-! ### Physical time of the completed counterflow -/

/-- The physical time `r/(1 + r) ∈ [0, 1)` of the completed counterflow at counterflow time `r ≥ 0`
(`Sec4.stripCounterflowPath` reads counterflow time `s/(1 − s)` at physical time `s`). -/
def physTime (r : ℝ) : ℝ := r / (1 + r)

theorem physTime_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ physTime r := div_nonneg hr (by linarith)

theorem physTime_lt_one {r : ℝ} (hr : 0 ≤ r) : physTime r < 1 := by
  rw [physTime, div_lt_one (by linarith)]; linarith

theorem physTime_pos {r : ℝ} (hr : 0 < r) : 0 < physTime r := div_pos hr (by linarith)

theorem physTime_div {r : ℝ} (hr : 0 ≤ r) : physTime r / (1 - physTime r) = r := by
  have h1 : (1 + r) ≠ 0 := by linarith
  rw [physTime]
  field_simp
  ring

theorem physTime_div_one_sub {s : ℝ} (hs : s < 1) : physTime (s / (1 - s)) = s := by
  have h1 : (1 - s) ≠ 0 := by linarith
  rw [physTime]
  field_simp
  ring

theorem strictMonoOn_physTime : StrictMonoOn physTime (Ici 0) := by
  intro r hr r' hr' h
  rw [physTime, physTime, div_lt_div_iff₀ (by linarith [mem_Ici.1 hr]) (by linarith [mem_Ici.1 hr'])]
  nlinarith

/-- The physical exit time `T/(1 + T)` (`1` if `T = ∞`). -/
def physExit (T : ℝ≥0∞) : ℝ := if T = ⊤ then 1 else physTime T.toReal

theorem physExit_le_one (T : ℝ≥0∞) : physExit T ≤ 1 := by
  unfold physExit
  split_ifs
  · exact le_rfl
  · exact (physTime_lt_one ENNReal.toReal_nonneg).le

theorem physExit_pos {T : ℝ≥0∞} (hT : 0 < T) : 0 < physExit T := by
  unfold physExit
  split_ifs with h
  · exact one_pos
  · exact physTime_pos (ENNReal.toReal_pos hT.ne' h)

/-- The physical times of the counterflow times before `T` form `[0, T/(1 + T))`. -/
theorem image_physTime (T : ℝ≥0∞) :
    (fun t : ℝ≥0 => physTime t) '' {t : ℝ≥0 | (t : ℝ≥0∞) < T} = Ico 0 (physExit T) := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨physTime_nonneg t.2, ?_⟩
    unfold physExit
    split_ifs with hT
    · exact physTime_lt_one t.2
    · have htT : (t : ℝ) < T.toReal := by
        have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hT).2 ht
        simpa using this
      exact strictMonoOn_physTime (mem_Ici.2 t.2) (mem_Ici.2 ENNReal.toReal_nonneg) htT
  · rintro ⟨hs0, hs1⟩
    have hs1' : s < 1 := lt_of_lt_of_le hs1 (physExit_le_one T)
    have hr : 0 ≤ s / (1 - s) := div_nonneg hs0 (by linarith)
    refine ⟨(s / (1 - s)).toNNReal, ?_, ?_⟩
    · show (((s / (1 - s)).toNNReal : ℝ≥0) : ℝ≥0∞) < T
      by_cases hT : T = ⊤
      · rw [hT]; exact ENNReal.coe_lt_top
      · have hs1'' : s < physTime T.toReal := by unfold physExit at hs1; rwa [ite_eq_right hT] at hs1
        have hlt : s / (1 - s) < T.toReal := by
          rw [← physTime_div_one_sub hs1'] at hs1''
          exact (strictMonoOn_physTime.lt_iff_lt (mem_Ici.2 hr) (mem_Ici.2 ENNReal.toReal_nonneg)).1 hs1''
        rw [show (((s / (1 - s)).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (s / (1 - s)) from rfl]
        exact (ENNReal.ofReal_lt_iff_lt_toReal hr hT).2 hlt
    · show physTime ((s / (1 - s)).toNNReal : ℝ) = s
      rw [Real.coe_toNNReal _ hr, physTime_div_one_sub hs1']

/-! ### Exhausting clocks and their inverses -/

/-- `a` is a clock of the counterflow before its exit time `T` that **exhausts `[0, ∞)`**: `a 0 = 0`, continuous and
strictly increasing before `T`, and unbounded there. -/
structure IsExhaustingClock (a : ℝ≥0 → ℝ) (T : ℝ≥0∞) : Prop where
  pos : 0 < T
  zero : a 0 = 0
  mono : StrictMonoOn a {t | (t : ℝ≥0∞) < T}
  cont : ContinuousOn a {t | (t : ℝ≥0∞) < T}
  unbounded : ∀ u : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ u ≤ a t

/-- The inverse of a clock before `T` (a choice of preimage; it is the inverse for exhausting clocks). -/
def clockInv (a : ℝ≥0 → ℝ) (T : ℝ≥0∞) (u : ℝ≥0) : ℝ≥0 :=
  Function.invFunOn (fun t => (a t).toNNReal) {t | (t : ℝ≥0∞) < T} u

namespace IsExhaustingClock

variable {a : ℝ≥0 → ℝ} {T : ℝ≥0∞} (ha : IsExhaustingClock a T)
include ha

theorem nonneg {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) : 0 ≤ a t := by
  rcases eq_or_lt_of_le (zero_le (a := t)) with h | h
  · rw [← h, ha.zero]
  · rw [← ha.zero]; exact (ha.mono (show ((0 : ℝ≥0) : ℝ≥0∞) < T by simpa using ha.pos) ht h).le

/-- Every capacity `u ≥ 0` is reached before `T`. -/
theorem exists_eq (u : ℝ≥0) : ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ a t = u := by
  obtain ⟨t₁, ht₁, hu⟩ := ha.unbounded u
  have hsub : Icc 0 t₁ ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < T} := fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₁
  have hc : ContinuousOn a (Icc 0 t₁) := ha.cont.mono hsub
  have h0 : a 0 ≤ u := by rw [ha.zero]; exact u.2
  obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (zero_le (a := t₁)) hc ⟨h0, hu⟩
  exact ⟨t, hsub ht, hteq⟩

theorem clockInv_spec (u : ℝ≥0) : (clockInv a T u : ℝ≥0∞) < T ∧ a (clockInv a T u) = u := by
  obtain ⟨t, ht, hteq⟩ := ha.exists_eq u
  have hmem : u ∈ (fun t => (a t).toNNReal) '' {t : ℝ≥0 | (t : ℝ≥0∞) < T} :=
    ⟨t, ht, by simp only [hteq, Real.toNNReal_coe]⟩
  have h1 := Function.invFunOn_mem hmem
  have h2 := Function.invFunOn_eq hmem
  refine ⟨h1, ?_⟩
  have h3 : (a (clockInv a T u)).toNNReal = u := h2
  have := ha.nonneg h1
  calc a (clockInv a T u) = ((a (clockInv a T u)).toNNReal : ℝ) := (Real.coe_toNNReal _ this).symm
    _ = u := by rw [h3]

theorem clockInv_apply {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) : clockInv a T (a t).toNNReal = t := by
  obtain ⟨h1, h2⟩ := ha.clockInv_spec (a t).toNNReal
  rw [Real.coe_toNNReal _ (ha.nonneg ht)] at h2
  exact ha.mono.injOn h1 ht h2

theorem toNNReal_clockInv (u : ℝ≥0) : (a (clockInv a T u)).toNNReal = u := by
  rw [(ha.clockInv_spec u).2, Real.toNNReal_coe]

theorem strictMono_clockInv : StrictMono (clockInv a T) := by
  intro u v huv
  obtain ⟨hu1, hu2⟩ := ha.clockInv_spec u
  obtain ⟨hv1, hv2⟩ := ha.clockInv_spec v
  by_contra h
  have h' := (ha.mono.le_iff_le hv1 hu1).2 (not_lt.1 h)
  rw [hu2, hv2] at h'
  exact absurd huv (not_lt.2 (by exact_mod_cast h'))

theorem image_clockInv : clockInv a T '' univ = {t : ℝ≥0 | (t : ℝ≥0∞) < T} := by
  ext t
  constructor
  · rintro ⟨u, -, rfl⟩
    exact (ha.clockInv_spec u).1
  · intro ht
    exact ⟨(a t).toNNReal, mem_univ _, ha.clockInv_apply ht⟩

theorem continuous_clockInv : Continuous (clockInv a T) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  refine continuousAt_of_monotoneOn_of_image_mem_nhds (s := univ)
    (ha.strictMono_clockInv.monotone.monotoneOn _) Filter.univ_mem ?_
  rw [ha.image_clockInv]
  exact (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds (ha.clockInv_spec u).1

end IsExhaustingClock

/-! ### The chart continuation -/

/-- **The pathwise counterflow restart from an exhausting clock** (`U′ = ∞`). Let `ψ` have the three properties of
an inverse restart chart (`CrossRestartInv.lean`), let `a` be an exhausting clock of the counterflow `γ′` (chart
`M_q`) before its exit time `T`, and let the chart path `γ` read the counterflow through `ψ` in the clock `a`:
`ψ(γ(a t)) = M_q⁻¹(γ′ t)` for `t < T`. Then the completed counterflow `ξ = Sec4.stripCounterflowPath q γ′` is
`ψ ∘ γ` in the clock `c(u) = a⁻¹(u)/(1 + a⁻¹(u))`, on `[0, ∞)`, with physical exit time `T/(1 + T)`. -/
theorem isCounterflowChartContinuation_of_clock {A : Set ℂ} {z : ℂ} {q Q : ℝ} {ψ : ℂ → ℂ}
    (hψ₁ : ∀ w ∈ H, ψ w ∉ Sec4.lowerLineH ∪ A)
    (hψ₂ : ∀ x : ℝ, -1 < x → x ≤ Q → ψ x ∉ Sec4.lowerLineH ∪ A)
    (hψ₃ : ∀ f : ℝ≥0 → ℂ, (∀ t, 0 ≤ (f t).im) → Tendsto (fun t => ‖f t‖) atTop atTop →
      Tendsto (fun t => ψ (f t)) atTop (𝓝 z))
    {γ' : ℝ≥0 → ℂ} {a : ℝ≥0 → ℝ} {T : ℝ≥0∞} (ha : IsExhaustingClock a T) {γ : ℝ≥0 → ℂ}
    (hγ : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → ψ (γ (a t).toNNReal) = (Sec4.stripCounterflowChart q).2.1 (γ' t)) :
    MarkovOther.IsCounterflowChartContinuation A z (Sec4.stripCounterflowPath q γ') Q γ ⊤ := by
  set c : ℝ≥0 → ℝ := fun u => physTime (clockInv a T u) with hc
  refine ⟨ψ, ⊤, c, physExit T, hψ₁, hψ₂, hψ₃, le_rfl, physExit_pos ha.pos, physExit_le_one T, ?_, ?_, ?_,
    fun h => absurd h (lt_irrefl _)⟩
  · intro u _ v _ huv
    exact strictMonoOn_physTime (mem_Ici.2 (clockInv a T u).2) (mem_Ici.2 (clockInv a T v).2)
      (by exact_mod_cast ha.strictMono_clockInv huv)
  · have hall : {u : ℝ≥0 | (u : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun u => ENNReal.coe_lt_top
    rw [hall, ← image_physTime T, ← ha.image_clockInv, image_image]
  · intro u _
    obtain ⟨h1, h2⟩ := ha.clockInv_spec u
    have hlt : c u < 1 := physTime_lt_one (clockInv a T u).2
    rw [Sec4.stripCounterflowPath_of_lt hlt]
    have hdiv : (c u / (1 - c u)).toNNReal = clockInv a T u := by
      rw [hc]
      simp only
      rw [physTime_div (NNReal.coe_nonneg _), Real.toNNReal_coe]
    rw [hdiv, ← hγ _ h1, ha.toNNReal_clockInv u]

end CrossRestart

end Sec5

end InteractingSLE
