/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsRead

/-!
# Reading a path-rule stop and the driver frozen there below a clock (D19, step 4)

Packet PROVE-AUX61-NOJUMP. Abstract setting, for one clock time: a σ-algebra `𝒢`, a `𝒢`-event `Eg`, a `𝒢`-measurable
clock value `τ`, a base driver `Wr` whose values at deterministic times `r < τ` are `𝒢`-measurable on `Eg`, a
`𝒢`-measurable record `rec`, and a measurable path rule `R`, with stop `V = R (rec, Wr)`.

* **`measurableSet_stop_le`**: `Eg ∩ {s < τ} ∩ {V ≤ s}` is a `𝒢`-event (the rule is decided by the driver frozen at
  `s`, `GW2Bh.pathRule_le_iff`);
* **`exists_frozen_reading`**: if moreover `Wr` is continuous before a lifetime `U > V` on `Eg`, the driver frozen at
  `V` is `𝒢`-measurable at every `q ≤ τ` on `Eg` (dyadic approximation of `V` from below on `{V < q}`, of `q` from
  below on `{q ≤ V}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Vs

open Exist.StagedLaw Supp8.GB6.HullId

section Abstract

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} {Eg : Set Ω} {τ : Ω → ℝ≥0∞} {Wr : ℝ≥0 → Ω → ℝ}
  {rec : Ω → RecData} {R : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}

/-- **The stop below the clock is read from the frozen driver.** -/
theorem measurableSet_stop_le (hEg : MeasurableSet[𝒢] Eg) (hτ : Measurable[𝒢] τ)
    (hZ : ∀ r : ℝ≥0, Measurable[𝒢] ((Eg ∩ {ω | (r : ℝ≥0∞) < τ ω}).indicator (Wr r)))
    (hrec : Measurable[𝒢] rec) (hR : Measurable R) (hRp : IsPathRule R) (s : ℝ≥0) :
    MeasurableSet[𝒢] (Eg ∩ {ω | (s : ℝ≥0∞) < τ ω} ∩ {ω | R (rec ω, fun u => Wr u ω) ≤ s}) := by
  set A := Eg ∩ {ω | (s : ℝ≥0∞) < τ ω} with hAdef
  have hA : MeasurableSet[𝒢] A := hEg.inter (measurableSet_lt measurable_const hτ)
  set Wf : Ω → ℝ≥0 → ℝ := fun ω u => A.indicator (Wr (min u s)) ω with hWf
  have hWfm : Measurable[𝒢] Wf := by
    refine measurable_pi_iff.2 fun u => ?_
    have e : (fun ω => Wf ω u) =
        A.indicator ((Eg ∩ {ω | ((min u s : ℝ≥0) : ℝ≥0∞) < τ ω}).indicator (Wr (min u s))) := by
      funext ω
      by_cases hω : ω ∈ A
      · have hω' : ω ∈ Eg ∩ {ω | ((min u s : ℝ≥0) : ℝ≥0∞) < τ ω} :=
          ⟨hω.1, lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right u s)) hω.2⟩
        simp only [hWf, indicator_of_mem hω, indicator_of_mem hω']
      · simp only [hWf, indicator_of_notMem hω]
    rw [e]
    exact (hZ _).indicator hA
  have e : A ∩ {ω | R (rec ω, fun u => Wr u ω) ≤ s} = A ∩ {ω | R (rec ω, Wf ω) ≤ s} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hω, hle⟩
      refine ⟨hω, (GW2Bh.pathRule_le_iff hRp fun u hu => ?_).1 hle⟩
      simp only [hWf, indicator_of_mem hω, min_eq_left hu]
    · rintro ⟨hω, hle⟩
      refine ⟨hω, (GW2Bh.pathRule_le_iff hRp fun u hu => ?_).2 hle⟩
      simp only [hWf, indicator_of_mem hω, min_eq_left hu]
  rw [e]
  exact hA.inter (measurableSet_le (hR.comp (hrec.prodMk hWfm)) measurable_const)

/-- The stop strictly below a level `c ≤ q` on `{q ≤ τ}`. -/
theorem measurableSet_stop_lt (hEg : MeasurableSet[𝒢] Eg) (hτ : Measurable[𝒢] τ)
    (hZ : ∀ r : ℝ≥0, Measurable[𝒢] ((Eg ∩ {ω | (r : ℝ≥0∞) < τ ω}).indicator (Wr r)))
    (hrec : Measurable[𝒢] rec) (hR : Measurable R) (hRp : IsPathRule R) {c q : ℝ≥0} (hcq : c ≤ q) :
    MeasurableSet[𝒢] (Eg ∩ {ω | (q : ℝ≥0∞) ≤ τ ω} ∩ {ω | R (rec ω, fun u => Wr u ω) < c}) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ c) with hc0 | hc0
  · have e : Eg ∩ {ω | (q : ℝ≥0∞) ≤ τ ω} ∩ {ω | R (rec ω, fun u => Wr u ω) < c} = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨-, hlt⟩
      rw [← hc0] at hlt
      exact absurd hlt (not_lt.2 zero_le)
    rw [e]; exact MeasurableSet.empty
  set s : ℕ → ℝ≥0 := fun n => c - 1 / ((n : ℝ≥0) + 1) with hs
  have hsc : ∀ n, s n < c := fun n => tsub_lt_self hc0 (by positivity)
  have e : Eg ∩ {ω | (q : ℝ≥0∞) ≤ τ ω} ∩ {ω | R (rec ω, fun u => Wr u ω) < c} =
      (Eg ∩ {ω | (q : ℝ≥0∞) ≤ τ ω}) ∩ ⋃ n : ℕ,
        (Eg ∩ {ω | (s n : ℝ≥0∞) < τ ω} ∩ {ω | R (rec ω, fun u => Wr u ω) ≤ s n}) := by
    ext ω
    simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hω, hq⟩, hlt⟩
      have hfin : R (rec ω, fun u => Wr u ω) ≠ ⊤ := ne_top_of_lt hlt
      set v := (R (rec ω, fun u => Wr u ω)).toNNReal with hv
      have hvc : v < c := by
        rw [← ENNReal.coe_lt_coe, hv, ENNReal.coe_toNNReal hfin]; exact hlt
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (show (v : ℝ) < c by exact_mod_cast hvc))
      have hvn : v ≤ s n := by
        have hn' : ((1 / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ) < (c : ℝ) - v := by push_cast; exact hn
        have hle : 1 / ((n : ℝ≥0) + 1) ≤ c := by
          rw [← NNReal.coe_le_coe]; have := v.2; linarith
        rw [hs, ← NNReal.coe_le_coe, NNReal.coe_sub hle]
        linarith
      refine ⟨⟨hω, hq⟩, n, ⟨hω, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ((hsc n).trans_le hcq)) hq⟩, ?_⟩
      rw [← ENNReal.coe_toNNReal hfin]; exact ENNReal.coe_le_coe.2 hvn
    · rintro ⟨⟨hω, hq⟩, n, -, hle⟩
      exact ⟨⟨hω, hq⟩, lt_of_le_of_lt hle (ENNReal.coe_lt_coe.2 (hsc n))⟩
  rw [e]
  exact (hEg.inter (measurableSet_le measurable_const hτ)).inter (MeasurableSet.iUnion fun n =>
    measurableSet_stop_le hEg hτ hZ hrec hR hRp _)

/-- **The driver frozen at the stop is read below the clock.** -/
theorem exists_frozen_reading (hEg : MeasurableSet[𝒢] Eg) (hτ : Measurable[𝒢] τ)
    (hZ : ∀ r : ℝ≥0, Measurable[𝒢] ((Eg ∩ {ω | (r : ℝ≥0∞) < τ ω}).indicator (Wr r)))
    (hrec : Measurable[𝒢] rec) (hR : Measurable R) (hRp : IsPathRule R) {U : Ω → ℝ≥0∞}
    (hcont : ∀ ω ∈ Eg, ContinuousOn (fun s => Wr s ω) {s | (s : ℝ≥0∞) < U ω})
    (hVU : ∀ ω ∈ Eg, R (rec ω, fun u => Wr u ω) < U ω) (hW0 : ∀ ω ∈ Eg, Wr 0 ω = 0) (q : ℝ≥0) :
    ∃ Y : Ω → ℝ, Measurable[𝒢] Y ∧ (∀ ω, ω ∉ Eg → Y ω = 0) ∧
      ∀ ω ∈ Eg, (q : ℝ≥0∞) ≤ τ ω → Y ω = Wr (min q (R (rec ω, fun u => Wr u ω)).toNNReal) ω := by
  classical
  set V : Ω → ℝ≥0∞ := fun ω => R (rec ω, fun u => Wr u ω) with hVdef
  have hopen : ∀ ω, IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < U ω} := fun ω =>
    isOpen_lt ENNReal.continuous_coe continuous_const
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ q) with hq0 | hq0
  · refine ⟨fun _ => 0, measurable_const, fun _ _ => rfl, fun ω hω _ => ?_⟩
    rw [← hq0, zero_min, hW0 ω hω]
  set A := Eg ∩ {ω | (q : ℝ≥0∞) ≤ τ ω} with hAdef
  have hA : MeasurableSet[𝒢] A := hEg.inter (measurableSet_le measurable_const hτ)
  set A₂ := Eg ∩ {ω | (q : ℝ≥0∞) ≤ τ ω} ∩ {ω | V ω < q} with hA₂def
  have hA₂ : MeasurableSet[𝒢] A₂ := measurableSet_stop_lt hEg hτ hZ hrec hR hRp le_rfl
  have hA₂c : ∀ c : ℝ≥0, MeasurableSet[𝒢] (A₂ ∩ {ω | V ω < c}) := fun c => by
    by_cases hcq : c ≤ q
    · have e : A₂ ∩ {ω | V ω < c} = (Eg ∩ {ω | (q : ℝ≥0∞) ≤ τ ω} ∩ {ω | V ω < c}) ∩ A₂ := by
        ext ω
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨⟨h1.1, h2⟩, h1⟩
        · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      rw [e]; exact (measurableSet_stop_lt hEg hτ hZ hrec hR hRp hcq).inter hA₂
    · have e : A₂ ∩ {ω | V ω < c} = A₂ := by
        refine inter_eq_left.2 fun ω hω => ?_
        exact lt_trans hω.2 (ENNReal.coe_lt_coe.2 (lt_of_not_ge hcq))
      rw [e]; exact hA₂
  set A₁ := A \ A₂ with hA₁def
  have hA₁ : MeasurableSet[𝒢] A₁ := hA.diff hA₂
  set Z : ℝ≥0 → Ω → ℝ := fun r => (Eg ∩ {ω | (r : ℝ≥0∞) < τ ω}).indicator (Wr r) with hZdef
  -- the reading on `{q ≤ V}`: from below `q`
  set rn : ℕ → ℝ≥0 := fun n => q * (1 - (1 / 2 : ℝ≥0) ^ (n + 1)) with hrn
  have hrnq : ∀ n, rn n < q := fun n =>
    mul_lt_of_lt_one_right hq0 (tsub_lt_self one_pos (pow_pos (by norm_num) _))
  have hrnt : Tendsto rn atTop (𝓝 q) := (Vk.tendsto_frac_nhdsLT hq0).mono_right nhdsWithin_le_nhds
  set Y₁ : Ω → ℝ := fun ω => limUnder atTop fun n => Z (rn n) ω with hY₁def
  have hY₁m : Measurable[𝒢] Y₁ :=
    (StronglyMeasurable.limUnder fun n => (hZ (rn n)).stronglyMeasurable).measurable
  -- the reading on `{V < q}`: dyadic approximation of the stop from below
  set g : ℕ → Ω → ℕ := fun n ω => if ω ∈ A₂ then ⌊(V ω).toNNReal * 2 ^ n⌋₊ else 0 with hgdef
  have hgm : ∀ n, Measurable[𝒢] (g n) := fun n => by
    refine measurable_to_countable' fun j => ?_
    have hfloor : ∀ ω ∈ A₂, (⌊(V ω).toNNReal * 2 ^ n⌋₊ = j ↔
        ¬ V ω < ((j : ℝ≥0) / 2 ^ n : ℝ≥0) ∧ V ω < (((j : ℝ≥0) + 1) / 2 ^ n : ℝ≥0)) := fun ω hω => by
      have hfin : V ω ≠ ⊤ := ne_top_of_lt hω.2
      have h2 : (0 : ℝ≥0) < 2 ^ n := by positivity
      obtain ⟨v, hv⟩ : ∃ v : ℝ≥0, V ω = v := ⟨_, (ENNReal.coe_toNNReal hfin).symm⟩
      rw [hv, ENNReal.toNNReal_coe, ENNReal.coe_lt_coe, ENNReal.coe_lt_coe, not_lt, Nat.floor_eq_iff (zero_le),
        div_le_iff₀ h2, lt_div_iff₀ h2]
    have e : g n ⁻¹' {j} = (A₂ ∩ ((A₂ ∩ {ω | V ω < ((j : ℝ≥0) / 2 ^ n : ℝ≥0)})ᶜ ∩
        (A₂ ∩ {ω | V ω < (((j : ℝ≥0) + 1) / 2 ^ n : ℝ≥0)}))) ∪ (A₂ᶜ ∩ {_ω | 0 = j}) := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, hgdef]
      by_cases hω : ω ∈ A₂
      · simp only [hω, ↓reduceIte, hfloor ω hω, true_and, not_true_eq_false, false_and, or_false]
      · simp only [hω, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
    rw [e]
    exact (hA₂.inter ((hA₂c _).compl.inter (hA₂c _))).union (hA₂.compl.inter (MeasurableSet.const _))
  set Zd : ℕ → Ω → ℝ := fun n ω => Z (((g n ω : ℕ) : ℝ≥0) / 2 ^ n) ω with hZddef
  have hZdm : ∀ n, Measurable[𝒢] (Zd n) := fun n =>
    Vm.measurable_comp_nat (hgm n) (F := fun j => Z ((j : ℝ≥0) / 2 ^ n)) fun j => hZ _
  set Y₂ : Ω → ℝ := fun ω => limUnder atTop fun n => Zd n ω with hY₂def
  have hY₂m : Measurable[𝒢] Y₂ :=
    (StronglyMeasurable.limUnder fun n => (hZdm n).stronglyMeasurable).measurable
  refine ⟨fun ω => A₁.indicator Y₁ ω + A₂.indicator Y₂ ω, (hY₁m.indicator hA₁).add (hY₂m.indicator hA₂),
    fun ω hω => ?_, fun ω hω hq => ?_⟩
  · have h1 : ω ∉ A₁ := fun h => hω h.1.1
    have h2 : ω ∉ A₂ := fun h => hω h.1.1
    simp only [indicator_of_notMem h1, indicator_of_notMem h2, add_zero]
  · have hVfin : V ω ≠ ⊤ := ne_top_of_lt (hVU ω hω)
    set v := (V ω).toNNReal with hv
    have hvV : (v : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal hVfin
    by_cases h₂ : ω ∈ A₂
    · -- the stop comes first
      have hvq : v < q := by rw [← ENNReal.coe_lt_coe, hvV]; exact h₂.2
      have h1 : ω ∉ A₁ := fun h => h.2 h₂
      simp only [indicator_of_notMem h1, indicator_of_mem h₂, zero_add, hY₂def]
      rw [show min q (V ω).toNNReal = v from min_eq_right hvq.le]
      have hval : ∀ n, Zd n ω = Wr (Vj.dfl n v) ω := fun n => by
        have hdfl : ((g n ω : ℕ) : ℝ≥0) / 2 ^ n = Vj.dfl n v := by
          simp only [hgdef, h₂, ↓reduceIte]; rfl
        have hmem : ω ∈ Eg ∩ {ω | ((Vj.dfl n v : ℝ≥0) : ℝ≥0∞) < τ ω} :=
          ⟨hω, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ((Vj.dfl_le n v).trans_lt hvq)) hq⟩
        simp only [hZddef, hdfl, hZdef, indicator_of_mem hmem]
      have hvU : (v : ℝ≥0∞) < U ω := by rw [hvV]; exact hVU ω hω
      have hc : Tendsto (fun s => Wr s ω) (𝓝 v) (𝓝 (Wr v ω)) :=
        ((hcont ω hω).continuousAt ((hopen ω).mem_nhds hvU)).tendsto
      refine Tendsto.limUnder_eq ?_
      exact (hc.comp (Vj.tendsto_dfl v)).congr fun n => (hval n).symm
    · -- the time comes first
      have h1 : ω ∈ A₁ := ⟨⟨hω, hq⟩, h₂⟩
      have hqV : q ≤ v := by
        by_contra hlt
        rw [not_le] at hlt
        exact h₂ ⟨⟨hω, hq⟩, show V ω < (q : ℝ≥0∞) by rw [← hvV]; exact ENNReal.coe_lt_coe.2 hlt⟩
      simp only [indicator_of_mem h1, indicator_of_notMem h₂, add_zero, hY₁def]
      rw [show min q (V ω).toNNReal = q from min_eq_left hqV]
      have hval : ∀ n, Z (rn n) ω = Wr (rn n) ω := fun n => by
        have hmem : ω ∈ Eg ∩ {ω | ((rn n : ℝ≥0) : ℝ≥0∞) < τ ω} :=
          ⟨hω, lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (hrnq n)) hq⟩
        simp only [hZdef, indicator_of_mem hmem]
      have hqU : (q : ℝ≥0∞) < U ω :=
        lt_of_le_of_lt (show (q : ℝ≥0∞) ≤ V ω by rw [← hvV]; exact ENNReal.coe_le_coe.2 hqV) (hVU ω hω)
      have hc : Tendsto (fun s => Wr s ω) (𝓝 q) (𝓝 (Wr q ω)) :=
        ((hcont ω hω).continuousAt ((hopen ω).mem_nhds hqU)).tendsto
      refine Tendsto.limUnder_eq ?_
      exact (hc.comp hrnt).congr fun n => (hval n).symm

end Abstract

end InteractingSLE.Theorem14.SB.Vs
