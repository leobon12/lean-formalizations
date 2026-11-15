/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofPath

/-!
# DS2 in reach form, III: measurability of the stopped path

Packet PROVE-T14-DS. For a process `st ω : ℝ≥0 → E` killed at a random lifetime `ζ` (measurable killed values at
every fixed time) that is continuous before its lifetime and exits a closed set `K` before it, on a measurable set
`G` of good outcomes:

* `le_exitTime_iff`: `c ≤ exitTime` is decided by the values at the times of a countable dense set below `c`;
* `measurable_exitTime_piecewise`: the exit time is measurable on `G`;
* `measurable_stopPath_piecewise`: the stopped path is a measurable random element of `C([0, T], E)` on `G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DSReach

open scoped PathMeas

section Deterministic

variable {E : Type*} [TopologicalSpace E] {K : Set E} {T : ℝ≥0} {st : ℝ≥0 → E} {ζ : ℝ≥0∞}

/-- **`c ≤ exitTime` through a countable dense set**: for `c ≤ T`, `c ≤ exitTime` exactly when every time of the
dense set `D` below `c` is alive with its state in `K` (`K` closed, the path continuous before `ζ`). -/
theorem le_exitTime_iff (hK : IsClosed K) (hc : ContinuousOn st {s | (s : ℝ≥0∞) < ζ}) {D : Set ℝ≥0}
    (hD : Dense D) {c : ℝ≥0} (hcT : c ≤ T) :
    c ≤ exitTime K T st ζ ↔ ∀ q ∈ D, q < c → (q : ℝ≥0∞) < ζ ∧ st q ∈ K := by
  constructor
  · intro h q _ hq
    exact lt_and_mem_of_lt_exitTime (hq.trans_le h)
  · intro h
    refine le_csInf ⟨T, Or.inl rfl⟩ fun s hs => ?_
    by_contra hsc
    push Not at hsc
    -- every time below `c` is alive
    obtain ⟨q, hqD, hsq, hqc⟩ := hD.exists_between hsc
    have hsζ : (s : ℝ≥0∞) < ζ := lt_trans (by exact_mod_cast hsq) (h q hqD hqc).1
    -- and its state is in `K`, as a limit of states at dense times below `c`
    have hsK : st s ∈ K := by
      have hcl : s ∈ closure (Iio c ∩ D) := hD.open_subset_closure_inter isOpen_Iio hsc
      obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
      exact hK.mem_of_tendsto (((continuousAt_of_lt hc hsζ).tendsto).comp hlim)
        (Eventually.of_forall fun n => (h (u n) (hu n).2 (hu n).1).2)
    rcases hs with hsT | hbad
    · exact absurd (hsT ▸ hsc) (not_lt.2 hcT)
    · exact hbad ⟨hsζ, hsK⟩

end Deterministic

section Random

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] {K : Set E} {T : ℝ≥0} {st : Ω → ℝ≥0 → E} {ζ : Ω → ℝ≥0∞} {x₀ : E}
  {G : Set Ω}

omit [SecondCountableTopology E] in
open Classical in
/-- **The exit time is measurable on the good set.** -/
theorem measurable_exitTime_piecewise (hK : IsClosed K) (hG : MeasurableSet G)
    (hkill : ∀ q : ℝ≥0, Measurable fun ω => if (q : ℝ≥0∞) < ζ ω then st ω q else x₀)
    (hζ : ∀ q : ℝ≥0, MeasurableSet {ω | (q : ℝ≥0∞) < ζ ω})
    (hcont : ∀ ω ∈ G, ContinuousOn (st ω) {s | (s : ℝ≥0∞) < ζ ω}) :
    Measurable fun ω => if ω ∈ G then exitTime K T (st ω) (ζ ω) else 0 := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  refine measurable_of_Ici fun c => ?_
  have hgood : ∀ q : ℝ≥0, MeasurableSet {ω | (q : ℝ≥0∞) < ζ ω ∧ st ω q ∈ K} := by
    intro q
    have : {ω | (q : ℝ≥0∞) < ζ ω ∧ st ω q ∈ K} = {ω | (q : ℝ≥0∞) < ζ ω} ∩
        (fun ω => if (q : ℝ≥0∞) < ζ ω then st ω q else x₀) ⁻¹' K := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simp only [h1, ↓reduceIte]; exact h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simpa only [h1, ↓reduceIte] using h2⟩
    rw [this]
    exact (hζ q).inter (hkill q hK.measurableSet)
  by_cases hcT : c ≤ T
  · have e : (fun ω => if ω ∈ G then exitTime K T (st ω) (ζ ω) else 0) ⁻¹' Ici c =
        (G ∩ ⋂ q ∈ D, {ω | q < c → (q : ℝ≥0∞) < ζ ω ∧ st ω q ∈ K}) ∪ (Gᶜ ∩ {_ω | c ≤ 0}) := by
      ext ω
      simp only [mem_preimage, mem_Ici, mem_union, mem_inter_iff, mem_iInter, mem_ofPred_eq,
        mem_compl_iff]
      by_cases hω : ω ∈ G
      · simp only [hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
        exact le_exitTime_iff hK (hcont ω hω) hDd hcT
      · simp only [hω, ↓reduceIte, false_and, not_false_eq_true, true_and, false_or]
    rw [e]
    refine (hG.inter (MeasurableSet.biInter hDc fun q _ => ?_)).union
      (hG.compl.inter (MeasurableSet.const _))
    by_cases hq : q < c
    · simp only [hq, true_implies]
      exact hgood q
    · simp only [hq, false_implies]
      exact MeasurableSet.univ
  · have e : (fun ω => if ω ∈ G then exitTime K T (st ω) (ζ ω) else 0) ⁻¹' Ici c =
        Gᶜ ∩ {_ω | c ≤ 0} := by
      ext ω
      simp only [mem_preimage, mem_Ici, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
      by_cases hω : ω ∈ G
      · simp only [hω, ↓reduceIte, not_true_eq_false, false_and, iff_false]
        exact fun h => hcT (h.trans exitTime_le)
      · simp only [hω, ↓reduceIte, not_false_eq_true, true_and]
    rw [e]
    exact hG.compl.inter (MeasurableSet.const _)

open Classical in
/-- **The stopped path is measurable on the good set.** On `G` the path is continuous before its lifetime and its
exit from the closed set `K` happens before the lifetime. -/
theorem measurable_stopPath_piecewise (hK : IsClosed K) (hG : MeasurableSet G)
    (hkill : ∀ q : ℝ≥0, Measurable fun ω => if (q : ℝ≥0∞) < ζ ω then st ω q else x₀)
    (hζ : ∀ q : ℝ≥0, MeasurableSet {ω | (q : ℝ≥0∞) < ζ ω})
    (hgood : ∀ ω ∈ G, ContinuousOn (st ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      (exitTime K T (st ω) (ζ ω) : ℝ≥0∞) < ζ ω) :
    Measurable fun ω => if ω ∈ G then stopPath K T (st ω) (ζ ω) x₀ else ContinuousMap.const _ x₀ := by
  set τ : Ω → ℝ≥0 := fun ω => if ω ∈ G then exitTime K T (st ω) (ζ ω) else 0 with hτdef
  have hτm : Measurable τ := measurable_exitTime_piecewise hK hG hkill hζ fun ω hω => (hgood ω hω).1
  refine measurable_to_pathSpace _ fun t => ?_
  -- dyadic approximations of the exit time from below
  set k : ℕ → Ω → ℕ := fun n ω => ⌊(2 : ℝ≥0) ^ n * τ ω⌋₊ with hkdef
  have hkm : ∀ n, Measurable (k n) := fun n =>
    Nat.measurable_floor.comp (measurable_const.mul hτm)
  set qt : ℕ → ℕ → ℝ≥0 := fun n j => min (t : ℝ≥0) ((j : ℝ≥0) / 2 ^ n) with hqt
  set F : ℕ → Ω × ℕ → E := fun n p =>
    if (qt n p.2 : ℝ≥0∞) < ζ p.1 then st p.1 (qt n p.2) else x₀ with hFdef
  have hFm : ∀ n, Measurable (F n) := fun n =>
    measurable_from_prod_countable_left fun j => hkill (qt n j)
  set g : ℕ → Ω → E := fun n ω => if ω ∈ G then F n (ω, k n ω) else x₀ with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n =>
    Measurable.ite hG ((hFm n).comp (measurable_id.prodMk (hkm n))) measurable_const
  refine measurable_of_tendsto_metrizable hgm (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ G
  · have hτω : τ ω = exitTime K T (st ω) (ζ ω) := by simp only [hτdef, hω, ↓reduceIte]
    simp only [hgdef, hω, ↓reduceIte]
    rw [stopPath_apply (hgood ω hω), ← hτω]
    -- the dyadic times converge to `τ ω` from below
    have hle : ∀ n, ((k n ω : ℝ≥0) / 2 ^ n) ≤ τ ω := fun n => by
      rw [div_le_iff₀ (pow_pos two_pos n), mul_comm]
      exact Nat.floor_le zero_le
    have hlim : Tendsto (fun n => ((k n ω : ℝ≥0) / 2 ^ n)) atTop (𝓝 (τ ω)) := by
      rw [← NNReal.tendsto_coe]
      have hlow : ∀ n, (τ ω : ℝ) - (1 / 2) ^ n ≤ (((k n ω : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) := fun n => by
        have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
        have hfl' : (2 : ℝ≥0) ^ n * τ ω < (k n ω : ℝ≥0) + 1 := Nat.lt_floor_add_one _
        have hfl : (2 : ℝ) ^ n * τ ω < (k n ω : ℝ) + 1 := by exact_mod_cast hfl'
        rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_two]
        have h3 : (τ ω : ℝ) ≤ ((k n ω : ℝ) + 1) / 2 ^ n := by
          rw [le_div_iff₀ h2]
          linarith
        have h4 : ((k n ω : ℝ) + 1) / 2 ^ n = (k n ω : ℝ) / 2 ^ n + (1 / 2) ^ n := by
          rw [one_div_pow, add_div]
        linarith
      have hup : ∀ n, (((k n ω : ℝ≥0) / 2 ^ n : ℝ≥0) : ℝ) ≤ τ ω := fun n => by exact_mod_cast hle n
      have hl : Tendsto (fun n : ℕ => (τ ω : ℝ) - (1 / 2) ^ n) atTop (𝓝 (τ ω)) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1)).const_sub (τ ω : ℝ)
        rwa [sub_zero] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup
    have hlt : ∀ n, (qt n (k n ω) : ℝ≥0∞) < ζ ω := fun n => by
      have h1 : qt n (k n ω) ≤ exitTime K T (st ω) (ζ ω) := by
        rw [← hτω]
        exact (min_le_right _ _).trans (hle n)
      exact lt_of_le_of_lt (by exact_mod_cast h1) (hgood ω hω).2
    have hev : (fun n => F n (ω, k n ω)) = fun n => st ω (qt n (k n ω)) := by
      funext n
      simp only [hFdef, hlt n, ↓reduceIte]
    rw [hev]
    have hτζ : ((min (t : ℝ≥0) (τ ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by rw [hτω]; exact_mod_cast min_le_right _ _) (hgood ω hω).2
    exact ((continuousAt_of_lt (hgood ω hω).1 hτζ).tendsto).comp
      ((tendsto_const_nhds.min hlim))
  · simp only [hgdef, hω, ↓reduceIte, ContinuousMap.const_apply]
    exact tendsto_const_nhds

end Random

end DSReach

end Supp12

end InteractingSLE
