/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField8Path
import InteractingSLE.Spec.Coupling.WholeField7Birth

/-!
# The killed history of a capped path through its first entrance is read off the stopped driving histories

Packet PROVE-WHOLEFIELD8. Setting: a right-continuous filtration `𝓕` (the driving filtration), a lifetime `ζ` and a
driving process `W` adapted before `ζ`, a nondecreasing sequence of stops `σₙ` announcing `ζ`, an open `U ⊆ ℍ`, a cap
`m`, and a path `ηc` (the capped flow line), continuous for every `ω`, which almost surely starts outside `U`, is
constant after `ζ ∧ m`, and agrees before the lifetime and the cap with the trace values `traceVal W ζ x`.

* `isStoppingTime_capStop`, `isStoppingTime_seqStop`: the rational entrance `R` of the trace values before `ζ`,
  capped at `m`, and the stops `τₙ = R ∧ m ∧ σₙ` are stopping times;
* **`ae_notMem_of_le_seqStop`**: almost surely the path avoids `U` up to every `τₙ`;
* **`measurable_aeSigma_khist`**: the killed history `(T^U, ηc|_{[0,T^U]}, lifeRec(cutLife ζ m, T^U))` of the path
  through its first entrance time `T^U` is measurable for the events almost surely equal to events of `⋁ₙ 𝓕_{τₙ}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open Sec6 Restart LocalSets

section Hist

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {x : ℝ} {U : Set ℂ} {m : ℝ≥0} {σ : ℕ → Ω → ℝ≥0}

/-- The rational entrance time of the trace values before the lifetime. -/
def entR (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (U : Set ℂ) (ω : Ω) : ℝ≥0∞ :=
  ratEntrance U (fun s => traceVal W ζ x s ω) (ζ ω)

/-- The stops `τₙ = R ∧ m ∧ σₙ`. -/
def tauN (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (U : Set ℂ) (m : ℝ≥0) (σ : ℕ → Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    ℝ≥0 :=
  seqStop (entR W ζ x U ω) m (fun k => σ k ω) n

theorem isStoppingTime_capStop (hW : AdaptedBefore 𝓕 ζ W) (hU : MeasurableSet U) :
    IsStoppingTime 𝓕 fun ω => (capStop (entR W ζ x U ω) m : WithTop ℝ≥0) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
  have e : {ω | (capStop (entR W ζ x U ω) m : WithTop ℝ≥0) < (t : WithTop ℝ≥0)} =
      (⋃ q : ℚ≥0, if (q : ℝ≥0) < t then {ω | ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ traceVal W ζ x q ω ∈ U} else ∅) ∪
        (if m < t then univ else ∅) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion]
    rw [WithTop.coe_lt_coe, ← ENNReal.coe_lt_coe, coe_capStop, min_lt_iff, entR, ratEntrance_lt_iff,
      ENNReal.coe_lt_coe]
    constructor
    · rintro (⟨q, hq1, hq2, hq3⟩ | hm)
      · exact Or.inl ⟨q, by rw [ite_eq_left (ENNReal.coe_lt_coe.1 hq3)]; exact ⟨hq1, hq2⟩⟩
      · exact Or.inr (by rw [ite_eq_left hm]; trivial)
    · rintro (⟨q, hq⟩ | hm)
      · by_cases hqt : (q : ℝ≥0) < t
        · rw [ite_eq_left hqt] at hq
          exact Or.inl ⟨q, hq.1, hq.2, ENNReal.coe_lt_coe.2 hqt⟩
        · rw [ite_eq_right hqt] at hq; exact absurd hq (notMem_empty _)
      · by_cases hmt : m < t
        · exact Or.inr hmt
        · rw [ite_eq_right hmt] at hm; exact absurd hm (notMem_empty _)
  rw [e]
  refine MeasurableSet.union (MeasurableSet.iUnion fun q => ?_) ?_
  · split_ifs with hqt
    · have h1 : MeasurableSet[𝓕 q] {ω | ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ traceVal W ζ x q ω ∈ U} := by
        have e2 : {ω | ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ traceVal W ζ x q ω ∈ U} =
            {ω | ((q : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ W q ω ∈ univ} ∩ (traceVal W ζ x q) ⁻¹' U := by
          ext ω; simp
        rw [e2]
        exact (hW q univ MeasurableSet.univ).inter (measurable_traceVal hW x q hU)
      exact 𝓕.mono hqt.le _ h1
    · exact @MeasurableSet.empty _ (𝓕 t)
  · split_ifs
    · exact @MeasurableSet.univ _ (𝓕 t)
    · exact @MeasurableSet.empty _ (𝓕 t)

theorem isStoppingTime_tauN (hW : AdaptedBefore 𝓕 ζ W) (hU : MeasurableSet U)
    (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0)) (n : ℕ) :
    IsStoppingTime 𝓕 fun ω => (tauN W ζ x U m σ n ω : WithTop ℝ≥0) :=
  isStoppingTime_coe_min (isStoppingTime_capStop hW hU) (hσ n)

/-- The supremum `c̃ = sup τₙ`. -/
def supT (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (U : Set ℂ) (m : ℝ≥0) (σ : ℕ → Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  supStop (entR W ζ x U ω) m (fun k => σ k ω)

open scoped Classical in
/-- The trace value at `s`, kept on `{∃ n, s ≤ τₙ}`. -/
def keptVal (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (U : Set ℂ) (m : ℝ≥0) (σ : ℕ → Ω → ℝ≥0) (s : ℝ≥0)
    (ω : Ω) : ℂ :=
  if ∃ n, s ≤ tauN W ζ x U m σ n ω then traceVal W ζ x s ω else 0

/-- The endpoint value: the limit of the kept values at the dyadic times below `c̃`. -/
def endVal' (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (U : Set ℂ) (m : ℝ≥0) (σ : ℕ → Ω → ℝ≥0) (ω : Ω) : ℂ :=
  limUnder atTop fun k => keptVal W ζ x U m σ (LP.dyadicBelow k (supT W ζ x U m σ ω)) ω

open scoped Classical in
/-- **The version of the killed history read from the stops.** -/
def khistV (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (x : ℝ) (U : Set ℂ) (m : ℝ≥0) (σ : ℕ → Ω → ℝ≥0) (ω : Ω) : KHist :=
  ((if IsEntered (entR W ζ x U ω) m (fun k => σ k ω) then (supT W ζ x U m σ ω : ℝ≥0∞) else ⊤,
    fun q => if IsEntered (entR W ζ x U ω) m (fun k => σ k ω) then
        (if (q : ℝ≥0) ≤ supT W ζ x U m σ ω then keptVal W ζ x U m σ q ω else 0)
      else (if ∃ n, (q : ℝ≥0) ≤ tauN W ζ x U m σ n ω then keptVal W ζ x U m σ q ω
        else endVal' W ζ x U m σ ω)),
    if IsEntered (entR W ζ x U ω) m (fun k => σ k ω) then ⊤
    else if ∃ n, m ≤ tauN W ζ x U m σ n ω then ⊤ else (supT W ζ x U m σ ω : ℝ≥0∞))

/-! ### The version is an observable of the join of the stopped σ-algebras -/

section Meas

variable (hW : AdaptedBefore 𝓕 ζ W) (hU : MeasurableSet U)
  (hσ : ∀ n, IsStoppingTime 𝓕 fun ω => (σ n ω : WithTop ℝ≥0)) (hσm : ∀ ω, Monotone fun n => σ n ω)

include hσm in
theorem monotone_tauN (ω : Ω) : Monotone fun n => tauN W ζ x U m σ n ω :=
  monotone_seqStop (σ := fun k => σ k ω) (hσm ω)

include hW hU in
theorem measurable_tauN (n : ℕ) :
    Measurable[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace] (tauN W ζ x U m σ n) := by
  refine measurable_of_Ici fun s => ?_
  have h := measurableSet_le_inter (isStoppingTime_tauN (x := x) (m := m) hW hU hσ n) (s := s)
    (@MeasurableSet.univ _ (𝓕 s))
  rw [inter_univ] at h
  exact (le_iSup (fun k => (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace) n) _ h

include hW hU in
theorem measurable_supT :
    Measurable[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace] (supT W ζ x U m σ) :=
  Measurable.iSup fun n => measurable_tauN hW hU hσ n

include hW hU in
theorem measurableSet_isEntered :
    MeasurableSet[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace]
      {ω | IsEntered (entR W ζ x U ω) m (fun k => σ k ω)} := by
  have hs := measurable_supT (x := x) (m := m) hW hU hσ
  have e : {ω | IsEntered (entR W ζ x U ω) m (fun k => σ k ω)} =
      {ω | supT W ζ x U m σ ω < m} ∩ ⋃ n, {ω | supT W ζ x U m σ ω ≤ tauN W ζ x U m σ n ω} := by
    ext ω; simp [IsEntered, supT, tauN]
  rw [e]
  exact (measurableSet_lt hs measurable_const).inter
    (MeasurableSet.iUnion fun n => measurableSet_le hs (measurable_tauN hW hU hσ n))

include hW hU hσm in
theorem measurable_keptVal (s : ℝ≥0) :
    Measurable[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace]
      (keptVal W ζ x U m σ s) :=
  measurable_ite_exists_le (isStoppingTime_tauN hW hU hσ) (monotone_tauN hσm) (measurable_traceVal hW x s)

omit [𝓕.IsRightContinuous] in
theorem measurable_comp_nat {m' : MeasurableSpace Ω} {F : ℕ → Ω → ℂ} (hF : ∀ j, Measurable[m'] (F j))
    {J : Ω → ℕ} (hJ : Measurable[m'] J) : Measurable[m'] fun ω => F (J ω) ω := by
  intro B hB
  have e : (fun ω => F (J ω) ω) ⁻¹' B = ⋃ j, (J ⁻¹' {j} ∩ F j ⁻¹' B) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨J ω, rfl, h⟩, fun ⟨j, hj, h⟩ => hj ▸ h⟩
  rw [e]
  exact MeasurableSet.iUnion fun j => (hJ (measurableSet_singleton j)).inter (hF j hB)

include hW hU hσm in
theorem measurable_endVal' :
    Measurable[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace]
      (endVal' W ζ x U m σ) := by
  have hk : ∀ k : ℕ, Measurable[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace]
      fun ω => keptVal W ζ x U m σ (LP.dyadicBelow k (supT W ζ x U m σ ω)) ω := fun k =>
    measurable_comp_nat (F := fun j ω => keptVal W ζ x U m σ ((j : ℝ≥0) / 2 ^ k) ω)
      (fun j => measurable_keptVal hW hU hσ hσm _)
      ((LP.measurable_dyadicIdx k).comp (measurable_supT hW hU hσ))
  exact (@StronglyMeasurable.limUnder ℕ Ω ℂ
    (⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace) _ _ atTop _ _ _ _
    fun k => (hk k).stronglyMeasurable).measurable

include hW hU hσm in
/-- **The version of the killed history is an observable of `⋁ₙ 𝓕_{τₙ}`.** -/
theorem measurable_khistV :
    Measurable[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace]
      (khistV W ζ x U m σ) := by
  classical
  have hs := measurable_supT (x := x) (m := m) hW hU hσ
  have hE := measurableSet_isEntered (x := x) (m := m) hW hU hσ
  have hex : ∀ s : ℝ≥0, MeasurableSet[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace]
      {ω | ∃ n, s ≤ tauN W ζ x U m σ n ω} := fun s =>
    measurableSet_exists_le (isStoppingTime_tauN hW hU hσ) s
  have hsc : Measurable[⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace]
      fun ω => (supT W ζ x U m σ ω : ℝ≥0∞) := measurable_coe_nnreal_ennreal.comp hs
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · exact Measurable.ite hE hsc measurable_const
  · refine @Measurable.of_eval Ω ℚ≥0 (fun _ => ℂ)
      (⨆ k, (isStoppingTime_tauN (x := x) (m := m) hW hU hσ k).measurableSpace) _ _ fun q => ?_
    refine Measurable.ite hE (Measurable.ite (measurableSet_le measurable_const hs)
      (measurable_keptVal hW hU hσ hσm _) measurable_const) ?_
    exact Measurable.ite (hex q) (measurable_keptVal hW hU hσ hσm _) (measurable_endVal' hW hU hσ hσm)
  · exact Measurable.ite hE measurable_const (Measurable.ite (hex m) measurable_const hsc)

end Meas

/-! ### On the good event the killed history is its version -/

section Path

variable {ηc : Ω → ℝ≥0 → ℂ} {ω : Ω}

omit [𝓕.IsRightContinuous] in
/-- **The first entrance of the capped path through the trace values.** -/
theorem firstEntrance_eq_entR (hU : IsOpen U) (hc : Continuous (ηc ω)) (g3 : ηc ω 0 ∉ U)
    (g4 : ∀ t, ηc ω t = ηc ω (min t (min (ζ ω) m).toNNReal))
    (g5 : ∀ s : ℝ≥0, s ≤ m → (s : ℝ≥0∞) < ζ ω → traceVal W ζ x s ω = ηc ω s) :
    firstEntrance U (pathCoord (ηc ω)) =
      if entR W ζ x U ω < m then entR W ζ x U ω else ⊤ := by
  have hcc : (((min (ζ ω) m).toNNReal : ℝ≥0) : ℝ≥0∞) = min (ζ ω) m :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  refine firstEntrance_eq_ratEntrance hU hc g3 g4 hcc fun s hs => ?_
  have h1 : (s : ℝ≥0∞) < min (ζ ω) m := hcc ▸ ENNReal.coe_lt_coe.2 hs
  exact g5 s (ENNReal.coe_le_coe.1 (lt_of_lt_of_le h1 (min_le_right _ _)).le) (lt_of_lt_of_le h1 (min_le_left _ _))

omit [𝓕.IsRightContinuous] in
/-- **The capped path avoids `U` up to every `τₙ`.** -/
theorem notMem_of_le_tauN (hU : IsOpen U) (hc : Continuous (ηc ω)) (g3 : ηc ω 0 ∉ U)
    (g4 : ∀ t, ηc ω t = ηc ω (min t (min (ζ ω) m).toNNReal))
    (g5 : ∀ s : ℝ≥0, s ≤ m → (s : ℝ≥0∞) < ζ ω → traceVal W ζ x s ω = ηc ω s) (n : ℕ) {t : ℝ≥0}
    (ht : t ≤ tauN W ζ x U m σ n ω) : ηc ω t ∉ U := by
  refine notMem_of_le_firstEntrance hU hc g3 ?_
  rw [firstEntrance_eq_entR hU hc g3 g4 g5]
  split_ifs
  · exact (ENNReal.coe_le_coe.2 ht).trans (coe_seqStop_le_R n)
  · exact le_top

omit [𝓕.IsRightContinuous] in
open scoped Classical in
/-- **On the good event the killed history through the first entrance is its version `khistV`.** -/
theorem khist_eq_khistV (hU : IsOpen U) (hc : Continuous (ηc ω))
    (g1 : ∀ n, (σ n ω : ℝ≥0∞) < ζ ω) (g2 : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ σ n ω)
    (g3 : ηc ω 0 ∉ U) (g4 : ∀ t, ηc ω t = ηc ω (min t (min (ζ ω) m).toNNReal))
    (g5 : ∀ s : ℝ≥0, s ≤ m → (s : ℝ≥0∞) < ζ ω → traceVal W ζ x s ω = ηc ω s) :
    khistOf (pathCoord (ηc ω)) (cutLife (ζ ω) m) (firstEntrance U (pathCoord (ηc ω))) =
      khistV W ζ x U m σ ω := by
  have hT := firstEntrance_eq_entR hU hc g3 g4 g5
  have hRζ : entR W ζ x U ω < ⊤ → entR W ζ x U ω < ζ ω := ratEntrance_lt_of_lt_top
  have hiff := isEntered_iff (R := entR W ζ x U ω) (m := m) (σ := fun k => σ k ω) g1 g2 hRζ
  have hsupm : supT W ζ x U m σ ω ≤ m := supStop_le_m
  unfold khistOf histOf khistV
  by_cases hE : IsEntered (entR W ζ x U ω) m (fun k => σ k ω)
  · have hRm := hiff.1 hE
    have hsup : (supT W ζ x U m σ ω : ℝ≥0∞) = entR W ζ x U ω := supStop_eq_of_isEntered g1 g2 hRζ hE
    have hRz : entR W ζ x U ω < ζ ω := hRζ (lt_of_lt_of_le hRm le_top)
    rw [hT, ite_eq_left hRm]
    simp only [hE, ↓reduceIte]
    refine Prod.ext (Prod.ext hsup.symm (funext fun q => ?_)) ?_
    · simp only [stopCoord, pathCoord]
      rw [← hsup]
      by_cases hq : (q : ℝ≥0) ≤ supT W ζ x U m σ ω
      · rw [ite_eq_left (ENNReal.coe_le_coe.2 hq), ite_eq_left hq]
        obtain ⟨n, hn⟩ := hE.2
        have hqn : (q : ℝ≥0) ≤ tauN W ζ x U m σ n ω := hq.trans hn
        rw [keptVal, ite_eq_left ⟨n, hqn⟩]
        refine (g5 _ (hq.trans hsupm) ?_).symm
        exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 hq) (hsup ▸ hRz)
      · rw [ite_eq_right (fun h => hq (ENNReal.coe_le_coe.1 h)), ite_eq_right hq]
    · have hnot : ¬ cutLife (ζ ω) m ≤ entR W ζ x U ω := by
        unfold cutLife
        split_ifs
        · exact not_le.2 hRz
        · exact not_le.2 (lt_of_lt_of_le hRm le_top)
      simp only [lifeRec, hnot, ↓reduceIte]
  · have hR : ¬ entR W ζ x U ω < m := fun h => hE (hiff.2 h)
    have hsup : (supT W ζ x U m σ ω : ℝ≥0∞) = min (ζ ω) m := supStop_eq_of_not_isEntered g1 g2 hRζ hE
    rw [hT, ite_eq_right hR]
    simp only [hE, ↓reduceIte]
    refine Prod.ext (Prod.ext rfl (funext fun q => ?_)) ?_
    · simp only [stopCoord, pathCoord, le_top, ↓reduceIte]
      by_cases hq : ∃ n, (q : ℝ≥0) ≤ tauN W ζ x U m σ n ω
      · rw [ite_eq_left hq, keptVal, ite_eq_left hq]
        obtain ⟨n, hn⟩ := hq
        refine (g5 _ (hn.trans (seqStop_le_m n)) ?_).symm
        exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hn.trans (seqStop_le_σ n))) (g1 n)
      · rw [ite_eq_right hq]
        push Not at hq
        have hsq : supT W ζ x U m σ ω ≤ q := ciSup_le fun n => (hq n).le
        have hcs : (min (ζ ω) m).toNNReal = supT W ζ x U m σ ω := by
          rw [← hsup, ENNReal.toNNReal_coe]
        have hγq : ηc ω q = ηc ω (supT W ζ x U m σ ω) := by
          rw [g4 q, hcs, min_eq_right hsq]
        have hsζ : (supT W ζ x U m σ ω : ℝ≥0∞) ≤ ζ ω := hsup ▸ min_le_left _ _
        have hkept : ∀ s : ℝ≥0, s < supT W ζ x U m σ ω → keptVal W ζ x U m σ s ω = ηc ω s := by
          intro s hs
          obtain ⟨n, hn⟩ := exists_le_seqStop_of_lt hs
          rw [keptVal, ite_eq_left ⟨n, hn⟩]
          exact g5 s (hs.le.trans hsupm) (lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hs) hsζ)
        have htend : Tendsto (fun k => keptVal W ζ x U m σ (LP.dyadicBelow k (supT W ζ x U m σ ω)) ω)
            atTop (𝓝 (ηc ω (supT W ζ x U m σ ω))) := by
          rcases eq_or_ne (supT W ζ x U m σ ω) 0 with h0 | h0
          · have hd : ∀ k, LP.dyadicBelow k (supT W ζ x U m σ ω) = 0 := fun k => by
              rw [h0]; simp [LP.dyadicBelow, LP.dyadicIdx]
            have hk0 : keptVal W ζ x U m σ 0 ω = ηc ω 0 := by
              rw [keptVal, ite_eq_left ⟨0, zero_le⟩]
              exact g5 0 zero_le (lt_of_le_of_lt bot_le (g1 0))
            have hfun : (fun k => keptVal W ζ x U m σ (LP.dyadicBelow k (supT W ζ x U m σ ω)) ω) =
                fun _ => ηc ω 0 := funext fun k => by rw [hd k, hk0]
            rw [hfun, h0]
            exact tendsto_const_nhds
          · have hpos : 0 < supT W ζ x U m σ ω := pos_iff_ne_zero.2 h0
            refine ((hc.tendsto _).comp (LP.tendsto_dyadicBelow _)).congr fun k => ?_
            exact (hkept _ (LP.dyadicBelow_lt hpos k)).symm
        rw [endVal', htend.limUnder_eq, hγq]
    · have hmiff : (∃ n, m ≤ tauN W ζ x U m σ n ω) ↔ (m : ℝ≥0∞) < ζ ω :=
        exists_m_le_seqStop_iff (R := entR W ζ x U ω) (m := m) (σ := fun k => σ k ω) g1 g2 hRζ hE
      simp only [lifeRec, le_top, ↓reduceIte]
      unfold cutLife
      by_cases hmζ : (m : ℝ≥0∞) < ζ ω
      · rw [ite_eq_right (not_le.2 hmζ), ite_eq_left (hmiff.2 hmζ)]
      · have hζm : ζ ω ≤ m := not_lt.1 hmζ
        rw [ite_eq_left hζm, ite_eq_right (fun h => hmζ (hmiff.1 h)), hsup, min_eq_left hζm]

end Path

end Hist

end WholeField

end InteractingSLE
