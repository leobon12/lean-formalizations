/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.LawUniqueHistory
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Frozen.Spec.drivingFiltration

/-!
# Aux. lemma 23 at coupling level: the driving history through a stopping rule

Packet PROVE-SEC4-A4, item (2), inputs (a) and (d) of `planning/handoffs/PROVE-SEC4-B3.md` (obstruction 1).
Specification Aux. lemma 23 (`source/spec/p097-144.md#aux-23`, p. 122): "Consider couplings … with their own stopped
driving histories retained as local marks. Fix a bounded own-filtration stopping rule `S < T_*` … Then every such
coupling has the same joint law of the entire field and the driving history through `S`." Proof: "The stopped driving
marginal is the same in the two couplings by uniqueness of the integrated SDE and the common stopping rule."

A stopping rule is a measurable functional `s` of the killed driving history (`LawUnique.killedHistory`: the lifetime
and the killed state at the dyadic times); in a coupling it gives the random time `S = s(history)`
(`ruleTime`), assumed to be a stopping time of the coupling's driving filtration. The **history through `S`**
(`stopHistory s`) records `S` and the killed state at the dyadic times `≤ S` (other samples are set to `0`).

* `measurable_stopHistory`: the history through `S` is a measurable function of the killed history;
* `measurable_stopHistory_killedHistory` (**input (a)**): it is measurable for the stopped σ-algebra `𝓕_S` of the
  frozen driving filtration (a sample at a dyadic time `d ≤ S` is `𝓕_d`-measurable and `{d ≤ S} ∩ E ∈ 𝓕_S` for
  `E ∈ 𝓕_d`);
* `map_stopHistory_eq` (**input (d)**): under Theorem 2.2's uniqueness in law (`LawUnique.KilledStateLawUnique`, the
  frozen `IsIntegratedSLEEvolution.measure_killedState_eq` for the word), two evolutions have the same law of the
  history through a common rule;
* `histPath`, `histVL`, `histVR`: the driver and the force coordinates read from a history (limits along left dyadic
  times); `histPath_stopHistory` / `histVL_stopHistory` / `histVR_stopHistory`: on a path continuous before its
  lifetime with `S < ζ` they are `W_{t ∧ S}`, `V^L_S`, `V^R_S`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec4

open LawUnique

variable {nL nR : ℕ}

/-! ### The history through a stopping rule -/

/-- The history through the stop `s(γ)`: the stop, and the killed samples at the dyadic times `≤ s(γ)` (the other
samples are set to `0`). -/
def stopHistory (s : HistorySpace nL nR → ℝ≥0) (γ : HistorySpace nL nR) : HistorySpace nL nR :=
  ((s γ : ℝ≥0∞), fun p => if dyadicTime p ≤ s γ then γ.2 p else 0)

theorem measurable_stopHistory {s : HistorySpace nL nR → ℝ≥0} (hs : Measurable s) :
    Measurable (stopHistory s) := by
  refine (measurable_coe_nnreal_ennreal.comp hs).prodMk (Measurable.of_eval fun p => ?_)
  exact Measurable.ite (measurableSet_le measurable_const hs)
    ((measurable_pi_apply p).comp measurable_snd) measurable_const

/-- The recorded stop of a history through `s`. -/
theorem stopHistory_fst (s : HistorySpace nL nR → ℝ≥0) (γ : HistorySpace nL nR) :
    (stopHistory s γ).1 = s γ := rfl

theorem stopHistory_snd_of_le {s : HistorySpace nL nR → ℝ≥0} {γ : HistorySpace nL nR}
    {p : ℕ × ℕ} (hp : dyadicTime p ≤ s γ) : (stopHistory s γ).2 p = γ.2 p := by
  simp only [stopHistory, hp, ↓reduceIte]

section Coupling

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The random time `S = s(killed history)` of a stopping rule `s` in a coupling, as a `WithTop ℝ≥0` time. -/
def ruleTime (s : HistorySpace nL nR → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Ω → WithTop ℝ≥0 :=
  fun ω => ((s (killedHistory W VL VR ζ ω) : ℝ≥0) : WithTop ℝ≥0)

omit mΩ in
theorem ruleTime_untopD (s : HistorySpace nL nR → ℝ≥0) (ω : Ω) :
    (ruleTime s W VL VR ζ ω).untopD 0 = s (killedHistory W VL VR ζ ω) := rfl

/-- The killed sample at a dyadic time `d` is measurable for the killed driving σ-algebra at `d`. -/
theorem measurable_killedSample (hX : IsMeasurableKilledDriving W VL VR ζ) (p : ℕ × ℕ) :
    Measurable[killedDrivingFiltration hX (dyadicTime p)]
      fun ω => (killedHistory W VL VR ζ ω).2 p := by
  intro S hS
  have hpre : (fun ω => (killedHistory W VL VR ζ ω).2 p) ⁻¹' S =
      {ω | (dyadicTime p : ℝ≥0∞) < ζ ω ∧ (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω),
          fun i => VR i (dyadicTime p) ω) ∈ S} ∪
        ({ω | (dyadicTime p : ℝ≥0∞) < ζ ω ∧ (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω),
          fun i => VR i (dyadicTime p) ω) ∈ univ}ᶜ ∩ {_ω | (0 : DrivingValue nL nR) ∈ S}) := by
    ext ω
    by_cases h : (dyadicTime p : ℝ≥0∞) < ζ ω <;> simp [killedHistory, h]
  rw [hpre]
  have h1 : MeasurableSet[killedDrivingFiltration hX (dyadicTime p)]
      {ω | (dyadicTime p : ℝ≥0∞) < ζ ω ∧ (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω),
          fun i => VR i (dyadicTime p) ω) ∈ S} :=
    MeasurableSpace.measurableSet_generateFrom ⟨dyadicTime p, le_rfl, S, hS, rfl⟩
  have h2 : MeasurableSet[killedDrivingFiltration hX (dyadicTime p)]
      {ω | (dyadicTime p : ℝ≥0∞) < ζ ω ∧ (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω),
          fun i => VR i (dyadicTime p) ω) ∈ univ} :=
    MeasurableSpace.measurableSet_generateFrom ⟨dyadicTime p, le_rfl, univ, MeasurableSet.univ, rfl⟩
  exact h1.union (h2.compl.inter (MeasurableSet.const _))

/-- `{d ≤ τ} ∩ E` is in the stopped σ-algebra of `τ` for `E ∈ 𝓕_d`. -/
theorem measurableSet_stopped_le_inter {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) {d : ℝ≥0} {E : Set Ω} (hE : MeasurableSet[𝓕 d] E) :
    MeasurableSet[hτ.measurableSpace] ({ω | (d : WithTop ℝ≥0) ≤ τ ω} ∩ E) := by
  have hd : MeasurableSet[𝓕 d] {ω | (d : WithTop ℝ≥0) ≤ τ ω} := by
    have : {ω | (d : WithTop ℝ≥0) ≤ τ ω} = {ω | τ ω < d}ᶜ := by
      ext ω
      show (d : WithTop ℝ≥0) ≤ τ ω ↔ ¬ τ ω < d
      exact not_lt.symm
    rw [this]
    exact (hτ.measurableSet_lt d).compl
  refine ⟨le_iSup (fun t => 𝓕 t) d _ (hd.inter hE), fun i => ?_⟩
  by_cases hdi : d ≤ i
  · exact (𝓕.mono hdi _ (hd.inter hE)).inter (hτ i)
  · have : ({ω | (d : WithTop ℝ≥0) ≤ τ ω} ∩ E) ∩ {ω | τ ω ≤ i} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro ω ⟨⟨h1, -⟩, h2⟩
      exact hdi (by exact_mod_cast (show (d : WithTop ℝ≥0) ≤ i from h1.trans h2))
    rw [this]
    exact @MeasurableSet.empty _ (𝓕 i)

/-- **Input (a): the history through the stopping rule is `𝓕_S`-measurable** for the stopped σ-algebra of the frozen
driving filtration. -/
theorem measurable_stopHistory_killedHistory {P : Measure Ω}
    (hX : IsMeasurableKilledDriving W VL VR ζ) {s : HistorySpace nL nR → ℝ≥0}
    (hS : IsStoppingTime (drivingFiltration P hX) (ruleTime s W VL VR ζ)) :
    Measurable[hS.measurableSpace] fun ω => stopHistory s (killedHistory W VL VR ζ ω) := by
  have hS'm : Measurable[hS.measurableSpace] fun ω => s (killedHistory W VL VR ζ ω) := by
    refine measurable_of_Iic fun a => ?_
    have h := hS.measurableSet_le' a
    have e : (fun ω => s (killedHistory W VL VR ζ ω)) ⁻¹' Iic a =
        {ω | ruleTime s W VL VR ζ ω ≤ a} := by
      ext ω
      simp only [mem_preimage, mem_Iic, mem_ofPred_eq, ruleTime, WithTop.coe_le_coe]
    rw [e]
    exact h
  have hsample : ∀ p : ℕ × ℕ, ∀ B : Set (DrivingValue nL nR), MeasurableSet B →
      MeasurableSet[drivingFiltration P hX (dyadicTime p)]
        ((fun ω => (killedHistory W VL VR ζ ω).2 p) ⁻¹' B) := fun p B hB =>
    Ito.le_usualAugmentation (killedDrivingFiltration hX) P (dyadicTime p) _
      (measurable_killedSample hX p hB)
  have hpre : ∀ p : ℕ × ℕ, ∀ B : Set (DrivingValue nL nR),
      (fun ω => (stopHistory s (killedHistory W VL VR ζ ω)).2 p) ⁻¹' B =
        ({ω | (dyadicTime p : WithTop ℝ≥0) ≤ ruleTime s W VL VR ζ ω} ∩
            (fun ω => (killedHistory W VL VR ζ ω).2 p) ⁻¹' B) ∪
          ({ω | dyadicTime p ≤ s (killedHistory W VL VR ζ ω)}ᶜ ∩
            {_ω | (0 : DrivingValue nL nR) ∈ B}) := by
    intro p B
    ext ω
    simp only [stopHistory, mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff]
    by_cases h : dyadicTime p ≤ s (killedHistory W VL VR ζ ω)
    · have h' : (dyadicTime p : WithTop ℝ≥0) ≤ ruleTime s W VL VR ζ ω := by
        simp only [ruleTime]; exact_mod_cast h
      simp only [h, ↓reduceIte]
      exact ⟨fun hb => Or.inl ⟨h', hb⟩,
        fun hh => hh.elim (fun h2 => h2.2) (fun h2 => absurd trivial h2.1)⟩
    · have h' : ¬ (dyadicTime p : WithTop ℝ≥0) ≤ ruleTime s W VL VR ζ ω := by
        simp only [ruleTime]; exact_mod_cast h
      simp only [h, ↓reduceIte]
      exact ⟨fun hb => Or.inr ⟨not_false, hb⟩,
        fun hh => hh.elim (fun h2 => absurd h2.1 h') (fun h2 => h2.2)⟩
  have hsnd : ∀ p : ℕ × ℕ, Measurable[hS.measurableSpace]
      fun ω => (stopHistory s (killedHistory W VL VR ζ ω)).2 p := by
    intro p B hB
    rw [hpre p B]
    exact (measurableSet_stopped_le_inter hS (hsample p B hB)).union
      ((measurableSet_le measurable_const hS'm).compl.inter (MeasurableSet.const _))
  let _ : MeasurableSpace Ω := hS.measurableSpace
  exact (measurable_coe_nnreal_ennreal.comp hS'm).prodMk (Measurable.of_eval hsnd)

end Coupling

/-! ### Input (d): the law of the history through a common rule -/

/-- **Input (d): the history through a common stopping rule has one law** in any two integrated `SLE_a(ρ)` evolutions
of the word, under Theorem 2.2's uniqueness in law (`KilledStateLawUnique`). -/
theorem map_stopHistory_eq {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hU : KilledStateLawUnique.{u, v} a xL xR ρL ρR)
    {s : HistorySpace nL nR → ℝ≥0} (hs : Measurable s)
    {Ω₁ : Type u} {m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {𝓕₁ : Filtration ℝ≥0 m₁} {W₁ : ℝ≥0 → Ω₁ → ℝ} {VL₁ : Fin nL → ℝ≥0 → Ω₁ → ℝ}
    {VR₁ : Fin nR → ℝ≥0 → Ω₁ → ℝ} {B₁ : ℝ≥0 → Ω₁ → ℝ} {ζ₁ : Ω₁ → ℝ≥0∞}
    (h₁ : IsIntegratedSLEEvolution a xL xR ρL ρR P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁)
    {Ω₂ : Type v} {m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {𝓕₂ : Filtration ℝ≥0 m₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ : Fin nL → ℝ≥0 → Ω₂ → ℝ}
    {VR₂ : Fin nR → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (h₂ : IsIntegratedSLEEvolution a xL xR ρL ρR P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂) :
    P₁.map (fun ω => stopHistory s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      P₂.map (fun ω => stopHistory s (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) := by
  have e₁ : (fun ω => stopHistory s (killedHistory W₁ VL₁ VR₁ ζ₁ ω)) =
      stopHistory s ∘ killedHistory W₁ VL₁ VR₁ ζ₁ := rfl
  have e₂ : (fun ω => stopHistory s (killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      stopHistory s ∘ killedHistory W₂ VL₂ VR₂ ζ₂ := rfl
  rw [e₁, e₂, ← Measure.map_map (measurable_stopHistory hs) (measurable_killedHistory hX₁),
    ← Measure.map_map (measurable_stopHistory hs) (measurable_killedHistory hX₂),
    map_killedHistory_eq hU h₁ hX₁ h₂ hX₂]

/-! ### Reading the driver and the force coordinates from a history -/

/-- The driver read from a history: the limit of the recorded driver at the left dyadic approximations of
`min t (recorded stop)`. -/
def histPath (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ :=
  limUnder atTop fun n => (γ.2 (lowerDyadic (min t γ.1.toNNReal) n)).1

/-- The left force coordinates at the recorded stop, read from a history. -/
def histVL (γ : HistorySpace nL nR) (i : Fin nL) : ℝ :=
  limUnder atTop fun n => (γ.2 (lowerDyadic γ.1.toNNReal n)).2.1 i

/-- The right force coordinates at the recorded stop, read from a history. -/
def histVR (γ : HistorySpace nL nR) (i : Fin nR) : ℝ :=
  limUnder atTop fun n => (γ.2 (lowerDyadic γ.1.toNNReal n)).2.2 i

section Read

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : HistorySpace nL nR → ℝ≥0} {ω : Ω}

theorem isOpen_lt_lifetime (a : ℝ≥0∞) : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < a} :=
  isOpen_Iio.preimage ENNReal.continuous_coe

/-- A function continuous before the lifetime is continuous at every time before it. -/
theorem continuousAt_of_lt_lifetime {f : ℝ≥0 → ℝ} {a : ℝ≥0∞}
    (hf : ContinuousOn f {t : ℝ≥0 | (t : ℝ≥0∞) < a}) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < a) :
    ContinuousAt f r :=
  hf.continuousAt ((isOpen_lt_lifetime a).mem_nhds hr)

/-- At a dyadic time `d ≤ S < ζ` the history through `S` records the state. -/
theorem stopHistory_killedHistory_snd {p : ℕ × ℕ}
    (hp : dyadicTime p ≤ s (killedHistory W VL VR ζ ω))
    (hlt : (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω) :
    (stopHistory s (killedHistory W VL VR ζ ω)).2 p =
      (W (dyadicTime p) ω, (fun i => VL i (dyadicTime p) ω), fun i => VR i (dyadicTime p) ω) := by
  rw [stopHistory_snd_of_le hp]
  have hd : (dyadicTime p : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hp) hlt
  simp only [killedHistory, hd, ↓reduceIte]

/-- **The driver read from the history through `S`** is `W_{t ∧ S}` on a path continuous before its lifetime, when
`S < ζ`. -/
theorem histPath_stopHistory (hlt : (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω)
    (hWc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω}) (t : ℝ≥0) :
    histPath (stopHistory s (killedHistory W VL VR ζ ω)) t =
      W (min t (s (killedHistory W VL VR ζ ω))) ω := by
  set S := s (killedHistory W VL VR ζ ω) with hSdef
  have hfst : (stopHistory s (killedHistory W VL VR ζ ω)).1.toNNReal = S := by
    rw [stopHistory_fst, ENNReal.toNNReal_coe]
  unfold histPath
  rw [hfst]
  set r := min t S with hr
  have hrS : r ≤ S := min_le_right _ _
  have hrζ : (r : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hrS) hlt
  refine Tendsto.limUnder_eq ?_
  have heq : (fun n => ((stopHistory s (killedHistory W VL VR ζ ω)).2 (lowerDyadic r n)).1) =
      fun n => W (dyadicTime (lowerDyadic r n)) ω := by
    funext n
    rw [stopHistory_killedHistory_snd ((dyadicTime_lowerDyadic_le r n).trans hrS) hlt]
  rw [heq]
  exact (continuousAt_of_lt_lifetime hWc hrζ).tendsto.comp (tendsto_dyadicTime_lowerDyadic r)

/-- **The left force coordinates read from the history through `S`** are `V^L_S`. -/
theorem histVL_stopHistory (hlt : (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω)
    (hVc : ∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) (i : Fin nL) :
    histVL (stopHistory s (killedHistory W VL VR ζ ω)) i =
      VL i (s (killedHistory W VL VR ζ ω)) ω := by
  have hfst : (stopHistory s (killedHistory W VL VR ζ ω)).1.toNNReal =
      s (killedHistory W VL VR ζ ω) := by
    rw [stopHistory_fst, ENNReal.toNNReal_coe]
  unfold histVL
  rw [hfst]
  refine Tendsto.limUnder_eq ?_
  have heq : (fun n => ((stopHistory s (killedHistory W VL VR ζ ω)).2
      (lowerDyadic (s (killedHistory W VL VR ζ ω)) n)).2.1 i) =
      fun n => VL i (dyadicTime (lowerDyadic (s (killedHistory W VL VR ζ ω)) n)) ω := by
    funext n
    rw [stopHistory_killedHistory_snd (dyadicTime_lowerDyadic_le _ n) hlt]
  rw [heq]
  exact (continuousAt_of_lt_lifetime (hVc i) hlt).tendsto.comp (tendsto_dyadicTime_lowerDyadic _)

/-- **The right force coordinates read from the history through `S`** are `V^R_S`. -/
theorem histVR_stopHistory (hlt : (s (killedHistory W VL VR ζ ω) : ℝ≥0∞) < ζ ω)
    (hVc : ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) (i : Fin nR) :
    histVR (stopHistory s (killedHistory W VL VR ζ ω)) i =
      VR i (s (killedHistory W VL VR ζ ω)) ω := by
  have hfst : (stopHistory s (killedHistory W VL VR ζ ω)).1.toNNReal =
      s (killedHistory W VL VR ζ ω) := by
    rw [stopHistory_fst, ENNReal.toNNReal_coe]
  unfold histVR
  rw [hfst]
  refine Tendsto.limUnder_eq ?_
  have heq : (fun n => ((stopHistory s (killedHistory W VL VR ζ ω)).2
      (lowerDyadic (s (killedHistory W VL VR ζ ω)) n)).2.2 i) =
      fun n => VR i (dyadicTime (lowerDyadic (s (killedHistory W VL VR ζ ω)) n)) ω := by
    funext n
    rw [stopHistory_killedHistory_snd (dyadicTime_lowerDyadic_le _ n) hlt]
  rw [heq]
  exact (continuousAt_of_lt_lifetime (hVc i) hlt).tendsto.comp (tendsto_dyadicTime_lowerDyadic _)

end Read

end Sec4

end InteractingSLE
