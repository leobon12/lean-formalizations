/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61ULocGlue

/-!
# Rule stops of the counterflow record and the flow record are enlarged stops

Packet PROVE-AUX61-UNIONLOC, item (P1) of `planning/handoffs/PROVE-AUX61-CHARTLOC.md`: the glued stop `t + T(r)` of
the restart (the flow time at which the restarted chart path reaches relative capacity `r`) is a function of the
counterflow record and of the flow path, and depends on the flow path only up to itself (Galmarino). Astra follow-up 4
§1.1: "An enlarged stopping decision is measurable from the retained pair at each grid time."

This file turns that deterministic property into the stop hypothesis of
`Aux61ULoc.isHistoryAvoidanceLocal_unionAt_cfGlueT`:

* `IsRecordStop stop`: a stopping operation on records (jointly measurable, `stop s ∘ stop t = stop s` for `s ≤ t`);
  `stopRec t = Sec4.stopHistory (fun _ => t)` on the killed-history space is one (`isRecordStop_stopRec`);
* `IsGalmarinoRule stop ρ`: a rule `ρ(y, g)` (other record `y`, own record `g`) whose value, when at most `t`, is read
  from the own record stopped at `t`;
* `ruleMarks stop ρ Y R`: the marks `σ(Y, R^T)` of the rule stop `T = ρ(Y, R)` (the other record and the own record
  stopped at `T`);
* **`isEnlargedStopComap_ruleMarks`**: a measurable Galmarino rule stop is a stop of the initially enlarged filtration
  `σ(Y) ∨ 𝓕_t` with the marks `σ(Y, R^T)`, in the pulled-back form `IsEnlargedStopComap`, whenever the own record
  stopped at every bounded stopping time `σ` is `𝓕_σ`-measurable; `measurableSet_ruleMarks_sup` (the marks are events of
  `σ(Y) ∨ 𝓕_∞`);
* `measurable_stopRec_killedHistory`: the killed history stopped at a bounded stopping time of the driving filtration is
  measurable for the stopped σ-algebra;
* **`isHistoryAvoidanceLocal_unionAt_rule_cfGlueT`** ((P1) with a rule stop): on the θ-glued space, for every measurable
  Galmarino rule `ρ` of (the counterflow record at `s`, the flow's killed history), the union `ℍ ∩ (K_s ∪ K̃_T)` at the
  rule stop `T` is history-marked local for the marks `σ(counterflow record at s, flow history stopped at T)`.

R48 / R77: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or
Astra's post-contact kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Aux61ULoc

/-! ### Rule stops -/

section Rule

variable {X Ω 𝒴 γ : Type*} [m𝒴 : MeasurableSpace 𝒴] [mγ : MeasurableSpace γ]

/-- **A stopping operation on records**: jointly measurable, and stopping at `t` then at `s ≤ t` is stopping at `s`. -/
structure IsRecordStop (stop : ℝ≥0 → γ → γ) : Prop where
  measurable : Measurable fun q : ℝ≥0 × γ => stop q.1 q.2
  stop_stop : ∀ (s t : ℝ≥0) (g : γ), s ≤ t → stop s (stop t g) = stop s g

/-- **A Galmarino rule**: whenever the rule read from the record stopped at `t`, or the rule read from the whole
record, is at most `t`, the two values agree (the rule only reads the record up to its own value). -/
def IsGalmarinoRule (stop : ℝ≥0 → γ → γ) (ρ : 𝒴 × γ → ℝ≥0∞) : Prop :=
  ∀ (y : 𝒴) (g : γ) (t : ℝ≥0), (ρ (y, stop t g) ≤ t ∨ ρ (y, g) ≤ t) → ρ (y, stop t g) = ρ (y, g)

/-- The record stopped at a possibly infinite time (the whole record at `⊤`). -/
def stopAt (stop : ℝ≥0 → γ → γ) (T : ℝ≥0∞) (g : γ) : γ := if T < ⊤ then stop T.toNNReal g else g

theorem measurable_stopAt {stop : ℝ≥0 → γ → γ} (hstop : IsRecordStop stop) :
    Measurable fun q : ℝ≥0∞ × γ => stopAt stop q.1 q.2 := by
  refine Measurable.ite (measurableSet_lt measurable_fst measurable_const) ?_ measurable_snd
  exact hstop.measurable.comp ((ENNReal.measurable_toNNReal.comp measurable_fst).prodMk measurable_snd)

/-- **The marks of a rule stop** `T = ρ(Y, R)`: the σ-algebra of the other record `Y` and the own record `R` stopped
at `T`. -/
@[instance_reducible]
def ruleMarks (stop : ℝ≥0 → γ → γ) (ρ : 𝒴 × γ → ℝ≥0∞) (Y : X → 𝒴) (R : X → γ) : MeasurableSpace X :=
  MeasurableSpace.comap (fun x => (Y x, stopAt stop (ρ (Y x, R x)) (R x))) inferInstance

/-- **A measurable Galmarino rule stop is an enlarged stop** (pulled back along `π`): if the own record `R` stopped at
every bounded `𝓕`-stopping time `σ` is `𝓕_σ`-measurable, then `T = ρ(Y, R ∘ π)` is a stop of `σ(Y) ∨ π⁻¹ 𝓕_t` with
the marks `σ(Y, (R ∘ π)^T)`. -/
theorem isEnlargedStopComap_ruleMarks {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {π : X → Ω} {R : Ω → γ}
    {Y : X → 𝒴} {stop : ℝ≥0 → γ → γ} (hstop : IsRecordStop stop) {ρ : 𝒴 × γ → ℝ≥0∞} (hρ : Measurable ρ)
    (hG : IsGalmarinoRule stop ρ)
    (hR : ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)),
      Measurable[hσ.measurableSpace] fun ω => stop (σ ω) (R ω)) :
    IsEnlargedStopComap (ruleMarks stop ρ Y fun x => R (π x)) (m𝒴.comap Y) 𝓕 π fun x => ρ (Y x, R (π x)) := by
  intro σ hσ M hM
  obtain ⟨C, hC, rfl⟩ := hM
  set 𝒮 : MeasurableSpace X := m𝒴.comap Y ⊔ hσ.measurableSpace.comap π with h𝒮
  -- the joint reading `(Y, σ ∘ π, R^σ ∘ π)`
  have hσm : Measurable[hσ.measurableSpace] σ := by
    refine measurable_of_Iic fun a => ?_
    have h := hσ.measurableSet_le' a
    simp only [WithTop.coe_le_coe] at h
    exact h
  have hΦ : Measurable[𝒮] fun x => (Y x, σ (π x), stop (σ (π x)) (R (π x))) := by
    refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
    · exact (comap_measurable Y).mono le_sup_left le_rfl
    · exact (hσm.comp (comap_measurable π)).mono le_sup_right le_rfl
    · exact ((hR σ hσ).comp (comap_measurable π)).mono le_sup_right le_rfl
  set D : Set (𝒴 × ℝ≥0 × γ) := {q | ρ (q.1, q.2.2) ≤ (q.2.1 : ℝ≥0∞) ∧
    (q.1, stopAt stop (ρ (q.1, q.2.2)) q.2.2) ∈ C} with hD
  have hρ' : Measurable fun q : 𝒴 × ℝ≥0 × γ => ρ (q.1, q.2.2) :=
    hρ.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hDm : MeasurableSet D := by
    refine (measurableSet_le hρ' (measurable_coe_nnreal_ennreal.comp (measurable_fst.comp measurable_snd))).inter ?_
    refine (measurable_fst.prodMk ((measurable_stopAt hstop).comp
      (hρ'.prodMk (measurable_snd.comp measurable_snd)))) hC
  have e : {x | ρ (Y x, R (π x)) ≤ (σ (π x) : ℝ≥0∞)} ∩
      (fun x => (Y x, stopAt stop (ρ (Y x, R (π x))) (R (π x)))) ⁻¹' C =
      (fun x => (Y x, σ (π x), stop (σ (π x)) (R (π x)))) ⁻¹' D := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, hD]
    set y := Y x
    set g := R (π x)
    set a := σ (π x)
    constructor
    · rintro ⟨hle, hmem⟩
      have heq : ρ (y, stop a g) = ρ (y, g) := hG y g a (Or.inr hle)
      have hlt : ρ (y, g) < ⊤ := hle.trans_lt ENNReal.coe_lt_top
      have hta : (ρ (y, g)).toNNReal ≤ a := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hlt.ne]
        exact hle
      refine ⟨by rw [heq]; exact hle, ?_⟩
      rw [heq]
      simp only [stopAt, hlt, ↓reduceIte] at hmem ⊢
      rw [hstop.stop_stop _ _ _ hta]
      exact hmem
    · rintro ⟨hle, hmem⟩
      have heq : ρ (y, stop a g) = ρ (y, g) := hG y g a (Or.inl hle)
      rw [heq] at hle hmem
      have hlt : ρ (y, g) < ⊤ := hle.trans_lt ENNReal.coe_lt_top
      have hta : (ρ (y, g)).toNNReal ≤ a := by
        rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hlt.ne]
        exact hle
      refine ⟨hle, ?_⟩
      simp only [stopAt, hlt, ↓reduceIte] at hmem ⊢
      rw [hstop.stop_stop _ _ _ hta] at hmem
      exact hmem
  rw [e]
  exact hΦ hDm

/-- **The marks of a rule stop are events of `σ(Y) ∨ π⁻¹ 𝓕_∞`** when the own record is `𝓕_∞`-measurable. -/
theorem measurableSet_ruleMarks_sup {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {π : X → Ω} {R : Ω → γ}
    {Y : X → 𝒴} {stop : ℝ≥0 → γ → γ} (hstop : IsRecordStop stop) {ρ : 𝒴 × γ → ℝ≥0∞} (hρ : Measurable ρ)
    (hR : Measurable[⨆ t, 𝓕 t] R) {M : Set X} (hM : MeasurableSet[ruleMarks stop ρ Y fun x => R (π x)] M) :
    MeasurableSet[m𝒴.comap Y ⊔ ⨆ r, (𝓕 r).comap π] M := by
  obtain ⟨C, hC, rfl⟩ := hM
  set 𝒮 : MeasurableSpace X := m𝒴.comap Y ⊔ ⨆ r, (𝓕 r).comap π with h𝒮
  have hRπ : Measurable[𝒮] fun x => R (π x) := by
    have h1 : Measurable[(⨆ t, 𝓕 t).comap π] fun x => R (π x) := hR.comp (comap_measurable π)
    refine h1.mono ?_ le_rfl
    rw [MeasurableSpace.comap_iSup]
    exact le_sup_right
  have hY : Measurable[𝒮] Y := (comap_measurable Y).mono le_sup_left le_rfl
  have hpair : Measurable[𝒮] fun x => (Y x, R (π x)) := hY.prodMk hRπ
  have hf : Measurable fun q : 𝒴 × γ => (q.1, stopAt stop (ρ q) q.2) :=
    measurable_fst.prodMk ((measurable_stopAt hstop).comp (hρ.prodMk measurable_snd))
  exact (hf.comp hpair) hC

end Rule

/-! ### The killed-history record -/

section Record

open LawUnique Sec4

variable {nL nR : ℕ}

/-- **The killed history stopped at a deterministic time** (`Sec4.stopHistory` at a constant stop). -/
def stopRec (t : ℝ≥0) (g : HistorySpace nL nR) : HistorySpace nL nR := stopHistory (fun _ => t) g

theorem isRecordStop_stopRec : IsRecordStop (stopRec (nL := nL) (nR := nR)) := by
  refine ⟨?_, fun s t g hst => ?_⟩
  · refine (measurable_coe_nnreal_ennreal.comp measurable_fst).prodMk (Measurable.of_eval fun p => ?_)
    exact Measurable.ite (measurableSet_le measurable_const measurable_fst)
      ((measurable_pi_apply p).comp (measurable_snd.comp measurable_snd)) measurable_const
  · simp only [stopRec, stopHistory]
    refine Prod.ext rfl (funext fun p => ?_)
    by_cases hp : dyadicTime p ≤ s
    · simp only [hp, hp.trans hst, ↓reduceIte]
    · simp only [hp, ↓reduceIte]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The killed history stopped at a bounded stopping time of the driving filtration is measurable for the stopped
σ-algebra** (the proof of `Sec4.measurable_stopHistory_killedHistory`, for an arbitrary stopping time). -/
theorem measurable_stopRec_killedHistory (hX : IsMeasurableKilledDriving W VL VR ζ) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) :
    Measurable[hσ.measurableSpace] fun ω => stopRec (σ ω) (killedHistory W VL VR ζ ω) := by
  have hσm : Measurable[hσ.measurableSpace] σ := by
    refine measurable_of_Iic fun a => ?_
    have h := hσ.measurableSet_le' a
    simp only [WithTop.coe_le_coe] at h
    exact h
  have hsample : ∀ p : ℕ × ℕ, ∀ B : Set (DrivingValue nL nR), MeasurableSet B →
      MeasurableSet[drivingFiltration P hX (dyadicTime p)]
        ((fun ω => (killedHistory W VL VR ζ ω).2 p) ⁻¹' B) := fun p B hB =>
    Ito.le_usualAugmentation (killedDrivingFiltration hX) P (dyadicTime p) _
      (measurable_killedSample hX p hB)
  have hpre : ∀ p : ℕ × ℕ, ∀ B : Set (DrivingValue nL nR),
      (fun ω => (stopRec (σ ω) (killedHistory W VL VR ζ ω)).2 p) ⁻¹' B =
        ({ω | (dyadicTime p : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0)} ∩
            (fun ω => (killedHistory W VL VR ζ ω).2 p) ⁻¹' B) ∪
          ({ω | dyadicTime p ≤ σ ω}ᶜ ∩ {_ω | (0 : DrivingValue nL nR) ∈ B}) := by
    intro p B
    ext ω
    simp only [stopRec, stopHistory, mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, mem_compl_iff,
      WithTop.coe_le_coe]
    by_cases h : dyadicTime p ≤ σ ω
    · simp only [h, ↓reduceIte]
      exact ⟨fun hb => Or.inl ⟨trivial, hb⟩, fun hh => hh.elim (fun h2 => h2.2) (fun h2 => absurd trivial h2.1)⟩
    · simp only [h, ↓reduceIte]
      exact ⟨fun hb => Or.inr ⟨not_false, hb⟩, fun hh => hh.elim (fun h2 => h2.1.elim) (fun h2 => h2.2)⟩
  have hsnd : ∀ p : ℕ × ℕ, Measurable[hσ.measurableSpace]
      fun ω => (stopRec (σ ω) (killedHistory W VL VR ζ ω)).2 p := by
    intro p B hB
    rw [hpre p B]
    exact (measurableSet_stopped_le_inter hσ (hsample p B hB)).union
      ((measurableSet_le measurable_const hσm).compl.inter (MeasurableSet.const _))
  let _ : MeasurableSpace Ω := hσ.measurableSpace
  exact (measurable_coe_nnreal_ennreal.comp hσm).prodMk (Measurable.of_eval hsnd)

/-- **The killed history is measurable for the terminal σ-algebra `⨆ t, 𝓕_t` of the driving filtration.** -/
theorem measurable_killedHistory_iSup (hX : IsMeasurableKilledDriving W VL VR ζ) :
    Measurable[⨆ t, drivingFiltration P hX t] (killedHistory W VL VR ζ) := by
  have hgen : ∀ q : ℝ≥0, MeasurableSet[⨆ t, drivingFiltration P hX t] {ω | (q : ℝ≥0∞) < ζ ω} := by
    intro q
    have h1 : MeasurableSet[killedDrivingFiltration hX q] {ω | (q : ℝ≥0∞) < ζ ω} := by
      refine MeasurableSpace.measurableSet_generateFrom ⟨q, le_rfl, univ, MeasurableSet.univ, ?_⟩
      ext ω
      simp only [mem_ofPred_eq, mem_univ, and_true]
    exact le_iSup (fun t => drivingFiltration P hX t) q _
      (Ito.le_usualAugmentation (killedDrivingFiltration hX) P q _ h1)
  have hζ : Measurable[⨆ t, drivingFiltration P hX t] ζ := by
    refine measurable_of_Ioi fun a => ?_
    by_cases ha : a = ⊤
    · have e : ζ ⁻¹' Ioi a = ∅ := by
        ext ω
        simp only [mem_preimage, mem_Ioi, ha, mem_empty_iff_false, iff_false, not_lt]
        exact le_top
      rw [e]
      exact @MeasurableSet.empty _ (⨆ t, drivingFiltration P hX t)
    · have e : ζ ⁻¹' Ioi a = ⋃ q : ℚ, ⋃ (_ : a < ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)),
          {ω | ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < ζ ω} := by
        ext ω
        simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq, exists_prop]
        constructor
        · intro h
          obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
          exact ⟨q, h1, h2⟩
        · rintro ⟨q, h1, h2⟩
          exact h1.trans h2
      rw [e]
      exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => hgen _
  have hsample : ∀ p : ℕ × ℕ, Measurable[⨆ t, drivingFiltration P hX t]
      fun ω => (killedHistory W VL VR ζ ω).2 p := fun p B hB =>
    le_iSup (fun t => drivingFiltration P hX t) (dyadicTime p) _
      (Ito.le_usualAugmentation (killedDrivingFiltration hX) P (dyadicTime p) _ (measurable_killedSample hX p hB))
  have hpi : Measurable[⨆ t, drivingFiltration P hX t] fun ω => (killedHistory W VL VR ζ ω).2 :=
    @measurable_pi_iff Ω (ℕ × ℕ) (fun _ => DrivingValue nL nR) (⨆ t, drivingFiltration P hX t) _ _ |>.2 hsample
  exact @Measurable.prodMk Ω (⨆ t, drivingFiltration P hX t) ℝ≥0∞ (ℕ × ℕ → DrivingValue nL nR) _ _ _ _ hζ hpi

end Record

/-! ### (P1) at a rule stop on the θ-glued space -/

section GlueRule

open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ WholeField LocalSets CrossCond.Theta Coupling
open Sec7.PocketStopWallsFin (regHull)

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
  {k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)} [IsMarkovKernel k] {u₀ : ℂ → ℝ}

/-- The counterflow record stopped at `s`, read on the glued space, generates `σ(cfStop s)`. -/
theorem comap_stopSigma_snd (s : ℝ≥0) :
    (stopSigma s).comap (Prod.snd : Ω × HistorySpace 0 0 → HistorySpace 0 0) =
      MeasurableSpace.comap (fun p : Ω × HistorySpace 0 0 => stopRec s p.2) inferInstance := by
  rw [stopSigma, MeasurableSpace.comap_comp]
  rfl

/-- **(P1) at a rule stop** (Astra follow-up 4 §1.1, L84–L104): on the θ-glued space, for every counterflow time `s` and
every measurable Galmarino rule `ρ` of (the counterflow record stopped at `s`, the flow's killed history), the union
`ℍ ∩ (K_s ∪ K̃_T)` of the counterflow hull `K_s` and the flow hull at the rule stop `T = ρ(cf record at s, flow
history)` (`ℍ` where `T = ∞`) satisfies the history-marked avoidance criterion for the marks
`σ(cf record at s, flow history stopped at T)` and the centred field `h − 𝔥₀`. The stop depends on BOTH records; neither
curve is assumed to be determined by the field. -/
theorem isHistoryAvoidanceLocal_unionAt_rule_cfGlueT
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀) (s : ℝ≥0)
    {ρ : HistorySpace 0 0 × HistorySpace nL nR → ℝ≥0∞} (hρ : Measurable ρ) (hG : IsGalmarinoRule stopRec ρ) :
    @IsHistoryAvoidanceLocal (Ω × HistorySpace 0 0)
      (ruleMarks stopRec ρ (fun p => stopRec s p.2) fun p => killedHistory W VL VR ζ p.1)
      Prod.instMeasurableSpace
      (unionAt (fun p => cfHullQ s p.2) (fun r p => regHull W ζ r p.1)
        fun p => ρ (stopRec s p.2, killedHistory W VL VR ζ p.1))
      (fun p => centredField h u₀ p.1)
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) := by
  have hX := hC.2.2.2.1
  have hT := isEnlargedStopComap_ruleMarks (𝓕 := drivingFiltration P hX) (π := Prod.fst)
    (R := killedHistory W VL VR ζ) (Y := fun p : Ω × HistorySpace 0 0 => stopRec s p.2) isRecordStop_stopRec hρ hG
    fun σ hσ => measurable_stopRec_killedHistory hX σ hσ
  have e := comap_stopSigma_snd (Ω := Ω) s
  refine isHistoryAvoidanceLocal_unionAt_cfGlueT hC hκ hζ hθb hcf hlaw hk hu₀ s _ _ (by rw [e]; exact hT)
    fun M hM => ?_
  rw [e]
  exact measurableSet_ruleMarks_sup isRecordStop_stopRec hρ (measurable_killedHistory_iSup hX) hM

end GlueRule

end InteractingSLE.Sec5.Aux61ULoc
