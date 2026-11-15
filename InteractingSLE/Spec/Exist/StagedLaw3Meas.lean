/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Cond

/-!
# The record is measurable for the announced history

Packet PROVE-STAGEDLAW3. The conditional law at the stop is computed given the announced history `𝓗 = ⋁ₙ 𝓓_{ρₙ}`
(`ae_condExp_cexp_stop`); the statement conditions on the record `R = recOf t E`. This file shows that, on the event
`{min t ζ < ∞}`, the record coincides almost surely with an `𝓗`-measurable record (`recVersion`):

* the samples are the limits of the samples of the stopped histories at `ρₙ` (continuity of the stopped driver on a good
  record), read through `𝓓_{ρₙ}`-measurable versions (`LocalExt.exists_measurable_stoppedHistory_version`);
* the stop is `⨆ₙ ρₙ = min t ζ` (almost surely, everywhere on `Ω`);
* the threshold flag `ζ ≤ t` is the event `∀ n, ρₙ < t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper Staged Restart LQGMetric

/-! ### The version -/

section Version

variable {Ω : Type*} {nL nR : ℕ}

open scoped Classical in
/-- **The version of the record read from the announced history.** -/
def recVersion (t : ℝ≥0∞) (ρ : ℕ → Ω → ℝ≥0) (K : ℕ → Ω → LocalExt.DrivingHist nL nR) (ω : Ω) : RecData :=
  (fun q => limsup (fun n => ((K n ω).2 q.toNNRat).1) atTop, ⨆ n, (ρ n ω : ℝ≥0∞),
    decide (∀ n, (ρ n ω : ℝ≥0∞) < t))

theorem measurable_recVersion [MeasurableSpace Ω] (t : ℝ≥0∞) {ρ : ℕ → Ω → ℝ≥0}
    {K : ℕ → Ω → LocalExt.DrivingHist nL nR} (hρ : ∀ n, Measurable (ρ n)) (hK : ∀ n, Measurable (K n)) :
    Measurable (recVersion t ρ K) := by
  classical
  have hρ' : ∀ n, Measurable fun ω => (ρ n ω : ℝ≥0∞) := fun n => measurable_coe_nnreal_ennreal.comp (hρ n)
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_) (Measurable.prodMk ?_ ?_)
  · exact Measurable.limsup fun n =>
      measurable_fst.comp ((measurable_pi_apply q.toNNRat).comp (measurable_snd.comp (hK n)))
  · exact Measurable.iSup hρ'
  · have hS : MeasurableSet {ω | ∀ n, (ρ n ω : ℝ≥0∞) < t} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun n => measurableSet_lt (hρ' n) measurable_const
    refine measurable_to_countable' fun b => ?_
    cases b
    · convert hS.compl using 1
      ext ω
      simp
    · convert hS using 1
      ext ω
      simp

end Version

theorem coe_toNNRat_eq (q : ℚ) : ((q.toNNRat : ℚ≥0) : ℝ≥0) = (q : ℝ).toNNReal := by
  ext
  rw [Real.coe_toNNReal']
  rw [show (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) from rfl]
  rw [show ((q.toNNRat : ℚ) : ℝ) = ((max q 0 : ℚ) : ℝ) from rfl, Rat.cast_max, Rat.cast_zero]

/-! ### The sup of the stops -/

theorem iSup_coe_stopSeq {σ : ℕ → ℝ≥0} {ζ t : ℝ≥0∞} (hlt : ∀ n, (σ n : ℝ≥0∞) < ζ)
    (hann : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ → ∃ n, s ≤ σ n) :
    (⨆ n, ((min t (σ n : ℝ≥0∞)).toNNReal : ℝ≥0∞)) = min t ζ := by
  have e : ∀ n, ((min t (σ n : ℝ≥0∞)).toNNReal : ℝ≥0∞) = min t (σ n : ℝ≥0∞) := fun n =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))
  simp only [e]
  have hsup : (⨆ n, (σ n : ℝ≥0∞)) = ζ := by
    refine le_antisymm (iSup_le fun n => (hlt n).le) (ENNReal.le_of_forall_nnreal_lt fun r hr => ?_)
    obtain ⟨n, hn⟩ := hann r hr
    exact (ENNReal.coe_le_coe.2 hn).trans (le_iSup (fun n => (σ n : ℝ≥0∞)) n)
  rw [← hsup]
  exact (inf_iSup_eq t _).symm

/-! ### The version is the record -/

section Ident

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q] {𝓕 : Filtration ℝ≥0 mΩ}
  {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}

/-- **On a good path, the version read from the announced history is the record.** -/
theorem recVersion_eq (t : ℝ≥0∞) {σ : ℕ → Ω → ℝ≥0}
    {K : ℕ → Ω → LocalExt.DrivingHist nL nR} {ω : Ω}
    (hg : IsGoodStopPath κ xL xR ρL ρR t (E ω) (fun i s => VL i s ω) (fun j s => VR j s ω) (fun s => B s ω))
    (hmono : Monotone fun n => σ n ω) (hlt : ∀ n, (σ n ω : ℝ≥0∞) < (E ω).2)
    (hann : ∀ s : ℝ≥0, (s : ℝ≥0∞) < (E ω).2 → ∃ n, s ≤ σ n ω)
    (hK : ∀ n, K n ω = Sec7.stoppedHistory (Sec7.completedState (fun s ω => (E ω).1 s) VL VR fun ω => (E ω).2)
      (fun ω => (stopSeq t σ n ω : WithTop ℝ≥0)) ω) :
    recVersion t (stopSeq t σ) K ω = recOf t (E ω) := by
  classical
  have hfin := hg.2.2.2.2.1
  obtain ⟨hle, hlim⟩ := tendsto_stopSeq (σ := fun n => σ n ω) hmono hlt hann hfin
  have hsζ : ∀ n, (stopSeq t σ n ω : ℝ≥0∞) < (E ω).2 := fun n =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (stopSeq_le t σ n ω)) (hlt n)
  set T := (min t (E ω).2).toNNReal with hTdef
  have hret : ∀ s : ℝ≥0, s ≤ T → (retOf t (E ω)).1 s = (E ω).1 s := by
    intro s hs
    change (E ω).1 (min (s : ℝ≥0∞) (min t (E ω).2)).toNNReal = _
    rw [min_eq_left (by rw [← ENNReal.coe_toNNReal hfin]; exact_mod_cast hs), ENNReal.toNNReal_coe]
  refine Prod.ext (funext fun q => ?_) (Prod.ext ?_ ?_)
  · -- the samples
    change limsup (fun n => ((K n ω).2 q.toNNRat).1) atTop = (retOf t (E ω)).1 (q : ℝ).toNNReal
    have hsamp : ∀ n, ((K n ω).2 q.toNNRat).1 =
        (retOf t (E ω)).1 (min ((q.toNNRat : ℚ≥0) : ℝ≥0) (stopSeq t σ n ω)) := by
      intro n
      rw [hK n]
      simp only [Sec7.stoppedHistory, Sec7.stopAt, WithTop.untopD_coe]
      have hlt' : ((min ((q.toNNRat : ℚ≥0) : ℝ≥0) (stopSeq t σ n ω) : ℝ≥0) : ℝ≥0∞) < (E ω).2 :=
        lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hsζ n)
      simp only [Sec7.completedState, hlt', ↓reduceIte, Sec7.drivingState]
      rw [hret (min ((q.toNNRat : ℚ≥0) : ℝ≥0) (stopSeq t σ n ω)) ((min_le_right _ _).trans (hle n))]
    simp only [hsamp]
    have hc : Tendsto (fun n => (retOf t (E ω)).1 (min ((q.toNNRat : ℚ≥0) : ℝ≥0) (stopSeq t σ n ω))) atTop
        (𝓝 ((retOf t (E ω)).1 (min ((q.toNNRat : ℚ≥0) : ℝ≥0) T))) :=
      ((continuous_retOf hg.2.2.1 hg.2.2.2.1).tendsto _).comp
        ((continuous_const.min continuous_id).tendsto _ |>.comp hlim)
    rw [hc.limsup_eq, ← retOf_eq_min hfin, coe_toNNRat_eq]
  · -- the stop
    exact iSup_coe_stopSeq hlt hann
  · -- the threshold flag
    change decide (∀ n, (stopSeq t σ n ω : ℝ≥0∞) < t) = decide ((E ω).2 ≤ t)
    refine decide_eq_decide.2 ⟨fun h => ?_, fun h n => ?_⟩
    · by_contra hζt
      push Not at hζt
      have htfin : t ≠ ⊤ := ne_top_of_lt hζt
      obtain ⟨n, hn⟩ := hann t.toNNReal (by rw [ENNReal.coe_toNNReal htfin]; exact hζt)
      have h1 := h n
      have h2 : stopSeq t σ n ω = t.toNNReal := by
        unfold stopSeq
        rw [min_eq_left (by rw [← ENNReal.coe_toNNReal htfin]; exact_mod_cast hn)]
      rw [h2, ENNReal.coe_toNNReal htfin] at h1
      exact lt_irrefl _ h1
    · exact lt_of_lt_of_le (hsζ n) h

end Ident

end StagedLaw

end Exist

end InteractingSLE
