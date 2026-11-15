/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkMart9Region

/-!
# Local first-mark good events and the existing spatial stopping times

The numerical `rHit` and `rLoc` constructions are reused unchanged. Their
stopping-time proofs require local adaptedness and continuity, not maximality.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Mart9

open Zhan.Retarget

/-- Local solution paths, Brownian regularity, and source exhaustion before separation. -/
structure IsGood {Ω : Type*} (κ a b : ℝ) (xL ρL : Fin 0 → ℝ) (ρR : Fin 2 → ℝ)
    (W B : ℝ≥0 → Ω → ℝ) (VL : Fin 0 → ℝ≥0 → Ω → ℝ) (VR : Fin 2 → ℝ≥0 → Ω → ℝ)
    (e : Ω → ℝ≥0∞) (S : ℕ → Ω → ℝ≥0) (ω : Ω) : Prop where
  path : Sec2.IsSLEPathUpTo κ xL ![a, b] ρL ρR (W · ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (e ω)
  contB : Continuous (B · ω)
  zeroB : B 0 ω = 0
  before : ∀ n, (S n ω : ℝ≥0∞) < sepTime (W · ω) (VR 0 · ω) (e ω)
  cofinal : ∀ t : ℝ≥0, (t : ℝ≥0∞) < sepTime (W · ω) (VR 0 · ω) (e ω) → ∃ n, t ≤ S n ω

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}

/-- A measurable conull good event from an announced local evolution. -/
theorem exists_good (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hS : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
      (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) S) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧
      ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω := by
  have hae : ∀ᵐ ω ∂P, IsGood κ a b xL ρL ρR W B VL VR e S ω := by
    filter_upwards [hE.ae_path, hE.brownian.1.cont, hE.brownian.1.eval_zero_ae_eq_zero,
      ae_all_iff.2 hS.2.2.1, hS.2.2.2] with ω hp hBc hB0 hb hc
    exact ⟨hp, hBc, hB0, hb, hc⟩
  refine ⟨(toMeasurable P {ω | ¬ IsGood κ a b xL ρL ρR W B VL VR e S ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · rw [compl_compl, measure_toMeasurable]
    exact ae_iff.1 hae
  · intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable _ _ hn)

omit mΩ in
/-- Local deterministic retargeting data on each good sample. -/
theorem IsGood.data {ω : Ω} (hg : IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (ha : 0 < a) (hab : a < b) :
    RetargetData (j := 0) (m := 1) xL ![a, b] (W · ω)
      (fun i t => VL i t ω) (fun i t => VR i t ω)
      (sepTime (W · ω) (VR 0 · ω) (e ω)) :=
  Local2.retargetData_first ha hab (hg.path.mono (sepTime_le _ _ _)) (fun _ ht => lt_of_lt_sepTime ht)

omit mΩ in
/-- The existing localizer lies strictly before raw separation on every good sample. -/
theorem IsGood.loc_lt {ω : Ω} (hg : IsGood κ a b xL ρL ρR W B VL VR e S ω) (n : ℕ) :
    (rLoc 0 G S W VL VR B e n ω : ℝ≥0∞) < sepTime (W · ω) (VR 0 · ω) (e ω) :=
  (ENNReal.coe_le_coe.2 (rLoc_le_T n ω)).trans_lt (hg.before n)

variable (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
  (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)

omit mΩ in
include hgood in
/-- The masked original Brownian path is continuous on every sample. -/
theorem continuous_brownG (ω : Ω) : Continuous (Sec2.TwoSeed.brownG G B · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using (hgood ω hω).contB
  · simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
/-- Masking a null exceptional event preserves the original Brownian law. -/
theorem isFilteredBrownianReal_brownG :
    IsFilteredBrownianReal (usualAugmentation 𝓕 P) (Sec2.TwoSeed.brownG G B) P := by
  have h := (Ito.isFilteredBrownianReal_modify
    (Ito.isFilteredBrownianReal_usualAugmentation hE.brownian) hGm hGc
    (fun ω hω => (hgood ω hω).contB)).1
  rwa [Ito.nullAugmented_usualAugmentation] at h

include hE hGm hGc hgood in
/-- The existing spatial exit is a stopping time for a local source evolution. -/
theorem isStoppingTime_rHit (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) (rHit 0 G W VL VR e n) := by
  have hG0 : MeasurableSet[usualAugmentation 𝓕 P 0] G :=
    by simpa only [compl_compl] using
      (Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc 0).compl
  have hw := Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) hE.adapted_W
  have hL := fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.adapted_VL i)
  have hR := fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation 𝓕 P) (hE.adapted_VR i)
  have hhit := Coupling.isStoppingTime_hitBelow_state hw hL hR hG0 (fun ω hω =>
    (hgood ω hω).path.continuousOn_w.prodMk
      ((continuousOn_pi.2 (hgood ω hω).path.continuousOn_vL).prodMk
        (continuousOn_pi.2 (hgood ω hω).path.continuousOn_vR))) (continuous_rLev 0 n) 0
  intro t
  have he : {ω | rHit 0 G W VL VR e n ω ≤ t} = Gᶜ ∪
      {ω | (if ω ∈ G then Coupling.hitBelow
        (fun s => rLev 0 n (Coupling.stateAt W VL VR s ω)) (e ω) 0 else ⊤) ≤ t} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [mem_ofPred_eq, rHit, hω, ↓reduceIte, mem_union, mem_compl_iff, not_true_eq_false, false_or]
    · simp only [rHit, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff,
        not_false_eq_true, true_or, iff_true]
      exact zero_le
  rw [he]
  exact ((usualAugmentation 𝓕 P).mono (zero_le (a := t)) _ hG0).compl.union (hhit t)

include hE hGm hGc hgood in
/-- The existing spatial/Brownian localizers are stopping times for a local evolution. -/
theorem isStoppingTime_rLoc
    (hS : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (S n ω : WithTop ℝ≥0)) (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (rLoc 0 G S W VL VR B e n ω : WithTop ℝ≥0) := by
  refine Sec2.TwoSeed.isStoppingTime_capTime ?_
    ((isStoppingTime_rHit hE hGm hGc hgood n).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG hE hGm hGc hgood).2.1 (continuous_brownG hgood) n))
  have h := (isStoppingTime_const (usualAugmentation 𝓕 P) (n : ℝ≥0)).min (hS n)
  convert h using 2 with ω
  exact WithTop.coe_min _ _

end InteractingSLE.Sec5.TwoMark.Mart9
