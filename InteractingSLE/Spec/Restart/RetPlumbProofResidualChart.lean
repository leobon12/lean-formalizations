/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualPhysical

/-!
# Chart coordinates from a truncated physical lifetime

Packet PROVE-RETPLUMB. Approximate the observed coordinate from strictly before
both its physical line and the boundary lifetime. Continuity supplies the stopped
endpoint. The full future lifetime is never an observation at the current line.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7
open QuantumZipper (H)
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Survival observations through a line determine the lifetime truncated there. -/
theorem measurable_indicator_min_of_survival {𝓖 : Filtration ℝ≥0 mΩ}
    {F : Set Ω} (_hF : MeasurableSet[𝓖 0] F) {V : Ω → ℝ≥0∞}
    (hV : ∀ s, MeasurableSet[𝓖 s] (F ∩ {ω | (s : ℝ≥0∞) < V ω})) (t : ℝ≥0) :
    Measurable[𝓖 t] (F.indicator fun ω => min (V ω) (t : ℝ≥0∞)) := by
  classical
  refine measurable_of_Ioi fun a => ?_
  induction a using ENNReal.recTopCoe with
  | top => simp only [Ioi_top, preimage_empty, MeasurableSet.empty]
  | coe s =>
    by_cases hst : s < t
    · have he : (F.indicator fun ω => min (V ω) (t : ℝ≥0∞)) ⁻¹' Ioi (s : ℝ≥0∞) =
          F ∩ {ω | (s : ℝ≥0∞) < V ω} := by
        ext ω
        by_cases hω : ω ∈ F <;> simp [hω, hst]
      rw [he]
      exact 𝓖.mono hst.le _ (hV s)
    · have he : (F.indicator fun ω => min (V ω) (t : ℝ≥0∞)) ⁻¹' Ioi (s : ℝ≥0∞) = ∅ := by
        ext ω
        by_cases hω : ω ∈ F <;> simp [hω, hst]
      rw [he]
      exact @MeasurableSet.empty Ω (𝓖 t)

/-- Truncating the lifetime at the observation line does not change the
coordinate approached from below that truncated lifetime. -/
theorem contPath_min_truncated {D : Set ℂ} {φ : ℂ → ℂ} {η : ℝ≥0 → ℂ}
    {a s t : ℝ≥0} {V : ℝ≥0∞} (hst : s ≤ t) :
    contPath D φ η a V (min s (min V (t : ℝ≥0∞)).toNNReal) = contPath D φ η a V s := by
  have hfin : min V (t : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  by_cases hVs : V ≤ (s : ℝ≥0∞)
  · have hVt := hVs.trans (ENNReal.coe_le_coe.2 hst)
    have hfinV : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hVs
    have hsV : V.toNNReal ≤ s := by
      apply ENNReal.coe_le_coe.1
      rwa [ENNReal.coe_toNNReal hfinV]
    rw [min_eq_left hVt, min_eq_right hsV, contPath_of_le
      (by rw [ENNReal.coe_toNNReal hfinV]), contPath_of_le hVs]
  · have hs : s ≤ (min V (t : ℝ≥0∞)).toNNReal := by
      apply ENNReal.coe_le_coe.1
      rw [ENNReal.coe_toNNReal hfin]
      exact le_min (le_of_not_ge hVs) (ENNReal.coe_le_coe.2 hst)
    rw [min_eq_left hs]

/-- A continuous observable proxy agreeing before the truncated lifetime
recovers the boundary-stopped chart coordinate. Only the truncated lifetime
and the current proxy coordinates must be measurable. -/
theorem measurable_contPath_of_past {F : Set Ω} (hF : MeasurableSet F)
    {D : Ω → Set ℂ} (hDo : ∀ ω, IsOpen (D ω))
    (hDm : ∀ z, MeasurableSet {ω | z ∈ D ω}) {φ : Ω → ℂ → ℂ}
    (hφm : ∀ z, Measurable ({ω | z ∈ D ω}.indicator fun ω => φ ω z))
    {η ηc : Ω → ℝ≥0 → ℂ} (hηc : ∀ q, Measurable fun ω => ηc ω q)
    (hc : ∀ ω ∈ F, Continuous (ηc ω)) (a t : ℝ≥0) (ht : 0 < t)
    {V : Ω → ℝ≥0∞} (hV : Measurable (F.indicator fun ω => min (V ω) (t : ℝ≥0∞)))
    (hpos : ∀ ω ∈ F, 0 < V ω)
    (he : ∀ ω ∈ F, ∀ q : ℝ≥0, (q : ℝ≥0∞) < min (V ω) (t : ℝ≥0∞) →
      ηc ω (a + q) = η ω (a + q))
    (hcl : ∀ ω ∈ F, ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω → η ω (a + q) ∈ closure (D ω))
    (hlim : ∀ ω ∈ F, ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ w, Tendsto (φ ω) (𝓝[D ω] (η ω (a + q))) (𝓝 w))
    (hΓ : ∀ ω ∈ F, Continuous (contPath (D ω) (φ ω) (η ω) a (V ω)))
    (s : ℝ≥0) (hst : s ≤ t) :
    Measurable (F.indicator fun ω => contPath (D ω) (φ ω) (η ω) a (V ω) s) := by
  classical
  let U := F.indicator fun ω => min (V ω) (t : ℝ≥0∞)
  have hU : ∀ ω ∈ F, U ω = min (V ω) (t : ℝ≥0∞) := fun ω hω => indicator_of_mem hω _
  let D' : Ω → Set ℂ := fun ω => if ω ∈ F then D ω else H
  let φ' : Ω → ℂ → ℂ := fun ω => if ω ∈ F then φ ω else id
  have hDo' : ∀ ω, IsOpen (D' ω) := fun ω => by
    dsimp [D']; split_ifs
    · exact hDo ω
    · exact QuantumZipper.isOpen_H
  have hDm' : ∀ z, MeasurableSet {ω | z ∈ D' ω} := fun z => by
    have he' : {ω | z ∈ D' ω} = (F ∩ {ω | z ∈ D ω}) ∪ (Fᶜ ∩ {_ω | z ∈ H}) := by
      ext ω; by_cases hω : ω ∈ F <;> simp [D', hω]
    rw [he']
    exact (hF.inter (hDm z)).union (hF.compl.inter (MeasurableSet.const _))
  have hφ' : ∀ z, Measurable ({ω | z ∈ D' ω}.indicator fun ω => φ' ω z) := fun z => by
    have he' : ({ω | z ∈ D' ω}.indicator fun ω => φ' ω z) =
        F.piecewise ({ω | z ∈ D ω}.indicator fun ω => φ ω z)
          (fun _ => if z ∈ H then z else 0) := by
      funext ω
      by_cases hω : ω ∈ F <;> by_cases hz : z ∈ H <;>
        simp [Set.indicator, Set.piecewise, D', φ', hω, hz]
    rw [he']
    exact (hφm z).piecewise hF measurable_const
  have hq : ∀ ω ∈ F, ∀ n : ℕ, (approxTime (U ω) s n : ℝ≥0∞) < min (V ω) (t : ℝ≥0∞) := by
    intro ω hω n
    rw [← hU ω hω]
    exact approxTime_lt (by rw [hU ω hω]; exact lt_min (hpos ω hω) (ENNReal.coe_pos.2 ht)) s n
  let Z : ℕ → Ω → ℂ := fun n ω =>
    if ω ∈ F then contPath (D ω) (φ ω) (η ω) a (V ω) (approxTime (U ω) s n) else 0
  have hZ : ∀ n, Measurable (Z n) := by
    intro n
    let q : Ω → ℂ := fun ω => if ω ∈ F then ηc ω (a + approxTime (U ω) s n) else 0
    have hqm : Measurable q := measurable_piecewise_eval hF hηc
      (measurable_const.add (measurable_approxTime hV s n))
      (fun ω hω => (hc ω hω).continuousOn)
    have hqD : ∀ ω, q ω ∈ closure (D' ω) := by
      intro ω
      by_cases hω : ω ∈ F
      · simp only [q, D', ite_eq_left hω, he ω hω _ (hq ω hω n)]
        exact hcl ω hω _ ((hq ω hω n).trans_le (min_le_left _ _))
      · simp only [q, D', ite_eq_right hω]
        rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
        show (0 : ℝ) ≤ (0 : ℂ).im
        simp
    apply measurable_of_tendsto_nhdsWithin hDo' hDm' hφ' hqm hqD
    intro ω
    by_cases hω : ω ∈ F
    · simp only [φ', D', q, Z, ite_eq_left hω, he ω hω _ (hq ω hω n)]
      rw [contPath_of_lt ((hq ω hω n).trans_le (min_le_left _ _))]
      exact tendsto_nhds_limUnder (hlim ω hω _ ((hq ω hω n).trans_le (min_le_left _ _)))
    · simp only [φ', D', q, Z, ite_eq_right hω]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
  apply measurable_of_tendsto_metrizable hZ
  refine tendsto_pi_nhds.2 fun ω => ?_
  by_cases hω : ω ∈ F
  · simp only [Z, ite_eq_left hω, indicator_of_mem hω]
    have hfin : U ω ≠ ⊤ := by
      rw [hU ω hω]
      exact ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    have hconv : Tendsto (fun n : ℕ => contPath (D ω) (φ ω) (η ω) a (V ω)
        (approxTime (U ω) s n)) atTop
        (𝓝 (contPath (D ω) (φ ω) (η ω) a (V ω) (min s (U ω).toNNReal))) :=
      ((hΓ ω hω).tendsto _).comp (tendsto_approxTime hfin s)
    have hv : contPath (D ω) (φ ω) (η ω) a (V ω) (min s (U ω).toNNReal) =
        contPath (D ω) (φ ω) (η ω) a (V ω) s := by
      rw [hU ω hω]
      exact contPath_min_truncated hst
    rw [hv] at hconv
    exact hconv
  · simp only [Z, ite_eq_right hω, indicator_of_notMem hω]
    exact tendsto_const_nhds

end InteractingSLE.Restart.RetAux79
