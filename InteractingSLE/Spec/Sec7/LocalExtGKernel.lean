/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtGChart
import InteractingSLE.Spec.Coupling.MartMeans2Chart

/-!
# Aux. lemma 53 in the half-plane: the Gaussian clause of the restarted coupling

Packet PROVE-LOCEXT-G. Specification p. 245, Aux. lemma 53 ("At every finite own-filtration stopping time `τ < T_*`,
condition on the recorded driving history and map the active field and future hulls by the centered map
`f_τ = g_τ − W_τ`, with the inherited logarithmic derivative branch. Their conditional law again satisfies the
original optional hull specification, with the current force groups as initial data"). The conditional-law clause
after the restart is landed in the original domain of the chart (`IsOptionalHullCoupling.restart_condExp`,
PROVE-SEC5-D); this file moves it to the half-plane with a chart **read from the recorded history**, so that the
restarted field is a measurable function of the field and of the history:

* `exists_measurable_stoppedHistory_version`: the recorded history `𝒳_T` has a `𝓓_T`-measurable version (through the
  progressive versions of the driving process), equal to `𝒳_T` on every path continuous before `ζ > T`;
* **`isCouplingCharFun_restart`**: for every `𝓓_T`-measurable `K` equal to `𝒳_T` almost surely on `{T < ζ}`, the
  chart field `h' = h ∘ f_K⁻¹ − χ arg (f_K⁻¹)′` (`chartTransport (histChart K) 1 0 χ h`) satisfies the coupling clause
  `IsCouplingCharFun` of the **restarted** processes `W_{T+·} − W_T`, `V_{T+·} − W_T`, `ζ − T` for the restarted
  filtration `𝓖'_s = 𝓓_{T+s}`: at every `𝓖'`-stopping time `τ' < ζ − T`, conditionally on `𝓖'_{τ'}`, the pairing of
  `h'` with every test function supported off the restarted hull `K'_{τ'}` has the frozen kernel of the restarted
  coupling, with the **current force positions** `V_{T+τ'} − W_{T+τ'}` as data (Aux. lemma 53's Gaussian clause);
* `restartField K h`: that chart field as a function of `(h, K)` (`measurable_restartField`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec5.Markov Sec2.Restart

variable {nL nR : ℕ}

/-- **The restarted field read from the history**: `h ∘ f_y⁻¹ − χ arg (f_y⁻¹)′`, `f_y` the Loewner chart read from
the recorded history `y` (`histChart`). -/
def restartField (κ : ℝ) (p : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) :
    LQGMetric.DistOn upperHalfPlaneOpens :=
  Chart.chartTransport (isConformal_histChart p.2) 1 0 (chiC κ) p.1

theorem measurable_restartField (κ : ℝ) : Measurable (restartField (nL := nL) (nR := nR) κ) :=
  measurable_histChartField 1 0 (chiC κ)

theorem isChartTransport_restartField (κ : ℝ) (p : LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) :
    IsChartTransport (histChart p.2) 1 0 (chiC κ) p.1 (restartField κ p) :=
  Chart.isChartTransport_chartTransport (isConformal_histChart p.2)
    (Chart.locallyIntegrableOn_of_continuousOn
      ((isConformal_histChart p.2).continuousOn_lift_inv (continuousOn_lift_histChart p.2))) 1 0 (chiC κ) p.1

section Restart

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **A `𝓓_T`-measurable version of the recorded history `𝒳_T`**: the history of the progressive versions of the
driving process, equal to `𝒳_T` wherever the path is an integrated SLE path and `T < ζ`. -/
theorem exists_measurable_stoppedHistory_version (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) :
    ∃ K : Ω → DrivingHist nL nR, Measurable[hT.measurableSpace] K ∧
      ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
          (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω := by
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hle : killedDrivingFiltration hX ≤ 𝓓 := Ito.le_usualAugmentation _ P
  have hWad : AdaptedBefore 𝓓 ζ W := Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_W hX)
  have hLad : ∀ i, AdaptedBefore 𝓓 ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hRad : ∀ j, AdaptedBefore 𝓓 ζ (VR j) := fun j =>
    Ito.adaptedBefore_mono hle (Coupling.adaptedBefore_killedDriving_VR hX j)
  refine ⟨fun ω => stoppedHistory (pvState ζ W VL VR) (fun ω => (T ω : WithTop ℝ≥0)) ω, ?_, ?_⟩
  · -- the time and each sample are `𝓓_T`-measurable
    have hq : ∀ q : ℚ≥0, IsStoppingTime 𝓓 fun ω => ((min (q : ℝ≥0) (T ω) : ℝ≥0) : WithTop ℝ≥0) := by
      intro q
      have h := hT.min_const (q : ℝ≥0)
      have e : (fun ω => ((min (q : ℝ≥0) (T ω) : ℝ≥0) : WithTop ℝ≥0)) =
          fun ω => min ((T ω : ℝ≥0) : WithTop ℝ≥0) ((q : ℝ≥0) : WithTop ℝ≥0) := by
        funext ω
        rw [WithTop.coe_min, min_comm]
      rw [e]
      exact h
    have hqle : ∀ q : ℚ≥0, (hq q).measurableSpace ≤ hT.measurableSpace := fun q =>
      IsStoppingTime.measurableSpace_mono _ _ fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)
    have hev : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓓 ζ X → ∀ q : ℚ≥0,
        Measurable[hT.measurableSpace] fun ω => progVersion ζ X (min (q : ℝ≥0) (T ω)) ω := by
      intro X hX' q
      have h := measurable_stoppedValue (isStronglyProgressive_progVersion hX') (hq q)
      exact h.mono (hqle q) le_rfl
    have hT' : Measurable[hT.measurableSpace] fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0) := hT.measurable
    refine hT'.prodMk (@Measurable.of_eval Ω ℚ≥0 (fun _ => ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))
      hT.measurableSpace _ _ fun q => ?_)
    have hst : (fun ω => pvState ζ W VL VR (stopAt (fun ω => (T ω : WithTop ℝ≥0)) (q : ℝ≥0) ω) ω) =
        fun ω => pvState ζ W VL VR (min (q : ℝ≥0) (T ω)) ω := by
      funext ω
      simp only [stopAt, WithTop.untopD_coe]
    change Measurable[hT.measurableSpace]
      fun ω => pvState ζ W VL VR (stopAt (fun ω => (T ω : WithTop ℝ≥0)) (q : ℝ≥0) ω) ω
    rw [hst]
    exact (hev hWad q).prodMk ((@Measurable.of_eval Ω (Fin nL) (fun _ => ℝ) hT.measurableSpace _ _
      fun i => hev (hLad i) q).prodMk
      (@Measurable.of_eval Ω (Fin nR) (fun _ => ℝ) hT.measurableSpace _ _ fun j => hev (hRad j) q))
  · intro ω hp hTζ
    simp only [stoppedHistory]
    refine Prod.ext rfl (funext fun q => ?_)
    simp only [stopAt, WithTop.untopD_coe]
    have hlt : ((min (q : ℝ≥0) (T ω) : ℝ≥0) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hTζ
    obtain ⟨h1, h2, h3⟩ := restart_values hp hlt
    simp only [pvState, completedState, hlt, ↓reduceIte, drivingState, h1, h2, h3]

/-- **Aux. lemma 53, the Gaussian clause in the half-plane.** For a frozen optional hull coupling, a finite stopping
time `T` of its driving filtration `𝓓` and a `𝓓_T`-measurable version `K` of the recorded history `𝒳_T`, the
restarted field `h' = restartField κ (h, K)` (`h ∘ f_T⁻¹ − χ arg (f_T⁻¹)′`) satisfies the coupling clause of the
restarted processes for the restarted filtration `𝓖'_s = 𝓓_{T+s}`: at every `𝓖'`-stopping time `τ' < ζ − T`, every
bounded harmonic extension `u` of the current force data and every test function `φ` supported off the restarted hull,
`E[e^{i (h', φ)} | 𝓖'_{τ'}] = exp(i ∫ 𝔥'_{τ'} φ − ½ E'_{τ'}(φ))` almost surely. -/
theorem isCouplingCharFun_restart [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) :
    Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (restartFiltration (drivingFiltration P hX) T hT)
      (restartDrv W T) (fun i => restartMark (VL i) W T) (fun j => restartMark (VR j) W T) (restartLife ζ T)
      (fun ω => restartField κ (h ω, K ω)) := by
  have hpath := hC.1.2.2.2.2
  have h0 := restartFiltration_zero (𝓕 := drivingFiltration P hX) hT
  have hKm' : Measurable[restartFiltration (drivingFiltration P hX) T hT 0] K := by rw [h0]; exact hKm
  refine Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport (c := fun ω => histChart (K ω))
    (fun ω => isConformal_histChart (K ω)) (fun z => hKm' (measurableSet_mem_dom_histChart z))
    (fun z => ?_) (fun z => ?_) (fun ω => continuousOn_lift_histChart (K ω)) hC.2.1 ?_ ?_
    (fun ω => isChartTransport_restartField κ (h ω, K ω))
  · have h := (measurable_indicator_fwd_histChart (nL := nL) (nR := nR) z).comp hKm'
    have e : ({ω | z ∈ (histChart (K ω)).dom}.indicator fun ω => (histChart (K ω)).1 z) =
        ({y | z ∈ (histChart y).dom}.indicator fun y => (histChart y).1 z) ∘ K := by
      funext ω
      by_cases hz : z ∈ (histChart (K ω)).dom
      · simp only [Function.comp_apply, indicator_of_mem (show K ω ∈ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_mem (show ω ∈ {ω | z ∈ (histChart (K ω)).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show K ω ∉ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_notMem (show ω ∉ {ω | z ∈ (histChart (K ω)).dom} from hz)]
    rw [e]
    exact h
  · have h := (measurable_indicator_lift_histChart (nL := nL) (nR := nR) z).comp hKm'
    have e : ({ω | z ∈ (histChart (K ω)).dom}.indicator fun ω => (histChart (K ω)).2.2 z) =
        ({y | z ∈ (histChart y).dom}.indicator fun y => (histChart y).2.2 z) ∘ K := by
      funext ω
      by_cases hz : z ∈ (histChart (K ω)).dom
      · simp only [Function.comp_apply, indicator_of_mem (show K ω ∈ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_mem (show ω ∈ {ω | z ∈ (histChart (K ω)).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show K ω ∉ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_notMem (show ω ∉ {ω | z ∈ (histChart (K ω)).dom} from hz)]
    rw [e]
    exact h
  · -- the restarted driver starts at `0` and is continuous before the restarted lifetime
    filter_upwards [hpath] with ω hp
    refine ⟨by simp [restartDrv], ?_⟩
    by_cases hTζ : (T ω : ℝ≥0∞) < ζ ω
    · exact (hp.restart hTζ).2.2.2.1
    · have he : {t : ℝ≥0 | (t : ℝ≥0∞) < restartLife ζ T ω} = ∅ := by
        ext t
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, restartLife]
        rw [tsub_eq_zero_of_le (not_lt.1 hTζ)]
        exact zero_le
      rw [he]
      exact continuousOn_empty _
  · -- the clause in the original domain of the chart: Aux. lemma 53 of `Sec5.Markov`
    intro τ hτ hτζ u hu φ
    have hmain := hC.restart_condExp hX hT τ hτ hτζ u hu φ
    filter_upwards [hmain, hK, hpath, hτζ] with ω h1 h2 hp h4
    have hTζ : (T ω : ℝ≥0∞) < ζ ω := by
      have h5 : 0 < restartLife ζ T ω := lt_of_le_of_lt zero_le h4
      exact tsub_pos_iff_lt.1 h5
    have hc : histChart (K ω) = restartChart W T ω := by
      rw [h2 hTζ]
      exact (restartChart_eq_histChart hp.2.2.2.1 hp.1 hTζ).symm
    simp only [hc]
    exact h1

end Restart

end LocalExt

end InteractingSLE
