/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR10StoppedSlow

/-!
# The near-event comparison through a genuine buffer exit

Continuity extends agreement to a positive finite stopping time. A
reference path inside the inner buffer cannot cross that time if the
physical state there is outside the buffer. The local stopped SDE then
constructs a full reference evolution with the physical crossing inequality.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR10

open GW2TipSystem.RootN4 GW2TipSystem.RootV7 Supp12.DSReach

/-- A path agreeing with the physical path before a positive stop cannot
stay inside a buffer across the stop if the physical stopped value is
outside. The stop may be infinite; no stopping-time property is needed
for this deterministic assertion. -/
theorem lt_stop_of_buffer_exit {X : Type*} [TopologicalSpace X] [T2Space X]
    {f g : ℝ≥0 → X} {V L : ℝ≥0∞} {T t : ℝ≥0} {B : Set X}
    (hV : 0 < V) (hgc : ContinuousOn g {s | (s : ℝ≥0∞) < L})
    (hfc : ∀ v : ℝ≥0, (v : ℝ≥0∞) = V → ContinuousOn f (Iic v))
    (hag : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V → g s = f s)
    (hexit : ∀ v : ℝ≥0, (v : ℝ≥0∞) = V → v < T → f v ∉ B)
    (htT : t < T) (htL : (t : ℝ≥0∞) < L) (hB : ∀ s ≤ t, g s ∈ B) :
    (t : ℝ≥0∞) < V := by
  by_contra hnot
  have hVt : V ≤ (t : ℝ≥0∞) := le_of_not_gt hnot
  have hVne : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hVt
  let v := V.toNNReal
  have hv : (v : ℝ≥0∞) = V := ENNReal.coe_toNNReal hVne
  have hv0 : 0 < v := by
    apply ENNReal.coe_pos.1
    rwa [hv]
  have hvt : v ≤ t := ENNReal.coe_le_coe.1 (hv.symm ▸ hVt)
  have hgclosed : ContinuousOn g (Iic v) := hgc.mono fun s hs =>
    (ENNReal.coe_le_coe.2 (hs.trans hvt)).trans_lt htL
  have heq : EqOn g f (Iio v) := fun s hs =>
    hag s (by rw [← hv]; exact ENNReal.coe_lt_coe.2 hs)
  have heqclosed : EqOn g f (Iic v) := heq.of_subset_closure hgclosed (hfc v hv)
    Iio_subset_Iic_self (by rw [closure_Iio' (show (Iio v).Nonempty from ⟨0, hv0⟩)])
  have heqv : g v = f v := heqclosed (by simp only [mem_Iic]; exact le_refl v)
  exact hexit v hv (hvt.trans_lt htT) (heqv ▸ hB v hvt)

/-- Local stopped dynamics plus the actual buffer-exit property construct
a full finite-force reference evolution and the required one-sided
crossing inequality. All law and continuation data are conclusions. -/
theorem exists_reachComparison_of_stoppedEvolution {κ a : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} (xL ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ)
    (hF : IsOrderedForceWord xL xR)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B V)
    (hc : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, (v : ℝ≥0∞) = V ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic v))
    (hV : ∀ᵐ ω ∂P, 0 < V ω)
    (T : ℝ≥0) (O Bf : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    (htarget : ∀ p ∈ O, 2 < a + p.1)
    (hexit : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, (v : ℝ≥0∞) = V ω → v < T →
      Coupling.stateAt W VL VR v ω ∉ Bf)
    {sample : Ω → DriverRecord} (hsample : Measurable sample)
    (hlife : ∀ᵐ ω ∂P, (sample ω).1 = V ω)
    (hread : ∀ᵐ ω ∂P, ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample ω).1 →
      (sample ω).2 q = a + W q ω) :
    ∃ e : EvolutionData.{u} nL nR, e.IsEvolution κ xL ρL xR ρR ∧
      e.P (reachEvent T O Bf e.W e.VL e.VR e.lifetime) ≤ (P.map sample)
        {z | ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q} := by
  obtain ⟨Ω', mΩ', P', _, π, hπ, 𝓕', W', VL', VR', B', ζ', hmarginal, hE', hag⟩ :=
    Restart.StoppedCont.stoppedContinuationStatement hκ xL xR ρL ρR hF
      P 𝓕 W VL VR B V hE hc
  let e : EvolutionData.{u} nL nR := ⟨Ω', mΩ', P', 𝓕', W', VL', VR', B', ζ'⟩
  have hdata : ∀ᵐ ξ ∂P', (0 < V (π ξ)) ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = V (π ξ) →
        ContinuousOn (fun t => Coupling.stateAt W VL VR t (π ξ)) (Iic v)) ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = V (π ξ) → v < T →
        Coupling.stateAt W VL VR v (π ξ) ∉ Bf) ∧
      (sample (π ξ)).1 = V (π ξ) ∧
      ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (sample (π ξ)).1 →
        (sample (π ξ)).2 q = a + W q (π ξ) := by
    exact ae_of_ae_map hπ.aemeasurable
      (hmarginal.symm ▸ (hV.and (hc.and (hexit.and (hlife.and hread)))))
  refine ⟨e, hE', reach_probability_le_on_extension e hE' hπ hmarginal
    hsample T O Bf htarget ?_ ?_⟩
  · filter_upwards [hdata, hag, hE'.2.2.2.2] with ξ hd hξ hp
    intro t htT htζ htB
    change IsIntegratedSLEPath κ xL xR ρL ρR (fun s => W' s ξ)
      (fun i s => VL' i s ξ) (fun j s => VR' j s ξ) (fun s => B' s ξ) (ζ' ξ) at hp
    rw [hd.2.2.2.1]
    refine lt_stop_of_buffer_exit
      (f := fun s => Coupling.stateAt W VL VR s (π ξ))
      (g := fun s => Coupling.stateAt W' VL' VR' s ξ)
      (V := V (π ξ)) (L := ζ' ξ) (T := T) (B := Bf) hd.1
      (hp.isForcePath.continuousOn_w.prodMk
        ((continuousOn_pi.2 hp.isForcePath.continuousOn_vL).prodMk
          (continuousOn_pi.2 hp.isForcePath.continuousOn_vR))) hd.2.1
      (fun s hs => ?_) hd.2.2.1 htT htζ htB
    obtain ⟨hW, hL, hR⟩ := hξ.2 s hs
    exact Prod.ext hW (Prod.ext (funext hL) (funext hR))
  · filter_upwards [hdata, hag] with ξ hd hξ
    intro q hq _
    change (sample (π ξ)).2 q = a + W' q ξ
    rw [hd.2.2.2.2 q hq, (hξ.2 q (hd.2.2.2.1 ▸ hq)).1]

end InteractingSLE.Theorem14.GW2JDetR10
