/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR11Facts

/-! # The near comparison from precisely the stopped SDE and buffer facts -/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR11

open GW2TipSystem.RootN4 GW2TipSystem.RootV7 Supp12.DSReach CS3Cross

theorem isOpen_nearTarget {κ : ℝ} (f : NearCrossingFamily.{u} κ) :
    IsOpen (nearTarget f) := by
  unfold nearTarget
  split_ifs
  · exact isOpen_leftTarget
  · exact isOpen_rightTarget

theorem isOpen_nearBuffer {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) :
    IsOpen (nearBuffer f n) := by
  unfold nearBuffer
  split_ifs
  · exact isOpen_setOf_inBuffer _ _ _ _
  · exact isOpen_setOf_inBuffer _ _ _ _

theorem inBuffer_of_mem_nearBuffer {κ : ℝ} (f : NearCrossingFamily.{u} κ) (n : ℕ) :
    ∀ p ∈ nearBuffer f n,
      InBuffer f.mL f.mR (n : ℝ) (1 / ((n : ℝ) + 1)) p := by
  rcases f.horientation with h | h
  · simpa only [nearBuffer, h.1, Bool.true_eq, ↓reduceIte, leftBuf, h.2.1,
      mem_ofPred_eq]
      using fun p (hp : p ∈ leftBuf (nL := f.nL) f.mL f.nR n) => hp
  · simpa only [nearBuffer, h.1, Bool.false_eq_true, ↓reduceIte, rightBuf, h.2.1,
      mem_ofPred_eq]
      using fun p (hp : p ∈ rightBuf (nR := f.nR) f.nL f.mR n) => hp

/-- The actual local SDE and deterministic buffer fact imply the fixed
reference family's comparison for this word and buffer. -/
theorem near_comparison {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {κ : ℝ} (hκ : 0 < κ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : NearData Ω κ) {sample : ℕ → Ω → DriverRecord}
    (hsample : ∀ a, Measurable (sample a)) (reach : ℕ → Set DriverRecord) (n m : ℕ)
    (hSDE : (z.dynamics n m).IsStopped μ κ
      z.family.xL (z.family.ρLs m) z.family.xR (z.family.ρRs m))
    (hBuffer : NearBufferFact z μ sample reach n m) :
    z.family.crossProb m n ≤ (μ.map (sample (z.candidate n m)))
      (reach (z.candidate n m)) := by
  let d := z.dynamics n m
  let f := z.family
  obtain ⟨Ω', mΩ', μ', _, π, hπ, 𝓕', W', VL', VR', B', ζ', hmarginal, hE', hag⟩ :=
    Restart.StoppedCont.stoppedContinuationStatement hκ f.xL f.xR
      (f.ρLs m) (f.ρRs m) (f.hw m).1 μ d.filtration d.W d.VL d.VR d.B d.stop
      hSDE.1 hSDE.2
  let e : EvolutionData.{u} f.nL f.nR := ⟨Ω', mΩ', μ', 𝓕', W', VL', VR', B', ζ'⟩
  have heq := GW2JDetR10.reach_probability_eq_of_same_word hκ f.hnL f.hnR
    f.hε (show 0 < 1 / ((n : ℝ) + 1) by positivity) f.hη f.hxL0 f.hxR0
    f.hxL f.hxR (f.hw m) (f.sequence m) e (f.hE m) hE' (n : ℝ≥0) (n : ℝ)
    (nearTarget f) (nearBuffer f n) (isOpen_nearTarget f) (isOpen_nearBuffer f n)
    (inBuffer_of_mem_nearBuffer f n)
  change (f.sequence m).P (reachEvent (n : ℝ≥0) (nearTarget f) (nearBuffer f n)
    (f.sequence m).W (f.sequence m).VL (f.sequence m).VR (f.sequence m).lifetime) ≤ _
  rw [heq, Measure.map_apply (hsample _) hBuffer.1, ← hmarginal,
    Measure.map_apply hπ ((hsample _) hBuffer.1)]
  have hdata : ∀ᵐ ξ ∂μ',
      (∀ t : ℝ≥0, (t : ℝ≥0∞) = d.stop (π ξ) →
        ContinuousOn (fun v => Coupling.stateAt d.W d.VL d.VR v (π ξ)) (Iic t)) ∧
      0 < d.stop (π ξ) ∧
      (∀ v : ℝ≥0, (v : ℝ≥0∞) = d.stop (π ξ) → v < (n : ℝ≥0) →
        Coupling.stateAt d.W d.VL d.VR v (π ξ) ∉ nearBuffer f n) ∧
      ∀ t : ℝ≥0, t < (n : ℝ≥0) → (t : ℝ≥0∞) < d.stop (π ξ) →
        Coupling.stateAt d.W d.VL d.VR t (π ξ) ∈ nearTarget f →
        sample (z.candidate n m) (π ξ) ∈ reach (z.candidate n m) :=
    ae_of_ae_map hπ.aemeasurable (hmarginal.symm ▸ (hSDE.2.and hBuffer.2))
  refine measure_mono_ae ?_
  filter_upwards [hdata, hag, hE'.2.2.2.2] with ξ hd hξ hp hreach
  change IsIntegratedSLEPath κ f.xL f.xR (f.ρLs m) (f.ρRs m)
    (fun v => W' v ξ) (fun i v => VL' i v ξ) (fun j v => VR' j v ξ)
    (fun v => B' v ξ) (ζ' ξ) at hp
  obtain ⟨t, htT, htζ, htO, htB⟩ := hreach
  have hstate : ∀ v : ℝ≥0, (v : ℝ≥0∞) < d.stop (π ξ) →
      Coupling.stateAt W' VL' VR' v ξ = Coupling.stateAt d.W d.VL d.VR v (π ξ) := by
    intro v hv
    obtain ⟨hW, hL, hR⟩ := hξ.2 v hv
    exact Prod.ext hW (Prod.ext (funext hL) (funext hR))
  have htV := GW2JDetR10.lt_stop_of_buffer_exit
    (f := fun v => Coupling.stateAt d.W d.VL d.VR v (π ξ))
    (g := fun v => Coupling.stateAt W' VL' VR' v ξ) hd.2.1
    (hp.isForcePath.continuousOn_w.prodMk
      ((continuousOn_pi.2 hp.isForcePath.continuousOn_vL).prodMk
        (continuousOn_pi.2 hp.isForcePath.continuousOn_vR))) hd.1 hstate hd.2.2.1
    htT htζ htB
  exact hd.2.2.2 t htT htV (hstate t htV ▸ htO)

end InteractingSLE.Theorem14.GW2JDetR11
