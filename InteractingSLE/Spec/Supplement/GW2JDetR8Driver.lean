/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR8Zero
import InteractingSLE.Spec.Supplement.GW2JDetR3Chain
import InteractingSLE.Spec.Supplement.GW2JDetR4Contact
import InteractingSLE.Spec.Sec7.PocketMartLife

/-! # GW2: read the stopped chart mean using any actual relative driver version -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2JDetR8

open GW2Fb Supp8 Supp8.GB6 Supp8.GB6LMean Supp8.Q3Chain Exist.StagedLaw
open Restart Sec7.PocketTraversal GW2TipSystem GW2JointKernel RelSafeS

/-- The physical clock is continuous through each strictly live pre-contact
stop. This follows from the actual two traces, also for a finite explored life. -/
theorem clock_regular_before_contact {w wα : ℝ≥0 → ℝ} {γ α : ℝ≥0 → ℂ}
    {ζα : ℝ≥0∞} (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    {s T : ℝ≥0} (hsH : γ s ∈ H) (hα : IsGeneratingTrace wα ζα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < ζα}) (hwα0 : wα 0 = 0)
    (hTζ : (T : ℝ≥0∞) < ζα)
    (hTc : (T : ℝ≥0∞) < firstContactTime (fun t => (α t : OnePoint ℂ))
      ((fun t => sphereInv (γ t : OnePoint ℂ)) '' Icc 0 s)) :
    relClock (Ito.rpath w) s (Ito.rpath wα) 0 = 0 ∧
      ContinuousOn (fun t : ℝ≥0 => relClock (Ito.rpath w) s (Ito.rpath wα) t) (Icc 0 T) := by
  have hz : 0 < ζα := lt_of_le_of_lt bot_le hTζ
  obtain ⟨_, _, ha0, _, hac, _, _⟩ := GW2JDetR3.exists_inverse_capacity_chain
    (fun t (_ : Unit) => w t) (fun _ => ⊤) () hγ hw.continuousOn hw0
    ENNReal.coe_lt_top hsH hα hwα hwα0 hz
  have he : EqOn (rdrv (cfRec s (fun t (_ : Unit) => w t) (fun _ => ⊤) ()))
      (Ito.rpath w) (Icc 0 (s : ℝ)) :=
    GaugeE.record_prefix_eq s hw0 hw.continuousOn ENNReal.coe_lt_top
  have hclock := relClock_eq_of_eqOn s.coe_nonneg he (Ito.rpath wα)
  rw [hclock] at ha0 hac
  refine ⟨ha0, hac.mono fun t ht => ?_⟩
  have htT := ENNReal.coe_le_coe.mpr ht.2
  refine lt_min ?_ (htT.trans_lt hTζ)
  rw [GW2JDetR4.firstContactTime_sphereInv α γ s]
  exact htT.trans_lt hTc

/-- Canonical means at geometric marks only depend on the driver's prefix.
Both the boundary extension and its Loewner transport use the same prefix. -/
theorem couplingMean_bheProc_congr {κ : ℝ} {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    {W R : ℝ≥0 → ℝ} (hR : Continuous R) {q : ℝ≥0}
    (he : EqOn (Ito.rpath W) (Ito.rpath R) (Icc 0 (q : ℝ))) :
    couplingMean κ (Ito.rpath W) q
        (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => W t)
          (geomLW (fun t (_ : Unit) => W t) (fun _ => xL))
          (geomRW (fun t (_ : Unit) => W t) (fun _ => xR)) () q) =
      couplingMean κ (Ito.rpath R) q
        (DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => R t)
          (geomLW (fun t (_ : Unit) => R t) (fun _ => xL))
          (geomRW (fun t (_ : Unit) => R t) (fun _ => xR)) () q) := by
  have hNN : ∀ t : ℝ≥0, t ≤ q → W t = R t := fun t ht => by
    simpa only [Ito.rpath, Real.toNNReal_coe] using he ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr ht⟩
  have hL := fun i => Sec7.PocketMartLife.geomLW_congr
    (W := fun t (_ : Unit) => W t) (W' := fun t (_ : Unit) => R t)
    (ω := ()) hR hNN (fun _ => xL) i
  have hRi := fun i => Sec7.PocketMartLife.geomRW_congr
    (W := fun t (_ : Unit) => W t) (W' := fun t (_ : Unit) => R t)
    (ω := ()) hR hNN (fun _ => xR) i
  have hB : DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => W t)
      (geomLW (fun t (_ : Unit) => W t) (fun _ => xL))
      (geomRW (fun t (_ : Unit) => W t) (fun _ => xR)) () q =
      DomainMarkov.bheProc κ ρL ρR (fun t (_ : Unit) => R t)
        (geomLW (fun t (_ : Unit) => R t) (fun _ => xL))
        (geomRW (fun t (_ : Unit) => R t) (fun _ => xR)) () q := by
    unfold DomainMarkov.bheProc
    congr 1
    · funext i
      dsimp only
      rw [hL i, hNN q le_rfl]
    · funext j
      dsimp only
      rw [hRi j, hNN q le_rfl]
  funext y
  rw [hB]
  exact Sec7.Lemma71B.couplingMean_congr q.coe_nonneg he κ _ y

/-- A frozen chain and a continuous relative version with the actual same
physical hulls have the same driver through the stopped relative time. -/
theorem relChainStop_driver_eq_of_hulls {κ : ℝ} {nL nR mL mR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {σL : Fin mL → ℝ} {σR : Fin mR → ℝ} {yL : Fin mL → ℝ} {yR : Fin mR → ℝ}
    {U : ℝ → ℝ} {w R : ℝ≥0 → ℝ} {s T : ℝ≥0}
    {p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)}
    (hp : IsRelChainStop κ ρL ρR xL xR σL σR yL yR U s w T p)
    (hRc : Continuous R) (hR0 : R 0 = 0)
    (ha0 : relClock U s (Ito.rpath w) 0 = 0)
    (hac : ContinuousOn (fun t : ℝ≥0 => relClock U s (Ito.rpath w) t) (Icc 0 T))
    (hHR : HullsUpTo U s (Ito.rpath w) (Ito.rpath R) T) :
    EqOn (fun r : ℝ => p.2.2.1 r.toNNReal) (Ito.rpath R)
      (Icc 0 (relClock U s (Ito.rpath w) T)) := by
  have hRp0 : Ito.rpath R 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hR0
  have he := eqOn_of_hullsUpTo hp.2.2.2.2.1 hp.2.2.2.2.2.1
    (hRc.comp continuous_real_toNNReal) hRp0 ha0 hac
    (fun t ht => (relChainStop_prefix hp t ht).2.2) hHR
  intro x hx
  simpa only [Ito.rpath, Function.comp_def, Real.coe_toNNReal _ hx.1] using he hx

end InteractingSLE.Theorem14.GW2JDetR8
