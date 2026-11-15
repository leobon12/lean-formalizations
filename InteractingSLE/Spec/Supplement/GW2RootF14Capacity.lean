/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootF14Window

/-!
# Literal capacity on finite relative trace windows

Packet PROVE-T14-GW2ROOT2. The exact joint-chart carrier and half capacity
follow using finite generating lifetimes on both sides of the chart.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF14

open Supp8.GB6 Restart

/-- The literal `capOf` of an upper generating-trace prefix is its own
time, for every strictly pre-lifetime cutoff. -/
theorem capOf_upper_prefix_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}
    (hΓ : IsGeneratingTrace w T Γ) (hw : ContinuousOn w {r | (r : ℝ≥0∞) < T})
    (hw0 : w 0 = 0) {v : ℝ≥0} (hv : (v : ℝ≥0∞) < T) :
    capOf (Γ '' Icc 0 v ∩ H) = (v : ℝ) := by
  have hc := hΓ.2.1.mono (show Icc 0 v ⊆ {r : ℝ≥0 | (r : ℝ≥0∞) ≤ T} from
    fun r hr => (ENNReal.coe_le_coe.mpr hr.2).trans hv.le)
  obtain ⟨_, hb, ha, hf⟩ := RootD12.upper_prefix_geometry hc (by rw [hΓ.1]; exact le_rfl)
  rw [RootC11.capOf_eq_hcapSet hb ha, hf]
  have hg : IsGeneratingTrace w T (fun r => Γ r - (0 : ℝ)) := by
    simpa only [ofReal_zero, sub_zero] using hΓ
  rw [Restart.IsGeneratingTrace.hcapSet_fillH_add hg hw hw0 hv]
  ring

variable {Wc Wrel : ℝ≥0 → ℝ} {Tγ TΓ : ℝ≥0∞} {γ Γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace Wc Tγ γ)
  (hWc : ContinuousOn Wc {t | (t : ℝ≥0∞) < Tγ}) (hWc0 : Wc 0 = 0)
  (hΓ : IsGeneratingTrace Wrel TΓ Γ)
  (hWrel : ContinuousOn Wrel {t | (t : ℝ≥0∞) < TΓ}) (hWrel0 : Wrel 0 = 0)
  {U : ℝ → ℝ} {σ : ℝ} (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ)
  {B : ℝ≥0} (hBT : (B : ℝ≥0∞) < Tγ)
  (hcapT : ((relClock U σ (fun q : ℝ => Wc q.toNNReal) B).toNNReal : ℝ≥0∞) < TΓ)
  (hsm : StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t) (Icc 0 B))
  (hac : ContinuousOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t) (Icc 0 B))
  (ha0 : relClock U σ (fun q : ℝ => Wc q.toNNReal) 0 = 0)
  (hK : ∀ t ∈ Icc 0 B,
    QuantumZipper.fwdHull (fun q : ℝ => Wrel q.toNNReal)
      (relClock U σ (fun q : ℝ => Wc q.toNNReal) t) =
        relMap U σ '' QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t)
  (hdom : ∀ t ∈ Icc 0 B, ∀ z ∈ QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t,
    -z⁻¹ ∉ QuantumZipper.fwdHull U σ)
  (hγdom : ∀ t ∈ Icc 0 B, γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U σ)

include hγ hWc hWc0 hΓ hWrel hWrel0 hU hU0 hσ hBT hcapT hsm hac ha0 hK hdom hγdom

/-- The actual domain restriction in `prefixImage` gives the finite
relative upper trace carrier, without complete-trace hypotheses. -/
theorem jointChart_prefix_eq_of_finite {v : ℝ≥0} (hv : v < B) :
    (GW2JointKernel.jointChart U σ).1 ''
        (γ '' Icc 0 v ∩ (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U σ)) =
      Γ '' Icc 0 (relClock U σ (fun q : ℝ => Wc q.toNNReal) v).toNNReal ∩ H := by
  rw [RootE13.prefix_inter_jointDomain_eq (fun r hr => hγdom r ⟨zero_le, hr.2.trans hv.le⟩)]
  change relMap U σ '' (γ '' Icc 0 v ∩ H) = _
  exact relMap_upper_prefix_eq_of_finite hγ hWc hWc0 hΓ hWrel hWrel0 hU hU0 hσ
    hBT hcapT hsm hac ha0 hK hdom hγdom hv

/-- The intrinsic relative clock evaluates the literal capacity of the
finite physical prefix in the joint chart. -/
theorem capOf_jointChart_prefix_of_finite {v : ℝ≥0} (hv : v < B) :
    capOf ((GW2JointKernel.jointChart U σ).1 ''
        (γ '' Icc 0 v ∩ (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull U σ))) =
      relClock U σ (fun q : ℝ => Wc q.toNNReal) v := by
  have hvB : v ∈ Icc 0 B := ⟨zero_le, hv.le⟩
  have hB : B ∈ Icc 0 B := ⟨zero_le, le_rfl⟩
  have hnonneg : 0 ≤ relClock U σ (fun q : ℝ => Wc q.toNNReal) v := by
    have := hsm.monotoneOn (show (0 : ℝ≥0) ∈ Icc 0 B from ⟨le_rfl, zero_le⟩) hvB zero_le
    simpa only [NNReal.coe_zero, ha0] using this
  have hvT : ((relClock U σ (fun q : ℝ => Wc q.toNNReal) v).toNNReal : ℝ≥0∞) < TΓ :=
    (ENNReal.coe_le_coe.mpr (Real.toNNReal_mono (hsm.monotoneOn hvB hB hv.le))).trans_lt hcapT
  rw [jointChart_prefix_eq_of_finite hγ hWc hWc0 hΓ hWrel hWrel0 hU hU0 hσ
    hBT hcapT hsm hac ha0 hK hdom hγdom hv,
    capOf_upper_prefix_of_isGeneratingTrace hΓ hWrel hWrel0 hvT,
    Real.coe_toNNReal _ hnonneg]

end InteractingSLE.Theorem14.GW2TipSystem.RootF14
