/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootF14Capacity

/-!
# The actual first root clock with finite generating lifetimes

Packet PROVE-T14-GW2ROOT2. Only a protected finite prefix of the actual
canonical driver is used. Complete physical and relative trace witnesses
and global continuity of those two drivers are no longer hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF14

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (θ : ℝ) (v : ℝ≥0) (ω : Ω)
  {Wc : ℝ≥0 → ℝ} {Tγ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace Wc Tγ γ)
  (hWc : ContinuousOn Wc {t | (t : ℝ≥0∞) < Tγ}) (hWc0 : Wc 0 = 0)
  (hfirst : (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1 = Wc)
  (hlife : (v : ℝ≥0∞) ≤ (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2)

include hγ hWc hWc0 hfirst hlife

/-- A trace only through a later protected horizon identifies the actual
canonical first physical prefix. No continuity at the raw lifetime is used. -/
theorem prefixSet_single_eq_of_finite (hvT : (v : ℝ≥0∞) < Tγ) :
    prefixSet hκ h12p βA b jumps c₀ h 0 [(θ, v)] ω = γ '' Icc 0 v := by
  have hc : ContinuousOn Wc {t | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} :=
    hWc.mono (fun r hr => hr.trans_lt hvT)
  have hmodel := RootE13.physSet_single_eq_prefix κ b jumps true θ
    (fun _ => (Wc, (v : ℝ≥0∞))) (hγ.mono_horizon hvT.le) hc hWc0 le_rfl
  rw [CounterflowRange.physSet_single, min_self] at hmodel
  have hs : schedSpec 0 [(θ, v)] = (0, true, [Sum.inl (θ, (v : ℝ≥0∞))]) := by
    simp only [schedSpec, scheduleProgram, tsub_zero]
  rw [hs] at hfirst hlife
  unfold prefixSet
  rw [hs, CounterflowRange.physSet_single, min_eq_left hlife, hfirst]
  exact hmodel

variable {Wrel : ℝ≥0 → ℝ} {TΓ : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}
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
  (Wcf : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (s : ℝ≥0)
  (hchart : (fun q : ℝ => regW s Wcf ζ' q.toNNReal ω) = U) (hs : (s : ℝ) = σ)
  (hv : v < B)

include hγ hWc hWc0 hfirst hlife hΓ hWrel hWrel0 hU hU0 hσ hBT hcapT hsm hac ha0 hK hdom hγdom
  hchart hs hv

/-- The actual regularized first image is a finite relative upper trace
prefix, derived from the finite generating traces and relative hulls. -/
theorem prefixImage_single_eq_of_finite :
    prefixImage hκ h12p βA b jumps c₀ h (regW s Wcf ζ') s 0 [(θ, v)] ω =
      Γ '' Icc 0 (relClock U σ (fun q : ℝ => Wc q.toNNReal) v).toNNReal ∩ H := by
  have hvT : (v : ℝ≥0∞) < Tγ := (ENNReal.coe_le_coe.mpr hv.le).trans_lt hBT
  unfold prefixImage
  rw [prefixSet_single_eq_of_finite hκ h12p βA b jumps c₀ h θ v ω hγ hWc hWc0 hfirst hlife hvT,
    hchart, hs]
  exact jointChart_prefix_eq_of_finite hγ hWc hWc0 hΓ hWrel hWrel0 hU hU0 hσ
    hBT hcapT hsm hac ha0 hK hdom hγdom hv

/-- Literal capacity of the actual regularized first image, with finite
lifetimes and no assumed physical or chart carrier identity. -/
theorem capOf_prefixImage_single_of_finite :
    capOf (prefixImage hκ h12p βA b jumps c₀ h (regW s Wcf ζ') s 0 [(θ, v)] ω) =
      relClock U σ (fun q : ℝ => Wc q.toNNReal) v := by
  have himg := prefixImage_single_eq_of_finite hκ h12p βA b jumps c₀ h θ v ω hγ hWc hWc0
    hfirst hlife hΓ hWrel hWrel0 hU hU0 hσ hBT hcapT hsm hac ha0 hK hdom hγdom
    Wcf ζ' s hchart hs hv
  have hraw := jointChart_prefix_eq_of_finite hγ hWc hWc0 hΓ hWrel hWrel0 hU hU0 hσ
    hBT hcapT hsm hac ha0 hK hdom hγdom hv
  exact (congrArg capOf (himg.trans hraw.symm)).trans
    (capOf_jointChart_prefix_of_finite hγ hWc hWc0 hΓ hWrel hWrel0 hU hU0 hσ
      hBT hcapT hsm hac ha0 hK hdom hγdom hv)

/-- The actual initial normalized root clock with finite physical and
relative lifetimes. Initial admissibility follows from the root index. -/
theorem capR_nil_eq_relClock_of_finite {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q)
    (hroot : rootPt r.1 = 0) (hentry : rootEntry r.1 = (θ, v)) :
    capR hκ h12p βA b jumps c₀ h Wcf ζ' s r [] ω =
      4 ^ r.2 * relClock U σ (fun q : ℝ => Wc q.toNNReal) v := by
  have hadm : SchedAdm b jumps Θ Q (κ := κ) (rootPt r.1) (rootEntry r.1) [] := by
    refine ⟨Or.inl hroot, ?_⟩
    rw [schedOf_nil]
    refine ⟨?_, by simp⟩
    intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact ⟨r.1.2.1.property, r.1.2.2.property⟩
  have hc := capOf_prefixImage_single_of_finite hκ h12p βA b jumps c₀ h θ v ω hγ hWc hWc0
    hfirst hlife hΓ hWrel hWrel0 hU hU0 hσ hBT hcapT hsm hac ha0 hK hdom hγdom
    Wcf ζ' s hchart hs hv
  simp only [capR, entryList, List.map_nil, schedCap]
  rw [capV, ite_eq_left hadm, schedOf_nil, hroot, hentry, hc]

end InteractingSLE.Theorem14.GW2TipSystem.RootF14
