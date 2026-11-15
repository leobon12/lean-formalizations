/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootE13Single

/-!
# The actual first root capacity from the pre-contact relative hulls

Packet PROVE-T14-GW2ROOT2. The one-entry canonical physical prefix is
identified by its generating trace, and its regularized joint-chart image
by GB6's relative hulls. This proves the initial normalized `capR` value.
The GB6 witnesses for the actual root remain explicit inputs; no capacity
identity or prefix-image identity is an input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE13

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

variable {Wc Wrel : ℝ≥0 → ℝ} {U : ℝ → ℝ} {σ : ℝ} {Tc : ℝ≥0∞}
  {γ Γ : ℝ≥0 → ℂ}
  (hWc : Continuous Wc) (hWc0 : Wc 0 = 0)
  (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ)
  (hγ : IsGeneratingTrace Wc ⊤ γ)
  (hWrel : Continuous Wrel) (hWrel0 : Wrel 0 = 0) (hΓ : IsGeneratingTrace Wrel ⊤ Γ)
  (hsm : StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t)
    {t | (t : ℝ≥0∞) < Tc})
  (hac : ContinuousOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t)
    {t | (t : ℝ≥0∞) < Tc})
  (hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ relClock U σ (fun q : ℝ => Wc q.toNNReal) t)
  (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
    QuantumZipper.fwdHull (fun q : ℝ => Wrel q.toNNReal)
      (relClock U σ (fun q : ℝ => Wc q.toNNReal) t) =
        relMap U σ '' QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t)
  (hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc →
    ∀ z ∈ QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t,
      -z⁻¹ ∉ QuantumZipper.fwdHull U σ)
  (hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → γ t ∈ H →
    -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U σ)
  (ha0 : relClock U σ (fun q : ℝ => Wc q.toNNReal) 0 = 0)

include hWc hWc0 hU hU0 hσ hγ hWrel hWrel0 hΓ hsm hac hnn hK hdom hγdom ha0

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (Wcf : ℝ≥0 → Ω → ℝ)
  (ζ' : Ω → ℝ≥0∞) (s : ℝ≥0) (θ : ℝ) (v : ℝ≥0) (ω : Ω)
  (hfirst : (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1 = Wc)
  (hlife : (v : ℝ≥0∞) ≤ (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2)
  (hchart : (fun q : ℝ => regW s Wcf ζ' q.toNNReal ω) = U) (hs : (s : ℝ) = σ)
  (hv : (v : ℝ≥0∞) < Tc)

include hfirst hlife hchart hs hv

/-- The actual regularized one-entry prefix image is the relative upper
trace prefix. The physical prefix identity is proved from canonical data. -/
theorem prefixImage_single_eq :
    prefixImage hκ h12p βA b jumps c₀ h (regW s Wcf ζ') s 0 [(θ, v)] ω =
      Γ '' Icc 0 (relClock U σ (fun q : ℝ => Wc q.toNNReal) v).toNNReal ∩ H := by
  have hgen : IsGeneratingTrace
      (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1
      (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2 γ := by
    rw [hfirst]
    exact hγ.mono_horizon le_top
  have hw : ContinuousOn (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1
      {t | (t : ℝ≥0∞) ≤ (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2} := by
    rw [hfirst]
    exact hWc.continuousOn
  have hw0 : (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1 0 = 0 := by
    rw [hfirst, hWc0]
  unfold prefixImage
  rw [prefixSet_single_eq_prefix hκ h12p βA b jumps c₀ h θ v ω hgen hw hw0 hlife, hchart, hs]
  exact jointChart_prefix_eq hWc hWc0 hU hU0 hσ hγ hWrel hWrel0 hΓ
    hsm hac hnn hK hdom hγdom ha0 hv

/-- The actual regularized one-entry capacity equals its relative clock;
no boundedness, attachment or carrier identity is assumed. -/
theorem capOf_prefixImage_single :
    capOf (prefixImage hκ h12p βA b jumps c₀ h (regW s Wcf ζ') s 0 [(θ, v)] ω) =
      relClock U σ (fun q : ℝ => Wc q.toNNReal) v := by
  have himg := prefixImage_single_eq hWc hWc0 hU hU0 hσ hγ hWrel hWrel0 hΓ
    hsm hac hnn hK hdom hγdom ha0 hκ h12p βA b jumps c₀ h Wcf ζ' s θ v ω
    hfirst hlife hchart hs hv
  have hraw := jointChart_prefix_eq hWc hWc0 hU hU0 hσ hγ hWrel hWrel0 hΓ
    hsm hac hnn hK hdom hγdom ha0 hv
  exact (congrArg capOf (himg.trans hraw.symm)).trans
    (capOf_jointChart_prefix hWc hWc0 hU hU0 hσ hγ hWrel hWrel0 hΓ
      hsm hac hnn hK hdom hγdom ha0 hv)

/-- At an admissible original root, the initial normalized `capR` is
exactly the dyadically scaled relative clock of its canonical first piece. -/
theorem capR_nil_eq_relClock {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q)
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
  have hc := capOf_prefixImage_single hWc hWc0 hU hU0 hσ hγ hWrel hWrel0 hΓ
    hsm hac hnn hK hdom hγdom ha0 hκ h12p βA b jumps c₀ h Wcf ζ' s θ v ω
    hfirst hlife hchart hs hv
  simp only [capR, entryList, List.map_nil, schedCap]
  rw [capV, ite_eq_left hadm, schedOf_nil, hroot, hentry, hc]

end InteractingSLE.Theorem14.GW2TipSystem.RootE13
