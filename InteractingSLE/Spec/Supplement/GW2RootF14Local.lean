/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootF14Actual
import InteractingSLE.Spec.Sec5.Aux61R2Obstruction

/-!
# The initial root clock strictly before contact and both lifetimes

Packet PROVE-T14-GW2ROOT2. Clock continuity supplies the protected finite
window. The final theorem assumes only the pre-contact geometric data,
the original finite traces, and the two live-time conditions at the cutoff.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF14

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

/-- A continuous clock with a live value admits a strictly later physical
cutoff that is still before both the physical and relative horizons. -/
theorem exists_clock_buffer {a : ℝ≥0 → ℝ} {S T : ℝ≥0∞} {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < S) (hac : ContinuousWithinAt a {r | (r : ℝ≥0∞) < S} v)
    (ha : ((a v).toNNReal : ℝ≥0∞) < T) :
    ∃ B : ℝ≥0, v < B ∧ (B : ℝ≥0∞) < S ∧ ((a B).toNNReal : ℝ≥0∞) < T := by
  have hN : {r : ℝ≥0 | (r : ℝ≥0∞) < S} ∈ 𝓝 v :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hv
  have hc : ContinuousAt (fun r => ((a r).toNNReal : ℝ≥0∞)) v :=
    ENNReal.continuous_coe.continuousAt.comp
      (continuous_real_toNNReal.continuousAt.comp (hac.continuousAt hN))
  have hcap : ∀ᶠ r in 𝓝 v, ((a r).toNNReal : ℝ≥0∞) < T :=
    hc.eventually (isOpen_Iio.mem_nhds ha)
  have hboth : ∀ᶠ (r : ℝ≥0) in 𝓝 v, (r : ℝ≥0∞) < S ∧ ((a r).toNNReal : ℝ≥0∞) < T :=
    Filter.Eventually.and hN hcap
  obtain ⟨B, hB, hvB⟩ := ((hboth.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : Ioi v ∈ 𝓝[>] v)).exists
  exact ⟨B, hvB, hB.1, hB.2⟩

/-- The actual first normalized root clock before contact, with finite
generating lifetimes. The protected window, complete models and tip domain
condition are proved from the stated pre-contact hull data. -/
theorem capR_nil_eq_relClock_before_contact
    {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
    (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
    (h : Ω → DistOn upperHalfPlaneOpens) (θ : ℝ) (v : ℝ≥0) (ω : Ω)
    {Wc Wrel : ℝ≥0 → ℝ} {Tγ TΓ Tc : ℝ≥0∞} {γ Γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace Wc Tγ γ)
    (hWc : ContinuousOn Wc {t | (t : ℝ≥0∞) < Tγ}) (hWc0 : Wc 0 = 0)
    (hfirst : (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).1 = Wc)
    (hlife : (v : ℝ≥0∞) ≤ (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω).2)
    (hΓ : IsGeneratingTrace Wrel TΓ Γ)
    (hWrel : ContinuousOn Wrel {t | (t : ℝ≥0∞) < TΓ}) (hWrel0 : Wrel 0 = 0)
    {U : ℝ → ℝ} {σ : ℝ} (hU : Continuous U) (hU0 : U 0 = 0) (hσ : 0 ≤ σ)
    (hsm : StrictMonoOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t)
      {t | (t : ℝ≥0∞) < min Tc Tγ})
    (hac : ContinuousOn (fun t : ℝ≥0 => relClock U σ (fun q : ℝ => Wc q.toNNReal) t)
      {t | (t : ℝ≥0∞) < min Tc Tγ})
    (ha0 : relClock U σ (fun q : ℝ => Wc q.toNNReal) 0 = 0)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < min Tc Tγ →
      QuantumZipper.fwdHull (fun q : ℝ => Wrel q.toNNReal)
        (relClock U σ (fun q : ℝ => Wc q.toNNReal) t) =
          relMap U σ '' QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t)
    (hdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < min Tc Tγ →
      ∀ z ∈ QuantumZipper.fwdHull (fun q : ℝ => Wc q.toNNReal) t,
        -z⁻¹ ∉ QuantumZipper.fwdHull U σ)
    (Wcf : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (s : ℝ≥0)
    (hchart : (fun q : ℝ => regW s Wcf ζ' q.toNNReal ω) = U) (hs : (s : ℝ) = σ)
    (hv : (v : ℝ≥0∞) < min Tc Tγ)
    (hvrel : ((relClock U σ (fun q : ℝ => Wc q.toNNReal) v).toNNReal : ℝ≥0∞) < TΓ)
    {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q)
    (hroot : rootPt r.1 = 0) (hentry : rootEntry r.1 = (θ, v)) :
    capR hκ h12p βA b jumps c₀ h Wcf ζ' s r [] ω =
      4 ^ r.2 * relClock U σ (fun q : ℝ => Wc q.toNNReal) v := by
  obtain ⟨B, hvB, hBS, hBTΓ⟩ := exists_clock_buffer hv (hac v hv) hvrel
  have hsub : Icc 0 B ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < min Tc Tγ} :=
    fun t ht => (ENNReal.coe_le_coe.mpr ht.2).trans_lt hBS
  have hγdom : ∀ t : ℝ≥0, (t : ℝ≥0∞) < min Tc Tγ → γ t ∈ H →
      -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U σ := by
    intro t ht htH
    exact hdom t ht (γ t) (Sec5.Aux61R2.WinFibre.mem_fwdHull_of_isGeneratingTrace
      hγ (ht.trans_le (min_le_right _ _)) htH)
  exact capR_nil_eq_relClock_of_finite hκ h12p βA b jumps c₀ h θ v ω hγ hWc hWc0
    hfirst hlife hΓ hWrel hWrel0 hU hU0 hσ (hBS.trans_le (min_le_right _ _)) hBTΓ
    (hsm.mono hsub) (hac.mono hsub) ha0
    (fun t ht => hK t (hsub ht)) (fun t ht => hdom t (hsub ht))
    (fun t ht => hγdom t (hsub ht)) Wcf ζ' s hchart hs hvB r hroot hentry

end InteractingSLE.Theorem14.GW2TipSystem.RootF14
