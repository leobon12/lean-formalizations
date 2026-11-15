/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootM17Trace
import InteractingSLE.Spec.Supplement.GW2RootF14Local

/-!
# The first canonical root clock from the original trace data

Packet PROVE-T14-GW2ROOT2. The relative generating trace and all clock,
separation and hull data are constructed. The canonical pair itself
supplies driver identification and available lifetime. Only the original
chart and canonical generating traces, driver regularity and the live
pre-contact cutoff occur as mathematical premises.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootM17

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

/-- The actual initial normalized root clock follows from the original
canonical trace and the live interior chart-tip event. No relative
generating trace, capacity-clock property or hull identity is assumed. -/
theorem capR_nil_eq_relClock_from_canonical_trace
    {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
    (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
    (h : Ω → DistOn upperHalfPlaneOpens) (θ : ℝ) (v : ℝ≥0) (ω : Ω)
    (Wcf : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (fun t => Wcf t ω) (ζ' ω) α)
    (hWcf : Continuous (fun t => Wcf t ω)) (hWcf0 : Wcf 0 ω = 0) (hζ : ζ' ω = ⊤)
    (s : ℝ≥0) (hsH : α s ∈ H) {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (hroot : rootPt r.1 = 0) (hentry : rootEntry r.1 = (θ, v)) :
    let E := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω
    ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace E.1 E.2 γ →
      ContinuousOn E.1 {t | (t : ℝ≥0∞) < E.2} → E.1 0 = 0 →
      (v : ℝ≥0∞) < min
        (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
          ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) E.2 →
      capR hκ h12p βA b jumps c₀ h Wcf ζ' s r [] ω =
        4 ^ r.2 * relClock (fun q : ℝ => regW s Wcf ζ' q.toNNReal ω) s (Ito.rpath E.1) v := by
  dsimp only
  intro γ hγ hW hW0 hv
  let E := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω
  let U : ℝ → ℝ := fun q => regW s Wcf ζ' q.toNNReal ω
  change IsGeneratingTrace E.1 E.2 γ at hγ
  change ContinuousOn E.1 {t | (t : ℝ≥0∞) < E.2} at hW
  change E.1 0 = 0 at hW0
  have hs : (s : ℝ≥0∞) < ζ' ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨B, V, Γ, hvB, hBS, hV, hV0, hΓ, ha0, hm, hc, hK⟩ :=
    exists_regW_relative_trace_before_contact Wcf ζ' ω hα hWcf.continuousOn hWcf0 hs hsH hγ hW hW0 hv
  have heU : U = Ito.rpath (fun t => Wcf t ω) := by
    funext q
    exact regW_eq s hζ hWcf0 hWcf q.toNNReal
  have hU : Continuous U := by rw [heU]; exact hWcf.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by
    rw [heU]
    simpa only [Ito.rpath, Real.toNNReal_zero] using hWcf0
  have hdom : ∀ t ∈ Icc 0 B, ∀ z ∈ QuantumZipper.fwdHull (Ito.rpath E.1) t,
      -z⁻¹ ∉ QuantumZipper.fwdHull U s := by
    intro t ht z hz
    exact RootG15.inv_notMem_regW_fwdHull_before_contact Wcf ζ' ω hα hWcf.continuousOn hWcf0 hs
      hγ hW hW0 t ((ENNReal.coe_le_coe.mpr ht.2).trans_lt hBS) z hz
  have hγdom : ∀ t ∈ Icc 0 B, γ t ∈ H → -(γ t)⁻¹ ∉ QuantumZipper.fwdHull U s := by
    intro t ht hHt
    have htT : (t : ℝ≥0∞) < E.2 :=
      (ENNReal.coe_le_coe.mpr ht.2).trans_lt (lt_min_iff.mp hBS).2
    exact hdom t ht (γ t) (Sec5.Aux61R2.WinFibre.mem_fwdHull_of_isGeneratingTrace hγ htT hHt)
  exact RootF14.capR_nil_eq_relClock_of_finite hκ h12p βA b jumps c₀ h θ v ω
    hγ hW hW0 rfl (lt_min_iff.mp hv).2.le hΓ hV.continuousOn hV0
    hU hU0 s.coe_nonneg (lt_min_iff.mp hBS).2 ENNReal.coe_lt_top hm hc ha0 hK hdom hγdom
    Wcf ζ' s rfl rfl hvB r hroot hentry

end InteractingSLE.Theorem14.GW2TipSystem.RootM17
