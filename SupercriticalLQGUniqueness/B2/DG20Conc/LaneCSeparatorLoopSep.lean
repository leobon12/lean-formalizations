import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorReparam
import QuantumZipper.Proofs.Complex.TopoEilenberg

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Topology
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 
theorem laneC_ratio_loop_separates_points
    {σ : ℝ → ℂ} (hσ : ContinuousOn σ (Icc (0 : ℝ) 1))
    (hclosed : σ 0 = σ 1) {c v : ℂ}
    {G : C(unitInterval, ℂ)} (hG : ∀ u, G u ≠ 0)
    (hGdef : ∀ u, G u = (σ u - c) / (σ u - v))
    (hdeg : QuantumZipper.CA.Topo.loopDeg G hG ≠ 0) :
    v ∉ connectedComponentIn (σ '' Icc (0 : ℝ) 1)ᶜ c := by
  let J : Set ℂ := σ '' Icc (0 : ℝ) 1
  have hJ : IsCompact J := isCompact_Icc.image_of_continuousOn hσ
  intro hcomp
  obtain ⟨L, hLc, hLexp⟩ :=
    QuantumZipper.CA.Topo.hasLogOn_of_not_separates hJ hcomp
  let ℓ : unitInterval → ℂ := fun u => L (σ u)
  have hℓ : Continuous ℓ := by
    have hc : Continuous (fun u : unitInterval => σ u) :=
      hσ.comp_continuous continuous_subtype_val (fun u => u.2)
    exact hLc.comp_continuous hc (fun u => mem_image_of_mem σ u.2)
  have hℓexp : ∀ u : unitInterval, Complex.exp (ℓ u) = G u := by
    intro u
    rw [hLexp _ (mem_image_of_mem σ u.2), hGdef]
  have hGc : G 0 = G 1 := by
    rw [hGdef, hGdef]
    simpa using congrArg (fun z : ℂ => (z - c) / (z - v)) hclosed
  have hdegEq := QuantumZipper.CA.Topo.loopDeg_eq_of_lift G hG hGc hℓ hℓexp
  have hℓeq : ℓ 1 = ℓ 0 := by simpa [ℓ] using congrArg L hclosed.symm
  rw [hℓeq, sub_self] at hdegEq
  have : QuantumZipper.CA.Topo.loopDeg G hG = 0 := by
    have hmul : ((QuantumZipper.CA.Topo.loopDeg G hG : ℤ) : ℂ) *
        (2 * Real.pi * Complex.I) = 0 := hdegEq.symm
    have hzero := (mul_eq_zero.mp hmul).resolve_right
      QuantumZipper.CA.Topo.two_pi_I_ne_zero'
    exact_mod_cast hzero
  exact hdeg this

end SupercriticalLQGUniqueness.B2.DG20Conc
