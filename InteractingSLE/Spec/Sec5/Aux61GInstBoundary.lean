/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstMean

/-!
# Boundary values of the deterministic correction in the restart mean

Packet PROVE-AUX61-GLUEINST. On a continuous inverse-chart access into the
cutoff neighbourhood, the explicit mean has the canonical single-line germ.
On an old real access, its difference from the single-line mean and `q`
vanishes. These are the deterministic halves of the boundary comparison.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)
open scoped NNReal ENNReal ComplexConjugate

namespace InteractingSLE.Sec5.Aux61GInst

open Restart.FlowStopIdentCMI (CMCut)
open Restart.FlowLocalityGen
open Aux61Win (IsCutoffOn meanF)

section Boundary

variable {κ : ℝ} {v q : ℂ → ℝ} {F : CMCut} {N : Set ℂ} {O : Set ℝ}
  (hF : IsCutoffOn F q N O) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
  {t : ℝ} (ht : 0 ≤ t) (hKN : closure (fwdHull w t) ⊆ N)
  {Ψ : ℂ → ℂ} (hΨ : EqOn Ψ (fwdMapInv w t) H) (hΨc : ContinuousOn Ψ Hbar)

include hF hw hw0 ht hKN hΨ hΨc

/-- The Green potential used in the explicit mean vanishes at every continuous
inverse-chart boundary access. -/
theorem tendsto_greenPot_boundary (x : ℝ) :
    Tendsto (fun ξ => GB7a.greenPot w (H.indicator (QuantumZipper.K3.greenDensity F.f)) t (Ψ ξ))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  rw [greenPot_eq_aliveGreenPot hF hKN]
  exact tendsto_aliveGreenPot_boundary F hw hw0 ht hΨ hΨc x

/-- On the cutoff neighbourhood, the deterministic mean has the canonical
single-line boundary germ, including the new slit sides. -/
theorem tendsto_meanF_sub_couplingMean (x : ℝ) (hx : Ψ x ∈ N) :
    Tendsto (fun ξ => meanF κ v q F w t (Ψ ξ) - couplingMean κ w t v (Ψ ξ))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hlim := ((hΨc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto
  have hN : ∀ᶠ ξ in 𝓝[H] (x : ℂ), Ψ ξ ∈ N := hlim (hF.isOpen.mem_nhds hx)
  refine (tendsto_greenPot_boundary hF hw hw0 ht hKN hΨ hΨc x).congr' ?_
  filter_upwards [hN, self_mem_nhdsWithin] with ξ hξN hξH
  have hξ : Ψ ξ ∈ H := by
    rw [hΨ hξH]
    exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 ht hξH).1
  rw [meanF, hF.eq _ hξN hξ]
  ring

/-- On an old real access, the deterministic correction has the boundary value
`q`: subtracting both `q` and the single-line mean leaves zero. -/
theorem tendsto_meanF_sub_couplingMean_sub_q (x : ℝ) (hx : (Ψ x).im = 0) :
    Tendsto (fun ξ => meanF κ v q F w t (Ψ ξ) - couplingMean κ w t v (Ψ ξ) - q (Ψ ξ))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have hconj : conj (Ψ x) = Ψ x := Complex.ext (by simp) (by simp [hx])
  have hF0 : F.f (Ψ x) = 0 := by
    have he := F.odd (Ψ x)
    rw [hconj] at he
    linarith only [he]
  have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have hlim := ((hΨc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto
  have hf := (F.smooth.continuous.tendsto (Ψ x)).comp hlim
  rw [hF0] at hf
  have hg := (tendsto_greenPot_boundary hF hw hw0 ht hKN hΨ hΨc x).sub hf
  rw [sub_zero] at hg
  refine hg.congr' (Eventually.of_forall fun ξ => ?_)
  dsimp only [Function.comp_apply]
  rw [meanF]
  ring

end Boundary

end InteractingSLE.Sec5.Aux61GInst
