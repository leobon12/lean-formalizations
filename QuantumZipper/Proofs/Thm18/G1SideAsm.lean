import QuantumZipper.Proofs.Thm18.G1SideIdent
import QuantumZipper.Proofs.Thm18.G1SideDilE
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (10): the offset identity at one circle, from the family facts

For the pulled-back canonical field `x = coordChange (rescale w Q s) ψ Q` (RC3 at the circle),
and a family member `Ψq = s ψ(c ·)` on `ℍ` (exact at the dyadic circle `fc(t/c, 2^{-k})`, with the
continuum smoothing limit of `w` on the pushed circle), the regularized value of `x` on the offset
circle `fc(t, c 2^{-k})` is the dyadic average of the family member at `t/c`, minus `Q log c`
(`offset_hE`). Scale consistency comes from `Thm18Asm.G1.scaleConsistentAt_of_continuum`; the rest
is `G1Side.evalReg_offset_eq_avg_family`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

open Thm18Asm

theorem ofReal_mem_Hbar_side (t : ℝ) : ((t : ℝ) : ℂ) ∈ Hbar := by
  show (0 : ℝ) ≤ ((t : ℝ) : ℂ).im
  simp

/-- **The offset identity at one circle.** -/
theorem offset_hE {γ : ℝ} {w : FieldSample} (hw : IsRegularSample w) {ψ Ψq : ℂ → ℂ}
    (hψm : Measurable ψ) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : ∀ z ∈ H, ψ z ∈ Hbar)
    (hψi : ∀ d ∈ Hbar, ∀ r > 0, Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d r))
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hq : EqOn Ψq (fun z => (s : ℂ) * ψ ((c : ℂ) * z)) H)
    (hRC3 : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale w (Qc γ) s) ψ (Qc γ)) (foldedCircle d r) =
        coordChange (rescale w (Qc γ) s) ψ (Qc γ) (foldedCircle d r))
    {k : ℕ} {t : ℝ}
    (hexq : avgReg (coordChange w Ψq (Qc γ)) k ((t / c : ℝ) : ℂ) =
      coordChange w Ψq (Qc γ) (foldedCircle ((t / c : ℝ) : ℂ) (radius k)))
    (hint : ∀ σ : ℝ, 0 < σ → Integrable (fun v => evalReg w (foldedCircle v σ))
      ((foldedCircle ((t / c : ℝ) : ℂ) (radius k)).map Ψq))
    (hlim : ∃ L : ℝ, Tendsto (fun σ => ∫ v, evalReg w (foldedCircle v σ)
      ∂((foldedCircle ((t / c : ℝ) : ℂ) (radius k)).map Ψq)) (𝓝[>] 0) (𝓝 L)) :
    evalReg (coordChange (rescale w (Qc γ) s) ψ (Qc γ)) (foldedCircle (t : ℂ) (c * radius k)) =
      avgReg (coordChange w Ψq (Qc γ)) k ((t / c : ℝ) : ℂ) - Qc γ * Real.log c := by
  have hr := radius_pos k
  have hcr : 0 < c * radius k := mul_pos hc hr
  have hmS : Measurable fun z : ℂ => (s : ℂ) * z := measurable_const_mul _
  have hmC : Measurable fun z : ℂ => (c : ℂ) * z := measurable_const_mul _
  have hfc : (foldedCircle ((t / c : ℝ) : ℂ) (radius k)).map (fun z => (c : ℂ) * z) =
      foldedCircle (t : ℂ) (c * radius k) := by
    rw [WedgeTK.fc_map_mul _ _ hc]
    congr 1
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    field_simp
  have hmap : ((foldedCircle (t : ℂ) (c * radius k)).map ψ).map (fun z => (s : ℂ) * z) =
      (foldedCircle ((t / c : ℝ) : ℂ) (radius k)).map Ψq := by
    rw [Measure.map_map hmS hψm, ← hfc, Measure.map_map (hmS.comp hψm) hmC]
    refine Measure.map_congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H ((t / c : ℝ) : ℂ) hr] with z hz
    exact (hq hz).symm
  have hν : ∀ᵐ u ∂((foldedCircle (t : ℂ) (c * radius k)).map ψ), u ∈ Hbar := by
    have hHm : MeasurableSet Hbar :=
      (isClosed_le continuous_const Complex.continuous_im).measurableSet
    refine (ae_map_iff hψm.aemeasurable hHm).2 ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H (t : ℂ) hcr] with z hz
    exact hψH z hz
  obtain ⟨L, hL⟩ := hlim
  have hsc : G1.ScaleConsistentAt w (Qc γ) s ((foldedCircle (t : ℂ) (c * radius k)).map ψ) :=
    G1.scaleConsistentAt_of_continuum hw (Qc γ) hs hν (by rw [hmap]; exact hint)
      (L := L) (by rw [hmap]; exact hL)
  have hd : ∀ᵐ z ∂foldedCircle (t : ℂ) (c * radius k), deriv ψ z ≠ 0 := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H (t : ℂ) hcr] with z hz
    exact hψ0 z hz
  have hRE := g1z2_regEq_of_eqOn w hq (Qc γ)
  have hex : avgReg (coordChange w (fun z => (s : ℂ) * ψ ((c : ℂ) * z)) (Qc γ)) k
      ((t / c : ℝ) : ℂ) =
      coordChange w (fun z => (s : ℂ) * ψ ((c : ℂ) * z)) (Qc γ)
        (foldedCircle ((t / c : ℝ) : ℂ) (radius k)) := by
    rw [← hRE k, hexq, g1zMeas_coordChange_fc_congr w hq (Qc γ) _ hr]
  have h := evalReg_offset_eq_avg_family (γ := γ) hψm hs hc
    (hRC3 _ (ofReal_mem_Hbar_side t) _ hcr) hsc hd
    (hψi _ (ofReal_mem_Hbar_side t) _ hcr) hex
  rw [h, ← hRE k]

end G1Side
end QuantumZipper
