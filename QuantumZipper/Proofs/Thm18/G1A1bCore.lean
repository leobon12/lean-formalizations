import QuantumZipper.Proofs.Thm18.ExactClG1b
import QuantumZipper.Proofs.Thm18.RTBeurMass
import QuantumZipper.Proofs.Thm18.G1RegLogDeriv
import QuantumZipper.Proofs.RS.TraceRadial

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1A1b (core): the side exactness node at one sample, from the fixed-driver side RTX data

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71 (the side surface of `Z_{−ℓ} c` is the rerooted side surface; coordinate change (1.3));
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 2.1 (coordinate change of the field).
Route: D72 (`handoff/G4-CORE.md` §8, "G1 A1b reduction" and SideRTX).

Per sample and deterministically: if the unzipped field `U = coordChange Y f_t⁻¹ Q` is regular
with witness `F`, and for every folded circle the smoothed values `∫ F(·, ρ)` along the measure
`(f_t ∘ ψ)_* fc(d, s)` (`ψ` the OLD side map, a function of the driver only) converge, as the
continuous radius `ρ ↓ 0`, to the raw value `U((f_t ∘ ψ)_* fc(d, s))` (side round-trip exactness,
"SideRTX"), then the new side field satisfies the conclusion of `G1ZA1bSideExactArcStmt`.

* `evalReg_eq_of_tendsto_radius`: `evalReg` from a continuous-radius limit;
* `evalReg_rescale_eq_of_tendsto`: the same for the rescaled field (radii `a 2^{-k}`);
* `map_mul_sideMap_eq_fwdMap'`: `fc(d, s).map (a ψ') = fc(d', s').map (f_t ∘ ψ)` (no
  measurability of `f_t` needed);
* **`exact_of_sideRTX`**: the per-sample reduction, through `ExactCl.g1za1b_exact_of_push`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18
namespace G1A1b

open Thm18Asm ExactCl

theorem measurableSet_Hbar' : MeasurableSet Hbar :=
  (isClosed_le continuous_const Complex.continuous_im).measurableSet

/-- `evalReg` from the continuous-radius limit of the smoothed witness. -/
theorem evalReg_eq_of_tendsto_radius {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {ν : Measure ℂ} (hν : ∀ᵐ z ∂ν, z ∈ Hbar) {L : ℝ}
    (hL : Tendsto (fun ρ => ∫ z, F (z, ρ) ∂ν) (𝓝[>] 0) (𝓝 L)) : evalReg x ν = L := by
  have e : (fun k : ℕ => ∫ w, avgReg x k w ∂ν) = fun k => ∫ z, F (z, radius k) ∂ν :=
    funext fun k => integral_congr_ae (hν.mono fun z hz => (hF.2.1 k z hz).limUnder_eq)
  unfold evalReg
  rw [e]
  exact (hL.comp RegClosure.tendsto_radius_nhdsGT).limUnder_eq

/-- `evalReg` of the rescaled field from the continuous-radius limit at the dilated measure. -/
theorem evalReg_rescale_eq_of_tendsto {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (Q : ℝ) {a : ℝ} (ha : 0 < a) {ν : Measure ℂ} [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ Hbar) {L : ℝ}
    (hint : ∀ ρ : ℝ, 0 < ρ → Integrable (fun z => F (z, ρ)) (ν.map fun w => (a : ℂ) * w))
    (hL : Tendsto (fun ρ => ∫ z, F (z, ρ) ∂(ν.map fun w => (a : ℂ) * w)) (𝓝[>] 0) (𝓝 L)) :
    evalReg (rescale x Q a) ν = L + Q * Real.log a := by
  have hR := hF.rescale' Q ha
  have hemb : MeasurableEmbedding fun w : ℂ => (a : ℂ) * w :=
    (Homeomorph.mulLeft₀ (a : ℂ) (by exact_mod_cast ha.ne')).measurableEmbedding
  have hr : Tendsto (fun k : ℕ => a * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos ha (radius_pos k)⟩
    have := (tendsto_nhdsWithin_iff.1 RegClosure.tendsto_radius_nhdsGT).1.const_mul a
    simpa using this
  have hav : ∀ k : ℕ, ∀ z ∈ Hbar,
      avgReg (rescale x Q a) k z = F ((a : ℂ) * z, a * radius k) + Q * Real.log a :=
    fun k z hz => (hR.2.1 k z hz).limUnder_eq
  have e : ∀ k : ℕ, ∫ w, avgReg (rescale x Q a) k w ∂ν =
      ∫ z, F (z, a * radius k) ∂(ν.map fun w => (a : ℂ) * w) + Q * Real.log a := by
    intro k
    have hi : Integrable (fun w => F ((a : ℂ) * w, a * radius k)) ν :=
      (hemb.integrable_map_iff).1 (hint _ (mul_pos ha (radius_pos k)))
    rw [integral_congr_ae (hν.mono fun z hz => hav k z hz),
      integral_add hi (integrable_const _), hemb.integral_map, integral_const]
    simp
  unfold evalReg
  rw [funext e]
  exact ((hL.comp hr).add_const _).limUnder_eq

theorem affR_mem_H {β lam : ℝ} (hlam : 0 < lam) {v : ℂ} (hv : v ∈ H) : affR β lam v ∈ H := by
  show 0 < (affR β lam v).im
  have : 0 < v.im := hv
  unfold affR
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.add_im]
  positivity

/-- **Round-trip form of the new side measure**, without measurability of `f_t`:
`fc(d, s).map (a ψ') = fc(d', s').map (f_t ∘ ψ)`. -/
theorem map_mul_sideMap_eq_fwdMap' {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {ψ ψ' : ℂ → ℂ} {a β lam : ℝ} (hlam : 0 < lam) (hψ'm : Measurable ψ')
    (hmaps : ∀ v ∈ H, (a : ℂ) * ψ' v ∈ H)
    (hEq : EqOn (fun u => fwdMapInv W t ((a : ℂ) * ψ' (u + (β : ℂ)))) (fun u => ψ (u / (lam : ℂ))) H)
    (d : ℂ) {s : ℝ} (hs : 0 < s) :
    (foldedCircle d s).map (fun u => (a : ℂ) * ψ' u) =
      (foldedCircle (((lam⁻¹ : ℝ) : ℂ) * (d + ((-β : ℝ) : ℂ))) (lam⁻¹ * s)).map
        (fun w => fwdMap W t (ψ w)) := by
  set G : ℂ → ℂ := fun w => fwdMap W t (ψ w) with hG
  have hGaff : ∀ v ∈ H, G (affR β lam v) = (a : ℂ) * ψ' v := fun v hv => by
    simp only [hG]
    rw [← comp_eq_affR (F := fwdMapInv W t) hlam hEq hv]
    exact RS.fwdMap_fwdMapInv hW hW0 ht (hmaps v hv)
  have hs' : 0 < lam⁻¹ * s := mul_pos (inv_pos.2 hlam) hs
  have hGm : AEMeasurable G
      (foldedCircle (((lam⁻¹ : ℝ) : ℂ) * (d + ((-β : ℝ) : ℂ))) (lam⁻¹ * s)) := by
    have hm : Measurable fun w : ℂ => (a : ℂ) * ψ' ((lam : ℂ) * w + (β : ℂ)) :=
      measurable_const_mul _ |>.comp (hψ'm.comp ((measurable_const_mul _).add_const _))
    refine hm.aemeasurable.congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H _ hs'] with w hw
    have hv : (lam : ℂ) * w + (β : ℂ) ∈ H := by
      show 0 < ((lam : ℂ) * w + (β : ℂ)).im
      have : 0 < w.im := hw
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero]
      positivity
    have haff : affR β lam ((lam : ℂ) * w + (β : ℂ)) = w := by
      unfold affR
      have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
      push_cast
      field_simp
      ring
    rw [← hGaff _ hv, haff]
  calc (foldedCircle d s).map (fun u => (a : ℂ) * ψ' u)
      = (foldedCircle d s).map (G ∘ affR β lam) := by
        refine Measure.map_congr ?_
        filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with v hv
        exact (hGaff v hv).symm
    _ = ((foldedCircle d s).map (affR β lam)).map G :=
        (AEMeasurable.map_map_of_aemeasurable (by rwa [foldedCircle_map_affine hlam])
          (measurable_affR β lam).aemeasurable).symm
    _ = _ := by rw [foldedCircle_map_affine hlam]

/-- **Side round-trip exactness data at one time** (the SideRTX data): `U_t` is regular with
witness `F`, and along every `(f_t ∘ ψ)_* fc(d, s)` the smoothed witness is integrable and
converges, as the continuous radius `ρ ↓ 0`, to the raw value of `U_t`. -/
def SideRTXAt (Y : FieldSample) (Q : ℝ) (W : ℝ → ℝ) (t : ℝ) (ψ : ℂ → ℂ) : Prop :=
  ∃ F : ℂ × ℝ → ℝ, IsRegularWith (coordChange Y (fwdMapInv W t) Q) F ∧
    ∀ d ∈ Hbar, ∀ s : ℝ, 0 < s →
      (∀ ρ : ℝ, 0 < ρ → Integrable (fun z => F (z, ρ))
        ((foldedCircle d s).map fun w => fwdMap W t (ψ w))) ∧
      Tendsto (fun ρ => ∫ z, F (z, ρ) ∂((foldedCircle d s).map fun w => fwdMap W t (ψ w)))
        (𝓝[>] 0) (𝓝 (coordChange Y (fwdMapInv W t) Q
          ((foldedCircle d s).map fun w => fwdMap W t (ψ w))))

/-- **`G1ZA1bSideExactArcStmt` at one sample, from SideRTX at the unzipping time.** -/
theorem exact_of_sideRTX {Y : FieldSample} {Q : ℝ} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t a β lam : ℝ} (ht : 0 ≤ t) (ha : 0 < a) {ψ ψ' : ℂ → ℂ}
    (hreg : IsRegularSample (coordChange Y ψ Q))
    (hex : ∀ d ∈ Hbar, ∀ s > 0, evalReg (coordChange Y ψ Q) (foldedCircle d s) =
      coordChange Y ψ Q (foldedCircle d s))
    (hlam : 0 < lam) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hne : ∀ z ∈ H, deriv ψ z ≠ 0)
    (hint : ∀ (d : ℂ) (s : ℝ), 0 < s →
      Integrable (fun z => Real.log ‖deriv ψ z‖) (foldedCircle d s))
    (hEq : EqOn (fun u => fwdMapInv W t ((a : ℂ) * ψ' (u + (β : ℂ))))
      (fun u => ψ (u / (lam : ℂ))) H)
    (hψ'm : Measurable ψ') (hψ'd : DifferentiableOn ℂ ψ' H) (hψ'i : InjOn ψ' H)
    (hψ'H : MapsTo ψ' H H) (hR : SideRTXAt Y Q W t ψ) :
    ∀ e ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (coordChange (rescale (coordChange Y (fwdMapInv W t) Q) Q a) ψ' Q)
          (foldedCircle e r) =
        coordChange Y (fun u => fwdMapInv W t ((a : ℂ) * ψ' u)) Q (foldedCircle e r) := by
  obtain ⟨F, hU, hRTX⟩ := hR
  set f := fwdMapInv W t with hf
  have hfm : Measurable f := RTBeur.measurable_fwdMapInv_rt hW hW0 ht
  have hmaps : ∀ v ∈ H, (a : ℂ) * ψ' v ∈ H := fun v hv => by
    show 0 < ((a : ℂ) * ψ' v).im
    have : 0 < (ψ' v).im := hψ'H hv
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    positivity
  have haψm : Measurable fun u => (a : ℂ) * ψ' u := (measurable_const_mul _).comp hψ'm
  refine g1za1b_exact_of_push ha hreg hex hlam hψm hψd hne hint hEq hψ'm
    (fun _ _ => hfm.aemeasurable) fun d hd s hs => ?_
  set d' : ℂ := ((lam⁻¹ : ℝ) : ℂ) * (d + ((-β : ℝ) : ℂ)) with hd'
  have hd'H : d' ∈ Hbar := by
    show 0 ≤ d'.im
    have : 0 ≤ d.im := hd
    simp only [hd', Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im]
    positivity
  have hs' : 0 < lam⁻¹ * s := mul_pos (inv_pos.2 hlam) hs
  obtain ⟨hI, hT⟩ := hRTX d' hd'H _ hs'
  have hmap := map_mul_sideMap_eq_fwdMap' hW hW0 ht hlam hψ'm hmaps hEq d hs
  rw [← hmap] at hI hT
  have haeν : ∀ᵐ z ∂((foldedCircle d s).map fun u => (a : ℂ) * ψ' u), z ∈ Hbar :=
    (ae_map_iff haψm.aemeasurable measurableSet_Hbar').2
      ((TwoPoint.foldedCircle_ae_mem_H d hs).mono fun v hv => le_of_lt (hmaps v hv))
  have E2 : evalReg (coordChange Y f Q) ((foldedCircle d s).map fun u => (a : ℂ) * ψ' u) =
      coordChange Y f Q ((foldedCircle d s).map fun u => (a : ℂ) * ψ' u) :=
    evalReg_eq_of_tendsto_radius hU haeν hT
  -- E1
  have : IsProbabilityMeasure ((foldedCircle d s).map ψ') :=
    (Measure.isProbabilityMeasure_map_iff hψ'm.aemeasurable).2 inferInstance
  have hνa : ((foldedCircle d s).map ψ').map (fun w => (a : ℂ) * w) =
      (foldedCircle d s).map fun u => (a : ℂ) * ψ' u :=
    Measure.map_map (measurable_const_mul _) hψ'm
  have hνH : ∀ᵐ z ∂((foldedCircle d s).map ψ'), z ∈ Hbar :=
    (ae_map_iff hψ'm.aemeasurable measurableSet_Hbar').2
      ((TwoPoint.foldedCircle_ae_mem_H d hs).mono fun v hv => le_of_lt (hψ'H hv))
  have E1 : evalReg (rescale (coordChange Y f Q) Q a) ((foldedCircle d s).map ψ') =
      rescale (coordChange Y f Q) Q a ((foldedCircle d s).map ψ') := by
    rw [evalReg_rescale_eq_of_tendsto hU Q ha hνH (by rw [hνa]; exact hI) (by rw [hνa]; exact hT)]
    show _ = evalReg (coordChange Y f Q) (((foldedCircle d s).map ψ').map fun w => (a : ℂ) * w) +
      Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (a : ℂ) * w) z‖ ∂((foldedCircle d s).map ψ')
    rw [hνa, E2, RegClosure.integral_log_deriv_mul ha]
  -- chain rule and integrability
  have hchain : ∀ᵐ u ∂(foldedCircle d s),
      Real.log ‖deriv (fun u => f ((a : ℂ) * ψ' u)) u‖ =
        Real.log ‖deriv f ((a : ℂ) * ψ' u)‖ + Real.log a + Real.log ‖deriv ψ' u‖ := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
    have h1 : HasDerivAt ψ' (deriv ψ' u) u :=
      ((hψ'd u hu).differentiableAt (isOpen_H.mem_nhds hu)).hasDerivAt
    have h2 : HasDerivAt (fun u => (a : ℂ) * ψ' u) ((a : ℂ) * deriv ψ' u) u := h1.const_mul _
    have h3 : HasDerivAt f (deriv f ((a : ℂ) * ψ' u)) ((a : ℂ) * ψ' u) :=
      (RS.differentiableAt_fwdMapInv hW hW0 ht (hmaps u hu)).hasDerivAt
    have hc := h3.comp u h2
    have hprod : ‖deriv (fun u => f ((a : ℂ) * ψ' u)) u‖ =
        ‖deriv f ((a : ℂ) * ψ' u)‖ * (a * ‖deriv ψ' u‖) := by
      rw [show (fun u => f ((a : ℂ) * ψ' u)) = f ∘ (fun u => (a : ℂ) * ψ' u) from rfl,
        hc.deriv, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
    have hne0 : ‖deriv (fun u => f ((a : ℂ) * ψ' u)) u‖ ≠ 0 := by
      rw [norm_deriv_comp_eq hlam hψd hEq hu]
      exact div_ne_zero (norm_ne_zero_iff.2 (hne _ (affR_mem_H hlam hu))) hlam.ne'
    rw [hprod] at hne0 ⊢
    have hA := left_ne_zero_of_mul hne0
    have hB := right_ne_zero_of_mul (right_ne_zero_of_mul hne0)
    rw [Real.log_mul hA (mul_ne_zero ha.ne' hB), Real.log_mul ha.ne' hB]
    ring
  have hI2 : Integrable (fun u => Real.log ‖deriv ψ' u‖) (foldedCircle d s) :=
    G1.integrable_log_norm_deriv_foldedCircle_of_injOn hψ'd hψ'i d hs
  have hL : Measurable fun z => Real.log ‖deriv ψ z‖ :=
    Real.measurable_log.comp (measurable_deriv ψ).norm
  have hint' : Integrable (fun v => Real.log ‖deriv ψ (affR β lam v)‖) (foldedCircle d s) :=
    (integrable_map_measure hL.aestronglyMeasurable (measurable_affR β lam).aemeasurable).1
      (by rw [foldedCircle_map_affine hlam]; exact hint _ _ hs')
  have hcompI : Integrable (fun u => Real.log ‖deriv (fun u => f ((a : ℂ) * ψ' u)) u‖)
      (foldedCircle d s) := by
    refine (hint'.sub (integrable_const (Real.log lam))).congr ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with v hv
    simp only [Pi.sub_apply]
    rw [norm_deriv_comp_eq hlam hψd hEq hv, Real.log_div
      (norm_ne_zero_iff.2 (hne _ (affR_mem_H hlam hv))) hlam.ne']
  have hI1 : Integrable (fun u => Real.log ‖deriv f ((a : ℂ) * ψ' u)‖) (foldedCircle d s) := by
    refine ((hcompI.sub (integrable_const (Real.log a))).sub hI2).congr ?_
    filter_upwards [hchain] with u hu
    simp only [Pi.sub_apply]
    rw [hu]
    ring
  exact ⟨E1, E2, hI1, hI2, hchain⟩

end G1A1b
end R18
end QuantumZipper
