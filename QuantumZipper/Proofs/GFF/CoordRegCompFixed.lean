import QuantumZipper.Proofs.GFF.CoordRegCompBasic
import QuantumZipper.Proofs.Zipper.B2Reg

/-!
# RC3 composition law for fixed drivers

For continuous drivers `V`, `A`, `V_f` with `V = V_f` on `[0,t]` and `A r = V_f(t+r) − V_f t` on
`[0,s]` (so `revMap A s ∘ revMap V t = revMap V_f (t+s)` on `ℍ`), and a probability measure `μ`
on `ℍ` with bounded support, integrable `|log Im|`, a strip bound, and Frostman images
`μ.map (revMap V t)`, `μ.map (revMap V_f (t+s))`, almost surely

`evalReg y (μ.map (revMap V t)) = y (μ.map (revMap V t))`,
`y = coordChange (ofFun (a log‖·‖ + g₁) + X) (revMap A s) Q`

(`ae_evalReg_comp_fixed`): RC3-general (`CoordReg.ae_evalReg_coordChange_revMap_gen`) applied to
`ν = μ.map (revMap V t)`, whose hypotheses follow from `CoordRegCompBasic` because the reverse
flow increases imaginary parts. Instances: `μ` a folded circle `fc(w,r)` with arbitrary centre
`w ∈ ℂ` (`ae_evalReg_comp_fc`), and `μ` a probability measure carried by a compact subset of `ℍ`
with a Frostman bound (`ae_evalReg_comp_compact`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 and its proof (p. 18), through RC3-general; Sheffield arXiv:1012.4797 §5.2
(pp. 57–59) for the use. The reduction itself is an own argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace CoordRegComp

open CoordReg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **RC3 composition law, fixed drivers.** -/
theorem ae_evalReg_comp_fixed (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {Vf V A : ℝ → ℝ} (hVf : Continuous Vf)
    (hV : Continuous V) (hA : Continuous A) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hVV : EqOn Vf V (Icc 0 t)) (hAV : ∀ r ∈ Icc (0 : ℝ) s, Vf (t + r) - Vf t = A r)
    {μ : Measure ℂ} [IsProbabilityMeasure μ] {R c γ α C α' C' : ℝ}
    (hμR : ∀ᵐ z ∂μ, z ∈ H ∧ ‖z‖ ≤ R) (hl : Integrable (fun z : ℂ => |Real.log z.im|) μ)
    (hS : StripBound μ c γ) (hγ : 0 < γ) (hF : IsFrostman (μ.map (revMap V t)) α C)
    (hα : 0 < α) (hF' : IsFrostman (μ.map (revMap Vf (t + s))) α' C') (hα' : 0 < α') :
    ∀ᵐ ω ∂P, evalReg (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap A s) Q) (μ.map (revMap V t)) =
      coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q
        (μ.map (revMap V t)) := by
  have hFm := TwoPoint.measurable_revMap hV ht
  have hAm := TwoPoint.measurable_revMap hA hs
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hV ht R
  have hνH : ∀ᵐ z ∂(μ.map (revMap V t)), z ∈ H :=
    (ae_map_iff hFm.aemeasurable isOpen_H.measurableSet).2
      (hμR.mono fun z hz => TwoPoint.im_revMap_pos hV hz.1 ht)
  have hsupp : (μ.map (revMap V t)) (closedBall 0 Bf ∩ Hbar)ᶜ = 0 := by
    have hae : ∀ᵐ z ∂μ, revMap V t z ∈ closedBall 0 Bf ∩ Hbar :=
      hμR.mono fun z hz => ⟨by rw [mem_closedBall, dist_zero_right]; exact hBf z hz.1 hz.2,
        (TwoPoint.im_revMap_pos hV hz.1 ht).le⟩
    rw [Measure.map_apply hFm (isClosed_closedBall.inter isClosed_Hbar).measurableSet.compl,
      show revMap V t ⁻¹' (closedBall 0 Bf ∩ Hbar)ᶜ =
        {z : ℂ | revMap V t z ∈ closedBall 0 Bf ∩ Hbar}ᶜ from rfl]
    exact mem_ae_iff.1 hae
  have hup : ∀ᵐ z ∂μ, z ∈ H ∧ z.im ≤ (revMap V t z).im ∧ (revMap V t z).im ≤ Bf :=
    hμR.mono fun z hz => ⟨hz.1, im_le_im_revMap V hV z hz.1 ht,
      (Complex.im_le_norm _).trans (hBf z hz.1 hz.2)⟩
  have hlν := integrable_abs_log_im_map hFm hup hl
  have hSν := stripBound_map hFm (hup.mono fun z hz => ⟨hz.1, hz.2.1⟩) hl hS
  have hmap : (μ.map (revMap V t)).map (revMap A s) = μ.map (revMap Vf (t + s)) := by
    rw [Measure.map_map hAm hFm]
    exact Measure.map_congr (hμR.mono fun z hz =>
      (TwoPoint.revMap_concat_eq hVf ht hs hVV hAV hz.1).symm)
  have hFf : IsFrostman ((μ.map (revMap V t)).map (revMap A s)) α' C' := by
    rw [hmap]; exact hF'
  filter_upwards [ae_evalReg_coordChange_revMap_gen hA hs hX a hg₁ Q hsupp hνH hF hα hlν hSν
    hγ hFf hα'] with ω h
  rw [h]
  rfl

/-- **RC3 composition law at a folded circle** (arbitrary centre `w ∈ ℂ`, radius `r > 0`). -/
theorem ae_evalReg_comp_fc (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {Vf V A : ℝ → ℝ} (hVf : Continuous Vf)
    (hV : Continuous V) (hA : Continuous A) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hVV : EqOn Vf V (Icc 0 t)) (hAV : ∀ r ∈ Icc (0 : ℝ) s, Vf (t + r) - Vf t = A r)
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, evalReg (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap A s) Q) ((foldedCircle w r).map (revMap V t)) =
      coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q
        ((foldedCircle w r).map (revMap V t)) := by
  have hμR : ∀ᵐ z ∂foldedCircle w r, z ∈ H ∧ ‖z‖ ≤ ‖w‖ + r := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr,
      TwoPoint.foldedCircle_ae_norm_le w hr.le] with z h1 h2 using ⟨h1, h2⟩
  have hF := TwoPoint.isFrostman_revMap_foldedCircle hV ht hr le_rfl (le_refl (‖w‖ + r))
  have hF' := TwoPoint.isFrostman_revMap_foldedCircle hVf (add_nonneg ht hs) hr le_rfl
    (le_refl (‖w‖ + r))
  exact ae_evalReg_comp_fixed hX a hg₁ Q hVf hV hA ht hs hVV hAV hμR
    (TwoPoint.integrable_log_im_foldedCircle w hr).abs (stripBound_foldedCircle w hr)
    (by norm_num) (fun p ρ hρ => hF p ρ hρ) (by norm_num) (fun p ρ hρ => hF' p ρ hρ)
    (by norm_num)

/-- **RC3 composition law at a compactly supported Frostman probability measure.** -/
theorem ae_evalReg_comp_compact (hX : IsFreeGFFModConstH X P) [IsProbabilityMeasure P] (a : ℝ)
    {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) {Vf V A : ℝ → ℝ} (hVf : Continuous Vf)
    (hV : Continuous V) (hA : Continuous A) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hVV : EqOn Vf V (Icc 0 t)) (hAV : ∀ r ∈ Icc (0 : ℝ) s, Vf (t + r) - Vf t = A r)
    {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖ : ϖ Kᶜ = 0) {α C : ℝ} (hFϖ : IsFrostman ϖ α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, evalReg (coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω)
        (revMap A s) Q) (ϖ.map (revMap V t)) =
      coordChange (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) (revMap A s) Q
        (ϖ.map (revMap V t)) := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hμR : ∀ᵐ z ∂ϖ, z ∈ H ∧ ‖z‖ ≤ M := (ae_iff.2 hϖ).mono fun z hz =>
    ⟨hKH hz, by simpa using hM z hz⟩
  obtain ⟨c, hS, hl⟩ := stripBound_of_compact hK hKH hϖ
  have hF2 : TwoPoint.IsFrostman ϖ α C := fun p ρ hρ => hFϖ p ρ hρ
  obtain ⟨C₁, hF⟩ := B2.isFrostman_map_revMap_of_compact hV ht hK hKH hϖ hα.le hF2
  obtain ⟨C₂, hF'⟩ := B2.isFrostman_map_revMap_of_compact hVf (add_nonneg ht hs) hK hKH hϖ
    hα.le hF2
  exact ae_evalReg_comp_fixed hX a hg₁ Q hVf hV hA ht hs hVV hAV hμR hl hS one_pos
    (fun p ρ hρ => hF p ρ hρ) hα (fun p ρ hρ => hF' p ρ hρ) hα

end CoordRegComp
end QuantumZipper
