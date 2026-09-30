import QuantumZipper.Proofs.Zipper.Cor15PosZip
import QuantumZipper.Proofs.Loewner.ReverseHolo

/-!
# Corollary 1.5, positive times: reduction of the re-zipping field statement

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
no proof in the paper). The field half of blocker 1 (`Cor15RezipFieldStmt`, `Cor15PosZip`) is
reduced here to two sharper statements at the countably many dyadic folded circles `σ_i`:

* `Cor15HullNullStmt` (not proved): a.s. `σ_i` does not charge the hull `η[0,t] =
  revHull (vrev W t) t`;
* `Cor15RezipRegStmt` (not proved): a.s. the unzipped field is regular at `σ_i.map f_t`,
  `f_t = revMapInv (vrev W t) t`.

`cor15RezipFieldStmt_of` proves `Cor15RezipFieldStmt` from them. The deterministic core is
`rezip_apply`: for a measure `μ` carried by `f_t⁻¹(ℍ) = revMap V t '' ℍ`, re-zipping
`coordChange x F Q` (`F = revMap V t` on `ℍ`) along `ψ = revMapInv V t` gives back
`evalReg x μ`, once the first field is regular at `μ.map ψ`: `(μ.map ψ).map F = μ`, and
`log |F' ∘ ψ| = −log |ψ'|` by the inverse function theorem (`hasStrictDerivAt_revMapInv`).
**Own elementary argument** (change of variables and the chain rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open B2

section Det

variable {V : ℝ → ℝ} {t : ℝ}

theorem revMapInv_revMap (hV : Continuous V) (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    revMapInv V t (revMap V t z) = z := by
  have hu : ∃! z', z' ∈ H ∧ revMap V t z' = revMap V t z :=
    ⟨z, ⟨hz, rfl⟩, fun z' hz' => injOn_revMap V hV ht hz'.1 hz hz'.2⟩
  unfold revMapInv
  rw [dite_eq_left_of_eq_true (eq_true hu)]
  exact injOn_revMap V hV ht hu.choose_spec.1.1 hz hu.choose_spec.1.2

theorem hasStrictDerivAt_revMapInv (hV : Continuous V) (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    HasStrictDerivAt (revMapInv V t) (deriv (revMap V t) z)⁻¹ (revMap V t z) := by
  have hH : H ∈ 𝓝 z := isOpen_H.mem_nhds hz
  have hs : HasStrictDerivAt (revMap V t) (deriv (revMap V t) z) z :=
    ((differentiableOn_revMap V hV ht).analyticAt hH).hasStrictDerivAt
  exact hs.to_local_left_inverse (deriv_revMap_ne_zero V hV ht hz)
    (Filter.mem_of_superset hH fun z' hz' => revMapInv_revMap hV ht hz')

theorem isOpen_revMap_image (hV : Continuous V) (ht : 0 ≤ t) : IsOpen (revMap V t '' H) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hH : H ∈ 𝓝 z := isOpen_H.mem_nhds hz
  have hs : HasStrictDerivAt (revMap V t) (deriv (revMap V t) z) z :=
    ((differentiableOn_revMap V hV ht).analyticAt hH).hasStrictDerivAt
  rw [← hs.map_nhds_eq (deriv_revMap_ne_zero V hV ht hz)]
  exact image_mem_map hH

/-- **Re-zipping, deterministic core.** -/
theorem rezip_apply (hV : Continuous V) (ht : 0 ≤ t) (x : FieldSample) (Q : ℝ) {F : ℂ → ℂ}
    (hF : EqOn F (revMap V t) H) {μ : Measure ℂ} (hμ : μ (revMap V t '' H)ᶜ = 0)
    (hreg : evalReg (coordChange x F Q) (μ.map (revMapInv V t)) =
      coordChange x F Q (μ.map (revMapInv V t))) :
    coordChange (coordChange x F Q) (revMapInv V t) Q μ = evalReg x μ := by
  set φ := revMap V t with hφ
  set ψ := revMapInv V t with hψ
  set U := φ '' H with hUdef
  have hU : ∀ᵐ w ∂μ, w ∈ U := ae_iff.2 hμ
  have hψU : ∀ w ∈ U, ψ w ∈ H ∧ φ (ψ w) = w := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hψ, revMapInv_revMap hV ht hz]
    exact ⟨hz, rfl⟩
  have hψc : ContinuousOn ψ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hasStrictDerivAt_revMapInv hV ht hz).hasDerivAt.continuousAt.continuousWithinAt
  have hUo : IsOpen U := isOpen_revMap_image hV ht
  have hψm : AEMeasurable ψ μ := by
    have h := hψc.aemeasurable (μ := μ) hUo.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hU] at h
  have hmapH : ∀ᵐ z ∂(μ.map ψ), z ∈ H :=
    (ae_map_iff hψm isOpen_H.measurableSet).2 (hU.mono fun w hw => (hψU w hw).1)
  have e1 : coordChange (coordChange x F Q) ψ Q μ =
      evalReg (coordChange x F Q) (μ.map ψ) + Q * ∫ z, Real.log ‖deriv ψ z‖ ∂μ := rfl
  have e2 : coordChange x F Q (μ.map ψ) =
      evalReg x ((μ.map ψ).map F) + Q * ∫ z, Real.log ‖deriv F z‖ ∂(μ.map ψ) := rfl
  have e3 : (μ.map ψ).map F = μ := by
    rw [Measure.map_congr (hmapH.mono fun z hz => hF hz),
      AEMeasurable.map_map_of_aemeasurable (TwoPoint.measurable_revMap hV ht).aemeasurable hψm]
    rw [Measure.map_congr (f := φ ∘ ψ) (g := id) (hU.mono fun w hw => (hψU w hw).2),
      Measure.map_id]
  have e4 : ∫ z, Real.log ‖deriv F z‖ ∂(μ.map ψ) = ∫ w, Real.log ‖deriv F (ψ w)‖ ∂μ :=
    integral_map hψm (measurable_deriv F).norm.log.aestronglyMeasurable
  have e5 : ∫ w, Real.log ‖deriv F (ψ w)‖ ∂μ = -∫ w, Real.log ‖deriv ψ w‖ ∂μ := by
    rw [← integral_neg]
    refine integral_congr_ae (hU.mono fun w hw => ?_)
    obtain ⟨z, hz, rfl⟩ := hw
    have hd : deriv ψ (φ z) = (deriv φ z)⁻¹ :=
      (hasStrictDerivAt_revMapInv hV ht hz).hasDerivAt.deriv
    have hFd : deriv F z = deriv φ z :=
      Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hF)
    show Real.log ‖deriv F (ψ (φ z))‖ = -Real.log ‖deriv ψ (φ z)‖
    rw [hd, hψ, revMapInv_revMap hV ht hz, hFd, norm_inv, Real.log_inv, neg_neg]
  rw [e1, hreg, e2, e3, e4, e5]
  ring

end Det

/-- **Remaining statement (K0)** (not proved). A.s. the dyadic folded circles do not charge the
hull `revHull (vrev W t) t` (the SLE_κ curve `η[0,t]`, `κ < 4`). -/
def Cor15HullNullStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ t : ℝ, 0 < t →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ i : ℕ,
    ∀ᵐ ω ∂P, foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
      (revHull (vrev (drive κ B ω) t) t) = 0

/-- **Remaining statement (R)** (not proved). A.s. the unzipped field is regular at the image
under the centered forward map `f_t = revMapInv (vrev W t) t` of each dyadic folded circle. -/
def Cor15RezipRegStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ t : ℝ, 0 < t →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P → ∀ i : ℕ,
    ∀ᵐ ω ∂P,
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t)
        ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2).map
          (revMapInv (vrev (drive κ B ω) t) t)) =
      unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t
        ((foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2).map
          (revMapInv (vrev (drive κ B ω) t) t))

/-- The field statement of blocker 1 from (K0) and (R). -/
theorem cor15RezipFieldStmt_of (hK : Cor15HullNullStmt) (hR : Cor15RezipRegStmt) :
    Cor15RezipFieldStmt := by
  intro κ hκ hκ4 t ht Ω _ P _ B X hB hX hind
  filter_upwards [ae_all_iff.2 (hK κ hκ hκ4 t ht P B hB),
    ae_all_iff.2 (hR κ hκ hκ4 t ht P B X hB hX hind), ae_evalReg_fc_h0rev_add κ hX, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hk hr hd hc h0
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hVc : Continuous (vrev (drive κ B ω) t) := continuous_vrev hWc t
  refine UnzipFull.regEq_of_coordsFull (funext fun i => ?_)
  have hri := UnzipFull.fullIndex_radius_pos i
  have hHc : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2 Hᶜ = 0 :=
    ae_iff.1 (TwoPoint.foldedCircle_ae_mem_H _ hri)
  have hμ : foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2
      (revMap (vrev (drive κ B ω) t) t '' H)ᶜ = 0 := by
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hHc (hk i))
    by_cases hzH : z ∈ H
    · exact Or.inr ⟨hzH, hz⟩
    · exact Or.inl hzH
  show coordChange (coordChange (ofFun (h0rev κ) + X ω) (fwdMapInv (drive κ B ω) t)
      (Qc (Real.sqrt κ))) (revMapInv (vrev (drive κ B ω) t) t) (Qc (Real.sqrt κ)) _ = _
  rw [rezip_apply hVc ht.le _ _ (fun z hz => fwdMapInv_eq_revMap_vrev hWc hW0 ht.le hz) hμ
    (hr i)]
  exact hd i

end Cor15Group
end QuantumZipper
