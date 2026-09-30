import QuantumZipper.Proofs.Thm18.A1RS3Meas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (12): `A1RSSmearMeasStmt` holds, hence `A1RFSmearContStmt`

**`a1rsSmearMeasStmt_holds`**: the dyadic pairings of the `Ψ`-smeared family are, on good
continuous paths, the jointly measurable functions
`(a, y) ↦ ∫∫ avgReg y k (finvM (a, foldH(fM(a, Ψ_a w) + ρ e^{iθ}))) dfc(d, s)(w) dθ`
(`finvM`, `fM`: A1RS3Meas.lean; Fubini-type measurability
`StronglyMeasurable.integral_prod_right'`).

**`a1rsRatCauchyStmt_holds`**, **`a1rfSmearContStmt_holds`**. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- **`A1RSSmearMeasStmt` holds.** -/
theorem a1rsSmearMeasStmt_holds : A1RSSmearMeasStmt := by
  intro γ hγ hγ2 Ψ hΨ left p ρ k
  set κ : ℝ := γ ^ 2 with hκ
  have hκ0 : 0 < κ := by positivity
  set tt : ℝ := max (p 0) 0 with htt
  have htt0 : 0 ≤ tt := le_max_right _ _
  set m := E6.XAreaPC.angMeas with hm
  have hcm : Continuous fun q : ℂ × ℝ => circleMap q.1 ρ q.2 := by
    unfold circleMap; fun_prop
  have hΨm : Measurable fun q : (ℝ≥0 → ℝ) × ℂ => Ψ left q.1 q.2 := hΨ.1 left
  set Gint : ((ℝ≥0 → ℝ) × FieldSample) × (ℂ × ℝ) → ℝ := fun z =>
    avgReg z.1.2 k (finvM κ tt (z.1.1, foldH (circleMap (fM κ tt (z.1.1, Ψ left z.1.1 z.2.1))
      ρ z.2.2))) with hGint
  have hGm : Measurable Gint := by
    have h1 : Measurable fun z : ((ℝ≥0 → ℝ) × FieldSample) × (ℂ × ℝ) =>
        fM κ tt (z.1.1, Ψ left z.1.1 z.2.1) :=
      (measurable_fM κ htt0).comp (measurable_fst.fst.prodMk
        (hΨm.comp (measurable_fst.fst.prodMk measurable_snd.fst)))
    have h2 : Measurable fun z : ((ℝ≥0 → ℝ) × FieldSample) × (ℂ × ℝ) =>
        foldH (circleMap (fM κ tt (z.1.1, Ψ left z.1.1 z.2.1)) ρ z.2.2) :=
      measurable_foldH.comp (hcm.measurable.comp (h1.prodMk measurable_snd.snd))
    exact (measurable_avgReg k).comp (measurable_fst.snd.prodMk
      ((measurable_finvM κ htt0).comp (measurable_fst.fst.prodMk h2)))
  refine ⟨fun z => ∫ q, Gint (z, q) ∂((foldedCircle (parD p) (p 3)).prod m),
    (StronglyMeasurable.integral_prod_right' hGm.stronglyMeasurable).measurable, ?_⟩
  intro hp _ a hc hG y
  have ht : 0 < p 0 := hp.1
  have htt' : tt = p 0 := max_eq_left ht.le
  set W := pathDrive κ a with hW
  have h0 : a 0 = 0 := by
    have h := hG.2.1
    simp only [hW, pathDrive, Real.toNNReal_zero] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (Real.sqrt_pos.2 hκ0).ne'
    · exact h'
  have hreg : regDrv κ a = W := regDrv_eq hc h0
  -- the selected side map lies in the complement of the hull
  have hs : IsSimpleChord (pathTrace (γ ^ 2) a) := hG.2.2.2.1
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hs left
  have hUn := G1ZA1a.isNormalizedUniformizer_sideDom hs left
  obtain ⟨β, hβ, hdil⟩ := g1z2_invFunOn_eq_dilate hs left hφ hUn
  have hβ' : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hβ.ne'
  have hΨK : ∀ w ∈ H, Ψ left a w ∈ H \ fwdHull W (p 0) := by
    intro w hw
    have hw' : ((β : ℂ))⁻¹ * w ∈ H := by
      show 0 < (((β : ℂ))⁻¹ * w).im
      rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]; exact mul_pos (inv_pos.2 hβ) hw
    have h1 := sideMap_mem_compl_fwdHull hG ht.le left hw'
    have h2 : g1zSideMap left W (((β : ℂ))⁻¹ * w) = Ψ left a w := by
      have := hdil hw'
      simp only at this
      rw [mul_inv_cancel_left₀ hβ'] at this
      rw [← hΨa] at this
      exact this
    rw [← h2]; exact h1
  -- the measurable versions agree
  have hfinv : ∀ u : ℂ, finvM κ tt (a, u) = fwdMapInv W (p 0) u := by
    intro u; rw [finvM_eq κ htt0, hreg, htt']
  have hfM : ∀ w ∈ H, fM κ tt (a, Ψ left a w) = fwdMap W (p 0) (Ψ left a w) := by
    intro w hw
    have := fM_eq κ htt0 a (z := Ψ left a w) (by rw [hreg, htt']; exact hΨK w hw)
    rw [this, hreg, htt']
  set Gt : ℂ → ℂ := fun w => fM κ tt (a, Ψ left a w) with hGt
  have hGtm : Measurable Gt :=
    (measurable_fM κ htt0).comp (measurable_const.prodMk (hΨm.comp
      (measurable_const.prodMk measurable_id)))
  set Hm : ℂ × ℝ → ℂ := fun q => finvM κ tt (a, foldH (circleMap q.1 ρ q.2)) with hHm
  have hHmm : Measurable Hm :=
    (measurable_finvM κ htt0).comp (measurable_const.prodMk
      (measurable_foldH.comp hcm.measurable))
  have hmu : ((foldedCircle (parD p) (p 3)).map fun w => fwdMap W (p 0) (Ψ left a w)) =
      (foldedCircle (parD p) (p 3)).map Gt :=
    Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H (parD p) hp.2).mono fun w hw =>
      (hfM w hw).symm)
  have hsm : smearPsi Ψ κ left a p ρ = (((foldedCircle (parD p) (p 3)).prod m).map
      (Prod.map Gt id)).map Hm := by
    unfold smearPsi
    rw [hmu, ← Measure.map_prod_map _ _ hGtm measurable_id, Measure.map_id]
    congr 1
    funext q
    exact (hfinv _).symm
  have hak : Measurable (avgReg y k) :=
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  have e1 : ∫ w, avgReg y k w ∂((((foldedCircle (parD p) (p 3)).prod m).map
      (Prod.map Gt id)).map Hm) = ∫ q, avgReg y k (Hm q) ∂(((foldedCircle (parD p) (p 3)).prod m).map
      (Prod.map Gt id)) := integral_map hHmm.aemeasurable hak.aestronglyMeasurable
  have e2 : ∫ q, avgReg y k (Hm q) ∂(((foldedCircle (parD p) (p 3)).prod m).map
      (Prod.map Gt id)) = ∫ q, avgReg y k (Hm (Prod.map Gt id q)) ∂((foldedCircle (parD p) (p 3)).prod m) :=
    integral_map (hGtm.prodMap measurable_id).aemeasurable (hak.comp hHmm).aestronglyMeasurable
  rw [hsm, e1, e2]
  rfl

/-- **`A1RSRatCauchyStmt` holds.** -/
theorem a1rsRatCauchyStmt_holds : A1RSRatCauchyStmt :=
  a1rsRatCauchyStmt_of_freeBrown (a1rsFreeBrownStmt_of_meas a1rsSmearMeasStmt_holds)

/-- **`A1RFSmearContStmt` holds.** -/
theorem a1rfSmearContStmt_holds : A1RFSmearContStmt :=
  a1rfSmearContStmt_of_ratCauchy a1rsRatCauchyStmt_holds

end A1RS
end R18
end QuantumZipper
