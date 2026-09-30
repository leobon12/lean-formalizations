import QuantumZipper.Proofs.Zipper.WedgeCocycleCore
import QuantumZipper.Proofs.Zipper.WedgeFlowWDMain
import QuantumZipper.Proofs.Zipper.F1PStarShiftRegRed
import QuantumZipper.Proofs.Zipper.F1PStarShiftRegDet
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN: the B3(d) field identity along the capacity flow, pointwise

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (rule (5.1),
pp. 60–62: canonical rescaling `h ↦ h(a·) + Q log a` with Brownian scaling of the driver) and
§1.4 (the capacity zipper is a flow). Own elementary bookkeeping, following the `P_*` pattern
of `F1.pStarZipLenInputs_of_core` / `F1.pStarShiftRegStmt_of_core` (the paper states the
equivariance without proof).

Deterministic setting of one realization: a field `y₀`, a continuous driver `W` with `W 0 = 0`,
and the collided configuration `c = zipCapDown γ u (y₀, W)` (field `x_u`, driver `W(u + ·) − W u`).
Given, for this realization,

* (G) regularity of the unzipped fields `x_t` at all times,
* (E) exactness (RC3) of `x_t` at every folded circle centred in `ℍ̄`,
* (RC3-flow) RC3 of `x_u` at the pushed circles of the flow from `u` to `u + s`,
* (C-flow) the continuum limit of the smoothed pairings of `x_u` along the pushed circles of the
  shifted driver,

the field identity of `B3d.ZipLenInputsStmt` (clause 5) holds for every constant `k` with
`a = scaleParam γ (x_u + k) > 0` (`zipLen_field_pt`). Route: constant commutation (from C-flow,
`F1.regShift_of_contData`), scale consistency (`WedgeUnzip.scaleConsistent_of_continuum`), exactness
of the unzipped shifted field (raw flow cocycle `F1.flow_raw_cocycle_of_rc3` + (E)), then
`WedgeUnzip.regEq_unzippedField_canonConfig`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace B3d
namespace ZipLen

variable {γ : ℝ} {y₀ : FieldSample} {W : ℝ → ℝ}

/-- The pushed circles of the driver of `zipCapDown γ u (y₀, W)` are those of `shiftDrv W u`. -/
theorem fc_map_zipCapDown_snd (hW : Continuous W) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    (foldedCircle c r).map (fwdMapInv (zipCapDown γ u (y₀, W)).2 t) =
      (foldedCircle c r).map (fwdMapInv (F1.shiftDrv W u) t) := by
  have hae := TwoPoint.foldedCircle_ae_mem_H c hr
  refine Measure.map_congr (hae.mono fun z hz => ?_)
  have h1 := RegUnif.eqOn_fwdMapInv_shift hW hu ht hz
  have h2 : fwdMapInv (F1.shiftDrv W u) t z = revMap (B2.vrev W (u + t)) t z :=
    RegUnif.eqOn_fwdMapInv_shift hW hu ht hz
  exact h1.trans h2.symm

/-- Circle values of a regular sample plus a constant. -/
theorem evalReg_addConst_fc_of_regular {x : FieldSample} (hx : IsRegularSample x) (k : ℝ)
    (v : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    evalReg (addConst x k) (foldedCircle v ρ) = evalReg x (foldedCircle v ρ) + k := by
  obtain ⟨F, hF⟩ := hx
  rw [(hF.addConst' k).evalReg_fc v hρ, hF.evalReg_fc v hρ]

/-- **The B3(d) field identity for the collided configuration**, pointwise (see the module
docstring). -/
theorem zipLen_field_pt (hW : Continuous W) (hW0 : W 0 = 0)
    (hG : ∀ t : ℝ, 0 ≤ t → IsRegularSample (unzippedField γ (y₀, W) t))
    (hE : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (y₀, W) t) (foldedCircle d r) =
        unzippedField γ (y₀, W) t (foldedCircle d r))
    (hRC : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (unzippedField γ (y₀, W) u)
          ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) =
        unzippedField γ (y₀, W) u ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)))
    (hC : ∀ u t : ℝ, 0 ≤ u → 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (unzippedField γ (y₀, W) u) (foldedCircle v ρ)
          ∂((foldedCircle c r).map (fwdMapInv (F1.shiftDrv W u) t))) (𝓝[>] 0) (𝓝 L))
    {u : ℝ} (hu : 0 ≤ u) (k : ℝ)
    (ha : 0 < scaleParam γ (addConst (zipCapDown γ u (y₀, W)).1 k)) {s : ℝ} (hs : 0 ≤ s) :
    RegEq (unzippedField γ (canonConfig γ
        (addConst (zipCapDown γ u (y₀, W)).1 k, (zipCapDown γ u (y₀, W)).2)) s)
      (rescale (addConst (unzippedField γ (zipCapDown γ u (y₀, W))
          (scaleParam γ (addConst (zipCapDown γ u (y₀, W)).1 k) ^ 2 * s)) k) (Qc γ)
        (scaleParam γ (addConst (zipCapDown γ u (y₀, W)).1 k))) := by
  obtain ⟨hWc, hWc0, hWcmax⟩ := F1.zipCapDown_snd_props (γ := γ) (τ := u) (c := (y₀, W)) hW
  set Yu := (zipCapDown γ u (y₀, W)).1 with hYu_def
  set Wc := (zipCapDown γ u (y₀, W)).2 with hWc_def
  set a := scaleParam γ (addConst Yu k) with ha_def
  have hYu : IsRegularSample Yu := hG u hu
  have has : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  -- continuum data of `x_u` along the pushed circles of its driver
  have hCD : ∀ t : ℝ, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
      F1.ContData Yu ((foldedCircle c r).map (fwdMapInv Wc t)) := by
    intro t ht c r hr
    rw [hWc_def, fc_map_zipCapDown_snd hW hu ht c hr]
    exact ⟨fun ρ hρ => F1.integrable_smoothed_of_regular hYu hWc
      hWc0 ht c hr hρ, hC u t hu ht c r hr⟩
  have hRS : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      E1.RegShift Yu ((foldedCircle d r).map (fwdMapInv Wc t)) := fun t ht d _ r hr =>
    F1.regShift_of_contData hYu (F1.fc_map_fwdMapInv_props hWc hWc0 ht d hr).2 (hCD t ht d r hr)
  -- (i) unzipping commutes with the constant
  have hK : ∀ t : ℝ, 0 ≤ t → RegEq (unzippedField γ (addConst Yu k, Wc) t)
      (addConst (unzippedField γ (Yu, Wc) t) k) := fun t ht =>
    F1.regEq_unzippedField_addConst_of_regShift (hRS t ht)
  -- raw flow cocycle
  have hraw : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      unzippedField γ (Yu, Wc) t (foldedCircle d r) =
        unzippedField γ (y₀, W) (u + t) (foldedCircle d r) := fun t ht d hd r hr =>
    F1.flow_raw_cocycle_of_rc3 γ y₀ hW hW0 hu ht d hr (hRC u t hu ht d hd r hr)
  -- (ii) scale consistency
  have hsc : ∀ (d : ℂ) (r : ℝ), 0 < r → Thm18Asm.G1.ScaleConsistentAt (addConst Yu k) (Qc γ) a
      ((foldedCircle d r).map (fwdMapInv (canonConfig γ (addConst Yu k, Wc)).2 s)) := by
    intro d r hr
    rw [B3d.canonConfig_snd_of_max hWcmax]
    have hy : IsRegularSample (addConst Yu k) := hYu.addConst' k
    obtain ⟨hint, L, hL⟩ := hCD (a ^ 2 * s) has ((a : ℂ) * d) (a * r) (mul_pos ha hr)
    have := (F1.fc_map_fwdMapInv_props hWc hWc0 has ((a : ℂ) * d) (mul_pos ha hr)).1
    refine WedgeUnzip.scaleConsistent_of_continuum hy (Qc γ) hWc hWc0 ha hs d hr
      (fun ρ hρ => F1.integrable_smoothed_of_regular hy hWc hWc0 has _ (mul_pos ha hr) hρ)
      ⟨L + ∫ _v, k ∂((foldedCircle ((a : ℂ) * d) (a * r)).map (fwdMapInv Wc (a ^ 2 * s))), ?_⟩
    refine (hL.add_const _).congr' (eventually_mem_nhdsWithin.mono fun ρ hρ => ?_)
    have hρ' : (0 : ℝ) < ρ := hρ
    simp_rw [evalReg_addConst_fc_of_regular hYu k _ hρ']
    exact (integral_add (hint ρ hρ') (integrable_const k)).symm
  -- (iii) exactness of the unzipped shifted field
  have hexact : ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s) (foldedCircle d r) := by
    intro d hd r hr
    have hDreg : IsRegularSample (unzippedField γ (Yu, Wc) (a ^ 2 * s)) :=
      F1.isRegularSample_of_fc_Hbar (hraw _ has) (hG _ (add_nonneg hu has))
    have hDeq := F1.regEq_of_fc_Hbar (hraw _ has)
    have h1 : evalReg (unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s)) =
        evalReg (addConst (unzippedField γ (Yu, Wc) (a ^ 2 * s)) k) :=
      Factorization.evalReg_congr (B3d.avgReg_eq_of_regEq (hK _ has))
    have hUfc : unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s) (foldedCircle d r) =
        unzippedField γ (Yu, Wc) (a ^ 2 * s) (foldedCircle d r) + k :=
      F2.coordChange_addConst_fc k (hRS _ has d hd r hr)
    have h3 : evalReg (unzippedField γ (Yu, Wc) (a ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (y₀, W) (u + a ^ 2 * s) (foldedCircle d r) := by
      rw [Factorization.evalReg_congr (B3d.avgReg_eq_of_regEq hDeq)]
      exact hE _ (add_nonneg hu has) d hd r hr
    rw [h1, evalReg_addConst_fc_of_regular hDreg k d hr, h3, hUfc, hraw _ has d hd r hr]
  have hmain := WedgeUnzip.regEq_unzippedField_canonConfig (γ := γ) (y := addConst Yu k)
    (W := Wc) hWc hWc0 hWcmax ha hs hsc hexact
  have hresc : rescale (unzippedField γ (addConst Yu k, Wc) (a ^ 2 * s)) (Qc γ) a =
      rescale (addConst (unzippedField γ (Yu, Wc) (a ^ 2 * s)) k) (Qc γ) a :=
    Factorization.coordChange_congr (B3d.avgReg_eq_of_regEq (hK _ has)) _ _
  rw [hresc] at hmain
  exact hmain

end ZipLen
end B3d
end QuantumZipper
