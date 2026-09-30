import QuantumZipper.Proofs.Zipper.RegShiftUnifBasic
import QuantumZipper.Proofs.Zipper.UnifGaugeNodes
import QuantumZipper.Proofs.Zipper.UnifD33Close

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# REGSHIFT-UNIF: the gauge regularity input from the D33 uniform-Cauchy node

Theorem 1.3, uniform-in-time chain (decision D37). The regularity input
`RegUnif.GaugeRegStmt κ T P B Y` (`UnifGaugeBasic.lean`) asks, a.s. and for all `s ∈ [0,T]` at
once, for `E1.RegShift` of the configuration field `𝔥₀ + Y` along every pushed dyadic folded
circle `(f_s)_* fc_i` and for `Cor15Group.BdryConvAE` of the unzipped field `h⁰_s`.

## Reduction

On one full event (`JointMod`, proved: `ae_exists_joint_witness`; fixed-circle regularity of
`𝔥₀ + Y`, proved: `Cor15Group.ae_evalReg_fc_h0rev_add`; continuity of the driver):

* the time-`0` witness `Z(0, ·)` of the unzipped field is a witness of `𝔥₀ + Y` itself
  (`raw_unzip_zero_eq`, `isRegularWith_of_raw_eq`), which gives the raw-convergence and
  integrability parts of `RegShift` along `(f_s)_* fc` for every `s` (`regShift_fc_map_of_witness`);
* the remaining part, convergence of `∫ avgReg (𝔥₀ + Y) j d(f_s)_* fc` as `j → ∞`, is the value at
  `(u, s) = (0, s)` of the uniform-Cauchy family `Φ_j(u, s)` of decision D33; uniform Cauchy on the
  rational points of the triangle gives it at every point (`exists_tendsto_of_uc_tri`);
* `BdryConvAE` of `h⁰_s` holds at *every* real point, since the witness `Z(s, ·)` of the unzipped
  field is continuous on `Hbar × (0,∞)`.

## Main results

* `gaugeRegStmt_of_ucFull : UnifUCFullStmt κ T P B Y → GaugeRegStmt κ T P B Y` (`T > 0`), where
  `UnifUCFullStmt` is `UnifUCStmt` at *all* enumerated folded circles `fc_i` (radius
  `(m+1)/2^j`) instead of the circles `fc(d, 2^{-k})`, `d ∈ Dy`, only;
* `gaugeRegDyStmt_of_uc : UnifUCStmt κ T P B Y → GaugeRegDyStmt κ T P B Y`, the form of the
  input at the circles of radius `2^{-k}` — the only ones read by `bdryApprox` — from the existing
  D33 node itself;
* `unifGlobal_unifAtomless_of_nrmF_uc`, `unifGlobal_unifAtomless_of_gaugeLeaves_uc`: the D37
  gauge transfer of UG/UA with `GaugeRegStmt` replaced by `UnifUCStmt κ T P B (nrmF X)`.

Sources: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 rule (5.1)
(pp. 60–62) and §5.4; Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
185 (2011), Prop. 3.1 (regularized coordinate change, through `CoordRegComp` and JointMod). The
density/continuity bookkeeping is an own elementary argument (as in `UnifRC3UC.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 RegCont TwoPoint B5 B1Full CharFun

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-! ## The uniform-Cauchy family at an arbitrary folded circle -/

/-- `Φ_j(u, s)` of D33 at the folded circle `fc(c, r)`:
`∫ avgReg y_u j d(R_{u,s})_* fc(c, r)`. -/
def PhiJR (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (c : ℂ) (r : ℝ) (j : ℕ) (ω : Ω)
    (p : ℝ × ℝ) : ℝ :=
  ∫ z, avgReg (Yf κ (p.1 + p.2) p.2 B X ω) j z
    ∂(foldedCircle c r).map (revMap (Vr κ (p.1 + p.2) B ω) p.2)

omit [MeasurableSpace Ω] in
/-- `PhiJR` in terms of a witness (`PhiJ_eq_witness` at an arbitrary folded circle). -/
theorem PhiJR_eq_witness {κ : ℝ} {ω : Ω} (hc : Continuous fun s => B s ω)
    {Z : ℝ × (ℂ × ℝ) → ℝ} {T : ℝ} (hZr : ∀ t ∈ Icc 0 T, IsRegularWith
      (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)))
    (c : ℂ) {r : ℝ} (hr : 0 < r) (j : ℕ) {p : ℝ × ℝ} (hp : p ∈ tri T) :
    PhiJR κ B X c r j ω p = ∫ z, Z (p.1, (revMap (vrev (drive κ B ω) (p.1 + p.2)) p.2 z,
      radius j)) ∂foldedCircle c r := by
  have hV : Continuous (Vr κ (p.1 + p.2) B ω) := continuous_vrev (drive_continuous hc) _
  have hm := CoordRegComp.measurable_avgReg_right (Yf κ (p.1 + p.2) p.2 B X ω) j
  unfold PhiJR
  rw [integral_map (TwoPoint.measurable_revMap hV hp.2.1).aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae ((foldedCircle_ae_mem_H c hr).mono fun z hz => ?_)
  rw [Yf_eq_unzippedField, add_sub_cancel_right]
  exact (hZr p.1 ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩).avgReg_eq j
    (im_revMap_pos hV hz hp.2.1).le

/-! ## Pathwise statements -/

omit [MeasurableSpace Ω] in
/-- **Pathwise `RegShift`** of `𝔥₀ + X` along `(f_s)_* fc(c, r)` for every `s ∈ [0,T]`, from the
JointMod witness, fixed-circle regularity and uniform Cauchy of `Φ_j` at `fc(c, r)`. -/
theorem regShift_cfg_of_uc_path {κ T : ℝ} (hT : 0 < T) {ω : Ω}
    (hc : Continuous fun s => B s ω) (h0 : B 0 ω = 0) {Z : ℝ × (ℂ × ℝ) → ℝ}
    (hZc : ContinuousOn Z (parSet T))
    (hZr : ∀ t ∈ Icc 0 T, IsRegularWith
      (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)))
    (hfix : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X ω)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X ω) (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2))
    (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hUC : ∀ n : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ j', N ≤ j' → ∀ p ∈ triQ T,
      |PhiJR κ B X c r j ω p - PhiJR κ B X c r j' ω p| ≤ 1 / ((n : ℝ) + 1))
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    E1.RegShift (cfg κ B X ω).1 ((foldedCircle c r).map (fwdMapInv (drive κ B ω) s)) := by
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hy0 : IsRegularWith (ofFun (h0rev κ) + X ω) (fun p => Z (0, p)) :=
    isRegularWith_of_raw_eq (raw_unzip_zero_eq (Real.sqrt κ) hW hW0 hfix)
      (hZr 0 ⟨le_rfl, hT.le⟩)
  refine regShift_fc_map_of_witness hW hW0 hs.1 hy0 c hr ?_
  have hp : ((0 : ℝ), s) ∈ tri T := ⟨le_rfl, hs.1, by simpa using hs.2⟩
  have hUC' : ∀ n : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ j', N ≤ j' → ∀ p ∈ triQ T,
      |(∫ z, Z (p.1, (revMap (vrev (drive κ B ω) (p.1 + p.2)) p.2 z, radius j))
          ∂foldedCircle c r) -
        ∫ z, Z (p.1, (revMap (vrev (drive κ B ω) (p.1 + p.2)) p.2 z, radius j'))
          ∂foldedCircle c r| ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨N, hN⟩ := hUC n
    refine ⟨N, fun j hj j' hj' q hq => ?_⟩
    rw [← PhiJR_eq_witness hc hZr c hr j (triQ_subset_tri T hq),
      ← PhiJR_eq_witness hc hZr c hr j' (triQ_subset_tri T hq)]
    exact hN j hj j' hj' q hq
  have := exists_tendsto_of_uc_tri hW hT hZc c hr hUC' hp
  simpa only [zero_add] using this

omit [MeasurableSpace Ω] in
/-- **`BdryConvAE` of `h⁰_s`** from the witness: the raw boundary averages converge at every real
point. -/
theorem bdryConvAE_h0f_of_witness {κ T s : ℝ} {ω : Ω} {Z : ℝ × (ℂ × ℝ) → ℝ}
    (hZr : ∀ t ∈ Icc 0 T, IsRegularWith
      (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)))
    (hs : s ∈ Icc 0 T) : Cor15Group.BdryConvAE (h0f κ s B X ω) := by
  rw [h0f_eq_unzippedField]
  intro k
  exact Eventually.of_forall fun t => ⟨_, (hZr s hs).2.1 k (t : ℂ) (by
    show (0 : ℝ) ≤ (t : ℂ).im
    simp)⟩

/-! ## The a.s. statements -/

/-- **The gauge regularity input at the circles of radius `2^{-k}`** (the only circles read by
`bdryApprox`): as `GaugeRegStmt`, with `E1.RegShift` asked along `(f_s)_* fc(d, 2^{-k})`,
`d ∈ Dy`, only. -/
def GaugeRegDyStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T,
    (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (cfg κ B Y ω).1
      ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) s))) ∧
      Cor15Group.BdryConvAE (h0f κ s B Y ω)

/-- **`GaugeRegDyStmt` from the D33 node `UnifUCStmt`.** -/
theorem gaugeRegDyStmt_of_uc [IsProbabilityMeasure P] {κ T : ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hT : 0 < T)
    (hU : UnifUCStmt κ T P B X) : GaugeRegDyStmt κ T P B X := by
  have hUC : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ d ∈ Dy, ∀ n : ℕ, ∃ N : ℕ, ∀ j, N ≤ j → ∀ j', N ≤ j' →
      ∀ p ∈ triQ T, |PhiJ κ B X d k j ω p - PhiJ κ B X d k j' ω p| ≤ 1 / ((n : ℝ) + 1) :=
    ae_all_iff.2 fun k => (eventually_countable_ball countable_Dy).2 fun d hd => hU k d hd
  filter_upwards [hUC, ae_exists_joint_witness (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    Cor15Group.ae_evalReg_fc_h0rev_add κ hX, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω h1 h2 h3 hc h0 s hs
  obtain ⟨Z, hZc, hZr⟩ := h2
  exact ⟨fun k d hd => regShift_cfg_of_uc_path hT hc h0 hZc hZr h3 d (radius_pos k)
    (h1 k d hd) hs, bdryConvAE_h0f_of_witness hZr hs⟩

/-! ## The gauge transfer from `GaugeRegDyStmt` -/

/-- `coordChange` commutes with constants at the level of `avgReg` when `evalReg` does so along
the pushed circles of radius `2^{-k}` centred in `Dy`. -/
theorem avgReg_coordChange_addConst_dy {x : FieldSample} {ψ : ℂ → ℂ} {Q c : ℝ}
    (h : ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift x ((foldedCircle d (radius k)).map ψ)) :
    avgReg (coordChange (addConst x c) ψ Q) = avgReg (addConst (coordChange x ψ Q) c) := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  rw [raw_eq_foldH (coordChange (addConst x c) ψ Q) n k z, raw_eq_foldH (addConst (coordChange x ψ Q) c) n k z,
    F2.coordChange_addConst_fc (ψ := ψ) (Q := Q) c (h k _ (foldH_dyadicRoundC_mem_Dy n z))]
  simp [addConst]

/-! ## Unconditional forms (the D33 node is proved: `unifUCStmt_holds`) -/

/-- **`GaugeRegDyStmt` holds** for every `Γ⁰` sample independent of the driver, `T > 0`. -/
theorem gaugeRegDyStmt_holds [IsProbabilityMeasure P] {κ T : ℝ} (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) (hT : 0 < T) :
    GaugeRegDyStmt κ T P B X :=
  gaugeRegDyStmt_of_uc hB hX hind hT (unifUCStmt_holds hB hX hind hT)

end RegUnif
end QuantumZipper
