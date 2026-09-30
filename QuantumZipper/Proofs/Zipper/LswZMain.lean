import QuantumZipper.Proofs.Zipper.WedgeFlowWDMain
import QuantumZipper.Proofs.Zipper.XFlowClose
import QuantumZipper.Proofs.Zipper.LogShiftW2Main
import QuantumZipper.Proofs.Zipper.LogShiftW2Cap
import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.WedgeXCont
import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Zipper.Cor15Partial
import QuantumZipper.Proofs.Zipper.B5LocDet
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeLogImDom
import QuantumZipper.Proofs.Zipper.YBdryMerge2Tip
import QuantumZipper.Proofs.Zipper.UnifRCSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSL-Z: the field cocycle of the log-shifted configuration (`LswZCocycleRegStmt`)

Task LSL-Z. `lswZCocycleRegStmt_holds` proves `F1.LswZCocycleRegStmt` **without hypotheses**, from proved
results only: the free-field flow nodes (`xFlowRC3Stmt_holds`, `xFlowUCStmt_holds`,
XFlowClose.lean), the regularity of `x` (`WedgeUnzip.ae_isRegularSample_xLogSing`), of the `Γ⁰`
fields `y_u` for all `u` (`WedgeUnzip.ae_forall_isRegularSample_unzY`, JointMod) and of
`−√κ log|E_u|` (`WedgeUnzip.tipXReg_of_logImDomReg logImDomRegStmt_holds`), the dyadic circle
identity `x_u = y_u − √κ log|E_u|` on dyadic folded circles (`F2.step3FieldCircDy_holds`) and the
global Carathéodory core (`WedgeUnzip.globalCaraStmt_holds`). Neither X-G nor X-C is needed: every
continuum input of `unzipAddFun` is replaced by its dyadic form, supplied by `XFlowUCStmt` (at
`u = 0` for the base level, `lswZ_dyAlong_of_flow`), and the regularity of `x_u` is replaced by
that of its dyadic proxy `y_u − √κ log|E_u|` (`lswZ_unzipAddFun_dy'`).
`logShiftLenWeightStmt_of_piece'` is `logShiftLenWeightStmt_of_piece` with this leaf discharged.

The argument is the one of the wedge flow chain (`WedgeFlowWDBasic.flow_rc3_transfer`,
`WedgeCocycleCore.flow_raw_cocycle_of_rc3`), for `Z ≈ x + G` on folded circles,
`x = X + α₀(−log|·|)`:

* `Z_u ≈ x_u + G ∘ E_u` on folded circles (`lswZ_unzipAddFun_dy` at time `u`);
* unzipping once more by `s` along the shifted driver: `unzipAddFun` for `x_u` at the pushed
  circle `(f^{(u)}_s)⁻¹_* fc(d, r)`. Its continuum input is replaced here by the **dyadic**
  convergence of `∫ avgReg x_u k d(f^{(u)}_s)⁻¹_* fc(d, r)`, which is exactly the pointwise
  consequence of the proved five-parameter uniform convergence `XFlowUCStmt`
  (`lswZ_unzipAddFun_dy`: the proof of `WedgeUnzip.unzipAddFun` only uses the dyadic sequence);
* the `x` raw cocycle from `XFlowRC3Stmt` (`flow_raw_cocycle_of_rc3`) and the flow of the Loewner
  maps for the continuous part;
* raw agreement on folded circles gives `RegEq` (`regEq_of_fc_Hbar`).

Sources: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 rule (5.1)
(pp. 60–62; the coordinate change is affine in the field and a cocycle by the chain rule) and §1.4
(the capacity zipper is a flow); Duplantier–Sheffield, *Liouville quantum gravity and KPZ*,
Invent. Math. 185 (2011), Prop. 3.1. The bookkeeping is an own elementary argument (as in
`WedgeUnzipAddFun.lean`, `WedgeFlowWDBasic.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open B2 TwoPoint

/-- The dyadic continuum input: the regularized pairings `∫ avgReg x k dν`,
`ν = (f_t⁻¹)_* fc(d, r)`, converge as `k → ∞`. -/
abbrev DyAlong (x : FieldSample) (W : ℝ → ℝ) (t : ℝ) (d : ℂ) (r : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (fun k : ℕ => ∫ w, avgReg x k w ∂((foldedCircle d r).map (fwdMapInv W t)))
    atTop (𝓝 L)

/-- **Unzipping commutes with adding a continuous function, dyadic form.** As
`WedgeUnzip.unzipAddFun`, with the continuum input replaced by the convergence of the dyadic
regularized pairings `∫ avgReg x k dν`, `ν = (f_t⁻¹)_* fc(d, r)`. -/
theorem lswZ_unzipAddFun_dy (γ : ℝ) (x : FieldSample) (g : ℂ → ℝ) (W : ℝ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hW : Continuous W) (hW0 : W 0 = 0) (hg : Continuous g)
    (hx : IsRegularSample x) (d : ℂ) {r : ℝ} (hr : 0 < r)
    (hlim : DyAlong x W t d r) :
    unzippedField γ (x + ofFun g, W) t (foldedCircle d r) =
      (unzippedField γ (x, W) t + ofFun (g ∘ F2.extInv W t)) (foldedCircle d r) := by
  obtain ⟨L, hxlim⟩ := hlim
  have hxreg := hx
  obtain ⟨F, hF⟩ := hx
  set ψ := fwdMapInv W t
  set ν : Measure ℂ := (foldedCircle d r).map ψ with hν_def
  obtain ⟨_C, B, _hC, _hB, hfacts⟩ := RegCont.νT_facts hW hW0 t d hr
  obtain ⟨hνP, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure ν := hνP
  have hgc : ContinuousOn g Hbar := hg.continuousOn
  have hHb : ∀ {w : ℂ}, w ∈ H → w ∈ Hbar := fun {w} (hw : w ∈ H) =>
    (show 0 ≤ w.im from le_of_lt (show 0 < w.im from hw))
  set F' : ℂ × ℝ → ℝ := fun q => F q + ∫ v, g v ∂foldedCircle q.1 q.2
  have hF' : IsRegularWith (x + ofFun g) F' := GoodSample.gs_add_ofFun hF hgc
  -- the circle averages of `g`
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (B + 1)).exists_bound_of_continuousOn
    hg.continuousOn
  have hM' : ∀ z : ℂ, ‖z‖ ≤ B + 1 → |g z| ≤ M := fun z hz => by
    have := hM z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
    rwa [Real.norm_eq_abs] at this
  have hsm : ∀ k : ℕ, Continuous fun w => GoodSample.smoothFun g w (radius k) := fun k =>
    GoodSample.continuous_smoothFun hgc _
  have hsint : ∀ k : ℕ, Integrable (fun w => GoodSample.smoothFun g w (radius k)) ν := fun k =>
    (integrable_const M).mono' (hsm k).aestronglyMeasurable (hνB.mono fun w hw => by
      rw [Real.norm_eq_abs]
      exact WedgeUnzip.abs_smoothFun_le hM' (radius_pos k).le
        (by linarith [hw.2, RegCont.radius_le_one k]))
  have hglim : Tendsto (fun k : ℕ => ∫ w, GoodSample.smoothFun g w (radius k) ∂ν) atTop
      (𝓝 (∫ w, g w ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => M)
      (fun k => (hsm k).aestronglyMeasurable) (integrable_const M) (fun k => hνB.mono fun w hw => by
        rw [Real.norm_eq_abs]
        exact WedgeUnzip.abs_smoothFun_le hM' (radius_pos k).le
          (by linarith [hw.2, RegCont.radius_le_one k]))
      (hνB.mono fun w hw => ?_)
    have h1 := CoordReg.tendsto_integral_fc_of_continuousOn hg.measurable hg.continuousOn hw.1
      (fun ρ hρ hρ1 => (integrable_const M).mono' hg.aestronglyMeasurable
        ((TwoPoint.foldedCircle_ae_norm_le w hρ.le).mono fun z hz => by
          rw [Real.norm_eq_abs]; exact hM' z (by linarith [hw.2])))
    exact h1.comp RegClosure.tendsto_radius_nhdsGT
  -- the sequence for `x + g`
  have hintA : ∀ k : ℕ, Integrable (fun w => avgReg x k w) ν := fun k =>
    (integrable_smoothed_of_regular hxreg hW hW0 ht d hr (radius_pos k)).congr
      (hνB.mono fun w hw => by
        show evalReg x (foldedCircle w (radius k)) = avgReg x k w
        rw [WedgeUnzip.avgReg_eq_of_regularWith hF k (hHb hw.1),
          hF.evalReg_fc_of_mem (hHb hw.1) (radius_pos k)])
  have hb : ∀ k : ℕ, ∫ w, avgReg (x + ofFun g) k w ∂ν =
      ∫ w, avgReg x k w ∂ν + ∫ w, GoodSample.smoothFun g w (radius k) ∂ν := fun k => by
    rw [← integral_add (hintA k) (hsint k)]
    refine integral_congr_ae (hνB.mono fun w hw => ?_)
    show avgReg (x + ofFun g) k w = avgReg x k w + GoodSample.smoothFun g w (radius k)
    rw [WedgeUnzip.avgReg_eq_of_regularWith hF' k (hHb hw.1),
      WedgeUnzip.avgReg_eq_of_regularWith hF k (hHb hw.1)]
    rfl
  have hE1 : evalReg x ν = L := hxlim.limUnder_eq
  have hE2 : evalReg (x + ofFun g) ν = L + ∫ w, g w ∂ν :=
    ((hxlim.add hglim).congr fun k => (hb k).symm).limUnder_eq
  have hgE : ∫ z, (g ∘ F2.extInv W t) z ∂foldedCircle d r = ∫ w, g w ∂ν := by
    rw [hν_def, integral_map (RegCont.aemeasurable_fwdMapInv hW hW0 ht d hr)
      hg.aestronglyMeasurable]
    refine integral_congr_ae ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    have hz' : 0 < z.im := hz
    simp [F2.extInv, hz']
  show evalReg (x + ofFun g) ν + Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle d r =
    (evalReg x ν + Qc γ * ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle d r) +
      ∫ z, (g ∘ F2.extInv W t) z ∂foldedCircle d r
  rw [hE1, hE2, hgE]
  ring

/-- **`lswZ_unzipAddFun_dy` for a field only known to agree with a regular one on the dyadic
folded circles** (all that `avgReg`, hence `evalReg` and `coordChange`, ever reads). -/
theorem lswZ_unzipAddFun_dy' (γ : ℝ) {x x' : FieldSample} (g : ℂ → ℝ) (W : ℝ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (hW : Continuous W) (hW0 : W 0 = 0) (hg : Continuous g)
    (hx' : IsRegularSample x')
    (hraw : ∀ (n : ℕ) (a b : ℤ) (k : ℕ), x (foldedCircle (CircleCont.lpt n a b) (radius k)) =
      x' (foldedCircle (CircleCont.lpt n a b) (radius k)))
    (d : ℂ) {r : ℝ} (hr : 0 < r) (hlim : DyAlong x W t d r) :
    unzippedField γ (x + ofFun g, W) t (foldedCircle d r) =
      (unzippedField γ (x, W) t + ofFun (g ∘ F2.extInv W t)) (foldedCircle d r) := by
  have havg : avgReg x = avgReg x' :=
    funext fun k => funext fun z => F2.forall_avgReg_eq_of_lpt hraw k z
  have havg2 : avgReg (x + ofFun g) = avgReg (x' + ofFun g) :=
    funext fun k => funext fun z => F2.forall_avgReg_eq_of_lpt (fun n a b k => by
      show x _ + ofFun g _ = x' _ + ofFun g _
      rw [hraw]) k z
  have e1 : unzippedField γ (x + ofFun g, W) t = unzippedField γ (x' + ofFun g, W) t :=
    Factorization.coordChange_congr havg2 _ _
  have e2 : unzippedField γ (x, W) t = unzippedField γ (x', W) t :=
    Factorization.coordChange_congr havg _ _
  obtain ⟨L, hL⟩ := hlim
  rw [havg] at hL
  rw [e1, e2]
  exact lswZ_unzipAddFun_dy γ x' g W t ht hW hW0 hg hx' d hr ⟨L, hL⟩

/-- **`z_u` agrees on folded circles with `x_u + gExt`** (as `unz_fc_split`, dyadic input). -/
theorem lswZ_unz_fc_split_dy (γ : ℝ) {z x : FieldSample} {G : ℂ → ℝ} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hG : Continuous G) (hx : IsRegularSample x)
    (hz : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → z (foldedCircle d r) = (x + ofFun G) (foldedCircle d r))
    {u : ℝ} (hu : 0 ≤ u) (hxu : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → DyAlong x W u d r) :
    ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → unzippedField γ (z, W) u (foldedCircle d r) =
      (unzippedField γ (x, W) u + ofFun (gExt G W u)) (foldedCircle d r) := by
  intro d hd r hr
  have e1 : unzippedField γ (z, W) u = unzippedField γ (x + ofFun G, W) u :=
    Factorization.coordChange_congr
      (funext fun k => funext fun w => regEq_of_fc_Hbar hz k w) _ _
  rw [e1, lswZ_unzipAddFun_dy γ x G W u hu hW hW0 hG hx d hr (hxu d hd r hr)]
  simp only [Pi.add_apply]
  congr 1
  exact ofFun_fc_congr (fun w hw => (gExt_eq hw).symm) d hr

/-- **The dyadic input for `x` at time `t` from the flow pairings at `u = 0`**: at time `0` the
unzipped field has the regularized values of `x` on `ℍ̄` (as `bdryR_unzippedField_zero`). -/
theorem lswZ_dyAlong_of_flow (γ : ℝ) {x : FieldSample} (hx : IsRegularSample x) {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (d : ℂ) {r : ℝ} (hr : 0 < r)
    {L : ℝ} (h : Tendsto (fun j : ℕ => ∫ z, avgReg (unzippedField γ (x, W) 0) j z
      ∂flowNu W (0, t, d, r)) atTop (𝓝 L)) : DyAlong x W t d r := by
  obtain ⟨F, hF⟩ := hx
  have hid : EqOn (fwdMapInv W 0) id H := fun w hw => by
    rw [Thm18Asm.G1Pkg.fwdMapInv_zero_time hW (show 0 < w.im from hw), hW0]
    simp
  have h2 : coordChange x id (Qc γ) = fun μ => evalReg x μ :=
    funext fun μ => Cor15Partial.coordChange_id_apply x (Qc γ) μ
  have havg : ∀ k : ℕ, ∀ z ∈ Hbar,
      avgReg (unzippedField γ (x, W) 0) k z = avgReg x k z := by
    intro k z hz
    show avgReg (coordChange x (fwdMapInv W 0) (Qc γ)) k z = _
    rw [CoordReg.avgReg_coordChange_congr x hid (Qc γ) k z, h2]
    exact WedgeCan.avgReg_evalReg_eq hF k hz
  have hν : flowNu W (0, t, d, r) = (foldedCircle d r).map (fwdMapInv W t) := by
    show (foldedCircle d r).map (revMap (B2.vrev W (0 + t)) t) = _
    refine Measure.map_congr ((foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    rw [zero_add, fwdMapInv_eq_revMap_vrev hW hW0 ht hz]
  obtain ⟨_C, B, _hC, _hB, hfacts⟩ := RegCont.νT_facts hW hW0 t d hr
  obtain ⟨-, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  refine ⟨L, h.congr fun j => ?_⟩
  rw [hν]
  exact integral_congr_ae (hνB.mono fun w hw => havg j w (mem_Hbar_of_H hw.1))

/-- **Raw cocycle of `z ≈ x + G` from the raw cocycle of `x`** (deterministic; as
`flow_rc3_transfer`, with the nested continuum input of `x_u` in dyadic form). -/
theorem lswZ_raw_cocycle_dy (γ : ℝ) {z x : FieldSample} {G : ℂ → ℝ} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hG : Continuous G) (hx : IsRegularSample x)
    (hz : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → z (foldedCircle d r) = (x + ofFun G) (foldedCircle d r))
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (hCu : ContinuousOn (F2.extInv W u) Hbar)
    (hxu : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → DyAlong x W u d r)
    {xu' : FieldSample} (hxuR : IsRegularSample xu')
    (hxuraw : ∀ (n : ℕ) (a b : ℤ) (k : ℕ),
      unzippedField γ (x, W) u (foldedCircle (CircleCont.lpt n a b) (radius k)) =
        xu' (foldedCircle (CircleCont.lpt n a b) (radius k)))
    {d : ℂ} {r : ℝ} (hr : 0 < r)
    (hxus : DyAlong x W (u + s) d r)
    (hxuD : DyAlong (unzippedField γ (x, W) u) (shiftDrv W u) s d r)
    (hX : evalReg (unzippedField γ (x, W) u)
        ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s)) =
      unzippedField γ (x, W) u ((foldedCircle d r).map (revMap (B2.vrev W (u + s)) s))) :
    unzippedField γ (zipCapDown γ u (z, W)) s (foldedCircle d r) =
      unzippedField γ (z, W) (u + s) (foldedCircle d r) := by
  have hsplit := lswZ_unz_fc_split_dy γ hW hW0 hG hx hz hu hxu
  have e2 : unzippedField γ (zipCapDown γ u (z, W)) s =
      unzippedField γ (unzippedField γ (x, W) u + ofFun (gExt G W u), shiftDrv W u) s :=
    Factorization.coordChange_congr
      (funext fun k => funext fun w => regEq_of_fc_Hbar hsplit k w) _ _
  have e3 : unzippedField γ (z, W) (u + s) = unzippedField γ (x + ofFun G, W) (u + s) :=
    Factorization.coordChange_congr
      (funext fun k => funext fun w => regEq_of_fc_Hbar hz k w) _ _
  rw [e2, e3, lswZ_unzipAddFun_dy' γ (gExt G W u) (shiftDrv W u) s hs
      (shiftDrv_continuous hW u) (shiftDrv_zero W u) (gExt_continuous hG hCu) hxuR hxuraw d hr
      hxuD,
    lswZ_unzipAddFun_dy γ x G W (u + s) (add_nonneg hu hs) hW hW0 hG hx d hr hxus]
  have hE := flow_raw_cocycle_of_rc3 γ x hW hW0 hu hs d hr hX
  show unzippedField γ (unzippedField γ (x, W) u, shiftDrv W u) s (foldedCircle d r) +
      ofFun (gExt G W u ∘ F2.extInv (shiftDrv W u) s) (foldedCircle d r) =
    unzippedField γ (x, W) (u + s) (foldedCircle d r) +
      ofFun (G ∘ F2.extInv W (u + s)) (foldedCircle d r)
  have hE' : unzippedField γ (unzippedField γ (x, W) u, shiftDrv W u) s (foldedCircle d r) =
      unzippedField γ (x, W) (u + s) (foldedCircle d r) := hE
  rw [hE']
  congr 1
  unfold ofFun
  refine integral_congr_ae ((foldedCircle_ae_mem_H d hr).mono fun w hw => ?_)
  obtain ⟨hm, hcomp⟩ := fwdMapInv_shiftDrv_comp hW hW0 hu hs hw
  simp only [Function.comp_apply]
  rw [extInv_of_mem_H _ _ hw, extInv_of_mem_H _ _ hw, gExt_eq (mem_Hbar_of_H hm),
    extInv_of_mem_H _ _ hm, hcomp]

/-- The pushed circle of the flow node is the image under the shifted inverse map. -/
theorem lswZ_flowNu_eq {W : ℝ → ℝ} (hW : Continuous W) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s)
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    flowNu W (u, s, d, r) = (foldedCircle d r).map (fwdMapInv (shiftDrv W u) s) := by
  unfold flowNu
  exact Measure.map_congr ((foldedCircle_ae_mem_H d hr).mono fun z hz =>
    (RegUnif.eqOn_fwdMapInv_shift hW hu hs hz).symm)

/-- **`LswZCocycleRegStmt` holds** (no hypotheses). The free-field flow nodes `XFlowRC3Stmt`,
`XFlowUCStmt`, the regularity of `x`, of `y_u` and of `−√κ log|E_u|`, the dyadic circle identity
`x_u = y_u − √κ log|E_u|` and the global Carathéodory core are all proved. -/
theorem lswZCocycleRegStmt_holds : LswZCocycleRegStmt := by
  intro κ hκ hκ4 Ω _ P _ B X G Z hB hX hI hGZ
  filter_upwards [WedgeUnzip.ae_forall_isRegularSample_unzY (κ := κ) hB hX hI,
    WedgeUnzip.tipXReg_of_logImDomReg WedgeUnzip.logImDomRegStmt_holds κ hκ hκ4 P B hB,
    F2.step3FieldCircDy_holds κ hκ hκ4 P B X hB hX hI,
    WedgeUnzip.ae_isRegularSample_xLogSing hX κ,
    xFlowRC3Stmt_holds κ hκ hκ4 P B X hB hX hI, xFlowUCStmt_holds κ hκ hκ4 P B X hB hX hI,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB, hGZ, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω hYr hTr hcirc hxr hRo hUo hCa hZ hc h0
  obtain ⟨hGc, hZfc⟩ := hZ
  obtain ⟨L, hL⟩ := hUo
  intro u s hu hs
  have hW : Continuous (drive κ B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hbase : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      DyAlong (X ω + F2.logSingField κ) (drive κ B ω) t d r := fun t ht d hd r hr =>
    lswZ_dyAlong_of_flow (Real.sqrt κ) hxr hW hW0 ht d hr
      (hL.tendsto_at (show ((0 : ℝ), t, d, r) ∈ flowPar from ⟨le_rfl, ht, hd, hr⟩))
  have hxuR : IsRegularSample (F2.unzY κ (X ω) (drive κ B ω) u +
      ofFun (WedgeUnzip.logTipFun κ (drive κ B ω) u)) := by
    obtain ⟨F, hF⟩ := hYr u hu
    exact ⟨_, WedgeUnzip.isRegularWith_add hF (hTr u hu)⟩
  refine regEq_of_fc_Hbar fun d hd r hr => ?_
  refine lswZ_raw_cocycle_dy (Real.sqrt κ) hW hW0 hGc hxr hZfc hu hs (hCa u hu)
    (fun d hd r hr => hbase u hu d hd r hr) hxuR (fun n a b k => hcirc u hu n a b k) hr
    (hbase (u + s) (add_nonneg hu hs) d hd r hr) ⟨L (u, s, d, r), ?_⟩
    (hRo u s hu hs d hd r hr)
  have hp : (u, s, d, r) ∈ flowPar := ⟨hu, hs, hd, hr⟩
  have h := hL.tendsto_at hp
  rw [← lswZ_flowNu_eq hW hu hs d hr]
  exact h

end F1
end QuantumZipper
