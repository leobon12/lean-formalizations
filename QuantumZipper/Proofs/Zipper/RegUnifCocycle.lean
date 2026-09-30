import QuantumZipper.Proofs.Zipper.RegUnif
import QuantumZipper.Proofs.GFF.CoordRegComp

/-!
# REG-UNIF: the field cocycle of `zipCapDown` at the raw level

Deterministic identities (`double_apply_fc`, `single_apply_fc`): for a continuous driver `W` with
`W 0 = 0`, `u, s ≥ 0`, `R = revMap (vrev W (u + s)) s` and `x_u` the field unzipped by `u`,

* the field of `(x, W)` unzipped by `u`, then by `s`, at `fc(w, r)` is
  `evalReg x_u (R_* fc(w, r)) + Q ∫ log |R'| dfc(w, r)`;
* the field unzipped by `u + s` at `fc(w, r)` is `x_u (R_* fc(w, r)) + Q ∫ log |R'| dfc(w, r)`.

So the raw cocycle at a folded circle is exactly RC3 for `x_u` at the pushed circle. At fixed
`(u, s)` this is `CoordRegComp.ae_evalReg_Yf_push` (RC3 composition law, proved), which gives
`rawCocycleFixedStmt_holds` (the input `RawCocycleFixedStmt` of `RegUnif.lean`, now
unconditional). Uniformly in `(u, s)` it is the open input `UnifRC3Stmt`, from which
`B3d.CapCocycleRegStmt` follows with `JointModStmt` (`capCocycleRegStmt_of_unifRC3`).

Source: own elementary argument (flow property `RegCont.fwdMapInv_add` in the form of
`B2.coordChange_fwdMapInv_split_fc`); the RC3 input follows Duplantier–Sheffield, Invent. Math.
185 (2011), Prop. 3.1, as formalized in `CoordRegComp`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

open B2

/-! ## Deterministic identities -/

variable {W : ℝ → ℝ}

/-- The unzip map of the driver `W(u + ·) − W u` by `s` agrees on `ℍ` with `revMap (vrev W (u+s)) s`. -/
theorem eqOn_fwdMapInv_shift (hW : Continuous W) {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) :
    EqOn (fwdMapInv (fun r => W (u + max r 0) - W u) s) (revMap (vrev W (u + s)) s) H := by
  have hWu : Continuous fun r => W (u + max r 0) - W u := by fun_prop
  have hWu0 : (fun r => W (u + max r 0) - W u) 0 = 0 := by simp
  intro z hz
  rw [CoordReg.eqOn_fwdMapInv hWu hWu0 hs hz]
  refine ReverseFlow.revMap_congr_drive z fun r hr => ?_
  show W (u + max (s - r) 0) - W u - (W (u + max s 0) - W u) = vrev W (u + s) r
  rw [vrev_of_mem ⟨hr.1, hr.2.trans (le_add_of_nonneg_left hu)⟩,
    max_eq_left (sub_nonneg.2 hr.2), max_eq_left hs]
  ring_nf

/-- **Doubly unzipped field at a folded circle.** -/
theorem double_apply_fc (γ : ℝ) (x : FieldSample) (hW : Continuous W) {u s : ℝ} (hu : 0 ≤ u)
    (hs : 0 ≤ s) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    (zipCapDown γ s (zipCapDown γ u (x, W))).1 (foldedCircle w r) =
      evalReg (unzippedField γ (x, W) u)
          ((foldedCircle w r).map (revMap (vrev W (u + s)) s)) +
        Qc γ * ∫ z, Real.log ‖deriv (revMap (vrev W (u + s)) s) z‖ ∂foldedCircle w r := by
  have hEq := eqOn_fwdMapInv_shift hW hu hs
  have hae := TwoPoint.foldedCircle_ae_mem_H w hr
  have hmap : (foldedCircle w r).map (fwdMapInv (fun r => W (u + max r 0) - W u) s) =
      (foldedCircle w r).map (revMap (vrev W (u + s)) s) :=
    Measure.map_congr (hae.mono fun z hz => hEq hz)
  have hder : ∀ᵐ z ∂foldedCircle w r,
      Real.log ‖deriv (fwdMapInv (fun r => W (u + max r 0) - W u) s) z‖ =
        Real.log ‖deriv (revMap (vrev W (u + s)) s) z‖ := by
    filter_upwards [hae] with z hz
    rw [Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hEq)]
  show coordChange (coordChange x (fwdMapInv W u) (Qc γ))
      (fwdMapInv (fun r => W (u + max r 0) - W u) s) (Qc γ) (foldedCircle w r) = _
  unfold coordChange
  rw [hmap, integral_congr_ae hder]
  rfl

/-- **Field unzipped by `u + s` at a folded circle** (the raw split of B2). -/
theorem single_apply_fc (γ : ℝ) (x : FieldSample) (hW : Continuous W) (hW0 : W 0 = 0)
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    (zipCapDown γ (u + s) (x, W)).1 (foldedCircle w r) =
      unzippedField γ (x, W) u ((foldedCircle w r).map (revMap (vrev W (u + s)) s)) +
        Qc γ * ∫ z, Real.log ‖deriv (revMap (vrev W (u + s)) s) z‖ ∂foldedCircle w r := by
  have h := coordChange_fwdMapInv_split_fc x (Qc γ) hW hW0 hs (le_add_of_nonneg_left hu) w hr
  rw [add_sub_cancel_right] at h
  exact h

/-! ## RC3 at the pushed circles, fixed times -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample} {κ : ℝ}

/-- `CoordRegComp.ae_evalReg_Yf_fc` at an arbitrary folded circle. -/
theorem ae_evalReg_Yf_fc_gen [IsProbabilityMeasure P] (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ∀ᵐ ω ∂P, evalReg (Yf κ T t B X ω) ((foldedCircle w r).map (revMap (Vr κ T B ω) t)) =
      Yf κ T t B X ω ((foldedCircle w r).map (revMap (Vr κ T B ω) t)) := by
  refine CoordRegComp.ae_evalReg_Yf_push hB hX hind ht htT (TwoPoint.foldedCircle_ae_mem_H _ hr)
    fun Vf V A hVf hV hA hVV hAV => ?_
  rw [CoordReg.h0rev_eq_logAdd κ]
  exact CoordRegComp.ae_evalReg_comp_fc hX (2 / Real.sqrt κ) continuous_const _ hVf hV hA ht
    (sub_nonneg.2 htT) hVV hAV w hr

omit [MeasurableSpace Ω] in
/-- Raw cocycle at a folded circle from RC3 at the pushed circle (pathwise). -/
theorem raw_cocycle_of_rc3 {ω : Ω} (hc : Continuous fun s => B s ω) (h0 : B 0 ω = 0)
    {u s : ℝ} (hu : 0 ≤ u) (hs : 0 ≤ s) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (h : evalReg (Yf κ (u + s) s B X ω) ((foldedCircle w r).map (revMap (Vr κ (u + s) B ω) s)) =
      Yf κ (u + s) s B X ω ((foldedCircle w r).map (revMap (Vr κ (u + s) B ω) s))) :
    (zipCapDown (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) u (cfg κ B X ω))).1
        (foldedCircle w r) =
      (zipCapDown (Real.sqrt κ) (u + s) (cfg κ B X ω)).1 (foldedCircle w r) := by
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  rw [Yf_eq_unzippedField, add_sub_cancel_right] at h
  rw [show cfg κ B X ω = (ofFun (h0rev κ) + X ω, drive κ B ω) from rfl,
    double_apply_fc _ _ hW hu hs w hr, single_apply_fc _ _ hW hW0 hu hs w hr]
  exact congrArg (· + _) h

/-! ## The uniform cocycle -/

/-- **Open input: RC3 at the pushed dyadic circles, uniformly in `(u, s)`.** -/
def UnifRC3Stmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ T → ∀ k : ℕ, ∀ d ∈ Dy,
    evalReg (Yf κ (u + s) s B X ω)
        ((foldedCircle d (radius k)).map (revMap (Vr κ (u + s) B ω) s)) =
      Yf κ (u + s) s B X ω ((foldedCircle d (radius k)).map (revMap (Vr κ (u + s) B ω) s))

/-- **`B3d.CapCocycleRegStmt` from `JointModStmt` and `UnifRC3Stmt`.** -/
theorem capCocycleRegStmt_of_unifRC3 [IsProbabilityMeasure P] {T : ℝ}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hT : 0 < T) (hJ : JointModStmt κ (Real.sqrt κ) T P B X) (hU : UnifRC3Stmt κ T P B X) :
    B3d.CapCocycleRegStmt κ T P B X := by
  filter_upwards [hU, ae_forall_isRegularWith_of_jointMod hB hX hind hT hJ, hB.cont,
    hB.eval_zero_ae_eq_zero] with ω h1 h2 hc h0
  intro u s hu hs hus
  obtain ⟨G, hG⟩ := h2
  have hraw : ∀ k : ℕ, ∀ d ∈ Dy,
      (zipCapDown (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) u (cfg κ B X ω))).1
          (foldedCircle d (radius k)) =
        (zipCapDown (Real.sqrt κ) (u + s) (cfg κ B X ω)).1 (foldedCircle d (radius k)) :=
    fun k d hd => raw_cocycle_of_rc3 hc h0 hu hs d (radius_pos k) (h1 u s hu hs hus k d hd)
  have hconv := (hG (u + s) ⟨add_nonneg hu hs, hus⟩).2
  exact ⟨regEq_of_raw_eq hraw, rawConverges_of_raw_eq hraw hconv, hconv⟩

end RegUnif
end QuantumZipper
