import QuantumZipper.Proofs.Zipper.B5VHccMeas
import QuantumZipper.Proofs.Zipper.B5VFixWin

/-!
# B5V-HCC, the independent side: the window event holds a.s. for a fixed driver

Task B5V-HCC (`handoff/B5.md`). For a fixed continuous path `w` on `[0,t]` and a free field `X'`,
almost surely the data `(coordsFull (nrm (𝔥₀ + X')), w)` lie in the window event
`eqP κ ht u v` (**`ae_mem_eqP_fixed`**). This is `B5.ae_qBoundaryMeasureOn_hFix_window` (the
coordinate-change rule at a fixed driver; Sheffield, arXiv:1012.4797, proof of Lemma 5.6,
pp. 66–68) read through the coordinates: the normalization `nrm` shifts both sides by the same
additive constant `c₀`, and both boundary measures scale by `e^{−γ c₀/2}`
(`LocalRule.qBoundaryMeasureOn_addConst`, `LocalRule.qBoundaryMeasure_addConst'`), using
`RegShift` along the pushed circles (`E1.ae_regShift_h0X_fc`) and raw convergence of the circle
averages. Also the deterministic coordinate identities used on both sides
(`coordsFull_Zr`, `coordsFull_coordChange_fromC_nrm`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

open E1 E1.M4 CoordsFull Collision B1Full B2

theorem evalReg_zero_measure (x : FieldSample) : evalReg x 0 = 0 := by
  unfold evalReg
  simp only [integral_zero_measure]
  exact tendsto_const_nhds.limUnder_eq

theorem coordsFull_Zr (κ : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : DP t) :
    coordsFull (Zr κ ht p) =
      coordsFull (coordChange (fromC p.1) (revMap (CharFun.Wof 1 t ht p.2) t) (Qc (Real.sqrt κ))) := by
  have hm : mC κ ht 0 p = 0 := by
    simp [mC, varpiT, qt, evalReg_zero_measure]
  rw [Zr, zR, coordsFull_fromC, zC, hm]
  funext i
  rw [coordsFull_addConst, neg_zero, add_zero]

theorem coordsFull_coordChange_fromC_nrm {V : ℝ → ℝ} {t Q : ℝ} {Y : FieldSample}
    (h2 : ∀ i, RegShift Y (pfc V t i)) :
    coordsFull (coordChange (fromC (coordsFull (nrm Y))) (revMap V t) Q) =
      coordsFull (addConst (coordChange Y (revMap V t) Q) (-(Y (foldedCircle 0 1)))) := by
  have hc := coordsFull_fromC (nrm Y)
  have e1 : evalReg (fromC (coordsFull (nrm Y))) = evalReg (nrm Y) :=
    funext (evalReg_congr_coordsFull hc)
  have e2 : coordChange (fromC (coordsFull (nrm Y))) = coordChange (nrm Y) := by
    funext F Q μ; simp only [coordChange, e1]
  rw [e2]
  have : ∀ i, IsProbabilityMeasure (pfc V t i) := fun i => by unfold pfc; infer_instance
  funext i
  simp only [coordsFull_addConst]
  simp only [coordsFull, coordChange, nrm]
  rw [evalReg_addConst_of_regShift (h2 i)]
  ring

/-- Raw convergence of `𝔥₀ + x` from that of `x`. -/
theorem rawConverges_h0rev_add (κ : ℝ) {x : FieldSample} (hx : LocalRule.RawConverges x Hbar) :
    LocalRule.RawConverges (ofFun (h0rev κ) + x) Hbar := by
  intro k z hz
  rw [CoordReg.h0rev_eq_logAdd κ]
  exact CoordReg.exists_tendsto_raw_ofFun_logAdd _ continuousOn_const (hx k z hz)

/-- On the certificate, the guarded measure of an open set is the local boundary measure. -/
theorem gM_Ioo_eq {κ : ℝ} {x : FieldSample} (h : BCert (Real.sqrt κ) x) (u v : ℝ) :
    gM κ x (Ioo u v) = qBoundaryMeasureOn (Real.sqrt κ) x (Ioo u v) (Ioo u v) := by
  rw [gM, if_pos h, LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo (InfMass.isVagueLimitOnR_restrict
    (isVagueLimitR_qBoundaryMeasure (exists_isVagueLimitR_of_bCert h)) isOpen_Ioo),
    Measure.restrict_apply_self]

variable {Ω : Type} [MeasurableSpace Ω] {P' : Measure Ω} [IsProbabilityMeasure P']
  {X' : Ω → FieldSample}

/-- **The window event holds a.s. for a fixed driver path.** -/
theorem ae_mem_eqP_fixed {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hX : IsFreeGFFModConstH X' P')
    {t : ℝ} (ht : 0 ≤ t) (w : C(Icc (0 : ℝ) t, ℝ)) {u v : ℝ} (huv : u < v) :
    ∀ᵐ ω ∂P', (coordsFull (nrm (ofFun (h0rev κ) + X' ω)), w) ∈ eqP κ ht u v := by
  set W := CharFun.Wof 1 t ht w with hWdef
  have hWc : Continuous W := CharFun.continuous_Wof 1 t ht w
  by_cases hgw : w ⟨0, ⟨le_rfl, ht⟩⟩ = 0 ∧ v ∈ liveNeg W t
  swap
  · exact Eventually.of_forall fun ω => Or.inl fun hg => hgw hg.1.1
  obtain ⟨hw0, hv⟩ := hgw
  have hW0 : W 0 = 0 := by simp [hWdef, CharFun.Wof, projIcc_left, hw0]
  have hwin : ∀ x ∈ Icc u v, x < 0 ∧ IsLive W t x := fun x hx =>
    ⟨hx.2.trans_lt hv.1, hv.2.trans_le (realHitTime_anti hWc hx.2 (by rw [hW0]; exact hv.1))⟩
  set γ := Real.sqrt κ with hγ
  filter_upwards [ae_qBoundaryMeasureOn_hFix_window hκ hκ4 hX hWc hW0 ht huv hwin,
    ae_all_iff.2 fun i => ae_regShift_h0X_fc (κ := κ) hX hWc ht i,
    CoordReg.ae_isRegularSample_coordChange_h0rev' hWc ht hX κ (Qc γ),
    RegSample.ae_isRegularSample hX] with ω hid hrs hregF hregX
  by_cases hg : (coordsFull (nrm (ofFun (h0rev κ) + X' ω)), w) ∈ goodP κ ht v
  swap
  · exact Or.inl hg
  right
  set Y := ofFun (h0rev κ) + X' ω with hY
  set c0 := Y (foldedCircle 0 1) with hc0
  set p : DP t := (coordsFull (nrm Y), w) with hp
  obtain ⟨⟨-, hC⟩, hC1⟩ := hg
  have hZ : coordsFull (Zr κ ht p) = coordsFull (addConst (hFix κ W t (X' ω)) (-c0)) :=
    (coordsFull_Zr κ ht p).trans (coordsFull_coordChange_fromC_nrm hrs)
  have hF : coordsFull (fromC p.1) = coordsFull (addConst Y (-c0)) := coordsFull_fromC (nrm Y)
  have hrY : LocalRule.RawConverges Y Hbar := rawConverges_h0rev_add κ hregX.rawConverges
  have hu : IsLive W t u := (hwin u ⟨le_rfl, huv.le⟩).2
  have hu0 : u < W 0 := by rw [hW0]; exact (hwin u ⟨le_rfl, huv.le⟩).1
  have hv0 : v < W 0 := by rw [hW0]; exact hv.1
  show gM κ (Zr κ ht p) (Ioo u v) = gM κ (fromC p.1) (Ioo (Fm t ht u w) (Fm t ht v w))
  rw [gM_Ioo_eq hC, qBoundaryMeasureOn_congr_full hZ,
    LocalRule.qBoundaryMeasureOn_addConst (x := hFix κ W t (X' ω)) hregF.rawConverges _ _ isOpen_Ioo,
    Measure.smul_apply,
    hid, gM, if_pos (show BCert (Real.sqrt κ) (fromC p.1) from hC1), qBoundaryMeasure_congr_full hF,
    LocalRule.qBoundaryMeasure_addConst' hrY, Measure.smul_apply,
    Fm_eq_realRevMap ht hu hu0, Fm_eq_realRevMap ht hv.2 hv0]

end B5
end QuantumZipper
