import QuantumZipper.Proofs.Zipper.XFlowClose
import QuantumZipper.Proofs.Zipper.WedgeYGoodExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WEDGE-CORE: `YExactAllStmt` proved from the free-field flow chain

`WedgeUnzip.YExactAllStmt` (RC3 of the unzipped `Γ⁰` field `y_t` on **every** folded circle, at
every time) follows pathwise from the proved five-parameter locally uniform convergence of the
`x`-pairings (`F1.xFlowUCStmt_holds`), the proved deterministic log node
(`F1.xFlowLogUCStmt_holds`), X-X (`F1.xExactAllStmt_holds`), the `Γ⁰` JointMod witness
(`RegUnif.ae_exists_joint_witness`), RegShift along unzipped dyadic circles
(`RegUnif.gaugeRegDyStmt_holds`) and exactness of the time-`0` fields at the enumerated circles
(Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1, via
`CoordReg.ae_evalReg_logAdd_eq_frostman`).

Route (own bookkeeping, no new analytic input). With `p₁ = (t, 0, d, r)`, `p₀ = (0, t, d, r)`,
`Λ(p) = ∫ log|f_u⁻¹| dν_p`, and the pathwise split `Φ^y_j = Φ_j + √κ L_j`
(`F1.flowPhi_eq_split`):

* regularized side: `evalReg y_t fc = lim Φ^y_j(p₁) = evalReg x_t fc + √κ Λ(p₁)`;
* raw side: `y_t fc − x_t fc = evalReg y ν − evalReg x ν` (`ν = (f_t⁻¹)_* fc`), and both are the
  limits at `p₀` (time-`0` fields have the same `avgReg`), so `y_t fc = x_t fc + √κ Λ(p₀)`;
* `Λ(p₀) = Λ(p₁) = ∫ log|f_t⁻¹| dfc` (flow identity `f_t⁻¹ = R_{0,t}` on `ℍ`);
* X-X closes: `evalReg x_t fc = x_t fc`.

Main result: `yExactAllStmt_holds : YExactAllStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

open F1 RegUnif RegCont TwoPoint

/-- On `ℍ`, `f_t⁻¹ = R_{0,t}` (the flow identity at `u = t`, `s = 0`). -/
theorem fwdMapInv_eq_revMap_vrev {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv W t z = revMap (B2.vrev W t) t z := by
  have h := fwdMapInv_revMap_comp hW hW0 ht (le_refl (0 : ℝ)) hz
  simp only [add_zero, zero_add] at h
  rwa [CharFun.revMap_zero_eq (B2.continuous_vrev hW t) (B2.vrev_zero ht) hz] at h

/-- `ν_{(0,t,d,r)} = (f_t⁻¹)_* fc(d, r)`. -/
theorem flowNu_zero_left {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    flowNu W (0, t, d, r) = (foldedCircle d r).map (fwdMapInv W t) := by
  show (foldedCircle d r).map (revMap (B2.vrev W (0 + t)) t) = _
  rw [zero_add]
  exact Measure.map_congr ((foldedCircle_ae_mem_H d hr).mono fun z hz =>
    (fwdMapInv_eq_revMap_vrev hW hW0 ht hz).symm)

/-- `ν_{(t,0,d,r)} = fc(d, r)`. -/
theorem flowNu_zero_right {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    flowNu W (t, 0, d, r) = foldedCircle d r := by
  show (foldedCircle d r).map (revMap (B2.vrev W (t + 0)) 0) = _
  rw [add_zero]
  have h : revMap (B2.vrev W t) 0 =ᵐ[foldedCircle d r] id :=
    (foldedCircle_ae_mem_H d hr).mono fun z hz =>
      CharFun.revMap_zero_eq (B2.continuous_vrev hW t) (B2.vrev_zero ht) hz
  rw [Measure.map_congr h, Measure.map_id]

/-- `Λ(0, t, d, r) = ∫ log|f_t⁻¹| dfc(d, r)`. -/
theorem logInt_zero_left {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ w, Real.log ‖fwdMapInv W 0 w‖ ∂flowNu W (0, t, d, r) =
      ∫ z, Real.log ‖fwdMapInv W t z‖ ∂foldedCircle d r := by
  have hV := B2.continuous_vrev hW t
  have hRm : Measurable (revMap (B2.vrev W t) t) := measurable_revMap hV ht
  have e : flowNu W (0, t, d, r) = (foldedCircle d r).map (revMap (B2.vrev W t) t) := by
    show (foldedCircle d r).map (revMap (B2.vrev W (0 + t)) t) = _
    rw [zero_add]
  have hH : ∀ᵐ w ∂(foldedCircle d r).map (revMap (B2.vrev W t) t), w ∈ H :=
    (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
      ((foldedCircle_ae_mem_H d hr).mono fun z hz => im_revMap_pos hV hz ht)
  have hm : Measurable fun w : ℂ => Real.log ‖w‖ := Real.measurable_log.comp measurable_norm
  rw [e, integral_congr_ae (hH.mono fun w hw => by
      show Real.log ‖fwdMapInv W 0 w‖ = Real.log ‖w‖
      rw [Thm18Asm.G1Pkg.fwdMapInv_zero_time hW (show 0 < w.im from hw), hW0]
      simp),
    integral_map hRm.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae ((foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
  show Real.log ‖revMap (B2.vrev W t) t z‖ = Real.log ‖fwdMapInv W t z‖
  rw [fwdMapInv_eq_revMap_vrev hW hW0 ht hz]

/-- `Λ(t, 0, d, r) = ∫ log|f_t⁻¹| dfc(d, r)`. -/
theorem logInt_zero_right {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    (d : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ w, Real.log ‖fwdMapInv W (t, (0 : ℝ), d, r).1 w‖ ∂flowNu W (t, 0, d, r) =
      ∫ z, Real.log ‖fwdMapInv W t z‖ ∂foldedCircle d r := by
  rw [flowNu_zero_right hW ht d hr]

/-- **The `Γ⁰` pairings converge at every flow parameter**, to `L + √κ Λ`. -/
theorem tendsto_flowPhiY_of_uc (κ : ℝ) {X : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {L : ℝ × ℝ × ℂ × ℝ → ℝ}
    (hUC : TendstoLocallyUniformlyOn (fun j => flowPhi κ X W j) L atTop flowPar)
    (hR : ∀ u : ℝ, 0 ≤ u → ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (ofFun (h0rev κ) + X)
      ((foldedCircle d (radius k)).map (fwdMapInv W u)))
    (hF : ∀ u : ℝ, 0 ≤ u → ∃ F : ℂ × ℝ → ℝ,
      IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X, W) u) F)
    {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowPar) :
    Tendsto (fun j => flowPhi κ X W j p) atTop (𝓝 (L p)) ∧
    Tendsto (fun j => flowPhiY κ X W j p) atTop
      (𝓝 (L p + Real.sqrt κ * ∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂flowNu W p)) := by
  have h1 := hUC.tendsto_at hp
  obtain ⟨m, hm⟩ := flowBox_mem_nhdsWithin hp
  have h2 := (xFlowLogUCStmt_holds W hW hW0 m).tendsto_at (mem_of_mem_nhdsWithin hp hm)
  refine ⟨h1, ?_⟩
  obtain ⟨u, s, d, r⟩ := p
  obtain ⟨hu, hs, -, hr⟩ := hp
  obtain ⟨F, hF'⟩ := hF u hu
  refine (h1.add (h2.const_mul (Real.sqrt κ))).congr fun j => ?_
  rw [flowPhi_eq_split κ hW hW0 d hu hs hr (hR u hu) hF' j]
  ring

/-- Time-`0` fields exact at the enumerated circles have the time-`0` `avgReg`. -/
theorem evalReg_unzip_zero_eq {γ : ℝ} {y : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0)
    (hy : ∀ i : ℕ, evalReg y (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      y (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)) (ν : Measure ℂ) :
    evalReg (unzippedField γ (y, W) 0) ν = evalReg y ν := by
  refine evalReg_congr_avgReg (fun k z => ?_) ν
  unfold avgReg
  congr 1
  funext n
  exact (RegUnif.raw_unzip_zero_eq γ hW hW0 hy n k z).symm

/-- **Pathwise raw identity** `y_t fc = x_t fc + √κ ∫ log|f_t⁻¹| dfc` on every folded circle. -/
theorem unzY_fc_eq_pathwise (κ : ℝ) {X : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {L : ℝ × ℝ × ℂ × ℝ → ℝ}
    (hUC : TendstoLocallyUniformlyOn (fun j => flowPhi κ X W j) L atTop flowPar)
    (hR : ∀ u : ℝ, 0 ≤ u → ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (ofFun (h0rev κ) + X)
      ((foldedCircle d (radius k)).map (fwdMapInv W u)))
    (hF : ∀ u : ℝ, 0 ≤ u → ∃ F : ℂ × ℝ → ℝ,
      IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X, W) u) F)
    (hfx : ∀ i : ℕ, evalReg (X + F2.logSingField κ)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (X + F2.logSingField κ) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    {t : ℝ} (ht : 0 ≤ t) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    F2.unzY κ X W t (foldedCircle d r) = F2.unzX κ X W t (foldedCircle d r) +
      Real.sqrt κ * ∫ z, Real.log ‖fwdMapInv W t z‖ ∂foldedCircle d r := by
  have hp0 : ((0, t, d, r) : ℝ × ℝ × ℂ × ℝ) ∈ flowPar := ⟨le_rfl, ht, hd, hr⟩
  obtain ⟨a0, b0⟩ := tendsto_flowPhiY_of_uc κ hW hW0 hUC hR hF hp0
  rw [logInt_zero_left hW hW0 ht d hr] at b0
  have hν0 := flowNu_zero_left hW hW0 ht d hr
  have rY : F2.unzY κ X W t (foldedCircle d r) =
      evalReg (ofFun (h0rev κ) + X) ((foldedCircle d r).map (fwdMapInv W t)) +
        Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (fwdMapInv W t) z‖ ∂foldedCircle d r := by
    rw [unzY_eq_h0]; rfl
  have rX : F2.unzX κ X W t (foldedCircle d r) =
      evalReg (X + F2.logSingField κ) ((foldedCircle d r).map (fwdMapInv W t)) +
        Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (fwdMapInv W t) z‖ ∂foldedCircle d r := rfl
  have gY : evalReg (ofFun (h0rev κ) + X) ((foldedCircle d r).map (fwdMapInv W t)) =
      L (0, t, d, r) + Real.sqrt κ * ∫ z, Real.log ‖fwdMapInv W t z‖ ∂foldedCircle d r := by
    rw [← hν0, ← evalReg_unzip_zero_eq (γ := Real.sqrt κ) hW hW0 hfy]
    exact b0.limUnder_eq
  have gX : evalReg (X + F2.logSingField κ) ((foldedCircle d r).map (fwdMapInv W t)) =
      L (0, t, d, r) := by
    rw [← hν0, ← evalReg_unzip_zero_eq (γ := Real.sqrt κ) hW hW0 hfx]
    exact a0.limUnder_eq
  rw [rY, rX, gY, gX]
  ring

/-- **Pathwise `YExactAll`.** -/
theorem yExact_pathwise (κ : ℝ) {X : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {L : ℝ × ℝ × ℂ × ℝ → ℝ}
    (hUC : TendstoLocallyUniformlyOn (fun j => flowPhi κ X W j) L atTop flowPar)
    (hR : ∀ u : ℝ, 0 ≤ u → ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (ofFun (h0rev κ) + X)
      ((foldedCircle d (radius k)).map (fwdMapInv W u)))
    (hF : ∀ u : ℝ, 0 ≤ u → ∃ F : ℂ × ℝ → ℝ,
      IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X, W) u) F)
    (hfx : ∀ i : ℕ, evalReg (X + F2.logSingField κ)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (X + F2.logSingField κ) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hXX : ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (F2.unzX κ X W t) (foldedCircle d r) = F2.unzX κ X W t (foldedCircle d r))
    {t : ℝ} (ht : 0 ≤ t) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r) :
    evalReg (F2.unzY κ X W t) (foldedCircle d r) = F2.unzY κ X W t (foldedCircle d r) := by
  have hp1 : ((t, 0, d, r) : ℝ × ℝ × ℂ × ℝ) ∈ flowPar := ⟨ht, le_rfl, hd, hr⟩
  obtain ⟨a1, b1⟩ := tendsto_flowPhiY_of_uc κ hW hW0 hUC hR hF hp1
  rw [logInt_zero_right hW ht d hr] at b1
  have hν1 := flowNu_zero_right hW ht d hr
  have eY : evalReg (F2.unzY κ X W t) (foldedCircle d r) = L (t, 0, d, r) +
      Real.sqrt κ * ∫ z, Real.log ‖fwdMapInv W t z‖ ∂foldedCircle d r := by
    rw [unzY_eq_h0]
    exact (congrArg _ hν1.symm).trans b1.limUnder_eq
  have eX : evalReg (F2.unzX κ X W t) (foldedCircle d r) = L (t, 0, d, r) := by
    rw [← hν1]
    exact a1.limUnder_eq
  have hx := hXX t ht d hd r hr
  rw [eX] at hx
  rw [eY, unzY_fc_eq_pathwise κ hW hW0 hUC hR hF hfx hfy ht hd hr, ← hx]

/-- **The almost-sure pathwise inputs** (all proved nodes). -/
theorem ae_core2Y_inputs {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 ∧
      (∃ L : ℝ × ℝ × ℂ × ℝ → ℝ, TendstoLocallyUniformlyOn
        (fun j => flowPhi κ (X ω) (drive κ B ω) j) L atTop flowPar) ∧
      (∀ u : ℝ, 0 ≤ u → ∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (ofFun (h0rev κ) + X ω)
        ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) u))) ∧
      (∀ u : ℝ, 0 ≤ u → ∃ F : ℂ × ℝ → ℝ,
        IsRegularWith (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) u) F) ∧
      (∀ i : ℕ, evalReg (X ω + F2.logSingField κ)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
        (X ω + F2.logSingField κ) (foldedCircle (CoordsFull.fullIndex i).1
          (CoordsFull.fullIndex i).2)) ∧
      (∀ i : ℕ, evalReg (ofFun (h0rev κ) + X ω)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
        (ofFun (h0rev κ) + X ω) (foldedCircle (CoordsFull.fullIndex i).1
          (CoordsFull.fullIndex i).2)) := by
  have hwit : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ Z : ℝ × (ℂ × ℝ) → ℝ, ContinuousOn Z (parSet ((n : ℝ) + 1)) ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), IsRegularWith
        (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t) (fun p => Z (t, p)) :=
    ae_all_iff.2 fun n => ae_exists_joint_witness (κ := κ) (γ := Real.sqrt κ) hB hX hind
      (by positivity)
  have hreg : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) ((n : ℝ) + 1),
      (∀ k : ℕ, ∀ d ∈ Dy, E1.RegShift (B2.cfg κ B X ω).1
        ((foldedCircle d (radius k)).map (fwdMapInv (drive κ B ω) s))) ∧
        Cor15Group.BdryConvAE (B2.h0f κ s B X ω) :=
    ae_all_iff.2 fun n => gaugeRegDyStmt_holds hB hX hind (by positivity)
  have hfx : ∀ᵐ ω ∂P, ∀ i : ℕ, evalReg (X ω + F2.logSingField κ)
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (X ω + F2.logSingField κ) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2) := by
    refine ae_all_iff.2 fun i => ?_
    have hr := UnzipFull.fullIndex_radius_pos i
    have h := CoordReg.ae_evalReg_logAdd_eq_frostman hX
      (ν := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)
      (CircleFubini.foldedCircle_support hr.le le_rfl)
      (Cor15Group.isFrostman_fc _ hr) one_pos (-(Real.sqrt κ - 2 / Real.sqrt κ))
      (g₁ := fun _ => (0 : ℝ)) continuousOn_const
    refine h.mono fun ω hω => ?_
    rw [logSing_eq_logAdd]
    exact hω
  have hfy : ∀ᵐ ω ∂P, ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X ω)
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X ω) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2) := by
    refine ae_all_iff.2 fun i => ?_
    have hr := UnzipFull.fullIndex_radius_pos i
    have h := CoordReg.ae_evalReg_logAdd_eq_frostman hX
      (ν := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)
      (CircleFubini.foldedCircle_support hr.le le_rfl)
      (Cor15Group.isFrostman_fc _ hr) one_pos (2 / Real.sqrt κ)
      (g₁ := fun _ => (0 : ℝ)) continuousOn_const
    refine h.mono fun ω hω => ?_
    rw [CoordReg.h0rev_eq_logAdd]
    exact hω
  filter_upwards [hwit, hreg, hfx, hfy, hB.cont, hB.eval_zero_ae_eq_zero,
    xFlowUCStmt_holds κ hκ hκ4 P B X hB hX hind] with ω hZ hRg hfxω hfyω hc h0 hUC
  have hW : Continuous (drive κ B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have huT : ∀ u : ℝ, 0 ≤ u → u ∈ Icc (0 : ℝ) ((⌈u⌉₊ : ℝ) + 1) := fun u hu =>
    ⟨hu, by linarith [Nat.le_ceil u]⟩
  refine ⟨hW, hW0, hUC, fun u hu => (hRg _ u (huT u hu)).1, fun u hu => ?_, hfxω, hfyω⟩
  obtain ⟨Z, -, hZr⟩ := hZ ⌈u⌉₊
  exact ⟨_, hZr u (huT u hu)⟩

/-- **`YExactAllStmt` holds.** -/
theorem yExactAllStmt_holds : YExactAllStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [ae_core2Y_inputs hκ hκ4 hB hX hind,
    xExactAllStmt_holds κ hκ hκ4 P B X hB hX hind]
    with ω ⟨hW, hW0, ⟨L, hL⟩, hR, hF, hfx, hfy⟩ hXX t ht d hd r hr
  exact yExact_pathwise κ hW hW0 hL hR hF hfx hfy hXX ht hd hr

end WedgeUnzip
end QuantumZipper
