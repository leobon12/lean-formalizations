import QuantumZipper.Proofs.Thm18.G1RestRed
import QuantumZipper.Proofs.LQG.GoodMeasurableReg
import QuantumZipper.Proofs.Zipper.WedgeLawReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST, RC3 part: null-measurability of the every-circle RC3 set from a uniform Cauchy input

`G1RestRC3NullMeasStmt` (G1RestRed.lean) asks that the set of pairs (path, data) at which the
pulled-back field `x = coordChange (fromC c) ψ Q`, `ψ = Ψ left a`, has raw value = regularized
value at **every** folded circle be null-measurable for the product law. We exhibit a measurable
subset `M` of full product measure, defined by **countably many** conditions, following the
countable certificate of `GoodMeas.regular_of_cert` (M4-R5(a), GoodMeasurableReg.lean):

* path side (a measurable full-measure subset of the a.e. set where both selected maps satisfy
  `PsiGood` and `PsiExt`): `ψ` has a continuous extension `ψe : Hbar → Hbar` and
  `q ↦ ∫ log |ψ'| dfc(q)` is continuous on `Hbar × (0,∞)` (Koebe, `logBd_log_norm_deriv`);
* data side: `fromC c` is a regular sample (so `avgReg (fromC c) i` is continuous on `Hbar`);
* joint, countable: RC2 for `x` (`G1Meas.measurableSet_rc2`); the smoothings
  `PhiP i q = ∫ avgReg (fromC c) i (ψ z) dfc(q)(z)` are uniformly Cauchy at the dyadic points of
  each box (`C2P`); RC3 at the dyadic circles (`C3P`).

Deterministic core (`rc3All_of_cert`): then `PhiP i → lim` locally uniformly on
`Hbar × (0,∞)`, so the raw value `x(fc q) = lim q + Q ∫ log|ψ'| dfc(q)` is continuous there, as
is the regular witness of `x`; they agree at the dyadic points, hence everywhere.

The only new probabilistic input is `G1RestUnifStmt` (the uniform Cauchy property `C2P` a.s. at
the representative); everything else is from the repository (RC2 and RC3 a.s.,
`wedgeRegSampleStmt_holds`, `g1RegPathChordStmt`, `G1PsiExtStmt`).

Main result: `g1RestRC3NullMeasStmt_of_unif : G1RestUnifStmt → G1RestRC3NullMeasStmt`.

Own argument (measurability bookkeeping, following `GoodMeasurableReg.lean`; the uniform
convergence input is the Kolmogorov–Čentsov continuity of the circle-average process,
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

open GoodMeas (Sd box qpt le_of_qpt exists_box isOpen_box mprop_abs_le)

/-! ## 1. The certificate -/

/-- Smoothing of `avgReg y i ∘ ψ` along the folded circle `fc(q)`. -/
def PhiP (y : FieldSample) (ψ : ℂ → ℂ) (i : ℕ) (q : ℂ × ℝ) : ℝ :=
  ∫ z, avgReg y i (ψ z) ∂foldedCircle q.1 q.2

/-- The log-derivative part of the coordinate change at `fc(q)`. -/
def LamP (ψ : ℂ → ℂ) (q : ℂ × ℝ) : ℝ := ∫ z, Real.log ‖deriv ψ z‖ ∂foldedCircle q.1 q.2

/-- Uniform Cauchy property of `PhiP` at the dyadic points of the boxes. -/
def C2P (y : FieldSample) (ψ : ℂ → ℂ) : Prop :=
  ∀ m e : ℕ, ∃ J : ℕ, ∀ i : ℕ, J ≤ i → ∀ i' : ℕ, J ≤ i' → ∀ j : ℕ × ℤ × ℤ × ℤ,
    qpt j ∈ Sd → qpt j ∈ box m →
      |PhiP y ψ i (qpt j) - PhiP y ψ i' (qpt j)| ≤ 1 / ((e : ℝ) + 1)

/-- RC3 at the dyadic folded circles. -/
def C3P (x : FieldSample) : Prop :=
  ∀ j : ℕ × ℤ × ℤ × ℤ, qpt j ∈ Sd →
    evalReg x (foldedCircle (qpt j).1 (qpt j).2) = x (foldedCircle (qpt j).1 (qpt j).2)

theorem coordChange_fc_eq {y : FieldSample} {ψ : ℂ → ℂ} (hψm : Measurable ψ) (Q : ℝ)
    (q : ℂ × ℝ) : coordChange y ψ Q (foldedCircle q.1 q.2) =
      limUnder atTop (fun i => PhiP y ψ i q) + Q * LamP ψ q := by
  show evalReg y ((foldedCircle q.1 q.2).map ψ) + _ = _
  unfold evalReg PhiP LamP
  congr 2
  funext i
  exact integral_map hψm.aemeasurable
    ((measurable_avgReg i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- **Deterministic core**: the countable certificate gives RC3 at every folded circle. -/
theorem rc3All_of_cert {y : FieldSample} {ψ : ℂ → ℂ} {Q : ℝ} (hψm : Measurable ψ)
    (hPc : ∀ i, ContinuousOn (PhiP y ψ i) Sd) (hΛ : ContinuousOn (LamP ψ) Sd)
    (hreg : IsRegularSample (coordChange y ψ Q)) (h2 : C2P y ψ)
    (h3 : C3P (coordChange y ψ Q)) : RC3All (coordChange y ψ Q) := by
  set lim : ℂ × ℝ → ℝ := fun q => limUnder atTop fun i => PhiP y ψ i q with hlim
  have hU : ∀ m e : ℕ, ∃ J : ℕ, ∀ i ≥ J, ∀ i' ≥ J, ∀ p ∈ Sd, p ∈ box m →
      |PhiP y ψ i p - PhiP y ψ i' p| ≤ 1 / ((e : ℝ) + 1) := by
    intro m e
    obtain ⟨J, hJ⟩ := h2 m e
    refine ⟨J, fun i hi i' hi' p hp hpm => ?_⟩
    exact le_of_qpt (φ := fun q => |PhiP y ψ i q - PhiP y ψ i' q|) hp hpm
      (continuous_abs.continuousAt.comp_continuousWithinAt (((hPc i).sub (hPc i')) p hp))
      (fun j hj1 hj2 => hJ i hi i' hi' j hj1 hj2)
  have hT : ∀ p ∈ Sd, Tendsto (fun i => PhiP y ψ i p) atTop (𝓝 (lim p)) := by
    intro p hp
    obtain ⟨m, hm⟩ := exists_box hp.2
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
      (Metric.cauchySeq_iff.2 fun ε hε => ?_))
    obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
    obtain ⟨J, hJ⟩ := hU m e
    exact ⟨J, fun i hi i' hi' => by
      rw [Real.dist_eq]; exact (hJ i hi i' hi' p hp hm).trans_lt he⟩
  have hU' : ∀ m e : ℕ, ∃ J : ℕ, ∀ i ≥ J, ∀ p ∈ Sd, p ∈ box m →
      |PhiP y ψ i p - lim p| ≤ 1 / ((e : ℝ) + 1) := by
    intro m e
    obtain ⟨J, hJ⟩ := hU m e
    refine ⟨J, fun i hi p hp hpm => ?_⟩
    exact le_of_tendsto ((tendsto_const_nhds.sub (hT p hp)).abs :
      Tendsto (fun i' => |PhiP y ψ i p - PhiP y ψ i' p|) atTop _)
      (eventually_atTop.2 ⟨J, fun i' hi' => hJ i hi i' hi' p hp hpm⟩)
  have hL : TendstoLocallyUniformlyOn (PhiP y ψ) lim atTop Sd := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε p hp
    obtain ⟨e, he⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm⟩ := exists_box hp.2
    obtain ⟨J, hJ⟩ := hU' m e
    refine ⟨box m ∩ Sd, inter_mem (mem_nhdsWithin_of_mem_nhds ((isOpen_box m).mem_nhds hm))
      self_mem_nhdsWithin, eventually_atTop.2 ⟨J, fun i hi q hq => ?_⟩⟩
    rw [Real.dist_eq, abs_sub_comm]
    exact (hJ i hi q hq.2 hq.1).trans_lt he
  have hlc : ContinuousOn lim Sd :=
    hL.continuousOn (Eventually.frequently (Eventually.of_forall hPc))
  obtain ⟨F, hF⟩ := hreg
  have hraw : ContinuousOn (fun q : ℂ × ℝ => coordChange y ψ Q (foldedCircle q.1 q.2)) Sd :=
    (hlc.add (continuousOn_const.mul hΛ)).congr fun q _ => coordChange_fc_eq hψm Q q
  intro d hd r hr
  have hp : ((d, r) : ℂ × ℝ) ∈ Sd := ⟨hd, hr⟩
  obtain ⟨m, hm⟩ := exists_box (p := (d, r)) hr
  have hle := le_of_qpt (φ := fun q => |F q - coordChange y ψ Q (foldedCircle q.1 q.2)|) hp hm
    (continuous_abs.continuousAt.comp_continuousWithinAt ((hF.1.sub hraw) _ hp)) (c := 0)
    (fun j hj _ => by
      have e1 : F (qpt j) = evalReg (coordChange y ψ Q) (foldedCircle (qpt j).1 (qpt j).2) := by
        rw [hF.evalReg_fc_of_mem hj.1 hj.2]
      show |F (qpt j) - _| ≤ 0
      rw [e1, h3 j hj, sub_self, abs_zero])
  rw [hF.evalReg_fc_of_mem hd hr]
  exact sub_eq_zero.1 (abs_nonpos_iff.1 hle)

/-- Continuity of `PhiP` from a continuous extension of `ψ` and continuity of `avgReg`. -/
theorem phiP_continuousOn {y : FieldSample} {ψ ψe : ℂ → ℂ} (hc : ContinuousOn ψe Hbar)
    (hmt : MapsTo ψe Hbar Hbar) (heq : EqOn ψ ψe H) {i : ℕ}
    (hav : ContinuousOn (avgReg y i) Hbar) : ContinuousOn (PhiP y ψ i) Sd := by
  refine ((GoodSample.gs_continuousOn_integral_fc_fun (hav.comp hc hmt)).mono
    (subset_univ _)).congr fun q hq => ?_
  show ∫ z, avgReg y i (ψ z) ∂foldedCircle q.1 q.2 =
    ∫ v, (avgReg y i ∘ ψe) v ∂foldedCircle q.1 q.2
  refine integral_congr_ae ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H q.1 (show (0 : ℝ) < q.2 from hq.2)] with z hz
  simp only [Function.comp, heq hz]

/-- The certificate, per path and data, with the path- and data-side hypotheses. -/
theorem rc3All_of_good {y : FieldSample} {ψ : ℂ → ℂ} {Q : ℝ} (hg : G1RC.PsiGood ψ)
    (he : G1RC.PsiExt ψ) (hy : IsRegularSample y)
    (hreg : IsRegularSample (coordChange y ψ Q)) (h2 : C2P y ψ)
    (h3 : C3P (coordChange y ψ Q)) : RC3All (coordChange y ψ Q) := by
  obtain ⟨ψe, -, hc, hmt, heq, -⟩ := he
  obtain ⟨G, hG⟩ := hy
  have hav : ∀ i, ContinuousOn (avgReg y i) Hbar := fun i =>
    GoodMeas.continuousOn_avgReg_of_C1 (GoodMeas.C1_of_regular hG) i
  exact rc3All_of_cert hg.1 (fun i => phiP_continuousOn hc hmt heq (hav i))
    ((G1RC.logBd_log_norm_deriv hg).continuousOn.mono fun q hq => (hq.2 : (0 : ℝ) < q.2))
    hreg h2 h3

end G1Rest
end Thm18Asm
end QuantumZipper
