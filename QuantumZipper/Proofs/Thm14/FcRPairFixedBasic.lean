import QuantumZipper.Proofs.Field.TRegE4
import QuantumZipper.Proofs.Zipper.B2Reg
import QuantumZipper.Proofs.LQG.WedgeToolkit

/-!
# FCR-PAIR, part 2: fixed-driver probabilistic tools

For a fixed continuous driver `W` and `f = revMap W T`:

* `fc_push_regular`, `tdens_push_regular`: the pushforwards under `f` of a folded circle of
  positive radius (also for real centres, i.e. semicircles) and of a bounded compactly supported
  density in `ℍ` are finite measures with bounded support in `Hbar` and a Frostman bound of
  positive exponent (`UnzipFull.Inputs.frost` = `TwoPoint.isFrostman_revMap_foldedCircle`,
  `B2.isFrostman_map_revMap_of_compact`);
* `ae_evalReg_eq_of_regular`: for such measures `evalReg (X ω) ν = X ω ν` a.s. (RC1,
  `FrostmanReg.ae_tendsto_integral_avgReg_frostman`, Duplantier–Sheffield, *Liouville quantum
  gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1 and its proof);
* `admissible_of_regular`: they are admissible (`FrostmanReg.isAdmissibleH_of_frostman`);
* `prob_ge_le_kernelCov2`: Chebyshev for a balanced admissible pair,
  `P(c ≤ |X μ − X ν|) ≤ kernelCov2 neumannH (μ,ν) (μ,ν) / c²`.

Own bookkeeping around the cited inputs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

open CharFun

/-- Regularity package used by RC1: bounded support in `Hbar` and a Frostman bound. -/
def PushRegular (ν : Measure ℂ) : Prop :=
  ∃ R α C : ℝ, 0 < α ∧ ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0 ∧ IsFrostman ν α C

section Push

variable {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
include hW hT

/-- The pushforward of a folded circle of positive radius is regular. -/
theorem fc_push_regular (w : ℂ) {r : ℝ} (hr : 0 < r) :
    PushRegular ((foldedCircle w r).map (revMap W T)) := by
  have hm := TwoPoint.measurable_revMap hW hT
  set ν := (foldedCircle w r).map (revMap W T) with hν
  obtain ⟨C, hC⟩ := UnzipFull.norm_revMap_le hW hT (‖w‖ + r)
  have hνH : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ C := by
    rw [hν]
    refine (ae_map_iff hm.aemeasurable (isOpen_H.measurableSet.inter
      (measurableSet_le continuous_norm.measurable measurable_const))).2 ?_
    filter_upwards [UnzipFull.inputs_holds.aeH w hr, UnzipFull.fc_ae_norm_le w hr.le]
      with u hu hR
    exact ⟨Semigroup.mem_H_revMap hW hT hu, hC u hu hR⟩
  have hνK : ∀ᵐ z ∂ν, z ∈ Metric.closedBall (0 : ℂ) C ∩ Hbar :=
    hνH.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, H_subset_Hbar hz.1⟩
  obtain ⟨α, C', hα, hF⟩ := UnzipFull.inputs_holds.frost W hW hT w hr
  exact ⟨C, α, C', hα, ae_iff.1 hνK, fun p s hs => hF p s hs⟩

/-- The pushforward of a bounded density with compact support in `ℍ` is regular. -/
theorem tdens_push_regular {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ} (hd : Dens a K M δ) :
    PushRegular ((tdens a).map (revMap W T)) := by
  have : IsFiniteMeasure (tdens a) := hd.admissible.1
  have hF := TRegE4.isFrostman_of_le_smul_volume ENNReal.coe_ne_top hd.tdens_le
  obtain ⟨C₁, hF1⟩ := B2.isFrostman_map_revMap_of_compact hW hT hd.compact hd.subH
    hd.tdens_compl (by norm_num : (0 : ℝ) ≤ 2) (fun p r hr => hF p r hr)
  obtain ⟨R, hR⟩ := B2.map_revMap_support_of_compact hW hT hd.compact hd.subH hd.tdens_compl
  exact ⟨R, 2, C₁, two_pos, hR, fun p r hr => hF1 p r hr⟩

end Push

/-- RC1 in `evalReg` form: for a regular finite measure, `evalReg (X ω) ν = X ω ν` a.s. -/
theorem ae_evalReg_eq_of_regular {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (h : PushRegular ν) :
    ∀ᵐ ω ∂P, evalReg (X ω) ν = X ω ν := by
  obtain ⟨R, α, C, hα, hs, hF⟩ := h
  filter_upwards [UnzipFull.rc1_holds hX ν hs (fun p r hr => hF p r hr) hα] with ω h
  exact h.limUnder_eq

/-- A regular finite measure is admissible. -/
theorem admissible_of_regular {ν : Measure ℂ} [IsFiniteMeasure ν] (h : PushRegular ν) :
    IsAdmissibleH ν := by
  obtain ⟨R, α, C, hα, hs, hF⟩ := h
  exact FrostmanReg.isAdmissibleH_of_frostman hs hF hα

/-- **Chebyshev for a balanced admissible pair.** -/
theorem prob_ge_le_kernelCov2 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (p : WedgeTK.BPair) {c : ℝ} (hc : 0 < c) :
    P {ω | c ≤ |X ω p.1.1 - X ω p.1.2|} ≤
      ENNReal.ofReal (kernelCov2 neumannH p.1 p.1 / c ^ 2) := by
  set D : Ω → ℝ := WedgeTK.gaussFam X (fun _ : Unit => p) () with hD
  have hmem := WedgeTK.memLp_gaussFam hX (fun _ : Unit => p) ()
  have hmean : ∫ ω, D ω ∂P = 0 := WedgeTK.integral_gaussFam hX (fun _ : Unit => p) ()
  have hvar : variance D P = kernelCov2 neumannH p.1 p.1 := by
    rw [← covariance_self hmem.aemeasurable, WedgeTK.cov_gaussFam hX]
  have hcheb := meas_ge_le_variance_div_sq hmem hc
  rw [hmean, hvar] at hcheb
  refine le_trans (measure_mono fun ω hω => ?_) hcheb
  simp only [mem_ofPred_eq, sub_zero] at hω ⊢
  exact hω

end Thm14WDG
end QuantumZipper
