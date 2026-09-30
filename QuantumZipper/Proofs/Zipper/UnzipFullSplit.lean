import QuantumZipper.Proofs.Zipper.CouplingMarkov
import QuantumZipper.Proofs.Zipper.WeldingUniqueness
import QuantumZipper.Field.CoordsFull
import QuantumZipper.Proofs.Loewner.TwoPoint
import QuantumZipper.Proofs.GFF.FrostmanReg

/-!
# B1-FULL, part 1: REG-SPLIT and the circle coordinates of the unzipped field

`audits/2026-09-27-regcoord/AUDIT3.md` §4.1 (REG-SPLIT) and `blueprint/E_BRANCH_BLUEPRINT.md` §3.

* `ae_split_fc_fixed`, `ae_split_fc_random`: for a folded circle `σ = fc(w, r)`, `r > 0`, and the
  reverse map `ψ = revMap W T` (deterministic, resp. random and independent of `X`), almost surely
  `evalReg (𝔥₀ + X) (σ.map ψ) = ∫ 𝔥₀ d(σ.map ψ) + evalReg X (σ.map ψ)`. The circle may pass
  through `0`: the `𝔥₀`-part is handled by the exact folded-circle average
  `ofFun 𝔥₀ (fc c ρ) = (2/√κ) log (max ρ ‖c‖)` and dominated convergence, using
  `‖ψ u‖ ≥ Im u` (no two-point bound needed for this part).
* `ae_coordsFull_unzip`: the unzipped field `x_U = coordChange (𝔥₀ + X) (fwdMapInv W t) Q` has a.s.
  the same full circle coordinates as the Theorem 1.3 field `couplingFieldRev κ V t X` built from a
  Brownian motion `B'` independent of `X` (`V = √κ B'`, the time-reversed driver). Hence a.s.
  `RegEq` (`regEq_of_coordsFull`) and equal boundary measures
  (`qBoundaryMeasure_congr_of_coordsFull`).

## Interfaces

The inputs RC1 (`Proofs/GFF/FrostmanReg.lean`) and L2PT (F), (L) (`Proofs/Loewner/TwoPoint.lean`)
are being built by other agents. They enter here only through the structure `Inputs`, whose fields
are the exact statements of those files (in a slightly weakened form); `Inputs` is to be
discharged by those theorems once built.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace UnzipFull

open CharFun UnzipInvariance

/-! ## 0. Interfaces (to be discharged by `FrostmanReg` and `TwoPoint`) -/

/-- Frostman bound (same body as `QuantumZipper.IsFrostman` and `TwoPoint.IsFrostman`). -/
def IsFrostmanI (ν : Measure ℂ) (α C : ℝ) : Prop :=
  ∀ w : ℂ, ∀ r : ℝ, 0 < r → (ν (Metric.closedBall w r)).toReal ≤ C * r ^ α

/-- **Interface.** The statements used from RC1 and L2PT. -/
structure Inputs : Prop where
  /-- RC1 (`FrostmanReg.ae_tendsto_integral_avgReg_frostman`). -/
  rc1 : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample}, IsFreeGFFModConstH X P → ∀ (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R α C : ℝ}, ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0 → IsFrostmanI ν α C → 0 < α →
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν) atTop (𝓝 (X ω ν))
  /-- (F) (`TwoPoint.isFrostman_revMap_foldedCircle`). -/
  frost : ∀ (W : ℝ → ℝ), Continuous W → ∀ {T : ℝ}, 0 ≤ T → ∀ (w : ℂ) {r : ℝ}, 0 < r →
    ∃ α C : ℝ, 0 < α ∧ IsFrostmanI ((foldedCircle w r).map (revMap W T)) α C
  /-- (L) (`TwoPoint.integrable_log_norm_deriv_revMap_foldedCircle`). -/
  logDeriv : ∀ (W : ℝ → ℝ), Continuous W → ∀ {T : ℝ}, 0 ≤ T → ∀ (w : ℂ) {r : ℝ}, 0 < r →
    Integrable (fun u => Real.log ‖deriv (revMap W T) u‖) (foldedCircle w r)
  /-- `TwoPoint.integrable_log_im_foldedCircle`. -/
  logIm : ∀ (w : ℂ) {r : ℝ}, 0 < r → Integrable (fun x : ℂ => Real.log x.im) (foldedCircle w r)
  /-- `TwoPoint.foldedCircle_ae_mem_H`. -/
  aeH : ∀ (w : ℂ) {r : ℝ}, 0 < r → ∀ᵐ x ∂(foldedCircle w r), x ∈ H

/-- **Interface RC1** (`FrostmanReg.ae_tendsto_integral_avgReg_frostman`, not yet built). -/
def RC1 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample}, IsFreeGFFModConstH X P → ∀ (ν : Measure ℂ) [IsFiniteMeasure ν]
    {R α C : ℝ}, ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0 → IsFrostmanI ν α C → 0 < α →
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ z, avgReg (X ω) k z ∂ν) atTop (𝓝 (X ω ν))

/-- The L2PT fields of `Inputs` are discharged by `TwoPoint` (built); only RC1 remains. -/
theorem inputs_of_rc1 (h : RC1) : Inputs where
  rc1 := fun hX ν _ _ _ _ hs hF hα => h hX ν hs hF hα
  frost := fun W hW _ hT w _ hr => ⟨1 / 3, _, by norm_num,
    TwoPoint.isFrostman_revMap_foldedCircle hW hT (w := w) hr le_rfl le_rfl⟩
  logDeriv := fun W hW _ hT w _ hr => TwoPoint.integrable_log_norm_deriv_revMap_foldedCircle hW hT w hr
  logIm := fun w _ hr => TwoPoint.integrable_log_im_foldedCircle w hr
  aeH := fun w _ hr => TwoPoint.foldedCircle_ae_mem_H w hr

theorem rc1_holds : RC1 := fun hX ν _ _ _ _ hs hF hα =>
  FrostmanReg.ae_tendsto_integral_avgReg_frostman hX hs hF hα

/-- All inputs hold (RC1 from `FrostmanReg`, L2PT from `TwoPoint`). -/
theorem inputs_holds : Inputs := inputs_of_rc1 rc1_holds

/-! ## 1. Deterministic facts -/

theorem norm_foldH' (x : ℂ) : ‖foldH x‖ = ‖x‖ := by
  unfold foldH; split_ifs <;> simp

theorem ne_zero_of_mem_H {z : ℂ} (hz : z ∈ H) : z ≠ 0 := fun h => by
  simp [H, h] at hz

/-- Exact folded-circle average of `𝔥₀`. -/
theorem ofFun_h0rev_fc (κ : ℝ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ofFun (h0rev κ) (foldedCircle c r) = 2 / Real.sqrt κ * Real.log (max r ‖c‖) := by
  unfold ofFun foldedCircle
  rw [integral_map measurable_foldH.aemeasurable (measurable_h0rev κ).aestronglyMeasurable]
  simp only [h0rev, norm_foldH']
  rw [integral_const_mul]
  have := integral_log_norm_sub_circleUnif c 0 hr
  simp only [sub_zero] at this
  rw [this]

theorem tendsto_ofFun_h0rev_fc (κ : ℝ) (k : ℕ) (z : ℂ) :
    Tendsto (fun n => ofFun (h0rev κ) (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (2 / Real.sqrt κ * Real.log (max (radius k) ‖z‖))) := by
  simp_rw [ofFun_h0rev_fc κ _ (radius_pos k)]
  have hc : Continuous fun x : ℂ => 2 / Real.sqrt κ * Real.log (max (radius k) ‖x‖) :=
    continuous_const.mul ((continuous_const.max continuous_norm).log fun x =>
      (lt_max_of_lt_left (radius_pos k)).ne')
  exact (hc.tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)

theorem fc_ae_norm_le (w : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ x ∂(foldedCircle w r), ‖x‖ ≤ ‖w‖ + r := by
  unfold foldedCircle
  rw [ae_map_iff measurable_foldH.aemeasurable
    (measurableSet_le continuous_norm.measurable measurable_const)]
  filter_upwards [CircleMV.ae_circleUnif w r] with x hx
  rw [norm_foldH']
  calc ‖x‖ = ‖w + (x - w)‖ := by ring_nf
    _ ≤ ‖w‖ + ‖x - w‖ := norm_add_le _ _
    _ = ‖w‖ + r := by rw [hx, abs_of_nonneg hr]

/-- `revMap W T` is bounded on bounded subsets of `ℍ`. -/
theorem norm_revMap_le {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (R₀ : ℝ) :
    ∃ C : ℝ, ∀ z ∈ H, ‖z‖ ≤ R₀ → ‖revMap W T z‖ ≤ C := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hW.continuousOn (s := Icc 0 T))
  have hM' : ∀ s ∈ Icc (0 : ℝ) T, |W s| ≤ M := fun s hs => by
    simpa [Real.norm_eq_abs] using hM s hs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0 ⟨le_rfl, hT⟩)
  set K := 4 * (2 * M + T + 1) + |R₀| with hK
  have hK4 : 4 ≤ K := by nlinarith [abs_nonneg R₀]
  refine ⟨K + 2 * M + T, fun z hz hzR => ?_⟩
  by_cases hle : ‖revMap W T z‖ ≤ K
  · linarith
  push_neg at hle
  have hcont : ContinuousOn (fun s => ‖revMap W s z‖) (Icc 0 T) :=
    (ReverseFlow.continuousOn_revMap_time W hW z hz).norm.mono Icc_subset_Ici_self
  have h0 : ‖revMap W 0 z‖ ≤ K := by
    obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz 0 le_rfl
    rw [revMap_eq W hW z le_rfl le_rfl hu, (hu.2 0 ⟨le_rfl, le_rfl⟩).2,
      intervalIntegral.integral_same, sub_zero]
    calc ‖z - (W 0 : ℂ)‖ ≤ ‖z‖ + ‖(W 0 : ℂ)‖ := norm_sub_le _ _
      _ ≤ |R₀| + M := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (hzR.trans (le_abs_self _)) (hM' 0 ⟨le_rfl, hT⟩)
      _ ≤ K := by linarith
  obtain ⟨s₀, hs₀, hs₀eq'⟩ := intermediate_value_Icc hT hcont ⟨h0, hle.le⟩
  have hs₀eq : ‖revMap W s₀ z‖ = K := hs₀eq'
  have hsplit : revMap W T z =
      revMap (fun r => W (s₀ + r) - W s₀) (T - s₀) (revMap W s₀ z) := by
    have := ReverseFlow.revMap_add W hW z hz hs₀.1 (sub_nonneg.2 hs₀.2)
    rwa [add_sub_cancel] at this
  have hW' : Continuous fun r => W (s₀ + r) - W s₀ :=
    (hW.comp (continuous_const.add continuous_id)).sub continuous_const
  have hM'' : ∀ r ∈ Icc (0 : ℝ) (T - s₀), |W (s₀ + r) - W s₀| ≤ 2 * M := fun r hr => by
    have h1 := hM' (s₀ + r) ⟨by linarith [hs₀.1, hr.1], by linarith [hr.2]⟩
    have h2 := hM' s₀ hs₀
    calc |W (s₀ + r) - W s₀| ≤ |W (s₀ + r)| + |W s₀| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hzH : revMap W s₀ z ∈ H := Semigroup.mem_H_revMap hW hs₀.1 hz
  have hfar := WeldingUniqueness.norm_revMap_sub_far hW' (sub_nonneg.2 hs₀.2) hM'' hzH
    (by rw [hs₀eq]; nlinarith [abs_nonneg R₀, hs₀.1])
  rw [hs₀eq] at hfar
  rw [hsplit]
  set u₀ := revMap W s₀ z
  set a := revMap (fun r => W (s₀ + r) - W s₀) (T - s₀) u₀
  set c : ℂ := ((W (s₀ + (T - s₀)) - W s₀ : ℝ) : ℂ)
  have e : a = (a - (u₀ - c)) + u₀ - c := by ring
  have hc : ‖c‖ ≤ 2 * M := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hM'' (T - s₀) ⟨sub_nonneg.2 hs₀.2, le_rfl⟩
  have hdiv : 4 * (T - s₀) / K ≤ T := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hs₀.1]
  calc ‖a‖ = ‖(a - (u₀ - c)) + u₀ - c‖ := by rw [← e]
    _ ≤ ‖a - (u₀ - c)‖ + ‖u₀‖ + ‖c‖ := by
        have := norm_add_le (a - (u₀ - c)) u₀
        have := norm_sub_le (a - (u₀ - c) + u₀) c
        linarith
    _ ≤ T + K + 2 * M := by
        rw [show ‖u₀‖ = K from hs₀eq]
        exact add_le_add (add_le_add (hfar.trans hdiv) le_rfl) hc
    _ = K + 2 * M + T := by ring

theorem abs_log_norm_revMap_le {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {R C : ℝ} (hC : ∀ z ∈ H, ‖z‖ ≤ R → ‖revMap W T z‖ ≤ C) {u : ℂ} (hu : u ∈ H)
    (huR : ‖u‖ ≤ R) :
    |Real.log ‖revMap W T u‖| ≤ |Real.log u.im| + |Real.log C| := by
  have hu' : 0 < u.im := hu
  have h1 : u.im ≤ ‖revMap W T u‖ :=
    (im_le_im_revMap W hW u hu hT).trans ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have hpos : 0 < ‖revMap W T u‖ := lt_of_lt_of_le hu' h1
  have h2 : ‖revMap W T u‖ ≤ C := hC u hu huR
  rcases le_total 0 (Real.log ‖revMap W T u‖) with h | h
  · rw [abs_of_nonneg h]
    have := Real.log_le_log hpos h2
    linarith [le_abs_self (Real.log C), abs_nonneg (Real.log u.im)]
  · rw [abs_of_nonpos h]
    have := Real.log_le_log hu' h1
    linarith [neg_abs_le (Real.log u.im), abs_nonneg (Real.log C)]

theorem integrable_log_norm_revMap_fc (hI : Inputs) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ}
    (hT : 0 ≤ T) (hm : Measurable (revMap W T)) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun u => Real.log ‖revMap W T u‖) (foldedCircle w r) := by
  obtain ⟨C, hC⟩ := norm_revMap_le hW hT (‖w‖ + r)
  refine ((hI.logIm w hr).abs.add (integrable_const |Real.log C|)).mono'
    (Real.measurable_log.comp hm.norm).aestronglyMeasurable ?_
  filter_upwards [hI.aeH w hr, fc_ae_norm_le w hr.le] with u hu hR
  rw [Real.norm_eq_abs]
  exact abs_log_norm_revMap_le hW hT hC hu hR

/-- `∫ 𝔥_T dσ = ∫ 𝔥₀ d(σ.map f_T) + Q ∫ log|f_T'| dσ` on folded circles. -/
theorem integral_hTrev_fc (hI : Inputs) (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ}
    (hT : 0 ≤ T) (hm : Measurable (revMap W T)) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ z, hTrev κ W T z ∂(foldedCircle w r) =
      (∫ z, h0rev κ z ∂((foldedCircle w r).map (revMap W T))) +
        Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (revMap W T) z‖ ∂(foldedCircle w r) := by
  have hf : Integrable (fun u => h0rev κ (revMap W T u)) (foldedCircle w r) :=
    (integrable_log_norm_revMap_fc hI hW hT hm w hr).const_mul (2 / Real.sqrt κ)
  have hg : Integrable (fun u => Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W T) u‖)
      (foldedCircle w r) := (hI.logDeriv W hW hT w hr).const_mul _
  rw [integral_map hm.aemeasurable (measurable_h0rev κ).aestronglyMeasurable,
    ← integral_const_mul, ← integral_add hf hg]
  rfl

/-! ## 2. REG-SPLIT for a fixed driver -/

/-- **REG-SPLIT, deterministic driver.** -/
theorem ae_split_fc_fixed (hI : Inputs) (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) (hm : Measurable (revMap W T))
    (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω) ((foldedCircle w r).map (revMap W T)) =
      (∫ z, h0rev κ z ∂((foldedCircle w r).map (revMap W T))) +
        evalReg (X ω) ((foldedCircle w r).map (revMap W T)) := by
  set ν := (foldedCircle w r).map (revMap W T) with hν
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  obtain ⟨C, hC⟩ := norm_revMap_le hW hT (‖w‖ + r)
  have hνH : ∀ᵐ z ∂ν, z ∈ H ∧ ‖z‖ ≤ C := by
    rw [hν]
    refine (ae_map_iff hm.aemeasurable (isOpen_H.measurableSet.inter
      (measurableSet_le continuous_norm.measurable measurable_const))).2 ?_
    filter_upwards [hI.aeH w hr, fc_ae_norm_le w hr.le] with u hu hR
    exact ⟨Semigroup.mem_H_revMap hW hT hu, hC u hu hR⟩
  have hνK : ∀ᵐ z ∂ν, z ∈ Metric.closedBall (0 : ℂ) C ∩ Hbar :=
    hνH.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, H_subset_Hbar hz.1⟩
  have hsupp : ν (Metric.closedBall 0 C ∩ Hbar)ᶜ = 0 := ae_iff.1 hνK
  obtain ⟨α, C', hα, hF⟩ := hI.frost W hW hT w hr
  have hconv := hI.rc1 hX ν hsupp hF hα
  have h3 : ∀ᵐ ω ∂P, ∀ k, ∀ z ∈ Hbar,
      Tendsto (fun n => X ω (foldedCircle (dyadicRoundC n z) (radius k))) atTop
        (𝓝 (avgReg (X ω) k z)) :=
    ae_all_iff.2 fun k => (BdryExist.ae_avgReg_spec hX k).1
  have hcont : ∀ k : ℕ, ∃ Y : ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun z => Y z ω) Hbar) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ Hbar, avgReg (X ω) k z = Y z ω + X ω (foldedCircle 0 (radius k)) := by
    intro k
    obtain ⟨Y, hY, -, hl⟩ := exists_continuous_circleAvg hX k 0 (by simp [Hbar])
    exact ⟨Y, hY, hl⟩
  choose Y hYc hYl using hcont
  have h4 : ∀ᵐ ω ∂P, ∀ k, ContinuousOn (avgReg (X ω) k) Hbar := by
    filter_upwards [ae_all_iff.2 hYl] with ω hω k
    exact ((hYc k ω).add continuousOn_const).congr fun z hz => hω k z hz
  -- the deterministic part
  have hlogint : Integrable (fun z => Real.log ‖z‖) ν := by
    rw [hν]
    exact (integrable_map_measure (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
      hm.aemeasurable).2 (integrable_log_norm_revMap_fc hI hW hT hm w hr)
  set F : ℕ → ℂ → ℝ := fun k z => 2 / Real.sqrt κ * Real.log (max (radius k) ‖z‖) with hFdef
  have hFm : ∀ k, Measurable (F k) := fun k =>
    measurable_const.mul (Real.measurable_log.comp (measurable_const.max measurable_norm))
  have hFb : ∀ k, ∀ z : ℂ, z ≠ 0 → |F k z| ≤ |2 / Real.sqrt κ| * |Real.log ‖z‖| := by
    intro k z hz
    have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hr1 : radius k ≤ 1 := by unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)
    simp only [hFdef, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases le_total 1 ‖z‖ with h1 | h1
    · rw [max_eq_right (hr1.trans h1)]
    · have hmpos : 0 < max (radius k) ‖z‖ := lt_max_of_lt_right hz'
      have hlo : Real.log ‖z‖ ≤ Real.log (max (radius k) ‖z‖) :=
        Real.log_le_log hz' (le_max_right _ _)
      have hhi : Real.log (max (radius k) ‖z‖) ≤ 0 := Real.log_nonpos hmpos.le (max_le hr1 h1)
      rw [abs_of_nonpos hhi, abs_of_nonpos (hlo.trans hhi)]
      linarith
  have hbound : Integrable (fun z => |2 / Real.sqrt κ| * |Real.log ‖z‖|) ν :=
    hlogint.abs.const_mul _
  have hFint : ∀ k, Integrable (F k) ν := fun k =>
    hbound.mono' (hFm k).aestronglyMeasurable
      (hνH.mono fun z hz => by rw [Real.norm_eq_abs]; exact hFb k z (ne_zero_of_mem_H hz.1))
  have hFlim : Tendsto (fun k => ∫ z, F k z ∂ν) atTop (𝓝 (∫ z, h0rev κ z ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence _ (fun k => (hFm k).aestronglyMeasurable)
      hbound (fun k => hνH.mono fun z hz => by
        rw [Real.norm_eq_abs]; exact hFb k z (ne_zero_of_mem_H hz.1)) ?_
    filter_upwards [hνH] with z hz
    have hz0 : 0 < ‖z‖ := norm_pos_iff.2 (ne_zero_of_mem_H hz.1)
    have hev : ∀ᶠ k in atTop, radius k ≤ ‖z‖ :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num)).eventually (ge_mem_nhds hz0)
    refine tendsto_const_nhds.congr' (hev.mono fun k hk => ?_)
    show h0rev κ z = 2 / Real.sqrt κ * Real.log (max (radius k) ‖z‖)
    rw [max_eq_right hk]
    rfl
  filter_upwards [hconv, h3, h4] with ω hc h3 h4
  have hK : IsCompact (Metric.closedBall (0 : ℂ) C ∩ Hbar) :=
    (isCompact_closedBall 0 C).inter_right isClosed_Hbar
  have hXint : ∀ k, Integrable (avgReg (X ω) k) ν := fun k => by
    have : IntegrableOn (avgReg (X ω) k) (Metric.closedBall 0 C ∩ Hbar) ν :=
      ((h4 k).mono Set.inter_subset_right).integrableOn_compact hK
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hνK] at this
  have hsplit : ∀ k, ∫ z, avgReg (ofFun (h0rev κ) + X ω) k z ∂ν =
      ∫ z, F k z ∂ν + ∫ z, avgReg (X ω) k z ∂ν := by
    intro k
    rw [← integral_add (hFint k) (hXint k)]
    refine integral_congr_ae (hνH.mono fun z hz => ?_)
    exact ((tendsto_ofFun_h0rev_fc κ k z).add (h3 k z (H_subset_Hbar hz.1))).limUnder_eq
  have hXe : evalReg (X ω) ν = X ω ν := hc.limUnder_eq
  rw [hXe]
  exact ((hFlim.add hc).congr fun k => (hsplit k).symm).limUnder_eq

/-! ## 3. Random drivers -/

theorem measurable_evalReg_push_gen (κ T : ℝ) (hT : 0 ≤ T) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg p.2 (μ.map (revMap (Wof κ T hT p.1) T)) := by
  have heq : ∀ p : C(Icc (0 : ℝ) T, ℝ) × FieldSample,
      evalReg p.2 (μ.map (revMap (Wof κ T hT p.1) T)) =
        limUnder atTop fun k => ∫ z, avgReg p.2 k (Fm κ T hT (p.1, z)) ∂μ := by
    intro p
    unfold evalReg
    congr 1
    funext k
    rw [integral_map (measurable_revMap_Wof κ T hT p.1).aemeasurable
      (show Measurable fun w => avgReg p.2 k w from
        (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
    rfl
  rw [show (fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg p.2 (μ.map (revMap (Wof κ T hT p.1) T))) = _ from funext heq]
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have hm : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      avgReg q.1.2 k (Fm κ T hT (q.1.1, q.2)) :=
    (measurable_avgReg k).comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_Fm κ T hT).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'

theorem measurable_evalReg_h0rev_push_gen (κ T : ℝ) (hT : 0 ≤ T) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg (ofFun (h0rev κ) + p.2) (μ.map (revMap (Wof κ T hT p.1) T)) := by
  have hpair : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      ((p.1, ofFun (h0rev κ) + p.2) : C(Icc (0 : ℝ) T, ℝ) × FieldSample) :=
    measurable_fst.prodMk ((measurable_add_left _).comp measurable_snd)
  have key := (measurable_evalReg_push_gen κ T hT μ).comp hpair
  simp only [Function.comp_def] at key
  exact key

theorem measurable_integral_h0rev_push_gen (κ T : ℝ) (hT : 0 ≤ T) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ w, h0rev κ w ∂(μ.map (revMap (Wof κ T hT f) T)) := by
  have heq : ∀ f : C(Icc (0 : ℝ) T, ℝ),
      ∫ w, h0rev κ w ∂(μ.map (revMap (Wof κ T hT f) T)) =
        ∫ z, h0rev κ (Fm κ T hT (f, z)) ∂μ := fun f =>
    integral_map (measurable_revMap_Wof κ T hT f).aemeasurable
      (measurable_h0rev κ).aestronglyMeasurable
  rw [show (fun f : C(Icc (0 : ℝ) T, ℝ) =>
      ∫ w, h0rev κ w ∂(μ.map (revMap (Wof κ T hT f) T))) = _ from funext heq]
  exact (((measurable_h0rev κ).comp (measurable_Fm κ T hT)).stronglyMeasurable.integral_prod_right').measurable

/-- **REG-SPLIT, random driver independent of the field.** -/
theorem ae_split_fc_random (hI : Inputs) (κ : ℝ) {T : ℝ} (hT : 0 ≤ T) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g)
    (hind : IndepFun g X P) (w : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, evalReg (ofFun (h0rev κ) + X ω)
        ((foldedCircle w r).map (revMap (Wof κ T hT (g ω)) T)) =
      (∫ z, h0rev κ z ∂((foldedCircle w r).map (revMap (Wof κ T hT (g ω)) T))) +
        evalReg (X ω) ((foldedCircle w r).map (revMap (Wof κ T hT (g ω)) T)) := by
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hE : MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      evalReg (ofFun (h0rev κ) + p.2) ((foldedCircle w r).map (revMap (Wof κ T hT p.1) T)) =
        (∫ z, h0rev κ z ∂((foldedCircle w r).map (revMap (Wof κ T hT p.1) T))) +
          evalReg p.2 ((foldedCircle w r).map (revMap (Wof κ T hT p.1) T))} :=
    measurableSet_eq_fun (measurable_evalReg_h0rev_push_gen κ T hT _)
      (((measurable_integral_h0rev_push_gen κ T hT _).comp measurable_fst).add
        (measurable_evalReg_push_gen κ T hT _))
  exact ae_indep hg hXm hind hE fun f => ae_split_fc_fixed hI κ hX (continuous_Wof κ T hT f) hT
    (measurable_revMap_Wof κ T hT f) w hr

/-! ## 4. Circle coordinates of the unzipped field -/

/-- The unzipping map at time `t` is the reverse map of the driver `√κ B'` with `B' = revBM` an
independent Brownian motion. -/
theorem exists_unzip_driver (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 ≤ t) :
    ∃ B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B' P ∧ (∀ s, Measurable (B' s)) ∧
      (∀ ω, Continuous fun s => B' s ω) ∧ IndepFun (pathOf B') X P ∧
      ∀ᵐ ω ∂P, EqOn (fwdMapInv (drive κ B ω) t) (revMap (drive κ B' ω) t) H := by
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hB₁ : IsPreBrownianReal B₁ P := hB.toIsPreBrownianReal.congr fun s => by
    filter_upwards [hB₁eq] with ω h using (h s).symm
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  refine ⟨revBM B₁ t.toNNReal, isBrownianReal_revBM hB₁ hB₁c _, fun s =>
    ((hB₁m _).add (hB₁m _)).sub ((hB₁m _).const_smul _), fun ω => ?_, ?_, ?_⟩
  · simp only [revBM_apply]
    exact (((hB₁c ω).comp (continuous_const.sub continuous_id)).add
      ((hB₁c ω).comp (continuous_id.max continuous_const))).sub continuous_const
  · have hΦ : Measurable fun p : ℝ≥0 → ℝ =>
        fun s => p (t.toNNReal - s) + p (max s t.toNNReal) - 2 * p t.toNNReal := by
      fun_prop
    have := hind₁.comp hΦ measurable_id
    convert this using 1
    all_goals first
      | rfl
      | (funext ω s; simp [pathOf])
  · filter_upwards [hB₁eq, hB₁.eval_zero_ae_eq_zero] with ω h1 h0 w hw
    have hdr : drive κ B ω = drive κ B₁ ω := funext fun x => by simp [drive, h1]
    rw [hdr, fwdMapInv_eq_revMap_timeRev _ (drive_continuous (hB₁c ω)) (drive_zero h0) ht hw,
      revMap_timeRev_eq_drive_revBM κ B₁ ht ω w]

theorem fullIndex_radius_pos (i : ℕ) : 0 < (CoordsFull.fullIndex i).2 := by
  unfold CoordsFull.fullIndex; positivity

/-- Equal circle coordinates give equal regularized fields. -/
theorem regEq_of_coordsFull {x x' : FieldSample}
    (h : CoordsFull.coordsFull x = CoordsFull.coordsFull x') : RegEq x x' := fun k z => by
  rw [CoordsFull.avgReg_congr_full h]

/-- Equal circle coordinates give equal boundary measures. -/
theorem qBoundaryMeasure_congr_of_coordsFull (γ : ℝ) {x x' : FieldSample}
    (h : CoordsFull.coordsFull x = CoordsFull.coordsFull x') :
    qBoundaryMeasure γ x = qBoundaryMeasure γ x' := by
  have hb : bdryApprox γ x = bdryApprox γ x' := by
    funext k
    unfold bdryApprox
    rw [CoordsFull.avgReg_congr_full h]
  unfold qBoundaryMeasure
  rw [hb]

end UnzipFull
end QuantumZipper
