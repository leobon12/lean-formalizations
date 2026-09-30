import QuantumZipper.Proofs.Thm18.G2AgreeCond
import QuantumZipper.Proofs.Section5.Prop17PalmCReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 identification nodes: regularity of the Palm field at translated circles

`g2PalmReg_holds`: for every real `x`, a.s. the Palm field `h_x = normField γ (X₀ + ψ_x)` is
regular (`evalReg = raw value`) at every translated dyadic folded circle
`fc(dyadicRoundC n z, radius k) + x`. Hence `G2PalmRegGoodStmt γ` reduces to the goodness node
`G2PalmGoodStmt γ` (`g2PalmRegGoodStmt_of_good`).

Route (own adaptation of `Prop17PalmCReg`/`Prop17PalmCLog`, AGENT_GUIDE cost rule): on folded
circles `h_x` equals `ofFun G + addConst X₀ c` with
`G v = −γ log‖v − x‖ + (2/γ) log‖v‖ + γ log⁺‖v‖` (the two logarithmic poles `x` and `0` are
real; `kPot refS = −2 log⁺‖·‖`), so it has the same regularizations as that field; RC1 with two
real logarithmic poles (`g2_ae_evalReg_logAdd2`, the proof of
`S5.FieldLaw.Raw.palmC_ae_evalReg_logAdd` with one more pole) gives regularity at each Frostman
folded circle, and there are countably many.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm

open S5.FieldLaw.Raw FrostmanReg SmoothConv CoordReg

local notation "Ω₀" => gffBase.Ω

/-! ## RC1 with two real logarithmic poles -/

theorem g2_avgReg_logAdd2 (a t b t' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar)
    {x : FieldSample} {k : ℕ} {z : ℂ}
    (hx : Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (avgReg x k z))) :
    avgReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ +
        (b * Real.log ‖v - (t' : ℂ)‖ + g₁ v)) + x) k z =
      a * Real.log (max (radius k) ‖z - (t : ℂ)‖) +
        (b * Real.log (max (radius k) ‖z - (t' : ℂ)‖) + GoodSample.smoothFun g₁ z (radius k)) +
        avgReg x k z := by
  have hr := radius_pos k
  have ha : Tendsto (fun n => a * Real.log (max (radius k) ‖dyadicRoundC n z - (t : ℂ)‖) +
      (b * Real.log (max (radius k) ‖dyadicRoundC n z - (t' : ℂ)‖) +
        GoodSample.smoothFun g₁ (dyadicRoundC n z) (radius k))) atTop
      (𝓝 (a * Real.log (max (radius k) ‖z - (t : ℂ)‖) +
        (b * Real.log (max (radius k) ‖z - (t' : ℂ)‖) + GoodSample.smoothFun g₁ z (radius k)))) :=
    ((((palmC_continuous_log_max_sub hr t).tendsto z).comp
      (RegClosure.tendsto_dyadicRoundC z)).const_mul a).add
      (((((palmC_continuous_log_max_sub hr t').tendsto z).comp
        (RegClosure.tendsto_dyadicRoundC z)).const_mul b).add
        (((GoodSample.continuous_smoothFun hg₁ _).tendsto z).comp
          (RegClosure.tendsto_dyadicRoundC z)))
  have e : (fun n => (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ +
      (b * Real.log ‖v - (t' : ℂ)‖ + g₁ v)) + x) (foldedCircle (dyadicRoundC n z) (radius k))) =
      fun n => (a * Real.log (max (radius k) ‖dyadicRoundC n z - (t : ℂ)‖) +
        (b * Real.log (max (radius k) ‖dyadicRoundC n z - (t' : ℂ)‖) +
          GoodSample.smoothFun g₁ (dyadicRoundC n z) (radius k))) +
          x (foldedCircle (dyadicRoundC n z) (radius k)) := by
    funext n
    show ofFun _ _ + x _ = _
    simp only [ofFun]
    have i1 : Integrable (fun v => a * Real.log ‖v - (t : ℂ)‖)
        (foldedCircle (dyadicRoundC n z) (radius k)) :=
      (palmC_integrable_log_sub_fc _ t _).const_mul a
    have i2 : Integrable (fun v => b * Real.log ‖v - (t' : ℂ)‖)
        (foldedCircle (dyadicRoundC n z) (radius k)) :=
      (palmC_integrable_log_sub_fc _ t' _).const_mul b
    have i3 : Integrable g₁ (foldedCircle (dyadicRoundC n z) (radius k)) :=
      RegClosure.integrable_fc hg₁ _ hr.le
    have i23 : Integrable (fun v => b * Real.log ‖v - (t' : ℂ)‖ + g₁ v)
        (foldedCircle (dyadicRoundC n z) (radius k)) := i2.add i3
    rw [integral_add i1 i23, integral_add i2 i3, integral_const_mul, integral_const_mul,
      palmC_integral_log_sub_fc _ t hr, palmC_integral_log_sub_fc _ t' hr]
    rfl
  unfold avgReg
  rw [e]
  exact (ha.add hx).limUnder_eq

/-- **RC1 with two logarithmic poles at real points.** -/
theorem g2_ae_evalReg_logAdd2 {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {ν : Measure ℂ}
    {α C : ℝ} [IsFiniteMeasure ν] {R : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (a t b t' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar) :
    ∀ᵐ ω ∂P, evalReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ +
        (b * Real.log ‖v - (t' : ℂ)‖ + g₁ v)) + X ω) ν =
      (∫ z, (a * Real.log ‖z - (t : ℂ)‖ + (b * Real.log ‖z - (t' : ℂ)‖ + g₁ z)) ∂ν) + X ω ν := by
  set K := Metric.closedBall (0 : ℂ) R ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hKH : K ⊆ Hbar := Set.inter_subset_right
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_mem_of_compl_null_frostman hsupp
  have hlog := palmC_integrable_log_sub_frostman hsupp h hα t
  have hlog' := palmC_integrable_log_sub_frostman hsupp h hα t'
  have hg₁i : Integrable g₁ ν := integrable_of_continuousOn_frostman hK hKH hsupp hg₁
  filter_upwards [ae_all_iff.2 fun k => ae_circleAvg_tendsto_frostman hX k,
    ae_tendsto_integral_avgReg_frostman hX hsupp h hα] with ω hc ht
  have heq : ∀ k, ∫ z, avgReg (ofFun (fun v => a * Real.log ‖v - (t : ℂ)‖ +
      (b * Real.log ‖v - (t' : ℂ)‖ + g₁ v)) + X ω) k z ∂ν =
      a * ∫ z, Real.log (max (radius k) ‖z - (t : ℂ)‖) ∂ν +
        (b * ∫ z, Real.log (max (radius k) ‖z - (t' : ℂ)‖) ∂ν +
          ∫ z, GoodSample.smoothFun g₁ z (radius k) ∂ν) + ∫ z, avgReg (X ω) k z ∂ν := by
    intro k
    have i1 : Integrable (fun z => Real.log (max (radius k) ‖z - (t : ℂ)‖)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (palmC_continuous_log_max_sub (radius_pos k) t).continuousOn
    have i1' : Integrable (fun z => Real.log (max (radius k) ‖z - (t' : ℂ)‖)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (palmC_continuous_log_max_sub (radius_pos k) t').continuousOn
    have i2 : Integrable (fun z => GoodSample.smoothFun g₁ z (radius k)) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp
        (GoodSample.continuous_smoothFun hg₁ _).continuousOn
    have i3 : Integrable (fun z => avgReg (X ω) k z) ν :=
      integrable_of_continuousOn_frostman hK hKH hsupp (hc k).1
    have i12' : Integrable (fun z => b * Real.log (max (radius k) ‖z - (t' : ℂ)‖) +
        GoodSample.smoothFun g₁ z (radius k)) ν := (i1'.const_mul b).add i2
    have i12 : Integrable (fun z => a * Real.log (max (radius k) ‖z - (t : ℂ)‖) +
        (b * Real.log (max (radius k) ‖z - (t' : ℂ)‖) + GoodSample.smoothFun g₁ z (radius k)))
        ν := (i1.const_mul a).add i12'
    rw [← integral_const_mul a, ← integral_const_mul b, ← integral_add (i1'.const_mul b) i2,
      ← integral_add (i1.const_mul a) i12', ← integral_add i12 i3]
    exact integral_congr_ae (hae.mono fun z hz =>
      g2_avgReg_logAdd2 a t b t' hg₁ ((hc k).2 z (hKH hz)))
  have hbg : Integrable (fun z => b * Real.log ‖z - (t' : ℂ)‖ + g₁ z) ν :=
    (hlog'.const_mul b).add hg₁i
  have hval : (∫ z, (a * Real.log ‖z - (t : ℂ)‖ + (b * Real.log ‖z - (t' : ℂ)‖ + g₁ z)) ∂ν) +
      X ω ν = a * ∫ z, Real.log ‖z - (t : ℂ)‖ ∂ν +
        (b * ∫ z, Real.log ‖z - (t' : ℂ)‖ ∂ν + ∫ z, g₁ z ∂ν) + X ω ν := by
    rw [integral_add (hlog.const_mul a) hbg, integral_add (hlog'.const_mul b) hg₁i,
      integral_const_mul, integral_const_mul]
  rw [hval]
  refine Tendsto.limUnder_eq ?_
  simp only [heq]
  exact (((palmC_tendsto_integral_log_max_sub hsupp h hα t).const_mul a).add
    (((palmC_tendsto_integral_log_max_sub hsupp h hα t').const_mul b).add
      (tendsto_integral_smoothFun_frostman hg₁ hK hKH hsupp))).add ht

/-! ## The Palm field on folded circles -/

/-- The logarithmic mean of the Palm field (poles `x` and `0`). -/
def g2PalmG (γ x : ℝ) (v : ℂ) : ℝ :=
  -γ * Real.log ‖v - (x : ℂ)‖ +
    (2 / Real.sqrt (γ ^ 2) * Real.log ‖v - ((0 : ℝ) : ℂ)‖ + γ * Real.posLog ‖v‖)

/-- The random constant of the Palm field. -/
def g2PalmConst (γ x : ℝ) (ω : Ω₀) : ℝ :=
  -(gffBase.X ω refS + ∫ u, g2PalmPsi γ x u ∂refS)

theorem g2PalmPsi_eq (γ x : ℝ) (v : ℂ) :
    g2PalmPsi γ x v = -γ * Real.log ‖v - (x : ℂ)‖ + γ * Real.posLog ‖v‖ := by
  have h1 : ‖(x : ℂ) - conj v‖ = ‖v - (x : ℂ)‖ := by
    rw [show (x : ℂ) - conj v = conj ((x : ℂ) - v) by rw [map_sub, Complex.conj_ofReal],
      Complex.norm_conj, norm_sub_rev]
  simp only [g2PalmPsi, neumannH, h1, norm_sub_rev (x : ℂ) v]
  rw [show refS = foldedCircle 0 1 from rfl, kPot_refS_eq]
  ring

theorem normField_xPalm_fc (γ x : ℝ) (ω : Ω₀) (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    normField γ (xPalm γ x) ω (foldedCircle c ρ) =
      (ofFun (g2PalmG γ x) + addConst (gffBase.X ω) (g2PalmConst γ x ω)) (foldedCircle c ρ) := by
  have hc : ContinuousOn (fun v : ℂ => γ * Real.posLog ‖v‖) Hbar := by
    have : Continuous fun v : ℂ => γ * Real.posLog ‖v‖ := by fun_prop
    exact this.continuousOn
  have i0 : Integrable (fun v => h0rev (γ ^ 2) v) (foldedCircle c ρ) :=
    (CoordReg.integrable_log_norm_foldedCircle c ρ).const_mul _
  have iψ : Integrable (g2PalmPsi γ x) (foldedCircle c ρ) := by
    refine (((palmC_integrable_log_sub_fc c x ρ).const_mul (-γ)).add
      (RegClosure.integrable_fc hc c hρ.le)).congr (ae_of_all _ fun v => ?_)
    simp only [Pi.add_apply]
    rw [g2PalmPsi_eq]
  have e : g2PalmG γ x = fun v => h0rev (γ ^ 2) v + g2PalmPsi γ x v := by
    funext v
    rw [g2PalmPsi_eq, g2PalmG, h0rev, Complex.ofReal_zero, sub_zero]
    ring
  simp only [normField, xPalm, addConst, Pi.add_apply, ofFun, g2PalmConst]
  rw [e, integral_add i0 iψ, measure_univ, ENNReal.toReal_one]
  ring

/-- **Regularity of the Palm field at translated dyadic folded circles.** -/
theorem g2PalmReg_holds (γ x : ℝ) :
    ∀ᵐ ω ∂gffBase.P, ∀ (n k : ℕ) (z : ℂ),
      evalReg (normField γ (xPalm γ x) ω)
          ((foldedCircle (dyadicRoundC n z) (radius k)).map (· + (x : ℂ))) =
        normField γ (xPalm γ x) ω ((foldedCircle (dyadicRoundC n z) (radius k)).map (· + (x : ℂ))) := by
  have hc : Measurable (g2PalmConst γ x) :=
    ((gffBase.gff.measurable_coord _).add_const _).neg
  have hX' := isFreeGFFModConstH_addConst gffBase.gff hc
  have hgc : ContinuousOn (fun v : ℂ => γ * Real.posLog ‖v‖) Hbar := by
    have : Continuous fun v : ℂ => γ * Real.posLog ‖v‖ := by fun_prop
    exact this.continuousOn
  set F : Ω₀ → FieldSample := fun ω =>
    ofFun (g2PalmG γ x) + addConst (gffBase.X ω) (g2PalmConst γ x ω) with hF
  have hfc : ∀ ω (n k : ℕ) (z : ℂ), normField γ (xPalm γ x) ω
      (foldedCircle (dyadicRoundC n z) (radius k)) =
      F ω (foldedCircle (dyadicRoundC n z) (radius k)) := fun ω n k z =>
    normField_xPalm_fc γ x ω _ (radius_pos k)
  have hev : ∀ ω ν, evalReg (normField γ (xPalm γ x) ω) ν = evalReg (F ω) ν := by
    intro ω ν
    have hav : ∀ k w, avgReg (normField γ (xPalm γ x) ω) k w = avgReg (F ω) k w := fun k w =>
      D3Plus.avgReg_congr (r := ‖w‖ + radius k + 1) (fun n k' z _ => hfc ω n k' z)
        (lt_add_one _)
    simp only [evalReg, hav]
  set S : Set ℂ := ⋃ n : ℕ, Set.range (dyadicRoundC n) with hS
  have hSc : S.Countable := by
    refine Set.countable_iUnion fun n => ?_
    refine (Set.countable_range
      (fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ))).mono ?_
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
  have key : ∀ d : ℂ, ∀ k : ℕ, ∀ᵐ ω ∂gffBase.P,
      evalReg (normField γ (xPalm γ x) ω) ((foldedCircle d (radius k)).map (· + (x : ℂ))) =
        normField γ (xPalm γ x) ω ((foldedCircle d (radius k)).map (· + (x : ℂ))) := by
    intro d k
    have hr := radius_pos k
    rw [palmC_fc_map_add_real]
    have hsupp : foldedCircle (d + x) (radius k)
        (Metric.closedBall 0 (‖d + (x : ℂ)‖ + radius k) ∩ Hbar)ᶜ = 0 :=
      CircleFubini.foldedCircle_support hr.le le_rfl
    filter_upwards [g2_ae_evalReg_logAdd2 hX' hsupp (Cor15Group.isFrostman_fc _ hr) one_pos
      (-γ) x (2 / Real.sqrt (γ ^ 2)) 0 hgc] with ω hω
    rw [hev, normField_xPalm_fc γ x ω _ hr]
    exact hω
  have hall : ∀ᵐ ω ∂gffBase.P, ∀ d ∈ S, ∀ k : ℕ,
      evalReg (normField γ (xPalm γ x) ω) ((foldedCircle d (radius k)).map (· + (x : ℂ))) =
        normField γ (xPalm γ x) ω ((foldedCircle d (radius k)).map (· + (x : ℂ))) :=
    (ae_ball_iff hSc).2 fun d _ => ae_all_iff.2 fun k => key d k
  filter_upwards [hall] with ω hω n k z
  exact hω _ (Set.mem_iUnion.2 ⟨n, z, rfl⟩) k

/-! ## Reduction of the regularity/goodness node to goodness -/

/-- **Goodness of the Palm field** (Duplantier–Sheffield, arXiv:0808.1560, §3.3: under the
rooted measure at `x`, `h` is a free-boundary GFF plus `γ(−log|x − ·|)` plus a function
harmonic near `x`; `γ < Q`, so a.s. `γ`-good as in `LogSingGood.logSingGoodAS_holds`). -/
def G2PalmGoodStmt (γ : ℝ) : Prop :=
  ∀ x : ℝ, x ≠ 0 → |x| < 1 → ∀ᵐ ω ∂gffBase.P, IsLQGGood γ (normField γ (xPalm γ x) ω)

theorem g2PalmRegGoodStmt_of_good {γ : ℝ} (h : G2PalmGoodStmt γ) : G2PalmRegGoodStmt γ := by
  intro x hx0 hx1
  filter_upwards [h x hx0 hx1, g2PalmReg_holds γ x] with ω hg hr
  exact ⟨hg, fun n k z _ => hr n k z⟩

/-- **`G2FixMixStmt` from D3⁺(i) (N2 form), the Palm identities, the length smoothing, the
goodness of the Palm field and the two boundary-length locality nodes.** -/
theorem g2FixMixStmt_of_goodLeaves {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hPX : G2RootXPalmIdStmt γ) (hSX : G2RootXLenSmoothStmt γ)
    (hPR : G2RootRPalmIdStmt γ) (hSR : G2RootRLenSmoothStmt γ)
    (hG : G2PalmGoodStmt γ) (hLX : G2RootXCutLocStmt γ) (hLR : G2RootRCutLocStmt γ) :
    G2FixMixStmt γ :=
  g2FixMixStmt_of_locLeaves hγ hγ2 hN2 hPX hSX hPR hSR (g2PalmRegGoodStmt_of_good hG) hLX hLR

end Thm18Asm
end QuantumZipper
