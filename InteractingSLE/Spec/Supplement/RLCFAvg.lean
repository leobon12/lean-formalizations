/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCFAvgDatum

/-!
# The chart real completion at the contact: integration over the retained datum, and Theorem W5

Packet PROVE-RLC-F, piece (iv). Source: supplement §7.1, p. 490 ("The same assertion applies after conditioning on one
retained initial datum. It suffices to prove it for almost every fixed datum. The final probability-one statement is
measurable in the original field and histories, so it can then be integrated"); W5's real local frame (pp. 535–536);
Astra's Prop. 5.2 with its countable witness construction (R52).

* **`RLC.retainedChartRealCompletionAtStatement_of_restart`**: `RLC.RetainedChartRealCompletionAtStatement` (the
  chart-level real-contact input at the contact, `RLCFAvgSide.lean`) from the named G2a, G3, G8 and
  `JumpVisitStatement` and the strengthened retained-pair restart `RLC.RetainedPairRestartUntouchedStatement`
  (PROVE-RLC-E). The per-datum event `RLC.RealEventC` (universally measurable, `RLCFAvgCode.lean`) holds almost surely
  for almost every datum (`RLC.ae_realEventC`, `RLCFAvgDatum.lean`), so almost surely along the restart
  (`RLC.ae_mem_of_ae_ae_compProd_of_uMeasurable`); pathwise it gives the property (`RLC.chartRealCompletionAt_of_event`,
  `RLCFAvgPath.lean`). The joint chart and the canonical seed germs are as in PROVE-RLC-B, RLC-D and RLC-E.
* `RLC.retainedChartRealCompletionAtStatement_of_param`: the same from Theorems 1.2 (param), 1.3 and the strengthened
  two-tip input `RLC.RetainedCanonCondDetUntouchedStatement` (R43/R48: for Theorem 1.5 only).
* **`RLC.w5Statement_of_frames_param`**: Theorem W5 (`Theorem15.W5Statement`) with the real-contact case discharged
  by G2a, G3, G8 and `JumpVisitStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Theorem15D5 Sec2.Assembly Supp7 Supp9D Restart

/-- Nonnegative imaginary parts at the dyadic times before the lifetime give `ℍ̄` before the lifetime. -/
theorem mem_Hbar_of_dyad {g : ℝ≥0 → ℂ} {U : ℝ≥0∞} (hc : ContinuousOn g {t | (t : ℝ≥0∞) ≤ U})
    (h : ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U → 0 ≤ (g (dyad n k)).im) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < U → g t ∈ Hbar := by
  intro t ht
  have hcs : ContinuousOn g (Iic t) := hc.mono fun s hs => (ENNReal.coe_le_coe.2 hs).trans ht.le
  show (0 : ℝ) ≤ (g t).im
  exact ge_of_tendsto ((Complex.continuous_im.tendsto _).comp (tendsto_comp_dyad_flr hcs le_rfl))
    (Eventually.of_forall fun n => h n _ ((ENNReal.coe_le_coe.2 (dyad_flr_le n t)).trans_lt ht))

/-- **`RetainedChartRealCompletionAtStatement` from G2a, G3, G8, `JumpVisitStatement` and the strengthened
retained-pair restart.** -/
theorem retainedChartRealCompletionAtStatement_of_restart (hG2a : G2aReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hG8 : G8FrameStatement.{0}) (hJV : JumpVisitStatement.{0})
    (hR : RetainedPairRestartUntouchedStatement.{u}) : RetainedChartRealCompletionAtStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ u r
  subst hu hr
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hker, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  have := hK
  obtain ⟨-, hU₁m, hU₂m, hΓ₁m, hΓ₂m, hΓ₁c, hΓ₂c⟩ := hco
  -- (1) the chart position of the first tip is positive
  have F1 : ∀ᵐ ω ∂P, ω ∈ M → 0 < (β ω).2 :=
    (ae_restrict_iff' hM).1 (ae_of_ae_map hβ.aemeasurable (hker.mono fun c hc => hc.1))
  -- (2) the chart seeds
  have F2 : ∀ᵐ ω ∂P, ω ∈ M → Γ₁ (X ω) 0 = ((β ω).2 : ℂ) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₁ p.2 0 = (p.1.2 : ℂ)} :=
      measurableSet_eq_fun ((hΓ₁m 0).comp measurable_snd)
        (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst))
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.1)
  have F3 : ∀ᵐ ω ∂P, ω ∈ M → Γ₂ (X ω) 0 = ((0 : ℝ) : ℂ) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₂ p.2 0 = ((0 : ℝ) : ℂ)} :=
      measurableSet_eq_fun ((hΓ₂m 0).comp measurable_snd) measurable_const
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.2)
  -- (3) a wrong side at the first tip kills the first continuation
  have F4 : ∀ᵐ ω ∂P, ω ∈ M → (β ω ∈ BadSeed κ θ₁ → U₁ (X ω) = 0) := by
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} := by
      have e : {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} =
          (Prod.fst ⁻¹' BadSeed κ θ₁)ᶜ ∪ {p | U₁ p.2 = 0} := by
        ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
      rw [e]
      exact ((measurableSet_badSeed κ θ₁).preimage measurable_fst).compl.union
        (measurableSet_eq_fun (hU₁m.comp measurable_snd) measurable_const)
    refine ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hker.mono fun c hc => ?_)
    by_cases hcb : c ∈ BadSeed κ θ₁
    · filter_upwards [ae_eq_zero_of_mem_badSeed hκ hcb hc.2.2.1] with s hs _ using hs
    · exact Eventually.of_forall fun s h' => absurd h' hcb
  -- (4) the chart paths stay in `ℍ̄` before their lifetimes
  have F6 : ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), (∀ t, Measurable fun x => Γ x t) → Measurable U →
      (∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s → 0 ≤ (Γ s t).im) →
      ∀ᵐ ω ∂P, ω ∈ M → ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U (X ω) → 0 ≤ (Γ (X ω) (dyad n k)).im := by
    intro Γ U hΓm hUm hae
    have hE : MeasurableSet {p : (BoundaryWord × ℝ) × S |
        ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U p.2 → 0 ≤ (Γ p.2 (dyad n k)).im} :=
      measurableSet_setOfPred.mpr (Measurable.forall fun n => Measurable.forall fun k =>
        (measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hUm.comp measurable_snd))).imp
          (measurableSet_setOfPred.mp (measurableSet_le measurable_const
            (Complex.measurable_im.comp ((hΓm (dyad n k)).comp measurable_snd)))))
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE)
      (hae.mono fun c hc => hc.mono fun s hs n k hnk => hs _ hnk.le)
  have F6₁ := F6 Γ₁ U₁ hΓ₁m hU₁m (hker.mono fun c hc => Supp7.ae_im_nonneg_of_isFlowLine hc.2.2.1)
  have F6₂ := F6 Γ₂ U₂ hΓ₂m hU₂m (hker.mono fun c hc => Supp7.ae_im_nonneg_of_isFlowLine hc.2.2.2)
  -- (5) the per-datum real completion event, integrated over the datum
  have hencm₁ : Measurable fun x : S => encC (Γ₁ x) :=
    measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hΓ₁m (dyad n k)
  have hencm₂ : Measurable fun x : S => encC (Γ₂ x) :=
    measurable_pi_iff.mpr fun n => measurable_pi_iff.mpr fun k => hΓ₂m (dyad n k)
  have hEum : LQGMetric.UMeasurableSet {p : (BoundaryWord × ℝ) × S | p.1 ∈ HasSeedGerms κ θ₁ θ₂ →
      RealEventC p.1.1 p.1.2 (encC (Γ₁ p.2)) (U₁ p.2) (encC (Γ₂ p.2)) (U₂ p.2)} := by
    have e : {p : (BoundaryWord × ℝ) × S | p.1 ∈ HasSeedGerms κ θ₁ θ₂ →
        RealEventC p.1.1 p.1.2 (encC (Γ₁ p.2)) (U₁ p.2) (encC (Γ₂ p.2)) (U₂ p.2)} =
        (Prod.fst ⁻¹' HasSeedGerms κ θ₁ θ₂)ᶜ ∪
          (fun p : (BoundaryWord × ℝ) × S => (p.1, ((encC (Γ₁ p.2), U₁ p.2), (encC (Γ₂ p.2), U₂ p.2)))) ⁻¹'
            {x | RealEventC x.1.1 x.1.2 x.2.1.1 x.2.1.2 x.2.2.1 x.2.2.2} := by
      ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
    rw [e]
    exact (LQGMetric.UMeasurableSet.of_measurableSet
      ((measurableSet_hasSeedGerms κ θ₁ θ₂).preimage measurable_fst)).compl.union
      (uMeasurableSet_realEventC.preimage (measurable_fst.prodMk
        (((hencm₁.comp measurable_snd).prodMk (hU₁m.comp measurable_snd)).prodMk
          ((hencm₂.comp measurable_snd).prodMk (hU₂m.comp measurable_snd)))))
  have F5 : ∀ᵐ ω ∂P, ω ∈ M → (β ω ∈ HasSeedGerms κ θ₁ θ₂ →
      RealEventC (β ω).1 (β ω).2 (encC (Γ₁ (X ω))) (U₁ (X ω)) (encC (Γ₂ (X ω))) (U₂ (X ω))) := by
    refine ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw hEum (hker.mono fun c hc => ?_)
    by_cases hcg : c ∈ HasSeedGerms κ θ₁ θ₂
    · filter_upwards [ae_realEventC hG2a hG3 hG8 hJV hκ hκ4 hθ hcg (K c) H₀ hc.2.1 Γ₁ Γ₂ U₁ U₂ hc.2.2.1
        hc.2.2.2] with s hs _ using hs
    · exact Eventually.of_forall fun s h' => absurd h' hcg
  refine ⟨fun ω => Γ₁ (X ω), fun ω => Γ₂ (X ω), fun ω => U₁ (X ω), fun ω => U₂ (X ω),
    fun ω => (β ω).2, ?_⟩
  filter_upwards [hpath, hag, F1, F2, F3, F4, F5, F6₁, F6₂, Sec7.ae_continuousOn_of_isFlowLine hη₁,
    Sec7.ae_continuousOn_of_isFlowLine hη₂, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    Supp7.ae_im_nonneg_of_isFlowLine hη₁, Supp7.ae_im_nonneg_of_isFlowLine hη₂,
    Supp9.ae_apply_zero_of_isFlowLine hη₁, Supp9.ae_apply_zero_of_isFlowLine hη₂]
    with ω hω hagω f1 f2 f3 f4 f5 f6₁ f6₂ k₁ k₂ i₁ i₂ m₁ m₂ z₁ z₂ hord
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, -, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩, hword,
    huw⟩ := hω hord
  have hg := hd.good ω (RetData.E_subset_G hE)
  obtain ⟨-, hC⟩ := hd.isRetChart hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have hdom := activeDomain_congr_Icc e₁ e₂
  have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
  have htip₁ : d.η₁ ω d.u = η₁ ω d.u := ha₁ d.u le_rfl
  -- the real joint chart (the proof of `RLC.realJointChartUntouchedStatement_of_restart`)
  have hJ : IsRealJointChart (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r (Γ₁ (X ω)) (Γ₂ (X ω)) (U₁ (X ω)) (U₂ (X ω))
      (d.inv ω) := by
    refine ⟨?_, ?_, hC.continuousOn_inv, hC.2.2.2.2.2.2.2.2.2.1, ?_,
      ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, fun s hs => ⟨hpth₁ s hs, hH₁ s hs⟩⟩,
      ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, fun s hs => ⟨hpth₂ s hs, hH₂ s hs⟩⟩, ?_⟩
    · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
    · rw [← htip]; exact hC.inv_zero hg.2.2.2.2.2.1
    · intro y y' he _ hA
      have hK' : d.inv ω (y : ℂ) ∉ prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
        rw [prefixSet_congr_Icc e₁ e₂]; exact hA
      exact ofReal_injective (eq_of_inv_eq_of_notMem hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1
        (ofReal_mem_Hbar y) (ofReal_mem_Hbar y') he hK')
  have hW0 : 0 < (β ω).2 := f1 hMω
  have hΓ0 : Γ₁ (X ω) 0 = ((β ω).2 : ℂ) := f2 hMω
  have hΓ0' : Γ₂ (X ω) 0 = 0 := by rw [f3 hMω]; simp
  -- the canonical seed germs of the datum (the proof of `RLC.retainedChartCompletionStatement_of_restart`)
  have h00 : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
  have hc₁0 : c₁ 0 = d.u := clock_zero hord.1.le hmono₁ himg₁
  have hψW : d.inv ω ((β ω).2 : ℂ) = d.η₁ ω d.u := by
    rw [htip₁, ← hc₁0, hpth₁ 0 h00, hΓ0]
  have hB : IsClosed (η₂ ω '' Icc 0 d.r) :=
    (isCompact_Icc.image_of_continuousOn (k₂.mono fun t ht =>
      (ENNReal.coe_le_coe.2 ht.2).trans hord.2.1.le)).isClosed
  have hU₁pos : 0 < U₁ (X ω) :=
    lt_of_lt_of_le (pos_of_isClock hord.1 k₁ i₁ hB hord.2.2.2.2.2.1 hmono₁ himg₁) hσ₁
  have hnb : β ω ∉ BadSeed κ θ₁ := fun hb' => (ne_of_gt hU₁pos) (f4 hMω hb')
  have hi : InjOn (d.η₁ ω) (Icc 0 d.u) :=
    (i₁.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hord.1.le).congr e₁.symm
  have hpH : d.η₂ ω d.r ∈ H := by rw [htip]; exact hord.2.2.2.1
  have hp : d.η₂ ω d.r ∉ d.η₁ ω '' Icc 0 d.u := by rw [htip, e₁.image_eq]; exact hord.2.2.2.2.1
  have hqH : d.η₁ ω d.u ∈ H := by rw [htip₁]; exact hord.2.2.1
  have hq : d.η₁ ω d.u ∉ d.η₂ ω '' Icc 0 d.r := by rw [htip₁, e₂.image_eq]; exact hord.2.2.2.2.2.1
  obtain ⟨δ, hδ, h0g, hWg⟩ := exists_wordGerm_of_retChart hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 hpH hp
    hg.2.2.2.2.2.2 hqH hq hi hψW (isRetainedWord_congr e₁.symm e₂.symm hword)
  have hgerm : β ω ∈ HasSeedGerms κ θ₁ θ₂ := by
    have := mem_hasSeedGerms_of_wordGerm (θ₂ := θ₂) hW0 hδ h0g hWg (by rwa [Prod.mk.eta])
    rwa [Prod.mk.eta] at this
  -- the real completion property at the contact
  have hCR := chartRealCompletionAt_of_event k₁ k₂ i₁ i₂ m₁ m₂ (by rw [z₁]; simp) (by rw [z₂]; simp) hord hJ hΓ0
    hΓ0' (hΓ₁c (X ω)) (hΓ₂c (X ω)) (mem_Hbar_of_dyad (hΓ₁c (X ω)) (f6₁ hMω))
    (mem_Hbar_of_dyad (hΓ₂c (X ω)) (f6₂ hMω)) hb huw (f5 hMω hgerm)
  rw [z₁, z₂, ofReal_re, ofReal_re] at hCR
  exact ⟨hW0, hΓ0, hΓ0', d.inv ω, hJ, hCR⟩

/-- **`RetainedChartRealCompletionAtStatement` from G2a, G3, G8, `JumpVisitStatement`, Theorems 1.2 (param), 1.3 and
the strengthened two-tip input** (R43/R48: for Theorem 1.5 only). -/
theorem retainedChartRealCompletionAtStatement_of_param (hG2a : G2aReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hG8 : G8FrameStatement.{0}) (hJV : JumpVisitStatement.{0})
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0})
    (hD : RetainedCanonCondDetUntouchedStatement.{u}) : RetainedChartRealCompletionAtStatement.{u} :=
  retainedChartRealCompletionAtStatement_of_restart hG2a hG3 hG8 hJV
    (retainedPairRestartUntouchedStatement_of_param h12p h13 hD)

/-- **Theorem W5** (`Theorem15.W5Statement`) from Aux. lemma 25, W0a, W0b, Lemma 7.7, the joint G7 carrier, the
common-seed comparison, G2a (hence G2), G3, G8, `JumpVisitStatement`, Theorems 1.2 (param), 1.3 and the strengthened
two-tip input: `RLC.w5Statement_of_chartRealAt_param` with the real-contact case discharged. -/
theorem w5Statement_of_frames_param (h25 : Theorem15.Aux25Statement.{u}) (hW0a : Supp9.W0aStatement.{u})
    (hW0b : Supp9.W0bStatement.{u}) (h77 : Supp10.Lemma77Statement.{0}) (hJ : JointRetainedPairStatement.{u})
    (hCS : Supp9.W5CommonSeedStatement.{u}) (hG2a : G2aReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hG8 : G8FrameStatement.{0}) (hJV : JumpVisitStatement.{0})
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0})
    (hD : RetainedCanonCondDetUntouchedStatement.{u}) : Theorem15.W5Statement.{u} :=
  w5Statement_of_chartRealAt_param h25 hW0a hW0b h77 hJ hCS (g2ReferenceStatement_of_g2a hG2a) hG3 h12p h13
    (retainedCanonCondDetStatement_of_untouched hD)
    (retainedChartRealCompletionAtStatement_of_param hG2a hG3 hG8 hJV h12p h13 hD)

end RLC

end InteractingSLE
