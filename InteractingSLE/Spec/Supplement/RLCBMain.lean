/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCBGerm
import InteractingSLE.Spec.Supplement.RLCMain

/-!
# Theorem 1.5's retained chart completion from G2, G2b and G3

Packet PROVE-RLC-B. **`RLC.RetainedChartCompletionStatement`** (the interior-case input of
`RLC.retainedLocalCompletionStatement_of_chart`, PROVE-RLC-A) is proved here from the two named inputs of
PROVE-RLC-A, `RLC.G2ReferenceStatement` (Lemma G2 with G2b) and `RLC.G3ChartComparisonStatement` (Lemma G3), and the
retained-pair restart (`Supp7.RetainedPairRestartStatement`, hence from Theorems 1.2 (param), 1.3 and PROVE-CONDDET's
`Restart.RetainedCanonCondDetStatement`), by the three steps of `planning/handoffs/PROVE-RLC-A.md` §"What remains" 1:

* (i) buffer selection: `RLC.ae_chartInteriorCompletion_of_hasSeedGerms` (`RLCBBuffer.lean`);
* (ii) the canonical seed germs of the datum: the retained word near the chart seeds
  (`RLC.exists_wordGerm_of_retChart`), the side at the first tip from positive lifetime (`RLC.BadSeed`) — here the
  positivity of the first clock (`pos_of_isClock`) at an ordinary retained pair;
* (iii) integration over the datum: the event is universally measurable (`RLCBCode.lean`).

Main results: `retainedChartCompletionStatement_of_restart`, `retainedChartCompletionStatement_of_param`, and the
reductions of `Supp9D.RetainedLocalCompletionStatement` to the real-contact case alone
(`retainedLocalCompletionStatement_of_restart`, `retainedLocalCompletionStatement_of_param`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart

/-! ### The clock at the retained cutoff -/

section Clock

variable {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {A : Set ℂ} {u : ℝ≥0} {c : ℝ≥0 → ℝ≥0} {σ : ℝ≥0∞}

/-- The clock starts at the cutoff. -/
theorem clock_zero (huζ : (u : ℝ≥0∞) ≤ ζ) (hmono : StrictMonoOn c {s | (s : ℝ≥0∞) ≤ σ})
    (himg : c '' {s | (s : ℝ≥0∞) ≤ σ} = {x | u ≤ x ∧ (x : ℝ≥0∞) ≤ ζ ∧ ∀ x' : ℝ≥0, u < x' → x' < x → η x' ∉ A}) :
    c 0 = u := by
  have hu : u ∈ c '' {s | (s : ℝ≥0∞) ≤ σ} := by
    rw [himg]; exact ⟨le_rfl, huζ, fun x' h1 h2 => absurd (h1.trans h2) (lt_irrefl _)⟩
  obtain ⟨s₀, hs₀, hcs₀⟩ := hu
  have h0 : (0 : ℝ≥0) ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ σ} := by
    show ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ; exact (ENNReal.coe_le_coe.2 zero_le).trans hs₀
  have hc0 : c 0 ∈ c '' {s | (s : ℝ≥0∞) ≤ σ} := ⟨0, h0, rfl⟩
  rw [himg] at hc0
  refine le_antisymm ?_ hc0.1
  rw [← hcs₀]
  exact hmono.monotoneOn h0 hs₀ zero_le

/-- **The clock runs for a positive chart time** at a cutoff strictly before the lifetime, when the path is
continuous and simple and its tip is off the closed rest `B` of `A = η([0, u]) ∪ B`. -/
theorem pos_of_isClock {B : Set ℂ} (huζ : (u : ℝ≥0∞) < ζ) (hc : ContinuousOn η {x | (x : ℝ≥0∞) ≤ ζ})
    (hi : InjOn η {x | (x : ℝ≥0∞) ≤ ζ}) (hB : IsClosed B) (huB : η u ∉ B)
    (hmono : StrictMonoOn c {s | (s : ℝ≥0∞) ≤ σ})
    (himg : c '' {s | (s : ℝ≥0∞) ≤ σ} =
      {x | u ≤ x ∧ (x : ℝ≥0∞) ≤ ζ ∧ ∀ x' : ℝ≥0, u < x' → x' < x → η x' ∉ η '' Icc 0 u ∪ B}) :
    0 < σ := by
  have hc0 := clock_zero huζ.le hmono himg
  obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB.isOpen_compl (η u) huB
  obtain ⟨δ, hδ, hδη⟩ := Metric.continuousWithinAt_iff.1 (hc u huζ.le) ε hε
  obtain ⟨v, huv, hvζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 huζ
  have huv' : u < v := by exact_mod_cast huv
  set x : ℝ≥0 := min (u + (δ / 2).toNNReal) v with hx
  have hd2 : (0 : ℝ≥0) < (δ / 2).toNNReal := Real.toNNReal_pos.2 (by positivity)
  have hux : u < x := lt_min (lt_add_of_pos_right _ hd2) huv'
  have hxv : x ≤ v := min_le_right _ _
  have hxδ : (x : ℝ) ≤ u + δ / 2 := by
    have h1 : x ≤ u + (δ / 2).toNNReal := min_le_left _ _
    have h2 : ((u + (δ / 2).toNNReal : ℝ≥0) : ℝ) = u + δ / 2 := by
      rw [NNReal.coe_add, Real.coe_toNNReal _ (by positivity)]
    rw [← h2]; exact_mod_cast h1
  have hxζ : (x : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hxv).trans hvζ.le
  have hxmem : x ∈ c '' {s | (s : ℝ≥0∞) ≤ σ} := by
    rw [himg]
    refine ⟨hux.le, hxζ, fun x' h1 h2 => ?_⟩
    have hx'ζ : (x' : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 h2.le).trans hxζ
    rintro (⟨s, hs, hse⟩ | hB')
    · have hsζ : (s : ℝ≥0∞) ≤ ζ := (ENNReal.coe_le_coe.2 hs.2).trans huζ.le
      have := hi hsζ hx'ζ hse
      exact absurd (this ▸ hs.2) (not_le.2 h1)
    · have hd : dist x' u < δ := by
        rw [NNReal.dist_eq, abs_lt]
        have h1' : (u : ℝ) < x' := by exact_mod_cast h1
        have h2' : (x' : ℝ) < x := by exact_mod_cast h2
        constructor <;> linarith
      exact hεB (hδη hx'ζ hd) hB'
  obtain ⟨s, hs, hcs⟩ := hxmem
  have hs0 : s ≠ 0 := fun h => by rw [h, hc0] at hcs; exact (ne_of_lt hux) hcs
  exact lt_of_lt_of_le (by exact_mod_cast pos_iff_ne_zero.2 hs0) hs

end Clock

/-! ### The retained word along prefix-agreeing paths -/

/-- `IsRetainedWord` sees the paths only through their prefixes. -/
theorem isRetainedWord_congr {κ θ₁ θ₂ : ℝ} {α α' β β' : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {c : BoundaryWord}
    (e₁ : EqOn α α' (Icc 0 a)) (e₂ : EqOn β β' (Icc 0 b)) (h : IsRetainedWord κ θ₁ θ₂ α a β b ψ c) :
    IsRetainedWord κ θ₁ θ₂ α' a β' b ψ c := by
  have ha : α a = α' a := e₁ (right_mem_Icc.2 zero_le)
  have hb : β b = β' b := e₂ (right_mem_Icc.2 zero_le)
  intro y hyH hyb hya hy
  rw [← e₁.image_eq, ← e₂.image_eq]
  rw [← e₁.image_eq, ← e₂.image_eq] at hy
  rw [← hb] at hyb
  rw [← ha] at hya
  exact h y hyH hyb hya hy

/-! ### The retained chart completion -/

/-- **`RetainedChartCompletionStatement` from G2 (+ G2b), G3 and the retained-pair restart** (supplement §7.1–§7.3,
pp. 490–493, and the verification of G3's hypotheses for retained original histories, p. 493). -/
theorem retainedChartCompletionStatement_of_restart (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hR : RetainedPairRestartStatement.{u}) :
    RetainedChartCompletionStatement.{u} := by
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
  -- (4) the chart interior completion property, integrated over the datum
  have hCICum : LQGMetric.UMeasurableSet {x : S | ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)} :=
    uMeasurableSet_chartInteriorCompletion hU₁m hU₂m hΓ₁m hΓ₂m hΓ₁c hΓ₂c
  have F5 : ∀ᵐ ω ∂P, ω ∈ M → (β ω ∈ HasSeedGerms κ θ₁ θ₂ →
      ChartInteriorCompletion (Γ₁ (X ω)) (U₁ (X ω)) (Γ₂ (X ω)) (U₂ (X ω))) := by
    have hE : LQGMetric.UMeasurableSet {p : (BoundaryWord × ℝ) × S | p.1 ∈ HasSeedGerms κ θ₁ θ₂ →
        ChartInteriorCompletion (Γ₁ p.2) (U₁ p.2) (Γ₂ p.2) (U₂ p.2)} := by
      have e : {p : (BoundaryWord × ℝ) × S | p.1 ∈ HasSeedGerms κ θ₁ θ₂ →
          ChartInteriorCompletion (Γ₁ p.2) (U₁ p.2) (Γ₂ p.2) (U₂ p.2)} =
          (Prod.fst ⁻¹' HasSeedGerms κ θ₁ θ₂)ᶜ ∪
            Prod.snd ⁻¹' {x : S | ChartInteriorCompletion (Γ₁ x) (U₁ x) (Γ₂ x) (U₂ x)} := by
        ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
      rw [e]
      exact (LQGMetric.UMeasurableSet.of_measurableSet
        ((measurableSet_hasSeedGerms κ θ₁ θ₂).preimage measurable_fst)).compl.union
        (hCICum.preimage measurable_snd)
    refine ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw hE (hker.mono fun c hc => ?_)
    by_cases hcg : c ∈ HasSeedGerms κ θ₁ θ₂
    · filter_upwards [ae_chartInteriorCompletion_of_hasSeedGerms hG2 hG3 hκ hκ4 hθ hcg (K c) H₀ hc.2.1 Γ₁ Γ₂
        U₁ U₂ hc.2.2.1 hc.2.2.2] with s hs _ using hs
    · exact Eventually.of_forall fun s h' => absurd h' hcg
  refine ⟨fun ω => H₀ (X ω), fun ω => Γ₁ (X ω), fun ω => Γ₂ (X ω), fun ω => U₁ (X ω), fun ω => U₂ (X ω),
    fun ω => (β ω).2, ?_⟩
  filter_upwards [hpath, hag, F1, F2, F3, F4, F5, Sec7.ae_continuousOn_of_isFlowLine hη₁,
    Sec7.ae_continuousOn_of_isFlowLine hη₂, Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁]
    with ω hω hagω f1 f2 f3 f4 f5 k₁ k₂ i₁ hord
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, hHX, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩,
    hword⟩ := hω hord
  have hg := hd.good ω (RetData.E_subset_G hE)
  obtain ⟨-, hC⟩ := hd.isRetChart hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have hdom := activeDomain_congr_Icc e₁ e₂
  have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
  have htip₁ : d.η₁ ω d.u = η₁ ω d.u := ha₁ d.u le_rfl
  -- the joint chart (the proof of `RLC.jointRetainedChartStatement_of_restart`)
  have htr := hd.isChartTransport_chartField κ h ω
  rw [RetData.chart_of_mem hE, ← hHX] at htr
  have hJ : IsJointRetainedChart κ (h ω) (H₀ (X ω)) (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r (Γ₁ (X ω)) (Γ₂ (X ω))
      (U₁ (X ω)) (U₂ (X ω)) := by
    refine ⟨d.fwd ω, d.inv ω, d.lift ω, c₁, c₂, σ₁, σ₂, ?_, ?_, hC.fwd_inv, ?_, ?_, ?_, htr,
      hC.continuousOn_inv, hC.2.2.2.2.2.2.2.2.2.1, ?_, hσ₁, hmono₁, himg₁, hσ₂, hmono₂, himg₂,
      fun s hs => ⟨hpth₁ s hs, hH₁ s hs⟩, fun s hs => ⟨hpth₂ s hs, hH₂ s hs⟩, ?_⟩
    · rw [← hdom, ← htip]; exact hC.isActiveChart hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.continuousOn_lift hg.2.2.2.2.2.1
    · rw [← hdom]; exact hC.deriv_eq hg.2.2.2.2.2.1
    · rw [← htip]; exact hC.inv_zero hg.2.2.2.2.2.1
    · intro s₁ s₂ hs₁ hs₂ he hA
      have hψ : d.inv ω (Γ₁ (X ω) s₁) = d.inv ω (Γ₂ (X ω) s₂) := by rw [← hpth₁ s₁ hs₁, ← hpth₂ s₂ hs₂, he]
      have hK : d.inv ω (Γ₁ (X ω) s₁) ∉ prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
        rw [prefixSet_congr_Icc e₁ e₂, ← hpth₁ s₁ hs₁]; exact hA
      exact eq_of_inv_eq_of_notMem hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1 (hH₁ s₁ hs₁) (hH₂ s₂ hs₂) hψ hK
  have hW0 : 0 < (β ω).2 := f1 hMω
  have hΓ0 : Γ₁ (X ω) 0 = ((β ω).2 : ℂ) := f2 hMω
  have hΓ0' : Γ₂ (X ω) 0 = 0 := by rw [f3 hMω]; simp
  -- the inverse chart sends the first chart seed to the first tip
  have h00 : ((0 : ℝ≥0) : ℝ≥0∞) ≤ σ₁ := by simp
  have hc₁0 : c₁ 0 = d.u := clock_zero hord.1.le hmono₁ himg₁
  have hψW : d.inv ω ((β ω).2 : ℂ) = d.η₁ ω d.u := by
    rw [htip₁, ← hc₁0, hpth₁ 0 h00, hΓ0]
  -- the first continuation runs for a positive time, so the first seed has the right sides
  have hB : IsClosed (η₂ ω '' Icc 0 d.r) :=
    (isCompact_Icc.image_of_continuousOn (k₂.mono fun t ht =>
      (ENNReal.coe_le_coe.2 ht.2).trans hord.2.1.le)).isClosed
  have hU₁pos : 0 < U₁ (X ω) :=
    lt_of_lt_of_le (pos_of_isClock hord.1 k₁ i₁ hB hord.2.2.2.2.2.1 hmono₁ himg₁) hσ₁
  have hnb : β ω ∉ BadSeed κ θ₁ := fun hb' => (ne_of_gt hU₁pos) (f4 hMω hb')
  -- the retained word near the chart seeds
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
  exact ⟨hJ, hW0, hΓ0, hΓ0', f5 hMω hgerm⟩

/-- **`RetainedChartCompletionStatement` from G2 (+ G2b), G3, Theorems 1.2 (param), 1.3 and PROVE-CONDDET's two-tip
P-side input** (R43: downstream of Theorem 1.2). -/
theorem retainedChartCompletionStatement_of_param (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetStatement.{u}) :
    RetainedChartCompletionStatement.{u} :=
  retainedChartCompletionStatement_of_restart hG2 hG3
    (retainedPairRestartStatement_of_clock (retainedKernelClockStatement_of_param h12p h13 hD))

/-- **Theorem 1.5's retained local completion from G2, G3, the retained-pair restart and the real-contact case.** -/
theorem retainedLocalCompletionStatement_of_restart (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (hR : RetainedPairRestartStatement.{u})
    (hReal : RetainedLocalCompletionRealStatement.{u}) : Supp9D.RetainedLocalCompletionStatement.{u} :=
  retainedLocalCompletionStatement_of_chart (retainedChartCompletionStatement_of_restart hG2 hG3 hR) hReal

/-- **Theorem 1.5's retained local completion from G2, G3, Theorems 1.2 (param), 1.3, PROVE-CONDDET's two-tip input
and the real-contact case.** -/
theorem retainedLocalCompletionStatement_of_param (hG2 : G2ReferenceStatement.{0})
    (hG3 : G3ChartComparisonStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetStatement.{u})
    (hReal : RetainedLocalCompletionRealStatement.{u}) : Supp9D.RetainedLocalCompletionStatement.{u} :=
  retainedLocalCompletionStatement_of_chart (retainedChartCompletionStatement_of_param hG2 hG3 h12p h13 hD) hReal

end RLC

end InteractingSLE
