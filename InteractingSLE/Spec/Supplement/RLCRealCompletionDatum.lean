/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCRealCompletionG7a
import InteractingSLE.Spec.Supplement.RLCGJump

/-!
# The chart real completion at the contact from Corollary G7a, integrated over the retained datum

Packet PROVE-G3RESTART. Source: supplement §7.1, p. 490 ("It suffices to prove it for almost every fixed datum. The
final probability-one statement is measurable in the original field and histories, so it can then be integrated");
W5's real local frame (pp. 535–536); Corollary G7a (pp. 498–499); Astra's Prop. 5.2 (R52).

PROVE-RLC-F's derivation (`RLC.ae_realEventC`, `RLC.retainedChartRealCompletionAtStatement_of_restart`) uses the
single-buffer `RLC.G3ChartComparisonStatement` only through the per-datum event. Here the per-datum event is isolated:

* `RealEventDatumStatement`: for every datum with the canonical seed germs, the countable-form real completion event
  `RLC.RealEventC` holds almost surely for the chart pair (the per-datum content of W5's real local frame);
* **`realEventDatumStatement_of_g7a`**: it follows from G2a, Corollary G7a and G8 (`RLC.ae_realEventC`'s proof with the
  `…_g7a` transfers of `RLCRealCompletionG7a.lean`, and the proved `RLC.jumpVisitStatement`);
  `realEventDatumStatement_of_g3`: PROVE-RLC-F's own route, for comparison;
* **`retainedChartRealCompletionAtStatement_of_datum`**: `RLC.RetainedChartRealCompletionAtStatement` from the
  per-datum statement and the strengthened retained-pair restart (the proof of
  `RLC.retainedChartRealCompletionAtStatement_of_restart` with the per-datum call abstracted);
* **`retainedChartRealCompletionAtStatement_of_g7a_param`**: the same from G2a, G7a, G8, Theorems 1.2 (param), 1.3 and
  the strengthened two-tip input `RLC.RetainedCanonCondDetUntouchedStatement`.

R43/R48: for Theorem 1.5 only.
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

/-! ### The per-datum real completion event -/

/-- **The real completion event at every datum with the canonical seed germs, almost surely** (W5's real local frame,
pp. 535–536, at one retained datum, supplement p. 490): for the GFF with the chart word `c.1` and its angle-`θ₁` flow
from `c.2` and angle-`θ₂` flow from `0`, the countable-form event `RLC.RealEventC` holds almost surely. -/
def RealEventDatumStatement : Prop :=
  ∀ κ θ₁ θ₂ : ℝ, 0 < κ → κ < 4 → θ₁ < θ₂ → ∀ c : BoundaryWord × ℝ, c ∈ HasSeedGerms κ θ₁ θ₂ →
    ∀ {S' : Type u} [MeasurableSpace S'] (Q₀ : Measure S') [IsProbabilityMeasure Q₀]
      (H₀ : S' → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData Q₀ H₀ c.1.fn c.1.jumps →
    ∀ (Γ₁ Γ₂ : S' → ℝ≥0 → ℂ) (U₁ U₂ : S' → ℝ≥0∞),
      IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ Q₀ H₀ Γ₁ U₁ → IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ Q₀ H₀ Γ₂ U₂ →
      ∀ᵐ x ∂Q₀, RealEventC c.1 c.2 (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x)

/-- PROVE-RLC-F's route to the per-datum statement (G2a, the single-buffer G3, G8; the jump part is proved). -/
theorem realEventDatumStatement_of_g3 (hG2a : G2aReferenceStatement.{u}) (hG3 : G3ChartComparisonStatement.{u})
    (hG8 : G8FrameStatement.{u}) : RealEventDatumStatement.{u} :=
  fun _ _ _ hκ hκ4 hθ _ hc _ _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂ =>
    ae_realEventC hG2a hG3 hG8 jumpVisitStatement hκ hκ4 hθ hc Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂

/-- **The real completion event at one datum from G2a, Corollary G7a and G8** (`RLC.ae_realEventC`'s proof: by region,
the G8 frame right of `w`, the G2a word between the seeds and the reflected G8 frame left of `0` when the visited
height is hitting and admissible, and otherwise no visit; the jump part from `RLC.jumpVisitStatement`; the comparison
with each reference is Corollary G7a). -/
theorem realEventDatumStatement_of_g7a (hG2a : G2aReferenceStatement.{u}) (hG7a : G7aChartStatement.{u})
    (hG8 : G8FrameStatement.{u}) : RealEventDatumStatement.{u} := by
  intro κ θ₁ θ₂ hκ hκ4 hθ c hc S' _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  obtain ⟨q, q₁, q₂, hSg⟩ := hc
  obtain ⟨c, w⟩ := c
  simp only at hSg hH h₁ h₂ ⊢
  have hw : 0 < w := hSg.w_pos
  have hc₁ := Sec7.ae_continuousOn_of_isFlowLine h₁
  have hc₂ := Sec7.ae_continuousOn_of_isFlowLine h₂
  have hm₁ := Supp7.ae_im_nonneg_of_isFlowLine h₁
  have hm₂ := Supp7.ae_im_nonneg_of_isFlowLine h₂
  have hlam := Sec4.sleLambda_pos hκ
  -- the jump part
  have hjump : ∀ᵐ x ∂Q₀, JumpFreeC c w (encC (Γ₁ x)) (U₁ x) := by
    filter_upwards [jumpVisitStatement κ hκ hκ4 c.fn c.jumps c.isPiecewiseConstantBoundaryData w θ₁ Q₀ H₀ hH Γ₁ U₁
      h₁, hc₁] with x hx cx i hi hiw pp hpp
    have cs : ContinuousOn (Γ₁ x) (Iic (dyad pp.1 pp.2)) :=
      cx.mono fun t ht => (ENNReal.coe_le_coe.2 ht).trans hpp.le
    rw [avoidPtC_iff, avoidC_encC_iff cs isClosed_singleton (singleton_nonempty _)]
    intro t ht hts he
    exact hx t ht ((ENNReal.coe_le_coe.2 hts).trans_lt hpp) (c.2.1 i) (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩) hiw he
  -- the strip part
  have key : ∀ S : List (ℚ × ℚ), StripCond c w S →
      ∃ k : ℕ, ∀ᵐ x ∂Q₀, StripEventC S w k (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x) := by
    intro S hSC
    rcases S with _ | ⟨ab₀, S₀⟩
    · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ (Eventually.of_forall fun x => Or.inl ?_)
      rintro t - - - ⟨ab, hab, -⟩
      exact absurd hab List.not_mem_nil
    set S := ab₀ :: S₀ with hSdef
    set C := c.fn ab₀.1 with hCdef
    have hC : ∀ ab ∈ S, c.fn ab.1 = C := fun ab hab => hSC.2.2 ab hab ab₀ List.mem_cons_self
    have hcC : ∀ ab ∈ S, ∀ y ∈ Ioo (ab.1 : ℝ) ab.2, y ∉ c.jumps → c.fn y = C := fun ab hab y hy _ =>
      ((hSC.fn_eq hab ⟨hy.1.le, hy.2.le⟩).2).trans (hC ab hab)
    rcases hSC.1 with hL | hM | hR
    · -- left of the second seed: the reflected G8 frame, or no visit by the higher-angle flow
      obtain ⟨b₀, hb₀, hb⟩ := exists_between_list_snd hL
      obtain ⟨a₁, ha₁⟩ := exists_lt_list_fst S
      have hab : ∀ ab ∈ S, min a₁ b₀ - 1 < ab.1 ∧ (ab.2 : ℝ) < b₀ := fun ab h =>
        ⟨by linarith [min_le_left a₁ b₀, ha₁ ab h], hb ab h⟩
      by_cases hwt : -2 < Sec4.cumWeightLeft κ (C + θ₂ * QuantumZipper.chiC κ) ∧
          Sec4.cumWeightLeft κ (C + θ₂ * QuantumZipper.chiC κ) < κ / 2 - 2
      · exact exists_ae_of_ref hc₁ hc₂ hm₁ hm₂ hSC hab hC
          (ae_isChartCompletable_of_frame_left_g7a hG8 hG7a hκ hκ4 hθ hSg (by linarith [min_le_right a₁ b₀]) hb₀
            hwt.1 hwt.2 Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂)
      · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ ?_
        filter_upwards [ae_noVisit_of_strips hwt fun ab hab =>
          ae_frameWeight_of_visit_left hκ hκ4 c.isPiecewiseConstantBoundaryData (hL ab hab).le (hcC ab hab)
            Q₀ H₀ hH Γ₂ U₂ h₂] with x hx using Or.inr hx
    · -- between the seeds: the G2a word, or no visit (Lemma 5.1)
      obtain ⟨a₂, ha₂, ha⟩ := exists_between_list_fst (w := 0) fun ab h => (hM ab h).1
      obtain ⟨b₁, hb₁, hb⟩ := exists_between_list_snd (w := w) fun ab h => (hM ab h).2
      set a₀ := min a₂ (w / 2) with ha₀def
      have ha₀ : 0 < a₀ := lt_min ha₂ (half_pos hw)
      have ha₀w : a₀ < w := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hw)
      have hab : ∀ ab ∈ S, a₀ < ab.1 ∧ (ab.2 : ℝ) < max b₁ a₀ := fun ab h =>
        ⟨lt_of_le_of_lt (min_le_left _ _) (ha ab h), lt_of_lt_of_le (hb ab h) (le_max_left _ _)⟩
      by_cases hadm : -sleLambda κ - θ₂ * QuantumZipper.chiC κ < C ∧ C < sleLambda κ - θ₁ * QuantumZipper.chiC κ
      · exact exists_ae_of_ref hc₁ hc₂ hm₁ hm₂ hSC hab hC
          (ae_isChartCompletable_of_mid_g7a hG2a hG7a hκ hκ4 hθ hSg ha₀ (le_max_right _ _) (max_lt hb₁ ha₀w) hadm
            Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂)
      · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ ?_
        filter_upwards [ae_noVisit_of_strips hadm fun ab hab => by
          filter_upwards [ae_admissible_of_visit' hκ hκ4 hθ c.isPiecewiseConstantBoundaryData (hM ab hab).1.le
            (hM ab hab).2.le (hcC ab hab) Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂] with x hx hv using hx (Or.inl hv)]
          with x hx using Or.inl hx
    · -- right of the first seed: the G8 frame, or no visit by the lower-angle flow
      obtain ⟨a₀, ha₀, ha⟩ := exists_between_list_fst hR
      obtain ⟨b₁, hb⟩ := exists_gt_list_snd S
      have hab : ∀ ab ∈ S, a₀ < ab.1 ∧ (ab.2 : ℝ) < max b₁ a₀ := fun ab h =>
        ⟨ha ab h, lt_of_lt_of_le (hb ab h) (le_max_left _ _)⟩
      by_cases hwt : -2 < Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) ∧
          Sec4.cumWeightRight κ (C + θ₁ * QuantumZipper.chiC κ) < κ / 2 - 2
      · exact exists_ae_of_ref hc₁ hc₂ hm₁ hm₂ hSC hab hC
          (ae_isChartCompletable_of_frame_g7a hG8 hG7a hκ hκ4 hθ hSg ha₀ (le_max_right _ _) hwt.1 hwt.2
            Q₀ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂)
      · refine exists_ae_of_noVisit hc₁ hc₂ hm₁ hm₂ ?_
        filter_upwards [ae_noVisit_of_strips hwt fun ab hab =>
          ae_frameWeight_of_visit_right hκ hκ4 c.isPiecewiseConstantBoundaryData (hR ab hab).le (hcC ab hab)
            Q₀ H₀ hH Γ₁ U₁ h₁] with x hx using Or.inl hx
  have hstrips : ∀ᵐ x ∂Q₀, ∀ S : List (ℚ × ℚ), StripCond c w S →
      ∃ k : ℕ, StripEventC S w k (encC (Γ₁ x)) (U₁ x) (encC (Γ₂ x)) (U₂ x) := by
    refine ae_all_iff.2 fun S => ?_
    by_cases hSC : StripCond c w S
    · obtain ⟨k, hk⟩ := key S hSC
      filter_upwards [hk] with x hx _ using ⟨k, hx⟩
    · exact Eventually.of_forall fun x h => absurd h hSC
  filter_upwards [hjump, hstrips] with x h1 h2
  exact realEventC_iff.2 ⟨h1, h2⟩

/-! ### Integration over the retained datum -/

/-- **`RetainedChartRealCompletionAtStatement` from the per-datum real completion event and the strengthened
retained-pair restart** (the proof of `RLC.retainedChartRealCompletionAtStatement_of_restart`, with its per-datum call
`RLC.ae_realEventC` replaced by the per-datum statement). -/
theorem retainedChartRealCompletionAtStatement_of_datum (hE : RealEventDatumStatement.{0})
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
    have hE' : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₁ p.2 0 = (p.1.2 : ℂ)} :=
      measurableSet_eq_fun ((hΓ₁m 0).comp measurable_snd)
        (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst))
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE')
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.1)
  have F3 : ∀ᵐ ω ∂P, ω ∈ M → Γ₂ (X ω) 0 = ((0 : ℝ) : ℂ) := by
    have hE' : MeasurableSet {p : (BoundaryWord × ℝ) × S | Γ₂ p.2 0 = ((0 : ℝ) : ℂ)} :=
      measurableSet_eq_fun ((hΓ₂m 0).comp measurable_snd) measurable_const
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE')
      (hker.mono fun c hc => Supp9.ae_apply_zero_of_isFlowLine hc.2.2.2)
  -- (3) a wrong side at the first tip kills the first continuation
  have F4 : ∀ᵐ ω ∂P, ω ∈ M → (β ω ∈ BadSeed κ θ₁ → U₁ (X ω) = 0) := by
    have hE' : MeasurableSet {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} := by
      have e : {p : (BoundaryWord × ℝ) × S | p.1 ∈ BadSeed κ θ₁ → U₁ p.2 = 0} =
          (Prod.fst ⁻¹' BadSeed κ θ₁)ᶜ ∪ {p | U₁ p.2 = 0} := by
        ext p; simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]; tauto
      rw [e]
      exact ((measurableSet_badSeed κ θ₁).preimage measurable_fst).compl.union
        (measurableSet_eq_fun (hU₁m.comp measurable_snd) measurable_const)
    refine ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE')
      (hker.mono fun c hc => ?_)
    by_cases hcb : c ∈ BadSeed κ θ₁
    · filter_upwards [ae_eq_zero_of_mem_badSeed hκ hcb hc.2.2.1] with s hs _ using hs
    · exact Eventually.of_forall fun s h' => absurd h' hcb
  -- (4) the chart paths stay in `ℍ̄` before their lifetimes
  have F6 : ∀ (Γ : S → ℝ≥0 → ℂ) (U : S → ℝ≥0∞), (∀ t, Measurable fun x => Γ x t) → Measurable U →
      (∀ᵐ c ∂(P.restrict M).map β, ∀ᵐ s ∂(K c), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ U s → 0 ≤ (Γ s t).im) →
      ∀ᵐ ω ∂P, ω ∈ M → ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U (X ω) → 0 ≤ (Γ (X ω) (dyad n k)).im := by
    intro Γ U hΓm hUm hae
    have hE' : MeasurableSet {p : (BoundaryWord × ℝ) × S |
        ∀ n k : ℕ, (dyad n k : ℝ≥0∞) < U p.2 → 0 ≤ (Γ p.2 (dyad n k)).im} :=
      measurableSet_setOfPred.mpr (Measurable.forall fun n => Measurable.forall fun k =>
        (measurableSet_setOfPred.mp (measurableSet_lt measurable_const (hUm.comp measurable_snd))).imp
          (measurableSet_setOfPred.mp (measurableSet_le measurable_const
            (Complex.measurable_im.comp ((hΓm (dyad n k)).comp measurable_snd)))))
    exact ae_mem_of_ae_ae_compProd_of_uMeasurable hM hβ hX hlaw (LQGMetric.UMeasurableSet.of_measurableSet hE')
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
    · filter_upwards [hE κ θ₁ θ₂ hκ hκ4 hθ c hcg (K c) H₀ hc.2.1 Γ₁ Γ₂ U₁ U₂ hc.2.2.1 hc.2.2.2]
        with s hs _ using hs
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
  have hE' := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, -, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩, hword,
    huw⟩ := hω hord
  have hg := hd.good ω (RetData.E_subset_G hE')
  obtain ⟨-, hC⟩ := hd.isRetChart hE'
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

/-- **`RetainedChartRealCompletionAtStatement` from G2a, Corollary G7a, G8, Theorems 1.2 (param), 1.3 and the
strengthened two-tip input** (R43/R48: for Theorem 1.5 only). -/
theorem retainedChartRealCompletionAtStatement_of_g7a_param (hG2a : G2aReferenceStatement.{0})
    (hG7a : G7aChartStatement.{0}) (hG8 : G8FrameStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetUntouchedStatement.{u}) :
    RetainedChartRealCompletionAtStatement.{u} :=
  retainedChartRealCompletionAtStatement_of_datum (realEventDatumStatement_of_g7a hG2a hG7a hG8)
    (retainedPairRestartUntouchedStatement_of_param h12p h13 hD)

end RLC

end InteractingSLE
