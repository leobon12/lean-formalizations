/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.QSchedStage

/-!
# Lemma 5.7 along a finite extreme-angle schedule: induction on the number of switches

Packet PROVE-QSCHED. For a staged history `E` of a schedule `s` (regular at every sample, all lifetimes infinite)
of a field `h` whose word has `ExtremeHeights`, and a centred counterflow `(W, ζ, γ)` of `h` with infinite lifetime:

* **`stage_cfStage`**: along the nested conditional laws, the world before piece `k` carries the conditional
  counterflow of the stage field, read in the composed chart of the earlier pieces (`CfStage`): at `k = 0` it is
  the given counterflow; one switch is `ae_cfStage_succ` with the restart law at the switch
  (`CounterflowGivenPrefix44Statement`), the stage witnesses, the tower of conditional laws and the record field;
* **`stage_firstHit`**: for `0 < q′ ≤ d k`, the physical counterflow first contacts the physical prefix
  `Γ((0, τ k + q′])` at its tip, along the nested conditional laws (Lemma 4.7 in the world before piece `k`,
  `ae_firstHit_of_cfStage`, pulled back through the chart, `isFirstHitQ_pathTrace`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open scoped NNReal ENNReal Real
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.QSched

open WangWu (negInv)
open Prop411Q (IsFirstHitQ)
open Sec7.Lemma71I (realPath)
open Exist Exist.Staged Exist.StagedLaw
open Restart (BoundaryWord)
open Prop513TreeExtract Prop513Schedule

section Induct

variable {κ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {c : BoundaryWord} {s : Schedule}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}

/-- The almost-sure facts at the world before piece `k`. -/
theorem ae_stage_facts (hκ : 0 < κ) (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length) :
    ∀ᵐ ω₀ ∂P,
      IsGFFWithBoundaryData (condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀)
        (stageField κ c s E h k) (stageWord κ c s E k ω₀).fn (stageWord κ c s E k ω₀).jumps ∧
      (∃ h' : Ω → DistOn upperHalfPlaneOpens,
        IsFlowLineDriver κ (stageWord κ c s E k ω₀).fn (stageWord κ c s E k ω₀).jumps (instrAngle (scheduleSpec s) k)
          (condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀) h' (fun t ω => (E k ω).1 t)
          (fun ω => (E k ω).2) ∧
        stageField κ c s E h k =ᵐ[condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀] h') ∧
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀),
        ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤ := by
  have hW := isStageWitness_stage hκ hh hE hr hTop k hk.le
  filter_upwards [hTop, hW.2.2.2, ae_isFlowLineDriver_stage_eq hκ c.isPiecewiseConstantBoundaryData hh hE hr hW,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 k) hTop] with ω₀ htop hG hD hTK
  have hl := launch_of_previous_top (κ := κ) (b := c.fn) (J := c.jumps) s (fun j => E j ω₀) hk
    fun j hj => htop j (by omega)
  exact ⟨hG hl, hD hl, hTK⟩

/-- **The conditional counterflow at every stage** (induction on the number of switches). -/
theorem stage_cfStage (hcg : CounterflowGivenPrefix44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hc : ExtremeHeights κ c) (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤)
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) :
    ∀ k, k < (scheduleSpec s).2.2.length →
      ∀ᶠ ω₀ in stageFilter P (pastSigma κ c.fn c.jumps (scheduleSpec s) E) k,
        CfStage (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) κ P (stageField κ c s E h k) (chartInv E s k) γ
          (0 < k) ω₀
  | 0, _ => by
    change ∀ᵐ ω₀ ∂P, _
    refine Eventually.of_forall fun ω₀ => ?_
    have hQ : condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E 0) ω₀ = P := by
      rw [pastSigma_zero]
      exact Theorem14.GW1.condExpKernel_bot_apply P ω₀
    unfold CfStage
    rw [hQ]
    refine ⟨h, W, ζ, γ, hh.1, EventuallyEq.refl _ _, hcf, hζ, ?_⟩
    filter_upwards [hγ] with ω hω
    exact ⟨hω, id, continuous_id, strictMono_id, rfl, fun u _ => ⟨fun h0 => absurd h0 (lt_irrefl 0), rfl⟩⟩
  | k + 1, hk => by
    have ih := stage_cfStage hcg hκ hκ4 hc hh hE hr hTop hcf hζ hγ k (by omega)
    rw [eventually_stageFilter_succ]
    have hfacts := ae_stage_facts hκ hh hE hr hTop (k := k) (by omega)
    have htower := ae_tower_stage hE hr hTop (k := k) (by omega)
    have hnext := ae_stageField_succ hE hTop (k := k) (by omega)
    have hall : ∀ᵐ ω₀ ∂P, _ := hfacts.and (htower.and hnext)
    filter_upwards [ih, stageFilter_of_ae hE.2.1 k hall] with ω₀ hst hf
    obtain ⟨⟨hG, ⟨h', hD, hYh'⟩, hTK⟩, ht, hn⟩ := hf
    exact ae_cfStage_succ hcg hκ hκ4 hst (extremeHeights_stageWord hκ hκ4 hc k (by omega) ω₀) hG
      (instrAngle_extreme s (by omega)) (hE.1 k) (hr k) (hTK.mono fun ω hω => hω k (by omega)) hD hYh' (dur s k)
      ht hn (Eventually.of_forall fun _ _ _ => rfl)

/-- **The physical first contact during piece `k`, along the nested conditional laws.** -/
theorem stage_firstHit (h47 : Prop411Q.Lemma47QHitStatement.{u}) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hcg : CounterflowGivenPrefix44Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hc : ExtremeHeights κ c) (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E) (hr : ∀ j ω, IsRegularDriver (E j ω))
    (hTop : ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤) (hgood : ∀ᵐ ω ∂P, GoodPieces E s ω)
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) {k : ℕ} (hk : k < (scheduleSpec s).2.2.length)
    {q' : ℝ} (hq' : 0 < q') (hqd : q' ≤ dur s k) :
    ∀ᶠ ω₀ in stageFilter P (pastSigma κ c.fn c.jumps (scheduleSpec s) E) k,
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀),
        IsFirstHitQ (realPath (pathTrace E s 0 ω)) (fun t : ℝ => γ ω t.toNNReal) ((tau s k : ℝ) + q') := by
  have hk' : k < (scheduleList s).length := by rwa [← length_scheduleSpec]
  have hst := stage_cfStage hcg hκ hκ4 hc hh hE hr hTop hcf hζ hγ k hk
  have hgK := Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 k) hgood
  have hall : ∀ᵐ ω₀ ∂P, _ := (ae_stage_facts hκ hh hE hr hTop hk).and hgK
  filter_upwards [hst, stageFilter_of_ae hE.2.1 k hall] with ω₀ hst₀ hf
  obtain ⟨⟨hG, ⟨h', hD, hYh'⟩, hTK⟩, hgω⟩ := hf
  have hΓ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ c.fn c.jumps (scheduleSpec s) E k) ω₀),
      IsGeneratingTrace (E k ω).1 (E k ω).2 (fun t => LP.traceAt t (E k ω).1) := by
    filter_upwards [hTK, hgω] with ω htop hg
    rw [htop k hk]
    exact (piece_trace hg hk').1
  have hfh := ae_firstHit_of_cfStage h47 href hκ hκ4 hst₀ (extremeHeights_stageWord hκ hκ4 hc k hk.le ω₀) hG
    (instrAngle_extreme s hk) hD hYh' hΓ
  filter_upwards [hfh, hgω] with ω hω hg
  obtain ⟨η₂, ℓ, hη₂, hℓc, hℓm, hℓ0, hrel, hfirst⟩ := hω
  exact isFirstHitQ_pathTrace hg hk' hη₂ hℓc hℓm hℓ0 hrel hfirst hq' hqd

end Induct

end InteractingSLE.Sec5.QSched
