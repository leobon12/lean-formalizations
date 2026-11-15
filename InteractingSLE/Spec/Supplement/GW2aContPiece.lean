/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContDefs

/-!
# Lemma GW2a for every program: a measurable event for the containment of one launched piece

Packet PROVE-GW2AC. The landed `GW2Later.exists_measurable_piece_event` (PROVE-T14-BR6) treats the GW2 flow programs,
whose launch charts are the success charts `succChart`. For an arbitrary program (boundary continuations, launches from
thresholds and connector points) the launch chart is the chart of the run, whose inverse at a measurable point of `ℍ`
is measurable on an event of regular pieces (`WalkLaw.exists_measurable_tipApprox`, PROVE-T14-WALKLAW3).

* **`exists_measurable_piece_event_run`**: for a staged history with measurable drivers regular at every sample whose
  launched pieces are almost surely regular (ruling R51), there is a measurable event `A` that is almost sure under the
  regular conditional law given the retained past at almost every sample where the launch datum
  `GW2Later.HasLaunchPair` holds, and on which the piece launched at `k` lies in the completed counterflow range.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aCont

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- Whether instruction `k` launches depends only on the state before it. -/
theorem launch_none_iff_of_run_eq {spec : ExplSpec} {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (h : ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none ↔
      (ExplState.run κ b jumps spec D' (k + 1)).2.2.2.1 k = none := by
  have e : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 = (ExplState.run κ b jumps spec D' (k + 1)).2.2.2.1 := by
    rw [run_succ, run_succ, h]
    cases spec.2.2[k]? with
    | none => rfl
    | some a => exact launches_step_indep spec.2.1 D D' _ (a, k)
  rw [e]

/-- The stopped driver of a launched piece, read by `tipApprox`, is `stopR` of the piece at its stop. -/
theorem tipApprox_eq_stopR (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) (τ : ℝ≥0) (n : ℕ) :
    WalkLaw.tipApprox κ b jumps spec D j τ n = (ExplState.run κ b jumps spec D j).2.2.2.2.1.2.1
      (fwdMapInv (stopR (D j).1 (pieceStop spec D j)) (τ : ℝ) (yPt n)) := rfl

/-- **A measurable event for the containment of the piece launched at `k`** (every program; measurable drivers regular
at every sample; regular pieces almost surely, ruling R51). Named inputs: GB6's restart law, GW0's forward implication
and Theorem 1.3 (those of `GW2Later.ae_condExpKernel_piece_subset_of_pair`). -/
theorem exists_measurable_piece_event_run (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ)
    (hθ : ∀ (θ : ℝ) (t : ℝ≥0∞), spec.2.2[k]? = some (Sum.inl (θ, t)) → θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∃ A : Set Ω, MeasurableSet A ∧
      (∀ᵐ ω₀ ∂P, HasLaunchPair κ b jumps P h W' spec E k ω₀ →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ A) ∧
      ∀ ω ∈ A, ∀ (c : Chart) (θ' : ℝ),
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ') →
        c.tipSet (stoppedDriver spec (fun j => E j ω) k) (pieceStop spec (fun j => E j ω) k) ⊆
          counterflowCompletedRange (fun t => W' t ω) := by
  classical
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hS.2.1 k
  have hEm : ∀ j, Measurable (E j) := hS.1
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hLm : MeasurableSet L := ((runMeasStatement κ b jumps hb spec E hEm hreg) k).1
  -- the counterflow
  obtain ⟨b', J', h', -, -, hfl'⟩ := id hcf
  have hk16 : 0 < 16 / κ := by positivity
  obtain ⟨h'', 𝓕, VL', VR', B', -, hC'⟩ := id hfl'
  have hAd : AdaptedBefore 𝓕 ζ' W' := hC'.1.2.1
  set K : ℝ≥0 → Ω → ℝ := fun t ω => if (t : ℝ≥0∞) < ζ' ω then W' t ω else 0 with hKdef
  have hKm : ∀ t, Measurable (K t) := fun t => (WholeField.measurable_killedVal hAd t).mono (𝓕.le t) le_rfl
  -- the good set
  set γ := GW2aSingle.chosenTrace W' ζ' with hγdef
  have hgood : ∀ᵐ ω ∂P, (∀ (j : ℕ) (c : Chart) (θ' : ℝ),
        (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
        GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)) ∧ ζ' ω = ⊤ ∧
      W' 0 ω = 0 ∧ Continuous (fun t => W' t ω) ∧ IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop := by
    filter_upwards [hR.ae_pieceRegular, hζ', Supp8.GB6.ae_driver_zero_continuousOn hfl',
      GW2aSingle.ae_chosenTrace hT13 hk16 hfl'] with ω hrg hζω hdω hγω
    rw [hζω] at hdω hγω
    have hWc : Continuous fun t => W' t ω := by
      have hc := hdω.2
      simp only [ENNReal.coe_lt_top, ofPred_true] at hc
      exact continuousOn_univ.1 hc
    exact ⟨hrg, hζω, hdω.1, hWc, hγω.1, hγω.2 rfl⟩
  obtain ⟨G, hGae, hGm, hGp⟩ := hgood.exists_measurable_mem
  have hMreg : ∀ ω ∈ G, ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2) := fun ω hω => (hGp ω hω).1
  set Sp : Ω → ℝ≥0∞ := fun ω => pieceStop spec (fun j => E j ω) k with hSpdef
  have hSpm : Measurable Sp := measurable_const.min (measurable_snd.comp (hEm k))
  -- the measurable approximants
  have hY : ∀ (q : ℚ) (n : ℕ), ∃ Y : Ω → ℂ, Measurable Y ∧ ∀ ω ∈ G,
      (ExplState.run κ b jumps spec (fun i => E i ω) (k + 1)).2.2.2.1 k ≠ none →
        WalkLaw.tipApprox κ b jumps spec (fun i => E i ω) k ((q : ℝ).toNNReal) n = Y ω := fun q n =>
    WalkLaw.exists_measurable_tipApprox hb spec hEm hreg hGm hMreg k _ n
  choose Y hYm hYeq using hY
  set A : Set Ω := {ω | ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ Sp ω →
    Tendsto (fun n => infEDist (Y q n ω) (cfDense fun t => K t ω)) atTop (𝓝 0)} with hAdef
  have hAm : MeasurableSet A := by
    have e : A = ⋂ q : ℚ, ({ω | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ Sp ω}ᶜ ∪
        {ω | Tendsto (fun n => infEDist (Y q n ω) (cfDense fun t => K t ω)) atTop (𝓝 0)}) := by
      ext ω
      simp only [hAdef, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [e]
    refine MeasurableSet.iInter fun q => ((measurableSet_le measurable_const hSpm).compl).union ?_
    exact measurableSet_tendsto (𝓝 0) fun n => measurable_infEDist_cfDense hKm (hYm q n)
  -- the counterflow range from the dense set on `G`
  have hK_eq : ∀ ω ∈ G, (fun t => K t ω) = fun t => W' t ω := fun ω hω => by
    funext t
    simp only [hKdef, (hGp ω hω).2.1, ENNReal.coe_lt_top, ite_true]
  have hRT : ∀ ω ∈ G, closure (cfDense fun t => K t ω) = counterflowCompletedRange fun t => W' t ω :=
    fun ω hω => by
      rw [hK_eq ω hω]
      obtain ⟨-, -, h0, hc, hγ', htr⟩ := hGp ω hω
      exact closure_cfDense_eq hγ' hc h0 htr
  have hYM : ∀ ω ∈ G, (ExplState.run κ b jumps spec (fun i => E i ω) (k + 1)).2.2.2.1 k ≠ none →
      ∀ (q : ℚ) (n : ℕ), Y q n ω = (ExplState.run κ b jumps spec (fun i => E i ω) k).2.2.2.2.1.2.1
        (fwdMapInv (stopR (E k ω).1 (Sp ω)) (((q : ℝ).toNNReal : ℝ≥0) : ℝ) (yPt n)) := fun ω hω hl q n => by
    rw [← hYeq q n ω hω hl, tipApprox_eq_stopR]
  have hpm : Measurable[pastSigma κ b jumps spec E k] (Exist.Staged.pastMap κ b jumps spec E k) := by
    intro s hs
    rw [Exist.Staged.pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  refine ⟨G ∩ (Lᶜ ∪ A), hGm.inter (hLm.compl.union hAm), ?_, ?_⟩
  · filter_upwards [ae_condExpKernel_piece_subset_of_pair hGB6 hGW0 hT13 hκ hκ4 hcf hζ' hS hR k hθ,
      Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hGae,
      ae_ae_run_eq runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) (k := k) (P := P)]
      with ω₀ hA2 hGk hrunk hp0
    by_cases hω₀L : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = none
    · filter_upwards [hGk, hrunk] with ω hωG hrunω
      exact ⟨hωG, Or.inl fun h => h ((launch_none_iff_of_run_eq hrunω).2 hω₀L)⟩
    obtain ⟨⟨c₀, θ₀⟩, hl₀⟩ := Option.ne_none_iff_exists'.1 hω₀L
    have hc₀ := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω₀) hl₀).2.2
    filter_upwards [hGk, hrunk, hA2 hp0 c₀ θ₀ hl₀] with ω hωG hrunω hsub
    refine ⟨hωG, ?_⟩
    have hωL : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := fun h0 =>
      hω₀L ((launch_none_iff_of_run_eq hrunω).1 h0)
    right
    obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hωL
    have hc := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hl).2.2
    intro q hq
    obtain ⟨f, -, hf, -⟩ := hasProperBdryExt_of_launch (hMreg ω hωG) hl
    obtain ⟨hw0, hw, α, hα, -⟩ := hMreg ω hωG k _ _ hl
    have hsub' : c.tipSet (fun r : ℝ≥0 => (E k ω).1 (min (r : ℝ≥0∞) (Sp ω)).toNNReal) (Sp ω) ⊆
        counterflowCompletedRange fun t => W' t ω := by
      rw [hc, hrunω, ← hc₀]
      exact hsub
    have h1 := tendsto_infEDist_of_tipSet_subset hf hα hw hw0 (hRT ω hωG) hsub' hq
    refine h1.congr fun n => ?_
    rw [hYM ω hωG hωL q n, hc]
    rfl
  · intro ω hω c θ' hl
    obtain ⟨hωG, hωLA⟩ := hω
    have hωL : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
      rw [hl]; exact Option.some_ne_none _
    have hωA : ω ∈ A := hωLA.resolve_left (not_not.2 hωL)
    have hc := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω) hl).2.2
    obtain ⟨f, -, hf, -⟩ := hasProperBdryExt_of_launch (hMreg ω hωG) hl
    obtain ⟨hw0, hw, α, hα, -⟩ := hMreg ω hωG k _ _ hl
    refine tipSet_subset_of_tendsto_infEDist hf hα hw hw0 (hRT ω hωG) fun q hq => ?_
    refine (hωA q hq).congr fun n => ?_
    rw [hYM ω hωG hωL q n, hc]
    rfl

end GW2aCont

end Theorem14

end InteractingSLE
