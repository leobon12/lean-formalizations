/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2LaterMeas
import InteractingSLE.Spec.Coupling.WholeField8Trace

/-!
# GW2a's later pieces: from the conditional law given the retained past to `P`

Packet PROVE-T14-BR6. For a GW2 flow program (a schedule program: ordinary pieces only, no switch after a threshold) and
a staged history whose launched pieces are regular (ruling R51), the conditional step
`GW2Later.ae_condExpKernel_piece_subset_of_pair` is passed from the regular conditional law given the retained past to
`P` (`ae_piece_subset_of_pair_flow`).

The containment event is replaced by a measurable event on a measurable good set of full measure (regular launched
pieces, a continuous transient counterflow trace): the distances of the chart images `c(F_q(i y_n))` of the piece's
inverse Loewner map at rational times `q` to the countable dense set `cfDense` of the completed counterflow range tend
to `0` (`GW2LaterMeas`). Under the conditional law at `ω₀` the retained past is that of `ω₀`, so the launch chart is
`ω₀`'s (equal records of regular pieces give equal charts, `succChart_eq_of_recOf_eq`), and the conditional step gives
the measurable event kernel-almost surely; the measurable event is then integrated back.
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

namespace GW2Later

open CounterflowRange GW2Schedule GW2aMulti Exist.StagedLaw

section Transfer

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- A kernel-almost-sure measurable event on a past event is `P`-almost sure there. -/
theorem ae_of_ae_condExpKernel_on' (h𝒢 : 𝒢 ≤ mΩ) {L A : Set Ω} (hL : MeasurableSet[𝒢] L) (hA : MeasurableSet A)
    (h : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ A) : ∀ᵐ ω ∂P, ω ∈ L → ω ∈ A := by
  have hp : MeasurableSet (Lᶜ ∪ A) := (h𝒢 _ hL).compl.union hA
  have h1 : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ Lᶜ ∪ A := by
    filter_upwards [h, Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hL.compl] with ω₀ h0 hc
    by_cases hω₀ : ω₀ ∈ L
    · exact (h0 hω₀).mono fun ω hω => Or.inr hω
    · exact (hc hω₀).mono fun ω hω => Or.inl hω
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝒢 hp h1] with ω hω hωL
  rcases hω with h' | h'
  · exact absurd hωL h'
  · exact h'

end Transfer

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- The own time of a flow-program instruction is its scheduled time. -/
theorem instrTime_eq_of_isFlowProg {spec : ExplSpec} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}
    (hprog : IsFlowProg spec.2.2 θ Δ) {j : ℕ} (hj : j < spec.2.2.length) : instrTime spec j = Δ j := by
  unfold instrTime
  rw [hprog j hj]

open Classical in
/-- The stopped driver of piece `k` on the event `M` (`0` off `M`), with stop `S`. -/
def stopProc (M : Set Ω) (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (S : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ M then (e ω).1 (min (t : ℝ≥0∞) (S ω)).toNNReal else 0

omit [StandardBorelSpace Ω] in
theorem measurable_stopProc {M : Set Ω} (hM : MeasurableSet M) {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (he : Measurable e)
    {S : Ω → ℝ≥0∞} (hS : Measurable S) (hSt : ∀ ω ∈ M, S ω ≠ ⊤)
    (hc : ∀ ω ∈ M, ContinuousOn (e ω).1 {t | (t : ℝ≥0∞) ≤ S ω}) (t : ℝ≥0) :
    Measurable (stopProc M e S t) := by
  classical
  have hC := Restart.measurable_piecewise_eval (G := M) hM (f := fun ω r => (((e ω).1 r : ℝ) : ℂ))
    (fun r => Complex.measurable_ofReal.comp ((measurable_pi_apply r).comp (measurable_fst.comp he)))
    (s := fun ω => (min (t : ℝ≥0∞) (S ω)).toNNReal)
    ((measurable_const.min hS).ennreal_toNNReal)
    (fun ω hω => (Complex.continuous_ofReal.comp_continuousOn ((hc ω hω).mono fun r (hr : r ≤ _) => by
      show (r : ℝ≥0∞) ≤ S ω
      refine le_trans (ENNReal.coe_le_coe.2 hr) ?_
      rw [ENNReal.coe_toNNReal (ne_top_of_le_ne_top (hSt ω hω) (min_le_right _ _))]
      exact min_le_right _ _)))
  have heq : stopProc M e S t = fun ω => (if ω ∈ M then (((e ω).1 (min (t : ℝ≥0∞) (S ω)).toNNReal : ℝ) : ℂ)
      else 0).re := by
    funext ω
    unfold stopProc
    split_ifs <;> simp
  rw [heq]
  exact Complex.measurable_re.comp hC

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
theorem continuous_stopProc {M : Set Ω} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {S : Ω → ℝ≥0∞} (hSt : ∀ ω ∈ M, S ω ≠ ⊤)
    (hc : ∀ ω ∈ M, ContinuousOn (e ω).1 {t | (t : ℝ≥0∞) ≤ S ω}) (ω : Ω) :
    Continuous fun t => stopProc M e S t ω := by
  classical
  unfold stopProc
  by_cases hω : ω ∈ M
  · simp only [hω, ite_true]
    exact continuous_stopAt (hSt ω hω) (hc ω hω)
  · simp only [hω, ite_false]
    exact continuous_const

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
theorem stopProc_zero {M : Set Ω} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {S : Ω → ℝ≥0∞} (h0 : ∀ ω ∈ M, (e ω).1 0 = 0)
    (ω : Ω) : stopProc M e S 0 ω = 0 := by
  classical
  unfold stopProc
  by_cases hω : ω ∈ M
  · simp only [hω, ite_true, ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]
    exact h0 ω hω
  · simp [hω]

omit [MeasurableSpace Ω] [StandardBorelSpace Ω] in
theorem stopProc_eq {M : Set Ω} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {S : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ M) :
    (fun x : ℝ => stopProc M e S x.toNNReal ω) = stopR (e ω).1 (S ω) := by
  classical
  funext x
  simp only [stopProc, hω, ite_true, stopR]

/-- **A measurable event for the containment of the piece launched at `k`** (GW2 flow programs, regular pieces).
There is a measurable event `A` such that (1) at almost every sample `ω₀` at which the first `k` pieces were
successful and the conditional counterflow pair is available, `A` is almost sure under the conditional law given the
retained past, and (2) on `A` the piece launched at `k`, read through its launch chart, lies in the completed
counterflow range. Named inputs: GB6's restart law, GW0's forward implication and Theorem 1.3. -/
theorem exists_measurable_piece_event (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞} (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) {k : ℕ} (hk : k < spec.2.2.length)
    (hθ : θ k ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ∃ A : Set Ω, MeasurableSet A ∧
      (∀ᵐ ω₀ ∂P, AllSucc Δ (fun j => E j ω₀) k → HasLaunchPair κ b jumps P h W' spec E k ω₀ →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ A) ∧
      ∀ ω ∈ A, ∀ (c : Chart) (θ' : ℝ),
        (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ') →
        c.tipSet (stoppedDriver spec (fun j => E j ω) k) (pieceStop spec (fun j => E j ω) k) ⊆
          counterflowCompletedRange (fun t => W' t ω) := by
  classical
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hS.2.1 k
  have hEm : ∀ j, Measurable (E j) := hS.1
  -- the launch events and charts of a GW2 flow program
  set L : Set Ω := {ω | AllSucc Δ (fun j => E j ω) k} with hLdef
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec E k] L := measurableSet_allSucc hgw hprog hΔ E hk.le
  have hLm : MeasurableSet L := h𝒢 _ hL𝒢
  have hlaunch : ∀ (j : ℕ) (hj : j < spec.2.2.length) (ω : Ω), AllSucc Δ (fun i => E i ω) j →
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j =
        some (succChart spec.1 Δ (fun i => E i ω) j, θ j) := fun j hj ω hs =>
    (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω) hj).1 hs
  have hinstr : ∀ j < spec.2.2.length, instrTime spec j = Δ j := fun j hj => instrTime_eq_of_isFlowProg hprog hj
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
      GW2aSingle.ae_chosenTrace hT13 hk16 hfl'] with ω hreg hζω hdω hγω
    rw [hζω] at hdω hγω
    have hWc : Continuous fun t => W' t ω := by
      have hc := hdω.2
      simp only [ENNReal.coe_lt_top, ofPred_true] at hc
      exact continuousOn_univ.1 hc
    exact ⟨hreg, hζω, hdω.1, hWc, hγω.1, hγω.2 rfl⟩
  obtain ⟨G, hGae, hGm, hGp⟩ := hgood.exists_measurable_mem
  set M : Set Ω := L ∩ G with hMdef
  have hMm : MeasurableSet M := hLm.inter hGm
  -- regularity of the earlier pieces and of piece `k` on `M`
  have hregj : ∀ ω ∈ L ∩ G, ∀ j < k, (E j ω).1 0 = 0 ∧ ContinuousOn (E j ω).1 {t | (t : ℝ≥0∞) ≤ Δ j} := by
    intro ω hω j hj
    have hjl : j < spec.2.2.length := lt_trans hj hk
    have hsj : AllSucc Δ (fun i => E i ω) j := hω.1.mono hj.le
    have hpr := (hGp ω hω.2).1 j _ _ (hlaunch j hjl ω hsj)
    rw [hinstr j hjl, min_eq_left (hω.1 j hj).le] at hpr
    exact ⟨hpr.1, hpr.2.1⟩
  set Sp : Ω → ℝ≥0∞ := fun ω => pieceStop spec (fun j => E j ω) k with hSpdef
  have hSpm : Measurable Sp := measurable_const.min (measurable_snd.comp (hEm k))
  have hSpt : ∀ ω, Sp ω ≠ ⊤ := fun ω => by
    show min (instrTime spec k) (E k ω).2 ≠ ⊤
    rw [hinstr k hk]
    exact ne_top_of_le_ne_top (hΔ k) (min_le_left _ _)
  have hregk : ∀ ω ∈ L ∩ G, GW1P.PieceRegular (E k ω).1 (Sp ω) := fun ω hω =>
    (hGp ω hω.2).1 k _ _ (hlaunch k hk ω hω.1)
  -- the measurable approximants
  set B : ℝ≥0 → Ω → ℝ := stopProc M (E k) Sp with hBdef
  have hBm : ∀ t, Measurable (B t) :=
    measurable_stopProc hMm (hEm k) hSpm (fun ω _ => hSpt ω) fun ω hω => (hregk ω hω).2.1
  have hBc : ∀ ω, Continuous fun t => B t ω :=
    continuous_stopProc (fun ω _ => hSpt ω) fun ω hω => (hregk ω hω).2.1
  have hB0 : ∀ ω, B 0 ω = 0 := stopProc_zero fun ω hω => (hregk ω hω).1
  set Z : ℚ → ℕ → Ω → ℂ := fun q n ω =>
    fwdMapInv (fun x : ℝ => B x.toNNReal ω) (((q : ℝ).toNNReal : ℝ≥0) : ℝ) (yPt n) with hZdef
  have hZm : ∀ q n, Measurable (Z q n) := fun q n =>
    measurable_fwdMapInv_apply hBm hBc hB0 (NNReal.coe_nonneg _) ⟨yPt n, yPt_mem_H n⟩
  have hZH : ∀ q n ω, Z q n ω ∈ H := fun q n ω =>
    QuantumZipper.RS.fwdMapInv_mem_H ((hBc ω).comp continuous_real_toNNReal) (by simpa using hB0 ω)
      (NNReal.coe_nonneg _) (yPt_mem_H n)
  have hY : ∀ q n, ∃ Y : Ω → ℂ, Measurable Y ∧
      ∀ ω ∈ M, (succChart spec.1 Δ (fun j => E j ω) k).2.1 (Z q n ω) = Y ω := fun q n =>
    exists_measurable_succChart_inv spec.1 hΔ hEm hMm k (fun ω hω => hω.1) hregj (hZm q n) (hZH q n)
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
      obtain ⟨-, -, h0, hc, hγ, htr⟩ := hGp ω hω
      exact closure_cfDense_eq hγ hc h0 htr
  -- the launch chart has boundary limits
  have hext : ∀ ω ∈ M, GW1P.HasProperBdryExt (succChart spec.1 Δ (fun j => E j ω) k) := fun ω hω =>
    hasProperBdryExt_of_launch (hGp ω hω.2).1 (hlaunch k hk ω hω.1)
  have hYM : ∀ ω ∈ M, ∀ (q : ℚ) (n : ℕ), Y q n ω = (succChart spec.1 Δ (fun j => E j ω) k).2.1
      (fwdMapInv (stopR (E k ω).1 (Sp ω)) (((q : ℝ).toNNReal : ℝ≥0) : ℝ) (yPt n)) := fun ω hω q n => by
    rw [← hYeq q n ω hω]
    simp only [hZdef, hBdef, stopProc_eq hω]
  -- the kernel step
  have hθk : ∀ (θ' : ℝ) (t : ℝ≥0∞), spec.2.2[k]? = some (Sum.inl (θ', t)) →
      θ' ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro θ' t h1
    rw [hprog k hk] at h1
    simp only [Option.some.injEq, Sum.inl.injEq, Prod.mk.injEq] at h1
    rw [← h1.1]
    exact hθ
  have hpm : Measurable[pastSigma κ b jumps spec E k] (Exist.Staged.pastMap κ b jumps spec E k) := by
    intro s hs
    rw [Exist.Staged.pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  refine ⟨G ∩ A, hGm.inter hAm, ?_, ?_⟩
  · filter_upwards [ae_condExpKernel_piece_subset_of_pair hGB6 hGW0 hT13 hκ hκ4 hcf hζ' hS hR k hθk,
      Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hGae, Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 hpm, hGae]
      with ω₀ hA2 hGk hpmk hω₀G hω₀L hp0
    filter_upwards [hA2 hp0 _ _ (hlaunch k hk ω₀ hω₀L), hGk, hpmk] with ω hsub hωG hpmω
    have hωL : ω ∈ L := by
      show AllSucc Δ (fun j => E j ω) k
      rw [allSucc_iff_flags hgw hprog hΔ E hk.le ω, hpmω]
      exact (allSucc_iff_flags hgw hprog hΔ E hk.le ω₀).1 hω₀L
    have hωM : ω ∈ M := ⟨hωL, hωG⟩
    have hchart : succChart spec.1 Δ (fun j => E j ω) k = succChart spec.1 Δ (fun j => E j ω₀) k := by
      refine succChart_eq_of_recOf_eq spec.1 hΔ k hωL hω₀L (fun j hj => (hregj ω hωM j hj).2)
        (fun j hj => (hregj ω₀ ⟨hω₀L, hω₀G⟩ j hj).2) fun j hj => ?_
      have h1 := congrFun hpmω ⟨j, hj⟩
      rw [pastMap_of_allSucc hgw hprog hΔ E hk.le hωL, pastMap_of_allSucc hgw hprog hΔ E hk.le hω₀L] at h1
      exact h1
    refine ⟨hωG, fun q hq => ?_⟩
    obtain ⟨f, -, hf, -⟩ := hext ω hωM
    obtain ⟨hw0, hw, α, hα, -⟩ := hregk ω hωM
    have hsub' : (succChart spec.1 Δ (fun j => E j ω) k).tipSet
        (fun r : ℝ≥0 => (E k ω).1 (min (r : ℝ≥0∞) (Sp ω)).toNNReal) (Sp ω) ⊆
          counterflowCompletedRange fun t => W' t ω := by
      rw [hchart]
      exact hsub
    have h1 := tendsto_infEDist_of_tipSet_subset hf hα hw hw0 (hRT ω hωG) hsub' hq
    refine h1.congr fun n => ?_
    rw [hYM ω hωM q n]
  · intro ω hω c θ' hl
    have hωL : ω ∈ L := by
      by_contra hns
      rw [(launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω) hk).2 hns] at hl
      exact absurd hl (by simp)
    obtain ⟨hωG, hωA⟩ := hω
    have hωM : ω ∈ M := ⟨hωL, hωG⟩
    rw [hlaunch k hk ω hωL] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    rw [← hl.1]
    obtain ⟨f, -, hf, -⟩ := hext ω hωM
    obtain ⟨hw0, hw, α, hα, -⟩ := hregk ω hωM
    refine tipSet_subset_of_tendsto_infEDist hf hα hw hw0 (hRT ω hωG) fun q hq => ?_
    refine (hωA q hq).congr fun n => ?_
    rw [hYM ω hωM q n]

/-- **GW2a's step for the piece launched at `k`, passed to `P`** (GW2 flow programs). For a staged history of a GW2
flow program whose launched pieces are regular (ruling R51), if the conditional counterflow pair (`HasLaunchPair`) is
available at the launch of instruction `k` almost surely on a past event `F`, then almost surely on `F` the piece
launched at `k`, read through its launch chart, lies in the completed counterflow range. Named inputs: GB6's restart
law, GW0's forward implication and Theorem 1.3 (those of `GW2aPiece.ae_condExpKernel_piece_subset`). -/
theorem ae_piece_subset_of_pair_flow (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞} (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) {k : ℕ} (hk : k < spec.2.2.length)
    (hθ : θ k ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {F : Set Ω}
    (hF : MeasurableSet[pastSigma κ b jumps spec E k] F)
    (hpair : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → HasLaunchPair κ b jumps P h W' spec E k ω₀) :
    ∀ᵐ ω ∂P, ω ∈ F → ∀ (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ') →
      c.tipSet (stoppedDriver spec (fun j => E j ω) k) (pieceStop spec (fun j => E j ω) k) ⊆
        counterflowCompletedRange (fun t => W' t ω) := by
  obtain ⟨A, hAm, hker, hpath⟩ := exists_measurable_piece_event hGB6 hGW0 hT13 hκ hκ4 hcf hζ' hgw hprog hΔ hS hR
    hk hθ
  have hL𝒢 : MeasurableSet[pastSigma κ b jumps spec E k] {ω | AllSucc Δ (fun j => E j ω) k} :=
    measurableSet_allSucc hgw hprog hΔ E hk.le
  have hker' : ∀ᵐ ω₀ ∂P, ω₀ ∈ F ∩ {ω | AllSucc Δ (fun j => E j ω) k} →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ A := by
    filter_upwards [hker, hpair] with ω₀ h1 h2 hω₀
    exact h1 hω₀.2 (h2 hω₀.1)
  have hP := ae_of_ae_condExpKernel_on' (hS.2.1 k) (hF.inter hL𝒢) hAm hker'
  filter_upwards [hP] with ω hω hωF c θ' hl
  have hωL : AllSucc Δ (fun j => E j ω) k := by
    by_contra hns
    rw [(launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω) hk).2 hns] at hl
    exact absurd hl (by simp)
  exact hpath ω (hω ⟨hωF, hωL⟩) c θ' hl

end GW2Later

end Theorem14

end InteractingSLE
