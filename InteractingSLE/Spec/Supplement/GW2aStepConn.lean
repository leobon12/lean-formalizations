/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aContStep
import InteractingSLE.Spec.Supplement.BR4a
import InteractingSLE.Spec.Supplement.GW1DetPhysical
import InteractingSLE.Spec.Supplement.GW2JointKernelProofWord
import InteractingSLE.Spec.Supplement.GW2JointKernelProofChart
import InteractingSLE.Spec.Sec7.Lemma78MeanWordMeas

/-!
# GW2a's connector step: BR4a's retargeting in the conditional world, from BR6's forcing

Packet PROVE-GW2A-STEP. GW2a (supplement p. 623–624): "BR6 forces the entire connector and its reverse first visits,
and BR4a gives the actual complete pair targeted at its next seed. […] A connector has no field reveal."

The landed named input `GW2aCont.GW2aConnectorStepStatement` (PROVE-GW2AC) is proved here from
* **`GW2aConnectorForcingStatement`** (named input; BR6 forcing in the conditional world): at a state with GW1's datum
  where the next instruction records a connector, for every centred counterflow `Wk` (infinite lifetime) of the field
  read in the state chart, almost surely under the regular conditional law given the retained past, every point of
  the connector is a limit of physical tips of `Wk` (read through the chart and the inversion), and, if the history is
  still alive after the move, the chart image of the new current point is visited by `Wk`. Its content is GW1's
  conditional boundary word at threshold and connector states (the original word on the untouched boundary, GW2a's
  "H + θχ ≤ −λ ⟹ … the BW2 calculation, while the whole conditional word is admissible") and Theorem BR6's sufficiency
  for that word, read through the chart;
* `BR4a.BR4aStatement` (existing leaf; reduced by PROVE-BR4A to its hull identity), applied in the conditional world;
* Theorem 1.3 (regular continuous transient counterflow traces).

The steps proved here: the step appending a connector is a `moveAlong` (chart recentred at the new point) or a
`moveToEnd` (status *done*), uniformly in the drivers (`arc_step_cases`); the regular conditional law after the step is
the one before it (no reveal: the last record is the empty one); the field of a centred counterflow pair is a GFF with
piecewise-constant data (`exists_isGFF_of_isCenteredCounterflowDriver`, through the return field); the recentred field
is the field read in the new chart (`IsChartTransport.trans`, `trans_recenter_id`); BR4a's clock relation composes with
the state chart (`GW1Det.isRetargetOf_tipAt_trans`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2aStep

open Exist.Staged Exist.StagedLaw GW2Later CounterflowRange GW2aMulti GW2aCont

/-! ### The named forcing input -/

/-- **Named input: BR6's forcing of a connector in the conditional world of the retained past** (supplement
p. 623–624, "For a right threshold the proposed connector has `H + θχ ≤ −λ ⟹ H ≤ −λ − θχ ≤ −Λ`. Its outward
conditional counterflow sums are consequently at most `d` by the BW2 calculation, while the whole conditional word is
admissible. BR6 forces the entire connector and its reverse first visits"; Corollary BW2, pp. 615–616; Theorem BR6,
p. 610). For a boundary-continued program from `0` and a staged history with measurable drivers regular at every
sample: at almost every `ω₀` at which GW1's datum holds after `k` instructions and instruction `k` records a connector,
for every field `h'` read in the state chart and every centred counterflow `Wk` of `h'` with infinite lifetime under
the regular conditional law given the retained past, almost surely under that law
* every point `y` of the connector is a limit of physical tips of `Wk`, read through the state chart and the
  inversion;
* if the history is alive after the move, the chart image of the new current point is a tip of `Wk` (the new seed is
  visited, BR4a's hypothesis). -/
def GW2aConnectorForcingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ (p : List Instr), IsBoundaryContinuedProgram p → ∀ E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      IsStagedHistory κ b jumps P h ⟨0, false, p⟩ E → StagedPiecesRegular κ b jumps P ⟨0, false, p⟩ E →
      (∀ j ω, IsRegularDriver (E j ω)) → ∀ k : ℕ,
        ∀ᵐ ω₀ ∂P, HasStatePair κ b jumps P h W' ⟨0, false, p⟩ E k ω₀ →
          (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) (k + 1)).2.1 ≠
            (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.1 →
          ∀ (h' : Ω → DistOn upperHalfPlaneOpens) (Wk : ℝ≥0 → Ω → ℝ) (ζk : Ω → ℝ≥0∞),
            (∀ ω, IsChartTransport (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.2.2.2.1 1 0
              (QuantumZipper.chiC κ) (h ω) (h' ω)) →
            IsCenteredCounterflowDriver κ (condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀) h' Wk ζk →
            (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀), ζk ω = ⊤) →
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀),
              (∀ y ∈ arcAt κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k,
                (y : ℂ) ∈ closure {z : ℂ | ∃ r : ℝ≥0,
                  ((ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.2.2.2.1.trans
                    infinitySourceChart).tipAt (fun s => Wk s ω) r z}) ∧
              (¬ IsTerminal (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) (k + 1)) →
                ((((ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.2.2.2.1.1
                  ((ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) (k + 1)).2.2.2.2.2.2.1 : ℂ)).re :
                    ℝ) : ℂ) ∈ infinitySourceChart.tipSet (fun s => Wk s ω) ⊤)

/-! ### Deterministic facts about connector steps -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem chart_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).2.2.2.2.1 = s.2.2.2.2.1.recenter (s.2.2.2.2.1.1 x).re := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem pt_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).2.2.2.2.2.2.1 = x := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem launches_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).2.2.2.1 = s.2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem isTerminal_moveToEnd (s : ExplState) (r : Bool) : IsTerminal (ExplState.moveToEnd s r) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  exact Or.inl rfl

theorem not_isTerminal_moveAlong (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    ¬ IsTerminal (ExplState.moveAlong s r x m) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rintro (h | h) <;> simp [ExplState.moveAlong] at h

/-- **A step that records a connector** starts from a living state and is a move along the original boundary to a
real point or to the end. -/
theorem arc_step_cases (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (hne : (ExplState.run κ b jumps spec D (k + 1)).2.1 ≠ (ExplState.run κ b jumps spec D k).2.1) :
    ¬ IsTerminal (ExplState.run κ b jumps spec D k) ∧
      ((∃ (r : Bool) (x : ℝ) (m : Bool), ExplState.run κ b jumps spec D (k + 1) =
          ExplState.moveAlong (ExplState.run κ b jumps spec D k) r x m) ∨
        ∃ r : Bool, ExplState.run κ b jumps spec D (k + 1) =
          ExplState.moveToEnd (ExplState.run κ b jumps spec D k) r) := by
  rw [run_succ] at hne ⊢
  cases hk : spec.2.2[k]? with
  | none => rw [hk] at hne; exact absurd rfl hne
  | some ins =>
    rw [hk] at hne
    rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
    · exfalso
      apply hne
      change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t).2.1 = _
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t
        with e | e | e <;> rw [e]
      · rfl
      · exact arcs_launch _ _ _ _ _
    all_goals
      first
        | (change (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) none pref).2.1 ≠ _ at hne
           change ¬ IsTerminal _ ∧ ((∃ (r : Bool) (x : ℝ) (m : Bool),
             ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) none pref = _) ∨
               ∃ r : Bool, ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) none pref = _))
        | (change (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) (some v) pref).2.1 ≠ _ at hne
           change ¬ IsTerminal _ ∧ ((∃ (r : Bool) (x : ℝ) (m : Bool),
             ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) (some v) pref = _) ∨
               ∃ r : Bool, ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) (some v) pref = _))
      refine ⟨fun hT => ?_, ?_⟩
      · rcases isTerminal_contStep (κ := κ) (b := b) (jumps := jumps) hT _ pref with e | e <;> rw [e] at hne
        · exact hne rfl
        · exact hne rfl
      · rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D k) _ pref
          with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
        · rw [e] at hne; exact absurd rfl hne
        · rw [e] at hne; exact absurd rfl hne
        · exact Or.inl ⟨r, x, m, e⟩
        · exact Or.inr ⟨r, e⟩

/-- Recentring a chart is composing it with the recentred identity chart. -/
theorem trans_recenter_id (c : Chart) (v : ℝ) : c.trans (Chart.id.recenter v) = c.recenter v := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext z
  change (0 : ℝ) + c.2.2 z = c.2.2 z
  rw [zero_add]

/-- A regular counterflow never has the inversion tip `0`. -/
theorem not_tipAt_zero {V : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace V ⊤ γ) (hV : Continuous V)
    (hV0 : V 0 = 0) (r : ℝ≥0) : ¬ infinitySourceChart.tipAt V r 0 := fun h0 => by
  obtain ⟨hne, he⟩ := (GW4Leaf.tipAt_infinitySourceChart_iff hγ hV hV0 r 0).1 h0
  exact hne (inv_eq_zero.1 (neg_eq_zero.1 he.symm))

/-! ### The field of a centred counterflow pair is a GFF -/

/-- **The infinity-source transport determines its source field.** -/
theorem eq_of_isChartTransport_infinitySourceChart {a k : ℝ} {f₁ f₂ g : DistOn upperHalfPlaneOpens}
    (h₁ : IsChartTransport infinitySourceChart (-1) a k f₁ g)
    (h₂ : IsChartTransport infinitySourceChart (-1) a k f₂ g) : f₁ = f₂ := by
  ext φ
  have e : Chart.pushTest Chart.isConformal_infinitySourceChart
      (Chart.pushTest Chart.isConformal_infinitySourceChart φ) = φ := by
    have := Sec7.StripSysField.pushTest_return_pushTest φ
    rwa [GW2JointKernel.pushTest_return_eq] at this
  have a1 := h₁.apply_eq Chart.isConformal_infinitySourceChart
    (Chart.pushTest Chart.isConformal_infinitySourceChart φ)
  have a2 := h₂.apply_eq Chart.isConformal_infinitySourceChart
    (Chart.pushTest Chart.isConformal_infinitySourceChart φ)
  rw [e] at a1 a2
  linarith

/-- **The field of a centred counterflow pair is a GFF with piecewise-constant data**: its infinity-source transport
is the flow-line field of the counterflow (a GFF), and the field is the return field of that transport. -/
theorem exists_isGFF_of_isCenteredCounterflowDriver (hκ : 0 < κ) {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {h' : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ ν h' W ζ) :
    ∃ (b' : ℝ → ℝ) (J' : Finset ℝ), IsPiecewiseConstantBoundaryData b' J' ∧ IsGFFWithBoundaryData ν h' b' J' := by
  obtain ⟨b₁, J₁, hr, hb₁, htr, hfl⟩ := hcf
  have hk : 0 < 16 / κ := by positivity
  have hG := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb₁ hfl
  obtain ⟨c, hcs, hcJ, hcb⟩ := Restart.BoundaryWord.exists_fn_eq_strictMonoOn hb₁
  have hsort : c.IsSorted := fun i j hij hj => hcs.monotoneOn (lt_of_le_of_lt hij hj) hj hij
  have hGc : IsGFFWithBoundaryData ν hr c.fn c.jumps := by
    rw [hcJ]
    exact (Restart.isGFFWithBoundaryData_congr ν hr (S := ((J₁ : Finset ℝ) : Set ℝ))
      fun y hy => hcb y hy).2 hG
  have hret := GW2JointKernel.isGFFWithBoundaryData_returnField_retWord hsort (-(Real.pi * QuantumZipper.chiC κ))
    (QuantumZipper.chiC (16 / κ)) hGc
  have heq : (fun ω => Sec7.StripSysField.returnField (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (hr ω)) = h' := funext fun ω =>
    eq_of_isChartTransport_infinitySourceChart (Sec7.StripSysField.isChartTransport_returnField _ _ _) (htr ω)
  rw [heq] at hret
  exact ⟨_, _, (GW2JointKernel.retWord _ _ c).isPiecewiseConstantBoundaryData, hret⟩

/-! ### The connector step -/

/-- **GW2a's connector step from BR6's forcing and BR4a** (conditional helper with a distinct name): the landed named
input `GW2aCont.GW2aConnectorStepStatement` from `GW2aConnectorForcingStatement`, Corollary BR4a (applied in the
conditional world of the retained past) and Theorem 1.3. -/
theorem gw2aConnectorStepStatement_of_forcing (hF : GW2aConnectorForcingStatement.{u})
    (hBR4a : BR4a.BR4aStatement.{u}) (hT13 : Exist.Theorem13Statement.{u}) : GW2aConnectorStepStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' p hp E hS hR hreg k
  have hle := hS.2.1
  have hEm := hS.1
  filter_upwards [hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' p hp E hS hR hreg k,
    ae_ae_run_eq runMeasStatement hb ⟨0, false, p⟩ (fun i _ => hEm i) (fun i _ => hreg i) (k := k) (P := P),
    ae_ae_condExpKernel_succ_eq hle k, hR.ae_pieceRegular,
    Sec7.Aux122Disint.ae_ae_condExpKernel (hle k) (ae_isClosed_counterflowCompletedRange hT13 hκ hcf hζ')]
    with ω₀ hF₀ hrun hK hreg0 hcl hD hne
  obtain ⟨hterm, hform⟩ := arc_step_cases ⟨0, false, p⟩ (fun j => E j ω₀) k hne
  obtain ⟨s', -, hmove⟩ : ∃ s' : ExplState,
      s'.2.1 ≠ (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.1 ∧
      ∀ D, ExplState.run κ b jumps ⟨0, false, p⟩ D k = ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k →
        ExplState.run κ b jumps ⟨0, false, p⟩ D (k + 1) = s' := by
    rcases run_succ_cases (κ := κ) (b := b) (jumps := jumps) ⟨0, false, p⟩
        (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k) k
      with hkeep | hdead | ⟨θ, t, -, hl⟩ | hm
    · exact absurd (by rw [hkeep _ rfl]) hne
    · exact absurd (by rw [hdead _ rfl]; rfl) hne
    · exact absurd (by rw [hl _ rfl]; exact arcs_launch _ _ _ _ _) hne
    · exact hm
  have hs' : ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) (k + 1) = s' := hmove _ rfl
  have hconf := isConformal_runChart ⟨0, false, p⟩ (fun j => E j ω₀) k fun i _ => hreg0 i
  have hext : GW1P.HasProperBdryExt (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.2.2.2.1 :=
    (GW1P.isClosed_pieces_run ⟨0, false, p⟩ (fun j => E j ω₀) hreg0 k).1
  set c := (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k).2.2.2.2.1 with hc
  set h' : Ω → DistOn upperHalfPlaneOpens := fun ω => Chart.chartTransport hconf.1 1 0 (QuantumZipper.chiC κ) (h ω)
    with hh'
  have htr' : ∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω) := fun ω =>
    Chart.isChartTransport_chartTransport hconf.1 (Chart.locallyIntegrableOn_of_continuousOn hconf.2) 1 0 _ (h ω)
  obtain ⟨Wk, ζk, hWk, hζk, hidk⟩ := hD hterm h' htr'
  have hFk := hF₀ hD hne h' Wk ζk htr' hWk hζk
  have hregk := GW2Later.ae_counterflow_regular hT13 hκ hWk hζk
  -- the connector lies in the range
  have hcont : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀),
      ((↑) : ℝ → ℂ) '' arcAt κ b jumps ⟨0, false, p⟩ (fun j => E j ω) k ⊆
        counterflowCompletedRange (fun t => W' t ω) := by
    filter_upwards [hrun, hidk, hcl, hFk] with ω hω hidω hclω hFω
    rw [arcAt_eq_of_run_eq hω]
    rintro _ ⟨y, hy, rfl⟩
    exact closure_minimal (fun z hz => by obtain ⟨r, hr⟩ := hz; exact hidω r z hr) hclω (hFω.1 y hy)
  rcases hform with ⟨r, x, m, hx⟩ | ⟨r, hx⟩
  · -- a move along the boundary to `x`: retarget the pair at the chart image of `x` (BR4a)
    set v : ℝ := (c.1 (x : ℂ)).re with hv
    have hvis : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀),
        (v : ℂ) ∈ infinitySourceChart.tipSet (fun s => Wk s ω) ⊤ := by
      filter_upwards [hFk] with ω hω
      have h2 := hω.2 (by rw [hx]; exact not_isTerminal_moveAlong _ _ _ _)
      rwa [hx, pt_moveAlong] at h2
    have hv0 : v ≠ 0 := by
      intro hv0
      obtain ⟨ω, hω1, hω2⟩ := (hvis.and hregk).exists
      obtain ⟨γ, hγ, hWc, hW0, -⟩ := hω2
      rw [hv0, Chart.tipSet_eq_tipAt] at hω1
      obtain ⟨t, -, ht⟩ := hω1
      exact not_tipAt_zero hγ hWc hW0 t (by simpa using ht)
    obtain ⟨bk, Jk, hbk, hGk⟩ := exists_isGFF_of_isCenteredCounterflowDriver hκ hWk
    obtain ⟨hv', Wv, ζv, ℓ, hvtr, hWv, -, hpath⟩ :=
      hBR4a κ hκ hκ4 bk Jk hbk _ h' hGk Wk ζk hWk hζk v hv0 hvis
    have hζv : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀), ζv ω = ⊤ :=
      hpath.mono fun _ hω => hω.1
    have hregv := GW2Later.ae_counterflow_regular hT13 hκ hWv hζv
    have hconfv := hconf.1.recenter v
    have htrv : ∀ ω', IsChartTransport (c.recenter v) 1 0 (QuantumZipper.chiC κ) (h ω') (hv' ω') := fun ω' => by
      rw [← trans_recenter_id]
      exact IsChartTransport.trans hconf.1 (Chart.isConformal_id.recenter v) hconf.2
        (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) H) (htr' ω') (hvtr ω')
    have hcrec : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps ⟨0, false, p⟩ E k) ω₀),
        lastRec κ b jumps ⟨0, false, p⟩ E k ω = readRec (fun _ => 0, 0, false) := by
      filter_upwards [hrun] with ω hω
      refine lastRec_of_noLaunch _ E k ?_
      rw [hmove _ hω, ← hs', hx, launches_moveAlong]
      exact launches_run_of_le (κ := κ) (b := b) (jumps := jumps) _ _ le_rfl
    filter_upwards [hcont, hrun, hK, ae_condExpKernel_comap_eq_self (measurable_lastRec hle k) hcrec]
      with ω hcω hω h1 h2
    refine ⟨hcω, fun hlive h'' htr'' => ?_⟩
    have hω' : ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω) (k + 1) =
        ExplState.moveAlong (ExplState.run κ b jumps ⟨0, false, p⟩ (fun j => E j ω₀) k) r x m :=
      (hmove _ hω).trans (hs'.symm.trans hx)
    rw [hω', chart_moveAlong] at htr''
    rw [hω', chart_moveAlong, ← h1, h2]
    have hh'' : h'' = hv' := funext fun ω' => (htr'' ω').unique hconfv (htrv ω')
    subst hh''
    refine ⟨Wv, ζv, hWv, hζv, ?_⟩
    filter_upwards [hpath, hregk, hregv, hidk] with ω' hp' hrk' hrv' hid' r' z hz
    obtain ⟨γk, hγk, hWkc, hWk0, htrk⟩ := hrk'
    obtain ⟨γv, hγv, hWvc, -, htrv'⟩ := hrv'
    have hQ : GW1Path.IsRegCf (fun s => Wk s ω') := ⟨hWkc, hWk0, γk, hγk, htrk⟩
    have hret : GW1Path.IsRetargetOf (fun s => Wv s ω') (fun s => Wk s ω') v :=
      ⟨⟨γv, hγv, htrv'⟩, ℓ ω', hp'.2.1, hp'.2.2.1, hp'.2.2.2.1, hp'.2.2.2.2⟩
    exact hid' _ z ((GW1Det.isRetargetOf_tipAt_trans hext hQ hWvc hret hp'.2.2.2.2 r' z).1 hz)
  · -- a move to the end: the history is done
    filter_upwards [hcont, hrun] with ω hcω hω
    refine ⟨hcω, fun hlive => absurd ?_ hlive⟩
    rw [(hmove _ hω).trans (hs'.symm.trans hx)]
    exact isTerminal_moveToEnd _ _

end GW2aStep

end Theorem14

end InteractingSLE
