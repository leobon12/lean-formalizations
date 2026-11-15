/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MhCap
import InteractingSLE.Spec.Supplement.SB2DrvLineSet
import InteractingSLE.Spec.Coupling.SafeFamily

/-!
# SB2(2)'s explored mean on the whole complement: the explored set read from the post-cap chart

Packet PROVE-SB2-LCMEAN, round 6 (the `hind₂` input in the form `Ln.IsStagePullback` needs). Round 5's
`Mh.exists_capMean_pointwise` identifies the explored prefix's mean on the post-cap chart domain `c'.dom` only, while
the stage pull-back asks the identity on all of `ℍ ∖ A₂` with `A₂ ⊇ ℍ ∖ D` (the filled explored set). Instead of
proving a domain identity for fills, the explored set is taken to be **`ℍ ∖ c'.dom` on the capped launch event** (the
walk prefix elsewhere): it contains the prefix (the domain misses it), it is measurable for the capped past (through the
chart version's closed-ball events), hence marked local by enlargement, and its complement is exactly the chart domain.

* `measurableSet_subset_dom`: `{V ⊆ dom}` is an event when the closed-ball events of the domain are (rational balls);
* **`measurable_capSet`**: the explored set `if ω ∈ G then ℍ ∖ dom else B` is measurable for the marks;
* **`exists_capMean_dom`**: SB2(2)'s explored set after the capped piece and its mean, pointwise on `ℍ ∖ A₂`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mi

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField

/-! ### Measurability of the complement of a random chart domain -/

section Meas

variable {Ω : Type*} {𝓜 : MeasurableSpace Ω}

/-- `{V ⊆ dom}` is an event when every closed-ball event of the domain is (a countable intersection over rational
balls inside `V`). -/
theorem measurableSet_subset_dom {c : Ω → Chart}
    (hCm : ∀ (z : ℂ) (ε : ℝ), MeasurableSet[𝓜] {ω | closedBall z ε ⊆ (c ω).dom}) {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet[𝓜] {ω | V ⊆ (c ω).dom} := by
  set J : Set (ℚ × ℚ × ℚ) := {q | closedBall (Coupling.ratCentre q) (q.2.2 : ℝ) ⊆ V} with hJ
  have e : {ω | V ⊆ (c ω).dom} =
      ⋂ q ∈ J, {ω | closedBall (Coupling.ratCentre q) (q.2.2 : ℝ) ⊆ (c ω).dom} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro hV' q hq
      exact (show closedBall (Coupling.ratCentre q) (q.2.2 : ℝ) ⊆ V from hq).trans hV'
    · intro hall z hz
      obtain ⟨F, hzF, hFV⟩ := Coupling.exists_rationalBalls isCompact_singleton hV (singleton_subset_iff.2 hz)
      obtain ⟨q, hqF, hzq⟩ := mem_iUnion₂.1 (hzF (mem_singleton z))
      have hqV : closedBall (Coupling.ratCentre q) (q.2.2 : ℝ) ⊆ V :=
        (subset_biUnion_of_mem (u := fun b => closedBall (Coupling.ratCentre b) (b.2.2 : ℝ)) hqF).trans hFV
      exact hall q hqV (ball_subset_closedBall hzq)
  rw [e]
  exact MeasurableSet.biInter (Set.to_countable J) fun q _ => hCm _ _

open Classical in
/-- **The explored set read from a chart on an event** (`ℍ ∖ dom` on `G`, `B` elsewhere) is measurable for the marks. -/
theorem measurable_capSet {c : Ω → Chart}
    (hCm : ∀ (z : ℂ) (ε : ℝ), MeasurableSet[𝓜] {ω | closedBall z ε ⊆ (c ω).dom}) {G : Set Ω}
    (hG : MeasurableSet[𝓜] G) {B : Ω → Set ℂ} (hBm : Measurable[𝓜, hittingSigma] B) :
    Measurable[𝓜, hittingSigma] fun ω => if ω ∈ G then H \ ((c ω).dom : Set ℂ) else B ω := by
  refine Sec7.R5Same.measurable_hitting_of_disjoint fun V hV hVH => ?_
  have e : {ω | Disjoint (if ω ∈ G then H \ ((c ω).dom : Set ℂ) else B ω) V} =
      (G ∩ {ω | V ⊆ (c ω).dom}) ∪ (Gᶜ ∩ {ω | Disjoint (B ω) V}) := by
    ext ω
    by_cases hω : ω ∈ G
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, not_true_eq_false,
        false_and, or_false, true_and]
      constructor
      · intro hd z hz
        by_contra hzD
        exact Set.disjoint_left.1 hd ⟨hVH hz, hzD⟩ hz
      · intro hsub
        exact Set.disjoint_left.2 fun z hz hzV => hz.2 (hsub hzV)
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff, not_false_eq_true,
        true_and, false_and, false_or]
  rw [e]
  exact (hG.inter (measurableSet_subset_dom hCm hV)).union (hG.compl.inter (hBm (measurableSet_avoid hV hVH)))

end Meas

theorem H_diff_H_diff {D : Set ℂ} (hD : D ⊆ H) : H \ (H \ D) = D := by
  ext z
  constructor
  · rintro ⟨hzH, hz⟩
    by_contra hzD
    exact hz ⟨hzH, hzD⟩
  · intro hz
    exact ⟨hD hz, fun h => h.2 hz⟩

/-! ### SB2(2)'s explored set after the capped piece and its mean on the whole complement -/

section SB2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s explored set after the capped piece, with its mean on the whole complement** (the `hind₂` form): a
measurable, relatively closed set `A₂` containing the walk prefix `B_{≤ℓ,τ}` almost surely, local and marked local for
the capped past, whose complement is the post-cap chart domain on the capped launch event; every local-set mean of `A₂`
is there, at every harmonic representative, the stop word's chart mean read through the post-cap chart. -/
theorem exists_capMean_dom (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) (hℓ : ℓ < (boundaryWalkSpec b jumps θ right).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (A₂ : Ω → Set ℂ) (c' : Ω → Chart),
      Measurable[mΩ, hittingSigma] A₂ ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      (∀ᵐ ω ∂P, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω ⊆ A₂ ω) ∧
      IsLocalSet A₂ (centredField h u₀) P ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) A₂ (centredField h u₀) P ∧
      (∀ ω, (c' ω).IsConformal) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        c' ω = (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1) ∧
      (∀ ω, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ → H \ A₂ ω = (c' ω).dom) ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g →
        ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
            (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
          ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g ω φ = ∫ z, v z * φ z) →
            EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
              (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω))).mean ((c' ω).1 z) -
                chiC κ * (c' ω).2.2 z) (H \ A₂ ω) := by
  classical
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  set E' := StagedReg.regFam E w with hE'def
  have hEw : IsStagedHistory κ b jumps P h w E' := hE' w hw
  set w' := capSpec w ℓ θ (τ : ℝ≥0∞) with hw'
  have hS' : IsStagedHistory κ b jumps P h w' E' := isStagedHistory_capSpec hb hEw (hreg' w) hℓ hwℓ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hav, ho, hloc⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hS' (hreg' w) hu₀
    (ℓ + 1)
  obtain ⟨B, hBm, hBc, hBae, -⟩ := Lcd.exists_lineVersion (P := P) ⟨_, hS'.2.1 (ℓ + 1)⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ho hav hloc
  obtain ⟨c', hc'c, hc'l, hc'h, hdom, hfwd, hCm, hliftm, hc'eq⟩ :=
    WalkInf.prefixChartVersionStatement_of_mem hθ right κ hκ hκ4 b jumps hb P h hh (fun spec => StagedReg.regFam E spec)
      hE' hR' hreg' ℓ τ
  have hPR := (hR' w hw).ae_pieceRegular
  have hdisj : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E' ℓ τ →
      ((c' ω).dom : Set ℂ) ⊆ H \ WalkLaw.stageSet κ b jumps w' E' (ℓ + 1) ω := by
    filter_upwards [hc'eq, hPR] with ω hcω hPRω hω
    have hreg'' := pieceRegular_capSpec (fun j => E' j ω) hℓ.le hwℓ hPRω (τ : ℝ≥0)
    have hcc := (GW1RestartFinal.chart_boundaryRange_run w' (fun j => E' j ω) hreg'' (ℓ + 1)).1
    have hdis := prefixChartDomStatement κ b jumps w (fun j => E' j ω) ℓ θ τ hℓ hwℓ hω.1 hω.2 hPRω
    rw [hcω hω]
    exact fun z hz => ⟨hcc.dom_subset hz, fun hzB => Set.disjoint_left.1 hdis hz hzB.1⟩
  have hG : MeasurableSet[pastSigma κ b jumps w' E' (ℓ + 1)] (capEvent κ b jumps w E' ℓ τ) :=
    measurableSet_capEvent hb hEw.1 (hreg' w) hℓ.le hwℓ τ
  set A : Ω → Set ℂ := fun ω => if ω ∈ capEvent κ b jumps w E' ℓ τ then H \ ((c' ω).dom : Set ℂ) else B ω
    with hA
  have hAm𝓜 : Measurable[pastSigma κ b jumps w' E' (ℓ + 1), hittingSigma] A := Mi.measurable_capSet hCm hG hBm
  have hAm : Measurable[mΩ, hittingSigma] A := hAm𝓜.mono (hS'.2.1 (ℓ + 1)) le_rfl
  have hcompl : ∀ ω, ω ∈ capEvent κ b jumps w E' ℓ τ → H \ A ω = (c' ω).dom := by
    intro ω hω
    simp only [hA, hω, ↓reduceIte]
    exact H_diff_H_diff (hc'c ω).dom_subset
  have hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    intro ω
    by_cases hω : ω ∈ capEvent κ b jumps w E' ℓ τ
    · refine ⟨?_, ?_⟩
      · simp only [hA, hω, ↓reduceIte]; exact sdiff_subset
      · rw [hcompl ω hω]; exact (c' ω).dom.isOpen
    · simp only [hA, hω, ↓reduceIte]; exact hBc ω
  have hsub : ∀ᵐ ω ∂P, WalkLaw.stageSet κ b jumps w' E' (ℓ + 1) ω ⊆ A ω := by
    filter_upwards [hBae, hdisj] with ω hBω hdω
    by_cases hω : ω ∈ capEvent κ b jumps w E' ℓ τ
    · simp only [hA, hω, ↓reduceIte]
      intro z hz
      exact ⟨WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω hz, fun hzD => (hdω hω hzD).2 hz⟩
    · simp only [hA, hω, ↓reduceIte]
      rw [hBω]
  have hAloc : IsHistoryAvoidanceLocal (pastSigma κ b jumps w' E' (ℓ + 1)) A (centredField h u₀) P :=
    Lv.isHistoryAvoidanceLocal_of_ae_enlargement hloc (hsub.mono fun ω h z hz => h hz.1)
      fun U hUH => hAm𝓜 (measurableSet_avoid U.isOpen hUH)
  have hAl : IsLocalSet A (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 hAm (Eventually.of_forall hAc)).out 4 1).2 hAloc.isAvoidanceLocal
  have hAD : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E' ℓ τ →
      ((c' ω).dom : Set ℂ) ⊆ H \ A ω ∧ IsOpen ((H \ A ω) \ (c' ω).dom) := by
    refine Eventually.of_forall fun ω hω => ?_
    rw [hcompl ω hω]
    exact ⟨subset_rfl, by simp⟩
  refine ⟨A, c', hAm, hAc, hsub, hAl, hAloc, hc'c, hc'eq, hcompl, fun g hg => ?_⟩
  obtain ⟨β, -, hmean⟩ := ae_capMean hκ hb hh hEw (hreg' w) hℓ hwℓ τ hu₀ hAm hAl hAloc hc'c hc'l hdom hfwd hCm
    hliftm hc'eq hAD hg
  refine ⟨β, ?_⟩
  have hbumps := ae_all_iff.2 fun i : ℚ × ℚ × ℚ => hmean (ratBump i)
  filter_upwards [hbumps] with ω hbω hω v hv hvg
  rw [hcompl ω hω] at hv hvg ⊢
  have hβs := isSorted_stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞) (E' ℓ ω))
  set β' := stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞) (E' ℓ ω)) with hβ'
  have hcm := harmonicOnNhd_chartMean (hc'c ω) (hc'h ω) hβs hu₀.1 (chiC κ)
  have hdH : ((c' ω).dom : Set ℂ) ⊆ H := (hc'c ω).dom_subset
  have hu₀c : ContinuousOn u₀ (c' ω).dom := fun z hz => (hu₀.1 z (hdH hz)).1.continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z) (c' ω).dom := by
    have h1 : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom :=
      fun z hz => (hcm z hz).1.continuousAt.continuousWithinAt
    refine (h1.add hu₀c).congr fun z _ => ?_
    simp only [Pi.add_apply]
    ring
  have heq : EqOn v (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom := by
    refine eqOn_of_ratBump (c' ω).dom.isOpen hdH hv hcm fun i hi => ?_
    rw [← hvg _ hi, hbω i hω hi, ← integral_sub (WholeField.integrable_mul_testOn hfc _ hi)
      (WholeField.integrable_mul_testOn hu₀c _ hi)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  intro z hz
  have e := heq hz
  simp only at e ⊢
  rw [e]
  ring

/-- B's stage-`ℓ` chart (the walk's run chart before instruction `ℓ`, regularized family). -/
def sb2StageChart (κ : ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (θ : ℝ) (right : Bool) (ℓ : ℕ) (ω : Ω) : Chart :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
    (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) ℓ).2.2.2.2.1

/-- The driver of piece `ℓ` stopped at `min τ ζ` (as recorded by `ExplState.launch`). -/
def sb2StopDrv {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ)
    (right : Bool) (ℓ : ℕ) (τ : ℝ≥0) (ω : Ω) : ℝ → ℝ := fun x : ℝ =>
  (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω).1
    (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞)
      (min (τ : ℝ≥0∞) (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω).2)).toNNReal

/-- The own stop time `min τ ζ` of piece `ℓ`, as a real number. -/
def sb2StopTime {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ)
    (right : Bool) (ℓ : ℕ) (τ : ℝ≥0) (ω : Ω) : ℝ :=
  ((min (τ : ℝ≥0∞) (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω).2).toNNReal : ℝ)

/-- **SB2(2)'s explored mean in the `hind₂` form of `Ln.IsStagePullback`** (`exists_capMean_dom` read through
`WalkSide.chart_run_capSpec_succ`: on the capped launch event the post-cap chart is B's stage-`ℓ` chart followed by the
Loewner map of the stopped piece): explored-chain formula with `GE := stopWord.mean`, the stopped driver
`sb2StopDrv` and the stop time `sb2StopTime`. -/
theorem exists_capMean_hind (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) (hℓ : ℓ < (boundaryWalkSpec b jumps θ right).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (A₂ : Ω → Set ℂ) (c' : Ω → Chart),
      Measurable[mΩ, hittingSigma] A₂ ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      (∀ᵐ ω ∂P, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω ⊆ A₂ ω) ∧
      IsLocalSet A₂ (centredField h u₀) P ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) A₂ (centredField h u₀) P ∧
      (∀ ω, (c' ω).IsConformal) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        c' ω = (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1) ∧
      (∀ ω, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ → H \ A₂ ω = (c' ω).dom) ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g →
        ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
            (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
          ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g ω φ = ∫ z, v z * φ z) →
            EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
              (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω))).mean
                (QuantumZipper.fwdMap (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)
                  ((sb2StageChart κ E b jumps θ right ℓ ω).1 z)) -
              chiC κ * ((QuantumZipper.logDerivFwd (sb2StopDrv E b jumps θ right ℓ τ ω)
                  (sb2StopTime E b jumps θ right ℓ τ ω) ((sb2StageChart κ E b jumps θ right ℓ ω).1 z)).im +
                (sb2StageChart κ E b jumps θ right ℓ ω).2.2 z)) (H \ A₂ ω)
  := by
  obtain ⟨A₂, c', hAm, hAc, hsub, hAl, hAloc, hc'c, hc'eq, hcompl, hmean⟩ :=
    exists_capMean_dom h12p h13 hθ right hκ hκ4 hb hh hE hER ℓ hℓ hwℓ τ hu₀
  refine ⟨A₂, c', hAm, hAc, hsub, hAl, hAloc, hc'c, hc'eq, hcompl, fun g hg => ?_⟩
  obtain ⟨β, hβ⟩ := hmean g hg
  refine ⟨β, ?_⟩
  filter_upwards [hβ, hc'eq] with ω h1 hcω hω v hv hvg z hz
  have e := h1 hω v hv hvg hz
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω.1
  have hch := chart_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ.le hwℓ
    (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) hl τ
  rw [hcω hω, hch] at e
  exact e

end SB2

end InteractingSLE.Theorem14.SB.Mi
