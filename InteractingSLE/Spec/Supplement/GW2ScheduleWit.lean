/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleLaw

/-!
# The staged law of a GW2 schedule with explicit witnesses read off the retained past

Packet PROVE-T14-TIP3. For a GW2 schedule `spec` (root `x₀ = spec.1`, the GW2 convention, angles `θ`, finite own times
`Δ`) and **any** family of drivers `E` that is measurable, regular at every sample and a conditional flow line at each
instruction (`StageOK`), the field read in the chart of instruction `k` and the boundary word of its conditional law
are explicit functions of the retained past (`pastMap`) and the field sample:

* `fieldChain k u f`: the field `f` read in the root chart, then in the record chart of each record of `u`;
* `pastWord k u` (`GW2SchedulePast`): the root word, then the single-stage word of each record.

`stageWitness_zero`, `stageWitness_succ` prove the invariant `IsStageWitness` of the landed staged law
(`Exist.StagedLaw.stageLaw`) for these witnesses (by the single-stage law `post_stage`).

**Determination** (`ae_agree_wordDrv`): at a launch, the `k`-th driver is then, almost surely, the field-determined
flow-line driver `wordDrv (θ k) (pastWord k u) (fieldChain k u (h ω))` of its retained past `u` (Theorem 1.2 in its
word-measurable form, through `Staged.ae_detCode_eq`), on its whole lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Schedule

open Exist Staged StagedLaw Restart LQGMetric

/-! ### The field read off a retained past -/

section Chain

variable (κ : ℝ) (x₀ : ℝ)

/-- **The field read in the chart of a retained past**: the root translation, then the record chart of each record. -/
def fieldChain : (k : ℕ) → PastData k → DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens
  | 0 => fun _ f => flowField x₀ 0 f
  | k + 1 => fun u f => recField κ (u (Fin.last k)) (fieldChain k (Fin.init (α := fun _ => RecData) u) f)

theorem measurable_fieldChain : ∀ k, Measurable fun p : PastData k × DistOn upperHalfPlaneOpens =>
    fieldChain κ x₀ k p.1 p.2
  | 0 => (measurable_flowField x₀ 0).comp measurable_snd
  | k + 1 => by
    have hinit : Measurable fun u : PastData (k + 1) => Fin.init (α := fun _ => RecData) u :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    exact measurable_recField_comp κ ((measurable_pi_apply (Fin.last k)).comp measurable_fst)
      ((measurable_fieldChain k).comp ((hinit.comp measurable_fst).prodMk measurable_snd))

variable {κ}

/-- The canonical field is the field read off the canonical records. -/
theorem fieldChain_canonRec (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (θ : ℕ → ℝ) (Δ : ℕ → ℝ≥0∞)
    (f : DistOn upperHalfPlaneOpens) :
    ∀ k, fieldChain κ x₀ k (fun i => canonRec hκ h12p βA c₀ x₀ θ Δ f i) f =
      (canonState hκ h12p βA c₀ x₀ θ Δ f k).2
  | 0 => rfl
  | k + 1 => by
    rw [canonState_succ]
    change recField κ (canonRec hκ h12p βA c₀ x₀ θ Δ f k)
      (fieldChain κ x₀ k (fun i : Fin k => canonRec hκ h12p βA c₀ x₀ θ Δ f i) f) = _
    rw [fieldChain_canonRec hκ h12p βA c₀ θ Δ f k]

end Chain

/-! ### The explicit witnesses -/

section Wit

variable {κ : ℝ} (θ : ℕ → ℝ) (Δ : ℕ → ℝ≥0∞) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (c₀ : BoundaryWord) {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}

/-- The word witness: the canonical word read off the retained past of `E`. -/
def wWord (κ' : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {Ω : Type u}
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) : BoundaryWord :=
  pastWord βA c₀ spec.1 θ k (pastMap κ' b jumps spec E k ω)

/-- The field witness: the field sample read off the retained past of `E`. -/
def wField (κ' : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) {Ω : Type u}
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  fieldChain κ' spec.1 k (pastMap κ' b jumps spec E k ω) (h ω)

theorem wWord_succ {Ω : Type u} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) :
    wWord θ βA c₀ κ b jumps spec E (k + 1) ω =
      βA (wWord θ βA c₀ κ b jumps spec E k ω, θ k, pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) := by
  simp only [wWord, pastWord]
  rw [pastMap_succ, Fin.init_snoc]

theorem wField_succ {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (ω : Ω) :
    wField κ b jumps spec h E (k + 1) ω =
      recField κ (pastMap κ b jumps spec E (k + 1) ω (Fin.last k)) (wField κ b jumps spec h E k ω) := by
  simp only [wField, fieldChain]
  rw [pastMap_succ, Fin.init_snoc]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem measurable_wField (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : Measurable h)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    Measurable (wField κ b jumps spec h E k) :=
  (measurable_fieldChain κ spec.1 k).comp
    ((measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) k le_rfl).prodMk hh)

/-- **The witness at instruction `0`**: the root chart, the root word and the field read in the root chart. -/
theorem stageWitness_zero (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hb : IsPiecewiseConstantBoundaryData b jumps) :
    IsStageWitness κ b jumps P h spec E 0 (wWord θ βA c₀ κ b jumps spec E 0) (wField κ b jumps spec h E 0) := by
  have hh₀ : IsGFFWithBoundaryData P h c₀.fn c₀.jumps := by
    rw [hc₀J]
    exact (Restart.isGFFWithBoundaryData_congr P h (S := (jumps : Set ℝ)) fun y hy => hc₀ y hy).2 hh
  have hgff := isGFFWithBoundaryData_shiftW spec.1 hh₀
  refine ⟨measurable_const, measurable_wField hb hh.1 hEm hreg 0, Eventually.of_forall fun ω _ => ?_, ?_⟩
  · exact ⟨Chart.isConformal_id.recenter _, Chart.continuousOn_recenter_lift Chart.continuousOn_id_lift,
      isChartTransport_shiftChart _ _ _⟩
  · rw [pastSigma_zero]
    filter_upwards [ae_isGFFWithBoundaryData_condExpKernel_bot hgff] with ω₀ h0 _
    exact h0

/-- **The next witness** (`post_stage`), for any measurable family regular at every sample. -/
theorem stageWitness_succ (hβA : IsStopLaw.{u} κ βA) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (hW : IsStageWitness κ b jumps P h spec E k (wWord θ βA c₀ κ b jumps spec E k) (wField κ b jumps spec h E k))
    (hok : StageOK κ b jumps P h spec E k) :
    IsStageWitness κ b jumps P h spec E (k + 1) (wWord θ βA c₀ κ b jumps spec E (k + 1))
      (wField κ b jumps spec h E (k + 1)) := by
  classical
  have hpm1 : Measurable (pastMap κ b jumps spec E (k + 1)) :=
    measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) (k + 1) le_rfl
  have h𝒢1 : pastSigma κ b jumps spec E (k + 1) ≤ mΩ := by rw [pastSigma_eq_comap]; exact hpm1.comap_le
  have hYm := measurable_wField (κ := κ) (spec := spec) hb hh.1 hEm hreg
  have hpost := post_stage hβA runMeasStatement hκ hb hh (fun j _ => hEm j) (fun j _ => hreg j) hok hW.1 hW.2.1
    hW.2.2.1 hW.2.2.2
  refine ⟨?_, hYm (k + 1), ?_, ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastWord βA c₀ spec.1 θ hβA.1 (k + 1)).comp (comap_measurable _)
  · rcases lt_or_ge (k + 1) spec.2.2.length with hk1 | hk1
    swap
    · exact Eventually.of_forall fun ω hl => absurd (launch_eq_none_of_le _ hk1) hl
    have hk : k < spec.2.2.length := lt_trans (Nat.lt_succ_self k) hk1
    filter_upwards [hW.2.2.1, hpost.1] with ω hpath hgood hl1
    have hs1 := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => E j ω) hk1).1 hl1
    have hs : AllSucc Δ (fun j => E j ω) k := hs1.mono (Nat.le_succ k)
    have hne := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => E j ω) hk).2 hs
    obtain ⟨hconf, hlift, hT⟩ := hpath hne
    have hgd := hgood hne (by
      rw [instrTime_eq θ Δ hprog hk]; exact ne_top_of_le_ne_top (hΔ k) (min_le_left _ _))
    rw [instrTime_eq θ Δ hprog hk] at hgd
    rw [chart_run_eq θ Δ hgw hprog hΔ _ hk.le hs] at hconf hlift hT
    rw [chart_run_eq θ Δ hgw hprog hΔ _ hk1.le hs1]
    have hWc : Continuous fun x : ℝ => (retOf (Δ k) (E k ω)).1 x.toNNReal :=
      (continuous_retOf (hreg k ω) hgd).comp continuous_real_toNNReal
    have hW0 : (fun x : ℝ => (retOf (Δ k) (E k ω)).1 x.toNNReal) 0 = 0 := by
      change (E k ω).1 (min (((0 : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (Δ k) (E k ω).2)).toNNReal = 0
      rw [Real.toNNReal_zero, ENNReal.coe_zero, min_eq_left (zero_le (a := min (Δ k) (E k ω).2)),
        ENNReal.toNNReal_zero]
      exact (hreg k ω).2.1
    have hlast : pastMap κ b jumps spec E (k + 1) ω (Fin.last k) = recOf (Δ k) (E k ω) := by
      rw [pastMap_of_allSucc hgw hprog hΔ E hk1.le hs1]
      rfl
    rw [wField_succ, hlast]
    change ((succChart spec.1 Δ (fun j => E j ω) k).loewner (fun x : ℝ => (retOf (Δ k) (E k ω)).1 x.toNNReal)
        ((min (Δ k) (E k ω).2).toNNReal : ℝ)).IsConformal ∧
      ContinuousOn (fun w => ((succChart spec.1 Δ (fun j => E j ω) k).loewner
        (fun x : ℝ => (retOf (Δ k) (E k ω)).1 x.toNNReal) ((min (Δ k) (E k ω).2).toNNReal : ℝ)).2.2
        (((succChart spec.1 Δ (fun j => E j ω) k).loewner (fun x : ℝ => (retOf (Δ k) (E k ω)).1 x.toNNReal)
          ((min (Δ k) (E k ω).2).toNNReal : ℝ)).2.1 w)) QuantumZipper.H ∧
      IsChartTransport ((succChart spec.1 Δ (fun j => E j ω) k).loewner
        (fun x : ℝ => (retOf (Δ k) (E k ω)).1 x.toNNReal) ((min (Δ k) (E k ω).2).toNNReal : ℝ)) 1 0
        (QuantumZipper.chiC κ) (h ω) (recField κ (recOf (Δ k) (E k ω)) (wField κ b jumps spec h E k ω))
    refine ⟨hconf.loewner hWc hW0 (NNReal.coe_nonneg _),
      hconf.continuousOn_loewner_lift hlift hWc hW0 (NNReal.coe_nonneg _), ?_⟩
    rw [InteractingSLE.Chart.loewner_eq_trans, ← recChart_eq_loewner (hreg k ω) hgd]
    exact IsChartTransport.trans hconf (isConformal_recChart _) hlift (continuousOn_recChart_lift _) hT
      (isChartTransport_recField κ _ _)
  · rcases lt_or_ge (k + 1) spec.2.2.length with hk1 | hk1
    swap
    · exact Eventually.of_forall fun ω hl => absurd (launch_eq_none_of_le _ hk1) hl
    have hk : k < spec.2.2.length := lt_trans (Nat.lt_succ_self k) hk1
    set M : Set Ω := {ω | AllSucc Δ (fun j => E j ω) (k + 1)} with hMdef
    have hCF : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (wField κ b jumps spec h E (k + 1) ω' φ : ℂ)) |
          pastSigma κ b jumps spec E (k + 1)] ω = gaussCF (wWord θ βA c₀ κ b jumps spec E (k + 1) ω) φ := by
      intro φ
      filter_upwards [hpost.2 φ] with ω e3 hωM
      have hs : AllSucc Δ (fun j => E j ω) k := (show AllSucc Δ (fun j => E j ω) (k + 1) from hωM).mono
        (Nat.le_succ k)
      have hne := (launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ (fun j => E j ω) hk).2 hs
      have hstop : min (instrTime spec k) (E k ω).2 ≠ ⊤ := by
        rw [instrTime_eq θ Δ hprog hk]; exact ne_top_of_le_ne_top (hΔ k) (min_le_left _ _)
      have e3' := e3 hne hstop
      have hfun : (fun ω' => Complex.exp (Complex.I * (wField κ b jumps spec h E (k + 1) ω' φ : ℂ))) =
          fun ω' => Complex.exp (Complex.I * (recField κ (pastMap κ b jumps spec E (k + 1) ω' (Fin.last k))
            (wField κ b jumps spec h E k ω') φ : ℂ)) := by
        funext ω'; rw [wField_succ]
      rw [hfun, e3', wWord_succ, instrAngle_eq θ Δ hprog hk]
    have hK := ae_isGFFWithBoundaryData_condExpKernel h𝒢1 (M := M)
      (β := wWord θ βA c₀ κ b jumps spec E (k + 1))
      (Eventually.of_forall fun ω _ => by rw [wWord_succ]; exact hβA.2.1 _) (hYm (k + 1)) hCF
    filter_upwards [hK] with ω₀ hG hl1
    exact hG ((launch_ne_none_iff (κ := κ) (b := b) (jumps := jumps) θ Δ hgw hprog hΔ _ hk1).1 hl1)

/-- **The explicit witnesses at every instruction**, for a measurable family regular at every sample whose pieces
are conditional flow lines. -/
theorem stageWitness_all (hβA : IsStopLaw.{u} κ βA) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) (hh : IsGFFWithBoundaryData P h b jumps)
    (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hok : ∀ k, StageOK κ b jumps P h spec E k) :
    ∀ k, IsStageWitness κ b jumps P h spec E k (wWord θ βA c₀ κ b jumps spec E k) (wField κ b jumps spec h E k)
  | 0 => stageWitness_zero θ βA c₀ hc₀J hc₀ hh hEm hreg hb
  | k + 1 => stageWitness_succ θ Δ βA c₀ hβA hκ hb hh hgw hprog hΔ hEm hreg
      (stageWitness_all hβA hκ hb hc₀J hc₀ hh hgw hprog hΔ hEm hreg hok k) (hok k)

end Wit

end GW2Schedule

end Theorem14

end InteractingSLE
