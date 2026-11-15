/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveLawL

/-!
# Lemma GW1: the later pieces of the right walk end on its own side

Packet PROVE-T14-GW1W. Lemma GW1, proof (`source/spec/p577-624.md` L949–L951, p. 618–619): "Thus a lower-extreme
continuation threshold can occur only on its right side. … Every finite threshold of a nonempty ordinary stage
consequently has physical value `q_j > w_j`, and is a new original right record."

* `status_run_succ_of_noLaunch`: an instruction of a walk that launches nothing never leaves a threshold status
  (deterministic);
* **`ae_status_ne_left_right_walk`**: for a staged right walk whose drivers are measurable and regular at every
  sample, almost surely **no** instruction ends at a new left record (every piece, not only the first; from the
  active-word classification `exists_witness_right` and the stage lemma `ae_stage_right`);
* **`ae_status_ne_right_left_walk`**: the mirror for the left walk;
* **`walkLaterRecordRegStatement_of_gw0`**, **`walkConnectorSideRegStatement_of_gw0`**:
  `GW1Conn.WalkLaterRecordStatement`
  and `GW3Word.WalkConnectorSideStatement` **for staged histories with drivers regular at every sample**
  (`WalkLaterRecordRegStatement`, `WalkConnectorSideRegStatement`: the same binders plus that regularity), from GW0's
  forward implication (the ambient bounds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW1W

open Exist Exist.StagedLaw Exist.Staged Restart LQGMetric

section Det

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- After the end of the program the state does not change. -/
theorem run_eq_of_length_le {m : ℕ} (hm : (boundaryWalkSpec b jumps θ right).2.2.length ≤ m) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D m =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (boundaryWalkSpec b jumps θ right).2.2.length := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← add_assoc, run_succ, GW1Conn.getElem?_boundaryWalkSpec,
      ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact ih (by omega)

/-- The status after a boundary continuation is not a threshold. -/
theorem status_contStep_ne_thr (s : ExplState) (pref : Bool) (o : Option Bool) :
    stStatus (ExplState.contStep κ b jumps s none pref) ≠ stThr o := by
  rcases status_contStep (κ := κ) (b := b) (jumps := jumps) s pref with ⟨r, h⟩ | h | h <;> rw [h] <;>
    simp [stArcM, stThr]

/-- **An instruction of a walk that launches nothing never leaves a threshold status.** -/
theorem status_run_succ_of_noLaunch {k : ℕ}
    (hn : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k = none) (o : Option Bool) :
    stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)) ≠ stThr o := by
  set L := (boundaryWalkSpec b jumps θ right).2.2.length with hL
  have hLpos : 0 < L ∧ L % 2 = 0 := by
    have hlen : L = 2 * ((PiecewiseConstantBoundaryData.jumpSet b jumps).card + 1) := by
      rw [hL]
      simp only [boundaryWalkSpec, List.length_flatten, List.map_replicate, List.sum_replicate,
        List.length_cons, List.length_nil, smul_eq_mul]
      ring
    omega
  -- the state after a continuation instruction
  have hcont : ∀ j, j < L → j % 2 = 1 →
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)) ≠ stThr o := fun j hj hodd => by
    rw [run_succ_walk_cont hj hodd]
    exact status_contStep_ne_thr _ _ _
  by_cases hk : k < L
  · rcases Nat.mod_two_eq_zero_or_one k with hev | hodd
    · have e := run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := right) (D := D) hk hev
      rw [e] at hn ⊢
      rw [flowStep_eq_self_of_noLaunch _ _ _ _ _ hn]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exfalso
        have : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D 0 = ExplState.init 0 := rfl
        rw [this] at hn
        simp only [ExplState.flowStep, ExplState.init] at hn
        rw [launches_launch, Function.update_self] at hn
        exact absurd hn (by simp)
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        exact hcont j (by omega) (by omega)
    · exact hcont k hk hodd
  · rw [run_eq_of_length_le (show L ≤ k + 1 by omega)]
    obtain ⟨j, hj⟩ : ∃ j, L = j + 1 := ⟨L - 1, by omega⟩
    rw [← hL, hj]
    exact hcont j (by omega) (by omega)

end Det

section Right

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **No piece of the right walk ends at a new left record** (Lemma GW1, (GW1.1), every piece), for a staged right
walk whose drivers are measurable and regular at every sample, under the ambient left bound `b + θχ < λ`. -/
theorem ae_status_ne_left_right_walk (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ true) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + θ * chiC κ < sleLambda κ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (k + 1)) ≠
        stThr (some false) := by
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨β, Y, hW, hinv⟩ := exists_witness_right hκ hb hh hE hreg hamb k
  filter_upwards [ae_stage_right hκ hb hh hE hreg hW (hinv.mono fun ω hω hl => (hω hl).1)] with ω hst
  by_cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (k + 1)).2.2.2.1 k = none
  · exact status_run_succ_of_noLaunch hl _
  · exact (hst hl).1

end Right

section LeftWalk

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {θ : ℝ}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **No piece of the left walk ends at a new right record** (Lemma GW1 reflected, every piece), for a staged left
walk whose drivers are measurable and regular at every sample, under the ambient right bound `−λ < b + θχ`. -/
theorem ae_status_ne_right_left_walk (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ false) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hamb : ∀ t, 0 < t → t ∉ jumps → -sleLambda κ < b t + θ * chiC κ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (k + 1)) ≠
        stThr (some true) := by
  refine ae_all_iff.2 fun k => ?_
  obtain ⟨β, Y, hW, hinv⟩ := exists_witness_left hκ hb hh hE hreg hamb k
  filter_upwards [ae_stage_left hκ hb hh hE hreg hW (hinv.mono fun ω hω hl => (hω hl).1)] with ω hst
  by_cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ false) (fun j => E j ω) (k + 1)).2.2.2.1 k = none
  · exact status_run_succ_of_noLaunch hl _
  · exact (hst hl).1

end LeftWalk

/-! ### The named statements for regular staged histories -/

/-- **`GW1Conn.WalkLaterRecordStatement` for staged histories with drivers regular at every sample** (its binders
verbatim, plus `∀ spec k ω, IsRegularDriver (E spec k ω)`): almost surely no instruction after the first ends the right
walk at a new left record, and none ends the left walk at a new right record. -/
def WalkLaterRecordRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, IsRegularDriver (E spec k ω)) →
      ∀ᵐ ω₀ ∂P, ∀ k : ℕ, 0 < k →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.2.2.1 ≠
          stThr (some false) ∧
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun j => E (boundaryWalkSpec b jumps (Real.pi / 2) false) j ω₀) (k + 1)).2.2.2.2.2.1 ≠
          stThr (some true)

/-- **`WalkLaterRecordRegStatement` from GW0's forward implication** (the ambient bounds of the counterflow word). -/
theorem walkLaterRecordRegStatement_of_gw0 (hGW0 : GW0.GW0ForwardStatement.{u}) : WalkLaterRecordRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ'
  have hpi := Real.pi_pos
  have hSR := hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  have hSL := hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false)
  filter_upwards [ae_status_ne_left_right_walk hκ hb hh hSR (hreg _) hambL,
    ae_status_ne_right_left_walk hκ hb hh hSL (hreg _) hambR] with ω h1 h2 k _
  exact ⟨h1 k, h2 k⟩

/-- **`GW3Word.WalkConnectorSideStatement` for staged histories with drivers regular at every sample** (its binders
verbatim, plus the regularity): almost surely every nontrivial real connector of the right walk is in `[0, ∞)` and every
one of the left walk in `(−∞, 0]` (Lemma GW1, "Every nontrivial real connector is rightward"). -/
def WalkConnectorSideRegStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec k ω, IsRegularDriver (E spec k ω)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        (∀ a ∈ (ExplState.run κ b jumps wR (fun k => E wR k ω₀) wR.2.2.length).2.1, a ⊆ Ici 0) ∧
        ∀ a ∈ (ExplState.run κ b jumps wL (fun k => E wL k ω₀) wL.2.2.length).2.1, a ⊆ Iic 0

/-- **`WalkConnectorSideRegStatement` from GW0's forward implication.** -/
theorem walkConnectorSideRegStatement_of_gw0 (hGW0 : GW0.GW0ForwardStatement.{u}) :
    WalkConnectorSideRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds hGW0 hκ hκ4 hb hh hcf hζ'
  obtain ⟨hrootL, hrootR⟩ := GW1Conn.root_bounds hb hambL hambR
  have hpi := Real.pi_pos
  have hSR := hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true)
  have hSL := hE _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false)
  filter_upwards [ae_status_ne_left_right_walk hκ hb hh hSR (hreg _) hambL,
    ae_status_ne_right_left_walk hκ hb hh hSL (hreg _) hambR] with ω h1 h2
  exact ⟨GW1Conn.arcs_subset_Ici_of_forall_ne hrootL _ h1, GW1Conn.arcs_subset_Iic_of_forall_ne hrootR _ h2⟩

/-! ### Arbitrary staged histories: the reduction to a regularization -/

/-- **Named input: staged walk histories can be regularized.** For every family of staged histories there is a family
of staged histories with drivers regular at every sample which, almost surely along each boundary walk, reaches every
threshold status the original family reaches. (Mathematical content: replace each driver by the continuous extension of
its rational samples before the lifetime; at a threshold the original driver is continuous before the stop, since real
points survive on every earlier interval, and equals its left limit at the stop by the third clause of
`IsStagedHistory`; the retained pasts then agree almost surely, by induction over the launches with the conditional
laws.) PROVE-T14-GW1P (§5 of its handoff) shows why some such step is needed: pathwise claims about later pieces do not
follow from `IsStagedHistory` without the passage from the conditional kernels to `P`. -/
def WalkRegularizationStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec)) →
      ∃ E' : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E' spec)) ∧
        (∀ spec k ω, IsRegularDriver (E' spec k ω)) ∧
        ∀ (θ : ℝ) (right : Bool), ∀ᵐ ω ∂P, ∀ (k : ℕ) (o : Option Bool),
          stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
              (fun j => E (boundaryWalkSpec b jumps θ right) j ω) (k + 1)) = stThr o →
            stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
              (fun j => E' (boundaryWalkSpec b jumps θ right) j ω) (k + 1)) = stThr o

/-- **`GW1Conn.WalkLaterRecordStatement` from GW0's forward implication and the regularization** (conditional helper
with a distinct name). -/
theorem walkLaterRecordStatement_of_regularization (hGW0 : GW0.GW0ForwardStatement.{u})
    (hR : WalkRegularizationStatement.{u}) : GW1Conn.WalkLaterRecordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  obtain ⟨E', hE', hreg, htr⟩ := hR κ hκ hκ4 b jumps hb P h hh E hE
  filter_upwards [walkLaterRecordRegStatement_of_gw0 hGW0 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E' hE' hreg,
    htr (-(Real.pi / 2)) true, htr (Real.pi / 2) false] with ω h1 h2 h3 k hk
  exact ⟨fun he => (h1 k hk).1 (h2 k _ he), fun he => (h1 k hk).2 (h3 k _ he)⟩

end GW1W

end Theorem14

end InteractingSLE
