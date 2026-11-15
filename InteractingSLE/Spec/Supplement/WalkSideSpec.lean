/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkBdryDefs

/-!
# Theorem 1.4's walk leaves: the capped program of a walk prefix

Packet PROVE-T14-WALKSIDE. Lemma GW3, proof (`source/spec/p625-671.md` L210–L226, p. 636: "Fix proper prefixes of the
two selected arcs … On an ordinary selected subarc the incoming own germ is …") reads the walk's mean near a recorded
piece through the **prefix** of that piece run to an own time `τ` before its stop. In the staged-history formalism a
prefix is itself a staged history: the program of the walk truncated before the launching instruction `ℓ`, followed
by the angle-`θ` flow for the own time `τ` (`capSpec`). Run with **the walk's own drivers**, its states agree with the
walk's before `ℓ`, and it is again a staged history of the field (`isStagedHistory_capSpec`): the staged clause at a
launch does not read the own time of the instruction.

* `capSpec`, its instructions (`capSpec_getElem?_of_lt`, `capSpec_getElem?_self`, `capSpec_getElem?_of_gt`);
* `run_capSpec_of_le`, `run_capSpec_succ`, `run_capSpec_of_ge`, `pastSigma_capSpec_of_le`;
* `launches_flowStep_time_indep`, `launches_run_capSpec_succ`;
* **`isStagedHistory_capSpec`**, `isBoundaryContinuedProgram_capSpec`.

Deterministic bookkeeping except the transfer of the staged clauses. R48: serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkSide

open Exist.StagedLaw Exist.Staged

/-! ### The capped program -/

/-- **The capped program**: the program of `w` truncated before instruction `ℓ`, followed by the angle-`θ` flow for
own time `τ` (same root, same GW2 flag). -/
def capSpec (w : ExplSpec) (ℓ : ℕ) (θ : ℝ) (τ : ℝ≥0∞) : ExplSpec :=
  (w.1, w.2.1, w.2.2.take ℓ ++ [Sum.inl (θ, τ)])

section Instr

variable {w : ExplSpec} {ℓ : ℕ} {θ : ℝ} {τ : ℝ≥0∞}

theorem capSpec_fst : (capSpec w ℓ θ τ).1 = w.1 := rfl

theorem capSpec_gw2 : (capSpec w ℓ θ τ).2.1 = w.2.1 := rfl

theorem capSpec_length (hℓ : ℓ ≤ w.2.2.length) : (capSpec w ℓ θ τ).2.2.length = ℓ + 1 := by
  simp [capSpec, List.length_take, hℓ]

theorem capSpec_getElem?_of_lt {k : ℕ} (hk : k < ℓ) (hℓ : ℓ ≤ w.2.2.length) :
    (capSpec w ℓ θ τ).2.2[k]? = w.2.2[k]? := by
  have hkt : k < (w.2.2.take ℓ).length := by rw [List.length_take]; omega
  simp only [capSpec]
  rw [List.getElem?_append_left hkt, List.getElem?_take_of_lt hk]

theorem capSpec_getElem?_self (hℓ : ℓ ≤ w.2.2.length) :
    (capSpec w ℓ θ τ).2.2[ℓ]? = some (Sum.inl (θ, τ)) := by
  have hl : (w.2.2.take ℓ).length = ℓ := by rw [List.length_take]; omega
  simp only [capSpec]
  rw [List.getElem?_append_right (by omega), hl, Nat.sub_self]
  rfl

theorem capSpec_getElem?_of_gt {k : ℕ} (hk : ℓ < k) (hℓ : ℓ ≤ w.2.2.length) :
    (capSpec w ℓ θ τ).2.2[k]? = none := by
  rw [List.getElem?_eq_none_iff, capSpec_length hℓ]
  omega

theorem instrTime_capSpec (hℓ : ℓ ≤ w.2.2.length) : instrTime (capSpec w ℓ θ τ) ℓ = τ := by
  simp only [instrTime, capSpec_getElem?_self hℓ]

theorem instrAngle_capSpec (hℓ : ℓ ≤ w.2.2.length) : instrAngle (capSpec w ℓ θ τ) ℓ = θ := by
  simp only [instrAngle, capSpec_getElem?_self hℓ]

theorem instrTime_capSpec_of_lt {k : ℕ} (hk : k < ℓ) (hℓ : ℓ ≤ w.2.2.length) :
    instrTime (capSpec w ℓ θ τ) k = instrTime w k := by
  simp only [instrTime, capSpec_getElem?_of_lt hk hℓ]

/-- The capped program of a boundary-continued program at an admissible angle is boundary-continued. -/
theorem isBoundaryContinuedProgram_capSpec (hw : IsBoundaryContinuedProgram w.2.2)
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) : IsBoundaryContinuedProgram (capSpec w ℓ θ τ).2.2 := by
  intro θ' t hmem
  simp only [capSpec, List.mem_append, List.mem_singleton, Sum.inl.injEq, Prod.mk.injEq] at hmem
  rcases hmem with hmem | ⟨rfl, -⟩
  · exact hw θ' t (List.mem_of_mem_take hmem)
  · exact hθ

end Instr

/-! ### Runs of the capped program -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec} {ℓ : ℕ} {θ : ℝ} {τ : ℝ≥0∞}

/-- **Before instruction `ℓ` the capped program runs as the program.** -/
theorem run_capSpec_of_le (hℓ : ℓ ≤ w.2.2.length) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k ≤ ℓ) :
    ExplState.run κ b jumps (capSpec w ℓ θ τ) D k = ExplState.run κ b jumps w D k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [run_succ, run_succ, ih (Nat.le_of_succ_le hk), capSpec_getElem?_of_lt (Nat.lt_of_succ_le hk) hℓ]
    rfl

/-- **Instruction `ℓ` of the capped program is the angle-`θ` flow for own time `τ`.** -/
theorem run_capSpec_succ (hℓ : ℓ ≤ w.2.2.length) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1) =
      ExplState.flowStep κ b w.2.1 (ExplState.run κ b jumps w D ℓ) ℓ (D ℓ) θ τ := by
  rw [run_succ, capSpec_getElem?_self hℓ, run_capSpec_of_le hℓ D le_rfl]
  rfl

/-- After instruction `ℓ` the capped program has no instructions. -/
theorem run_capSpec_of_ge (hℓ : ℓ ≤ w.2.2.length) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : ℓ + 1 ≤ k) :
    ExplState.run κ b jumps (capSpec w ℓ θ τ) D k = ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1) := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [run_succ, capSpec_getElem?_of_gt (by omega) hℓ]
    exact ih

/-- The retained σ-algebra of the capped program before `k ≤ ℓ` is the program's. -/
theorem pastSigma_capSpec_of_le (hℓ : ℓ ≤ w.2.2.length) {Ω : Type u} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k ≤ ℓ) : pastSigma κ b jumps (capSpec w ℓ θ τ) E k = pastSigma κ b jumps w E k := by
  unfold pastSigma
  simp_rw [run_capSpec_of_le (κ := κ) (b := b) (jumps := jumps) (θ := θ) (τ := τ) hℓ _ hk]

/-- The launch record of a flow step does not depend on the own time. -/
theorem launches_flowStep_time_indep (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ' : ℝ)
    (t t' : ℝ≥0∞) :
    (ExplState.flowStep κ b gw2 s k D θ' t).2.2.2.1 = (ExplState.flowStep κ b gw2 s k D θ' t').2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  repeat' first
    | (rw [launches_launch, launches_launch])
    | rfl
    | split

/-- **The launch record of instruction `ℓ` of the capped program is the program's**, when instruction `ℓ` of the
program is an angle-`θ` flow. -/
theorem launches_run_capSpec_succ (hℓ : ℓ ≤ w.2.2.length) {t : ℝ≥0∞}
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t))) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).2.2.2.1 =
      (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 := by
  rw [run_capSpec_succ hℓ D, run_succ (spec := w), hwℓ]
  exact launches_flowStep_time_indep _ _ _ _ _ _ _

end Run

/-! ### The capped program of a staged history is a staged history -/

section Staged

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {w : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {θ : ℝ} {τ : ℝ≥0∞}

/-- **The capped program, run with the program's drivers, is a staged history** when the program is one and its
instruction `ℓ` is an angle-`θ` flow: before `ℓ` the states and retained pasts agree; at `ℓ` the launch record does not
read the own time and the staged clause does not either; after `ℓ` nothing is launched. -/
theorem isStagedHistory_capSpec (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : IsStagedHistory κ b jumps P h w E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hℓ : ℓ < w.2.2.length)
    {t : ℝ≥0∞} (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t))) :
    IsStagedHistory κ b jumps P h (capSpec w ℓ θ τ) E := by
  refine ⟨hE.1, fun k => ?_, hE.2.2.1, fun k => ?_⟩
  · rw [pastSigma_eq_comap]
    exact (measurable_pastMap runMeasStatement hb (capSpec w ℓ θ τ) (k := k) (fun j _ => hE.1 j)
      (fun j _ => hreg j) k le_rfl).comap_le
  · rcases lt_trichotomy k ℓ with hk | rfl | hk
    · filter_upwards [hE.2.2.2 k] with ω₀ hω₀ c θ' hl
      rw [run_capSpec_of_le hℓ.le _ (Nat.succ_le_of_lt hk)] at hl
      rw [pastSigma_capSpec_of_le hℓ.le E hk.le]
      exact hω₀ c θ' hl
    · filter_upwards [hE.2.2.2 k] with ω₀ hω₀ c θ' hl
      rw [launches_run_capSpec_succ hℓ.le hwℓ] at hl
      rw [pastSigma_capSpec_of_le hℓ.le E le_rfl]
      exact hω₀ c θ' hl
    · refine Eventually.of_forall fun ω₀ c θ' hl => ?_
      rw [run_capSpec_of_ge hℓ.le _ (by omega : ℓ + 1 ≤ k + 1),
        launches_run_of_le (capSpec w ℓ θ τ) _ (Nat.succ_le_of_lt hk)] at hl
      exact absurd hl (by simp)

end Staged

/-! ### Recorded pieces, prefix sets and prefix charts -/

section Prefix

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The piece recorded when a driver `e` is launched for own time `t` from the state `s`. -/
def recPiece (s : ExplState) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0∞) : WalkBdry.Piece :=
  (s.2.2.2.2.1, fun r : ℝ≥0 => e.1 (min (r : ℝ≥0∞) (min t e.2)).toNNReal, min t e.2)

/-- **Every recorded piece was appended by a launch**: in a decomposition `pre ++ pc :: post` of the pieces after
`n` instructions, `pc` is the piece of an instruction `ℓ < n` that launched, and `pre` the pieces before `ℓ`. -/
theorem exists_launch_of_pieces_eq (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ (n : ℕ) {pre post : List WalkBdry.Piece} {pc : WalkBdry.Piece},
      (ExplState.run κ b jumps spec D n).1 = pre ++ pc :: post →
      ∃ ℓ < n, ∃ θ' : ℝ, (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.1 ℓ =
          some ((ExplState.run κ b jumps spec D ℓ).2.2.2.2.1, θ') ∧
        (ExplState.run κ b jumps spec D ℓ).1 = pre ∧
        pc = recPiece (ExplState.run κ b jumps spec D ℓ) (D ℓ) (instrTime spec ℓ)
  | 0, pre, post, pc, h => by
    have h0 : (ExplState.run κ b jumps spec D 0).1 = [] := rfl
    rw [h0] at h
    exact absurd h.symm (by simp)
  | n + 1, pre, post, pc, h => by
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · rw [GW1P.pieces_run_succ_of_noLaunch spec D hl] at h
      obtain ⟨ℓ, hℓ, θ'', h1, h2, h3⟩ := exists_launch_of_pieces_eq spec D n h
      exact ⟨ℓ, Nat.lt_succ_of_lt hℓ, θ'', h1, h2, h3⟩
    · obtain ⟨-, he, hc⟩ := eq_launch_of_launches spec D hl
      rw [he, CounterflowRange.pieces_launch] at h
      rcases List.eq_nil_or_concat post with rfl | ⟨post', y, rfl⟩
      · obtain ⟨h1, h2⟩ := List.append_inj' (h.trans (by simp : pre ++ [pc] = pre ++ [pc])) rfl
        refine ⟨n, Nat.lt_succ_self n, θ', by rw [hl, hc], h1, ?_⟩
        exact (List.singleton_inj.1 h2).symm
      · have e : pre ++ pc :: post'.concat y = (pre ++ pc :: post') ++ [y] := by simp
        rw [e] at h
        obtain ⟨h1, -⟩ := List.append_inj' h rfl
        obtain ⟨ℓ, hℓ, θ'', h1', h2', h3'⟩ := exists_launch_of_pieces_eq spec D n h1
        exact ⟨ℓ, Nat.lt_succ_of_lt hℓ, θ'', h1', h2', h3'⟩

variable {w : ExplSpec} {ℓ : ℕ} {θ : ℝ} {t : ℝ≥0∞}

/-- **The pieces of the capped program**: the program's pieces before `ℓ` and the piece of instruction `ℓ` for own
time `τ`, when instruction `ℓ` of the program (an angle-`θ` flow) launched. -/
theorem pieces_run_capSpec_succ (hℓ : ℓ ≤ w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t)))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ = some (c, θ')) (τ : ℝ≥0∞) :
    (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).1 =
      (ExplState.run κ b jumps w D ℓ).1 ++ [recPiece (ExplState.run κ b jumps w D ℓ) (D ℓ) τ] := by
  rw [← launches_run_capSpec_succ (τ := τ) hℓ hwℓ D] at hl
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (capSpec w ℓ θ τ) D hl
  rw [he, CounterflowRange.pieces_launch, instrTime_capSpec hℓ, run_capSpec_of_le hℓ D le_rfl]
  rfl

/-- The chart of the capped program after instruction `ℓ`, when it launched with a finite stop. -/
theorem chart_run_capSpec_succ (hℓ : ℓ ≤ w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t)))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ = some (c, θ')) (τ : ℝ≥0) :
    (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).2.2.2.2.1 =
      (ExplState.run κ b jumps w D ℓ).2.2.2.2.1.loewner
        (fun x : ℝ => (D ℓ).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) (D ℓ).2)).toNNReal)
        ((min (τ : ℝ≥0∞) (D ℓ).2).toNNReal : ℝ) := by
  rw [← launches_run_capSpec_succ (τ := (τ : ℝ≥0∞)) hℓ hwℓ D] at hl
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (capSpec w ℓ θ τ) D hl
  rw [he, chart_launch _ _ _ _ _ (ne_top_of_le_ne_top (by rw [instrTime_capSpec hℓ]; exact ENNReal.coe_ne_top)
    (min_le_left _ _)), instrTime_capSpec hℓ, run_capSpec_of_le hℓ D le_rfl]

end Prefix

/-! ### The prefix chart and the prefix set are the capped run's -/

section PrefixEq

open QuantumZipper (fwdMap fwdMapInv logDerivFwd)

/-- A stopped regular driver, read on real times, is continuous on `[0, t'']` below the lifetime. -/
theorem continuousOn_stoppedDrv {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) (S : ℝ≥0∞) {t'' : ℝ}
    (ht'' : ((t''.toNNReal : ℝ≥0) : ℝ≥0∞) < e.2) :
    ContinuousOn (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) (Icc 0 t'') := by
  have hg : Continuous fun x : ℝ => (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal := by
    by_cases hS : S = ⊤
    · simp only [hS, le_top, min_eq_left, ENNReal.toNNReal_coe]
      exact continuous_real_toNNReal
    · have e : (fun x : ℝ => (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) = fun x => min x.toNNReal S.toNNReal := by
        funext x
        rw [← ENNReal.coe_toNNReal hS, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.coe_toNNReal hS]
      rw [e]
      exact continuous_real_toNNReal.min continuous_const
  refine he.1.comp hg.continuousOn fun x hx => ?_
  change (((min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal : ℝ≥0) : ℝ≥0∞) < e.2
  refine lt_of_le_of_lt ?_ ht''
  refine le_trans ENNReal.coe_toNNReal_le_self (le_trans (min_le_left _ _) ?_)
  exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal hx.2)

/-- Two stoppings after `τ` of one driver agree on `[0, τ]`. -/
theorem eqOn_stoppedDrv (e : (ℝ≥0 → ℝ) × ℝ≥0∞) {S S' : ℝ≥0∞} {τ : ℝ≥0} (hS : (τ : ℝ≥0∞) ≤ S)
    (hS' : (τ : ℝ≥0∞) ≤ S') :
    EqOn (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal)
      (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) S').toNNReal) (Icc 0 (τ : ℝ)) := by
  intro x hx
  have hxτ : ((x.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ τ :=
    ENNReal.coe_le_coe.2 (by rw [← Real.toNNReal_coe (r := τ)]; exact Real.toNNReal_le_toNNReal hx.2)
  simp only [min_eq_left (hxτ.trans hS), min_eq_left (hxτ.trans hS')]

/-- A real time strictly between `τ` and a larger extended time. -/
theorem exists_real_btwn {τ : ℝ≥0} {S : ℝ≥0∞} (hτ : (τ : ℝ≥0∞) < S) :
    ∃ t'' : ℝ, (τ : ℝ) < t'' ∧ ((t''.toNNReal : ℝ≥0) : ℝ≥0∞) < S := by
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hτ
  refine ⟨r, by exact_mod_cast ENNReal.coe_lt_coe.1 hr1, ?_⟩
  rwa [Real.toNNReal_coe]

/-- **The prefix chart of a recorded piece is the chart of the piece stopped at `τ`.** -/
theorem prefixChart_recPiece (s : ExplState) {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {t : ℝ≥0∞}
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < min t e.2) :
    WalkBdry.prefixChart (recPiece s e t) τ = s.2.2.2.2.1.loewner
      (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) e.2)).toNNReal)
      ((min (τ : ℝ≥0∞) e.2).toNNReal : ℝ) := by
  have hτζ : (τ : ℝ≥0∞) < e.2 := lt_of_lt_of_le hτ (min_le_right _ _)
  have hmin : min (τ : ℝ≥0∞) e.2 = τ := min_eq_left hτζ.le
  obtain ⟨t'', ht''τ, ht''⟩ := exists_real_btwn hτ
  have ht''ζ : ((t''.toNNReal : ℝ≥0) : ℝ≥0∞) < e.2 := lt_of_lt_of_le ht'' (min_le_right _ _)
  set W₁ : ℝ → ℝ := fun x => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal with hW₁
  set W₂ : ℝ → ℝ := fun x => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) e.2)).toNNReal with hW₂
  have hEq : EqOn W₁ W₂ (Icc 0 (τ : ℝ)) := eqOn_stoppedDrv e hτ.le hmin.ge
  have hc₁ : ContinuousOn W₁ (Icc 0 t'') := continuousOn_stoppedDrv he _ ht''ζ
  have hc₂ : ContinuousOn W₂ (Icc 0 t'') := continuousOn_stoppedDrv he _ ht''ζ
  have hT : ((min (τ : ℝ≥0∞) e.2).toNNReal : ℝ) = τ := by rw [hmin, ENNReal.toNNReal_coe]
  rw [hT]
  change s.2.2.2.2.1.loewner W₁ τ = s.2.2.2.2.1.loewner W₂ τ
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun z => ?_) (funext fun z => ?_))
  · exact Ito.fwdMap_congr_of_eqOn_of_le hEq le_rfl
  · change s.2.2.2.2.1.2.1 (fwdMapInv W₁ τ z) = s.2.2.2.2.1.2.1 (fwdMapInv W₂ τ z)
    rw [LocalExt.fwdMapInv_congr_of_continuousOn hc₁ hc₂ τ.coe_nonneg ht''τ hEq z]
  · change (logDerivFwd W₁ τ (s.2.2.2.2.1.1 z)).im + s.2.2.2.2.1.2.2 z =
      (logDerivFwd W₂ τ (s.2.2.2.2.1.1 z)).im + s.2.2.2.2.1.2.2 z
    rw [Ito.logDerivFwd_congr_of_eqOn hEq τ.coe_nonneg le_rfl]

/-- **The tip set of a recorded piece up to `τ` is the tip set of the piece stopped at `τ`.** -/
theorem tipSet_recPiece (s : ExplState) {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {t : ℝ≥0∞}
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < min t e.2) :
    (recPiece s e t).1.tipSet (recPiece s e t).2.1 τ =
      (recPiece s e τ).1.tipSet (recPiece s e τ).2.1 (recPiece s e τ).2.2 := by
  have hτζ : (τ : ℝ≥0∞) < e.2 := lt_of_lt_of_le hτ (min_le_right _ _)
  have hmin : min (τ : ℝ≥0∞) e.2 = τ := min_eq_left hτζ.le
  obtain ⟨t'', ht''τ, ht''⟩ := exists_real_btwn hτ
  have ht''ζ : ((t''.toNNReal : ℝ≥0) : ℝ≥0∞) < e.2 := lt_of_lt_of_le ht'' (min_le_right _ _)
  have hc₁ := continuousOn_stoppedDrv he (min t e.2) ht''ζ
  have hc₂ := continuousOn_stoppedDrv he (min (τ : ℝ≥0∞) e.2) ht''ζ
  have hstop : (recPiece s e τ).2.2 = τ := hmin
  rw [hstop]
  ext z
  simp only [Chart.tipSet, mem_ofPred_eq, recPiece]
  refine exists_congr fun r => and_congr_right fun hr => ?_
  have hrτ : (r : ℝ) ≤ τ := by exact_mod_cast ENNReal.coe_le_coe.1 hr
  have hEq := (eqOn_stoppedDrv e (S := min t e.2) (S' := min (τ : ℝ≥0∞) e.2) hτ.le hmin.ge).mono
    (Icc_subset_Icc_right hrτ)
  have hfi : ∀ y : ℝ, fwdMapInv (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal) r
      (y * Complex.I) = fwdMapInv (fun x : ℝ => e.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞)
        (min (τ : ℝ≥0∞) e.2)).toNNReal) r (y * Complex.I) := fun y =>
    LocalExt.fwdMapInv_congr_of_continuousOn hc₁ hc₂ r.coe_nonneg (lt_of_le_of_lt hrτ ht''τ) hEq _
  simp only [hfi]

end PrefixEq

/-! ### The prefix set is the explored set of the capped program -/

section PrefixSet

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec} {ℓ : ℕ} {θ : ℝ} {t : ℝ≥0∞}

/-- **The prefix set of the piece of instruction `ℓ` is the explored set of the capped program after `ℓ`**, for a
launch at `ℓ` with a regular driver and `τ` before the stop. -/
theorem prefixSet_eq_stageSet {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (hℓ : ℓ ≤ w.2.2.length)
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t))) {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = some (c, θ'))
    (hreg : IsRegularDriver (E ℓ ω)) {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < min t (E ℓ ω).2) :
    WalkBdry.prefixSet (ExplState.run κ b jumps w (fun j => E j ω) ℓ).1
        (recPiece (ExplState.run κ b jumps w (fun j => E j ω) ℓ) (E ℓ ω) t) τ =
      WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1) ω := by
  rw [WalkLaw.stageSet, pieces_run_capSpec_succ hℓ hwℓ (fun j => E j ω) hl, WalkBdry.prefixSet,
    tipSet_recPiece _ hreg hτ]
  congr 1
  ext z
  simp only [mem_union, mem_iUnion, exists_prop, List.mem_append, List.mem_singleton]
  constructor
  · rintro (⟨p, hp, hz⟩ | hz)
    · exact ⟨p, Or.inl hp, hz⟩
    · exact ⟨_, Or.inr rfl, hz⟩
  · rintro ⟨p, hp | rfl, hz⟩
    · exact Or.inl ⟨p, hp, hz⟩
    · exact Or.inr hz

/-- **The prefix chart of the piece of instruction `ℓ` is the chart of the capped program after `ℓ`.** -/
theorem prefixChart_eq_chart {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (hℓ : ℓ ≤ w.2.2.length)
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t))) {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = some (c, θ'))
    (hreg : IsRegularDriver (E ℓ ω)) {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < min t (E ℓ ω).2) :
    WalkBdry.prefixChart (recPiece (ExplState.run κ b jumps w (fun j => E j ω) ℓ) (E ℓ ω) t) τ =
      (ExplState.run κ b jumps (capSpec w ℓ θ τ) (fun j => E j ω) (ℓ + 1)).2.2.2.2.1 := by
  rw [chart_run_capSpec_succ hℓ hwℓ (fun j => E j ω) hl τ, prefixChart_recPiece _ hreg hτ]

/-- On a launch, the retained datum of the capped instruction `ℓ` is the record of the driver stopped at `τ`. -/
theorem retained_run_capSpec_succ (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hℓ : ℓ ≤ w.2.2.length)
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t)))
    (hl : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none) (τ : ℝ≥0∞) :
    (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)).2.2.1 ℓ = retOf τ (D ℓ) := by
  rw [retained_run_succ_self, launches_run_capSpec_succ hℓ hwℓ D, instrTime_capSpec hℓ]
  simp only [hl, ↓reduceIte]

end PrefixSet

end InteractingSLE.Theorem14.WalkSide
