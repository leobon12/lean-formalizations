/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LaEL

/-!
# SB2(2): the recursive construction of `EL` over the relative stages

Packet PROVE-SB2-LIFTSET (round 10). The relative stage curve at stage `j` is read in the relative run chart at stage
`j`, which depends on the relative drivers before `j`; so `EL` is built by recursion over the stages:

* `StageOK`, **`stageDrv`**, `stageDrv_regular`, **`stageDrv_spec`**: the driver of one stage (the construction of
  `exists_EL_of_stageCurves_zero` when the stage is admissible, `zeroDrv` otherwise), always regular;
* `before`, **`ELrec`** (well-founded recursion: stage `j`'s driver is the stage driver of the curve and events that a
  rule assigns to the drivers before `j`), `ELrec_eq`;
* **`exists_EL_rec`**: for a rule depending only on the earlier drivers and admissible when they are measurable, the
  family `ELrec` is measurable (strong induction), regular at every sample, `zeroDrv` on the zero events, and
  generates the stage curves (read with the family itself) on the driven events;
* `hdep_of_run`: rules that read the drivers through the run at stage `j` satisfy the dependence hypothesis
  (`run_congr`);
* **`RelStageRuleAt`**, **`SB2LowerRelStageRuleStatement`** (named input, the rule form of `SB2LaEL`'s stage curves);
  **`sb2LowerRelDriverDataStatement_of_rule`**, `sb2LowerLaunchLiftStatement_of_rule`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- A driver with its lifetime. -/
abbrev Drv : Type := (ℝ≥0 → ℝ) × ℝ≥0∞

section Stage

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hypotheses of one stage of the construction. -/
def StageOK (ρ₀ : Ω → ℝ → ℂ) (G₀ Z₀ : Set Ω) : Prop :=
  (∀ t, 0 ≤ t → Measurable fun ω => ρ₀ ω t) ∧ MeasurableSet G₀ ∧ MeasurableSet Z₀ ∧
    ∀ ω ∈ G₀, IsDrivenCurve (ρ₀ ω)

open Classical in
/-- **The driver of one stage**: the construction of `exists_EL_of_stageCurves_zero` when the stage is admissible,
`zeroDrv` otherwise. -/
def stageDrv (ρ₀ : Ω → ℝ → ℂ) (G₀ Z₀ : Set Ω) : Ω → Drv :=
  if h : StageOK ρ₀ G₀ Z₀ then
    (exists_EL_of_stageCurves_zero (ρ := fun _ => ρ₀) (G := fun _ => G₀) (Z := fun _ => Z₀)
      (fun _ => h.1) (fun _ => h.2.1) (fun _ => h.2.2.1) (fun _ => h.2.2.2)).choose 0
  else fun _ => zeroDrv

/-- The stage driver is regular at every sample. -/
theorem stageDrv_regular (ρ₀ : Ω → ℝ → ℂ) (G₀ Z₀ : Set Ω) (ω : Ω) : IsRegularDriver (stageDrv ρ₀ G₀ Z₀ ω) := by
  unfold stageDrv
  split_ifs with h
  · exact (exists_EL_of_stageCurves_zero (ρ := fun _ => ρ₀) (G := fun _ => G₀) (Z := fun _ => Z₀)
      (fun _ => h.1) (fun _ => h.2.1) (fun _ => h.2.2.1) (fun _ => h.2.2.2)).choose_spec.2.1 0 ω
  · exact isRegularDriver_zeroDrv

/-- The stage driver of an admissible stage. -/
theorem stageDrv_spec {ρ₀ : Ω → ℝ → ℂ} {G₀ Z₀ : Set Ω} (h : StageOK ρ₀ G₀ Z₀) :
    Measurable (stageDrv ρ₀ G₀ Z₀) ∧ (∀ ω ∈ Z₀, stageDrv ρ₀ G₀ Z₀ ω = zeroDrv) ∧
      ∀ ω ∈ G₀, ω ∉ Z₀ → (stageDrv ρ₀ G₀ Z₀ ω).2 = capLife (ρ₀ ω) ∧
        ∀ T < capLife (ρ₀ ω), IsGeneratingTrace (stageDrv ρ₀ G₀ Z₀ ω).1 T (capTrace (ρ₀ ω)) := by
  have hs := (exists_EL_of_stageCurves_zero (ρ := fun _ => ρ₀) (G := fun _ => G₀) (Z := fun _ => Z₀)
      (fun _ => h.1) (fun _ => h.2.1) (fun _ => h.2.2.1) (fun _ => h.2.2.2)).choose_spec
  have e : stageDrv ρ₀ G₀ Z₀ = (exists_EL_of_stageCurves_zero (ρ := fun _ => ρ₀) (G := fun _ => G₀)
      (Z := fun _ => Z₀) (fun _ => h.1) (fun _ => h.2.1) (fun _ => h.2.2.1) (fun _ => h.2.2.2)).choose 0 := by
    unfold stageDrv; simp only [h, ↓reduceDIte]
  rw [e]
  exact ⟨hs.1 0, hs.2.2.1 0, hs.2.2.2 0⟩

end Stage


/-! ### The recursion over the stages -/

section Rec

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The family of the drivers before stage `j` (the zero root at the later indices). -/
def before (F : ℕ → Ω → Drv) (j : ℕ) : ℕ → Ω → Drv := fun i => if i < j then F i else fun _ => zeroDrv

/-- **The recursive relative drivers**: stage `j`'s driver is the stage driver of the curve and events that the rule
assigns to the drivers before `j`. -/
def ELrec (ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ) (G Z : ℕ → (ℕ → Ω → Drv) → Set Ω) (j : ℕ) : Ω → Drv :=
  stageDrv (ρ j (fun i => if _ : i < j then ELrec ρ G Z i else fun _ => zeroDrv))
    (G j (fun i => if _ : i < j then ELrec ρ G Z i else fun _ => zeroDrv))
    (Z j (fun i => if _ : i < j then ELrec ρ G Z i else fun _ => zeroDrv))
termination_by j

/-- The unfolding equation of `ELrec`. -/
theorem ELrec_eq (ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ) (G Z : ℕ → (ℕ → Ω → Drv) → Set Ω) (j : ℕ) :
    ELrec ρ G Z j = stageDrv (ρ j (before (ELrec ρ G Z) j)) (G j (before (ELrec ρ G Z) j))
      (Z j (before (ELrec ρ G Z) j)) := by
  rw [ELrec]
  rfl

/-- **The recursive construction of `EL`**: a rule assigning to the drivers before stage `j` the stage curve and
events of stage `j` — depending only on those drivers, measurable at every time when they are measurable, driven on
`G` — has a driver family that is measurable, regular at every sample, `zeroDrv` on the zero events and generating the
stage curves (with their capacity lifetimes) on the driven events, all read with the family itself. -/
theorem exists_EL_rec (ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ) (G Z : ℕ → (ℕ → Ω → Drv) → Set Ω)
    (hdep : ∀ j F F', (∀ i < j, F i = F' i) → ρ j F = ρ j F' ∧ G j F = G j F' ∧ Z j F = Z j F')
    (hok : ∀ j F, (∀ i < j, Measurable (F i)) → StageOK (ρ j F) (G j F) (Z j F)) :
    ∃ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      (∀ j, ∀ ω ∈ Z j EL, EL j ω = zeroDrv) ∧
      ∀ j, ∀ ω ∈ G j EL, ω ∉ Z j EL → (EL j ω).2 = capLife (ρ j EL ω) ∧
        ∀ T < capLife (ρ j EL ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j EL ω)) := by
  set EL := ELrec ρ G Z with hEL
  have hbef : ∀ j, ∀ i < j, before EL j i = EL i := fun j i hi => by simp [before, hi]
  have hmeas : ∀ j, Measurable (EL j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      have hok' := hok j (before EL j) fun i hi => by rw [hbef j i hi]; exact ih i hi
      rw [hEL, ELrec_eq]
      exact (stageDrv_spec hok').1
  have hok' : ∀ j, StageOK (ρ j (before EL j)) (G j (before EL j)) (Z j (before EL j)) := fun j =>
    hok j (before EL j) fun i hi => by rw [hbef j i hi]; exact hmeas i
  have hsame : ∀ j, ρ j (before EL j) = ρ j EL ∧ G j (before EL j) = G j EL ∧ Z j (before EL j) = Z j EL :=
    fun j => hdep j _ _ (hbef j)
  refine ⟨EL, hmeas, fun j ω => ?_, fun j ω hω => ?_, fun j ω hω hnZ => ?_⟩
  · rw [hEL, ELrec_eq]; exact stageDrv_regular _ _ _ ω
  · obtain ⟨-, -, hZ⟩ := hsame j
    rw [hEL, ELrec_eq]
    exact (stageDrv_spec (hok' j)).2.1 ω (by rw [hZ]; exact hω)
  · obtain ⟨hρ, hG, hZ⟩ := hsame j
    have := (stageDrv_spec (hok' j)).2.2 ω (by rw [hG]; exact hω) (by rw [hZ]; exact hnZ)
    rw [hEL, ELrec_eq, ← hρ]
    exact this

end Rec


/-- **Rules that read the drivers through the run at stage `j`** depend only on the drivers before `j` (`run_congr`):
the dependence hypothesis of `exists_EL_rec` for the concrete rule (the lifted actual piece read in the relative run
chart at stage `j`). -/
theorem hdep_of_run {Ω : Type*} {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (spec : ExplSpec)
    (Φρ : ℕ → Ω → ExplState → ℝ → ℂ) (ΦG ΦZ : ℕ → Ω → ExplState → Prop) :
    ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) →
      (fun ω => Φρ j ω (ExplState.run κ b J spec (fun i => F i ω) j)) =
          (fun ω => Φρ j ω (ExplState.run κ b J spec (fun i => F' i ω) j)) ∧
        {ω | ΦG j ω (ExplState.run κ b J spec (fun i => F i ω) j)} =
          {ω | ΦG j ω (ExplState.run κ b J spec (fun i => F' i ω) j)} ∧
        {ω | ΦZ j ω (ExplState.run κ b J spec (fun i => F i ω) j)} =
          {ω | ΦZ j ω (ExplState.run κ b J spec (fun i => F' i ω) j)} := by
  intro j F F' h
  have hr : ∀ ω, ExplState.run κ b J spec (fun i => F i ω) j = ExplState.run κ b J spec (fun i => F' i ω) j :=
    fun ω => run_congr spec fun i hi => by rw [h i hi]
  refine ⟨funext fun ω => by rw [hr ω], ?_, ?_⟩ <;> ext ω <;> simp only [mem_ofPred_eq, hr ω]

universe u

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The stage rule of the relative walk at one launch**: a rule giving stage `j`'s curve and events from the drivers
before `j` (the relative run chart at stage `j` reads only those), depending only on them, admissible when they are
measurable, such that every everywhere regular family that is `zeroDrv` on its zero events and generates its stage
curves on its driven events (both read with the family itself) satisfies the data clause. -/
def RelStageRuleAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
    ∃ (ρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ) (G Z : ℕ → (ℕ → Ω → Drv) → Set Ω),
      (∀ j F F', (∀ i < j, F i = F' i) → ρ j F = ρ j F' ∧ G j F = G j F' ∧ Z j F = Z j F') ∧
      (∀ j F, (∀ i < j, Measurable (F i)) → StageOK (ρ j F) (G j F) (Z j F)) ∧
      ∀ EL : ℕ → Ω → Drv, (∀ j ω, IsRegularDriver (EL j ω)) → (∀ j, ∀ ω ∈ Z j EL, EL j ω = zeroDrv) →
        (∀ j, ∀ ω ∈ G j EL, ω ∉ Z j EL → (EL j ω).2 = capLife (ρ j EL ω) ∧
          ∀ T < capLife (ρ j EL ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j EL ω))) →
        RelDataClause κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named input: SB2(2)'s stage rule at the later launches.** -/
def SB2LowerRelStageRuleStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelStageRuleAt κ b jumps P E u l k ω₀ c b' J'

/-- **`EL` built recursively from the stage rule** gives the head-free relative-driver data. -/
theorem sb2LowerRelDriverDataStatement_of_rule (hS : SB2LowerRelStageRuleStatement.{u}) :
    SB2LowerRelDriverDataStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk
  refine relDriverDataAt_of_clause fun m hm => ?_
  obtain ⟨ρ, G, Z, hdep, hok, hcl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, h1, h2, h3, h4⟩ := exists_EL_rec ρ G Z hdep hok
  exact ⟨EL, h1, h2, hcl EL h2 h3 h4⟩

/-- **SB2(2)'s combined target (R104a) from the stage rule and the conditional half** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_rule (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerRelStageRuleStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_data h12 h13 h12₀ h13₀ (sb2LowerRelDriverDataStatement_of_rule hS) hcond

end InteractingSLE.Theorem14.SB.Lk
