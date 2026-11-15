/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LiStage
import InteractingSLE.Spec.Supplement.SBLuDense

/-!
# SB2(2): the concrete stage rule of the relative walk

Packet PROVE-SB2-LIFTSET (round 12). The concrete rule behind `SB2LhRec.RelStageRuleAt`: relative stage `j` lifts the
actual piece launched at stage `j + o` (`o` the even stage where the actual walk reaches `R`), read in the relative
run chart at stage `j` — which depends on the earlier relative drivers only through the run. Here `o = relOff`: the even
stage of the start configuration (the launch adding `R`; the flow stage before the connector adding `R`; or, when that
connector ends at a restart mark `R`, the launch at `R` two stages later).

* `pcPt` (a piece's point: the launch chart's boundary value at the chosen trace, as in `LuM.newPiece`), `goodT` (its
  times in the upper chart's domain `c.2.1 '' ℍ`), `relVal` (the intrinsic lift `c.1 · + m` read in the relative
  chart), `stVal` (`relVal` at good times, its limit along good times elsewhere), **`stCurve`** (the stage curve on
  `[0, ∞)`: the actual time is `clockOf L u` for a finite lifetime `L`);
* `entryStage` (the first step adding `R` to the actual walk's physical part), `startOff` (its even stage), `ArcEntry`,
  `MarkEntry` (the connector adding `R` ends at a mark `R`), `ZeroRoot`, **`relOff`** (`startOff`, plus `2` at a mark);
* **`cρ`, `cZ`, `cG`**: the concrete rule (zero roots at odd stages and at stage `0` of an arc start not ending at a
  mark; driven events read through the run); **`hdep_concrete`**: it depends only on the earlier drivers
  (`hdep_of_run`);
* **`exists_EL_concrete`**: `exists_EL_rec` applied to the concrete rule;
* **`ConcreteRuleAt`**, **`SB2LowerConcreteRuleStatement`** (named input: the rule's admissibility and data clause for
  the concrete curves and zero events, with driven events read through the run);
  **`relStageRuleAt_of_concrete`**, **`sb2LowerRelDriverDataStatement_of_concrete`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C GW1Bookkeep

/-! ### The stage curve -/

/-- The point at trace time `t` of the piece launched from `s` with driver `e`: the boundary value of the launch chart
at the chosen trace (as in `LuM.newPiece`). -/
def pcPt (s : ExplState) (e : Drv) (t : ℝ≥0) : ℂ := LuM.bdVal (stChart s) (LuM.trOf e t)

/-- The good times of the piece: up to its lifetime, with the point in the upper chart's domain `c.2.1 '' ℍ`. -/
def goodT (c : Chart) (s : ExplState) (e : Drv) : Set ℝ≥0 :=
  {t | (t : ℝ≥0∞) ≤ e.2 ∧ pcPt s e t ∈ c.2.1 '' H}

/-- The intrinsic lift `c.1 · + m` of the piece's point at time `t`, read in the relative chart at `s₂`. -/
def relVal (c : Chart) (m : ℝ) (s₁ : ExplState) (e : Drv) (s₂ : ExplState) (t : ℝ≥0) : ℂ :=
  (stChart s₂).1 (liftPt c m (pcPt s₁ e t))

open Classical in
/-- The stage values: `relVal` at good times, its limit along the good times elsewhere. -/
def stVal (c : Chart) (m : ℝ) (s₁ : ExplState) (e : Drv) (s₂ : ExplState) (t : ℝ≥0) : ℂ :=
  if t ∈ goodT c s₁ e then relVal c m s₁ e s₂ t else limUnder (𝓝[goodT c s₁ e] t) (relVal c m s₁ e s₂)

/-- **The stage curve** on `[0, ∞)`: the stage values at actual time `u` (infinite lifetime) or `clockOf L u` (finite
lifetime `L`). -/
def stCurve (c : Chart) (m : ℝ) (s₁ : ExplState) (e : Drv) (s₂ : ExplState) : ℝ → ℂ :=
  fun u => stVal c m s₁ e s₂ (if e.2 = ⊤ then u else clockOf e.2.toReal u).toNNReal

theorem stVal_of_good {c : Chart} {m : ℝ} {s₁ : ExplState} {e : Drv} {s₂ : ExplState} {t : ℝ≥0}
    (ht : t ∈ goodT c s₁ e) : stVal c m s₁ e s₂ t = relVal c m s₁ e s₂ t := by
  unfold stVal
  simp only [ht, ↓reduceIte]

theorem stCurve_of_fin {c : Chart} {m : ℝ} {s₁ : ExplState} {e : Drv} {s₂ : ExplState} (he : e.2 ≠ ⊤) (u : ℝ) :
    stCurve c m s₁ e s₂ u = stVal c m s₁ e s₂ (clockOf e.2.toReal u).toNNReal := by
  unfold stCurve
  simp only [he, ↓reduceIte]

theorem stCurve_of_top {c : Chart} {m : ℝ} {s₁ : ExplState} {e : Drv} {s₂ : ExplState} (he : e.2 = ⊤) (u : ℝ) :
    stCurve c m s₁ e s₂ u = stVal c m s₁ e s₂ u.toNNReal := by
  unfold stCurve
  simp only [he, ↓reduceIte]

/-! ### The offset -/

section Offset

variable (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ)

open Classical in
/-- The first step of the actual walk adding `R` to its physical part (`0` if none). -/
def entryStage (R : ℝ) (D₁ : ℕ → Drv) : ℕ :=
  if h : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1))
  then Nat.find h else 0

/-- **The offset `o`**: the even stage at which the start configuration sits (the launch adding `R`, or the flow stage
before the connector adding `R`). -/
def startOff (R : ℝ) (D₁ : ℕ → Drv) : ℕ := 2 * (entryStage κ θ b₁ J₁ R D₁ / 2)

/-- `R` is first added by a connector (an odd step): the arc start. -/
def ArcEntry (R : ℝ) (D₁ : ℕ → Drv) : Prop := entryStage κ θ b₁ J₁ R D₁ % 2 = 1

theorem startOff_even (R : ℝ) (D₁ : ℕ → Drv) : startOff κ θ b₁ J₁ R D₁ % 2 = 0 := by
  unfold startOff; omega

theorem entryStage_spec {R : ℝ} {D₁ : ℕ → Drv}
    (h : ∃ n, (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1))) :
    (R : ℂ) ∈ statePhysicalSet 0
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (entryStage κ θ b₁ J₁ R D₁ + 1)) ∧
      ∀ n < entryStage κ θ b₁ J₁ R D₁,
        (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)) := by
  classical
  have e : entryStage κ θ b₁ J₁ R D₁ = Nat.find h := by
    unfold entryStage; simp only [h, ↓reduceDIte]
  rw [e]
  exact ⟨Nat.find_spec h, fun n hn => Nat.find_min h hn⟩

/-- At an arc start the offset is the stage before the entry; otherwise it is the entry. -/
theorem startOff_eq (R : ℝ) (D₁ : ℕ → Drv) :
    (ArcEntry κ θ b₁ J₁ R D₁ → startOff κ θ b₁ J₁ R D₁ + 1 = entryStage κ θ b₁ J₁ R D₁) ∧
      (¬ ArcEntry κ θ b₁ J₁ R D₁ → startOff κ θ b₁ J₁ R D₁ = entryStage κ θ b₁ J₁ R D₁) := by
  unfold startOff ArcEntry
  constructor <;> intro h <;> omega

/-- `R` is first added by the connector from stage `o + 1` and is a restart mark there: the connector ends at `R` and
the start is the piece launched at `R` at stage `o + 2` (`SB2LdMark.markStart`). -/
def MarkEntry (R : ℝ) (D₁ : ℕ → Drv) : Prop :=
  ArcEntry κ θ b₁ J₁ R D₁ ∧
    R ∈ GW1W.restartSet κ b₁ J₁
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (startOff κ θ b₁ J₁ R D₁ + 1))

/-- The relative stage `0` is the zero root: an arc start whose connector does not end at a mark at `R`. -/
def ZeroRoot (R : ℝ) (D₁ : ℕ → Drv) : Prop := ArcEntry κ θ b₁ J₁ R D₁ ∧ ¬ MarkEntry κ θ b₁ J₁ R D₁

open Classical in
/-- **The relative offset**: relative stage `j` is actual stage `j + relOff` — `o + 2` when `R` is the mark, `o`
otherwise. -/
def relOff (R : ℝ) (D₁ : ℕ → Drv) : ℕ :=
  startOff κ θ b₁ J₁ R D₁ + if MarkEntry κ θ b₁ J₁ R D₁ then 2 else 0

theorem relOff_even (R : ℝ) (D₁ : ℕ → Drv) : relOff κ θ b₁ J₁ R D₁ % 2 = 0 := by
  classical
  have h := startOff_even κ θ b₁ J₁ R D₁
  unfold relOff
  split_ifs <;> omega

theorem relOff_of_mark {R : ℝ} {D₁ : ℕ → Drv} (h : MarkEntry κ θ b₁ J₁ R D₁) :
    relOff κ θ b₁ J₁ R D₁ = startOff κ θ b₁ J₁ R D₁ + 2 := by
  classical
  unfold relOff
  simp only [h, ↓reduceIte]

theorem relOff_of_not_mark {R : ℝ} {D₁ : ℕ → Drv} (h : ¬ MarkEntry κ θ b₁ J₁ R D₁) :
    relOff κ θ b₁ J₁ R D₁ = startOff κ θ b₁ J₁ R D₁ := by
  classical
  unfold relOff
  simp only [h, ↓reduceIte, add_zero]

end Offset

/-! ### The concrete rule -/

section Rule

variable {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart)
  (m : ℝ) (D₁ : Ω → ℕ → Drv)

/-- The concrete stage-`j` curve read in the relative run chart (`ExplState`-level form). -/
def cΦ (j : ℕ) (ω : Ω) (s₂ : ExplState) : ℝ → ℂ :=
  stCurve c m (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω)))
    (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))) s₂

/-- **The concrete stage curves**: the lift of the actual piece launched at stage `j + relOff`, read in the relative run
chart at stage `j`. -/
def cρ (j : ℕ) (F : ℕ → Ω → Drv) (ω : Ω) : ℝ → ℂ :=
  cΦ κ θ b₁ J₁ R c m D₁ j ω (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun i => F i ω) j)

/-- **The concrete zero events**: the odd (connector) stages, and stage `0` of an arc start not ending at a mark (the
zero root). -/
def cZ (j : ℕ) (_F : ℕ → Ω → Drv) : Set Ω :=
  {ω | j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R (D₁ ω))}

/-- **The driven events**, read through the relative run at stage `j`. -/
def cG (ΦG : ℕ → Ω → ExplState → Prop) (j : ℕ) (F : ℕ → Ω → Drv) : Set Ω :=
  {ω | ΦG j ω (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun i => F i ω) j)}

/-- **The concrete rule depends only on the earlier drivers** (`hdep_of_run`). -/
theorem hdep_concrete (ΦG : ℕ → Ω → ExplState → Prop) :
    ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) →
      cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j F = cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j F' ∧
        cG κ θ b₂ J₂ ΦG j F = cG κ θ b₂ J₂ ΦG j F' ∧
        cZ κ θ b₁ J₁ R D₁ j F = cZ κ θ b₁ J₁ R D₁ j F' := by
  intro j F F' h
  obtain ⟨h1, h2, -⟩ := hdep_of_run (κ := κ) (b := b₂) (J := J₂) (boundaryWalkSpec b₂ J₂ θ true)
    (cΦ κ θ b₁ J₁ R c m D₁) ΦG (fun _ _ _ => True) j F F' h
  exact ⟨h1, h2, rfl⟩

/-- **`exists_EL_rec` applied to the concrete rule.** -/
theorem exists_EL_concrete [MeasurableSpace Ω] (ΦG : ℕ → Ω → ExplState → Prop)
    (hok : ∀ j F, (∀ i < j, Measurable (F i)) →
      StageOK (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j F) (cG κ θ b₂ J₂ ΦG j F) (cZ κ θ b₁ J₁ R D₁ j F)) :
    ∃ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      (∀ j, ∀ ω ∈ cZ κ θ b₁ J₁ R D₁ j EL, EL j ω = zeroDrv) ∧
      ∀ j, ∀ ω ∈ cG κ θ b₂ J₂ ΦG j EL, ω ∉ cZ κ θ b₁ J₁ R D₁ j EL →
        (EL j ω).2 = capLife (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω) ∧
        ∀ T < capLife (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (cρ κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω)) :=
  exists_EL_rec _ _ _ (hdep_concrete κ θ b₁ J₁ b₂ J₂ R c m D₁ ΦG) hok

end Rule

end InteractingSLE.Theorem14.SB.Lk
