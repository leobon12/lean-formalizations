/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JtGen
import InteractingSLE.Spec.Supplement.SB2JyConc

/-!
# SB2(2): the v3 concrete stage rule (decision D6, option A; ruling R120)

Packet PROVE-SB2-LIFTSET (round 16). The v3 rule:

* **`visitTime`**: the first time a piece visits `R` (`sInf`; `0` if it does not);
* **`stageShift`**: at relative stage `0` the start piece is read from its visit time of `R` (at a mark entry the piece
  starts at `R`, so this is `0`); `0` at the other stages;
* **`cΦ3`/`cρ3`**: the stage curve `stCurvep` of the shifted point map `t ↦ pcPt s₁ e₁ (t_R + t)` on `[0, e₁.2 − t_R]`,
  read in the relative run chart at stage `j` (through the run only);
* **`cZ3`**: the zero events — odd stages, stage `0` of a zero root, and stages whose actual piece has lifetime `0`
  (D6: zero-lifetime start pieces are zero roots);
* `hdep_concrete3` (`hdep_of_run`), **`exists_EL_concrete3`** (`exists_EL_rec'`, the weak admissibility).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C GW1Bookkeep

/-- **The first time a piece visits `R`** (`0` if it does not). -/
def visitTime (s : ExplState) (e : Drv) (R : ℝ) : ℝ≥0 :=
  sInf {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e.2 ∧ pcPt s e t = (R : ℂ)}

section Rule

variable {Ω : Type*} (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (c : Chart)
  (m : ℝ) (D₁ : Ω → ℕ → Drv)

/-- **The stage shift**: the start piece's visit time of `R` at relative stage `0`, `0` at the other stages. -/
def stageShift (j : ℕ) (ω : Ω) : ℝ≥0 :=
  if j = 0 then visitTime (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω)))
    (D₁ ω (relOff κ θ b₁ J₁ R (D₁ ω))) R else 0

/-- The v3 stage-`j` curve read in a relative state `s₂` (`ExplState`-level form). -/
def cΦ3 (j : ℕ) (ω : Ω) (s₂ : ExplState) : ℝ → ℂ :=
  stCurvep c m
    (fun t => pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) (D₁ ω) (j + relOff κ θ b₁ J₁ R (D₁ ω)))
      (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))) (stageShift κ θ b₁ J₁ R D₁ j ω + t))
    ((D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 - stageShift κ θ b₁ J₁ R D₁ j ω) s₂

/-- **The v3 stage curves**: the lift of the actual piece launched at stage `j + relOff` (read from its visit time of
`R` at stage `0`), in the relative run chart at stage `j`. -/
def cρ3 (j : ℕ) (F : ℕ → Ω → Drv) (ω : Ω) : ℝ → ℂ :=
  cΦ3 κ θ b₁ J₁ R c m D₁ j ω (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun i => F i ω) j)

/-- **The v3 zero events**: odd stages, stage `0` of a zero root, and stages whose actual piece has lifetime `0`. -/
def cZ3 (j : ℕ) (_F : ℕ → Ω → Drv) : Set Ω :=
  {ω | j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R (D₁ ω)) ∨ (D₁ ω (j + relOff κ θ b₁ J₁ R (D₁ ω))).2 = 0}

/-- **The v3 rule depends only on the earlier drivers** (`hdep_of_run`). -/
theorem hdep_concrete3 (ΦG : ℕ → Ω → ExplState → Prop) :
    ∀ j (F F' : ℕ → Ω → Drv), (∀ i < j, F i = F' i) →
      cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F = cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F' ∧
        cG κ θ b₂ J₂ ΦG j F = cG κ θ b₂ J₂ ΦG j F' ∧
        cZ3 κ θ b₁ J₁ R D₁ j F = cZ3 κ θ b₁ J₁ R D₁ j F' := by
  intro j F F' h
  obtain ⟨h1, h2, -⟩ := hdep_of_run (κ := κ) (b := b₂) (J := J₂) (boundaryWalkSpec b₂ J₂ θ true)
    (cΦ3 κ θ b₁ J₁ R c m D₁) ΦG (fun _ _ _ => True) j F F' h
  exact ⟨h1, h2, rfl⟩

/-- **`exists_EL_rec'` applied to the v3 rule.** -/
theorem exists_EL_concrete3 [MeasurableSpace Ω] (ΦG : ℕ → Ω → ExplState → Prop)
    (hok : ∀ j F, (∀ i < j, Measurable (F i)) → (∀ i < j, ∀ ω, IsRegularDriver (F i ω)) →
      (∀ i < j, ∀ ω ∈ cZ3 κ θ b₁ J₁ R D₁ i F, F i ω = zeroDrv) →
      (∀ i < j, ∀ ω ∈ cG κ θ b₂ J₂ ΦG i F, ω ∉ cZ3 κ θ b₁ J₁ R D₁ i F →
        (F i ω).2 = capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω) ∧
        ∀ T < capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω),
          IsGeneratingTrace (F i ω).1 T (capTrace (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ i F ω))) →
      StageOK (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F) (cG κ θ b₂ J₂ ΦG j F) (cZ3 κ θ b₁ J₁ R D₁ j F)) :
    ∃ EL : ℕ → Ω → Drv, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      (∀ j, ∀ ω ∈ cZ3 κ θ b₁ J₁ R D₁ j EL, EL j ω = zeroDrv) ∧
      ∀ j, ∀ ω ∈ cG κ θ b₂ J₂ ΦG j EL, ω ∉ cZ3 κ θ b₁ J₁ R D₁ j EL →
        (EL j ω).2 = capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω) ∧
        ∀ T < capLife (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j EL ω)) :=
  exists_EL_rec' _ _ _ (hdep_concrete3 κ θ b₁ J₁ b₂ J₂ R c m D₁ ΦG) hok

/-- Away from stage `0` the shift is `0`. -/
theorem stageShift_of_ne {j : ℕ} (hj : j ≠ 0) (ω : Ω) : stageShift κ θ b₁ J₁ R D₁ j ω = 0 := by
  unfold stageShift; simp only [hj, ↓reduceIte]

end Rule

end InteractingSLE.Theorem14.SB.Lk
