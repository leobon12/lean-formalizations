/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KM2PostStop
import InteractingSLE.Spec.Supplement.GW2JDetCode

/-!
# Canonical GW2 stages stopped by functions of their killed paths

Iterate the landed one-stage stopping-time law while retaining the initial
record and every stopped piece. The stopping rules may depend on the entire
past. This construction concerns the canonical joint-chart experiment; its
identification with the physical relative exploration is a separate issue.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u v

namespace InteractingSLE.Theorem14.GW2JDetR5

open Restart Exist Exist.Staged Exist.StagedLaw GW2Schedule GW2KM2

/-- The initial retained record followed by all the stopped piece records. -/
def Past (S : Type v) : ℕ → Type v
  | 0 => S
  | n + 1 => Past S n × RecData

instance pastMeasurableSpace {S : Type v} [mS : MeasurableSpace S] :
    (n : ℕ) → MeasurableSpace (Past S n)
  | 0 => mS
  | n + 1 => by
    let _ := pastMeasurableSpace (S := S) n
    change MeasurableSpace (Past S n × RecData)
    infer_instance

instance pastStandardBorelSpace {S : Type v} [MeasurableSpace S]
    [StandardBorelSpace S] : (n : ℕ) → StandardBorelSpace (Past S n)
  | 0 => inferInstanceAs (StandardBorelSpace S)
  | n + 1 => by
    let _ := pastStandardBorelSpace (S := S) n
    change StandardBorelSpace (Past S n × RecData)
    infer_instance

variable {S : Type v} {κ : ℝ}

/-- Read the current finite boundary word from the complete retained past. -/
def stageWord (W₀ : S → BoundaryWord) (θ : ℕ → ℝ) :
    (n : ℕ) → Past S n → BoundaryWord
  | 0 => W₀
  | n + 1 => fun x => stopWord κ (stageWord W₀ θ n x.1, θ n, x.2)

/-- Retain only the initial live event and finiteness of earlier records. -/
def finitePast (A : Set S) : (n : ℕ) → Set (Past S n)
  | 0 => A
  | n + 1 => {x | x.1 ∈ finitePast A n ∧ x.2.2.1 ≠ ⊤}

theorem isSorted_stageWord {W₀ : S → BoundaryWord} (hW₀ : ∀ x, (W₀ x).IsSorted)
    (θ : ℕ → ℝ) : ∀ n (x : Past S n), (stageWord (κ := κ) W₀ θ n x).IsSorted
  | 0, x => hW₀ x
  | _ + 1, _ => isSorted_stopWord _ _

variable [MeasurableSpace S]

theorem measurable_stageWord {W₀ : S → BoundaryWord} (hW₀ : Measurable W₀)
    (θ : ℕ → ℝ) : ∀ n, Measurable (stageWord (κ := κ) W₀ θ n)
  | 0 => hW₀
  | n + 1 => by
    change Measurable fun x : Past S n × RecData =>
      stopWord κ (stageWord W₀ θ n x.1, θ n, x.2)
    exact (measurable_stopWord κ).comp
      (((measurable_stageWord hW₀ θ n).comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))

theorem measurableSet_finitePast {A : Set S} (hA : MeasurableSet A) :
    ∀ n, MeasurableSet (finitePast A n)
  | 0 => hA
  | n + 1 => by
    change MeasurableSet {x : Past S n × RecData |
      x.1 ∈ finitePast A n ∧ x.2.2.1 ≠ ⊤}
    exact ((measurableSet_finitePast hA n).preimage measurable_fst).inter
      (measurableSet_eq_fun
        (measurable_fst.comp (measurable_snd.comp measurable_snd)) measurable_const).compl

variable (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
    (W₀ : S → BoundaryWord) (θ : ℕ → ℝ)
    (τ : (n : ℕ) → Past S n → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞)
    {Ω : Type u} (p : Ω → S) (F : Ω → DistOn upperHalfPlaneOpens)

/-- The full past and the field read in the current stopped-record chart. -/
def stageState : (n : ℕ) → Ω → Past S n × DistOn upperHalfPlaneOpens
  | 0 => fun ω => (p ω, F ω)
  | n + 1 => fun ω =>
    let x := stageState n ω
    let E := wordDrv hκ h12p (θ n) (stageWord (κ := κ) W₀ θ n x.1) x.2
    let R := recOf (τ n x.1 E) E
    ((x.1, R), recField κ R x.2)

/-- The measurable canonical piece launched from the current field. -/
def stagePiece (n : ℕ) (ω : Ω) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  wordDrv hκ h12p (θ n)
    (stageWord (κ := κ) W₀ θ n (stageState hκ h12p W₀ θ τ p F n ω).1)
    (stageState hκ h12p W₀ θ τ p F n ω).2

variable [MeasurableSpace Ω]

theorem measurable_stageState (hW₀ : Measurable W₀) (hp : Measurable p)
    (hF : Measurable F)
    (hτ : ∀ n, Measurable fun x : Past S n × ((ℝ≥0 → ℝ) × ℝ≥0∞) =>
      τ n x.1 x.2) : ∀ n, Measurable (stageState hκ h12p W₀ θ τ p F n)
  | 0 => hp.prodMk hF
  | n + 1 => by
    have hx := measurable_stageState hW₀ hp hF hτ n
    have hr := measurable_stageRec hκ h12p (θ n) (measurable_stageWord (κ := κ) hW₀ θ n)
      (measurable_fst.comp hx) (measurable_snd.comp hx) (hτ n)
    exact ((measurable_fst.comp hx).prodMk hr).prodMk
      (measurable_recField_comp κ hr (measurable_snd.comp hx))

theorem measurable_stagePiece (hW₀ : Measurable W₀) (hp : Measurable p)
    (hF : Measurable F)
    (hτ : ∀ n, Measurable fun x : Past S n × ((ℝ≥0 → ℝ) × ℝ≥0∞) =>
      τ n x.1 x.2) (n : ℕ) : Measurable (stagePiece hκ h12p W₀ θ τ p F n) := by
  have hx := measurable_stageState hκ h12p W₀ θ τ p F hW₀ hp hF hτ n
  exact measurable_stageDrv hκ h12p (θ n) (measurable_stageWord (κ := κ) hW₀ θ n)
    (measurable_fst.comp hx) (measurable_snd.comp hx)

omit [MeasurableSpace S] [MeasurableSpace Ω] in
theorem isRegularDriver_stagePiece (n : ℕ) (ω : Ω) :
    IsRegularDriver (stagePiece hκ h12p W₀ θ τ p F n ω) :=
  isRegularDriver_wordDrv hκ h12p (θ n) _ _

end InteractingSLE.Theorem14.GW2JDetR5
