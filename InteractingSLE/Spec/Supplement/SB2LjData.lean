/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LjRule

/-!
# SB2(2): the relative-driver data from the concrete stage rule

Packet PROVE-SB2-LIFTSET (round 12). At a later launch the concrete rule (`SB2LjRule`) is read with the actual
drivers `E (boundaryWalkSpec b jumps (-π/2) true) · ω`, the relative data `affData 1 m b'`, `affJumps 1 m J'`, the
visit point `R = realMax (upperPrefix …)`, the upper chart `c` and the shift `m`:

* `lD₁`, `lR`, **`lρ`, `lZ`, `lG`**: the concrete curves, zero events and (run-read) driven events at the launch;
* **`ConcreteRuleAt`**, **`SB2LowerConcreteRuleStatement`** (named input): some run-read driven events make the
  concrete rule admissible, and every family that is regular, `zeroDrv` on the zero events and generates the concrete
  curves on the driven ones satisfies the data clause;
* **`relStageRuleAt_of_concrete`**, `sb2LowerRelStageRuleStatement_of_concrete`: the concrete rule is a stage rule
  (`hdep_concrete`);
* **`sb2LowerRelDriverDataStatement_of_concrete`** (`exists_EL_rec`), `sb2LowerLaunchLiftStatement_of_concrete`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

universe u

section Launch

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)

/-- The actual (lower-walk) drivers at a sample. -/
abbrev lD₁ : Ω → ℕ → Drv := fun ω j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω

/-- The visit point `R` of the launch. -/
abbrev lR : ℝ := realMax (upperPrefix κ b jumps E u l k ω₀)

/-- **The concrete stage curves at the launch.** -/
abbrev lρ : ℕ → (ℕ → Ω → Drv) → Ω → ℝ → ℂ :=
  cρ κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J') (lR κ b jumps E u l k ω₀) c m (lD₁ b jumps E)

/-- **The concrete zero events at the launch.** -/
abbrev lZ : ℕ → (ℕ → Ω → Drv) → Set Ω :=
  cZ κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E)

/-- **Run-read driven events at the launch.** -/
abbrev lG (ΦG : ℕ → Ω → ExplState → Prop) : ℕ → (ℕ → Ω → Drv) → Set Ω :=
  cG κ (-(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') ΦG

end Launch

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The concrete stage rule at one launch**: for the shift `m`, driven events read through the relative run make
the concrete rule admissible when the earlier drivers are measurable, and every everywhere regular family that is
`zeroDrv` on the concrete zero events and generates the concrete curves on the driven events satisfies the data
clause. -/
def ConcreteRuleAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ ΦG : ℕ → Ω → ExplState → Prop,
    (∀ j F, (∀ i < j, Measurable (F i)) →
      StageOK (lρ κ b jumps E u l k ω₀ c b' J' m j F) (lG κ b' J' m ΦG j F) (lZ κ b jumps E u l k ω₀ j F)) ∧
    ∀ EL : ℕ → Ω → Drv, (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ lZ κ b jumps E u l k ω₀ j EL, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ lG κ b' J' m ΦG j EL, ω ∉ lZ κ b jumps E u l k ω₀ j EL →
        (EL j ω).2 = capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω) ∧
        ∀ T < capLife (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω),
          IsGeneratingTrace (EL j ω).1 T (capTrace (lρ κ b jumps E u l k ω₀ c b' J' m j EL ω))) →
      RelDataClause κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named input: SB2(2)'s concrete stage rule at the later launches.** -/
def SB2LowerConcreteRuleStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ConcreteRuleAt κ b jumps P E u l k ω₀ c b' J'

/-- **The concrete rule is a stage rule** (its dependence on the earlier drivers is `hdep_concrete`). -/
theorem relStageRuleAt_of_concrete {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ}
    (h : ConcreteRuleAt κ b jumps P E u l k ω₀ c b' J') : RelStageRuleAt κ b jumps P E u l k ω₀ c b' J' := by
  intro m hm
  obtain ⟨ΦG, hok, hcl⟩ := h m hm
  exact ⟨_, _, _, hdep_concrete _ _ _ _ _ _ _ _ _ _ ΦG, hok, hcl⟩

/-- The concrete rule gives SB2(2)'s stage rule. -/
theorem sb2LowerRelStageRuleStatement_of_concrete (hS : SB2LowerConcreteRuleStatement.{u}) :
    SB2LowerRelStageRuleStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk
  exact relStageRuleAt_of_concrete (h₀ c θ hlaunch b' J' h' hb' hT' hG' hk)

/-- **The head-free relative-driver data from the concrete rule** (`EL` built by `exists_EL_rec`). -/
theorem sb2LowerRelDriverDataStatement_of_concrete (hS : SB2LowerConcreteRuleStatement.{u}) :
    SB2LowerRelDriverDataStatement.{u} :=
  sb2LowerRelDriverDataStatement_of_rule (sb2LowerRelStageRuleStatement_of_concrete hS)

/-- **SB2(2)'s combined target (R104a) from the concrete rule and the conditional half** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_concrete (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerConcreteRuleStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_rule h12 h13 h12₀ h13₀ (sb2LowerRelStageRuleStatement_of_concrete hS) hcond

end InteractingSLE.Theorem14.SB.Lk
