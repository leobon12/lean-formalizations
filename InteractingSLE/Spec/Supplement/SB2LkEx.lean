/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkLink
import InteractingSLE.Spec.Supplement.SB2LkUnique

/-!
# SB2(2)'s erasure identity for one relative walk suffices

Packet PROVE-T14-SB2LIFT. `Lk.SB2LowerTailLiftIdentStatement` asks for the lift onto the walk of EVERY regular staged
lower walk of the conditional field. By the uniqueness of staged histories of one field (`SB2LkUnique`,
Theorem 1.2 piece by piece) all of them have almost surely the same physical set, so it suffices that SOME regular
staged lower walk of the conditional field carries the lift — the source's form ("the actual completed lower tail
… is again a finite simple proper lower walk of the retained conditional field"):

* `TailLiftEx`, **`SB2LowerTailLiftExStatement`** (named input): at the later launches, some regular staged lower walk
  of the conditional field has the actual lower tail lifted onto its walk;
* **`sb2LowerTailLiftIdentStatement_of_ex`**, **`sb2LowerLaunchLiftStatement_of_liftEx`**: SB2(2)'s combined target
  (R104a) at every launch from Theorems 1.2–1.3 and that input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw

/-- **The lift for one relative walk**: for `m = −e_R` there is a regular staged lower walk `EL` of the conditional
field (frame `affField m h'`) such that, almost surely under the retained kernel, the tail after `R` of every proper
parametrization of the actual lower walk lifts onto `EL`'s walk. -/
def TailLiftEx (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL ∧
    StagedPiecesRegular κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (relLowerSpec b' J' m) EL ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **Named input: SB2(2)'s erasure identity for one relative walk at the later launches** (supplement p. 631:
"Erase `B` through its unique visit to `R` and lift the remaining tail into `D_A`. The result is again a finite simple
proper lower walk of the retained conditional field"; p. 632: "the actual completed lower tail has an injective,
proper lift"). -/
def SB2LowerTailLiftExStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → TailLiftEx κ b jumps P E u l k ω₀ c b' J' h'

/-- **The lift for one relative walk gives the lift for every one** (uniqueness of staged histories of one field,
under the retained kernel). -/
theorem sb2LowerTailLiftIdentStatement_of_ex (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hex : SB2LowerTailLiftExStatement.{u}) :
    SB2LowerTailLiftIdentStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hex κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hex₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hst hreg
  obtain ⟨EL₀, hst₀, hreg₀, hlift₀⟩ := hex₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hsame := ae_physSet_eq_of_isStagedHistory_of_thm12_thm13 h12 h13 h12₀ h13₀ hκ hb'' hst₀ hreg₀ hst hreg
  filter_upwards [hlift₀, hsame] with ω hlω hsω
  intro β₀ hβ hβ0 hβr
  have h1 := hlω β₀ hβ hβ0 hβr
  have hW : relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL₀ ω =
      relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω := hsω
  rwa [hW] at h1

/-- **SB2(2)'s combined target (R104a) from the erasure identity for one relative walk** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_liftEx (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hex : SB2LowerTailLiftExStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_liftIdent h12 h13 h12₀ h13₀
    (sb2LowerTailLiftIdentStatement_of_ex h12 h13 h12₀ h13₀ hex)

end InteractingSLE.Theorem14.SB.Lk
