/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AssemblyLower
import InteractingSLE.Spec.Supplement.SBS3CanonComp

/-!
# Lemma S3 for SB2(2)'s lower walk: the walk-form interface (proposed)

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3 with the roles of the histories exchanged, supplement p. 631).
PROVE-T14-S3's `LowerRationalProtectedWordStatement` takes the second history to be one charted lower piece. Lemma
S3's geometry (S2's lift, the joint unbounded domain, the second map-out) needs a second history that is a proper
curve from `0` with the old history on one closed side, and a hull touching `ℝ`; for SB2(2) this is the lower walk
itself (a proper parametrization `β₀` from `0`, after its visit to `R = max (A ∩ ℝ)`). Before `t_R` the walk lies in
the old filled hull (`Lk.s2HullRight`), where the joint domain of S3 does not reach. This file states that form:

* **`LowerWalkProtectedWordStatement`** (named input): the marked comparison on rational common arcs of `β₀` after
  `t_R`, with an upper-schedule label and the right height of angle `−π/2` as the exposed second value; its geometric
  fields are supplied by `exists_s3_geometry_lower` (with `runChart_package`);
* `SB2LowerWalkTailNoCommonArcStatement`: the S3 conclusion for the walk's tail;
* `no_common_tail_arc_of_rational`, **`sb2LowerWalkTailNoCommonArcStatement_of_walkProtectedWord`**: the strict
  height contradiction (`ProtectedWordComparison.false_lower`) and the rational intersection under each kernel.

`Lk.SB2LowerNoCommonArcStatement` (all pieces, all times) has no consumer in the repository; its pre-`t_R` part is not
covered by Lemma S3's argument.

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.S3.Canon

open Exist.Staged Exist.StagedLaw Lu LuM
open Supp9B (IsProperCurve)

/-- **Named input (proposed lower form of Lemma S3; not discharged here).** The marked comparison of SB2(2) on each
rational compact common arc of the **lower walk itself**, after its visit `t_R` to `R = max (A ∩ ℝ)`: for every
proper parametrization `β₀` of the actual lower walk from `0`, under the retained upper kernel. The second history is
the walk prefix `β₀([0, q₂])` (a local set, hull `fill β₀[0, q₂]`), not a single charted piece; the old word carries
an upper-schedule label and the exposed second value is the right height of angle `−π/2`. All deterministic geometry
of such a comparison is `exists_s3_geometry_lower` (with `runChart_package` for the walk's run chart). -/
def LowerWalkProtectedWordStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
    ∀ q₁ q₂ : ℚ,
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ tR : ℝ≥0, β₀ tR = (realMax (upperPrefix κ b jumps E u l k ω₀) : ℂ) →
        tR < (q₁ : ℝ).toNNReal → (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
        β₀ '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ upperPrefix κ b jumps E u l k ω₀ →
        ∃ d : ProtectedWordComparison κ (sleLambda κ - (-(Real.pi / 2)) * chiC κ)
          (upperPrefix κ b jumps E u l k ω₀) β₀ (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal,
          Lh.SideH κ l (d.word.fn d.coordinate)

/-- **Lemma S3 for the lower walk's tail** (SB2(2), supplement p. 631: after its unique visit to `R` the lower walk
shares no open arc with the retained upper history), in the form produced by `LowerWalkProtectedWordStatement`. -/
def SB2LowerWalkTailNoCommonArcStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ tR : ℝ≥0, β₀ tR = (realMax (upperPrefix κ b jumps E u l k ω₀) : ℂ) →
        ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β₀ '' Ioo s₁ s₂ ⊆ upperPrefix κ b jumps E u l k ω₀

/-- Every common open interval after `t_R` contains a rational closed interval after `t_R`. -/
theorem no_common_tail_arc_of_rational {β : ℝ≥0 → ℂ} {A : Set ℂ} {tR : ℝ≥0}
    (hQ : ∀ q₁ q₂ : ℚ, tR < (q₁ : ℝ).toNNReal → (q₁ : ℝ).toNNReal < (q₂ : ℝ).toNNReal →
      ¬ β '' Icc (q₁ : ℝ).toNNReal (q₂ : ℝ).toNNReal ⊆ A) :
    ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ A := by
  intro s₁ s₂ hR hs hA
  obtain ⟨q₁, hs₁, hq₁⟩ := Supp9.W0b.exists_rat_btwn_nnreal hs
  obtain ⟨q₂, hq₁₂, hq₂⟩ := Supp9.W0b.exists_rat_btwn_nnreal hq₁
  apply hQ q₁ q₂ (hR.trans_lt hs₁) hq₁₂
  rintro z ⟨t, ht, rfl⟩
  exact hA ⟨t, ⟨hs₁.trans_le ht.1, ht.2.trans_lt hq₂⟩, rfl⟩

/-- **The lower walk's tail has no common open arc with the upper history**, from the walk-form marked comparison
(the strict height contradiction `ProtectedWordComparison.false_lower` and the countable rational intersection under
each retained kernel). -/
theorem sb2LowerWalkTailNoCommonArcStatement_of_walkProtectedWord
    (hW : LowerWalkProtectedWordStatement.{u}) : SB2LowerWalkTailNoCommonArcStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hl hlθ hL hleft
  filter_upwards [hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER
    u l k hu hl hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  have hall := ae_all_iff.2 fun q₁ => ae_all_iff.2 (h₀ c θ hlaunch b' J' h' hb' hT' hG' q₁)
  filter_upwards [hall] with ω hω
  intro β₀ hβ hβ0 hrange tR htR
  refine no_common_tail_arc_of_rational fun q₁ q₂ hR hq hA => ?_
  obtain ⟨d, hlabel⟩ := hω q₁ q₂ β₀ hβ hβ0 hrange tR htR hR hq hA
  exact d.false_lower hκ hκ4 (fun p hp => (hlθ p hp).1) hlabel

end InteractingSLE.Theorem14.SB.S3.Canon
