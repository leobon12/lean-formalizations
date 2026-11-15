/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2CvProps
import InteractingSLE.Spec.Supplement.GW2RootC24Assembly

/-!
# GW2's root cover discharges the cover input of the root-test assembly

Packet PROVE-GW2-COVER. The assembly `RootC24.gw2RootTestStatement_of_oneSided_comparisons` takes the
cover as `hCover : RootC24.RootCoverStatement D` for its construction family `D`. Here:

* `withCover D`: the construction family `D` with its initial events replaced by GW2's root cover
  (`RootCv.coverEvent`); the experiments are unchanged;
* **`rootCoverStatement_withCover`**, **`rootCoverStatement_of_G_eq`**: the cover input holds for every
  construction family whose initial events are the root cover, from Theorem 1.3 (universes `u`, `0`;
  allowed for Theorem 1.4 by R48);
* the dilation scale (Prop. 5.9, p. 143, "Rescale it"; Lemma GW2's proof: "Rescale so that these
  finitely many labels … lie outside `[−3, 3]`"): `scaledCoverEvent c gap r` refines the cover event
  of `r = (x, k)` by `3 < 2ᵏ · gap x`, for any label gap `gap x` known at the root's stage start;
  **`ae_exists_mem_scaledCoverEvent`**: if the gap is almost surely positive on the cover events, the
  refined events still cover `{α(s) ∈ ℍ}`; `rootCoverStatement_withScaledCover`;
* `gw2RootTestStatement_of_cover`, `gw2RootTestStatement_of_scaledCover`: the C24 assembly with its
  cover input discharged (distinct conditional helpers; the other C24 inputs are unchanged).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootCv

open Exist RootC24

/-! ### The unscaled cover -/

/-- **The construction family with GW2's root cover** as its initial events. -/
def withCover (D : ConstructionFamily.{u}) : ConstructionFamily.{u} :=
  fun Ω _ _ c => ⟨coverEvent c, (D Ω c).experiment⟩

/-- **The cover input of the root-test assembly**, for every construction family whose initial
events are GW2's root cover. -/
theorem rootCoverStatement_of_G_eq (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0})
    (D : ConstructionFamily.{u})
    (hD : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω),
      (D Ω c).G = coverEvent c) :
    RootCoverStatement D := by
  intro Ω _ _ c
  rw [hD Ω c]
  exact ⟨ae_exists_mem_coverEvent h13 h13₀ c, measurableSet_coverEvent c⟩

/-- **The cover input of the root-test assembly for `withCover D`.** -/
theorem rootCoverStatement_withCover (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0})
    (D : ConstructionFamily.{u}) : RootCoverStatement (withCover D) :=
  rootCoverStatement_of_G_eq h13 h13₀ (withCover D) fun _ _ _ _ => rfl

/-! ### The scaled cover -/

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The cover event refined by the dilation scale**: the labels, measured by `gap x`, lie outside
`[−3, 3]` after dilation by `2ᵏ`. -/
def scaledCoverEvent (c : SourceData Ω) (gap : RootIdx c.Θ c.Q → Ω → ℝ) (r : ScaledRootIdx c.Θ c.Q) :
    Set Ω :=
  coverEvent c r ∩ {ω | 3 < 2 ^ r.2 * gap r.1 ω}

theorem scaledCoverEvent_subset (c : SourceData Ω) (gap : RootIdx c.Θ c.Q → Ω → ℝ)
    (r : ScaledRootIdx c.Θ c.Q) : scaledCoverEvent c gap r ⊆ coverEvent c r :=
  inter_subset_left

/-- The refined cover events are known at the root's stage start when the gap is. -/
theorem measurableSet_scaledCoverEvent (c : SourceData Ω) {gap : RootIdx c.Θ c.Q → Ω → ℝ}
    (hgap : ∀ r : ScaledRootIdx c.Θ c.Q, Measurable[c.sigma r []] (gap r.1)) (r : ScaledRootIdx c.Θ c.Q) :
    MeasurableSet[c.sigma r []] (scaledCoverEvent c gap r) := by
  have hm : Measurable[c.sigma r []] fun ω => 2 ^ r.2 * gap r.1 ω := (hgap r).const_mul _
  exact @MeasurableSet.inter Ω (c.sigma r []) _ _ (measurableSet_coverEvent c r) (hm measurableSet_Ioi)

/-- A positive gap is beaten by some dyadic scale. -/
theorem exists_scale {g : ℝ} (hg : 0 < g) : ∃ k : ℕ, 3 < 2 ^ k * g := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (3 / g) one_lt_two
  exact ⟨k, by rwa [div_lt_iff₀ hg] at hk⟩

variable [StandardBorelSpace Ω]

/-- **The refined cover** (Lemma GW2's proof, rescaling): if the label gap is almost surely positive
on every cover event, the refined cover events still cover `{α(s) ∈ ℍ}` almost surely. -/
theorem ae_exists_mem_scaledCoverEvent (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0})
    (c : SourceData Ω) {gap : RootIdx c.Θ c.Q → Ω → ℝ}
    (hpos : ∀ x : RootIdx c.Θ c.Q, ∀ᵐ ω ∂c.P, ω ∈ coverEvent c (x, 0) → 0 < gap x ω) :
    ∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → ∃ r : ScaledRootIdx c.Θ c.Q, ω ∈ scaledCoverEvent c gap r := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hall : ∀ᵐ ω ∂c.P, ∀ x : RootIdx c.Θ c.Q, ω ∈ coverEvent c (x, 0) → 0 < gap x ω :=
    ae_all_iff.2 hpos
  filter_upwards [ae_exists_mem_coverEvent h13 h13₀ c, hall] with ω hcov hg hsH
  obtain ⟨⟨x, k₀⟩, hω⟩ := hcov hsH
  have hω0 : ω ∈ coverEvent c (x, 0) := hω
  obtain ⟨k, hk⟩ := exists_scale (hg x hω0)
  exact ⟨(x, k), hω0, hk⟩

/-! ### The scaled construction family -/

/-- A label gap for every source setup. -/
abbrev GapFamily : Type (u + 1) :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω),
    RootIdx c.Θ c.Q → Ω → ℝ

/-- **The construction family with GW2's scaled root cover** as its initial events. -/
def withScaledCover (D : ConstructionFamily.{u}) (gap : GapFamily.{u}) : ConstructionFamily.{u} :=
  fun Ω _ _ c => ⟨scaledCoverEvent c (gap Ω c), (D Ω c).experiment⟩

/-- **The cover input of the root-test assembly for the scaled cover**, for a label gap known at
each root's stage start and almost surely positive on the cover events. -/
theorem rootCoverStatement_withScaledCover (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (D : ConstructionFamily.{u}) (gap : GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ coverEvent c (x, 0) → 0 < gap Ω c x ω) :
    RootCoverStatement (withScaledCover D gap) := fun Ω _ _ c =>
  ⟨ae_exists_mem_scaledCoverEvent h13 h13₀ c (hpos Ω c),
    measurableSet_scaledCoverEvent c (hgap Ω c)⟩

/-! ### The root-test assembly with the cover discharged -/

/-- **`RootC24`'s assembly with the cover input discharged** (a conditional helper: the geometry and
the two one-sided comparisons of the construction family `withCover D` remain inputs). -/
theorem gw2RootTestStatement_of_cover (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0})
    (D : ConstructionFamily.{u}) (hGeometry : RootGeometryStatement (withCover D))
    (hNear : RetainedNearModelsStatement (withCover D))
    (hSlow : RetainedSlowComparisonsStatement (withCover D)) :
    GW2TipSystem.GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons h13 (withCover D)
    (rootCoverStatement_withCover h13 h13₀ D) hGeometry hNear hSlow

/-- **`RootC24`'s assembly with the scaled cover input discharged**, for a label gap known at each
root's stage start and almost surely positive on the cover events. -/
theorem gw2RootTestStatement_of_scaledCover (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (D : ConstructionFamily.{u}) (gap : GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryStatement (withScaledCover D gap))
    (hNear : RetainedNearModelsStatement (withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (withScaledCover D gap)) :
    GW2TipSystem.GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons h13 (withScaledCover D gap)
    (rootCoverStatement_withScaledCover h13 h13₀ D gap hgap hpos) hGeometry hNear hSlow

end InteractingSLE.Theorem14.GW2TipSystem.RootCv
