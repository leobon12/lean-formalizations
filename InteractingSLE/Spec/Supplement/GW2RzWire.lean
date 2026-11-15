/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzSched
import InteractingSLE.Spec.Supplement.GW2SdxPair


/-!
# GW2 at a root `x`: the wiring to SDE's `VPkgXSafe` (decision D8, layer 6)

Packet PROVE-GW2-ROOTX, round 3. SDE's successor pair `GW2Sdx.VPairInputsX` asks `VPkgXSafe` of the version-indexed
packages: on every time-ordered history, every near slot (for all large `m`) and every slow slot generates the
retained σ-algebra and is safe. With the root-`x` engine (`GW2Sde.StageInst.GoodX.generates_isSafe`) this reduces to
the instances being good at their root points; at roots where no root-`x` instance applies (a negative root point,
`s = 0`; the alive events are null there) the slot may be the trivially safe variable:

* `hasRelSafe_empty` (K2's safe law on the empty record event), `trivVar`, **`trivVar_generates_isSafe`**;
* `SafeSlotX`, `SafeSlotX.generates_isSafe`, **`vpkgXSafe_of_safeSlots`**.

The `driverId` field's analytic input at a root is `GW2Rz.ae_hull_version_rootX` (BUF's
`GW2Bf.ae_j32Read_eq_of_hull`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rz

open Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.Q3Stop GW2Rd GW2Sde GW2Sdi GW2Sdx GW2KM2
  GW2TipSystem GW2TipSystem.RootC24

/-! ### A trivially safe stage variable -/

/-- **K2's safe law on the empty record event**: the conditioned law is the zero measure. -/
theorem hasRelSafe_empty (k : ℝ) (w : WordType) (β : RecData → BoundaryWord) (μ : Measure CanonSpace) :
    HasRelSafe k w β ∅ μ := by
  have he : typeEvent k w β ∅ = ∅ := by
    ext y
    simp only [typeEvent, empty_inter, preimage_empty, mem_empty_iff_false]
  unfold HasRelSafe
  rw [he, cond_empty]
  refine ⟨fun ψ q D _ _ => ?_, fun s Fb _ D _ _ f Ξ => ?_, ?_, fun φ => integrable_zero_measure⟩
  · simp only [Measure.restrict_zero, integral_zero_measure]
  · simp only [Measure.restrict_zero, integral_zero_measure, mul_zero]
  · simp only [ae_zero, Filter.eventually_bot]

section Triv

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The trivially safe stage variable** after a history: the retained record, the empty record event, a zero
relative driver with a constant cap and stop. It is the stage variable of a root where no root-`x` instance applies
(a negative root point or `s = 0`), where the alive events are null. -/
def trivVar (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) : StageVar Ω where
  record := GW2Rd.stageEncRec c r l
  β := fun _ => c.c₀
  E := ∅
  Hr := fun _ => 0
  R := fun _ _ => 0
  V := fun _ => 1
  ρ := fun _ => 1
  ρs := fun _ _ => 0
  stop := fun _ => 1
  stopRule := fun _ _ => 1

/-- **The trivial stage variable generates the retained σ-algebra and is safe.** -/
theorem trivVar_generates_isSafe (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    (trivVar c r l).Generates (𝒢 := c.sigma r l) c.P ∧
      (trivVar c r l).IsSafe c.κ c.P (trivVar c r l).record := by
  have hrec : Measurable (trivVar c r l).record := measurable_stageEncRec c r l
  have hcomap : MeasurableSpace.comap (trivVar c r l).record inferInstance = c.sigma r l :=
    GW2Rd.comap_stageEncRec_sigma c r l
  refine ⟨⟨hrec, hcomap.le.trans (LocalSets.le_aeSigma _ _), hcomap.symm.le.trans (LocalSets.le_aeSigma _ _)⟩,
    ⟨measurable_const, MeasurableSet.empty, ?_, fun _ h => absurd h (notMem_empty _), measurable_const,
      fun _ => measurable_const, fun _ => continuous_const, fun _ => rfl, measurable_const,
      fun w => hasRelSafe_empty _ w _ _, ae_of_all _ fun _ h => absurd h (notMem_empty _), measurable_const,
      fun _ _ _ _ => rfl, ae_of_all _ fun _ => rfl, fun _ => measurable_const, fun _ _ _ _ _ => rfl,
      fun _ _ => ENNReal.zero_ne_top, fun _ => monotone_const, ae_of_all _ fun _ h => absurd h (notMem_empty _),
      ae_of_all _ fun _ h => absurd h (notMem_empty _), fun _ t => ?_, measurable_const, ae_of_all _ fun _ => rfl,
      ae_of_all _ fun _ h => absurd h (notMem_empty _), ae_of_all _ fun _ h => absurd h (notMem_empty _)⟩⟩
  · refine (countable_singleton (wordType c.κ c.c₀)).mono ?_
    rintro _ ⟨y, rfl⟩
    rfl
  · change MeasurableSet[pathKilledSigma t] {e : (ℝ≥0 → ℝ) × ℝ≥0∞ | (1 : ℝ≥0∞) ≤ t}
    by_cases ht : (1 : ℝ≥0∞) ≤ t
    · simp only [ht, ofPred_true, MeasurableSet.univ]
    · simp only [ht, ofPred_false, MeasurableSet.empty]

end Triv

/-! ### The wiring to `VPkgXSafe` -/

/-- **A safe slot at a history**: the trivial stage variable, or the stage variable of an instance that is good at
some root point with a good physical stop. -/
def SafeSlotX {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (v : StageVar Ω) : Prop :=
  v = trivVar c r l ∨ ∃ (I : StageInst Ω) (st : StageStop Ω) (x₀ : ℝ),
    v = I.varX c r l x₀ st ∧ I.GoodX c r l x₀ ∧ st.GoodX I c r l x₀

/-- **The root-`x` engine on a slot**: a safe slot generates the retained σ-algebra and is safe. -/
theorem SafeSlotX.generates_isSafe {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω}
    {r : ScaledRootIdx c.Θ c.Q} {l : List (EntryIdx c.Θ c.Q)} {v : StageVar Ω} (h : SafeSlotX c r l v) :
    v.Generates (𝒢 := c.sigma r l) c.P ∧ v.IsSafe c.κ c.P v.record := by
  rcases h with rfl | ⟨I, st, x₀, rfl, hI, hst⟩
  · exact trivVar_generates_isSafe c r l
  · exact hI.generates_isSafe hst

/-- **`VPkgXSafe` from root-`x` instances** (decision D8's wiring to SDE's `GW2Sdx.VPairInputsX`, field `safe`): if
on every time-ordered history every near slot (for all large `m`) and every slow slot is a safe slot — the stage
variable of an instance good at its root point with a good stop, or the trivial variable — the package is safe. -/
theorem vpkgXSafe_of_safeSlots (V : VPkgXFamily.{u})
    (hnear : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)), HistOrdered c r l → ∀ n : ℕ, ∀ᶠ m in atTop,
        ∀ a : ℕ, SafeSlotX c r l ((V Ω c r).nearVar l n m a))
    (hslow : ∀ (n : ℕ) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (k : ℕ) (l : List (EntryIdx c.Θ c.Q)), l.length = 2 * k + 4 →
        HistOrdered c r l → ∀ a : ℕ, SafeSlotX c r l ((V Ω c r).slowVar l a n)) :
    VPkgXSafe V :=
  ⟨fun Ω _ _ c r l hl n => (hnear Ω c r l hl n).mono fun _ h a => (h a).generates_isSafe,
    fun n Ω _ _ c r k l hlen hl a => (hslow n Ω c r k l hlen hl a).generates_isSafe⟩

end InteractingSLE.Theorem14.GW2Rz
