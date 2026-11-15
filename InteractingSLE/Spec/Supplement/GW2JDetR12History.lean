/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR11SourceKernel

/-!
# Initial root data under every retained-history kernel

The literal switched-history sigma algebras grow along extensions.
Consequently COVER and its observed initial records remain known at every
history. Original source facts on COVER pass to each full retained kernel.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR12

open GW2TipSystem GW2TipSystem.RootC24 GW2Schedule GW2Tip Exist Staged StagedLaw

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- The exact source sigma algebras grow when a switched entry is retained. -/
theorem sigma_le_cons (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (x : EntryIdx c.Θ c.Q) :
    c.sigma r l ≤ c.sigma r (x :: l) := by
  simpa only [SourceData.sigma, rootSigma, schedSpecOf, entryList_cons] using
    stageSigma_schedOf_mono (hκ := c.hκ) (h12p := c.h12p)
      (βA := c.βA) (c₀ := c.c₀) (h := c.h) c.s c.W c.ζ
      (rootPt r.1) (rootEntry r.1) ((x.1 : ℝ), (x.2 : ℝ≥0)) (entryList l)

omit [StandardBorelSpace Ω] in
/-- No history loses the initial records, including exceptional branches. -/
theorem sigma_nil_le (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : c.sigma r [] ≤ c.sigma r l := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih => exact ih.trans (sigma_le_cons c r l x)

omit [StandardBorelSpace Ω] in
/-- COVER is known under every complete retained history. -/
theorem measurableSet_coverEvent_history (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    MeasurableSet[c.sigma r l] (RootCv.coverEvent c r) :=
  sigma_nil_le c r l _ (RootCv.measurableSet_coverEvent c r)

omit [StandardBorelSpace Ω] in
/-- The literal initial pair is measurable in every retained history. -/
theorem measurable_rootRecs_history (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    Measurable[c.sigma r l] (RootCv.rootRecs c r.1) :=
  (RootCv.measurable_rootRecs c r).mono (sigma_nil_le c r l) le_rfl

/-- An actual source fact on COVER holds under every full retained kernel
at almost every COVER state. No independence of retained curves is used. -/
theorem ae_conditional_on_cover (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) {p : Ω → Prop}
    (hp : ∀ᵐ ξ ∂c.P, ξ ∈ RootCv.coverEvent c r → p ξ) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, p ξ := by
  have hσ : c.sigma r l ≤ ‹MeasurableSpace Ω› :=
    stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hfact := Sec7.Aux122Disint.ae_ae_condExpKernel hσ hp
  have hmem := Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := c.P) hσ
    (measurableSet_coverEvent_history c r l)
  filter_upwards [hfact, hmem] with ω₀ hf hm hω₀
  filter_upwards [hf, hm hω₀] with ξ hξ hmemξ
  exact hξ hmemξ

/-- Every literal retained record is fixed under the full history kernel.
This uses the entire stage map, including the retained counterflow record. -/
theorem ae_conditional_stageMap_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
      stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
          (schedSpecOf r.1 l) ((entryList l).length + 1) ξ =
        stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
          (schedSpecOf r.1 l) ((entryList l).length + 1) ω₀ :=
  Sec7.Aux122Disint.ae_ae_condExpKernel_eq
    (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _)
    (comap_measurable (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpecOf r.1 l) ((entryList l).length + 1)))

/-- The initial observed pair stays fixed under each full retained kernel. -/
theorem ae_conditional_rootRecs_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
      RootCv.rootRecs c r.1 ξ = RootCv.rootRecs c r.1 ω₀ :=
  Sec7.Aux122Disint.ae_ae_condExpKernel_eq
    (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _)
    (measurable_rootRecs_history c r l)

end InteractingSLE.Theorem14.GW2JDetR12
