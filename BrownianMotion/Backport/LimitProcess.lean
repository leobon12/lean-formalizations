/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/

-- PORT (interacting_sle, ruling R20): backported from Mathlib commit
-- e91b128082cc221d6432a6a5aadcd3243af8e76c, `Mathlib/Probability/Process/LimitProcess.lean`
-- (Apache-2.0), which is newer than this project's Mathlib a4c8ef0a. Only the declarations the
-- vendored modules use are kept: `HasLimitProcess`, `HasLimitProcess.congr`,
-- `hasLimitProcess_congr_iff`, `limitProcess_ae_eq`, `limitProcess_congr`. They are stated for
-- the `Filtration.limitProcess` that Mathlib a4c8ef0a already defines
-- (`Mathlib/Probability/Process/Filtration.lean`), whose body is the newer one with
-- `HasLimitProcess` unfolded; the proofs unfold that predicate where the newer ones rewrite
-- with it.
module

public import Mathlib.Probability.Process.Filtration
public import BrownianMotion.Backport.Indistinguishable
-- PORT (interacting_sle, ruling R20): the upstream package options, set per file.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Limit process (backport)

`HasLimitProcess X 𝓕 P` states that `X` converges `P`-almost surely towards a
`⨆ t, 𝓕 t`-strongly measurable function; `𝓕.limitProcess X P` (Mathlib) chooses that limit.
-/

public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace MeasureTheory.Filtration

variable {ι Ω E : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω} [TopologicalSpace E]
  {P : Measure Ω} {𝓕 : Filtration ι mΩ} {X Y : ι → Ω → E} {g : Ω → E}

/-- A stochastic process `X` satisfies `𝓕.HasLimitProcess X P` if it converges `P`-almost surely
towards a `⨆ t, 𝓕 t`-strongly measurable random variable. -/
@[expose]
def HasLimitProcess (X : ι → Ω → E) (𝓕 : Filtration ι mΩ) (P : Measure Ω) : Prop :=
  ∃ g : Ω → E, StronglyMeasurable[⨆ t, 𝓕 t] g ∧ ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))

lemma HasLimitProcess.congr (h : X ≡ᵐ[P] Y) (hX : HasLimitProcess X 𝓕 P) :
    HasLimitProcess Y 𝓕 P := by
  obtain ⟨g, mg, hg⟩ := hX
  refine ⟨g, mg, ?_⟩
  filter_upwards [h, hg] with ω h1 h2
  simp_all

lemma hasLimitProcess_congr_iff (h : X ≡ᵐ[P] Y) :
    HasLimitProcess X 𝓕 P ↔ HasLimitProcess Y 𝓕 P where
  mp h' := h'.congr h
  mpr h' := h'.congr h.symm

variable [IsDirectedOrder ι] [Nonempty ι] [T2Space E] [Zero E]

/-- If `X` converges almost surely towards `g` a `⨆ t, 𝓕 t`-strongly measurable function,
then `g` is almost surely equal to `𝓕.limitProcess X P`. -/
lemma limitProcess_ae_eq (mg : StronglyMeasurable[⨆ t, 𝓕 t] g)
    (hg : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (g ω))) :
    𝓕.limitProcess X P =ᵐ[P] g := by
  have this : HasLimitProcess X 𝓕 P := ⟨g, mg, hg⟩
  unfold HasLimitProcess at this
  rw [limitProcess, dite_eq_left this]
  filter_upwards [hg, this.choose_spec.2] with ω h1 h2 using tendsto_nhds_unique h2 h1

omit [Nonempty ι] in
@[gcongr]
lemma limitProcess_congr (hXY : X ≡ᵐ[P] Y) :
    𝓕.limitProcess X P =ᵐ[P] 𝓕.limitProcess Y P := by
  obtain h | _ := isEmpty_or_nonempty ι
  · have : X = Y := by ext i; exact h.elim' i
    rw [this]
  rw [limitProcess]
  split_ifs with h
  · symm
    apply limitProcess_ae_eq h.choose_spec.1
    filter_upwards [h.choose_spec.2, hXY] with ω h1 h2 using h1.congr h2
  · have h' : ¬ HasLimitProcess Y 𝓕 P := (hasLimitProcess_congr_iff hXY).not.1 h
    unfold HasLimitProcess at h'
    rw [limitProcess, dite_eq_right h']

end MeasureTheory.Filtration
