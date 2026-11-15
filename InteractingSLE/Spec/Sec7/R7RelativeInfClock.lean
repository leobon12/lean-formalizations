/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7RelativeInfGrowth

/-!
# Continuity of the collapsed ambient own-future at infinity

PROVE-R7-GAPEQ. The proved mapped gap equalities supply RG2. Reuse the landed
clock quotient continuity theorem and restrict the unbounded clock fibers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 R7StopIn

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ}

/-- Restricting a nonterminal clock window preserves its global right fibers. -/
theorem fibreRight_restrict (hP : IsErasurePocketInf η C y₀ τ) {u S v : ℝ} (hu : 0 ≤ u)
    (hS : S < clockEnd η C τ) (hv : v ∈ Icc u S) :
    fibreRight (pocketClockInf η C τ) (pocketFibreInf η C τ u) (pocketFibreInf η C τ S) v =
      pocketFibreInf η C τ v := by
  have hv0 : 0 ≤ v := hu.trans hv.1
  have hu' : u ∈ Ico 0 (clockEnd η C τ) := ⟨hu, (hv.1.trans hv.2).trans_lt hS⟩
  have hv' : v ∈ Ico 0 (clockEnd η C τ) := ⟨hv0, hv.2.trans_lt hS⟩
  have hS' : S ∈ Ico 0 (clockEnd η C τ) := ⟨hv0.trans hv.2, hS⟩
  have hℓs := hP.clock_fibre hu'
  have hvA : pocketFibreInf η C τ v ∈ {t ∈ Icc (pocketFibreInf η C τ u) (pocketFibreInf η C τ S) |
      pocketClockInf η C τ t ≤ max v (pocketClockInf η C τ (pocketFibreInf η C τ u))} :=
    ⟨⟨hP.monotoneOn_fibre hu' hv' hv.1, hP.monotoneOn_fibre hv' hS' hv.2⟩, by
      rw [hP.clock_fibre hv']; exact le_max_left _ _⟩
  refine le_antisymm (csSup_le ⟨_, hvA⟩ fun t ht => ?_) (le_csSup ⟨_, fun t ht => ht.1.2⟩ hvA)
  rw [hℓs, max_eq_left hv.1] at ht
  by_contra h
  push Not at h
  exact absurd ht.2 (not_le.2 (hP.lt_clock_of_fibre_lt hv' h))

/-- Mapped gap equality gives a continuous collapsed own-future after every
nonterminal retained prefix. No continuity of the fiber map itself is asserted. -/
theorem continuousOn_collapsed_future (hP : IsErasurePocketInf η C y₀ τ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hgap : ∀ s a b : ℝ, τ ≤ s → s < a → a < b →
      (∀ t ∈ Icc a b, η t ∉ C) →
      a ∈ closure {t | τ < t ∧ η t ∈ C} →
      b ∈ closure {t | a < t ∧ η t ∈ C} → trMap W s a 0 = trMap W s b 0)
    {u S : ℝ} (hu : 0 ≤ u) (huS : u ≤ S) (hS : S < clockEnd η C τ) :
    ContinuousOn (fun v => trMap W (pocketFibreInf η C τ u) (pocketFibreInf η C τ v) 0)
      (Icc u S) := by
  have hu' : u ∈ Ico 0 (clockEnd η C τ) := ⟨hu, huS.trans_lt hS⟩
  have hSm : S ∈ Ico 0 (clockEnd η C τ) := ⟨hu.trans huS, hS⟩
  let s := pocketFibreInf η C τ u
  let T := pocketFibreInf η C τ S
  have hτs : τ ≤ s := hP.fibre_mem hu'
  have hs0 : 0 ≤ s := hP.fibre_nonneg hu'
  have hsT : s ≤ T := hP.monotoneOn_fibre hu' hSm huS
  have hc := continuousOn_collapsed_ownFuture hη hW hW0 hP.continuous_clock hP.monotone_clock
    hs0 hsT (S := T) (fun a ha b hb hab he hmax => ?_)
  · rw [hP.clock_fibre hu', hP.clock_fibre hSm] at hc
    exact hc.congr fun v hv => congrArg (fun t => trMap W s t 0)
      (fibreRight_restrict hP hu hS hv).symm
  · obtain ⟨havoid, hbcl, hacl⟩ := hP.maximal_fibre hτs (hP.clock_lt_of_fibre hSm)
      ha hb hab he hmax
    have hsa : s < a := by
      refine lt_of_le_of_ne ha.1 fun h => ?_
      rw [← h] at he
      exact (hP.clock_lt_of_fibre hu' b (lt_of_le_of_lt h.le hab)).ne he
    exact hgap s a b hτs hsa hab havoid
      (closure_mono (s := {t | s < t ∧ η t ∈ C}) (t := {t | τ < t ∧ η t ∈ C})
        (fun t ht => ⟨hτs.trans_lt ht.1, ht.2⟩) (hacl.resolve_left hsa.ne')) hbcl

end InteractingSLE.Sec7.R7RelativeInf

