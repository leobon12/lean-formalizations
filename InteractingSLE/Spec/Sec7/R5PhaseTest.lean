/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5PhaseRef
import InteractingSLE.Spec.Sec7.PhaseContR7
import InteractingSLE.Spec.Sec7.Aux29CorChart

/-!
# Lemma R.5 on a change-pocket test: the base chart's analytic data

Packet PROVE-R5-PHASE. The deterministic inputs of `R5Phase.pocketStopPhaseSideLimit_of_incrementLaws_offExc` for the
pocket chart of a Jordan coordinate shifted by an integer branch `n` (`PocketStopField.shiftChart`, lift `− 2πn`):

* **`shiftChart_aux29Facts`** (any open pocket in `ℍ` with a Jordan coordinate, bounded or opening at the seed): the
  chart is conformal with the analytic lift `pLog − 2πin`, its inverse extends continuously to `ℍ̄`, and its
  composition with `mob` has a limit at `∞`;
* `shiftChart_dom_facts`: conformal, domain the pocket, forward map the coordinate;
* `isOpen_H_diff_regHull`: the reference domains are open.

Margin- and word-independent. Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Bornology
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Phase

open PocketStopField PocketStopSide Aux29Cor PocketStopWallsFin

variable {Ω : Type*}

/-- The Jordan alternatives of a pocket coordinate (bounded pocket with a pole, or pocket opening at `∞`). -/
def IsJordanCases (C : Set ℂ) (ψ : ℂ → ℂ) : Prop :=
  (∃ pole seed : ℂ, IsBounded C ∧ pole ∉ C ∧ Sec6.IsJordanCoord C pole seed ψ) ∨
    ∃ seed : ℂ, Sec6.IsJordanCoordInf C seed ψ

theorem IsJordanCases.isConformalBijection {C : Set ℂ} {ψ : ℂ → ℂ} (h : IsJordanCases C ψ) :
    IsConformalBijection ψ C H := by
  rcases h with ⟨_, _, _, _, hJ⟩ | ⟨_, hJ⟩
  · exact hJ.2.2.2.1
  · exact hJ.2.2.2.1

/-- On the event, the shifted pocket chart is conformal, has the pocket as domain and the coordinate as forward
map. -/
theorem shiftChart_dom_facts {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (n : Ω → ℤ) :
    ∀ ω ∈ A, (shiftChart (pChart A C ψ ω) (n ω)).IsConformal ∧
      ((shiftChart (pChart A C ψ ω) (n ω)).dom : Set ℂ) = C ω ∧
      EqOn (shiftChart (pChart A C ψ ω) (n ω)).1 (ψ ω) (C ω) := by
  intro ω hω
  have hprops := pChart_props hCo hCH hψ ω
  refine ⟨hprops.2.2.1, ?_, fun z _ => ?_⟩
  · change ((pChart A C ψ ω).dom : Set ℂ) = _
    rw [hprops.2.2.2]
    ext z
    simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
  · change pFwd A ψ ω z = _
    rw [pFwd_of_mem hω]

/-- **The base chart's analytic data for Aux. 29** (inputs `hc`, `hcExt`, `hcInf` of
`pocketStopPhaseSideLimit_of_incrementLaws_offExc`), for the pocket chart of a Jordan coordinate shifted by any
integer branch. -/
theorem shiftChart_aux29Facts {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hCH : ∀ ω ∈ A, C ω ⊆ H) (hJ : ∀ ω ∈ A, IsJordanCases (C ω) (ψ ω)) (n : Ω → ℤ) :
    (∀ ω ∈ A, (shiftChart (pChart A C ψ ω) (n ω)).IsConformal ∧
      IsDerivLog (shiftChart (pChart A C ψ ω) (n ω)).1
        (fun z => pLog A C ψ ω z - (n ω : ℂ) * (2 * Real.pi * Complex.I))
        (shiftChart (pChart A C ψ ω) (n ω)).dom ∧
      ∀ z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom, (shiftChart (pChart A C ψ ω) (n ω)).2.2 z =
        (pLog A C ψ ω z - (n ω : ℂ) * (2 * Real.pi * Complex.I)).im) ∧
    (∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (shiftChart (pChart A C ψ ω) (n ω)).2.1 H ∧ ContinuousOn E Hbar) ∧
    ∀ ω ∈ A, ∃ p : ℂ, Tendsto (fun w => mob ((shiftChart (pChart A C ψ ω) (n ω)).2.1 w))
      (cobounded ℂ ⊓ 𝓟 H) (𝓝 p) := by
  have hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H := fun ω hω => (hJ ω hω).isConformalBijection
  have hfacts := shiftChart_dom_facts hCo hCH hψ n
  have hext : ∀ ω ∈ A, (∃ seed : ℂ, (∃ pole : ℂ, IsBounded (C ω) ∧ pole ∉ C ω ∧
      Sec6.IsJordanCoord (C ω) pole seed (ψ ω)) ∨ Sec6.IsJordanCoordInf (C ω) seed (ψ ω)) := by
    intro ω hω
    rcases hJ ω hω with ⟨pole, seed, hb, hp, hJc⟩ | ⟨seed, hJc⟩
    · exact ⟨seed, Or.inl ⟨pole, hb, hp, hJc⟩⟩
    · exact ⟨seed, Or.inr hJc⟩
  refine ⟨fun ω hω => ⟨(hfacts ω hω).1, ?_, fun z _ => ?_⟩, fun ω hω => ?_, fun ω hω => ?_⟩
  · rw [(hfacts ω hω).2.1]
    exact isDerivLog_sub_int (isDerivLog_pLog hCo hψ hω) (n ω)
  · rw [im_sub_int_mul]
    rfl
  · obtain ⟨seed, hseed⟩ := hext ω hω
    obtain ⟨E, hE, hEc, -⟩ := exists_inverse_extension_of_jordan_cases hseed (hfacts ω hω).1 (hfacts ω hω).2.1
      (hfacts ω hω).2.2
    exact ⟨E, hE, hEc⟩
  · obtain ⟨seed, hseed⟩ := hext ω hω
    have hinv : (shiftChart (pChart A C ψ ω) (n ω)).2.1 = Function.invFunOn (ψ ω) (C ω) := by
      change pInv A C ψ ω = _
      rw [pInv_of_mem hω]
    rw [hinv]
    exact exists_tendsto_mob_invFunOn (hCH ω hω) hseed

/-- The reference domains `ℍ ∖ R_s` are open. -/
theorem isOpen_H_diff_regHull (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0) (ω : Ω) :
    IsOpen (H \ regHull W ζ s ω) :=
  QuantumZipper.FwdHolo.isOpen_compl_fwdHull ((continuous_regDrv W ζ ω).comp continuous_real_toNNReal)
    s.coe_nonneg

end InteractingSLE.Sec7.R5Phase
