/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootN4Family
import InteractingSLE.Spec.Sec5.ProbRestart

/-!
# The uniform slow probability for GW2 root stages

Continuation of PROVE-T14-GW2ROOT2. Lemma 5.10 gives a constant depending
only on `κ`, a drift bound `C`, and a compact interval of admissible first
seed weights. A `RestartWindow` records its qualitative SDE hypotheses.
The event considered includes paths which do not reach the restart event.
Constructing these windows under the retained stage laws remains an input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootS5

open RootN4

/-- Removing the restriction to the restart event by counting its complement
as slow. No measurability of the all-time event `X` is needed here. -/
theorem le_measureReal_compl_union {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A X : Set Ω}
    (hA : MeasurableSet A) {p : ℝ} (hp : p ≤ 1)
    (h : p * P.real A ≤ P.real (A ∩ X)) : p ≤ P.real (Aᶜ ∪ X) := by
  have hsum : P.real A + P.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl hA, probReal_univ]
  have hdisj : Disjoint (A ∩ X) Aᶜ :=
    disjoint_left.2 fun _ h1 h2 => h2 h1.1
  have heq : (A ∩ X) ∪ Aᶜ = Aᶜ ∪ X := by
    ext ω
    simp only [mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  calc
    p = p * (P.real A + P.real Aᶜ) := by rw [hsum, mul_one]
    _ ≤ P.real (A ∩ X) + P.real Aᶜ := by
      rw [mul_add]
      exact add_le_add h
        (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hp (measureReal_nonneg (μ := P) (s := Aᶜ)))
    _ = P.real (Aᶜ ∪ X) := by
      rw [← measureReal_union hdisj hA.compl, heq]

/-- One finite-force evolution and the precise hypotheses of Lemma 5.10 at
a possibly infinite stopping time. `A` is measurable at that stopping time;
on `A` the restart is before the evolution's actual continuation threshold.
An additional experiment buffer may kill observations sooner. -/
structure RestartWindow (κ C : ℝ) (J : Set ℝ) where
  nL : ℕ
  nR : ℕ
  xL : Fin nL → ℝ
  xR : Fin (nR + 1) → ℝ
  ρL : Fin nL → ℝ
  ρR : Fin (nR + 1) → ℝ
  e : EvolutionData.{u} nL (nR + 1)
  hE : e.IsEvolution κ xL ρL xR ρR
  hseed : ρR 0 ∈ J
  τ : e.Ω → WithTop ℝ≥0
  hτ : IsStoppingTime e.filtration τ
  A : Set e.Ω
  hA : MeasurableSet[hτ.measurableSpace] A
  hAζ : ∀ ω ∈ A, (τ ω : ℝ≥0∞) < e.lifetime ω
  hlife : ∀ᵐ ω ∂e.P, ω ∈ A → ∀ t : ℝ≥0, t ≤ 1 →
    (∀ s < t, |e.W ((τ ω).untopA + s) ω - e.W (τ ω).untopA ω| < 1) →
    (((τ ω).untopA + t : ℝ≥0) : ℝ≥0∞) < e.lifetime ω
  hdrift : ∀ᵐ ω ∂e.P, ω ∈ A → ∀ᵐ r ∂(volume : Measure ℝ),
    0 ≤ r → r.toNNReal ≤ 1 →
    (∀ s < r.toNNReal,
      |e.W ((τ ω).untopA + s) ω - e.W (τ ω).untopA ω| < 1) →
    |Sec5.otherDrift ρL ρR (e.W ((τ ω).untopA + r.toNNReal) ω)
      (fun i => e.VL i ((τ ω).untopA + r.toNNReal) ω)
      (fun i => e.VR i ((τ ω).untopA + r.toNNReal) ω)| ≤ C

/-- Outside the restart event `A`, or the driver stays within distance one
of its restart value for the next unit of relative capacity time. -/
def RestartWindow.slowEvent {κ C : ℝ} {J : Set ℝ}
    (w : RestartWindow.{u} κ C J) : Set w.e.Ω :=
  w.Aᶜ ∪ {ω | ∀ t : ℝ≥0, t < 1 →
    |w.e.W ((w.τ ω).untopA + t) ω - w.e.W (w.τ ω).untopA ω| < 1}

/-- One positive probability works for every window with the same `κ`, drift
bound and compact seed-weight range, independently of all word lengths,
starting positions and stopping times. This is a proved consequence of
Lemma 5.10; existence of windows for the root stages is not asserted. -/
theorem exists_uniform_slow_probability {κ C : ℝ} (hκ : 0 < κ)
    {J : Set ℝ} (hJ : IsCompact J) (hJ2 : J ⊆ Ioi (-2)) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ ∀ w : RestartWindow.{u} κ C J,
      ENNReal.ofReal p ≤ w.e.P w.slowEvent := by
  obtain ⟨p, hp, hcross⟩ :=
    Sec5.crossing_lower_bound_restart_stoppingTime (C := C) hκ hJ hJ2
  refine ⟨min p 1, lt_min hp one_pos, min_le_right _ _, fun w => ?_⟩
  let : MeasurableSpace w.e.Ω := w.e.mΩ
  have : IsProbabilityMeasure w.e.P := w.hE.1.1.isGaussianProcess.isProbabilityMeasure
  have hmain := hcross w.e.P w.e.filtration w.xL w.xR w.ρL w.ρR
    w.e.W w.e.VL w.e.VR w.e.B w.e.lifetime w.τ w.hτ w.A w.hE
    w.hseed w.hA w.hAζ w.hlife w.hdrift
  have hsmall : min p 1 * w.e.P.real w.A ≤
      w.e.P.real (w.A ∩ {ω | ∀ t : ℝ≥0, t < 1 →
        |w.e.W ((w.τ ω).untopA + t) ω - w.e.W (w.τ ω).untopA ω| < 1}) :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (measureReal_nonneg (μ := w.e.P) (s := w.A))).trans hmain
  have hbound := le_measureReal_compl_union
    (w.hτ.measurableSpace_le _ w.hA) (min_le_right p 1) hsmall
  have h := ENNReal.ofReal_le_ofReal hbound
  rwa [ofReal_measureReal] at h

end InteractingSLE.Theorem14.GW2TipSystem.RootS5
