/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopSideLim

/-!
# Reading the common pocket phase from continuous mean probes

PROVE-POCKET-SIDEIN, R73, follow-up 5 §3.2. On each bounded capacity horizon,
the corrected mean difference is the common phase times a positive harmonic
measure. Division gives continuity of that same phase. The countable horizon
intersection supplies one event for the entire positive lifetime. This adapter
uses the quotient argument already present in `PhaseSel.phase_eq_of_pos`;
it permits different surviving observation points on different horizons.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal Lemma71C PocketStop

/-- R73 (3.2) reads the phase as a quotient of continuous mean probes. -/
theorem continuousOn_phase_of_mean_probes {T : ℝ≥0∞} {d : ℝ≥0 → ℝ}
    {M M₀ w : ℕ → ℝ≥0 → ℝ}
    (hM : ∀ N, ContinuousOn (M N)
      {t | 0 < t ∧ (t : ℝ≥0∞) < T ∧ t < (N : ℝ≥0) + 1})
    (hM₀ : ∀ N, ContinuousOn (M₀ N)
      {t | 0 < t ∧ (t : ℝ≥0∞) < T ∧ t < (N : ℝ≥0) + 1})
    (hw : ∀ N, ContinuousOn (w N)
      {t | 0 < t ∧ (t : ℝ≥0∞) < T ∧ t < (N : ℝ≥0) + 1})
    (hpos : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T → t < (N : ℝ≥0) + 1 → 0 < w N t)
    (hmean : ∀ (N : ℕ) (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T → t < (N : ℝ≥0) + 1 →
      M N t - M₀ N t = d t * w N t) :
    ContinuousOn d {t | 0 < t ∧ (t : ℝ≥0∞) < T} := by
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  have htN : t < (N : ℝ≥0) + 1 := by
    have hNt : t < (N : ℝ≥0) := by exact_mod_cast hN
    exact hNt.trans (lt_add_one _)
  have hq : ContinuousOn d
      {r : ℝ≥0 | 0 < r ∧ (r : ℝ≥0∞) < T ∧ r < (N : ℝ≥0) + 1} := by
    refine (((hM N).sub (hM₀ N)).div (hw N)
      (fun r hr => (hpos N r hr.1 hr.2.1 hr.2.2).ne')).congr ?_
    intro r hr
    exact (eq_div_iff (hpos N r hr.1 hr.2.1 hr.2.2).ne').2
      (hmean N r hr.1 hr.2.1 hr.2.2).symm
  have hopen : IsOpen
      {r : ℝ≥0 | 0 < r ∧ (r : ℝ≥0∞) < T ∧ r < (N : ℝ≥0) + 1} :=
    isOpen_Ioi.inter ((isOpen_lt ENNReal.continuous_coe continuous_const).inter isOpen_Iio)
  exact (hq.continuousAt (hopen.mem_nhds ⟨ht.1, ht.2, htN⟩)).continuousWithinAt

/-- Countable bounded horizons give one continuous version on the positive
lifetime. The exact mean identity is required on each common horizon event. -/
theorem ae_continuous_phase_of_mean_probes {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {δ : ℝ≥0 → Ω → ℝ}
    {M M₀ w : ℕ → Ω → ℝ≥0 → ℝ}
    (hProbes : ∀ N : ℕ, ∀ᵐ ω ∂P, ω ∈ A →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (M N ω) S ∧ ContinuousOn (M₀ N ω) S ∧ ContinuousOn (w N ω) S ∧
        ∀ t ∈ S, 0 < w N ω t ∧ M N ω t - M₀ N ω t = δ t ω * w N ω t) :
    ∀ᵐ ω ∂P, ω ∈ A →
      ContinuousOn (fun t => δ t ω) {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω)} := by
  filter_upwards [ae_all_iff.2 hProbes] with ω hp hω
  exact continuousOn_phase_of_mean_probes
    (fun N => (hp N hω).1) (fun N => (hp N hω).2.1) (fun N => (hp N hω).2.2.1)
    (fun N t ht htT htN => ((hp N hω).2.2.2 t ⟨ht, htT, htN⟩).1)
    (fun N t ht htT htN => ((hp N hω).2.2.2 t ⟨ht, htT, htN⟩).2)

/-- The R73 quotient replaces the phase-continuity premise in the all-q
canonical reduction. The phase word and joint zero-visit inputs remain explicit. -/
theorem pocketStopSideLimit_of_phase_mean_probes {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} {κ : ℝ} (hκ : 4 < κ)
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
    {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}
    {K : ℝ≥0 → Ω → Set ℂ} {δ : ℝ≥0 → Ω → ℝ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hPhase : ∀ q, PocketStopPhaseSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) (δ q) q)
    {M M₀ w : ℕ → Ω → ℝ≥0 → ℝ}
    (hProbes : ∀ N : ℕ, ∀ᵐ ω ∂P, ω ∈ A →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (γ ω) ∧ t < (N : ℝ≥0) + 1};
      ContinuousOn (M N ω) S ∧ ContinuousOn (M₀ N ω) S ∧ ContinuousOn (w N ω) S ∧
        ∀ t ∈ S, 0 < w N ω t ∧ M N ω t - M₀ N ω t = δ t ω * w N ω t)
    {s : ι → Ω → ℝ≥0} {E : ι → Set Ω}
    (hZero : ∀ i, ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E i → δ (s i ω) ω = 0)
    (hVisits : ∀ᵐ ω ∂P, ω ∈ A → 0 < capLife (γ ω) →
      ∃ i, 0 < s i ω ∧ (s i ω : ℝ≥0∞) < capLife (γ ω) ∧ ω ∈ E i) :
    ∀ q, PocketStopSideLimit κ ρL ρR P A γ xL xR c a h₀ u (K q) q :=
  pocketStopSideLimit_of_phase_countable_anchors hκ hγ hseedL hseedR hPhase
    (ae_continuous_phase_of_mean_probes hProbes) hZero hVisits

end InteractingSLE.Sec7.PocketStopSide
