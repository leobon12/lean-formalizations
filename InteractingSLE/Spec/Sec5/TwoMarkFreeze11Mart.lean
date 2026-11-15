/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkFreeze11Paths
import InteractingSLE.Spec.ZhanGT4.A1CanonStopBM

/-!
# Frozen exponential martingales in the null augmentation

The vendor conditional-expectation theorem preserves martingales when null sets
are adjoined. Freezing the endpoint and removing exceptional paths then supplies
the continuous noise required by the existing announcing-clock construction.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Freeze11

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓘 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}
  {Q : ℕ → Ω → ℝ≥0} {G : Set Ω}

/-- A real martingale remains a martingale when measurable null sets are adjoined. -/
theorem martingale_nullAugmented [IsFiniteMeasure P] {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝓘 P) : Martingale X (Ito.nullAugmented 𝓘 P) P := by
  refine ⟨fun u => (hX.stronglyAdapted u).mono (Ito.le_nullAugmented 𝓘 P u), fun s u hsu => ?_⟩
  exact (MathFin.ItoLocalMartingale.condExp_sup_nulls (𝓘.le s) (hX.integrable u)).trans
    (hX.condExp_ae_eq hsu)

/-- Freezing the endpoint preserves every stopped exponential martingale. -/
theorem martingale_exp_frozenNoise [IsFiniteMeasure P]
    (hG : MeasurableSet[Ito.nullSets P] G) (hGc : P Gᶜ = 0)
    (hstrict : ∀ ω ∈ G, ∀ n, (Q n ω : ℝ≥0∞) < τ ω)
    (hQ : ∀ n, IsStoppingTime 𝓘 fun ω => (Q n ω : WithTop ℝ≥0))
    (hExp : ∀ θ n, Martingale (fun u ω => Real.exp (θ * N (min u (Q n ω)) ω -
      θ ^ 2 * ((min u (Q n ω) : ℝ≥0) : ℝ) / 2)) 𝓘 P) (θ : ℝ) (n : ℕ) :
    Martingale (fun u ω => Real.exp (θ * frozenNoise N τ G (min u (Q n ω)) ω -
      θ ^ 2 * ((min u (Q n ω) : ℝ≥0) : ℝ) / 2)) (Ito.nullAugmented 𝓘 P) P := by
  have hM := martingale_nullAugmented (hExp θ n)
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  refine hM.congr (fun u => ?_) (fun u => ?_)
  · have hGt : MeasurableSet[Ito.nullAugmented 𝓘 P u] G :=
      (show Ito.nullSets P ≤ Ito.nullAugmented 𝓘 P u from le_sup_right) _ hG
    have hmin := (ZhanGT4.A1Canon.measurable_min_of_isStoppingTime (hQ n) u).mono
      (Ito.le_nullAugmented 𝓘 P u) le_rfl
    have hclock := measurable_coe_nnreal_real.comp hmin
    have heq : (fun ω => Real.exp (θ * frozenNoise N τ G (min u (Q n ω)) ω -
        θ ^ 2 * ((min u (Q n ω) : ℝ≥0) : ℝ) / 2)) =
        fun ω => if ω ∈ G then Real.exp (θ * N (min u (Q n ω)) ω -
          θ ^ 2 * ((min u (Q n ω) : ℝ≥0) : ℝ) / 2)
        else Real.exp (-(θ ^ 2 * ((min u (Q n ω) : ℝ≥0) : ℝ) / 2)) := by
      funext ω
      rw [frozenNoise_min hstrict]
      split_ifs <;> simp only [mul_zero, zero_sub]
    rw [heq]
    exact ((hM.stronglyAdapted u).measurable.ite hGt
      (Real.measurable_exp.comp ((hclock.const_mul (θ ^ 2)).div_const 2).neg)).stronglyMeasurable
  · filter_upwards [hGa] with ω hω
    rw [frozenNoise_min hstrict]
    simp only [hω, ↓reduceIte]

/-- An announced continuous local noise with finite endpoints has a global frozen version. -/
theorem exists_frozen_version [IsProbabilityMeasure P]
    (hAnn : Coupling.IsAnnouncingSeq 𝓘 P τ Q)
    (hExp : ∀ θ n, Martingale (fun u ω => Real.exp (θ * N (min u (Q n ω)) ω -
      θ ^ 2 * ((min u (Q n ω) : ℝ≥0) : ℝ) / 2)) 𝓘 P)
    (h0 : ∀ ω, N 0 ω = 0)
    (hc : ∀ n ω, Continuous fun u => N (min u (Q n ω)) ω)
    (hlim : ∀ᵐ ω ∂P, τ ω ≠ ⊤ → ∃ L : ℝ,
      Tendsto (N · ω) (𝓝[<] (τ ω).toNNReal) (𝓝 L)) :
    ∃ (𝓚 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → ℝ) (ℓ : ℝ≥0 → Ω → ℝ≥0),
      (∀ u, 𝓘 u ≤ 𝓚 u) ∧ Sec6.Prop65.IsTCExpMartingale P 𝓚 M ℓ ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → ℓ u ω = u) ∧
      ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → M u ω = N u ω := by
  have ha := (ae_all_iff.2 hAnn.2.2.1).and (hAnn.2.2.2.and hlim)
  obtain ⟨G, hG, hGc, hgood⟩ := MathFin.ItoLocalMartingale.exists_nullsAlg_of_ae ha
  have hs : ∀ ω ∈ G, ∀ n, (Q n ω : ℝ≥0∞) < τ ω := fun ω hω => (hgood ω hω).1
  have he : ∀ ω ∈ G, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω → ∃ n, u ≤ Q n ω :=
    fun ω hω => (hgood ω hω).2.1
  have hl : ∀ ω ∈ G, τ ω ≠ ⊤ → ∃ L : ℝ,
      Tendsto (N · ω) (𝓝[<] (τ ω).toNNReal) (𝓝 L) := fun ω hω => (hgood ω hω).2.2
  have hp : ∀ ω ∈ G, 0 < τ ω := fun ω hω => lt_of_le_of_lt bot_le (hs ω hω 0)
  let 𝓗 := Ito.nullAugmented 𝓘 P
  have hSm : ∀ n u, Measurable[𝓗 u] fun ω => min u (Q n ω) := fun n u =>
    (ZhanGT4.A1Canon.measurable_min_of_isStoppingTime (hAnn.1 n) u).mono
      (Ito.le_nullAugmented 𝓘 P u) le_rfl
  have hTC := WholeField.isTCExpMartingale_annClock (𝒢 := fun _ : ℕ => 𝓗)
    (fun _ => monotone_const) hAnn.2.1 hSm (continuous_frozenNoise hc hp he hl)
    (frozenNoise_zero h0 hp) (fun n θ => martingale_exp_frozenNoise hG hGc hs hAnn.1 hExp θ n)
  refine ⟨WholeField.iSupFiltration (fun _ : ℕ => 𝓗),
    (fun u ω => frozenNoise N τ G (WholeField.annClock Q u ω) ω), WholeField.annClock Q,
    (fun u => (Ito.le_nullAugmented 𝓘 P u).trans
      (WholeField.le_iSupFiltration (fun _ : ℕ => 𝓗) 0 u)), hTC, ?_, ?_⟩
  · filter_upwards [hAnn.2.2.2] with ω hω u hu
    exact annClock_eq_before hω hu
  · have hGa : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
    filter_upwards [hGa] with ω hω u hu
    rw [annClock_eq_before (he ω hω) hu]
    simp only [frozenNoise, hω, hu, ↓reduceIte]

end InteractingSLE.Sec5.TwoMark.Freeze11
