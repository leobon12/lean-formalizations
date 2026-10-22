import HigherDimLQGMetric.Main.ExponentBridge
import HigherDimLQGMetric.Markov.Main
import HigherDimLQGMetric.Sec10.Lemma101

/-!
# Existence of a sharp weak metric from the LFPP subsequence theorem

Packet L10a. The B3 existence interface is applied with the canonical exponent,
the DGZ adapter, the open-set Markov theorem, and shell decoupling.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Discharge the final premises of [1] Theorem 1.3 for the canonical exponent. -/
theorem l10a_l8_of_inputs (hB3 : B3Goal)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hShell : ShellDecouplingFun)
    {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ) :
    ∀ εs : ℕ → ℝ, (∀ n, 0 < εs n) → Tendsto εs atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ),
        StrictMono φ ∧ IsWeakExpMetric d ξ D c ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistRd d), IsLGFPlusBddCont h P →
              TendstoInProbLU P
                (fun n ω => (aEps κ ξ (εs (φ n)))⁻¹ • lfppDist κ ξ (εs (φ n)) (h ω))
                atTop (fun ω => (D (h ω)).1) := by
  have hL8 := hB3 d hd κ hκ ξ (distExp d ξ) hξ
    (l10a_distExp_isKernelExponent hd hκ hξ) hsub
  exact hL8 ⟨distExp d ξ, l10a_dgzHyp hd hκ hξ hsub, hB2 d κ ξ (distExp d ξ)⟩
    dMarkovRd hShell

/-- One canonical subsequential weak assignment exists at every subcritical parameter. -/
theorem l10a_exists_weak_of_inputs (hB3 : B3Goal)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hShell : ShellDecouplingFun)
    {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ) :
    ∃ (D : DistRd d → ContMetric d) (c : ℝ → ℝ), IsWeakExpMetric d ξ D c := by
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  let εs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < εs n := fun n => by dsimp [εs]; positivity
  have hε0 : Tendsto εs atTop (𝓝 0) := by
    simpa only [εs] using tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, D, c, -, hD, -⟩ :=
    (l10a_l8_of_inputs hB3 hB2 hShell hd hκ hξ hsub) εs hεpos hε0
  exact ⟨D, c, hD⟩

/-- Phase B supplies a nonempty sharp weak class. -/
theorem sharpWeak_nonempty_of_inputs (hB3 : B3Goal)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hE2 : Theorem16Shape) (hShell : ShellDecouplingFun) :
    SharpWeakNonemptyStmt := by
  intro d ξ hd hξ hsub
  obtain ⟨D, c, hD⟩ := l10a_exists_weak_of_inputs hB3 hB2 hShell (by omega) hξ hsub
  exact ⟨D, (hE2 d hd hξ hsub hD).2⟩

end HigherDimLQGMetric
