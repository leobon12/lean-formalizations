/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3KernelRelTrace

/-!
# GB6's relative configuration on one sample, and almost surely

Packet PROVE-Q3-REL2, item (A) of `planning/handoffs/PROVE-Q3-REL.md` §4.1 assembled. PROVE-Q3-REL's
`Q3Rel.isRelConfigOff_gb6` bundles GB6's deterministic relative configuration `IsRelConfigOff` (the input of the
exceptional-point mean identification `Q3Rel.ae_eqOn_unionMean_of_relConfigOff`) from the retained chart, the
relative chain with a trace, the hull identity, the flow-frame disjointness, the tip identity, and the words. This file
supplies everything except the words:

* **`exists_isRelConfigOff_gb6`** (deterministic): for a flow driver frozen after `t₂ > s` with a global trace not
  returning to `0` on `(0, s]`, a counterflow with a complete trace, and counterflow times `0 < t < t₁ < T_c`, there is
  a relative chain `(Wr, ηr)` at `u = a(t) > 0` such that every choice of words and means satisfying the word clauses
  (`IsBoundedHarmonicExtension`, `BHMean.IsSideWord`, `BHMean.IsFlowedWord`) and the candidate formula gives
  `IsRelConfigOff`;
* **`ae_exists_isRelConfigOff_gb6`**: the same almost surely on GB6's interior-tip event, for a flow-line driver
  (`0 < κ < 4`; Aux. lemma 25 gives the no-return condition) and every continuous counterflow driver with complete
  traces.

What remains of item (A) is the words (item (A)4): `IsSideWord` for the counterflow word at `t` and the relative word
at `u`, and `IsFlowedWord` from the initial word of the conditional field. Deterministic apart from the last theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)

universe u

namespace InteractingSLE.Supp8.Q3Kernel

open GB6 (relMap relInv relClock firstContactTime sphereInv)
open Q3Rel (invHull relLog relBad IsRelConfigOff)

section Sample

variable {wα w : ℝ≥0 → ℝ} {Tα : ℝ≥0∞} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {U : ℝ → ℝ} {αr : ℝ → ℂ} {t₂ : ℝ}

/-- **GB6's relative configuration on one sample, up to the words** (deterministic). Setting of
`exists_relChain_tip`, with the frozen flow driver `U` having a global Loewner trace `αr` that does not vanish on
`(0, s]`. For counterflow times `0 < t < t₁ < T_c` there is a relative chain `(Wr, ηr)` at `u = a(t) > 0`
(`Ψ(K'_t) = K̃_u`) such that any words and means satisfying the word clauses and the candidate formula form an
`IsRelConfigOff` with GB6's retained chart. -/
theorem exists_isRelConfigOff_gb6 (hα : IsGeneratingTrace wα Tα α)
    (hwα : ContinuousOn wα {t | (t : ℝ≥0∞) < Tα}) (hwα0 : wα 0 = 0) (hs : (s : ℝ≥0∞) < Tα) (hsH : α s ∈ H)
    (hU : Continuous U) (hU0 : U 0 = 0) (hαr : IsLoewnerTrace U αr) (hNR : ∀ v ∈ Ioc (0 : ℝ) s, αr v ≠ 0)
    (hst₂ : (s : ℝ) < t₂) (hUeq : ∀ r ∈ Icc (0 : ℝ) t₂, U r = wα r.toNNReal)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0) {t t₁ : ℝ≥0} (ht0 : 0 < t)
    (htt₁ : t < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ t : OnePoint ℂ))
      ((fun t => (α t : OnePoint ℂ)) '' Icc 0 s)) :
    ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
      0 < relClock U s (fun r : ℝ => w r.toNNReal) t ∧
      relMap U s '' fwdHull (fun r : ℝ => w r.toNNReal) t =
        fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) ∧
      ∀ (χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ),
        IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
        IsBoundedHarmonicExtension βu Su G →
        BHMean.IsSideWord βE SE (fwdMapInv (fun r : ℝ => w r.toNNReal) t)
          (fwdHull (fun r : ℝ => w r.toNNReal) t) lam →
        BHMean.IsSideWord βu Su (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t))
          (fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) lam →
        BHMean.IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr (relClock U s (fun r : ℝ => w r.toNNReal) t))
          (fwdHull Wr (relClock U s (fun r : ℝ => w r.toNNReal) t)) →
        (∀ z, v z = G (fwdMap Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) (relMap U s z)) -
          χ * ((logDerivFwd Wr (relClock U s (fun r : ℝ => w r.toNNReal) t) (relMap U s z)).im +
            (relLog U s z).im)) →
        IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
          (fun r : ℝ => w r.toNNReal) Wr (fun r : ℝ => γ r.toNNReal) ηr t
          (relClock U s (fun r : ℝ => w r.toNNReal) t) χ lam β₀ βE βu S₀ SE Su G₀ GE G v := by
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le (NNReal.coe_nonneg s) with h0 | h0
    · exfalso
      have hs' : s = 0 := by exact_mod_cast h0.symm
      exact GB6.ne_zero_of_mem_H hsH (by rw [hs']; exact hα.1)
    · exact h0
  have hΨ := Q3Rel.isRetainedChartOff_relMap hU hU0 hαr hs0 hNR
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, hd, htip⟩ :=
    exists_relChain_tip hα hwα hwα0 hs hsH hU hU0 hst₂ hUeq hΨ hγ hw hw0 ht0 htt₁ ht₁
  refine ⟨Wr, ηr, hWr, hWr0, hηr, hu, hK, fun χ lam β₀ βE βu S₀ SE Su G₀ GE G v hG₀ hGE hG hsE hsu hflow hv => ?_⟩
  have hWc : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  have hWc0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simp [hw0]
  exact Q3Rel.isRelConfigOff_gb6 hU hU0 hαr hs0 hNR hWc hWc0 (isLoewnerTrace_of_isGeneratingTrace hγ) t.2 hWr hWr0
    hηr hu.le hK hd htip hG₀ hGE hG hsE hsu hflow hv

end Sample

/-- **GB6's relative configuration up to the words, almost surely** (`0 < κ < 4`). For a flow-line driver `Wα` with
generating traces `α` and a continuous counterflow driver `W` from `0` with complete generating traces `γ` (almost
surely), almost surely on the interior-tip event `{s < ζα, α(s) ∈ ℍ}` there is a frozen flow driver `U` (agreeing
with the flow driver on `[0, t₂]`, `t₂ > s`, hence with the same relative map and clock) such that for all counterflow
times `0 < t < t₁ < T_c` the conclusion of `exists_isRelConfigOff_gb6` holds. -/
theorem ae_exists_isRelConfigOff_gb6 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {J : Finset ℝ} {θ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {Wα W : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α γ : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h Wα ζα) (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (s : ℝ≥0) :
    ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      ∃ (U : ℝ → ℝ) (t₂ : ℝ), (s : ℝ) < t₂ ∧ (∀ r ∈ Icc (0 : ℝ) t₂, U r = Wα r.toNNReal ω) ∧
        ∀ t t₁ : ℝ≥0, 0 < t → t < t₁ →
          (t₁ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (γ ω t : OnePoint ℂ))
            ((fun t => (α ω t : OnePoint ℂ)) '' Icc 0 s) →
          ∃ (Wr : ℝ → ℝ) (ηr : ℝ → ℂ), Continuous Wr ∧ Wr 0 = 0 ∧ IsLoewnerTrace Wr ηr ∧
            0 < relClock U s (fun r : ℝ => W r.toNNReal ω) t ∧
            relMap U s '' fwdHull (fun r : ℝ => W r.toNNReal ω) t =
              fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) ∧
            ∀ (χ lam : ℝ) (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G v : ℂ → ℝ),
              IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
              IsBoundedHarmonicExtension βu Su G →
              BHMean.IsSideWord βE SE (fwdMapInv (fun r : ℝ => W r.toNNReal ω) t)
                (fwdHull (fun r : ℝ => W r.toNNReal ω) t) lam →
              BHMean.IsSideWord βu Su (fwdMapInv Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) lam →
              BHMean.IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t))
                (fwdHull Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t)) →
              (∀ z, v z = G (fwdMap Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)) -
                χ * ((logDerivFwd Wr (relClock U s (fun r : ℝ => W r.toNNReal ω) t) (relMap U s z)).im +
                  (relLog U s z).im)) →
              IsRelConfigOff (invHull U s) (relMap U s) (relInv U s) (relLog U s) (relBad U s)
                (fun r : ℝ => W r.toNNReal ω) Wr (fun r : ℝ => γ ω r.toNNReal) ηr t
                (relClock U s (fun r : ℝ => W r.toNNReal ω) t) χ lam β₀ βE βu S₀ SE Su G₀ GE G v := by
  filter_upwards [GB6.ae_driver_zero_continuousOn hF, hα, ae_trace_ne_zero_of_isFlowLineDriver hκ hκ4 hF, hW]
    with ω hω hαω hNRω hWω hs hsH
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · exfalso
      exact GB6.ne_zero_of_mem_H hsH (by rw [← h0]; exact hαω.1)
    · exact h0
  obtain ⟨U, αr, t₂, hst₂, -, hU, hU0, hαr, hUeq, hαeq, -⟩ := exists_frozen_retainedChartOff hαω hω.2 hω.1 hs hs0
    fun v hv hvs => hNRω (α ω) hαω v hv (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hvs) hs)
  have hNR : ∀ v ∈ Ioc (0 : ℝ) s, αr v ≠ 0 := fun v hv => by
    rw [hαeq v ⟨hv.1.le, hv.2.trans hst₂.le⟩]
    refine hNRω (α ω) hαω v.toNNReal (Real.toNNReal_pos.2 hv.1) (lt_of_le_of_lt ?_ hs)
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hv.2)
  refine ⟨U, t₂, hst₂, hUeq, fun t t₁ ht0 htt₁ ht₁ => ?_⟩
  exact exists_isRelConfigOff_gb6 hαω hω.2 hω.1 hs hsH hU hU0 hαr hNR hst₂ hUeq hWω.2.2 hWω.1 hWω.2.1 ht0 htt₁ ht₁

end InteractingSLE.Supp8.Q3Kernel
