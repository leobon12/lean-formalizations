/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Probability.GermZeroOne
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Backward (reverse) martingale convergence

Packet PROVE-LEMMA71D, item (1). For a decreasing sequence of σ-algebras `𝒢₀ ⊇ 𝒢₁ ⊇ ⋯` and `f ∈ L²`, the conditional
expectations `E[f | 𝒢ₙ]` converge to `E[f | ⋂ₙ 𝒢ₙ]` in `L²` (Lévy's downward theorem in its `L²` form), hence in
measure and almost surely along a subsequence. Mathlib (`a4c8ef0a`) has only the upward theorems
(`MeasureTheory.Integrable.tendsto_ae_condExp`, `tendsto_eLpNorm_condExp`).

Proof: `E[f | 𝒢ₙ]` is the orthogonal projection of `f` onto the closed subspace `L²(𝒢ₙ)`; projections onto a
decreasing sequence of closed subspaces converge to a limit `y` lying in every subspace
(QuantumZipper `GermZeroOne.exists_tendsto_starProjection_antitone`). Then `y` has a `⋂ₙ 𝒢ₙ`-measurable version
(`GermZeroOne.exists_iInf_version`, a `limsup` of versions), and its set integrals over `A ∈ ⋂ₙ 𝒢ₙ` are the limits of
`⟪1_A, E[f | 𝒢ₙ]⟫ = ∫_A f`, so `y = E[f | ⋂ₙ 𝒢ₙ]`. (The project's `LocalSets.exists_tendsto_condExp_antitone` gives the
`L²` limit without identifying it, which is the step needed here.)

## Main results

* `tendsto_condExpL2_iInf`: `E[f | 𝒢ₙ] → E[f | ⋂ₙ 𝒢ₙ]` in `L²` (as elements of `L²`);
* `tendstoInMeasure_condExp_iInf`: convergence in measure;
* **`exists_seq_ae_tendsto_condExp_iInf`**: almost sure convergence along a subsequence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace InteractingSLE

namespace Martingale

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒢 : ℕ → MeasurableSpace Ω}

/-- **Lévy's downward theorem, `L²` form.** Along a decreasing sequence of σ-algebras, the `L²` conditional
expectations of `f ∈ L²` converge in `L²` to an element almost everywhere equal to `E[f | ⋂ₙ 𝒢ₙ]`. -/
theorem tendsto_condExpL2_iInf (hle : ∀ n, 𝒢 n ≤ mΩ) (hanti : Antitone 𝒢) {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    ∃ y : Lp ℝ 2 P, Tendsto (fun n => (condExpL2 ℝ ℝ (hle n) (hf.toLp f) : Lp ℝ 2 P)) atTop (𝓝 y) ∧
      (y : Ω → ℝ) =ᵐ[P] P[f | ⨅ n, 𝒢 n] := by
  have : ∀ n, CompleteSpace (lpMeas ℝ ℝ (𝒢 n) 2 P) := fun n => by
    have : Fact (𝒢 n ≤ mΩ) := ⟨hle n⟩; infer_instance
  set F : Lp ℝ 2 P := hf.toLp f
  have hKanti : Antitone (fun n => lpMeas ℝ ℝ (𝒢 n) 2 P) := by
    intro a b hab u hu
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hu ⊢
    obtain ⟨g, hg, he⟩ := hu
    exact ⟨g, hg.mono (hanti hab), he⟩
  obtain ⟨y, hy, hyK⟩ :=
    QuantumZipper.GermZeroOne.exists_tendsto_starProjection_antitone _ hKanti F
  have hyn : ∀ n, (lpMeas ℝ ℝ (𝒢 n) 2 P).starProjection F
      = (condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) := fun n => by
    rw [Submodule.starProjection_apply]; rfl
  have hy' : Tendsto (fun n => (condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P)) atTop (𝓝 y) := by
    simpa only [hyn] using hy
  refine ⟨y, hy', ?_⟩
  -- a version measurable for the intersection
  have hym : ∀ m, ∃ g : Ω → ℝ, StronglyMeasurable[𝒢 m] g ∧ (y : Ω → ℝ) =ᵐ[P] g := fun m => by
    have h := hyK m
    rw [mem_lpMeas_iff_aestronglyMeasurable] at h
    obtain ⟨g, hg, he⟩ := h
    exact ⟨g, hg, he⟩
  obtain ⟨Y, hYm, hyY⟩ := QuantumZipper.GermZeroOne.exists_iInf_version hanti hym
  have hle' : (⨅ n, 𝒢 n) ≤ mΩ := (iInf_le 𝒢 0).trans (hle 0)
  have hfi : Integrable f P := hf.integrable one_le_two
  have hyi : Integrable (y : Ω → ℝ) P := (Lp.memLp y).integrable one_le_two
  refine hyY.trans (ae_eq_condExp_of_forall_setIntegral_eq hle' hfi
    (fun s _ _ => (hyi.congr hyY).integrableOn) (fun s hs hPs => ?_)
    hYm.stronglyMeasurable.aestronglyMeasurable)
  -- set integrals over `s ∈ ⋂ₙ 𝒢ₙ`
  have hsm : MeasurableSet s := hle' s hs
  have hsn : ∀ n, MeasurableSet[𝒢 n] s := fun n => MeasurableSpace.measurableSet_iInf.1 hs n
  have hlim : Tendsto (fun n => ∫ x in s, (condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) x ∂P) atTop
      (𝓝 (∫ x in s, (y : Ω → ℝ) x ∂P)) := by
    have hc := Filter.Tendsto.inner (𝕜 := ℝ)
      (tendsto_const_nhds (x := indicatorConstLp 2 hsm hPs.ne (1 : ℝ))) hy'
    simpa only [L2.inner_indicatorConstLp_one hsm hPs.ne] using hc
  have hconst : ∀ n, ∫ x in s, (condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) x ∂P = ∫ x in s, f x ∂P := fun n => by
    rw [setIntegral_congr_ae hsm ((hf.condExpL2_ae_eq_condExp (hle n)).mono fun x hx _ => hx),
      setIntegral_condExp (hle n) hfi (hsn n)]
  rw [setIntegral_congr_ae hsm (hyY.mono fun x hx _ => hx.symm)]
  simp only [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Lévy's downward theorem, in measure.** Along a decreasing sequence of σ-algebras, `E[f | 𝒢ₙ] → E[f | ⋂ₙ 𝒢ₙ]`
in measure for `f ∈ L²`. -/
theorem tendstoInMeasure_condExp_iInf (hle : ∀ n, 𝒢 n ≤ mΩ) (hanti : Antitone 𝒢) {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    TendstoInMeasure P (fun n => P[f | 𝒢 n]) atTop P[f | ⨅ n, 𝒢 n] := by
  obtain ⟨y, hy, hyc⟩ := tendsto_condExpL2_iInf hle hanti hf
  exact (tendstoInMeasure_of_tendsto_Lp hy).congr (fun n => hf.condExpL2_ae_eq_condExp (hle n)) hyc

/-- **Lévy's downward theorem, almost surely along a subsequence.** -/
theorem exists_seq_ae_tendsto_condExp_iInf (hle : ∀ n, 𝒢 n ≤ mΩ) (hanti : Antitone 𝒢) {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => P[f | 𝒢 (ns i)] ω) atTop (𝓝 (P[f | ⨅ n, 𝒢 n] ω)) :=
  (tendstoInMeasure_condExp_iInf hle hanti hf).exists_seq_tendsto_ae

end Martingale

end InteractingSLE
