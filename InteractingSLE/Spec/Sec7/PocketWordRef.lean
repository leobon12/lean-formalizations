/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketWordEvol
import InteractingSLE.Spec.Sec7.Lemma725Ref

/-!
# §7.4, Lemma 7.25's pocket-word evolution from Aux. lemma 122

Packet PROVE-STRIPSYS6 (specification §7.4.1, Lemma 7.25 and its proof, `source/spec/p385-432.md` L490–L515,
pp. 413–414; Aux. lemma 122, pp. 389–391; Aux. lemma 125, pp. 395–399).

`Lemma725Ref.PocketWordEvolution κ r_L r_R` (the open input `hPW` of Theorem 1.3 at `κ > 4`) asks for one integrated
evolution of a random pocket word with the seed weights `r_L, r_R`, with a continuous trace. This file derives it from
the conclusion of the pocket geometry in the form Aux. lemma 122 takes as hypotheses (`pocketWordEvolution_of_aux122`):
on a standard Borel probability space with a right-continuous filtration, the relative driver and the geometric force
coordinates of a finite word with seeds at `0` and the seed weights `r_L, r_R`, defined for all relative times (Aux.
lemma 125: "Thus `ζ = ∞`"), continuous, adapted, with the deterministic properties of geometric force images, the
exact boundary description with a common phase `d_t ∈ 2πχℤ`, coupling means that are local martingales until
swallowing and continuous before swallowing, and a continuous generating trace on every finite interval (the
complete continuous erased traversal, p. 414). Aux. lemma 122 (`PocketWord.aux122_isRandomWordEvolution`) selects the
zero phase and gives the integrated evolution of the random initial word on a time-zero event of probability one.

What is not proved here: the pocket geometry itself (the selected Jordan pocket of Aux. lemma 130, its erased
relative traversal and relative driver, the all-stop component mean with the initial word of Aux. lemmas 119–121,
the exterior reveal of Aux. lemma 124 and the infinite relative lifetime of Aux. lemma 125).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe v

namespace InteractingSLE

namespace Sec7

namespace PocketWord

open MartChar PhaseSel

/-- **Lemma 7.25's pocket-word evolution from coordinates satisfying Aux. lemma 122's hypotheses** for all times,
with a continuous generating trace on every finite interval (see the module docstring). -/
theorem pocketWordEvolution_of_aux122 {κ rL rR : ℝ} (hκ : 4 < κ) (hL : -2 < rL) (hLd : rL < κ / 2 - 4)
    (hR : -2 < rR) (hRd : rR < κ / 2 - 4) {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    (hρL : ρL 0 = rL) (hρR : ρR 0 = rR) {Ω : Type v} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ}
    (hseedL : ∀ ω, VL 0 0 ω = 0) (hseedR : ∀ ω, VR 0 0 ω = 0)
    (hxLd : ∀ ω (i : Fin nL), VL i.succ 0 ω < 0) (hxRd : ∀ ω (j : Fin nR), 0 < VR j.succ 0 ω)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    (hantiL : ∀ ω i, Antitone fun t => VL i t ω) (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω) (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω)
    {d : ℝ≥0 → Ω → ℝ} (hd : ∀ (t : ℝ≥0) ω, 0 < t → ∃ n : ℤ, d t ω = n * phaseStep κ)
    (hmart : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0))
        (fun t ω => couplingMean κ (wpath W ω) t (U ω t) z))
    (hcont : ∀ U : Ω → ℝ≥0 → ℂ → ℝ, (∀ ω t, IsBoundedHarmonicExtension
        (phaseData κ ρL ρR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) (d t ω))
        (forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)) (U ω t)) →
      ∀ ω (z : ℂ) (T' : ℝ), 0 ≤ T' → z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' →
        ContinuousOn (fun t : ℝ => couplingMean κ (wpath W ω) t (U ω t.toNNReal) z) (Icc 0 T'))
    (htr : ∀ ω (T : ℝ≥0), ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η) :
    Lemma725Ref.PocketWordEvolution.{v} κ rL rR := by
  have hrL' : ρL 0 < 2 * (κ / 2 - 2) - 2 := by rw [hρL]; linarith
  have hrR' : ρR 0 < 2 * (κ / 2 - 2) - 2 := by rw [hρR]; linarith
  obtain ⟨A, hA0, hP1, -, B, hE⟩ := aux122_isRandomWordEvolution hκ (hρL ▸ hL) hrL' (hρR ▸ hR) hrR' hseedL hseedR
    hxLd hxRd hW0 hWc hWa hVLa hVRa hordL hordR hpathL hpathR hantiL hmonoR hidxL hidxR hmergeL hmergeR hsep hd
    hmart hcont
  have hAm : MeasurableSet A := 𝓕.le 0 _ hA0
  have h0 : P A ≠ 0 := by rw [hP1]; exact one_ne_zero
  have hSB : StandardBorelSpace A := hAm.standardBorel
  have hQ : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hAm h0
  refine ⟨nL, nR, ρL, ρR, hρL, hρR, A, inferInstance, hSB, condSub P A, hQ, subFilt 𝓕 A 0, univ,
    fun (ω : A) i => VL i 0 ω, fun (ω : A) j => VR j 0 ω, by rw [measure_univ]; exact one_pos,
    fun ω _ => ?_, subFilt 𝓕 A, fun t (ω : A) => W t ω, fun i t (ω : A) => VL i t ω,
    fun j t (ω : A) => VR j t ω, B, _, hE, ae_of_all _ fun ω _ T _ => htr ω T⟩
  refine ⟨⟨hidxL ω 0, fun i => (hordL ω 0 i).trans_eq (hW0 ω), hidxR ω 0,
    fun j => (hW0 ω).symm.trans_le (hordR ω 0 j)⟩, hseedL ω, hseedR ω, fun i hi => ?_, fun j hj => ?_⟩
  · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 hi
    exact hxLd ω i'
  · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.2 hj
    exact hxRd ω j'

end PocketWord

end Sec7

end InteractingSLE
