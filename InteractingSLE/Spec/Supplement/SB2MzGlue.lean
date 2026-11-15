/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MxIdent

/-!
# The code match at a relative stage from per-stage canonical objects glued along the matched stage

Packet PROVE-SB2-LCMEAN, round 15 (item 4). The relative stage `j` lifts B's stage `N = j + relOff`, a random index.
The canonical objects come per fixed B-stage `n`: marks `𝓜 n`, a compact hull `K n`, an offset `x₀ n` and a word `c n`,
measurable for `𝓜 n`, with the conditional GFF law of the field read in the hull chart given `𝓜 n`. Glued along `N`
(whose events `{N = n}` are known to `𝓜 n`), they are measurable for the stopped σ-algebra (`Mx.stopSigma`) and carry
the glued law (`Mx.ae_isGFF_stopSigma`). `Mx.ae_codeMatch_of_canon` then gives the code match against every witness:

* `isDyadicHitMeasurable_stopSigma_glue`: glued hulls are dyadic-hit measurable for the stopped σ-algebra;
* **`ae_codeMatch_of_glued`**.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mz

open Restart Exist Exist.Staged Exist.StagedLaw Mx

/-- Glued hulls are dyadic-hit measurable for the stopped σ-algebra. -/
theorem isDyadicHitMeasurable_stopSigma_glue {Ω : Type*} {𝓜 : ℕ → MeasurableSpace Ω} {N : Ω → ℕ}
    {hN : ∀ n, MeasurableSet[𝓜 n] {ω | N ω = n}} {K : ℕ → Ω → Set ℂ}
    (hK : ∀ n, @IsDyadicHitMeasurable Ω (𝓜 n) (K n)) :
    @IsDyadicHitMeasurable Ω (stopSigma 𝓜 N hN) (fun ω => K (N ω) ω) := by
  intro m k n
  have e : {ω | (dyadicSquare m k ∩ K (N ω) ω).Nonempty} ∩ {ω | N ω = n} =
      {ω | (dyadicSquare m k ∩ K n ω).Nonempty} ∩ {ω | N ω = n} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rwa [h2] at h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h2]; exact h1, h2⟩
  rw [e]
  exact (hK n m k).inter (hN n)

section Glued

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The code match at a stage from per-stage canonical objects glued along the matched stage.** -/
theorem ae_codeMatch_of_glued (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (θ₀ : ℝ) {k : ℕ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hhm : Measurable h)
    {𝓜 : ℕ → MeasurableSpace Ω} (h𝓜 : ∀ n, 𝓜 n ≤ mΩ) {N : Ω → ℕ} (hN : ∀ n, MeasurableSet[𝓜 n] {ω | N ω = n})
    (hpast : pastSigma κ b jumps spec E k ≤ LocalSets.aeSigma (stopSigma 𝓜 N hN) P)
    {K : ℕ → Ω → Set ℂ} (hKm : ∀ n, @IsDyadicHitMeasurable Ω (𝓜 n) (K n)) (hKc : ∀ n ω, IsCompact (K n ω))
    (hKp : ∀ n ω, IsPreconnected (K n ω ∪ Restart.lowerHalf)) {x₀ : ℕ → Ω → ℝ} (hx₀ : ∀ n, Measurable[𝓜 n] (x₀ n))
    {hphys : Ω → DistOn upperHalfPlaneOpens} (hphm : Measurable hphys) {c : ℕ → Ω → BoundaryWord}
    (hc : ∀ n, Measurable[𝓜 n] (c n)) {G : ℕ → Set Ω}
    (hlaw : ∀ n, ∀ᵐ ω₁ ∂P, ω₁ ∈ G n → N ω₁ = n → IsGFFWithBoundaryData (condExpKernel P (𝓜 n) ω₁)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) 1 0 (chiC κ) (hphys ω))
      (c n ω₁).fn (c n ω₁).jumps)
    (hcode : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      ω ∈ G (N ω) ∧ IsDriverCodeMatch (driverCode h12p hκ θ₀ (c (N ω) ω,
        Chart.chartTransport (Mu.isConformal_canon (x₀ (N ω)) (hKc (N ω)) (hKp (N ω)) ω) 1 0 (chiC κ) (hphys ω)))
        (fun t => (E k ω).1 t) (E k ω).2)
    (htr : ∀ᵐ ω₁ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₁) (k + 1)).2.2.2.1 k ≠ none →
      ∀ ω, IsChartTransport (Cond.runChart κ b jumps spec E k ω₁) 1 0 (chiC κ) (h ω)
        (Chart.chartTransport (Mu.isConformal_canon (x₀ (N ω₁)) (hKc (N ω₁)) (hKp (N ω₁)) ω₁) 1 0 (chiC κ)
          (hphys ω)))
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2 := by
  set 𝓜' : {m : MeasurableSpace Ω // m ≤ mΩ} := ⟨stopSigma 𝓜 N hN, stopSigma_le h𝓜⟩ with h𝓜'
  have hKc' : ∀ ω, IsCompact (K (N ω) ω) := fun ω => hKc (N ω) ω
  have hKp' : ∀ ω, IsPreconnected (K (N ω) ω ∪ Restart.lowerHalf) := fun ω => hKp (N ω) ω
  -- the glued chart field is the per-stage one
  have hZ : ∀ ω, Chart.chartTransport (Mu.isConformal_canon (fun ω => x₀ (N ω) ω) hKc' hKp' ω) 1 0 (chiC κ)
      (hphys ω) = Chart.chartTransport (Mu.isConformal_canon (x₀ (N ω)) (hKc (N ω)) (hKp (N ω)) ω) 1 0 (chiC κ)
      (hphys ω) := fun ω => rfl
  have hlaw' : ∀ n, ∀ᵐ ω₁ ∂P, ω₁ ∈ G n → N ω₁ = n → IsGFFWithBoundaryData (condExpKernel P (𝓜 n) ω₁)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) 1 0 (chiC κ) (hphys ω))
      (c n ω₁).fn (c n ω₁).jumps := hlaw
  have hZm : ∀ n, Measurable fun ω =>
      Chart.chartTransport (Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) 1 0 (chiC κ) (hphys ω) := by
    intro n
    obtain ⟨-, hlc, -, hdom, hfwd, hlift⟩ := Mt.hullChart_k2Inputs (hKm n) (hKc n) (hKp n) (hx₀ n)
    exact Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K n ω)) (x₀ n ω))
      (fun ω => Mu.isConformal_canon (x₀ n) (hKc n) (hKp n) ω) (fun z => h𝓜 n _ (hdom z))
      (fun z => (hfwd z).mono (h𝓜 n) le_rfl) (fun z => (hlift z).mono (h𝓜 n) le_rfl) hlc hphm 1 0 (chiC κ)
  have hglue := ae_isGFF_stopSigma (μ := P) (hN := hN) h𝓜 hZm hlaw'
  refine ae_codeMatch_of_canon h12p h13 hκ θ₀ hb hEm hreg hhm 𝓜' hpast
    (isDyadicHitMeasurable_stopSigma_glue (hN := hN) hKm) hKc' hKp' (measurable_stopSigma_glue (hN := hN) hx₀)
    (hphys := hphys) (measurable_stopSigma_glue (hN := hN) hc) (G := {ω | ω ∈ G (N ω)}) ?_ hcode htr hW
  filter_upwards [hglue] with ω₁ h1 hG
  exact h1 hG

end Glued

end InteractingSLE.Theorem14.SB.Mz
