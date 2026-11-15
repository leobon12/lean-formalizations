/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksGirsanov
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Aux. lemma 54 for general words: the statement

Packet PROVE-DOMAINMARKOV7 (item 3 of `planning/handoffs/PROVE-DOMAINMARKOV5.md`). Aux. lemma 54 (specification
p. 246; used for stopped portions on p. 295: "For a stopped portion, the same conclusion follows by appending the
canonical future in its active residual field and applying that uniqueness, then restricting back to the recorded
stop"). Lemma G7, Lemma 7.6 and GB6 claim determination only up to a stop; the kernel assembly K2 needs a full
coupling, so a coupling known only through a stop must first be extended.

The landed form (`LocalExt.StoppedSeedExtendStatement`, proved for every `κ > 0` by
`LocalExt.stoppedSeedExtendStatement`)
covers words whose marks off the seeds have weight `0`, at local stops of a radius `r`, under a measure change. This
file states the general form:

* `IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h`: **a coupling through the stop `V`** — the frozen
  `IsOptionalHullCoupling` with the driving evolution replaced by a local evolution before `V`
  (`Sec2.IsSLEEvolutionUpTo`), the state continuous through a finite stop, and the locality and conditional-law
  clauses at every stopping time `τ ≤ V` (finite) of the driving filtration of the process killed at `V`;
* `StoppedHullExtendStatement κ`: **Aux. lemma 54** — every coupling through a stop extends, on an enlargement
  `Ω × C` whose first marginal is `P` and with the same field read through the first factor, to a full optional hull
  coupling whose coordinates agree with the stopped ones through the stop.

The statement is not proved here; see `planning/handoffs/PROVE-DOMAINMARKOV7.md` for the route (the record-law
construction of the seed case, with the two-seed history space `Sec4.HistorySpace 1 1` replaced by
`Sec4.HistorySpace nL nR` and the two-seed reference by Theorem 1.1's construction for the word).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

namespace StoppedExtend

/-- **A coupling through the stop `V`** (the hypotheses of Aux. lemma 54, specification p. 246, for a general word:
"another stopped coupling with the same driving law and the same original optional hull specification through `S`").
Clause by clause the frozen `IsOptionalHullCoupling`, with:

* the driving law **before `V`**: `B` is an `𝓕`-Brownian motion, the coordinates are `𝓕`-adapted before `V`, and
  almost surely Definition 2.1's path conditions hold before `V` (`Sec2.IsSLEEvolutionUpTo`);
* almost surely, at a finite stop the state is continuous on `[0, V]`;
* the field is measurable and `h − 𝔥⁰` is a zero-boundary GFF process (as in the frozen definition);
* at every finite stopping time `τ ≤ V` of the driving filtration of the coordinates killed at `V`, the hull `K_τ` is a
  local set of `h`, and off `K_τ` the conditional law of `h` given the stopped σ-algebra is the coupling kernel (as in
  the frozen definition, whose clause is at stopping times `τ < ζ`). -/
def IsStoppedHullCoupling (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (V : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B V ∧
    (∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T)) ∧
    Measurable h ∧
    (∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR)
        (forceJumpSet xL xR) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ z, u₀ z * φ z) P) ∧
    ∃ hX : IsMeasurableKilledDriving W VL VR V,
      ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ),
        (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) ≤ V ω ∧ τ ω ≠ ⊤) →
        IsLocalSet (fun ω => QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
            ((τ ω).untopD 0 : ℝ≥0)) h P ∧
          ∀ u : Ω → ℂ → ℝ,
            (∀ ω, IsBoundedHarmonicExtension
                (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
                  (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
                (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
                  (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
                (u ω)) →
            ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
              Disjoint (tsupport φ) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω)
                  ((τ ω).untopD 0 : ℝ≥0)) →
                condExp hτ.measurableSpace P
                    (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
                  Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                      ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
                    (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
                      ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ))

/-- **Named input: Aux. lemma 54 for general words** (specification p. 246: "Then the stopped coupling extends to a
full coupling with the original optional hull specification. The extension preserves the whole initial field and uses
only the stopped history and its active field when sampling the future"; p. 295). For an ordered force word, every
coupling through a stop `V` on `(Ω, P)` extends: on `Ω × C` with a probability measure `E` whose first marginal is
`P`, the field read through the first factor has a full optional hull coupling (the frozen `IsOptionalHullCoupling`)
whose lifetime is at least `V` and whose coordinates agree with the stopped ones at every time `t ≤ V` before the
lifetime. (The future is sampled, so the extension lives on an enlargement, as in the landed seed form
`LocalExt.HasReferenceExtension`; on the same space the case `V = 0` would already be a determination theorem.) -/
def StoppedHullExtendStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (V : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsStoppedHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B V h →
      ∃ (C : Type u) (_ : MeasurableSpace C) (E : Measure (Ω × C)) (_ : IsProbabilityMeasure E)
        (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × C))) (W' : ℝ≥0 → Ω × C → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × C → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × C → ℝ) (B' : ℝ≥0 → Ω × C → ℝ)
        (ζ' : Ω × C → ℝ≥0∞),
        E.map Prod.fst = P ∧
        IsOptionalHullCoupling κ xL xR ρL ρR E 𝓕' W' VL' VR' B' ζ' (fun p => h p.1) ∧
        ∀ᵐ p ∂E, V p.1 ≤ ζ' p ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 → (t : ℝ≥0∞) < ζ' p →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1

end StoppedExtend

end Restart

end InteractingSLE
