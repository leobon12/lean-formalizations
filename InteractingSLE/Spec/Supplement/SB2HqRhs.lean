/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2HqTr
import InteractingSLE.Spec.Supplement.SB2KqWord

/-!
# SB2(1)'s late (S) line mean, part 15: FIN's right side read in K2's coordinates

Packet PROVE-T14-SB2DRV (round 11). FIN's conclusion has the relative driver `Wr` of the configuration (globally
continuous) and the configuration's bounded harmonic extension `G` of the flowed typed word, shifted by FIN's constant
`a + χℓ₀ = 0`; `SB2JxFinStatement` has the line version's driver `W` and K2's `bheProc`.
**`integral_couplingMean_fin`**: when `W = Wr` below `V` and the relative time is `< V`, a test function off the
`W`-hull is off the `Wr`-hull (FIN's disjointness input) and the two coupling-mean integrals agree
(`Lemma71B.couplingMean_congr`, `eqOn_bheProc_of_flowedData`, `mapsTo_fwdMap_rpath` on `tsupport φ`).

Deterministic; no source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdHull logDerivFwd)
open LQGMetric (TestOn)

namespace InteractingSLE.Theorem14.SB.Lv

open Restart.DomainMarkov Sec7.PocketTraversal
open Supp8.Q3Chain (flowedData flowedJumps)

/-- **FIN's right side in K2's coordinates.** -/
theorem integral_couplingMean_fin {κ : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type*}
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous (W · ω)) (hW0 : ∀ ω, W 0 ω = 0) {xL : Ω → Fin nL → ℝ}
    {xR : Ω → Fin nR → ℝ} {ω : Ω} (hxL : ∀ i, xL ω i ≤ 0) (hxR : ∀ j, 0 ≤ xR ω j) {V : ℝ≥0∞} {Wr : ℝ → ℝ}
    (hWrc : Continuous Wr) (hWr0 : Wr 0 = 0) (hWV : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V → W q ω = Wr q) {s : ℝ≥0}
    (hsV : (s : ℝ≥0∞) < V) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension (flowedData κ ρL ρR (xL ω) (xR ω) Wr s) (flowedJumps (xL ω) (xR ω) Wr s) G)
    {c : ℝ} (hc : c = 0) (φ : TestOn upperHalfPlaneOpens)
    (hφ : Disjoint (tsupport φ) (fwdHull (fun r : ℝ => W r.toNNReal ω) s)) :
    Disjoint (tsupport φ) (fwdHull Wr s) ∧
      ∫ z, couplingMean κ Wr s (fun z => G z + c) z * φ z =
        ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) s
          (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω s) z * φ z := by
  obtain ⟨t', hst', ht'V⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hsV
  have hagree : EqOn Wr (fun r : ℝ => W r.toNNReal ω) (Icc 0 (t' : ℝ)) := by
    intro r hr
    have hlt : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < V := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) ht'V
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1]
      exact hr.2
    show Wr r = W r.toNNReal ω
    rw [hWV _ hlt, Real.coe_toNNReal _ hr.1]
  have hst'' : (s : ℝ) < t' := by exact_mod_cast hst'
  have hEqs : EqOn Wr (fun r : ℝ => W r.toNNReal ω) (Icc 0 (s : ℝ)) := fun r hr =>
    hagree ⟨hr.1, hr.2.trans hst''.le⟩
  have hK : fwdHull Wr s = fwdHull (fun r : ℝ => W r.toNNReal ω) s :=
    LocalExt.fwdHull_congr_of_eqOn_of_lt s.2 hst'' hagree
  have hGb := eqOn_bheProc_of_flowedData ρL ρR hWc hW0 hxL hxR hWrc hWr0 hEqs hG
  have hmaps := Sec7.StripSideHeightProb.mapsTo_fwdMap_rpath (w := fun t => W t ω) (ζ := ⊤)
    (hWc ω).continuousOn (q := s) ENNReal.coe_lt_top
  refine ⟨hK ▸ hφ, integral_congr_ae (Eventually.of_forall fun z => ?_)⟩
  by_cases hz : z ∈ tsupport φ
  · have hzH : z ∈ H := Coupling.tsupport_subset_H φ hz
    have hzK : z ∉ fwdHull (fun r : ℝ => W r.toNNReal ω) s := fun h => hφ.le_bot ⟨hz, h⟩
    show couplingMean κ Wr s (fun z => G z + c) z * φ z = _
    rw [Sec7.Lemma71B.couplingMean_congr s.coe_nonneg hEqs κ (fun z => G z + c) z]
    unfold couplingMean
    subst hc
    show (G (fwdMap (fun r : ℝ => W r.toNNReal ω) s z) + 0 -
        QuantumZipper.chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) s z).im) * φ z =
      (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω s (fwdMap (fun r : ℝ => W r.toNNReal ω) s z) -
        QuantumZipper.chiC κ * (logDerivFwd (fun r : ℝ => W r.toNNReal ω) s z).im) * φ z
    rw [add_zero, hGb (hmaps ⟨hzH, hzK⟩)]
  · show couplingMean κ Wr s (fun z => G z + c) z * φ z =
      couplingMean κ (fun r : ℝ => W r.toNNReal ω) s (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω s) z * φ z
    rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

end InteractingSLE.Theorem14.SB.Lv
