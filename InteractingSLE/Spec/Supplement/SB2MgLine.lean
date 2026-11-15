/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LinesSafe
import InteractingSLE.Spec.Supplement.SB2DrvLineUnion

/-!
# K2's (S) from marked-local line sets with a clopen relative region (generic)

Packet PROVE-SB2-LCMEAN, round 4. K2's safe law (S) is produced by `BW1Lines.hasSafeLaw_life_of_lineKernel` from a
Gaussian line kernel (`hker`) and the line mean (`hmean`). SB2(1)'s `Lv.hasSafeLaw_of_lineUnion` derives the kernel
from line sets that are history-marked local for the line filtration and whose complement contains the chart image
of the relative domain as a clopen part; it is stated for SB2(1)'s launch structures. Here is the same derivation for
an arbitrary line filtration, chart, clock and driver, so that SB2(2)'s lines (the filled retained and explored sets
of `Mf.exists_sb2LowerStageSets` at the own times of the lower piece, with the mean of
`Mg.sb2Lower_chartTransport_eq_couplingMean_unb`) can feed K2 directly:

* **`hasSafeLaw_of_markedLines`**: (S) with lifetime `V` from line sets `B t` (measurable, relatively closed,
  history-marked local for `𝓖 t`), the clopen inclusion of `c(ℍ ∖ K̃_{a t})` in `ℍ ∖ B t` on `F ∩ {a t < V}`, their
  local-set means `g t` and the line-mean identity for `g t + u₀`.

Generic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.SB.Mg

open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 LocalSets WholeField

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ≥0∞}

/-- **K2's (S) from marked-local line sets** (generic form of `Lv.hasSafeLaw_of_lineUnion`): line sets `B t`,
measurable, relatively closed and history-marked local for the line filtration `𝓖`, whose complement contains the
chart image of the relative domain `c(ℍ ∖ K̃_{a t})` as a clopen part on `F ∩ {a t < V}`, with local-set means `g t`
whose chart transport (plus the harmonic centring `u₀`) is the canonical mean of the continuation, give K2's safe law
of the chart field with lifetime `V`. -/
theorem hasSafeLaw_of_markedLines {𝓖 𝓗' : Filtration ℝ≥0 mΩ} {F : Set Ω} (hF : MeasurableSet[𝓖 0] F)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (σa k : ℝ) (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (V : Ω → ℝ≥0∞) (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR V ω) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t]
      {ω | a t ω < V ω ∧ Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (𝓖 t) (B t) (centredField h u₀) P)
    (hclop : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → a t ω < V ω →
      (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) ⊆ H \ B t ω ∧
        IsOpen ((H \ B t ω) \ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)))
    (g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens)
    (hg : ∀ t, IsLocalSetMean (B t) (centredField h u₀) P (g t))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 σa k (g t ω + smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal
          (bheProc κ ρL ρR W VL VR ω (a t ω).toNNReal) z * ψ z) :
    HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR fun ω => Chart.chartTransport (hc ω) 1 σa k (h ω) := by
  have hhm : Measurable (centredField h u₀) := measurable_centredField hh u₀
  have hℋ : ∀ t, 𝓖 t ≤ mΩ := fun t => 𝓖.le t
  have hgeq : ∀ t ω, g t ω + smoothDist upperHalfPlaneOpens u₀ = g t ω + (h ω - centredField h u₀ ω) := by
    intro t ω
    simp only [centredField, sub_sub_cancel]
  refine BW1Lines.hasSafeLaw_life_of_lineKernel hF hc hdom hfwd hliftm hliftc hh σa k hac ham ha0 haa h𝓗' V hreach
    hreg hS (fun t => germSigma (B t) (centredField h u₀) ⊔ 𝓖 t) (fun t => le_sup_right)
    (fun t => sup_le (germSigma_le (hBm t) hhm) (hℋ t))
    (fun t ω => g t ω + smoothDist upperHalfPlaneOpens u₀) (fun t φ => ?_) hmean
  set U₀ : ℝ := ∫ z, u₀ z * φ z with hU₀
  set X₀ : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) with hX₀def
  have hXX₀ : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) = Complex.exp (Complex.I * (U₀ : ℂ)) • X₀ := by
    funext ω'
    simp only [hX₀def, Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, centredField_apply h hu₀ ω' φ]
    congr 1
    push_cast
    ring
  have hsmul := condExp_smul (μ := P) (Complex.exp (Complex.I * (U₀ : ℂ))) X₀
    (germSigma (B t) (centredField h u₀) ⊔ 𝓖 t)
  filter_upwards [hsmul, Supp8.RelSafeS.ae_condExp_cexp_marked hh0 (hBm t) (hBc t) (hℋ t) (hloc t) (hg t) φ,
    hclop t] with ω h1 h2 h3 hωF hlt hsupp
  obtain ⟨hCV, hVC⟩ := h3 hωF hlt
  have hCo : IsOpen ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)) :=
    SmallGammaGeodesics.CC.isOpen_image_conf (QuantumZipper.FwdHolo.isOpen_compl_fwdHull
      ((hWc ω).comp continuous_real_toNNReal) (NNReal.coe_nonneg _))
      ((hc ω).1.mono sdiff_subset) ((hc ω).injOn.mono sdiff_subset)
  have hGc : zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)) φ φ =
      zeroGFFTestCov (H \ B t ω) φ φ :=
    (zeroGFFTestCov_eq_of_isClopen (hBc t ω).2 sdiff_subset hCo hCV hVC φ hsupp).symm
  have hM : (g t ω + smoothDist upperHalfPlaneOpens u₀) φ = g t ω φ + U₀ := by
    rw [hgeq t ω]
    show g t ω φ + (h ω φ - centredField h u₀ ω φ) = _
    rw [centredField_apply h hu₀ ω φ]
    ring
  rw [hGc, hM, hXX₀, h1, Pi.smul_apply, smul_eq_mul, h2, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  ring

end InteractingSLE.Theorem14.SB.Mg
