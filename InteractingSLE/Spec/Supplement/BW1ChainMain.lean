/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1ChainCf
import InteractingSLE.Spec.Supplement.BW1ChainLines
import InteractingSLE.Spec.Sec7.Lemma725RefSafeTransfer

/-!
# The relative chain, part 5: from the union data on physical lines to the conditional centred counterflow

Packet PROVE-BW1-CHAIN. The composition of the chain (union mean and union locality on deterministic physical lines
→ (S), (L) with infinite lifetime → mean martingales → Theorem 2.4 → relative evolution → K2 → conditional centred
counterflow), in one statement whose hypotheses are exactly the per-line facts of Proposition BW1's proof (p. 614):

* the physical line sets `B t` (in BW1: the retained piece and the counterflow hull up to `t`, in the counterflow
  frame) are history-marked local sets for marks `ℋ t ⊇ 𝓖_t`, with the active germ mean `M t` before the contact
  (BW1's union mean, `Q3Rel.ae_eqOn_unionMean_of_relConfigOff`);
* the chart transport of `M t` through the relative chart is the relative coupling mean at the relative capacity
  `a t` (Aux. 79 at the line; pointwise by `Sec7.PocketCoupling.chartTransport_eq_of_pointwise` and the candidate
  clause of `Q3Rel.IsRelConfigOff`), and `ℍ ∖ B t` is the chart image of `ℍ ∖ K̃_{a t}`;
* the relative driver is a continuous adapted process from `0` with the geometric force points of a `𝒢`-measurable
  word, the relative capacity `a` is a continuous adapted extended clock reaching every level, and the word reaches no
  continuation threshold (the infinite relative lifetime);
* almost surely on the live event, the field read through the relative chart is the field read through the state
  chart and the inversion (`hXeq`; `BW1ChainChart.chartTransport_jointChart_eq_cfField` with the offset
  `2πχ(16/κ)` when the state chart is the Loewner chart of the piece), the word is the counterflow word of the
  conditional data, and the state chart is fixed by the retained past.

**`isCondCounterflowDriverOn_of_lineData`**: then the relative driver drives, conditionally on `𝒢` on the live event,
the centred counterflow of the field read in the state chart (`SB.IsCondCounterflowDriverOn`, the probabilistic
conclusion of Proposition BW1), with lifetime the continuation threshold.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC fwdHull zeroGFFTestCov)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.BW1Chain

open Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.DomainMarkov.Aux79 Sec7 Sec7.PocketTraversal MartChar
open CondDriverBridge Exist.Staged LocalSets

variable {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The relative chain of Proposition BW1, from the union data on physical lines** (see the module docstring for
the hypotheses). -/
theorem isCondCounterflowDriverOn_of_lineData {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    -- the physical filtration, the time change and the relative clock
    {𝓖 𝓗' : Filtration ℝ≥0 mΩ} (h𝒢𝓖 : 𝒢 ≤ 𝓖 0) (h𝒢𝓗 : 𝒢 ≤ 𝓗' 0) {a : ℝ≥0 → Ω → ℝ≥0∞}
    (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω) (ha0 : ∀ ω, a 0 ω = 0)
    (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    -- the relative driver and its word
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗' W)
    (hthr : ∀ᵐ ω ∂P, ω ∈ F → thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) = ⊤)
    -- the relative chart and the physical field
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (σa k : ℝ)
    {hcf : Ω → DistOn upperHalfPlaneOpens} (hcfm : Measurable hcf) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField hcf u₀) P)
    -- the line sets, their marks, locality and means (before the contact)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[ℋ t, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField hcf u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal))
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (hM : ∀ t, Measurable[ℋ t] (M t))
    (hgm : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      tsupport φ ⊆ H \ B t ω →
        P[fun ω' => WholeField.centredField hcf u₀ ω' φ |
          germSigma (B t) (WholeField.centredField hcf u₀) ⊔ ℋ t] ω = M t ω φ - (∫ z, u₀ z * φ z))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 σa k (M t ω) ψ =
        ∫ z, couplingMean (16 / κ) (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal
          (bheProc (16 / κ) ρL ρR W (geomLW W xL) (geomRW W xR) ω (a t ω).toNNReal) z * ψ z)
    (hSψ : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t]
      {ω | a t ω < ⊤ ∧ Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (hSb : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t]
      {ω | a t ω < ⊤ ∧ Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    -- the state chart, the original field, and the identification of the two readings
    {c' : Ω → Chart} (hc' : ∀ ω, (c' ω).IsConformal) (hdom' : ∀ z, MeasurableSet {ω | z ∈ (c' ω).dom})
    (hfwd' : ∀ z, Measurable ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).1 z))
    (hliftm' : ∀ z, Measurable ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).2.2 z))
    (hlc' : ∀ ω, ContinuousOn (c' ω).2.2 (c' ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    (hXeq : ∀ᵐ ω ∂P, ω ∈ F → Chart.chartTransport (hc ω) 1 σa k (hcf ω) = cfField κ (hc' ω) (h ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => cfField κ (hc' ω) (h ω) φ) P)
    {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    (hword : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (bc ω) (jc ω) ∧ flowLineNL (bc ω) (jc ω) 0 = nL ∧
      flowLineNR (bc ω) (jc ω) 0 = nR ∧
        truncWord nL nR (padFL (16 / κ) 0 (bc ω) (jc ω)) = ((xL ω, xR ω), (ρL, ρR)))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c' ω = c' ω₀) :
    SB.IsCondCounterflowDriverOn κ 𝒢 P F h c' W
      (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
        (fun j t => geomRW W xR j t ω)) := by
  have hF𝓖 : MeasurableSet[𝓖 0] F := h𝒢𝓖 _ hF
  have hFℋ : ∀ t, MeasurableSet[ℋ t] F := fun t => h𝓖ℋ t _ (𝓖.mono (zero_le (a := t)) _ hF𝓖)
  have haaℋ : ∀ t, Measurable[ℋ t] (a t) := fun t => (haa t).mono (h𝓖ℋ t) le_rfl
  have hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W (geomLW W xL) (geomRW W xR) (fun _ => ⊤) ω :=
    ae_of_all _ fun ω _ => Restart.FCDet.isForceReg_thr hW0 hWc xL xR _ ω
  -- Aux. 77 at the lines
  have hker0 := ae_lineKernel_of_activeMean hu₀ hh0 hℋ hFℋ haaℋ hBm hBc hloc hM hgm
  have hker : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (hcf ω φ : ℂ)) | ℋ t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
            (a t ω).toNNReal)) φ φ : ℝ) : ℂ)) := by
    intro t φ
    filter_upwards [hker0 t φ, hBK t] with ω h1 h2 hωF hlt hsupp
    rw [← h2 hωF hlt] at hsupp ⊢
    exact h1 hωF hlt hsupp
  -- (S) and (L) with infinite lifetime
  have hlaw := hasSafeLaw_top_of_lineKernel (κ := 16 / κ) (ρL := ρL) (ρR := ρR) (VL := geomLW W xL)
    (VR := geomRW W xR) (𝓗' := 𝓗') hF𝓖 hc hdom hfwd hliftm hliftc hcfm σa k hac ham ha0 haa h𝓗' hreach hreg
    hSψ ℋ h𝓖ℋ hℋ M hker hmean
  have hmem := hasSafeMembers_top_of_lineLocal (VL := geomLW W xL) (VR := geomRW W xR) (𝓗' := 𝓗') hcfm hu₀ hh0
    hc hdom hfwd hliftm hliftc hlift σa k hac ham ha0 haa h𝓗' hreach hreg hSb ℋ h𝓖ℋ hℋ B
    (fun t => (hBm t).mono (hℋ t) le_rfl) hBc hloc hBK
  exact isCondCounterflowDriverOn_of_hasSafeLaw_top hκ h𝒢𝓗 hF hxL hxR hxL0 hxR0 hxLa hxRm hW0 hWc hWa hhm hc'
    hdom' hfwd' hliftm' hlc' hint (hasSafeLaw_congr_ae hlaw hXeq) (hasSafeMembers_congr_ae hmem hXeq) hthr hword
    hcc

/-- **A word with all side partial sums `> −2` has no continuation threshold**, for geometric force points of an
ordered initial word (`Lemma725RefSafe.thresholdTime_eq_top_of_partialSums`): the relative lifetime is infinite for
every sample. -/
theorem thresholdTime_geom_eq_top {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hsL : ∀ m : Fin nL, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i) {Ω' : Type*}
    {xL : Ω' → Fin nL → ℝ} {xR : Ω' → Fin nR → ℝ} (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω))
    {W : ℝ≥0 → Ω' → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) (ω : Ω') :
    thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω) (fun j t => geomRW W xR j t ω) = ⊤ :=
  Lemma725RefSafe.thresholdTime_eq_top_of_partialSums hsL hsR (fun t i => geomLW_le hWc xL ω t i)
    (fun t => antitone_index_geomLW hWc (hxLa ω) t) (fun t j => le_geomRW hWc xR ω t j)
    (fun t => monotone_index_geomRW hWc (hxRm ω) t)

/-- **The relative chain of Proposition BW1 with infinite relative lifetime from the word**: as
`isCondCounterflowDriverOn_of_lineData`, with the no-threshold hypothesis replaced by the deterministic condition
that every side partial sum of the relative word exceeds `−2`; the lifetime of the conditional counterflow is then
`⊤` for every sample. -/
theorem isCondCounterflowDriverOn_top_of_lineData {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hsL : ∀ m : Fin nL, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin nR, -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i) {F : Set Ω}
    (hF : MeasurableSet[𝒢] F) {𝓖 𝓗' : Filtration ℝ≥0 mΩ} (h𝒢𝓖 : 𝒢 ≤ 𝓖 0) (h𝒢𝓗 : 𝒢 ≤ 𝓗' 0)
    {a : ℝ≥0 → Ω → ℝ≥0∞} (hac : ∀ ω, Continuous fun t => a t ω) (ham : ∀ ω, Monotone fun t => a t ω)
    (ha0 : ∀ ω, a 0 ω = 0) (haa : ∀ t, Measurable[𝓖 t] (a t))
    (h𝓗' : ∀ q D, MeasurableSet[𝓗' q] D → ∀ t, MeasurableSet[𝓖 t] (D ∩ {ω | (q : ℝ≥0∞) ≤ a t ω}))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → ∃ t, (q : ℝ≥0∞) ≤ a t ω)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗' W)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom) (σa k : ℝ)
    {hcf : Ω → DistOn upperHalfPlaneOpens} (hcfm : Measurable hcf) {u₀ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField hcf u₀) P)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (h𝓖ℋ : ∀ t, 𝓖 t ≤ ℋ t) (hℋ : ∀ t, ℋ t ≤ mΩ)
    (B : ℝ≥0 → Ω → Set ℂ) (hBm : ∀ t, Measurable[ℋ t, hittingSigma] (B t))
    (hBc : ∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω))
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField hcf u₀) P)
    (hBK : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      H \ B t ω = (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal))
    (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (hM : ∀ t, Measurable[ℋ t] (M t))
    (hgm : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      tsupport φ ⊆ H \ B t ω →
        P[fun ω' => WholeField.centredField hcf u₀ ω' φ |
          germSigma (B t) (WholeField.centredField hcf u₀) ⊔ ℋ t] ω = M t ω φ - (∫ z, u₀ z * φ z))
    (hmean : ∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ F → a t ω < ⊤ →
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal) →
      Chart.chartTransport (hc ω) 1 σa k (M t ω) ψ =
        ∫ z, couplingMean (16 / κ) (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal
          (bheProc (16 / κ) ρL ρR W (geomLW W xL) (geomRW W xR) ω (a t ω).toNNReal) z * ψ z)
    (hSψ : ∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[𝓖 t]
      {ω | a t ω < ⊤ ∧ Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    (hSb : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[𝓖 t]
      {ω | a t ω < ⊤ ∧ Disjoint (Coupling.ballsK Fb) (fwdHull (fun s : ℝ => W s.toNNReal ω) (a t ω).toNNReal)})
    {c' : Ω → Chart} (hc' : ∀ ω, (c' ω).IsConformal) (hdom' : ∀ z, MeasurableSet {ω | z ∈ (c' ω).dom})
    (hfwd' : ∀ z, Measurable ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).1 z))
    (hliftm' : ∀ z, Measurable ({ω | z ∈ (c' ω).dom}.indicator fun ω => (c' ω).2.2 z))
    (hlc' : ∀ ω, ContinuousOn (c' ω).2.2 (c' ω).dom) {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    (hXeq : ∀ᵐ ω ∂P, ω ∈ F → Chart.chartTransport (hc ω) 1 σa k (hcf ω) = cfField κ (hc' ω) (h ω))
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => cfField κ (hc' ω) (h ω) φ) P)
    {bc : Ω → ℝ → ℝ} {jc : Ω → Finset ℝ}
    (hword : ∀ᵐ ω ∂P, ω ∈ F → IsPiecewiseConstantBoundaryData (bc ω) (jc ω) ∧ flowLineNL (bc ω) (jc ω) 0 = nL ∧
      flowLineNR (bc ω) (jc ω) 0 = nR ∧
        truncWord nL nR (padFL (16 / κ) 0 (bc ω) (jc ω)) = ((xL ω, xR ω), (ρL, ρR)))
    (hcc : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), c' ω = c' ω₀) :
    SB.IsCondCounterflowDriverOn κ 𝒢 P F h c' W (fun _ => ⊤) := by
  have hthr := thresholdTime_geom_eq_top hsL hsR hxLa hxRm hWc
  have h := isCondCounterflowDriverOn_of_lineData hκ hF h𝒢𝓖 h𝒢𝓗 hac ham ha0 haa h𝓗' hreach hxL hxR hxL0 hxR0
    hxLa hxRm hW0 hWc hWa (ae_of_all _ fun ω _ => hthr ω) hc hdom hfwd hliftm hliftc hlift σa k hcfm hu₀ hh0 ℋ h𝓖ℋ
    hℋ B hBm hBc hloc hBK M hM hgm hmean hSψ hSb hc' hdom' hfwd' hliftm' hlc' hhm hXeq hint hword hcc
  have e : (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω)) = fun _ => ⊤ := funext hthr
  rwa [e] at h

end InteractingSLE.Theorem14.BW1Chain
