/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SclKernel
import InteractingSLE.Spec.Supplement.GW2StlMean
import InteractingSLE.Spec.Supplement.SBS3MarkedMean
import InteractingSLE.Spec.Sec5.CrossCondStagedMean
import InteractingSLE.WangWu.PrefixLocalMean
import InteractingSLE.Spec.Sec5.Aux61SlitVChart
import InteractingSLE.Spec.Supplement.GW2SgChart

/-!
# GW2's stage chart law, part 2: the stage union mean from the stage chart law at time `t`

Packet PROVE-GW2-STAGEMEAN, stage-chart-law round (PROVE-GW2-SDE's `GW2Sde.StageInst.LinesLocal.mean`, RELDET's
`hmeanL`). The local-set mean of the physical union `B t` of a stage is read from the CONDITIONAL LAW of the field in
the stage chart moved to the stage clock (`Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`): if, given the
marks `ℋ t` of `B t`, the field read in the chart `C_t = (stage chart).loewner (stage driver) (stage clock)` is the GFF
of a word `β_t`, whose mean (raised by the stage offset) is the canonical bounded harmonic extension of the typed
stage word flowed to the clock, then every local-set mean of `B t` satisfies the stage identity of `LinesLocal.mean`.

* `isHarmonicDistOn_empty`: every distribution is harmonic on `∅`;
* **`StageInst.mean_of_chartLaw`**: `stageMeanAt` for every local-set mean of `B t` and every test function, from the
  chart law at time `t` (test function by test function; the countable bump family upgrades it to all test functions
  at once, `WangWu.ae_forall_apply_eq_of_forall_ae`; the chart transport by the stage chart then reads the coupling mean
  of the stage driver through `Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset`);
* **`StageChartLawAt`** (named input, the domain Markov property of the stage chart at time `t`) and
  **`StageInst.lines_mean_of_chartLaw`**: the target `LinesLocal.mean` from the chart law at every time. The chart
  law under `P` follows from the same law under almost every conditional kernel
  (`GW2Scl.ae_condExp_eq_on_of_ae_condExpKernel`).

Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Scl

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24
  LocalSets WholeField Supp8.RelSafeS GW2Stl

/-- Every distribution is harmonic on the empty set. -/
theorem isHarmonicDistOn_empty (T : DistOn upperHalfPlaneOpens) : IsHarmonicDistOn T ∅ := by
  refine ⟨0, fun z hz => absurd hz (notMem_empty z), fun φ hφ => ?_⟩
  have h0 : ∀ z, φ z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => notMem_empty z (hφ hz)
  have hφ0 : φ = 0 := by
    ext z
    exact h0 z
  rw [hφ0, map_zero]
  simp only [Pi.zero_apply, zero_mul, integral_zero]

/-- **The Gaussian conditional characteristic function passes from the conditional kernel to `P`** (the chart-law
clause of `StageChartLawAt` from its kernel form; `GW2Scl.ae_condExp_eq_on_of_ae_condExpKernel` with the bounds
`‖e^{iY(ψ)}‖ = 1` and `‖gaussCF β ψ‖ ≤ 1`). -/
theorem ae_condExp_cexp_of_kernel {Ω : Type*} {𝒢 𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (h𝓗 : 𝓗 ≤ mΩ)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hYm : Measurable Y) {β : Ω → BoundaryWord} (ψ : TestOn upperHalfPlaneOpens)
    (hβm : StronglyMeasurable[𝓗] fun ω => gaussCF (β ω) ψ) {G : Set Ω} (hG : MeasurableSet[𝓗] G)
    (hk : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ G →
      (condExpKernel P 𝒢 ω₀)[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | 𝓗] ω = gaussCF (β ω) ψ) :
    ∀ᵐ ω ∂P, ω ∈ G → P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | 𝓗] ω = gaussCF (β ω) ψ := by
  have hYψ : Measurable fun ω => Y ω ψ := (LQGMetric.measurable_distOn_apply ψ).comp hYm
  have hfm : StronglyMeasurable fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hYψ))).stronglyMeasurable
  refine ae_condExp_eq_on_of_ae_condExpKernel h𝒢 h𝓗 hfm (C := 1) (fun ω => ?_) hβm
    (fun ω => Restart.norm_gaussCF_le (β ω) ψ) hG hk
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **The stage identity from the stage chart law at time `t`.** -/
theorem StageInst.mean_of_chartLaw (I : StageInst Ω) (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : IsBoundedHarmonicExtension c.b c.jumps I.u₀) (hkc : I.kc = chiC c.κ) (w : WordType) (t : ℝ≥0)
    (hℋ : I.ℋ t ≤ mΩ) (hBm : Measurable[mΩ, hittingSigma] (I.B t)) (hBc : ∀ ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hloc : IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P)
    {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    {Ct : Ω → Chart} (hCt : WalkInf.IsMeasChart (I.ℋ t) Ct)
    (hCtEq : ∀ᵐ ω ∂c.P, ω ∈ G → Ct ω = (I.chart c ω).loewner (fun s : ℝ => I.drv c s.toNNReal ω)
      ((I.clock c t ω).toNNReal : ℝ))
    (hdomB : ∀ᵐ ω ∂c.P, ω ∈ G → ((Ct ω).dom : Set ℂ) = H \ I.B t ω)
    {Y : Ω → DistOn upperHalfPlaneOpens} (hYm : Measurable Y)
    (htr : ∀ᵐ ω ∂c.P, ω ∈ G → IsChartTransport (Ct ω) 1 0 (chiC c.κ) (c.h ω) (Y ω))
    {βt : Ω → BoundaryWord} (hβs : ∀ ω, (βt ω).IsSorted)
    (hlaw : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G →
      c.P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | I.ℋ t] ω = gaussCF (βt ω) ψ)
    (hβU : ∀ᵐ ω ∂c.P, ω ∈ G → EqOn (fun z => (βt ω).mean z + I.σa)
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
        (I.clock c t ω).toNNReal) H)
    (g : Ω → DistOn upperHalfPlaneOpens) (hg : IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, stageMeanAt I c r l w t ψ ω (g ω) := by
  classical
  obtain ⟨hCc, hCℓ, hCh, hCdom, hCfwd, hCball, hCliftm⟩ := hCt
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hlocal : IsLocalSet (I.B t) (centredField c.h I.u₀) c.P :=
    ((isLocalSet_tfae hh0 hBm (Eventually.of_forall hBc)).out 4 1).2 hloc.isAvoidanceLocal
  have hAD : ∀ᵐ ω ∂c.P, ω ∈ G →
      ((Ct ω).dom : Set ℂ) ⊆ H \ I.B t ω ∧ IsOpen ((H \ I.B t ω) \ (Ct ω).dom) := by
    filter_upwards [hdomB] with ω hd hω
    rw [hd hω, Set.sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩
  have hmean := fun φ : TestOn upperHalfPlaneOpens =>
    Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw (𝓗 := I.ℋ t) (c := Ct) hℋ hCc hCdom hCfwd hCball
      hCliftm hCℓ c.hh hu₀ hYm hG htr (β := βt) hlaw hBm hlocal hloc hAD hg φ
  have hu₀c : ContinuousOn I.u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  -- the word chart mean and its continuity on the chart domain
  have hwcm : ∀ ω, InnerProductSpace.HarmonicOnNhd (SB.S3.wordChartMean c.κ (βt ω) (Ct ω) I.u₀) (Ct ω).dom :=
    fun ω => SB.S3.harmonicOnNhd_wordChartMean (hβs ω) (hCc ω) (hCh ω) hu₀.1
  have hmmc : ∀ ω, ContinuousOn (fun z => (βt ω).mean ((Ct ω).1 z) - chiC c.κ * (Ct ω).2.2 z) (Ct ω).dom :=
    fun ω => (((Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (hwcm ω))).add
      (hu₀c.mono (hCc ω).dom_subset)).congr fun z _ => by
        simp only [SB.S3.wordChartMean, Pi.add_apply]
        ring
  -- the cut-off union and mean
  set A' : Ω → Set ℂ := fun ω => if ω ∈ G then I.B t ω else H with hA'
  set m : Ω → ℂ → ℝ := fun ω => if ω ∈ G then SB.S3.wordChartMean c.κ (βt ω) (Ct ω) I.u₀ else 0 with hm
  have hφ' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, tsupport φ ⊆ H \ A' ω →
      g ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [hmean φ, hdomB] with ω h1 hd hsupp
    by_cases hω : ω ∈ G
    · simp only [hA', hω, ↓reduceIte] at hsupp
      have hsD : tsupport φ ⊆ (Ct ω).dom := by rw [hd hω]; exact hsupp
      rw [h1 hω hsD]
      simp only [hm, hω, ↓reduceIte]
      have hi1 := WholeField.integrable_mul_testOn (hmmc ω) φ hsD
      have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [SB.S3.wordChartMean]
      ring
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self] at hsupp
      have h0 : ∀ z, φ z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => notMem_empty z (hsupp hz)
      have hφ0 : φ = 0 := by
        ext z
        exact h0 z
      rw [hφ0, map_zero]
      have e : (fun z => m ω z * (0 : TestOn upperHalfPlaneOpens) z) = fun _ => 0 := by
        funext z
        rw [← hφ0, h0 z, mul_zero]
      rw [e, integral_zero]
  have hharm' : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (g ω) (H \ A' ω) := by
    filter_upwards [hg.2.1] with ω h
    by_cases hω : ω ∈ G
    · simpa only [hA', hω, ↓reduceIte] using h
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
      exact isHarmonicDistOn_empty _
  have hopen' : ∀ᵐ ω ∂c.P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · simpa only [hA', hω, ↓reduceIte] using (hBc ω).2
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self, isOpen_empty]
  have hm' : ∀ᵐ ω ∂c.P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A' ω) := by
    filter_upwards [hdomB] with ω hd
    by_cases hω : ω ∈ G
    · simp only [hA', hm, hω, ↓reduceIte]
      rw [← hd hω]
      exact hwcm ω
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
      exact fun z hz => absurd hz (notMem_empty z)
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hharm' hopen' hm' hφ'
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  filter_upwards [hall, hlive, hCtEq, hdomB, hβU] with ω hallω hlv hct hd hβ hlive' hlt hψ hc
  have hωG : ω ∈ G := hlv hlive' hlt
  set S : ℝ → ℝ := fun s => I.drv c s.toNNReal ω with hSdef
  set q : ℝ := ((I.clock c t ω).toNNReal : ℝ) with hqdef
  have hSc : Continuous S := (continuous_stgDrv (hv.2.1 ω) _).comp continuous_real_toNNReal
  have hS0 : S 0 = 0 := by
    change I.drv c (0 : ℝ).toNNReal ω = 0
    rw [Real.toNNReal_zero]
    exact stgDrv_zero _ _
  have hq : 0 ≤ q := NNReal.coe_nonneg _
  set cs : Chart := I.chart c ω with hcs
  have hdomCt : ((Ct ω).dom : Set ℂ) = cs.2.1 '' (H \ fwdHull S q) := by
    rw [(hCc ω).coe_dom, hct hωG, ← QuantumZipper.RS.image_fwdMapInv_H hSc hS0 hq, image_image]
    rfl
  have hψO : tsupport ψ ⊆ H \ fwdHull S q := fun y hy =>
    ⟨Coupling.tsupport_subset_H ψ hy, Set.disjoint_left.1 hψ hy⟩
  have hmcO : ContinuousOn (fun z => (βt ω).mean ((Ct ω).1 z) - chiC c.κ * (Ct ω).2.2 z)
      (cs.2.1 '' (H \ fwdHull S q)) := by
    rw [← hdomCt]
    exact hmmc ω
  have hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ cs.2.1 '' (H \ fwdHull S q) →
      (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens I.u₀) φ =
        ∫ z, ((βt ω).mean ((Ct ω).1 z) - chiC c.κ * (Ct ω).2.2 z) * φ z := by
    intro φ hφ
    rw [← hdomCt] at hφ
    have hsupp : tsupport φ ⊆ H \ A' ω := by
      simp only [hA', hωG, ↓reduceIte]
      rw [← hd hωG]
      exact hφ
    have hi1 := WholeField.integrable_mul_testOn (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (hwcm ω)) φ hφ
    have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
    have hmω : m ω = SB.S3.wordChartMean c.κ (βt ω) (Ct ω) I.u₀ := by simp only [hm, hωG, ↓reduceIte]
    rw [add_apply, hallω φ hsupp, Coupling.smoothDist_apply_eq hu₀c φ, hmω, ← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [SB.S3.wordChartMean]
    ring
  rw [Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset hc (hmc.2.1 ω) sdiff_subset hmcO hT I.σa I.kc
    hψO]
  refine congrArg _ (funext fun y => ?_)
  by_cases hy : y ∈ tsupport ψ
  · have hyO := hψO hy
    have hyH : y ∈ H := hyO.1
    have h1 : (Ct ω).1 (cs.2.1 y) = fwdMap S q y := by
      rw [hct hωG]
      change fwdMap S q (cs.1 (cs.2.1 y)) = _
      rw [hc.2.2 y hyH]
    have h2 : (Ct ω).2.2 (cs.2.1 y) = (logDerivFwd S q y).im + cs.2.2 (cs.2.1 y) := by
      rw [hct hωG]
      change (logDerivFwd S q (cs.1 (cs.2.1 y))).im + cs.2.2 (cs.2.1 y) = _
      rw [hc.2.2 y hyH]
    have hfH : fwdMap S q y ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hSc hq hyO
    have h3 := hβ hωG hfH
    simp only at h3
    rw [h1, h2, hkc]
    simp only [couplingMean]
    rw [← h3]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]

/-- **Named input: the stage chart law at time `t`** (the domain Markov property of the stage chart): an
`ℋ t`-event `G` containing the live event before the cap, a chart family `C_t` (measurable for `ℋ t`) equal on `G` to
the stage chart moved to the stage clock, with domain `ℍ ∖ B t`, the field `Y` read in it, and words `β_t` such that,
given `ℋ t`, `Y` is on `G` the GFF of `β_t`, whose mean raised by the stage offset is the canonical bounded harmonic
extension of the typed stage word flowed to the clock. -/
def StageChartLawAt (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (w : WordType) (t : ℝ≥0) : Prop :=
  ∃ (G : Set Ω) (Ct : Ω → Chart) (Y : Ω → DistOn upperHalfPlaneOpens) (βt : Ω → BoundaryWord),
    MeasurableSet[I.ℋ t] G ∧
    (∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G) ∧
    WalkInf.IsMeasChart (I.ℋ t) Ct ∧
    (∀ᵐ ω ∂c.P, ω ∈ G → Ct ω = (I.chart c ω).loewner (fun s : ℝ => I.drv c s.toNNReal ω)
      ((I.clock c t ω).toNNReal : ℝ)) ∧
    (∀ᵐ ω ∂c.P, ω ∈ G → ((Ct ω).dom : Set ℂ) = H \ I.B t ω) ∧
    Measurable Y ∧ (∀ᵐ ω ∂c.P, ω ∈ G → IsChartTransport (Ct ω) 1 0 (chiC c.κ) (c.h ω) (Y ω)) ∧
    (∀ ω, (βt ω).IsSorted) ∧
    (∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G →
      c.P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | I.ℋ t] ω = gaussCF (βt ω) ψ) ∧
    (∀ᵐ ω ∂c.P, ω ∈ G → EqOn (fun z => (βt ω).mean z + I.σa)
      (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
        (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
        (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
          (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
        (I.clock c t ω).toNNReal) H)

/-- **`LinesLocal.mean` from the stage chart law at every time** (with the locality fields of RELDET). -/
theorem StageInst.lines_mean_of_chartLaw (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R))
    (hu₀ : IsBoundedHarmonicExtension c.b c.jumps I.u₀) (hkc : I.kc = chiC c.κ) (w : WordType)
    (hℋ : ∀ t, I.ℋ t ≤ mΩ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (I.B t))
    (hBc : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P)
    (hlaw : ∀ t, StageChartLawAt I c r l w t) :
    ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, stageMeanAt I c r l w t ψ ω (g ω) := by
  intro t g hg ψ
  obtain ⟨G, Ct, Y, βt, hG, hlive, hCt, hCtEq, hdomB, hYm, htr, hβs, hlawt, hβU⟩ := hlaw t
  exact StageInst.mean_of_chartLaw I hv hpre hu₀ hkc w t (hℋ t) (hBm t) (hBc t) (hloc t) hG hlive hCt hCtEq hdomB
    hYm htr hβs hlawt hβU g hg ψ

end InteractingSLE.Theorem14.GW2Scl
