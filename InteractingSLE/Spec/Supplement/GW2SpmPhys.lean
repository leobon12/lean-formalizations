/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SclMean

/-!
# GW2's stage mean, chart-free: the physical conditional law and the stage-chart reading

Packet PROVE-GW2-STAGEMEAN, physical-law round. Last round's named input `GW2Scl.StageChartLawAt` fixed the chart
in which the law is read (the instance's stage chart moved to the clock). On the conditional-kernel route the law
arrives in ANOTHER chart: the relative chart of the conditional counterflow at `σ_k` composed with the launch chart.
Both charts map `ℍ ∖ B t` onto `ℍ`, send the explored tip to `0` and the counterflow tip to `∞`, so they differ by a
real Möbius map fixing `0, ∞` — a positive DILATION, which is in general not `1` (the two relative maps are normalized
at different boundary points). The law is therefore stated here in PHYSICAL coordinates, where it is chart-free, and
the chart enters only through a deterministic per-sample identity of harmonic functions:

* `measurableSet_tsupport_subset_H_diff`: `{ω | supp φ ⊆ ℍ ∖ A ω}` is an event of any σ-algebra for which a relatively
  closed random set `A` is hitting-measurable;
* **`ae_apply_eq_of_physLaw`** (generic): if, given marks `ℋ` for which `A` is history-avoidance local, the conditional
  characteristic function of `h₀(φ)` on an `ℋ`-event is Gaussian with mean `m` and the variance of `ℍ ∖ A` at every
  frequency, then every local-set mean of `A` gives `g(φ) = m` there;
* `exists_realMobius_of_same_dom`: two conformal charts with the same domain differ by a real Möbius map of `ℍ`
  (the structural form of the chart identity);
* **`StageInst.mean_of_physLaw`**: `stageMeanAt` for every local-set mean of `B t` from (G1) the physical conditional
  law of the centred field given `ℋ t` with a harmonic mean `M` and (G2) the stage-chart reading of `M`
  (`M + u₀` read in the stage chart, plus the offset and the lift, is the canonical coupling mean);
* **`StagePhysLawAt`** (named input, clauses (G1) and (G2)) and **`StageInst.lines_mean_of_physLaw`**: the target
  `LinesLocal.mean` from it at every time.

Conditional helper with distinct names; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC zeroGFFTestCov)

universe u

namespace InteractingSLE.Theorem14.GW2Spm

open GW2KM2 Restart Restart.DomainMarkov Restart.FCDet Exist.StagedLaw Sec7.PocketTraversal Supp8.GB6
  Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe GW2Rd GW2Sde GW2TipSystem GW2TipSystem.RootC24
  LocalSets WholeField Supp8.RelSafeS GW2Stl GW2Scl

/-! ### Generic facts -/

/-- **The support event of a relatively closed random set is measurable.** -/
theorem measurableSet_tsupport_subset_H_diff {Ω : Type*} {m : MeasurableSpace Ω} {A : Ω → Set ℂ}
    (hA : Measurable[m, hittingSigma] A) (hAc : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[m] {ω | tsupport φ ⊆ H \ A ω} := by
  set K : Set ℂ := tsupport φ with hKdef
  have hK : IsCompact K := φ.hasCompactSupport.isCompact
  have hKH : K ⊆ H := Coupling.tsupport_subset_H φ
  set U : ℕ → Set ℂ := fun n => Metric.thickening (1 / ((n : ℝ) + 1)) K ∩ H with hUdef
  have hUo : ∀ n, IsOpen (U n) := fun n => Metric.isOpen_thickening.inter QuantumZipper.isOpen_H
  have e : {ω | K ⊆ H \ A ω} = ⋃ n, A ⁻¹' {S : Set ℂ | Disjoint S (U n)} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open (hAc ω).2 hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      refine mem_iUnion.2 ⟨n, ?_⟩
      change Disjoint (A ω) (U n)
      rw [Set.disjoint_left]
      intro z hzA hzU
      exact (hsub (Metric.thickening_mono hn.le K hzU.1)).2 hzA
    · intro hω
      obtain ⟨n, hn⟩ := mem_iUnion.1 hω
      intro z hz
      refine ⟨hKH hz, fun hzA => ?_⟩
      have hzU : z ∈ U n := ⟨Metric.self_subset_thickening (by positivity) K hz, hKH hz⟩
      exact Set.disjoint_left.1 hn hzA hzU
  rw [e]
  exact MeasurableSet.iUnion fun n => hA (measurableSet_avoid (hUo n) inter_subset_right)

/-- **The local-set mean from a Gaussian conditional law given the marks** (the chart-free core of
`Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`). -/
theorem ae_apply_eq_of_physLaw {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (hℋ : ℋ ≤ mΩ) (hmark : IsHistoryAvoidanceLocal ℋ A h₀ P)
    (hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω)) {g : Ω → DistOn upperHalfPlaneOpens}
    (hg : IsLocalSetMean A h₀ P g) (φ : TestOn upperHalfPlaneOpens) {S : Set Ω} (hS : MeasurableSet[ℋ] S)
    {m : Ω → ℝ}
    (hlaw : ∀ r : ℝ, ∀ᵐ ω ∂P, ω ∈ S →
      (P[fun ω' => Complex.exp (Complex.I * ((r * h₀ ω' φ : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((r * m ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (r ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ)) :
    ∀ᵐ ω ∂P, ω ∈ S → g ω φ = m ω := by
  have hloc : IsLocalSet A h₀ P := ((isLocalSet_tfae hh hA hAc).out 4 1).2 hmark.isAvoidanceLocal
  set ψ : ℕ → Ω → ℂ := fun n => P[fun ω' => Complex.exp (Complex.I *
      ((1 / ((n : ℝ) + 1) * h₀ ω' φ : ℝ) : ℂ)) | ℋ] with hψ_def
  have hψm : ∀ n, StronglyMeasurable[ℋ] (ψ n) := fun n => stronglyMeasurable_condExp
  have hmm : Measurable[ℋ] (meanOfCharFun ψ) := measurable_meanOfCharFun hψm
  have hmeq : ∀ᵐ ω ∂P, ω ∈ S → meanOfCharFun ψ ω = m ω := by
    filter_upwards [ae_all_iff.2 fun n : ℕ => hlaw (1 / ((n : ℝ) + 1))] with ω hω hωS
    exact meanOfCharFun_eq fun n => hω n hωS
  have hkern : ∀ r : ℝ, ∀ᵐ ω ∂P, ω ∈ S →
      (P[fun ω' => Complex.exp (Complex.I * ((r * h₀ ω' φ : ℝ) : ℂ)) | ℋ]) ω =
        Complex.exp (Complex.I * ((r * meanOfCharFun ψ ω : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (r ^ 2 * zeroGFFTestCov (H \ A ω) φ φ)) : ℝ) : ℂ) := by
    intro r
    filter_upwards [hlaw r, hmeq] with ω h1 h2 hωS
    rw [h2 hωS]
    exact h1 hωS
  obtain ⟨k1, -⟩ := ae_condExp_germSigma_history_eq hh hA hℋ hmark hAc φ hS hmm hkern
  have e := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hh hA hloc hℋ hmark hg φ
  filter_upwards [k1, e, hmeq] with ω h1 h2 h3 hωS
  rw [h2, h1 hωS, h3 hωS]

/-- **Two conformal charts with the same domain differ by a real Möbius map of `ℍ`.** -/
theorem exists_realMobius_of_same_dom {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal)
    (hdom : (c.dom : Set ℂ) = d.dom) :
    ∃ a b e f : ℝ, 0 < a * f - b * e ∧ EqOn (fun w => d.1 (c.2.1 w)) (QuantumZipper.CA.realMobius a b e f) H := by
  have hmaps : MapsTo c.2.1 H d.dom := fun w hw => by
    have h := hc.inv_mem_dom hw
    rw [← SetLike.mem_coe, hdom] at h
    exact h
  have hdiff : DifferentiableOn ℂ (fun w => d.1 (c.2.1 w)) H :=
    hd.differentiableOn_fwd.comp hc.1 hmaps
  refine QuantumZipper.CA.exists_realMobius_of_bijOn_H hdiff ⟨fun w hw => hd.fwd_mem (hmaps hw), ?_, ?_⟩
  · intro w₁ hw₁ w₂ hw₂ h
    have h' : d.2.1 (d.1 (c.2.1 w₁)) = d.2.1 (d.1 (c.2.1 w₂)) := congrArg d.2.1 h
    rw [hd.inv_fwd (hmaps hw₁), hd.inv_fwd (hmaps hw₂)] at h'
    exact hc.injOn hw₁ hw₂ h'
  · intro v hv
    have hvd : d.2.1 v ∈ (c.dom : Set ℂ) := by
      rw [hdom]
      exact hd.inv_mem_dom hv
    rw [hc.coe_dom] at hvd
    obtain ⟨w, hw, hwv⟩ := hvd
    exact ⟨w, hw, by simp only [hwv, hd.2.2 v hv]⟩

/-! ### The stage mean from the physical law -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)}

/-- **The stage identity from the physical conditional law and the stage-chart reading.** -/
theorem StageInst.mean_of_physLaw [IsProbabilityMeasure c.P] (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType) (t : ℝ≥0)
    (hzero : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h I.u₀) c.P)
    (hharm : InnerProductSpace.HarmonicOnNhd I.u₀ H)
    (hℋ : I.ℋ t ≤ mΩ) (hBm : Measurable[mΩ, hittingSigma] (I.B t))
    (hBℋ : Measurable[I.ℋ t, hittingSigma] (I.B t)) (hBc : ∀ ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hloc : IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P)
    {G : Set Ω} (hG : MeasurableSet[I.ℋ t] G)
    (hlive : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G)
    (hshape : ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω →
      H \ I.B t ω = (I.chart c ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    {M : Ω → ℂ → ℝ} (hMh : ∀ ω, InnerProductSpace.HarmonicOnNhd (M ω) (H \ I.B t ω))
    (hlaw : ∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, M ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ))
    (hread : ∀ᵐ ω ∂c.P, ω ∈ G → ∀ z ∈ H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω)
        ((I.clock c t ω).toNNReal : ℝ),
      M ω ((I.chart c ω).2.1 z) + I.u₀ ((I.chart c ω).2.1 z) + I.σa +
          I.kc * (I.chart c ω).2.2 ((I.chart c ω).2.1 z) =
        couplingMean c.κ (fun s : ℝ => I.drv c s.toNNReal ω) (I.clock c t ω).toNNReal
          (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
              (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
              (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
            (I.clock c t ω).toNNReal) z)
    (g : Ω → DistOn upperHalfPlaneOpens) (hg : IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g)
    (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, stageMeanAt I c r l w t ψ ω (g ω) := by
  classical
  have hu₀c : ContinuousOn I.u₀ H := fun z hz => (hharm z hz).1.continuousAt.continuousWithinAt
  -- (G1) gives the mean test function by test function
  have hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      g ω φ = ∫ z, M ω z * φ z := by
    intro φ
    have hSm : MeasurableSet[I.ℋ t] (G ∩ {ω | tsupport φ ⊆ H \ I.B t ω}) :=
      hG.inter (measurableSet_tsupport_subset_H_diff hBℋ hBc φ)
    have h := ae_apply_eq_of_physLaw hzero hBm hℋ hloc (Eventually.of_forall hBc) hg φ hSm
      (m := fun ω => ∫ z, M ω z * φ z) fun ρ => (hlaw φ ρ).mono fun ω hω hωS => hω hωS.1 hωS.2
    filter_upwards [h] with ω hω hωG hsupp
    exact hω ⟨hωG, hsupp⟩
  -- the cut-off union and mean
  set A' : Ω → Set ℂ := fun ω => if ω ∈ G then I.B t ω else H with hA'
  set m : Ω → ℂ → ℝ := fun ω => if ω ∈ G then M ω else 0 with hm
  have hφ' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, tsupport φ ⊆ H \ A' ω →
      g ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [hφ φ] with ω h1 hsupp
    by_cases hω : ω ∈ G
    · simp only [hA', hω, ↓reduceIte] at hsupp
      simp only [hm, hω, ↓reduceIte]
      exact h1 hω hsupp
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
  have hm' : ∀ᵐ ω ∂c.P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hA', hm, hω, ↓reduceIte]
      exact hMh ω
    · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
      exact fun z hz => absurd hz (notMem_empty z)
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hharm' hopen' hm' hφ'
  have hmc := isMeasChart_stgChart (measurable_gb6Rec_src c) hv.2.1 hv.2.2.1 hpre
  filter_upwards [hall, hlive, hshape, hread] with ω hallω hlv hsh hrd hlive' hlt hψ hc
  have hωG : ω ∈ G := hlv hlive' hlt
  set S : ℝ → ℝ := fun s => I.drv c s.toNNReal ω with hSdef
  set q : ℝ := ((I.clock c t ω).toNNReal : ℝ) with hqdef
  set cs : Chart := I.chart c ω with hcs
  have hψO : tsupport ψ ⊆ H \ fwdHull S q := fun y hy =>
    ⟨Coupling.tsupport_subset_H ψ hy, Set.disjoint_left.1 hψ hy⟩
  have hO : cs.2.1 '' (H \ fwdHull S q) = H \ I.B t ω := (hsh hlive' hlt).symm
  have hmcO : ContinuousOn (fun z => M ω z + I.u₀ z) (cs.2.1 '' (H \ fwdHull S q)) := by
    rw [hO]
    exact (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (hMh ω)).add (hu₀c.mono sdiff_subset)
  have hT : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ cs.2.1 '' (H \ fwdHull S q) →
      (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens I.u₀) φ =
        ∫ z, (M ω z + I.u₀ z) * φ z := by
    intro φ hφ
    rw [hO] at hφ
    have hsupp : tsupport φ ⊆ H \ A' ω := by
      simp only [hA', hωG, ↓reduceIte]
      exact hφ
    have hmω : m ω = M ω := by simp only [hm, hωG, ↓reduceIte]
    have hi1 := WholeField.integrable_mul_testOn (Sec5.Aux61SlitV.continuousOn_of_harmonicOnNhd (hMh ω)) φ hφ
    have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
    rw [add_apply, hallω φ hsupp, Coupling.smoothDist_apply_eq hu₀c φ, hmω, ← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [add_mul]
  rw [Sec5.Aux61SlitV.chartTransport_apply_eq_integral_of_subset hc (hmc.2.1 ω) sdiff_subset hmcO hT I.σa I.kc
    hψO]
  refine congrArg _ (funext fun y => ?_)
  by_cases hy : y ∈ tsupport ψ
  · rw [← hrd hωG y (hψO hy)]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]

/-- **Named input: the physical stage law at time `t`** — (G1) given the marks `ℋ t`, on an `ℋ t`-event `G`
containing the live event before the cap, the centred field tested against `φ` supported off `B t` is Gaussian with
mean `∫ M φ` (a harmonic `M` on `ℍ ∖ B t`) and the variance of `ℍ ∖ B t`; (G2) read in the stage chart, `M + u₀`
plus the stage offset and lift is the canonical coupling mean of the typed stage word along the stage driver. -/
def StagePhysLawAt (I : StageInst Ω) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (w : WordType) (t : ℝ≥0) : Prop :=
  ∃ (G : Set Ω) (M : Ω → ℂ → ℝ), MeasurableSet[I.ℋ t] G ∧
    (∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω → ω ∈ G) ∧
    (∀ ω, InnerProductSpace.HarmonicOnNhd (M ω) (H \ I.B t ω)) ∧
    (∀ (φ : TestOn upperHalfPlaneOpens) (ρ : ℝ), ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ I.B t ω →
      (c.P[fun ω' => Complex.exp (Complex.I * ((ρ * centredField c.h I.u₀ ω' φ : ℝ) : ℂ)) | I.ℋ t]) ω =
        Complex.exp (Complex.I * ((ρ * ∫ z, M ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * (ρ ^ 2 * zeroGFFTestCov (H \ I.B t ω) φ φ)) : ℝ) : ℂ)) ∧
    (∀ᵐ ω ∂c.P, ω ∈ G → ∀ z ∈ H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ),
      M ω ((I.chart c ω).2.1 z) + I.u₀ ((I.chart c ω).2.1 z) + I.σa +
          I.kc * (I.chart c ω).2.2 ((I.chart c ω).2.1 z) =
        couplingMean c.κ (fun s : ℝ => I.drv c s.toNNReal ω) (I.clock c t ω).toNNReal
          (bheProc c.κ (typedRhoL w) (typedRhoR w) (I.drv c)
            (fun i t ω => geomLW canonDrv (fun y => typedXL c.κ w (I.β y.1)) i t
              (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω))
            (fun j t ω => geomRW canonDrv (fun y => typedXR c.κ w (I.β y.1)) j t
              (I.srec c r l ω, relVar I.Hr (I.drv c) (I.cap c) ω)) ω
            (I.clock c t ω).toNNReal) z)

/-- **`LinesLocal.mean` from the physical stage law at every time** (with RELDET's locality fields and the stage shape
in the stage chart). -/
theorem StageInst.lines_mean_of_physLaw [IsProbabilityMeasure c.P] (I : StageInst Ω)
    (hv : IsGB6RelVersion c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hpre : Measurable (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R)) (w : WordType)
    (hzero : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h I.u₀) c.P)
    (hharm : InnerProductSpace.HarmonicOnNhd I.u₀ H)
    (hℋ : ∀ t, I.ℋ t ≤ mΩ) (hBm : ∀ t, Measurable[mΩ, hittingSigma] (I.B t))
    (hBℋ : ∀ t, Measurable[I.ℋ t, hittingSigma] (I.B t)) (hBc : ∀ t ω, I.B t ω ⊆ H ∧ IsOpen (H \ I.B t ω))
    (hloc : ∀ t, IsHistoryAvoidanceLocal (I.ℋ t) (I.B t) (centredField c.h I.u₀) c.P)
    (hshape : ∀ t : ℝ≥0, ∀ᵐ ω ∂c.P, ω ∈ liveEvRec c.κ w I.β I.E (I.srec c r l) → I.clock c t ω < I.cap c ω →
      H \ I.B t ω = (I.chart c ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => I.drv c s.toNNReal ω) ((I.clock c t ω).toNNReal : ℝ)))
    (hlaw : ∀ t, StagePhysLawAt I c r l w t) :
    ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
      IsLocalSetMean (I.B t) (centredField c.h I.u₀) c.P g → ∀ ψ : TestOn upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, stageMeanAt I c r l w t ψ ω (g ω) := by
  intro t g hg ψ
  obtain ⟨G, M, hG, hlive, hMh, hlawt, hread⟩ := hlaw t
  exact StageInst.mean_of_physLaw I hv hpre w t hzero hharm (hℋ t) (hBm t) (hBℋ t) (hBc t) (hloc t) hG hlive
    (hshape t) hMh hlawt hread g hg ψ

end InteractingSLE.Theorem14.GW2Spm
