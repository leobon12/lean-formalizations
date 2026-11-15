/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeMain
import InteractingSLE.Spec.Supplement.GB6LMeanDet
import InteractingSLE.Spec.Sec5.CrossCondStagedMean
import InteractingSLE.Spec.Sec5.StagedDepthSample

/-!
# BW1's union mean, part 1: the mean of the TERMINAL retained set

Packet PROVE-BW1-LINEMEAN. GB6's retained mean (`Supp8.GB6LMean.ae_eqOn_retMean`) works at an own time `s` strictly
before the flow's lifetime, transferring the means from stopped hulls at announcing stops. BW1 retains the COMPLETED
first piece, stopped at a continuation threshold (its record's own time is the lifetime), so no announcing stop reaches
it. Instead the mean is read from the staged law at the first instruction: conditionally on the retained past (the
record `rec`), the field read in the chart right after the piece is the GFF of the stop word
(`BW1Life.ae_bwField_gff`); in the counterflow frame this is the GFF of BW1's relative word `bwRelWord` read through
the relative chart of the record (`GW1Laws.isGFFWithBoundaryData_cfField_cfWordOf`, `bwRelField_eq_chartTransport`),
and the local-set mean of a set marked local for `σ(rec)` whose complement is the chart domain is the chart mean
(`Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw`).

* the relative chart of a record: its domain is `ℍ ∖ invHull`, its forward map is `relMap`, its lift is
  `Im relLog − 2π` (`coe_dom_relChart`, `relChart_fst`, `relChart_lift_eq`), its closed-disc events are measurable
  (`measurableSet_closedBall_subset_dom_relChart`);
* `gaussCF_vshift`: the Gaussian characteristic value of a word shifted by a constant;
* **`ae_eqOn_bRetMean`**: the retained mean in GB6's form `w₁ + 𝔥⁰ = G₀ ∘ Ψ − χ(16/κ) Im relLog` on the record event.

R48: BW1 serves Theorem 1.4; Theorems 1.2–1.3 enter only through `exists_bw1_retained_marks` (field determination).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1LMean

open Exist Exist.Staged Exist.StagedLaw Supp8.GB6 Supp8.RelSafeS LocalSets Restart BW1Ver BW1Life BW1Safe

/-! ### The retained set of a record -/

section Ret

theorem bRetOfRec_subset_H (TS : Set RecData) (r : RecData) : bRetOfRec TS r ⊆ H := by
  unfold bRetOfRec
  split_ifs
  · exact WangWu.image_negInv_subset_H (QuantumZipper.fwdHull_mono.2 _)
  · exact subset_rfl

theorem isOpen_H_diff_bRetOfRec (TS : Set RecData) (r : RecData) : IsOpen (H \ bRetOfRec TS r) := by
  unfold bRetOfRec
  split_ifs
  · rw [Supp8.Q3Rel.compl_invHull]
    exact WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rdrv _)
      (recS r).coe_nonneg) sdiff_subset
  · simp only [Set.sdiff_self, isOpen_empty]

theorem bRetOfRec_of_mem {TS : Set RecData} {r : RecData} (hr : r ∈ TS) :
    bRetOfRec TS r = Supp8.Q3Rel.invHull (rdrv r) (recS r) := by
  simp only [bRetOfRec, hr, ↓reduceIte]

theorem bRetOfRec_of_notMem {TS : Set RecData} {r : RecData} (hr : r ∉ TS) : bRetOfRec TS r = H := by
  simp only [bRetOfRec, hr, ↓reduceIte]

theorem not_isBounded_lowerUnion_bRetOfRec (TS : Set RecData) (r : RecData) :
    ∀ z ∈ lowerUnion (bRetOfRec TS r),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (bRetOfRec TS r)) z) := by
  unfold bRetOfRec
  split_ifs
  · exact Sec5.GlueCond.not_isBounded_lowerUnion_image_negInv
      (isHPHull_fwdHull (continuous_rdrv _) (recS r).coe_nonneg)
  · intro z _
    have e : lowerUnion H = univ := by
      ext w
      simp only [lowerUnion, mem_union, mem_univ, iff_true]
      by_cases hw : 0 < w.im
      · exact Or.inl hw
      · exact Or.inr (not_lt.1 hw)
    rw [e, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    intro hb
    have : CompactSpace ℂ := Metric.compactSpace_iff_isBounded_univ.2 hb
    exact noncompact_univ ℂ isCompact_univ

end Ret

/-! ### The relative chart of a record -/

section Chart

theorem coe_dom_relChart (r : RecData) :
    ((relChart r).dom : Set ℂ) = H \ Supp8.Q3Rel.invHull (rdrv r) (recS r) := by
  rw [(isConformal_relChart r).coe_dom, relChart_eq_jointChart (s := recS r) rfl]
  exact (Supp8.Q3Rel.isDomainChart_rel (continuous_rdrv r) (rdrv_zero r) (recS r).coe_nonneg).2.1

theorem relChart_fst (r : RecData) : (relChart r).1 = relMap (rdrv r) (recS r) := by
  rw [relChart_eq_jointChart (s := recS r) rfl]
  rfl

theorem relChart_lift_eq (r : RecData) {z : ℂ} (hz : z ∈ (relChart r).dom) :
    (relChart r).2.2 z = (Supp8.Q3Rel.relLog (rdrv r) (recS r) z).im - 2 * Real.pi := by
  have hc := isConformal_relChart r
  have hfH : (relChart r).1 z ∈ H := hc.fwd_mem hz
  have hzi : (relChart r).2.1 ((relChart r).1 z) = z := hc.inv_fwd hz
  have hrel := relChart_eq_jointChart (r := r) (s := recS r) rfl
  have h1 := Supp8.GB6LMean.jointChart_lift_inv (continuous_rdrv r) (rdrv_zero r) (recS r).coe_nonneg hfH
  rw [← hrel, hzi] at h1
  exact h1

theorem relMap_mem_H_of_mem_dom (r : RecData) {z : ℂ} (hz : z ∈ (relChart r).dom) :
    relMap (rdrv r) (recS r) z ∈ H := by
  rw [← relChart_fst]
  exact (isConformal_relChart r).fwd_mem hz

/-- **Closed-disc events of the relative chart of a record are measurable.** -/
theorem measurableSet_closedBall_subset_dom_relChart (z : ℂ) (ε : ℝ) :
    MeasurableSet {r : RecData | closedBall z ε ⊆ (relChart r).dom} := by
  by_cases hB : closedBall z ε ⊆ H
  · have h0 : ∀ x ∈ closedBall z ε, x ≠ 0 := fun x hx h => by
      have := hB hx
      rw [h] at this
      exact lt_irrefl _ (show (0 : ℂ).im > 0 from this)
    have hcont : ContinuousOn (fun x : ℂ => -x⁻¹) (closedBall z ε) := fun x hx =>
      ((continuousAt_inv₀ (h0 x hx)).neg).continuousWithinAt
    have hD : IsClosed ((fun x : ℂ => -x⁻¹) '' closedBall z ε) :=
      ((isCompact_closedBall z ε).image_of_continuousOn hcont).isClosed
    have e : {r : RecData | closedBall z ε ⊆ (relChart r).dom} =
        {r : RecData | Disjoint ((fun x : ℂ => -x⁻¹) '' closedBall z ε) (fwdHull (rdrv r) (recS r))} := by
      ext r
      simp only [mem_ofPred_eq]
      rw [coe_dom_relChart]
      constructor
      · intro hs
        refine Set.disjoint_left.2 ?_
        rintro _ ⟨x, hx, rfl⟩ hK
        refine (hs hx).2 ⟨-x⁻¹, hK, ?_⟩
        change -(-x⁻¹)⁻¹ = x
        rw [inv_neg, inv_inv, neg_neg]
      · intro hd x hx
        refine ⟨hB hx, ?_⟩
        rintro ⟨y, hy, hyx⟩
        refine Set.disjoint_left.1 hd ⟨x, hx, rfl⟩ ?_
        have : -x⁻¹ = y := by
          rw [← hyx]
          change -(-y⁻¹)⁻¹ = y
          rw [inv_neg, inv_inv, neg_neg]
        change -x⁻¹ ∈ _
        rw [this]
        exact hy
    rw [e]
    have h := Supp8.GB6LineL.measurableSet_disjoint_fwdHull_rand (m := inferInstance)
      (B := fun t (r : RecData) => rdrv r (t : ℝ)) (fun r => (continuous_rdrv r).comp NNReal.continuous_coe)
      (fun t => measurable_rdrv_apply (t : ℝ)) (q := fun r => (recS r : ℝ))
      (measurable_coe_nnreal_real.comp measurable_recS) (fun r => (recS r).coe_nonneg) hD
    rw [Supp8.GB6LineL.drive_rdrv] at h
    exact h
  · have e : {r : RecData | closedBall z ε ⊆ (relChart r).dom} = ∅ := by
      ext r
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun hs => hB (hs.trans (dom_relChart_subset_H r))
    rw [e]
    exact MeasurableSet.empty

end Chart

/-! ### A word shifted by a constant -/

section Shift

open Sec5.CrossCond.StagedDepth

/-- The Gaussian characteristic value of a word whose values are shifted by `a`. -/
theorem gaussCF_vshift (c : BoundaryWord) (a : ℝ) (ψ : TestOn upperHalfPlaneOpens) :
    gaussCF (vshift c a) ψ = Complex.exp (Complex.I * ((a * ∫ z, ψ z : ℝ) : ℂ)) * gaussCF c ψ := by
  have hi1 : Integrable fun z => c.mean z * ψ z :=
    WholeField.integrable_mul_testOn (BoundaryWord.continuousOn_mean c) ψ ψ.tsupport_subset
  have hi2 : Integrable fun z => a * ψ z :=
    (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport).const_mul a
  have e : (∫ z, (vshift c a).mean z * ψ z) = (∫ z, c.mean z * ψ z) + a * ∫ z, ψ z := by
    have hf : (fun z => (vshift c a).mean z * ψ z) = fun z => c.mean z * ψ z + a * ψ z := by
      funext z
      rw [mean_vshift]
      ring
    rw [hf, integral_add hi1 hi2, integral_const_mul]
  unfold gaussCF
  rw [e, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Shift

/-! ### The conditional law of BW1's relative field given the record -/

section Law

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **`σ(rec)` is the retained past of the regularized history after the first instruction.** -/
theorem comap_bwRec_eq_pastSigma :
    MeasurableSpace.comap (bwRec κ b jumps (bwSpec gw2 θ t rest) E) inferInstance =
      pastSigma κ b jumps (bwSpec gw2 θ t rest) (StagedReg.regHist (bwSpec gw2 θ t rest) E) 1 := by
  refine le_antisymm (measurable_pastSigma_pastMap_one_last (κ := κ) (b := b) (jumps := jumps)).comap_le ?_
  rw [pastSigma_eq_comap]
  have e : pastMap κ b jumps (bwSpec gw2 θ t rest) (StagedReg.regHist (bwSpec gw2 θ t rest) E) 1 =
      fun ω (_ : Fin 1) => bwRec κ b jumps (bwSpec gw2 θ t rest) E ω := by
    funext ω i
    rw [Fin.fin_one_eq_zero i]
    rfl
  rw [e]
  exact (@measurable_pi_iff Ω (Fin 1) (fun _ => RecData)
    (MeasurableSpace.comap (bwRec κ b jumps (bwSpec gw2 θ t rest) E) inferInstance) _ _ |>.2
      fun _ => comap_measurable (bwRec κ b jumps (bwSpec gw2 θ t rest) E)).comap_le

/-- **The conditional law of BW1's relative field given the record** (the staged law at the first instruction,
`ae_bwField_gff`, read in the counterflow frame): almost surely on the record event, the conditional characteristic
functional of `bwRelField` given `σ(rec)` is the Gaussian one of BW1's relative word `bwRelWord`. -/
theorem ae_condExp_cexp_bwRelField (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) {c₀ : BoundaryWord}
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) {r : Bool} {TS : Set RecData}
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔
      bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) (ψ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS →
      P[fun ω' => Complex.exp (Complex.I * (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E ω' ψ : ℂ)) |
          MeasurableSpace.comap (bwRec κ b jumps (bwSpec gw2 θ t rest) E) inferInstance] ω =
        gaussCF (bwRelWord κ θ c₀ (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) ψ := by
  obtain ⟨hκ, -, hb, hh, -, -, -, hS⟩ := hset
  set spec := bwSpec gw2 θ t rest with hspec
  set E' := StagedReg.regHist spec E with hE'
  have hEm' : ∀ j, Measurable (E' j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (E' j ω) := fun j ω => StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable (bwRec κ b jumps spec E) := measurable_pastMap_one_last hb hEm' hreg'
  have hXm : Measurable (bwRelField κ b jumps spec h E) :=
    (GW4Traverse.measurable_cfField κ).comp (measurable_bwField hb hh.1 hEm' hreg')
  have hlaw := (ae_bwField_gff (θ := θ) (t := t) (rest := rest) hκ hb hh rfl hEm' hreg' (stageOK_regHist_zero hS)
    hc₀J hc₀).2
  have hk := condExp_ae_eq_integral_condExpKernel hrec.comap_le
    (GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply ψ).comp hXm))
  rw [comap_bwRec_eq_pastSigma] at hk ⊢
  filter_upwards [hk, hlaw, hFTS] with ω hkω hlω hF hTS
  have hfin : min t (E' 0 ω).2 ≠ ⊤ := by
    rw [hE', StagedReg.regHist_snd]
    exact finStop_of_mem_bwEvent (hF.2 hTS)
  refine hkω.trans ?_
  have hsort := isSorted_stopWord κ (BoundaryWord.shiftW spec.1 c₀, θ, pastMap κ b jumps spec E' 1 ω (Fin.last 0))
  have hG := GW1Laws.isGFFWithBoundaryData_cfField_cfWordOf κ hsort (hlω hfin)
  exact integral_cexp_eq_gaussCF (GW1Laws.isSorted_cfWordOf κ hsort) hG ψ

end Law

/-! ### The retained mean -/

section Mean

open Sec5.CrossCond.StagedDepth

/-- The chart mean of a word through the relative chart of a record, centred: `𝔤_β ∘ Ψ − χ ℓ − 𝔥`. -/
def chartMeanFn (χ : ℝ) (β : BoundaryWord) (r : RecData) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  β.mean ((relChart r).1 z) - χ * (relChart r).2.2 z - u z

theorem harmonicOnNhd_chartMeanFn (χ : ℝ) {β : BoundaryWord} (hβ : β.IsSorted) (r : RecData) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) :
    InnerProductSpace.HarmonicOnNhd (chartMeanFn χ β r u) (relChart r).dom := by
  have hc := isConformal_relChart r
  have h1 : InnerProductSpace.HarmonicOnNhd (β.mean ∘ (relChart r).1) (relChart r).dom :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H (relChart r).dom.isOpen
      (BoundaryWord.isBoundedHarmonicExtension_mean β hβ).1 hc.differentiableOn_fwd fun z hz => hc.fwd_mem hz
  intro z hz
  have h2 := (harmonicOnNhd_lift_relChart r z hz).const_smul (c := χ)
  have e : chartMeanFn χ β r u = (β.mean ∘ (relChart r).1 - χ • (relChart r).2.2) - u := by
    funext y
    simp only [chartMeanFn, Pi.sub_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact ((h1 z hz).sub h2).sub (hu z (dom_relChart_subset_H r hz))

theorem continuousOn_chartMeanFn (χ : ℝ) {β : BoundaryWord} (hβ : β.IsSorted) (r : RecData) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) : ContinuousOn (chartMeanFn χ β r u) (relChart r).dom :=
  fun z hz => (harmonicOnNhd_chartMeanFn χ hβ r hu z hz).1.continuousAt.continuousWithinAt

/-- The bounded harmonic extension of a sorted word's counterflow data is its explicit mean. -/
theorem eqOn_bhe_cfData_mean {k : ℝ} (hk : 0 < k) {β : BoundaryWord} (hβ : β.IsSorted) {G₀ : ℂ → ℝ}
    (hG₀ : IsBoundedHarmonicExtension (Supp8.Q3Chain.cfData k β.fn β.jumps) (Supp8.Q3Chain.cfJumps β.fn β.jumps) G₀) :
    EqOn G₀ β.mean H := by
  refine Supp8.GB6LMean.eqOn_bhe_of_eqOff (Finset.finite_toSet _) (Finset.finite_toSet _)
    (BoundaryWord.isBoundedHarmonicExtension_mean β hβ) hG₀ fun x hx1 hx2 => ?_
  have hx0 : x ≠ 0 := fun h => hx2 (by
    rw [h]
    exact Finset.mem_insert_self _ _)
  have hxJ : x + 0 ∉ β.jumps := by rw [add_zero]; exact hx1
  rw [Supp8.Q3Chain.cfData, Exist.forceBoundaryData_flowLine_seed hk (BoundaryWord.isPiecewiseConstantBoundaryData β)
    0 0 hx0 hxJ, add_zero, zero_mul, add_zero]

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The retained mean of Proposition BW1** (the TERMINAL retained set). In BW1's setting, with Theorems 1.2–1.3, a
record event `TS` of the threshold event and the counterflow frame `(b′, J′, h′)` with its initial extension `𝔥⁰`
(`h′ − 𝔥⁰` a zero-boundary GFF): almost surely on the record event, every harmonic representative `w₁` of the local-set
mean of the retained set `R(A) = bRetOfRec TS rec` satisfies `w₁ + 𝔥⁰ = G₀ ∘ Ψ − χ(16/κ) Im relLog` off `R(A)`, for
every bounded harmonic extension `G₀` of the counterflow data of BW1's relative word (`Ψ = relMap`, the retained chart
of the record at its own time). -/
theorem ae_eqOn_bRetMean (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) {r : Bool} {TS : Set RecData}
    (hTS : MeasurableSet TS)
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔
      bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS)
    {c₀ : BoundaryWord} (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    {b' : ℝ → ℝ} {J' : Finset ℝ} {h' : Ω → DistOn upperHalfPlaneOpens}
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    (hcfl : IsFlowLineDriver (16 / κ) b' J' 0 P h' W' ζ') {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (Supp8.Q3Chain.cfData (16 / κ) b' J')
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P)
    {g₁ : Ω → DistOn upperHalfPlaneOpens}
    (hg₁ : IsLocalSetMean (fun ω => bRetOfRec TS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω))
      (WholeField.centredField h' u₀) P g₁) :
    ∀ᵐ ω ∂P, bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS →
      ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (Supp8.Q3Chain.cfData (16 / κ) (bwRelWord κ θ c₀ (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)).fn
            (bwRelWord κ θ c₀ (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)).jumps)
          (Supp8.Q3Chain.cfJumps (bwRelWord κ θ c₀ (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)).fn
            (bwRelWord κ θ c₀ (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁
            (H \ bRetOfRec TS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) →
          (∀ φ : TestOn upperHalfPlaneOpens,
            tsupport φ ⊆ H \ bRetOfRec TS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω) →
              g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => G₀ (relMap (rdrv (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω))
                (recS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) z) -
              chiC (16 / κ) * (Supp8.Q3Rel.relLog (rdrv (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω))
                (recS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) z).im)
            (H \ bRetOfRec TS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) := by
  classical
  have hset' := hset
  obtain ⟨hκ, -, hb, hh, -, -, -, hS⟩ := hset'
  set spec := bwSpec gw2 θ t rest with hspec
  set rec := bwRec κ b jumps spec E with hrecdef
  have hEm' : ∀ j, Measurable (StagedReg.regHist spec E j) := StagedReg.measurable_regHist hS.1
  have hreg' : ∀ j ω, IsRegularDriver (StagedReg.regHist spec E j ω) := fun j ω =>
    StagedReg.isRegularDriver_regHist j ω
  have hrec : Measurable rec := measurable_pastMap_one_last hb hEm' hreg'
  have hk : 0 < 16 / κ := by positivity
  set χ' := chiC (16 / κ) with hχ'
  -- the counterflow frame
  have hh'eq : ∀ ω, h' ω = GW4Traverse.cfField κ (h ω) := fun ω =>
    (hT ω).unique Chart.isConformal_infinitySourceChart (GW4Traverse.isChartTransport_cfField κ (h ω))
  have hX : ∀ ω, bwRelField κ b jumps spec h E ω =
      Chart.chartTransport (isConformal_relChart (rec ω)) 1 (2 * Real.pi * χ') χ' (h' ω) := fun ω => by
    rw [hh'eq]
    exact bwRelField_eq_chartTransport hκ _ rfl h E ω
  have hXm : Measurable (bwRelField κ b jumps spec h E) :=
    (GW4Traverse.measurable_cfField κ).comp (measurable_bwField hb hh.1 hEm' hreg')
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcfl
  -- the extension of the counterflow data `b′`
  obtain ⟨u₁, hu₁, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb'
  have hfin : (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)).Finite := by
    rw [← Supp8.Q3Chain.coe_initJumps]
    exact Finset.finite_toSet _
  have hu₀₁ : EqOn u₀ u₁ H := by
    refine Supp8.GB6LMean.eqOn_bhe_of_eqOff (Finset.finite_toSet J') hfin hu₁ hu₀ fun x hx1 hx2 => ?_
    have hx0 : x ≠ 0 := fun h0 => hx2 (by
      rw [h0, ← Supp8.Q3Chain.coe_initJumps]
      exact Finset.mem_insert_self _ _)
    have hxJ : x + 0 ∉ J' := by rw [add_zero]; exact hx1
    rw [Supp8.Q3Chain.cfData, Exist.forceBoundaryData_flowLine_seed hk hb' 0 0 hx0 hxJ, add_zero, zero_mul,
      add_zero]
  have hcen1 : WholeField.centredField h' u₀ = WholeField.centredField h' u₁ := by
    have e := WangWu.smoothDist_congr (fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt)
      (fun z hz => (hu₁.1 z hz).1.continuousAt.continuousWithinAt) hu₀₁
    funext ω
    simp only [WholeField.centredField, e]
  -- the retained set is marked local for the record
  obtain ⟨uo, huo, -⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension c₀.isPiecewiseConstantBoundaryData
  have huob : IsBoundedHarmonicExtension b jumps uo := by
    have h1 : IsBoundedHarmonicExtension c₀.fn jumps uo := by rw [← hc₀J]; exact huo
    exact (Restart.isBoundedHarmonicExtension_congr (fun y hy => hc₀ y hy) uo).1 h1
  have hcen := Supp8.Q3Chain.centredField_eq_reflect hκ hb hh hb' hG' hT huob hu₀
  obtain ⟨-, hloc⟩ := exists_bw1_retained_marks h12 h13 hset hc₀ huo hh0 (fun ω => hcen ω) hTS hFTS
  set A : Ω → Set ℂ := fun ω => bRetOfRec TS (rec ω) with hAdef
  have hAm : Measurable[mΩ, hittingSigma] A := (measurable_bRetOfRec hTS).comp hrec
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) :=
    Eventually.of_forall fun ω => ⟨bRetOfRec_subset_H TS _, isOpen_H_diff_bRetOfRec TS _⟩
  have hmark : WholeField.IsHistoryAvoidanceLocal (MeasurableSpace.comap rec inferInstance) A
      (WholeField.centredField h' u₁) P := by
    rw [← hcen1]
    intro U G hUH hG hd F hF
    exact hloc U G hUH hG hd F (le_sup_left (b := Ito.nullSets P) F hF)
  have hh1 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₁) P := by
    rw [← hcen1]; exact hh0
  have hlocA : IsLocalSet A (WholeField.centredField h' u₁) P :=
    ((isLocalSet_tfae hh1 hAm hAc).out 4 1).2 hmark.isAvoidanceLocal
  have hg₁' : IsLocalSetMean A (WholeField.centredField h' u₁) P g₁ := by rw [← hcen1]; exact hg₁
  -- the chart field with coefficients `1, 0, χ′` and its conditional law given the record
  set Y : Ω → DistOn upperHalfPlaneOpens := fun ω =>
    Chart.chartTransport (isConformal_relChart (rec ω)) 1 0 χ' (h' ω) with hYdef
  have hYapp : ∀ ω (ψ : TestOn upperHalfPlaneOpens),
      Y ω ψ = bwRelField κ b jumps spec h E ω ψ - 2 * Real.pi * χ' * ∫ z, ψ z := fun ω ψ => by
    rw [hX ω, hYdef]
    simp only [Chart.chartTransport_apply', Chart.oneDist_apply]
    ring
  have hYm : Measurable Y := by
    have e : Y = fun ω => bwRelField κ b jumps spec h E ω + -((2 * Real.pi * χ') • Chart.oneDist) := by
      funext ω
      ext ψ
      rw [hYapp]
      simp only [add_apply, neg_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, Chart.oneDist_apply]
      ring
    rw [e]
    exact (WholeField.measurable_add_dist _).comp hXm
  set β : Ω → BoundaryWord := fun ω => vshift (bwRelWord κ θ c₀ (rec ω)) (-(2 * Real.pi * χ')) with hβdef
  have hsortR : ∀ ω, (bwRelWord κ θ c₀ (rec ω)).IsSorted := fun ω =>
    GW1Laws.isSorted_cfWordOf κ (isSorted_stopWord κ _)
  have hlaw : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ rec ⁻¹' TS →
      P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | MeasurableSpace.comap rec inferInstance] ω =
        gaussCF (β ω) ψ := by
    intro ψ
    have hfun : (fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ))) =
        Complex.exp (Complex.I * (((-(2 * Real.pi * χ')) * ∫ z, ψ z : ℝ) : ℂ)) •
          fun ω' => Complex.exp (Complex.I * (bwRelField κ b jumps spec h E ω' ψ : ℂ)) := by
      funext ω'
      rw [Pi.smul_apply, smul_eq_mul, ← Complex.exp_add, hYapp]
      congr 1
      push_cast
      ring
    have hsm := condExp_smul (μ := P) (Complex.exp (Complex.I * (((-(2 * Real.pi * χ')) * ∫ z, ψ z : ℝ) : ℂ)))
      (fun ω' => Complex.exp (Complex.I * (bwRelField κ b jumps spec h E ω' ψ : ℂ)))
      (MeasurableSpace.comap rec inferInstance)
    filter_upwards [hsm, ae_condExp_cexp_bwRelField hset hc₀J hc₀ hFTS ψ] with ω hsmω hlω hω
    rw [hfun, hsmω, Pi.smul_apply, smul_eq_mul, hlω hω, hβdef, gaussCF_vshift]
  -- the chart mean, test function by test function
  have hdomA : ∀ ω, rec ω ∈ TS → ((relChart (rec ω)).dom : Set ℂ) = H \ A ω := fun ω hω => by
    rw [coe_dom_relChart, hAdef]
    simp only [bRetOfRec_of_mem hω]
  have hmean := fun φ : TestOn upperHalfPlaneOpens =>
    Sec5.CrossCond.Staged.ae_apply_eq_chartMean_of_chartLaw (𝓗 := MeasurableSpace.comap rec inferInstance)
      (c := fun ω => relChart (rec ω)) hrec.comap_le (fun ω => isConformal_relChart _)
      (fun z => ⟨_, measurableSet_mem_dom_relChart z, rfl⟩)
      (fun z => (measurable_indicator_fwd_relChart z).comp (comap_measurable rec))
      (fun z ε => ⟨_, measurableSet_closedBall_subset_dom_relChart z ε, rfl⟩)
      (fun z => (measurable_indicator_lift_relChart z).comp (comap_measurable rec))
      (fun ω => continuousOn_lift_relChart _) hG' hu₁ hYm (χ := χ') (G := rec ⁻¹' TS) ⟨TS, hTS, rfl⟩
      (Eventually.of_forall fun ω _ => Chart.isChartTransport_chartTransport (isConformal_relChart (rec ω))
        (Chart.locallyIntegrableOn_of_continuousOn ((continuousOn_lift_relChart (rec ω)).comp
          (isConformal_relChart (rec ω)).1.continuousOn fun w hw => (isConformal_relChart (rec ω)).inv_mem_dom hw))
        1 0 χ' (h' ω))
      (β := β) hlaw hAm hlocA hmark
      (Eventually.of_forall fun ω hω => by
        rw [hdomA ω hω]
        simp only [Set.sdiff_self, isOpen_empty, and_true, subset_rfl])
      hg₁' φ
  -- almost surely, for every test function off the retained set
  set m : Ω → ℂ → ℝ := fun ω => chartMeanFn χ' (β ω) (rec ω) u₁ with hmdef
  have hsortβ : ∀ ω, (β ω).IsSorted := fun ω => isSorted_vshift (hsortR ω) _
  have hmharm : ∀ ω, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A ω) := fun ω => by
    by_cases hω : rec ω ∈ TS
    · rw [← hdomA ω hω]
      exact harmonicOnNhd_chartMeanFn χ' (hsortβ ω) (rec ω) hu₁.1
    · intro z hz
      exfalso
      have hAH : A ω = H := by simp only [hAdef, bRetOfRec_of_notMem hω]
      rw [hAH] at hz
      exact hz.2 hz.1
  have hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ H \ A ω →
      g₁ ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [hmean φ] with ω hω hsupp
    by_cases hr : rec ω ∈ TS
    · have hsD : tsupport φ ⊆ (relChart (rec ω)).dom := by
        rw [hdomA ω hr]
        exact hsupp
      rw [hω hr hsD]
      have hc1 : ContinuousOn (fun z => (β ω).mean ((relChart (rec ω)).1 z) - χ' * (relChart (rec ω)).2.2 z)
          (relChart (rec ω)).dom := by
        have hc2 := continuousOn_chartMeanFn χ' (hsortβ ω) (rec ω) hu₁.1
        have hu₁c : ContinuousOn u₁ (relChart (rec ω)).dom := fun z hz =>
          (hu₁.1 z (dom_relChart_subset_H _ hz)).1.continuousAt.continuousWithinAt
        refine (hc2.add hu₁c).congr fun z _ => ?_
        simp only [chartMeanFn, Pi.add_apply]
        ring
      have hi1 := WholeField.integrable_mul_testOn hc1 φ hsD
      have hi2 := WholeField.integrable_mul_testOn (fun z hz =>
        (hu₁.1 z hz).1.continuousAt.continuousWithinAt) φ φ.tsupport_subset
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hmdef, chartMeanFn]
      ring
    · have hAH : A ω = H := by simp only [hAdef, bRetOfRec_of_notMem hr]
      rw [hAH, Set.sdiff_self] at hsupp
      have h0 : ∀ z, φ z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => hsupp hz
      have hφ0 : φ = 0 := by
        ext z
        exact h0 z
      rw [hφ0, map_zero]
      have e : (fun z => m ω z * (0 : TestOn upperHalfPlaneOpens) z) = fun _ => 0 := by
        funext z
        rw [← hφ0, h0 z, mul_zero]
      rw [e, integral_zero]
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae hg₁.2.1
    (Eventually.of_forall fun ω => isOpen_H_diff_bRetOfRec TS _) (Eventually.of_forall hmharm) hφ
  -- the pointwise identity
  filter_upwards [hall] with ω hω hr G₀ hG₀ w₁ hw₁ hr₁
  have heq : EqOn w₁ (m ω) (H \ A ω) :=
    Sec6.eqOn_of_integral_mul_eq (isOpen_H_diff_bRetOfRec TS _) sdiff_subset hw₁ (hmharm ω) fun φ hφs => by
      rw [← hr₁ φ hφs, hω φ hφs]
  intro z hz
  have hzD : z ∈ (relChart (rec ω)).dom := by
    change z ∈ ((relChart (rec ω)).dom : Set ℂ)
    rw [hdomA ω hr]
    exact hz
  have hΨ := relMap_mem_H_of_mem_dom (rec ω) hzD
  have hG := eqOn_bhe_cfData_mean hk (hsortR ω) hG₀ hΨ
  show w₁ z + u₀ z = _
  rw [heq hz, hmdef]
  simp only [chartMeanFn, hβdef, mean_vshift, relChart_lift_eq (rec ω) hzD, hu₀₁ hz.1, hG]
  rw [relChart_fst]
  ring

end Mean

end InteractingSLE.Theorem14.BW1LMean
