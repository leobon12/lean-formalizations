/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CrK2
import InteractingSLE.Spec.Supplement.SB2DrvLineEarly
import InteractingSLE.Spec.Supplement.SB2MuShift
import InteractingSLE.Spec.Supplement.OrdLateSeed
import InteractingSLE.Spec.Supplement.Aux94

/-!
# The entrance law at the root: the law given the entrance σ-algebra (D85, (A2))

Worker PROVE-SB2-F3LAW (round 8, D85). NOJUMP's root versions `Cr.RootVersionS` condition on the entrance σ-algebra
`(S.ver 0).𝓗 0`, which contains the root event `Fr`. K2's (S) for them (`HasSafeLaw`, CONDFIN's
`Cr.hasSafeLaw_hasSafeMembers_of_rootLines`) holds at every relative time, in particular at relative time `0`: there the
continuation hull is empty and the coupling functional is the Gaussian functional of the word plus the angle's constant
(`bheProc_zero_eq_mean_of_sorted`). So, given the entrance σ-algebra, the canonical chart field is the GFF of the word
almost surely on `Fr`:

* **`ae_condExp_entrance`**: the characteristic functional given `(S.ver 0).𝓗 0` on `Fr`, from (S) on the type cells;
* `exists_inter_eq_of_measurableSet_sup`, **`ae_condExp_sup_singleton`**: the same functional given the marks and one
  event `F'` almost surely equal to `Fr` (CONDFIN's `Ca.entrMarks`), by set integrals;
* **`ae_isGFF_hullChart_unshift`**: the converse of LCMEAN's `Mu.ae_isGFF_hullChart_shift` (offset `x₀` back to `0`).

The proof uses no flow-line locality beyond K2's line facts at deterministic B-times; the head inside `fill (A₁ 0)` is
handled by K2's strict time change (the clock is `0` until the entrance).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fu

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv

/-- **On a type cell of a sorted word the time-`0` coupling data are the word mean plus `ψχ`**
(`Lv.bheProc_zero_eq_mean` for a word that is already sorted). -/
theorem bheProc_zero_eq_mean_of_sorted {Ω : Type*} {κ ψ : ℝ} (hκ : 0 < κ) {w : WordType} {c : BoundaryWord}
    (hc : c ∈ FCDet.typeSet κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w)) (hcs : c.IsSorted)
    {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    {xL : Ω → Fin w.1 → ℝ} {xR : Ω → Fin w.2.1 → ℝ} {ω : Ω}
    (hxL : xL ω = FCDet.typeXL κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c)
    (hxR : xR ω = FCDet.typeXR κ ψ w.1 w.2.1 (typedRhoL w) (typedRhoR w) c) :
    ∀ z ∈ H, bheProc κ (typedRhoL w) (typedRhoR w) W (geomLW W xL) (geomRW W xR) ω 0 z = c.mean z + ψ * chiC κ := by
  have hft := FCDet.isFlowType_of_mem_typeSet hc
  obtain ⟨hsL, hsR⟩ := Restart.RetAux79.isFlowType_signs hft
  have hL0 : ∀ i, geomLW W xL i 0 ω = xL ω i := fun i =>
    geomLW_zero hWc hW0 (by rw [hxL]; exact hsL i)
  have hR0 : ∀ j, geomRW W xR j 0 ω = xR ω j := fun j =>
    geomRW_zero hWc hW0 (by rw [hxR]; exact hsR j)
  have hu := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := typedRhoL w) (ρR := typedRhoR w) (W := W)
    (VL := geomLW W xL) (VR := geomRW W xR) ω 0
  simp only [hL0, hR0, hW0, sub_zero, hxL, hxR] at hu
  have hS : ({0} ∪ (c.jumps : Set ℝ)).Finite := (finite_singleton 0).union c.jumps.finite_toSet
  refine Restart.RetAux79.eqOn_mean_add_of_forceBoundaryData hu hcs (ψ * chiC κ) hS fun y hy => ?_
  have h0 : y ≠ 0 := fun h' => hy (Or.inl h')
  have hJ : y ∉ c.jumps := fun h' => hy (Or.inr h')
  rw [Restart.RetAux79.forceBoundaryData_zero_of_isFlowType hft y,
    Exist.forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 ψ h0 (by simpa using hJ), add_zero]

/-- **The law given the entrance σ-algebra** (K2's (S) at relative time `0`). For NOJUMP's root versions over the root
event `Fr`, with a sorted word `c` measurable for the time-`0` line marks, a countable set of word types covering `Fr`
with admissible seeds, and K2's (S) for the first version on every type cell: almost surely on `Fr`, the
characteristic functional of the chart field given the entrance σ-algebra `(S.ver 0).𝓗 0` is the word's. -/
theorem ae_condExp_entrance {κ ψ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {Fr : Set Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {c : Ω → BoundaryWord}
    {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    (S : Cr.RootVersionS κ ψ P Fr 𝓖 A₁ A₂ Φ c types pc tL L relLife)
    (hc : Measurable[Ms.lineFiltC P 𝓖 0] c) (hcs : ∀ ω, (c ω).IsSorted) (hΦ : ∀ ω, (Φ ω).IsConformal)
    (hHm : Measurable fun ω => Chart.chartTransport (hΦ ω) 1 0 (chiC κ) (h ω))
    (htypes : types.Countable) (hcover : ∀ᵐ ω ∂P, ω ∈ Fr → angleWordType κ ψ (c ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ c Fr w → ω ∈ seedCell κ ψ c Fr w)
    (hlaw : ∀ w ∈ types, HasSafeLaw κ (typedRhoL w) (typedRhoR w) P (S.ver 0).𝓗 (seedCell κ ψ c Fr w) (S.V 0)
      (S.ver 0).W (geomLW (S.ver 0).W (cellXL κ ψ c w)) (geomRW (S.ver 0).W (cellXR κ ψ c w))
      (fun ω => Chart.chartTransport (hΦ ω) 1 (ψ * chiC κ) (chiC κ) (h ω)))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ Fr →
      P[fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hΦ ω') 1 0 (chiC κ) (h ω') φ : ℂ)) |
        (S.ver 0).𝓗 0] ω = gaussCF (c ω) φ := by
  have hle : (S.ver 0).𝓗 0 ≤ mΩ := (S.ver 0).𝓗.le 0
  have hc0 : Measurable[(S.ver 0).𝓗 0] c := hc.mono (S.ver 0).marks_le le_rfl
  set Z : Ω → ℂ := fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hΦ ω') 1 0 (chiC κ) (h ω') φ : ℂ))
    with hZdef
  have hZi : Integrable Z P :=
    GFF.integrable_exp_I_mul (P := P) ((LQGMetric.measurable_distOn_apply φ).comp hHm)
  have hγm : StronglyMeasurable[(S.ver 0).𝓗 0] fun ω => gaussCF (c ω) φ :=
    ((Restart.measurable_gaussCF φ).comp hc0).stronglyMeasurable
  have hγi : Integrable (fun ω => gaussCF (c ω) φ) P :=
    Integrable.of_bound (hγm.mono hle).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => Restart.norm_gaussCF_le _ φ)
  set e : ℂ := Complex.exp (Complex.I * ((ψ * chiC κ * ∫ z, φ z : ℝ) : ℂ)) with he
  have hX : ∀ ω, Complex.exp (Complex.I * (Chart.chartTransport (hΦ ω) 1 (ψ * chiC κ) (chiC κ) (h ω) φ : ℂ)) =
      e * Z ω := fun ω => by
    have h1 := CondDriverBridge.isTranslateAddConst_chartTransport (hΦ ω) (ψ * chiC κ) (chiC κ) (h ω) φ φ
      (fun z => by rw [Complex.ofReal_zero, add_zero])
    rw [h1, he, hZdef, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcell : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ seedCell κ ψ c Fr w → P[Z | (S.ver 0).𝓗 0] ω = gaussCF (c ω) φ := by
    intro w hw
    have hcm : MeasurableSet[(S.ver 0).𝓗 0] (seedCell κ ψ c Fr w) := measurableSet_seedCell hc0 (S.ver 0).root_meas w
    refine Exist.StagedLaw.ae_condExp_eq_of_setIntegral_eq hle hcm hZi hγm hγi fun A hA => ?_
    have hD : MeasurableSet[(S.ver 0).𝓗 0] (A ∩ seedCell κ ψ c Fr w) := hA.inter hcm
    have hDm : MeasurableSet (A ∩ seedCell κ ψ c Fr w) := hle _ hD
    have hpos : ∀ᵐ ω ∂P, ω ∈ A ∩ seedCell κ ψ c Fr w →
        ω ∈ seedCell κ ψ c Fr w ∧ ω ∈ avoidSet (S.ver 0).W (S.V 0) φ 0 := by
      filter_upwards [S.ann 0] with ω hω hωD
      refine ⟨hωD.2, ?_, ?_⟩
      · have h1 := (hω (seedCell_subset w hωD.2)).1 0
        simpa using lt_of_le_of_lt zero_le h1
      · have hWc : Continuous fun s : ℝ => (S.ver 0).W s.toNNReal ω :=
          ((S.ver 0).W_cont ω).comp continuous_real_toNNReal
        rw [NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hWc]
        exact disjoint_empty _
    have h1 := (hlaw w hw) φ 0 _ hD hpos
    have hcf : ∀ ω ∈ A ∩ seedCell κ ψ c Fr w,
        Coupling.cfAt κ (S.ver 0).W (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver 0).W
          (geomLW (S.ver 0).W (cellXL κ ψ c w)) (geomRW (S.ver 0).W (cellXR κ ψ c w))) φ 1
          (fun _ => (0 : ℝ≥0)) ω = e * gaussCF (c ω) φ := by
      intro ω hω
      have hw0 : (fun s : ℝ => (S.ver 0).W s.toNNReal ω) 0 = 0 := by
        simp only [Real.toNNReal_zero, (S.ver 0).W_zero]
      have hbhe := bheProc_zero_eq_mean_of_sorted hκ (mem_typeSet_of_mem_wordTypeCell hω.2.1) (hcs ω)
        (S.ver 0).W_zero (S.ver 0).W_cont (xL := cellXL κ ψ c w) (xR := cellXR κ ψ c w) (ω := ω) rfl rfl
      have hint : (∫ z, couplingMean κ (fun s : ℝ => (S.ver 0).W s.toNNReal ω) 0
          (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver 0).W (geomLW (S.ver 0).W (cellXL κ ψ c w))
            (geomRW (S.ver 0).W (cellXR κ ψ c w)) ω 0) z * φ z) =
          ∫ z, ((c ω).mean z + ψ * chiC κ) * φ z := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        by_cases hz : φ z = 0
        · simp only [hz, mul_zero]
        · have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ hz)
          have hz0 : z ≠ 0 := fun h' => by
            rw [h'] at hzH
            exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
          change couplingMean κ (fun s : ℝ => (S.ver 0).W s.toNNReal ω) 0 _ z * φ z = _
          rw [Coupling.MartMeans2.couplingMean_zero κ hw0 _ hz0, hbhe z hzH]
      have hI1 : Integrable fun z => (c ω).mean z * φ z :=
        Coupling.MartMeans2.integrable_mul_test_of_continuousOn (RLC.continuousOn_mean_H (hcs ω)) φ
          φ.tsupport_subset
      have hI0 : Integrable fun z => φ z := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
      have hsplit : (∫ z, ((c ω).mean z + ψ * chiC κ) * φ z) =
          (∫ z, (c ω).mean z * φ z) + ψ * chiC κ * ∫ z, φ z := by
        rw [← integral_const_mul, ← integral_add hI1 (hI0.const_mul _)]
        congr 1
        funext z
        ring
      have henergy : loewnerGreenEnergy (fun s : ℝ => (S.ver 0).W s.toNNReal ω) 0 φ =
          QuantumZipper.zeroGFFTestCov upperHalfPlaneOpens φ φ := by
        rw [Coupling.MartMeans2.loewnerGreenEnergy_zero_eq hw0, Sec7.Lemma71J.loewnerGreenEnergy_const_zero]
      simp only [Coupling.cfAt, gaussCF, he, NNReal.coe_zero]
      rw [hint, hsplit, henergy, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [setIntegral_congr_fun hDm (fun ω _ => hX ω), setIntegral_congr_fun hDm hcf, integral_const_mul,
      integral_const_mul] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  filter_upwards [(ae_ball_iff htypes).2 hcell, hcover, (ae_ball_iff htypes).2 hseed] with ω hcode hcov hsd hFr
  exact hcode _ (hcov hFr) (hsd _ (hcov hFr) ⟨hFr, rfl⟩)

/-- Every event of `𝓜 ⊔ σ(F)` agrees on `F` with an event of `𝓜`. -/
theorem exists_inter_eq_of_measurableSet_sup {Ω : Type*} {𝓜 : MeasurableSpace Ω} {F A : Set Ω}
    (hA : MeasurableSet[𝓜 ⊔ MeasurableSpace.generateFrom {F}] A) :
    ∃ M, MeasurableSet[𝓜] M ∧ A ∩ F = M ∩ F := by
  let 𝒞 : MeasurableSpace Ω :=
    { MeasurableSet' := fun A => ∃ M, MeasurableSet[𝓜] M ∧ A ∩ F = M ∩ F
      measurableSet_empty := ⟨∅, MeasurableSet.empty, by rw [empty_inter]⟩
      measurableSet_compl := fun A ⟨M, hM, e⟩ => ⟨Mᶜ, hM.compl, by
        ext x
        have hx := Set.ext_iff.1 e x
        simp only [mem_inter_iff, mem_compl_iff] at hx ⊢
        tauto⟩
      measurableSet_iUnion := fun f hf => by
        choose M hM e using hf
        exact ⟨⋃ i, M i, MeasurableSet.iUnion hM, by simp only [iUnion_inter, e]⟩ }
  have h1 : 𝓜 ≤ 𝒞 := fun A hA => ⟨A, hA, rfl⟩
  have h2 : MeasurableSpace.generateFrom {F} ≤ 𝒞 := MeasurableSpace.generateFrom_le fun t ht =>
    ⟨univ, MeasurableSet.univ, by rw [mem_singleton_iff.1 ht, univ_inter, inter_self]⟩
  exact sup_le h1 h2 A hA

/-- **A conditional expectation identified on `Fr` passes to the marks and one event `F' = Fr` a.s.**: if `𝓜 ≤ 𝓚`,
`Fr ∈ 𝓚`, `P[Z | 𝓚] = γ` almost surely on `Fr` with `γ` measurable for `𝓜`, and `F'` is measurable and almost surely
equal to `Fr`, then `P[Z | 𝓜 ⊔ σ(F')] = γ` almost surely on `F'`. -/
theorem ae_condExp_sup_singleton {Ω : Type*} {𝓜 𝓚 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓚 : 𝓚 ≤ mΩ) (h𝓜𝓚 : 𝓜 ≤ 𝓚) {Fr F' : Set Ω} (hFr : MeasurableSet[𝓚] Fr)
    (hF' : MeasurableSet F') (hFF : ∀ᵐ ω ∂P, ω ∈ F' ↔ ω ∈ Fr) {Z γ : Ω → ℂ} (hZ : Integrable Z P)
    (hγ : StronglyMeasurable[𝓜] γ) (hγi : Integrable γ P) (hK : ∀ᵐ ω ∂P, ω ∈ Fr → P[Z | 𝓚] ω = γ ω) :
    ∀ᵐ ω ∂P, ω ∈ F' → P[Z | 𝓜 ⊔ MeasurableSpace.generateFrom {F'}] ω = γ ω := by
  have h𝒢 : 𝓜 ⊔ MeasurableSpace.generateFrom {F'} ≤ mΩ :=
    sup_le (h𝓜𝓚.trans h𝓚) (MeasurableSpace.generateFrom_le fun t ht => by rw [mem_singleton_iff.1 ht]; exact hF')
  have hF'𝒢 : MeasurableSet[𝓜 ⊔ MeasurableSpace.generateFrom {F'}] F' :=
    le_sup_right (a := 𝓜) _ (MeasurableSpace.measurableSet_generateFrom (mem_singleton F'))
  refine Exist.StagedLaw.ae_condExp_eq_of_setIntegral_eq h𝒢 hF'𝒢 hZ (hγ.mono le_sup_left) hγi fun A hA => ?_
  obtain ⟨M, hM, e⟩ := exists_inter_eq_of_measurableSet_sup hA
  have hset : (M ∩ F' : Set Ω) =ᵐ[P] (M ∩ Fr : Set Ω) := by
    filter_upwards [hFF] with ω hω
    exact propext (and_congr_right fun _ => hω)
  have hMFr : MeasurableSet[𝓚] (M ∩ Fr) := (h𝓜𝓚 _ hM).inter hFr
  rw [e, setIntegral_congr_set hset, setIntegral_congr_set hset, ← setIntegral_condExp h𝓚 hZ hMFr]
  refine setIntegral_congr_ae (h𝓚 _ hMFr) ?_
  filter_upwards [hK] with ω hω hωM using hω hωM.2

/-- **The retained law read back in the offset-`0` chart** (the converse of `Mu.ae_isGFF_hullChart_shift`): if the
field read in the hull chart of `fill K` with a `𝒢`-measurable offset `x₀` is conditionally a GFF with the data of
`shiftW x₀ β`, the field read in the offset-`0` chart is conditionally a GFF with the data of `β`. -/
theorem ae_isGFF_hullChart_unshift {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {G : Set Ω}
    {K : Ω → Set ℂ} (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    {x₀ : Ω → ℝ} (hx₀ : Measurable[𝒢] x₀) {κ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    {β : Ω → BoundaryWord} (hYm : Measurable fun ω =>
      Chart.chartTransport (Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω) 1 0 (chiC κ) (h ω))
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).jumps) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → IsGFFWithBoundaryData (condExpKernel P 𝒢 ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω) 1 0 (chiC κ) (h ω))
      (β ω₀).fn (β ω₀).jumps := by
  have hA : ∀ ω, IsHPHull (fillH (K ω)) := Mo.isHPHull_fillH hKc hKp
  filter_upwards [hlaw, Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝒢 hx₀] with ω₀ hl hxeq hG
  have hg := hl hG
  have hrec := Supp9.IsGFFWithBoundaryData.recenter
    (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).isPiecewiseConstantBoundaryData (-x₀ ω₀) hg
  have hw := RLC.OrdLate.shiftW_neg_shiftW (x₀ ω₀) (β ω₀)
  rw [← hw, BoundaryWord.jumps_shiftW,
    show (BoundaryWord.shiftW (-x₀ ω₀) (BoundaryWord.shiftW (x₀ ω₀) (β ω₀))).fn =
      fun y => (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).fn (y + -x₀ ω₀) from funext (BoundaryWord.fn_shiftW _ _)]
  refine isGFFWithBoundaryData_congr_ae hrec hYm ?_
  filter_upwards [hxeq] with ω hω
  have hc0 := Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω
  have e := RLC.OrdDet.chartTransport_recenter_eq_flowField hc0 (Mu.continuousOn_lift_inv_hullChart (hA ω) 0)
    (x₀ ω) 1 0 (chiC κ) (h ω)
  have hch : Mo.hullChart (fillH (K ω)) (x₀ ω) = (Mo.hullChart (fillH (K ω)) 0).recenter (x₀ ω) :=
    Mu.hullChart_eq_recenter _ _
  have hHc : Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) =
      Exist.flowField (x₀ ω) 0 (Chart.chartTransport hc0 1 0 (chiC κ) (h ω)) := by
    rw [← e]
    congr 1
  show Exist.flowField (-x₀ ω₀) 0 (Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)) =
    Chart.chartTransport hc0 1 0 (chiC κ) (h ω)
  rw [hHc, hω, RLC.OrdLate.flowField_neg_flowField]

end InteractingSLE.Theorem14.SB.Fu
