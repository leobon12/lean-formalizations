/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCDetDriver
import InteractingSLE.Spec.Restart.FlowCodeWord
import InteractingSLE.Spec.Restart.ChartSpace

/-!
# (Det) for drivers on any probability space: K2 on a canonical standard Borel space

Packet PROVE-FCDET. K2 (`ConverseBefore.ae_isOptionalHullCoupling_k_prod`) uses `condExpKernel`, so it needs a standard
Borel space in `Type`, while the (Det) consumers (`FirstContactCanonCondDetStatement.{u}`, …) quantify over every
probability space in a universe `u`. The consumer's data are pushed forward, under the conditional law on the live
event, to the canonical space

  `CanonSpace = BoundaryWord × 𝒟'(ℍ) × PCode` (word, chart field, dyadic code of the driver),

a standard Borel space in `Type` with its natural filtration (`CanonSpace.filt`: the word at time `0`, the driver up
to time `q`). K2's inputs (S), (L) are integral identities over events of that filtration; their preimages are events
of the consumer's filtration, so they transfer by change of variables (`setIntegral_map_cond`; the `cfAt` side through
its measurable safe-set indicator). `FCDet.ae_driverCodeMatch_of_hasSafeLaw` runs on the canonical space, and the
driver match is a Borel condition, so it pulls back. No pathwise property of a trace is transferred.

## Main results

* `decDrv`: the continuous driver decoded from a dyadic code; `decDrv_enc`;
* `typeSet`, `typeXL`, `typeXR`: the words of a fixed flow-line type and their positions (Borel, via
  `Restart.flowPad`); `isFlowType_of_mem_typeSet`, `isOrderedForceWord_typeXL`;
* `geomLW_congr`, `geomRW_congr`, `thr_congr`, `bheProc_congr`, `cfAt_congr`: the continuation read at another point;
* `CanonSpace`, `CanonSpace.filt`; `ae_imp_of_ae_cond`, `ae_cond_of_ae_imp`, `setIntegral_map_cond`,
  `measurableSet_thresholdCondition_zero`;
* **`ae_driverCodeMatch_of_hasSafeLaw_on`**: on any probability space (any universe), (S), (L), a word of fixed
  flow-line type on the live event `M`, an admissible seed and integrable pairings give, almost surely on `M`, the
  canonical driver code match of the driver with the threshold as lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FCDet

open Sec2.Assembly

/-! ### The decoded driver -/

open scoped Classical in
/-- **The driver decoded from a dyadic code**: the continuous extension of the code recentred at `0` when the code
is uniformly continuous on every bounded dyadic set, `0` otherwise. Continuous and `0` at `0` for every code. -/
def decDrv (p : PCode) (t : ℝ≥0) : ℝ := if ∀ N : ℕ, UC p N then dec p t - dec p 0 else 0

theorem continuous_decDrv (p : PCode) : Continuous (decDrv p) := by
  classical
  by_cases hp : ∀ N : ℕ, UC p N
  · have e : decDrv p = fun t => dec p t - dec p 0 :=
      funext fun t => by simp only [decDrv, hp, implies_true, ↓reduceIte]
    rw [e]
    exact (Exist.continuous_dec_of_UC hp).sub continuous_const
  · have e : decDrv p = fun _ => 0 := funext fun t => by simp only [decDrv, hp, ↓reduceIte]
    rw [e]
    exact continuous_const

theorem decDrv_zero (p : PCode) : decDrv p 0 = 0 := by
  classical
  unfold decDrv
  split_ifs <;> simp

theorem measurable_decDrv (t : ℝ≥0) : Measurable fun p : PCode => decDrv p t := by
  classical
  have hS : MeasurableSet {p : PCode | ∀ N : ℕ, UC p N} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun N => measurableSet_UC N
  exact Measurable.ite hS ((measurable_dec_at measurable_id t).sub (measurable_dec_at measurable_id 0))
    measurable_const

theorem decDrv_enc {W : ℝ≥0 → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) : decDrv (enc W) = W := by
  classical
  funext t
  simp only [decDrv, Sec2.Assembly2.uc_enc_of_continuous hW, implies_true, ↓reduceIte,
    Sec2.Assembly2.dec_enc_of_continuous hW, hW0, sub_zero]

/-! ### The flow-line type of a word -/

/-- The number of left marks of the flow-line word from `0` is measurable in the word. -/
theorem measurable_flowLineNL_zero : Measurable fun c : BoundaryWord => flowLineNL c.fn c.jumps 0 := by
  have hc0 : Measurable fun c : BoundaryWord => (c, (0 : ℝ)) := measurable_id.prodMk measurable_const
  have h := Measurable.comp (g := fun a : BoundaryWord × ℝ => flowLineNL a.1.fn a.1.jumps a.2)
    measurable_flowLineNL hc0
  exact h

/-- The number of right marks of the flow-line word from `0` is measurable in the word. -/
theorem measurable_flowLineNR_zero : Measurable fun c : BoundaryWord => flowLineNR c.fn c.jumps 0 := by
  have hc0 : Measurable fun c : BoundaryWord => (c, (0 : ℝ)) := measurable_id.prodMk measurable_const
  have h := Measurable.comp (g := fun a : BoundaryWord × ℝ => flowLineNR a.1.fn a.1.jumps a.2)
    measurable_flowLineNR hc0
  exact h

section FlowType

variable (κ θ : ℝ) (nL nR : ℕ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)

/-- **The words of a given flow-line type**: the angle-`θ` flow-line word from `0` has `nL` left and `nR` right marks
with weights `ρL`, `ρR`. -/
def typeSet : Set BoundaryWord :=
  (fun c : BoundaryWord => flowLineNL c.fn c.jumps 0) ⁻¹' {nL} ∩
    ((fun c : BoundaryWord => flowLineNR c.fn c.jumps 0) ⁻¹' {nR} ∩
      ({c | ∀ i : Fin nL, (flowPad κ θ (c, 0)).2.1 i = ρL i} ∩ {c | ∀ j : Fin nR, (flowPad κ θ (c, 0)).2.2 j = ρR j}))

open scoped Classical in
/-- The left mark positions of a word of the type (`0` off the type). -/
def typeXL (c : BoundaryWord) : Fin nL → ℝ :=
  if c ∈ typeSet κ θ nL nR ρL ρR then fun i => (flowPad κ θ (c, 0)).1.1 i else 0

open scoped Classical in
/-- The right mark positions of a word of the type (`0` off the type). -/
def typeXR (c : BoundaryWord) : Fin nR → ℝ :=
  if c ∈ typeSet κ θ nL nR ρL ρR then fun j => (flowPad κ θ (c, 0)).1.2 j else 0

theorem measurableSet_typeSet : MeasurableSet (typeSet κ θ nL nR ρL ρR) := by
  have hc0 : Measurable fun c : BoundaryWord => (c, (0 : ℝ)) := measurable_id.prodMk measurable_const
  have hP := (measurable_flowPad κ θ).comp hc0
  have hL : ∀ i : Fin nL, Measurable fun c : BoundaryWord => (flowPad κ θ (c, 0)).2.1 i := fun i =>
    (measurable_pi_apply _).comp (measurable_fst.comp (measurable_snd.comp hP))
  have hR : ∀ j : Fin nR, Measurable fun c : BoundaryWord => (flowPad κ θ (c, 0)).2.2 j := fun j =>
    (measurable_pi_apply _).comp (measurable_snd.comp (measurable_snd.comp hP))
  have h3 : MeasurableSet {c : BoundaryWord | ∀ i : Fin nL, (flowPad κ θ (c, 0)).2.1 i = ρL i} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_eq_fun (hL i) measurable_const
  have h4 : MeasurableSet {c : BoundaryWord | ∀ j : Fin nR, (flowPad κ θ (c, 0)).2.2 j = ρR j} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter fun j => measurableSet_eq_fun (hR j) measurable_const
  exact (measurable_flowLineNL_zero (measurableSet_singleton nL)).inter
    ((measurable_flowLineNR_zero (measurableSet_singleton nR)).inter (h3.inter h4))

theorem measurable_typeXL : Measurable (typeXL κ θ nL nR ρL ρR) := by
  classical
  have hc0 : Measurable fun c : BoundaryWord => (c, (0 : ℝ)) := measurable_id.prodMk measurable_const
  have hP := (measurable_flowPad κ θ).comp hc0
  refine Measurable.ite (measurableSet_typeSet κ θ nL nR ρL ρR) (measurable_pi_iff.2 fun i => ?_) measurable_const
  exact (measurable_pi_apply _).comp (measurable_fst.comp (measurable_fst.comp hP))

theorem measurable_typeXR : Measurable (typeXR κ θ nL nR ρL ρR) := by
  classical
  have hc0 : Measurable fun c : BoundaryWord => (c, (0 : ℝ)) := measurable_id.prodMk measurable_const
  have hP := (measurable_flowPad κ θ).comp hc0
  refine Measurable.ite (measurableSet_typeSet κ θ nL nR ρL ρR) (measurable_pi_iff.2 fun j => ?_) measurable_const
  exact (measurable_pi_apply _).comp (measurable_snd.comp (measurable_fst.comp hP))

variable {κ θ nL nR ρL ρR}

/-- **A word of the type has the flow-line type with the type's positions.** -/
theorem isFlowType_of_mem_typeSet {c : BoundaryWord} (hc : c ∈ typeSet κ θ nL nR ρL ρR) :
    IsFlowType κ θ c (typeXL κ θ nL nR ρL ρR c) (typeXR κ θ nL nR ρL ρR c) ρL ρR := by
  classical
  have hc' := hc
  obtain ⟨eL, eR, hρL, hρR⟩ := hc'
  simp only [mem_preimage, mem_singleton_iff] at eL eR
  refine ⟨eL, eR, ?_, ?_, ?_, ?_⟩
  · funext i
    simp only [typeXL, hc, ↓reduceIte, flowPad, Fin.val_cast, i.2, ↓reduceDIte]
  · funext j
    simp only [typeXR, hc, ↓reduceIte, flowPad, Fin.val_cast, j.2, ↓reduceDIte]
  · funext i
    rw [← hρL (Fin.cast eL i)]
    simp only [flowPad, Fin.val_cast, i.2, ↓reduceDIte]
  · funext j
    rw [← hρR (Fin.cast eR j)]
    simp only [flowPad, Fin.val_cast, j.2, ↓reduceDIte]

/-- The positions of a word of the type are an ordered force word (the flow-line word's order; `0` off the type). -/
theorem isOrderedForceWord_typeXL (c : BoundaryWord) :
    IsOrderedForceWord (typeXL κ θ nL nR ρL ρR c) (typeXR κ θ nL nR ρL ρR c) := by
  classical
  by_cases hc : c ∈ typeSet κ θ nL nR ρL ρR
  · obtain ⟨eL, eR, hxL, hxR, -, -⟩ := isFlowType_of_mem_typeSet hc
    have hO := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
    have hL : typeXL κ θ nL nR ρL ρR c = fun i => flowLineXL c.fn c.jumps 0 (Fin.cast eL.symm i) := by
      funext i
      rw [← hxL]
      rfl
    have hR : typeXR κ θ nL nR ρL ρR c = fun j => flowLineXR c.fn c.jumps 0 (Fin.cast eR.symm j) := by
      funext j
      rw [← hxR]
      rfl
    rw [hL, hR]
    exact ⟨fun i i' h => hO.1 (Fin.le_def.2 (by simpa using Fin.le_def.1 h)), fun i => hO.2.1 _,
      fun j j' h => hO.2.2.1 (Fin.le_def.2 (by simpa using Fin.le_def.1 h)), fun j => hO.2.2.2 _⟩
  · have hL : typeXL κ θ nL nR ρL ρR c = 0 := by simp [typeXL, hc]
    have hR : typeXR κ θ nL nR ρL ρR c = 0 := by simp [typeXR, hc]
    rw [hL, hR]
    exact ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

end FlowType

/-! ### Reading the continuation at another point -/

section Congr

open Sec7.PocketTraversal DomainMarkov Coupling

variable {Ω Ω' : Type*} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {W' : ℝ≥0 → Ω' → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {xL' : Ω' → Fin nL → ℝ}
  {xR' : Ω' → Fin nR → ℝ} {ω : Ω} {ω' : Ω'}

theorem geomLW_congr (hW : ∀ t, W' t ω' = W t ω) (hx : xL' ω' = xL ω) (i : Fin nL) (t : ℝ≥0) :
    geomLW W' xL' i t ω' = geomLW W xL i t ω := by
  have hR : Bessel.realPath (fun t ω => -W' t ω) ω' = Bessel.realPath (fun t ω => -W t ω) ω := by
    funext r
    simp only [Bessel.realPath, hW]
  simp only [geomLW, hR, hx]

theorem geomRW_congr (hW : ∀ t, W' t ω' = W t ω) (hx : xR' ω' = xR ω) (j : Fin nR) (t : ℝ≥0) :
    geomRW W' xR' j t ω' = geomRW W xR j t ω := by
  have hR : Bessel.realPath W' ω' = Bessel.realPath W ω := by
    funext r
    simp only [Bessel.realPath, hW]
  simp only [geomRW, hR, hx]

theorem thr_congr (hW : ∀ t, W' t ω' = W t ω) (hxL : xL' ω' = xL ω) (hxR : xR' ω' = xR ω) :
    thr ρL ρR W' xL' xR' ω' = thr ρL ρR W xL xR ω := by
  simp only [thr, hW, geomLW_congr hW hxL, geomRW_congr hW hxR]

theorem bheProc_congr (hW : ∀ t, W' t ω' = W t ω) (hxL : xL' ω' = xL ω) (hxR : xR' ω' = xR ω) (κ : ℝ)
    (s : ℝ≥0) : bheProc κ ρL ρR W' (geomLW W' xL') (geomRW W' xR') ω' s =
      bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω s := by
  simp only [bheProc, hW, geomLW_congr hW hxL, geomRW_congr hW hxR]

theorem cfAt_congr (hW : ∀ t, W' t ω' = W t ω) (hxL : xL' ω' = xL ω) (hxR : xR' ω' = xR ω) (κ : ℝ)
    (ψ : ℂ → ℝ) (q : ℝ≥0) :
    cfAt κ W' (bheProc κ ρL ρR W' (geomLW W' xL') (geomRW W' xR')) ψ 1 (fun _ => q) ω' =
      cfAt κ W (bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR)) ψ 1 (fun _ => q) ω := by
  simp only [cfAt, hW, bheProc_congr hW hxL hxR]

end Congr

/-! ### The canonical space of a continuation -/

/-- **The canonical space of a continuation**: a boundary word, a field and the dyadic code of a driver. A standard
Borel space in `Type`. -/
abbrev CanonSpace : Type := BoundaryWord × DistOn upperHalfPlaneOpens × PCode

instance : StandardBorelSpace (DistOn upperHalfPlaneOpens × PCode) := StandardBorelSpace.prod

instance : StandardBorelSpace CanonSpace := StandardBorelSpace.prod

namespace CanonSpace

/-- The word coordinate. -/
def word (s : CanonSpace) : BoundaryWord := s.1

/-- The field coordinate. -/
def field (s : CanonSpace) : DistOn upperHalfPlaneOpens := s.2.1

/-- The decoded driver. -/
def drv (t : ℝ≥0) (s : CanonSpace) : ℝ := decDrv s.2.2 t

theorem measurable_word : Measurable word := measurable_fst

theorem measurable_field : Measurable field := measurable_fst.comp measurable_snd

theorem measurable_drv (t : ℝ≥0) : Measurable (drv t) := (measurable_decDrv t).comp (measurable_snd.comp measurable_snd)

/-- **The canonical filtration**: the word at time `0` and the driver up to time `q`. -/
def filt : Filtration ℝ≥0 (inferInstance : MeasurableSpace CanonSpace) where
  seq q := MeasurableSpace.comap word inferInstance ⊔
    ⨆ r : ℝ≥0, ⨆ (_ : r ≤ q), MeasurableSpace.comap (drv r) inferInstance
  mono' q q' hqq' := by
    refine sup_le_sup_left ?_ _
    refine iSup₂_le fun r hr => ?_
    exact le_iSup₂_of_le (f := fun r (_ : r ≤ q') => MeasurableSpace.comap (drv r) (inferInstance : MeasurableSpace ℝ))
      r (hr.trans hqq') le_rfl
  le' q := by
    refine sup_le measurable_word.comap_le (iSup₂_le fun r _ => ?_)
    exact (measurable_drv r).comap_le

theorem comap_word_le_filt (q : ℝ≥0) : MeasurableSpace.comap word inferInstance ≤ filt q := le_sup_left

theorem comap_drv_le_filt {r q : ℝ≥0} (hr : r ≤ q) :
    MeasurableSpace.comap (drv r) (inferInstance : MeasurableSpace ℝ) ≤ filt q :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun r (_ : r ≤ q) =>
    MeasurableSpace.comap (drv r) (inferInstance : MeasurableSpace ℝ)) r hr le_rfl)

theorem stronglyAdapted_drv : StronglyAdapted filt drv := fun _ =>
  (Measurable.of_comap_le (comap_drv_le_filt le_rfl)).stronglyMeasurable

end CanonSpace

/-! ### Transfer to the canonical space -/

section Transfer

open DomainMarkov DomainMarkov.K2 Coupling Sec7.PocketTraversal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {M : Set Ω}

omit mΩ in
/-- The geometric coordinates of a continuous driver from `0` have the weak path properties. -/
theorem isWeakPath_geom {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    IsWeakPath (W · ω) (fun i t => geomLW W xL i t ω) (fun j t => geomRW W xR j t ω) (ζ ω) :=
  ⟨hW0 ω, (hWc ω).continuousOn, fun i => (isForcePath_geomLW hWc xL ω i).1.continuousOn,
    fun j => (isForcePath_geomRW hWc xR ω j).1.continuousOn, fun t _ i => geomLW_le hWc xL ω t i,
    fun t _ j => le_geomRW hWc xR ω t j⟩

/-- Almost sure statements under the conditional law on `M` hold almost surely on `M`. -/
theorem ae_imp_of_ae_cond [IsFiniteMeasure P] (hM : MeasurableSet M) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂(P[|M]), p ω) : ∀ᵐ ω ∂P, ω ∈ M → p ω := by
  by_cases hPM : P M = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPM] with ω h1 h2 using absurd h2 h1
  rw [ProbabilityTheory.cond, Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.2 (measure_ne_top P M)),
    ae_restrict_iff' hM] at h
  exact h

/-- Almost sure statements on `M` hold almost surely under the conditional law on `M`. -/
theorem ae_cond_of_ae_imp (hM : MeasurableSet M) {p : Ω → Prop} (h : ∀ᵐ ω ∂P, ω ∈ M → p ω) :
    ∀ᵐ ω ∂(P[|M]), p ω := by
  filter_upwards [ProbabilityTheory.cond_absolutelyContinuous.ae_le h, ProbabilityTheory.ae_cond_mem hM]
    with ω h1 h2 using h1 h2

/-- **Integrals over canonical events**: for a measurable event `D'` of the canonical space and an a.e. strongly
measurable integrand, the integral under the law of `Y` given `M` is the normalized integral over `M ∩ Y⁻¹ D'`. -/
theorem setIntegral_map_cond [IsFiniteMeasure P] (hM : MeasurableSet M) {S : Type*} [MeasurableSpace S] {Y : Ω → S}
    (hY : Measurable Y) {D' : Set S} (hD' : MeasurableSet D') {f : S → ℂ}
    (hf : AEStronglyMeasurable f ((P[|M]).map Y)) :
    ∫ s in D', f s ∂((P[|M]).map Y) = (P M)⁻¹.toReal • ∫ ω in M ∩ Y ⁻¹' D', f (Y ω) ∂P := by
  rw [setIntegral_map hD' hf hY.aemeasurable]
  have hset : (Y ⁻¹' D' : Set Ω) =ᵐ[P[|M]] (M ∩ Y ⁻¹' D' : Set Ω) := by
    filter_upwards [ProbabilityTheory.ae_cond_mem hM] with ω hω
    simp only [mem_inter_iff, hω, true_and]
  rw [setIntegral_congr_set hset]
  exact setIntegral_cond_of_subset' (hM.inter (hY hD')) inter_subset_left _

end Transfer

/-- The threshold condition at the driver value `0` is a Borel condition on the marks. -/
theorem measurableSet_thresholdCondition_zero {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    MeasurableSet {p : (Fin nL → ℝ) × (Fin nR → ℝ) | ForceWord.ThresholdCondition ρL ρR 0 p.1 p.2} := by
  classical
  have hL : Measurable fun p : (Fin nL → ℝ) × (Fin nR → ℝ) =>
      ∑ i ∈ Finset.univ.filter (fun i => p.1 i = 0), ρL i := by
    simp_rw [Finset.sum_filter]
    exact Finset.measurable_sum _ fun i _ => Measurable.ite
      (measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_fst) measurable_const) measurable_const
      measurable_const
  have hR : Measurable fun p : (Fin nL → ℝ) × (Fin nR → ℝ) =>
      ∑ j ∈ Finset.univ.filter (fun j => p.2 j = 0), ρR j := by
    simp_rw [Finset.sum_filter]
    exact Finset.measurable_sum _ fun j _ => Measurable.ite
      (measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_snd) measurable_const) measurable_const
      measurable_const
  exact (measurableSet_le hL measurable_const).union (measurableSet_le hR measurable_const)

/-! ### (Det) for drivers on any probability space -/

section Main

open DomainMarkov DomainMarkov.K2 Coupling Sec7.PocketTraversal

universe u

/-- **(Det) for drivers on any probability space, in any universe** (K2 on the canonical space). Let `M` be an
initial event of a filtration `𝓗` on which a continuation is observed: an initial word `c` of a fixed flow-line type
on `M`, a globally continuous adapted driver `W` from `0`, the chart field `Hc` (`X = Hc + θχ` with integrable pairings
on `M`), an admissible seed on `M`, and K2's inputs (S) and (L) on `M` up to the threshold of the geometric images of
the type's positions. Then almost surely on `M` the driver, with the threshold as lifetime, matches the canonical
driver code of `(c, Hc)`. The proof pushes `(c, Hc, W)` forward to the standard Borel space `CanonSpace` under the
conditional law on `M`, transfers (S) and (L) to its natural filtration, applies `ae_driverCodeMatch_of_hasSafeLaw`
there, and pulls the (Borel) driver match back. -/
theorem ae_driverCodeMatch_of_hasSafeLaw_on {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {κ θ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓗 : Filtration ℝ≥0 mΩ} {M : Set Ω} (hM : MeasurableSet[𝓗 0] M) {c : Ω → BoundaryWord}
    (hc : Measurable[𝓗 0] c) (hMT : ∀ ω ∈ M, c ω ∈ typeSet κ θ nL nR ρL ρR) {W : ℝ≥0 → Ω → ℝ}
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗 W)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc)
    (hint : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω) φ) (P.restrict M))
    (hseed : ∀ᵐ ω ∂P, ω ∈ M → ¬ ForceWord.ThresholdCondition ρL ρR 0 (typeXL κ θ nL nR ρL ρR (c ω))
      (typeXR κ θ nL nR ρL ρR (c ω)))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 M
      (thr ρL ρR W (fun ω => typeXL κ θ nL nR ρL ρR (c ω)) (fun ω => typeXR κ θ nL nR ρL ρR (c ω))) W
      (geomLW W fun ω => typeXL κ θ nL nR ρL ρR (c ω)) (geomRW W fun ω => typeXR κ θ nL nR ρL ρR (c ω))
      fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω))
    (hmem : HasSafeMembers P 𝓗 M
      (thr ρL ρR W (fun ω => typeXL κ θ nL nR ρL ρR (c ω)) (fun ω => typeXR κ θ nL nR ρL ρR (c ω))) W
      fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω))
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F) :
    ∀ᵐ ω ∂P, ω ∈ M → IsDriverCodeMatch (F (c ω, Hc ω)) (fun t => W t ω)
      (thr ρL ρR W (fun ω => typeXL κ θ nL nR ρL ρR (c ω)) (fun ω => typeXR κ θ nL nR ρL ρR (c ω)) ω) := by
  classical
  set xLc : Ω → Fin nL → ℝ := fun ω => typeXL κ θ nL nR ρL ρR (c ω) with hxLc
  set xRc : Ω → Fin nR → ℝ := fun ω => typeXR κ θ nL nR ρL ρR (c ω) with hxRc
  set Xc : Ω → DistOn upperHalfPlaneOpens := fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (Hc ω)
    with hXc
  have hMm : MeasurableSet M := 𝓗.le 0 _ hM
  by_cases hPM : P M = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPM] with ω h1 h2 using absurd h2 h1
  have : IsProbabilityMeasure (P[|M]) := ProbabilityTheory.cond_isProbabilityMeasure hPM
  have hcm : Measurable c := hc.mono (𝓗.le 0) le_rfl
  have hWm : ∀ t, Measurable (W t) := fun t => (hWa t).measurable.mono (𝓗.le t) le_rfl
  set Y : Ω → CanonSpace := fun ω => (c ω, Hc ω, enc fun t => W t ω) with hYdef
  have hY : Measurable Y :=
    hcm.prodMk (hHc.prodMk (Sec2.Assembly2.measurable_enc.comp (measurable_pi_iff.2 hWm)))
  set Q : Measure CanonSpace := (P[|M]).map Y with hQ
  have : IsProbabilityMeasure Q := inferInstance
  -- the canonical coordinates read at `Y ω`
  have hWY : ∀ ω t, CanonSpace.drv t (Y ω) = W t ω := fun ω t => by
    simp only [CanonSpace.drv, hYdef, decDrv_enc (hWc ω) (hW0 ω)]
  set xL' : CanonSpace → Fin nL → ℝ := fun s => typeXL κ θ nL nR ρL ρR s.word with hxL'
  set xR' : CanonSpace → Fin nR → ℝ := fun s => typeXR κ θ nL nR ρL ρR s.word with hxR'
  set X' : CanonSpace → DistOn upperHalfPlaneOpens := fun s =>
    Exist.flowField 0 (θ * QuantumZipper.chiC κ) s.field with hX'
  have hthrY : ∀ ω, thr ρL ρR CanonSpace.drv xL' xR' (Y ω) = thr ρL ρR W xLc xRc ω := fun ω =>
    thr_congr (hWY ω) rfl rfl
  have hX'm : Measurable X' := (Exist.measurable_flowField 0 _).comp CanonSpace.measurable_field
  -- the initial σ-algebra of the canonical space
  have hword : Measurable[MeasurableSpace.comap CanonSpace.word inferInstance] CanonSpace.word :=
    comap_measurable _
  have hxL'm : Measurable[MeasurableSpace.comap CanonSpace.word inferInstance] xL' :=
    (measurable_typeXL κ θ nL nR ρL ρR).comp hword
  have hxR'm : Measurable[MeasurableSpace.comap CanonSpace.word inferInstance] xR' :=
    (measurable_typeXR κ θ nL nR ρL ρR).comp hword
  have hord : ∀ s, IsOrderedForceWord (xL' s) (xR' s) := fun s => isOrderedForceWord_typeXL s.word
  -- the canonical filtration reads `Y` from `𝓗`
  have hYq : ∀ q : ℝ≥0, Measurable[𝓗 q, CanonSpace.filt q] Y := by
    intro q
    rw [measurable_iff_comap_le]
    show MeasurableSpace.comap Y (MeasurableSpace.comap CanonSpace.word inferInstance ⊔
      ⨆ r : ℝ≥0, ⨆ (_ : r ≤ q), MeasurableSpace.comap (CanonSpace.drv r) inferInstance) ≤ 𝓗 q
    rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_iSup]
    refine sup_le ?_ (iSup_le fun r => ?_)
    · rw [MeasurableSpace.comap_comp]
      exact hc.comap_le.trans (𝓗.mono (zero_le (a := q)))
    · rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun hr => ?_
      rw [MeasurableSpace.comap_comp]
      have e : CanonSpace.drv r ∘ Y = W r := funext fun ω => hWY ω r
      rw [e]
      exact (hWa r).measurable.comap_le.trans (𝓗.mono hr)
  -- almost sure transfers
  have hQae : ∀ {p : CanonSpace → Prop}, (∀ᵐ s ∂Q, p s) → ∀ᵐ ω ∂P, ω ∈ M → p (Y ω) := fun h =>
    ae_imp_of_ae_cond hMm (ae_of_ae_map hY.aemeasurable h)
  have haeQ : ∀ {p : CanonSpace → Prop}, MeasurableSet {s | p s} → (∀ᵐ ω ∂P, ω ∈ M → p (Y ω)) →
      ∀ᵐ s ∂Q, p s := fun hp h => (ae_map_iff hY.aemeasurable hp).2 (ae_cond_of_ae_imp hMm h)
  -- the hypotheses on the canonical space
  have htype' : ∀ᵐ s ∂Q, IsFlowType κ θ s.word (xL' s) (xR' s) ρL ρR := by
    have h := haeQ (p := fun s => s.word ∈ typeSet κ θ nL nR ρL ρR)
      (CanonSpace.measurable_word (measurableSet_typeSet κ θ nL nR ρL ρR))
      (Eventually.of_forall fun ω hω => hMT ω hω)
    filter_upwards [h] with s hs using isFlowType_of_mem_typeSet hs
  have hseed' : ∀ᵐ s ∂Q, ¬ ForceWord.ThresholdCondition ρL ρR 0 (xL' s) (xR' s) := by
    refine haeQ ?_ hseed
    exact (((measurableSet_thresholdCondition_zero ρL ρR).preimage
      ((measurable_typeXL κ θ nL nR ρL ρR).comp CanonSpace.measurable_word |>.prodMk
        ((measurable_typeXR κ θ nL nR ρL ρR).comp CanonSpace.measurable_word))).compl)
  have hint' : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun s => X' s φ) Q := by
    intro φ
    have hφm : Measurable fun s => X' s φ := ((measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)).comp hX'm
    rw [integrable_map_measure hφm.aestronglyMeasurable hY.aemeasurable]
    rw [ProbabilityTheory.cond]
    exact (hint φ).smul_measure (ENNReal.inv_ne_top.2 hPM)
  -- the canonical continuation
  have hdrvc : ∀ s, Continuous fun t => CanonSpace.drv t s := fun s => continuous_decDrv _
  have hdrv0 : ∀ s, CanonSpace.drv 0 s = 0 := fun s => decDrv_zero _
  have hxL'₀ : Measurable[CanonSpace.filt 0] xL' := hxL'm.mono (CanonSpace.comap_word_le_filt 0) le_rfl
  have hxR'₀ : Measurable[CanonSpace.filt 0] xR' := hxR'm.mono (CanonSpace.comap_word_le_filt 0) le_rfl
  have hζm' : ∀ t : ℝ≥0, MeasurableSet[CanonSpace.filt t] {s | thr ρL ρR CanonSpace.drv xL' xR' s ≤ t} :=
    measurableSet_thr_le hdrvc CanonSpace.stronglyAdapted_drv hxL'₀ hxR'₀
  have hWa₀' : AdaptedBefore CanonSpace.filt (thr ρL ρR CanonSpace.drv xL' xR') CanonSpace.drv :=
    MartChar.adaptedBefore_of_stronglyAdapted hζm' CanonSpace.stronglyAdapted_drv
  have hVLa₀' : ∀ i, AdaptedBefore CanonSpace.filt (thr ρL ρR CanonSpace.drv xL' xR')
      (geomLW CanonSpace.drv xL' i) := fun i =>
    MartChar.adaptedBefore_of_stronglyAdapted hζm'
      (stronglyAdapted_geomLW CanonSpace.stronglyAdapted_drv hdrvc hxL'₀ i)
  have hVRa₀' : ∀ j, AdaptedBefore CanonSpace.filt (thr ρL ρR CanonSpace.drv xL' xR')
      (geomRW CanonSpace.drv xR' j) := fun j =>
    MartChar.adaptedBefore_of_stronglyAdapted hζm'
      (stronglyAdapted_geomRW CanonSpace.stronglyAdapted_drv hdrvc hxR'₀ j)
  have hweak' := isWeakPath_geom hdrv0 hdrvc xL' xR' (thr ρL ρR CanonSpace.drv xL' xR')
  have hav_congr : ∀ (ω : Ω) (ψ : ℂ → ℝ) (q : ℝ≥0),
      Y ω ∈ avoidSet CanonSpace.drv (thr ρL ρR CanonSpace.drv xL' xR') ψ q ↔
        ω ∈ avoidSet W (thr ρL ρR W xLc xRc) ψ q := fun ω ψ q => by
    simp only [avoidSet, mem_ofPred_eq, hthrY, hWY]
  -- (S) on the canonical space
  have hlaw' : HasSafeLaw κ ρL ρR Q CanonSpace.filt univ (thr ρL ρR CanonSpace.drv xL' xR') CanonSpace.drv
      (geomLW CanonSpace.drv xL') (geomRW CanonSpace.drv xR') X' := by
    intro ψ q D' hD' hD'ae
    have hD'm : MeasurableSet D' := CanonSpace.filt.le q _ hD'
    set u' := bheProc κ ρL ρR CanonSpace.drv (geomLW CanonSpace.drv xL') (geomRW CanonSpace.drv xR') with hu'
    set g' : CanonSpace → ℂ := (safeU CanonSpace.drv (thr ρL ρR CanonSpace.drv xL' xR') univ ψ q).indicator
      (cfAt κ CanonSpace.drv u' ψ 1 fun _ => q) with hg'
    have hg'm : Measurable g' :=
      (measurable_safeU_indicator_cfAt_of_weak hweak' hWa₀' MeasurableSet.univ u'
        (fun s r => isBoundedHarmonicExtension_bheProc s r) hVLa₀' hVRa₀' ψ q).mono (CanonSpace.filt.le q) le_rfl
    have hfm : Measurable fun s => Complex.exp (Complex.I * (X' s ψ : ℂ)) :=
      Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        (((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp hX'm)))
    have hRHS : ∫ s in D', cfAt κ CanonSpace.drv u' ψ 1 (fun _ => q) s ∂Q = ∫ s in D', g' s ∂Q := by
      refine setIntegral_congr_ae hD'm ?_
      filter_upwards [hD'ae] with s hs hsD
      exact (indicator_of_mem (mem_safeU_of_mem_avoidSet hweak' ψ (mem_univ s) (hs hsD).2) _).symm
    rw [hRHS, setIntegral_map_cond hMm hY hD'm hfm.aestronglyMeasurable,
      setIntegral_map_cond hMm hY hD'm hg'm.aestronglyMeasurable]
    congr 1
    have hD : MeasurableSet[𝓗 q] (M ∩ Y ⁻¹' D') := (𝓗.mono (zero_le (a := q)) _ hM).inter (hYq q hD')
    have hav : ∀ᵐ ω ∂P, ω ∈ M ∩ Y ⁻¹' D' → ω ∈ M ∧ ω ∈ avoidSet W (thr ρL ρR W xLc xRc) ψ q := by
      filter_upwards [hQae hD'ae] with ω hω hωD
      exact ⟨hωD.1, (hav_congr ω ψ q).1 (hω hωD.1 hωD.2).2⟩
    have key := hlaw ψ q (M ∩ Y ⁻¹' D') hD hav
    refine key.trans (setIntegral_congr_ae (hMm.inter (hY hD'm)) ?_)
    filter_upwards [hav] with ω hω hωD
    have hmem : Y ω ∈ safeU CanonSpace.drv (thr ρL ρR CanonSpace.drv xL' xR') univ ψ q :=
      mem_safeU_of_mem_avoidSet hweak' ψ (mem_univ _) ((hav_congr ω ψ q).2 (hω hωD).2)
    rw [hg', indicator_of_mem hmem]
    exact (cfAt_congr (hWY ω) rfl rfl κ ψ q).symm
  -- (L) on the canonical space
  have hmem' : HasSafeMembers Q CanonSpace.filt univ (thr ρL ρR CanonSpace.drv xL' xR') CanonSpace.drv X' := by
    intro q Fb hFb D' hD' hD'ae f Ξ
    have hD'm : MeasurableSet D' := CanonSpace.filt.le q _ hD'
    have hfm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun s => Complex.exp (Complex.I * (X' s φ : ℂ)) :=
      fun φ => Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
        (((measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)).comp hX'm)))
    rw [setIntegral_map_cond hMm hY hD'm (hfm _).aestronglyMeasurable,
      setIntegral_map_cond hMm hY hD'm (hfm _).aestronglyMeasurable, mul_smul_comm]
    congr 1
    have hD : MeasurableSet[𝓗 q] (M ∩ Y ⁻¹' D') := (𝓗.mono (zero_le (a := q)) _ hM).inter (hYq q hD')
    have hcond : ∀ᵐ ω ∂P, ω ∈ M ∩ Y ⁻¹' D' → ω ∈ M ∧ (q : ℝ≥0∞) < thr ρL ρR W xLc xRc ω ∧
        Disjoint (ballsK Fb) (fwdHull (fun r : ℝ => W r.toNNReal ω) (q : ℝ)) := by
      filter_upwards [hQae hD'ae] with ω hω hωD
      obtain ⟨-, h1, h2⟩ := hω hωD.1 hωD.2
      rw [hthrY] at h1
      simp only [hWY] at h2
      exact ⟨hωD.1, h1, h2⟩
    exact hmem q Fb hFb (M ∩ Y ⁻¹' D') hD hcond f Ξ
  -- (Det) on the canonical space, pulled back
  have hS := ae_driverCodeMatch_of_hasSafeLaw (Ω := CanonSpace)
    (𝒢 := MeasurableSpace.comap CanonSpace.word inferInstance) (P := Q) (θ := θ) hκ
    (CanonSpace.comap_word_le_filt 0) hword hxL'm hxR'm (fun s i => (hord s).2.1 i) (fun s j => (hord s).2.2.2 j)
    (fun s => (hord s).1) (fun s => (hord s).2.2.1) htype' hdrv0 hdrvc CanonSpace.stronglyAdapted_drv
    CanonSpace.measurable_field hX'm (fun s => Exist.isTranslateAddConst_flowField 0 _ _) hint' hseed' hlaw'
    hmem' hF
  filter_upwards [hQae hS] with ω hω hωM
  have h := hω hωM
  have e : (fun t => CanonSpace.drv t (Y ω)) = fun t => W t ω := funext fun t => hWY ω t
  rw [e, hthrY] at h
  exact h

end Main

end InteractingSLE.Restart.FCDet
