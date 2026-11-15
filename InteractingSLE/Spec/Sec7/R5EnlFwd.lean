/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlAdded
import InteractingSLE.Spec.Sec7.PocketTraversalMeas
import InteractingSLE.Spec.Sec7.SideC5Relative
import InteractingSLE.Spec.Sec7.PhaseContMeas
import InteractingSLE.Spec.Restart.ChartMeasRandom
import InteractingSLE.Spec.Ito.Loewner

/-!
# Measurability of the relative chart, at a fixed and at a random relative capacity (`hfwd`)

Packet PROVE-R5-ENLARGED (continued). R.5's reference chart is the relative Loewner chart `relChart c γ Q` of the
pocket traversal `γ` at the random relative capacity `Q = visitCap s` of the reference time `s`. The increment law
needs its forward map to be measurable for the reference record (`hfwd`). The route:

1. **Pathwise** (`relChart_fwd_eq_segG`): before the lifetime, on the chart's domain,
   `(relChart c γ q).fwd z = segG γ q (c.fwd z) − segDrv γ q`, with `c.fwd z` off the filled prefix: the chart is
   expressed through the canonical mapping-out function of the filled prefix (`segG`) and the canonical driver
   (`segDrv`), instead of a chosen local driver.
2. **Random points** (`measurable_indicator_comp_of_continuousAt`): a family of functions measurable at each fixed point
   and continuous at a measurable random point gives a measurable evaluation (the landed
   `Restart.measurable_of_tendsto_nhdsWithin`).
3. **Fixed capacity** (`measurable_indicator_fwd_relChart_fixed`): the forward map at a fixed relative capacity `q` is
   measurable for the relative prefix σ-algebra `locPrefixSigma 𝓦 A γ q` (the landed `measurable_indicator_mapOut` for
   `segG` and `measurable_indicator_segDrv_of_isDrivenCurve` for `segDrv`; the domain events from the active
   complement).
4. **Random capacity** (`measurable_indicator_fwd_relChart_rand`): approximate `Q` from below by dyadic `Q_n`; on
   `{Q_n = k 2⁻ⁿ}` the chart is the fixed-capacity one, transferred to the target record by a Galmarino-type hypothesis
   (`htrans`); the Loewner flow is continuous in time (`Ito.continuousOn_fwdMap_time'`), so the dyadic charts converge.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Enl

open PocketTraversal Lemma71C PocketStop PocketAdapt PocketCoupling

/-! ### 1. The relative chart through the canonical mapping-out function -/

section Path

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- **The relative chart through `segG` and `segDrv`.** Before the lifetime, for `z` in the relative chart's domain:
`c.fwd z` lies in the base chart's image off the filled prefix, the prefix complement is open, `segG γ q` is continuous
at `c.fwd z`, and the chart's forward value is `segG γ q (c.fwd z) − segDrv γ q`. -/
theorem relChart_fwd_eq_segG (hγ : IsDrivenCurve (γ ω)) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (γ ω))
    (hc : (c ω).IsConformal) {z : ℂ} (hz : z ∈ (relChart c γ q ω).dom) :
    z ∈ (c ω).dom ∧ (c ω).1 z ∈ H \ fillH (γ ω '' Icc 0 (capInv (γ ω) q)) ∧
      IsOpen (H \ fillH (γ ω '' Icc 0 (capInv (γ ω) q))) ∧
      ContinuousAt (segG (γ ω) q) ((c ω).1 z) ∧
      (relChart c γ q ω).1 z = segG (γ ω) q ((c ω).1 z) - segDrv (γ ω) q := by
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (γ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨n, hn0, hn⟩ := hγ.exists_pos_lt_capClock q.coe_nonneg hq'
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver n hn0
  have hK' : ∀ t ∈ Icc 0 (n : ℝ), fwdHull W (capClock (γ ω) t) = fillH (γ ω '' Icc 0 t) :=
    fun t ht => (hK t ht).2
  have heq : ∀ r ∈ Icc (0 : ℝ) (capClock (γ ω) n), segDriver (γ ω) r.toNNReal = W r := fun r hr => by
    show segDrv (γ ω) (r.toNNReal : ℝ) = W r
    rw [Real.coe_toNNReal _ hr.1]
    exact hγ.segDrv_eq hn0 hW hW0 hK' hr.1 hr.2
  have hrel : relChart c γ q ω = (c ω).loewner W q := loewner_congr (c ω) q.coe_nonneg hn heq
  have hcl := hc.loewner hW hW0 q.coe_nonneg
  have hfill : fillH (γ ω '' Icc 0 (capInv (γ ω) q)) = fwdHull W q :=
    hγ.fillH_capInv_eq hn0 hK' q.coe_nonneg hn.le
  have hdrv : segDrv (γ ω) q = W q := hγ.segDrv_eq hn0 hW hW0 hK' q.coe_nonneg hn.le
  rw [hrel] at hz ⊢
  rw [← SetLike.mem_coe, hcl.coe_dom] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hx : fwdMapInv W q w ∈ H \ fwdHull W q :=
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 q.coe_nonneg hw
  have hcx : (c ω).1 ((c ω).2.1 (fwdMapInv W q w)) = fwdMapInv W q w := hc.2.2 _ hx.1
  have hopen : IsOpen (H \ fwdHull W q) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW q.coe_nonneg
  change (c ω).2.1 (fwdMapInv W q w) ∈ (c ω).dom ∧ (c ω).1 ((c ω).2.1 (fwdMapInv W q w)) ∈ _ ∧ _ ∧
    ContinuousAt (segG (γ ω) q) ((c ω).1 ((c ω).2.1 (fwdMapInv W q w))) ∧
    fwdMap W q ((c ω).1 ((c ω).2.1 (fwdMapInv W q w))) = _
  rw [hcx, hfill]
  refine ⟨hc.inv_mem_dom hx.1, hx, hopen, ?_, ?_⟩
  · have hev : segG (γ ω) q =ᶠ[𝓝 (fwdMapInv W q w)] fun y => fwdMap W q y + W q := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hγ.segG_eq hn0 hW hW0 hK' q.coe_nonneg hn.le hy.1 hy.2
    refine ContinuousAt.congr ?_ hev.symm
    exact (((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW q.coe_nonneg).differentiableAt
      (hopen.mem_nhds hx)).continuousAt).add continuousAt_const
  · show fwdMap W q (fwdMapInv W q w) =
      segG (γ ω) q ((c ω).1 ((c ω).2.1 (fwdMapInv W q w))) - (segDrv (γ ω) q : ℂ)
    rw [hcx, hγ.segG_eq hn0 hW hW0 hK' q.coe_nonneg hn.le hx.1 hx.2, hdrv]
    ring

end Path

/-! ### 2. Measurable evaluation at a random point -/

section Eval

variable {Ω : Type*} [ℳ : MeasurableSpace Ω]

/-- **Evaluation at a measurable random point.** If `f ω` is measurable at each fixed point of the random open set
`D ω` (on `S`), `x` is measurable, `x ω ∈ D ω` and `f ω` is continuous at `x ω` for `ω ∈ S`, then `ω ↦ f ω (x ω)` is
measurable on `S`. -/
theorem measurable_indicator_comp_of_continuousAt {S : Set Ω} (hS : MeasurableSet S) {D : Ω → Set ℂ}
    (hDo : ∀ ω ∈ S, IsOpen (D ω)) (hDm : ∀ y, MeasurableSet (S ∩ {ω | y ∈ D ω})) {f : Ω → ℂ → ℂ}
    (hfm : ∀ y, Measurable ((S ∩ {ω | y ∈ D ω}).indicator fun ω => f ω y)) {x : Ω → ℂ} (hx : Measurable x)
    (hxD : ∀ ω ∈ S, x ω ∈ D ω) (hcont : ∀ ω ∈ S, ContinuousAt (f ω) (x ω)) :
    Measurable (S.indicator fun ω => f ω (x ω)) := by
  classical
  let D' : Ω → Set ℂ := fun ω => if ω ∈ S then D ω else univ
  let f' : Ω → ℂ → ℂ := fun ω => if ω ∈ S then f ω else fun _ => 0
  refine Restart.measurable_of_tendsto_nhdsWithin (D := D') (f := f') (q := x) (fun ω => ?_) (fun y => ?_)
    (fun y => ?_) hx (fun ω => ?_) (fun ω => ?_)
  · by_cases hω : ω ∈ S
    · simp only [D', hω, ↓reduceIte]
      exact hDo ω hω
    · simp only [D', hω, ↓reduceIte]
      exact isOpen_univ
  · have e : {ω | y ∈ D' ω} = (S ∩ {ω | y ∈ D ω}) ∪ Sᶜ := by
      ext ω
      by_cases hω : ω ∈ S <;> simp [D', hω]
    rw [e]
    exact (hDm y).union hS.compl
  · have e : ({ω | y ∈ D' ω}.indicator fun ω => f' ω y) = (S ∩ {ω | y ∈ D ω}).indicator fun ω => f ω y := by
      funext ω
      by_cases hω : ω ∈ S
      · by_cases hy : y ∈ D ω
        · rw [indicator_of_mem (show ω ∈ {ω | y ∈ D' ω} by simp [D', hω, hy]),
            indicator_of_mem (show ω ∈ S ∩ {ω | y ∈ D ω} from ⟨hω, hy⟩)]
          simp [f', hω]
        · rw [indicator_of_notMem (show ω ∉ {ω | y ∈ D' ω} by simp [D', hω, hy]),
            indicator_of_notMem (show ω ∉ S ∩ {ω | y ∈ D ω} from fun h => hy h.2)]
      · rw [indicator_of_notMem (show ω ∉ S ∩ {ω | y ∈ D ω} from fun h => hω h.1)]
        by_cases h : ω ∈ {ω | y ∈ D' ω}
        · rw [indicator_of_mem h]
          simp [f', hω]
        · rw [indicator_of_notMem h]
    rw [e]
    exact hfm y
  · by_cases hω : ω ∈ S
    · simp only [D', hω, ↓reduceIte]
      exact subset_closure (hxD ω hω)
    · simp only [D', hω, ↓reduceIte, closure_univ, mem_univ]
  · by_cases hω : ω ∈ S
    · simp only [D', f', hω, ↓reduceIte, indicator_of_mem hω]
      exact tendsto_nhdsWithin_of_tendsto_nhds (hcont ω hω).tendsto
    · simp only [f', hω, ↓reduceIte, indicator_of_notMem hω]
      exact tendsto_const_nhds

end Eval

/-! ### 3. The forward map at a fixed relative capacity -/

section Fixed

open Restart

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω}

/-- The prefix hits on the live event are relative-prefix events. -/
theorem measurableSet_live_inter_prefixHit {A : Set Ω} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {r : ℝ} (hr0 : 0 ≤ r)
    (hrq : r ≤ q) (n : ℕ) (k : ℤ × ℤ) :
    MeasurableSet[locPrefixSigma 𝓦 A γ q] ({ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩
      {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty}) := by
  have hrq' : r.toNNReal ≤ q := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
    exact hrq
  have e : {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩
      {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty} =
      {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩ (A ∩ prefixEvent γ r.toNNReal n k) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, prefixEvent, Real.coe_toNNReal _ hr0]
    constructor
    · rintro ⟨⟨hA, hq⟩, hhit⟩
      exact ⟨⟨hA, hq⟩, hA, lt_of_le_of_lt (by exact_mod_cast hrq') hq, hhit⟩
    · rintro ⟨h1, -, -, hhit⟩
      exact ⟨h1, hhit⟩
  rw [e]
  refine (PocketUnionPt.measurableSet_live (𝓦 := 𝓦) A γ q).inter ?_
  exact le_sup_right (a := 𝓦) _ (MeasurableSpace.measurableSet_generateFrom ⟨r.toNNReal, hrq', n, k, rfl⟩)

/-- **The relative chart's forward map at a fixed relative capacity is measurable for the relative prefix
σ-algebra** (with its domain events), from the base chart's measurability for the walls' σ-algebra `𝓦` and the
hitting measurability of the active complement. -/
theorem measurable_indicator_fwd_relChart_fixed {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcfwd : ∀ z, Measurable[𝓦] ((A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z))
    (q : ℝ≥0) (hKm : Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] (activeCompl A γ c q)) (z : ℂ) :
    MeasurableSet[locPrefixSigma 𝓦 A γ q]
        ({ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩ {ω | z ∈ (relChart c γ q ω).dom}) ∧
      Measurable[locPrefixSigma 𝓦 A γ q]
        (({ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩ {ω | z ∈ (relChart c γ q ω).dom}).indicator
          fun ω => (relChart c γ q ω).1 z) := by
  classical
  set ℳ : MeasurableSpace Ω := locPrefixSigma 𝓦 A γ q with hℳ
  set E : Set Ω := {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} with hEdef
  set S : Set Ω := E ∩ {ω | z ∈ (relChart c γ q ω).dom} with hSdef
  have hE : MeasurableSet[ℳ] E := PocketUnionPt.measurableSet_live (𝓦 := 𝓦) A γ q
  have hγE : ∀ ω ∈ E, IsDrivenCurve (γ ω) := fun ω hω => hγ ω hω.1
  have hdomE : ∀ ω ∈ E, ((relChart c γ q ω).dom : Set ℂ) = H \ activeCompl A γ c q ω := fun ω hω =>
    (PocketStopSide.H_diff_activeCompl_eq_relChart_dom hω.1 hω.2 (hγ ω hω.1) (hc ω hω.1)).symm
  have hS : MeasurableSet[ℳ] S := measurableSet_inter_mem_dom_of_hitting hE hKm hdomE
    (fun ω hω => by rw [← hdomE ω hω]; exact (relChart c γ q ω).dom.isOpen) z
  refine ⟨hS, ?_⟩
  -- the pathwise identity on `S`
  have hpath : ∀ ω ∈ S, z ∈ (c ω).dom ∧ (c ω).1 z ∈ H \ fillH (γ ω '' Icc 0 (capInv (γ ω) q)) ∧
      IsOpen (H \ fillH (γ ω '' Icc 0 (capInv (γ ω) q))) ∧ ContinuousAt (segG (γ ω) q) ((c ω).1 z) ∧
      (relChart c γ q ω).1 z = segG (γ ω) q ((c ω).1 z) - segDrv (γ ω) q := fun ω hω =>
    relChart_fwd_eq_segG (hγ ω hω.1.1) hω.1.2 (hc ω hω.1.1) hω.2
  -- the filled prefix as a random compact set
  set K : Ω → Set ℂ := Lemma71C.prefixOn γ E q with hKdef
  have hKE : ∀ ω ∈ E, K ω = γ ω '' Icc 0 (capInv (γ ω) q) := fun ω hω => by
    simp only [hKdef, Lemma71C.prefixOn, hω, ↓reduceIte, max_eq_left q.coe_nonneg]
  have hKd : @IsDyadicHitMeasurable Ω ℳ K := by
    intro n k
    have e : {ω | (dyadicSquare n k ∩ K ω).Nonempty} =
        E ∩ {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) q)).Nonempty} := by
      ext ω
      by_cases hω : ω ∈ E
      · simp only [mem_ofPred_eq, mem_inter_iff, hω, true_and, hKE ω hω]
      · simp only [hKdef, Lemma71C.prefixOn, hω, ↓reduceIte, inter_empty, Set.not_nonempty_empty,
          mem_ofPred_eq, mem_inter_iff, false_and]
    rw [e]
    exact measurableSet_live_inter_prefixHit q.coe_nonneg le_rfl n k
  have hKc : ∀ ω, IsCompact (K ω) := isCompact_prefixOn_of_isDrivenCurve hγE q
  have hKp := isPreconnected_prefixOn_of_isDrivenCurve hγE (q : ℝ)
  -- the base chart's forward value as a measurable random point
  set x : Ω → ℂ := (A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z with hxdef
  have hxm : Measurable[ℳ] x := (hcfwd z).mono le_sup_left le_rfl
  have hxS : ∀ ω ∈ S, x ω = (c ω).1 z := fun ω hω =>
    indicator_of_mem (show ω ∈ A ∩ {ω | z ∈ (c ω).dom} from ⟨hω.1.1, (hpath ω hω).1⟩) _
  -- `segG` at the random point
  have hG : Measurable[ℳ] (S.indicator fun ω => ConformalImage.mapOut (fillH (K ω)) (x ω)) := by
    refine measurable_indicator_comp_of_continuousAt (ℳ := ℳ) hS (D := fun ω => H \ fillH (K ω))
      (fun ω hω => by rw [hKE ω hω.1]; exact (hpath ω hω).2.2.1) (fun y => ?_) (fun y => ?_) hxm
      (fun ω hω => by rw [hxS ω hω, hKE ω hω.1]; exact (hpath ω hω).2.1)
      (fun ω hω => by
        rw [hxS ω hω, hKE ω hω.1]
        exact (hpath ω hω).2.2.2.1)
    · exact hS.inter (@measurableSet_mem_H_diff_fillH Ω ℳ K hKd hKc y)
    · have e : ((S ∩ {ω | y ∈ H \ fillH (K ω)}).indicator fun ω => ConformalImage.mapOut (fillH (K ω)) y) =
          S.indicator ({ω | y ∈ H \ fillH (K ω)}.indicator fun ω => ConformalImage.mapOut (fillH (K ω)) y) :=
        (indicator_indicator _ _ _).symm
      rw [e]
      exact (@measurable_indicator_mapOut Ω ℳ K hKd hKc hKp y).indicator hS
  -- the driver
  have hD : Measurable[ℳ] (E.indicator fun ω => segDrv (γ ω) q) :=
    @PocketTraversal.measurable_indicator_segDrv_of_isDrivenCurve Ω ℳ γ (q : ℝ) q.coe_nonneg E hγE hE
      (fun ω hω => by rw [ENNReal.ofReal_coe_nnreal]; exact hω.2)
      (fun r hr0 hrq n k => measurableSet_live_inter_prefixHit hr0 hrq n k)
  have e : (S.indicator fun ω => (relChart c γ q ω).1 z) =
      fun ω => S.indicator (fun ω => ConformalImage.mapOut (fillH (K ω)) (x ω)) ω -
        ((S.indicator (E.indicator fun ω => segDrv (γ ω) q) ω : ℝ) : ℂ) := by
    funext ω
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hω, indicator_of_mem hω.1,
        (hpath ω hω).2.2.2.2, hxS ω hω, hKE ω hω.1]
      rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem hω, indicator_of_notMem hω]
      simp
  rw [e]
  exact hG.sub (Complex.measurable_ofReal.comp (hD.indicator hS))

end Fixed

/-! ### 4. The forward map at a random relative capacity -/

section Random

/-- **Time continuity of the relative chart from below**: along capacities `q_n ≤ Q` tending to `Q`, the forward
values at a point of the chart's domain at `Q` converge. -/
theorem tendsto_relChart_fwd_of_le {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}
    (hγ : IsDrivenCurve (γ ω)) {Q : ℝ≥0} (hQ : (Q : ℝ≥0∞) < capLife (γ ω)) (hc : (c ω).IsConformal) {z : ℂ}
    (hz : z ∈ (relChart c γ Q ω).dom) {qs : ℕ → ℝ≥0} (hle : ∀ n, qs n ≤ Q)
    (hlim : Tendsto (fun n => (qs n : ℝ)) atTop (𝓝 (Q : ℝ))) :
    Tendsto (fun n => (relChart c γ (qs n) ω).1 z) atTop (𝓝 ((relChart c γ Q ω).1 z)) := by
  have hQ' : ENNReal.ofReal (Q : ℝ) < capLife (γ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨n, hn0, hn⟩ := hγ.exists_pos_lt_capClock Q.coe_nonneg hQ'
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hγ.localDriver n hn0
  have hK' : ∀ t ∈ Icc 0 (n : ℝ), fwdHull W (capClock (γ ω) t) = fillH (γ ω '' Icc 0 t) :=
    fun t ht => (hK t ht).2
  have heq : ∀ r ∈ Icc (0 : ℝ) (capClock (γ ω) n), segDriver (γ ω) r.toNNReal = W r := fun r hr => by
    show segDrv (γ ω) (r.toNNReal : ℝ) = W r
    rw [Real.coe_toNNReal _ hr.1]
    exact hγ.segDrv_eq hn0 hW hW0 hK' hr.1 hr.2
  have hrel : ∀ q : ℝ≥0, q ≤ Q → relChart c γ q ω = (c ω).loewner W q := fun q hq =>
    loewner_congr (c ω) q.coe_nonneg (lt_of_le_of_lt (show (q : ℝ) ≤ Q from hq) hn) heq
  have hcl := hc.loewner hW hW0 Q.coe_nonneg
  rw [hrel Q le_rfl, ← SetLike.mem_coe, hcl.coe_dom] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hx : fwdMapInv W Q w ∈ H \ fwdHull W Q :=
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 Q.coe_nonneg hw
  have hcx : (c ω).1 ((c ω).2.1 (fwdMapInv W Q w)) = fwdMapInv W Q w := hc.2.2 _ hx.1
  have hseq : ∀ k, (relChart c γ (qs k) ω).1 ((c ω).2.1 (fwdMapInv W Q w)) = fwdMap W (qs k) (fwdMapInv W Q w) := by
    intro k
    rw [hrel (qs k) (hle k)]
    show fwdMap W (qs k) ((c ω).1 ((c ω).2.1 (fwdMapInv W Q w))) = _
    rw [hcx]
  rw [hrel Q le_rfl]
  show Tendsto (fun k => (relChart c γ (qs k) ω).1 ((c ω).2.1 (fwdMapInv W Q w))) atTop
    (𝓝 (fwdMap W Q ((c ω).1 ((c ω).2.1 (fwdMapInv W Q w)))))
  simp only [hseq, hcx]
  have hcont := Ito.continuousOn_fwdMap_time' hW Q.coe_nonneg hx
  exact (hcont (Q : ℝ) ⟨Q.coe_nonneg, le_rfl⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun k => ⟨(qs k).coe_nonneg, hle k⟩⟩)

/-- The dyadic approximation from below of a capacity. -/
def dyadBelow (n : ℕ) (x : ℝ≥0) : ℝ≥0 := (⌊x * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n

theorem dyadBelow_le (n : ℕ) (x : ℝ≥0) : dyadBelow n x ≤ x := by
  rw [dyadBelow, div_le_iff₀ (pow_pos two_pos n)]
  exact Nat.floor_le zero_le

theorem tendsto_dyadBelow (x : ℝ≥0) : Tendsto (fun n => (dyadBelow n x : ℝ)) atTop (𝓝 (x : ℝ)) := by
  have hb : ∀ n : ℕ, (x : ℝ) - 1 / 2 ^ n ≤ dyadBelow n x := by
    intro n
    have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
    have hfl : ((x : ℝ) * 2 ^ n) < (⌊x * 2 ^ n⌋₊ : ℝ) + 1 := by
      have := Nat.lt_floor_add_one (x * 2 ^ n)
      exact_mod_cast this
    have e : (dyadBelow n x : ℝ) = (⌊x * 2 ^ n⌋₊ : ℝ) / 2 ^ n := by
      simp [dyadBelow]
    rw [e, le_div_iff₀ h2, sub_mul, one_div, inv_mul_cancel₀ h2.ne']
    linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hb
    (fun n => by exact_mod_cast dyadBelow_le n x)
  have h : Tendsto (fun n : ℕ => (x : ℝ) - 1 / 2 ^ n) atTop (𝓝 ((x : ℝ) - 0)) := by
    refine tendsto_const_nhds.sub ?_
    simp only [one_div]
    exact tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  simpa only [sub_zero] using h

theorem dyadBelow_eq_iff (n k : ℕ) (x : ℝ≥0) :
    dyadBelow n x = (k : ℝ≥0) / 2 ^ n ↔ (k : ℝ≥0) / 2 ^ n ≤ x ∧ ¬ ((k + 1 : ℕ) : ℝ≥0) / 2 ^ n ≤ x := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyadBelow, div_left_inj' h2.ne', Nat.cast_inj, Nat.floor_eq_iff zero_le, div_le_iff₀ h2,
    div_le_iff₀ h2, not_le]
  push_cast
  rfl

variable {Ω : Type*} {𝓦 ℳ : MeasurableSpace Ω}

/-- **`hfwd` for the relative chart at a random capacity.** On an event `G₀ ⊆ A` (measurable for the target record
`ℳ`, the random capacity `Q` live), if every relative-prefix event at a fixed capacity `q`, restricted to
`G₀ ∩ {q ≤ Q}`, is an `ℳ`-event (`htrans`, a Galmarino property), then the forward map at `Q` is `ℳ`-measurable on the
domain event. -/
theorem measurable_indicator_fwd_relChart_rand {A : Set Ω} {γ : Ω → ℝ → ℂ} {c : Ω → Chart}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcfwd : ∀ z, Measurable[𝓦] ((A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z))
    (hKm : ∀ q : ℝ≥0, Measurable[locPrefixSigma 𝓦 A γ q, hittingSigma] (activeCompl A γ c q))
    {Q : Ω → ℝ≥0} {G₀ : Set Ω} (hG₀ : MeasurableSet[ℳ] G₀) (hG₀A : G₀ ⊆ A)
    (hQlive : ∀ ω ∈ G₀, (Q ω : ℝ≥0∞) < capLife (γ ω))
    (htrans : ∀ (q : ℝ≥0) (M : Set Ω), MeasurableSet[locPrefixSigma 𝓦 A γ q] M →
      MeasurableSet[ℳ] (G₀ ∩ {ω | q ≤ Q ω} ∩ M)) (z : ℂ)
    (hdom : MeasurableSet[ℳ] (G₀ ∩ {ω | z ∈ (relChart c γ (Q ω) ω).dom})) :
    Measurable[ℳ] ((G₀ ∩ {ω | z ∈ (relChart c γ (Q ω) ω).dom}).indicator
      fun ω => (relChart c γ (Q ω) ω).1 z) := by
  classical
  -- the fixed-capacity maps
  set f : ℝ≥0 → Ω → ℂ := fun q => ({ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} ∩
    {ω | z ∈ (relChart c γ q ω).dom}).indicator fun ω => (relChart c γ q ω).1 z with hfdef
  have hfm : ∀ q, Measurable[locPrefixSigma 𝓦 A γ q] (f q) := fun q =>
    (measurable_indicator_fwd_relChart_fixed hγ hc hcfwd q (hKm q) z).2
  -- the dyadic approximants on `G₀`
  set F : ℕ → Ω → ℂ := fun n => G₀.indicator fun ω => f (dyadBelow n (Q ω)) ω with hFdef
  have hFm : ∀ n, Measurable[ℳ] (F n) := by
    intro n U hU
    have e : F n ⁻¹' U = (G₀ᶜ ∩ {_ω | (0 : ℂ) ∈ U}) ∪ ⋃ k : ℕ,
        ((G₀ ∩ {ω | ((k : ℝ≥0) / 2 ^ n) ≤ Q ω} ∩ f ((k : ℝ≥0) / 2 ^ n) ⁻¹' U) \
          (G₀ ∩ {ω | (((k + 1 : ℕ) : ℝ≥0) / 2 ^ n) ≤ Q ω} ∩ univ)) := by
      ext ω
      simp only [hFdef, mem_preimage, mem_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, mem_iUnion,
        Set.mem_sdiff, mem_univ, and_true]
      by_cases hω : ω ∈ G₀
      · rw [indicator_of_mem hω]
        constructor
        · intro h
          right
          refine ⟨⌊Q ω * 2 ^ n⌋₊, ?_⟩
          have hd := (dyadBelow_eq_iff n ⌊Q ω * 2 ^ n⌋₊ (Q ω)).1 rfl
          refine ⟨⟨⟨hω, hd.1⟩, h⟩, fun h' => hd.2 h'.2⟩
        · rintro (⟨h1, -⟩ | ⟨k, ⟨⟨-, hk1⟩, hk⟩, hk2⟩)
          · exact absurd hω h1
          · have hd : dyadBelow n (Q ω) = (k : ℝ≥0) / 2 ^ n :=
              (dyadBelow_eq_iff n k (Q ω)).2 ⟨hk1, fun h => hk2 ⟨hω, h⟩⟩
            rw [hd]
            exact hk
      · rw [indicator_of_notMem hω]
        constructor
        · intro h
          exact Or.inl ⟨hω, h⟩
        · rintro (⟨-, h⟩ | ⟨k, ⟨⟨h, -⟩, -⟩, -⟩)
          · exact h
          · exact absurd h hω
    rw [e]
    refine (hG₀.compl.inter (MeasurableSet.const _)).union (MeasurableSet.iUnion fun k => ?_)
    refine (htrans _ _ ((hfm _) hU)).diff (htrans _ _ ?_)
    exact @MeasurableSet.univ _ (locPrefixSigma 𝓦 A γ _)
  -- the limit on the domain event
  set D : Set Ω := G₀ ∩ {ω | z ∈ (relChart c γ (Q ω) ω).dom} with hDdef
  refine measurable_of_tendsto_metrizable (f := fun n => D.indicator (F n)) (fun n => (hFm n).indicator hdom) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ D
  · simp only [indicator_of_mem hω]
    have hA := hG₀A hω.1
    have hval : ∀ n, F n ω = (relChart c γ (dyadBelow n (Q ω)) ω).1 z := by
      intro n
      have hq : (dyadBelow n (Q ω) : ℝ≥0∞) < capLife (γ ω) :=
        lt_of_le_of_lt (by exact_mod_cast dyadBelow_le n (Q ω)) (hQlive ω hω.1)
      have hzd : z ∈ (relChart c γ (dyadBelow n (Q ω)) ω).dom :=
        PocketStopSide.relChart_dom_antitone (hc ω hA) (hγ ω hA) (hQlive ω hω.1) (dyadBelow_le n (Q ω)) hω.2
      simp only [hFdef, hfdef, indicator_of_mem hω.1]
      set q : ℝ≥0 := dyadBelow n (Q ω) with hqdef
      exact indicator_of_mem (show ω ∈ {ω' | ω' ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω')} ∩
        {ω' | z ∈ (relChart c γ q ω').dom} from ⟨⟨hA, hq⟩, hzd⟩) _
    simp only [hval]
    exact tendsto_relChart_fwd_of_le (hγ ω hA) (hQlive ω hω.1) (hc ω hA) hω.2 (fun n => dyadBelow_le n (Q ω))
      (tendsto_dyadBelow (Q ω))
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

end Random

end InteractingSLE.Sec7.R5Enl
