/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OLawR7
import InteractingSLE.Spec.Sec7.R5OLawDom
import InteractingSLE.Spec.Sec7.R5OutVisit
import InteractingSLE.Spec.Sec7.R5OutRef
import InteractingSLE.Spec.Sec7.R5EnlFwdR7

/-!
# Clause 4 of `R5Out.R5ClausesCompOn` on the visit references of an outer pocket (bounded)

Packet PROVE-R5-OUTERLAW (ruling R88). The outer twin of PROVE-R5-ENLARGED's `R5EnlFwdR7`. The `i`-th reference
chart is R5-REFCHART's `R5Ref.refChart` (the relative chart at the capacity `visitCap s` reached at the original
time `s = rationalOriginalTime i`), on an outer test (`HOuter.IsOuterCfg`). Its domain is the component of the
reference complement `C ∩ (ℍ ∖ K̃_s)` incident to the pocket target:

* **window identity** (`stopTimeM_le_iff_visitCap_outer`, `le_stopTimeM_of_visitCap_le_outer`,
  `visitCap_le_of_le_stopTimeM_outer`): at a visit `s`, `T⁰(q) ≤ s ↔ q ≤ visitCap s`, and `s ≤ T⁰(q) ↔ visitCap s ≤ q`
  (`q` live);
* **the chart on the window** (`refWindow_spec_outer`): live, conformal, `dom ⊆ ℍ ∖ B`, and `(ℍ ∖ B) ∖ dom` open —
  a point of the reference complement off the domain has its image in the relative hull but not on the relative trace
  (a pocket point on the trace up to `visitCap s` is in `K̃_s`, `outer_mem_hull_of_prefix`), hence in a bounded
  component of the complement of the trace (`isOpen_inter_preimage_fillH`);
* **`hdom`, `hfwd`** (`measurable_fwd_visitRef_outer`): through `R5OLaw.measurable_indicator_fwd_relChart_rand'` with
  the Galmarino transfer from `PocketStopMarked.Outer.isMarkedStop_stopTimeM`;
* **`r7HasOldChartIncrementLawOn_visit_outer`**, **`r7HasOldChartIncrementLawOn_ref_outer`**,
  **`r5ClausesCompOn_clause4_ref_outer`** — clause 4 of `R5Out.R5ClausesCompOn` for R5-REFCHART's family
  (`refEvent`, `refChart`, `F = refHull`) on an outer test.

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5OLaw

open WholeField PocketStopField PocketStopWalls PocketCoupling Lemma71C Lemma71I PocketCoord PocketJordan
  PocketMarks PocketWordAssembly PocketTraversal PocketAdapt PocketStop PocketStopWallsFin PocketStopMarked
  PocketWordPerQ PocketUnionPt R5Phase LocalSets Sec6 R5Enl

/-! ### A topological lemma: off the trace, the filled hull is open -/

/-- If `ψ` is continuous on the open `C` and no point of `C ∩ U` maps onto the closed set `X`, the points of
`C ∩ U` mapping into the filling of `X` form an open set (their images lie in bounded components of `ℍ ∖ X`). -/
theorem isOpen_inter_preimage_fillH {C U X : Set ℂ} {ψ : ℂ → ℂ} (hCo : IsOpen C) (hUo : IsOpen U)
    (hψc : ContinuousOn ψ C) (hX : IsClosed X) (hXU : ∀ y ∈ C ∩ U, ψ y ∉ X) :
    IsOpen (C ∩ U ∩ ψ ⁻¹' fillH X) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨⟨hzC, hzU⟩, hzF⟩ := hz
  have hzX : ψ z ∉ X := hXU z ⟨hzC, hzU⟩
  obtain ⟨hzH, hzF'⟩ := hzF
  rw [hX.closure_eq] at hzF'
  have hb : Bornology.IsBounded (connectedComponentIn (H \ X) (ψ z)) := hzF'.resolve_left hzX
  set V := connectedComponentIn (H \ X) (ψ z) with hV
  have hVo : IsOpen V := (QuantumZipper.isOpen_H.sdiff hX).connectedComponentIn
  have hVF : V ⊆ fillH X := by
    intro w hw
    have hwHX : w ∈ H \ X := connectedComponentIn_subset _ _ hw
    refine ⟨hwHX.1, Or.inr ?_⟩
    rw [hX.closure_eq, ← connectedComponentIn_eq hw]
    exact hb
  refine ⟨C ∩ ψ ⁻¹' V ∩ U, fun w hw => ⟨⟨hw.1.1, hw.2⟩, hVF hw.1.2⟩,
    (hψc.isOpen_inter_preimage hCo hVo).inter hUo, ⟨⟨hzC, ?_⟩, hzU⟩⟩
  exact mem_connectedComponentIn ⟨hzH, hzX⟩

/-! ### The window identity at a visit (bounded outer pocket) -/

section Path

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω}

/-- **The window identity** (outer pocket): if the counterflow visits the pocket at the original time `s`, the left
stop of `q` is at most `s` iff `q` is at most the capacity reached at `s`. -/
theorem stopTimeM_le_iff_visitCap_outer
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {ω : Ω} (hω : ω ∈ A) {s : ℝ≥0}
    (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) (q : ℝ≥0) :
    stopTimeM A R L r η ψ q ω ≤ s ↔ q ≤ (visitCap R L r η ψ ω s).toNNReal := by
  have hP := (hcfg ω hω).toPocket (hψ ω hω)
  have hv : (s : ℝ) ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := ⟨hP.erase.mem_Ioo s s.coe_nonneg hvisit, hvisit⟩
  obtain ⟨hpos, -⟩ := SideVis.erasure_relCap_pos_lt_of_visit hP.erase hP.driven hv
  unfold visitCap
  rw [PocketStopMarked.Outer.stopTimeM_le_iff hcfg hψ q hω s, Real.le_toNNReal_iff_coe_le hpos.le]
  constructor
  · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
    · exact h
    · exact absurd h (not_le.2 hv.1.2)
  · exact fun h => Or.inl ⟨hv.1.1.le, hv.1.2, h⟩

/-- **After the capacity reached at a visit, the left stop is after the visit** (outer pocket): `visitCap s ≤ q`
(`q` live) gives `s ≤ T⁰(q)`. -/
theorem le_stopTimeM_of_visitCap_le_outer
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {ω : Ω} (hω : ω ∈ A) {s : ℝ≥0}
    (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hle : (visitCap R L r η ψ ω s).toNNReal ≤ q) : (s : ℝ≥0∞) ≤ stopTimeM A R L r η ψ q ω := by
  have hP := (hcfg ω hω).toPocket (hψ ω hω)
  have hv : (s : ℝ) ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := ⟨hP.erase.mem_Ioo s s.coe_nonneg hvisit, hvisit⟩
  obtain ⟨hpos, hlive⟩ := SideVis.erasure_relCap_pos_lt_of_visit hP.erase hP.driven hv
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travAll R L r η ψ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  rw [R5OLaw.stopTimeM_eq_of_live hω hq, stopTime0, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (le_of_not_gt fun hlt => ?_)
  unfold visitCap at hle
  have hQq := (Real.toNNReal_le_iff_le_coe).1 hle
  have hm := PocketStopMarked.Outer.ambTime0_mem_Ico hP q.coe_nonneg hq'
  have h1 := (PocketStopMarked.Outer.ambTime0_le_iff hP q.coe_nonneg hq' hm).1 le_rfl
  have hTQ := R5Out.ambTime0_relCap_of_visit hP hv
  have h2 := R5Out.relCap_lt_of_lt_ambTime0 hP hpos.le hlive hm (by rw [hTQ]; exact hlt)
  linarith

/-- **Before the left stop, the capacity reached at a visit is at most `q`** (outer pocket, `q` live). -/
theorem visitCap_le_of_le_stopTimeM_outer
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) {ω : Ω} (hω : ω ∈ A) {s : ℝ≥0}
    (hvisit : η ω s ∈ cfPocket (R ω) (L ω) r) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsT : (s : ℝ≥0∞) ≤ stopTimeM A R L r η ψ q ω) : (visitCap R L r η ψ ω s).toNNReal ≤ q := by
  have hP := (hcfg ω hω).toPocket (hψ ω hω)
  have hv : (s : ℝ) ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := ⟨hP.erase.mem_Ioo s s.coe_nonneg hvisit, hvisit⟩
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travAll R L r η ψ ω) := by rwa [ENNReal.ofReal_coe_nnreal]
  have hm := PocketStopMarked.Outer.ambTime0_mem_Ico hP q.coe_nonneg hq'
  have hsT' : (s : ℝ) ≤ ambTime0 (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) q := by
    rw [R5OLaw.stopTimeM_eq_of_live hω hq, stopTime0, ← ENNReal.ofReal_coe_nnreal] at hsT
    exact (ENNReal.ofReal_le_ofReal_iff (hP.erase.nonneg.trans hm.1)).1 hsT
  -- `relCap t < q` on `[τ, s)`, and `relCap` is continuous at `s`
  unfold visitCap
  rw [Real.toNNReal_le_iff_le_coe]
  have hτs : firstHit (η ω) (cfArcR (R ω) (L ω) r 1) < s := hv.1.1
  have hcont : ContinuousWithinAt (relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) (Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) s) s :=
    ((PocketStopMarked.Outer.continuousOn_relCap hP) s ⟨hτs.le, hv.1.2⟩).mono
      fun t ht => ⟨ht.1, ht.2.trans hv.1.2⟩
  have hcl : (s : ℝ) ∈ closure (Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) s) := by
    rw [closure_Ico hτs.ne]; exact ⟨hτs.le, le_rfl⟩
  refine ContinuousWithinAt.closure_le hcl hcont continuousWithinAt_const fun t ht => ?_
  exact (R5Out.relCap_lt_of_lt_ambTime0 hP q.coe_nonneg hq' ⟨ht.1, ht.2.trans hv.1.2⟩
    (lt_of_lt_of_le ht.2 hsT')).le

end Path

/-! ### The reference chart on the window (bounded outer pocket) -/

section Window

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {η : Ω → ℝ → ℂ}
  {ψ : Ω → ℂ → ℂ} {A : Set Ω} {c : Ω → Chart}

/-- **The reference chart on the window** (bounded outer pocket): its capacity is live, it is conformal, its domain
lies in the reference complement `ℍ ∖ liveExt(K̃_s, 0)`, and the rest of the reference complement is open. -/
theorem refWindow_spec_outer
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hc : ∀ ω ∈ A, (c ω).IsConformal) (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (s : ℝ≥0) :
    ∀ ω ∈ refWindow A R L r η s,
      ((visitCap R L r η ψ ω s).toNNReal : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).IsConformal ∧
      ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom : Set ℂ) ⊆
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω ∧
      IsOpen ((H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω) \
        ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom : Set ℂ)) := by
  rintro ω ⟨hω, hv | hz⟩
  · have hP := (hcfg ω hω).toPocket (hψ ω hω)
    have hγ : IsDrivenCurve (travAll R L r η ψ ω) := ((hcfg ω hω).props (hψ ω hω)).1
    have hCH : cfPocket (R ω) (L ω) r ⊆ H := hP.subset_H
    have hCo : IsOpen (cfPocket (R ω) (L ω) r) := by
      rw [← hcdom ω hω]; exact (c ω).dom.isOpen
    have hHull : regHull W' ζ' s ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) s :=
      regHull_eq (continuous_nnreal_of_continuous_real (hcfg ω hω).continuous_W) (hζA ω hω) s
    have hl0 : ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
      refine ⟨hω, ?_⟩
      rw [ENNReal.coe_zero]
      exact PocketPhaseMeans.capLife_pos hγ
    have hB : H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω =
        cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) s) := by
      rw [liveExt_of_live hl0, H_diff_extHullSet, hHull]
    obtain ⟨hlive, hconf, hsub⟩ := R5Out.visit_chart_subset (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω (hcfg ω hω) (hψ
        ω hω) (hc ω hω) (hcdom ω hω)
      (hceq ω hω) s.coe_nonneg hv
    refine ⟨hlive, hconf, by rw [hB]; exact hsub, ?_⟩
    -- the rest of the reference complement: images in the filled relative prefix, off the prefix itself
    set Q : ℝ≥0 := (visitCap R L r η ψ ω s).toNNReal with hQ
    have hv' : (s : ℝ) ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) := ⟨hP.erase.mem_Ioo s s.coe_nonneg hv, hv⟩
    have hpos := (SideVis.erasure_relCap_pos_lt_of_visit hP.erase hP.driven hv').1
    have hQs : ((Q : ℝ)) = visitCap R L r η ψ ω s := Real.coe_toNNReal _ hpos.le
    have hlive' : ENNReal.ofReal (Q : ℝ) < capLife (travAll R L r η ψ ω) := by
      rw [ENNReal.ofReal_coe_nnreal]; exact hlive
    have hdom : ((relChart c (travAll R L r η ψ) Q ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ ψ ω ⁻¹' (H \ fillH (travAll R L r η ψ ω '' Icc 0
          (capInv (travAll R L r η ψ ω) Q))) := by
      rw [R5Out.current_dom_eq_relHull (C := fun ω => cfPocket (R ω) (L ω) r) (ψ := ψ) hω hlive hγ (hc ω hω)
          (hcdom ω hω) (hceq ω hω) hCH (hψ ω hω).2.2.2.1, HOuter.H_diff_relHull hCH,
        hγ.fwdHull_segDriver Q.coe_nonneg hlive']
    have e : (H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0 ω) \
        ((relChart c (travAll R L r η ψ) Q ω).dom : Set ℂ) =
        cfPocket (R ω) (L ω) r ∩ (H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) s) ∩
          ψ ω ⁻¹' fillH (travAll R L r η ψ ω '' Icc 0 (capInv (travAll R L r η ψ ω) Q)) := by
      rw [hB, hdom]
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨⟨hzC, hzs⟩, hn⟩
        refine ⟨⟨hzC, hzs⟩, ?_⟩
        by_contra hF
        exact hn ⟨hzC, (hψ ω hω).2.2.2.1.2.mapsTo hzC, hF⟩
      · rintro ⟨⟨hzC, hzs⟩, hF⟩
        exact ⟨⟨hzC, hzs⟩, fun h => h.2.2 hF⟩
    rw [e]
    refine isOpen_inter_preimage_fillH hCo (QuantumZipper.FwdHolo.isOpen_compl_fwdHull
      (hcfg ω hω).continuous_W s.coe_nonneg) (hψ ω hω).2.2.2.1.1.continuousOn
      (isCompact_Icc.image_of_continuousOn (hγ.continuousOn.mono fun t ht => ht.1)).isClosed ?_
    rintro y ⟨hyC, hys⟩ hyX
    have hyT := outer_mem_hull_of_prefix (hcfg ω hω) (hψ ω hω) Q hyC hyX
    rw [hQs] at hyT
    unfold visitCap at hyT
    rw [R5Out.ambTime0_relCap_of_visit hP hv'] at hyT
    exact hys.2 hyT
  · subst hz
    have hγ := ((hcfg ω hω).props (hψ ω hω)).1
    have h0 : (visitCap R L r η ψ ω ((0 : ℝ≥0) : ℝ)).toNNReal = 0 := by
      rw [NNReal.coe_zero, R5Out.visitCap_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω),
          Real.toNNReal_zero]
    have hCH : cfPocket (R ω) (L ω) r ⊆ H := ((hcfg ω hω).toPocket (hψ ω hω)).subset_H
    have hlive : ((0 : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := by
      rw [ENNReal.coe_zero]
      exact PocketPhaseMeans.capLife_pos hγ
    have hHull : regHull W' ζ' 0 ω = ∅ := by
      rw [regHull_eq (continuous_nnreal_of_continuous_real (hcfg ω hω).continuous_W) (hζA ω hω), NNReal.coe_zero,
        QuantumZipper.RS.fwdHull_zero_eq_empty (hcfg ω hω).continuous_W]
    have hdomeq : ((relChart c (travAll R L r η ψ) 0 ω).dom : Set ℂ) =
        H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' 0) 0 ω := by
      rw [R5Ref.relChart_zero_dom (c := c) (γ := travAll R L r η ψ) hγ, hcdom ω hω, H_diff_liveExt_zero hω hγ,
        hHull, sdiff_empty]
      exact (inter_eq_left.2 hCH).symm
    rw [h0]
    refine ⟨hlive, PocketStopSide.isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hlive
      (hc ω hω), hdomeq.le, ?_⟩
    rw [← hdomeq, Set.sdiff_self]
    exact isOpen_empty

variable {nL nR : ℕ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {G : Set Ω}

/-- **The reference window is an event of the reference record** `σ(walls) ∨ 𝓕_s` (outer pocket; on the test the
counterflow is the trace of the adapted driver). -/
theorem measurableSet_refWindow_outer (hX : IsMeasurableKilledDriving W' VL VR ζ')
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (s : ℝ≥0) :
    MeasurableSet[refInfo P hX R L s] (refWindow A R L r η s) := by
  have h𝓦s : wallsSigma P R L ≤ refInfo P hX R L s := wallsSigma_le_refInfo hX R L s
  by_cases hs : s = 0
  · subst hs
    rw [refWindow_zero]
    exact h𝓦s _ hA
  rw [refWindow_of_ne hs]
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have e : {ω | ω ∈ A ∧ η ω s ∈ cfPocket (R ω) (L ω) r} =
      {ω | ω ∈ A ∧ adTrace W' ζ' ω s ∈ cfPocket (R ω) (L ω) r} := by
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hω, h⟩
      exact ⟨hω, by rw [PocketStopMarked.Outer.adTrace_eq_of_mem hcfg hζA hω s.coe_nonneg]; exact h⟩
    · rintro ⟨hω, h⟩
      exact ⟨hω, by rw [← PocketStopMarked.Outer.adTrace_eq_of_mem hcfg hζA hω s.coe_nonneg]; exact h⟩
  rw [e]
  exact measurableSet_visit (mΩ := refInfo P hX R L s) (e := adTrace W' ζ') h𝓦s
    (measurable_right_wallsSigma hRc hLc) (measurable_left_wallsSigma hRc hLc) hGm hG (h𝓦s _ hA) hAG
    (measurable_adTrace_sup (X := fullHist ![R, L]) hWad le_rfl)

end Window

/-! ### `hdom` and `hfwd` for the reference chart (bounded outer pocket) -/

section Fwd

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h'' : Ω → DistOn upperHalfPlaneOpens}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {G A : Set Ω} {c : Ω → Chart}

/-- **The fixed-capacity inputs of an outer R.7 test** (the outer twin of `R5Enl.r7_fixed_inputs`, with the
traversal's fixed-time measurability `HOuter.measurable_travAll_outer`): the traversal at fixed own times, the pocket
and the coordinate at fixed points, the base chart's forward map, and the active complements at fixed capacities. -/
theorem r7_fixed_inputs_outer (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ)
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hc : ∀ ω ∈ A, (c ω).IsConformal) (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) :
    (∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u) ∧
      (∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}) ∧
      (∀ z, Measurable[wallsSigma P R L]
        ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z)) ∧
      (∀ z, Measurable[wallsSigma P R L] ((A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z)) ∧
      ∀ q : ℝ≥0, Measurable[locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q, hittingSigma]
        (activeCompl A (travAll R L r η ψ) c q) := by
  classical
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hCm : ∀ z, MeasurableSet[wallsSigma P R L] {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := fun z =>
    measurableSet_mem_cfPocket_of_subset hRm' hLm' hGm hG hA hAG z
  have hψm' : ∀ z, Measurable[wallsSigma P R L]
      ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := fun z =>
    hψm _ (hCm z) (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω =>
      ⟨subset_closure hω.2, fun h => (hG ω (hAG hω.1)).cfPt_openPt_notMem (h ▸ hω.2)⟩
  have hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => travAll R L r η ψ ω u := fun u hu =>
    HOuter.measurable_travAll_outer h𝓦 hRm' hLm' hA hcfg hηm subset_rfl hψ
      (fun A' hA' hA'A p hp hpC => hψm A' hA' (hA'A.trans hAG) p hp hpC) hu
  refine ⟨hγm, hCm, hψm', fun z => ?_, fun q => ?_⟩
  · have e : ((A ∩ {ω | z ∈ (c ω).dom}).indicator fun ω => (c ω).1 z) =
        {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z := by
      funext ω
      by_cases hω : ω ∈ A
      · have hmem : z ∈ (c ω).dom ↔ z ∈ cfPocket (R ω) (L ω) r := by
          rw [← SetLike.mem_coe, hcdom ω hω]
        by_cases hz : z ∈ cfPocket (R ω) (L ω) r
        · rw [indicator_of_mem (show ω ∈ A ∩ {ω | z ∈ (c ω).dom} from ⟨hω, hmem.2 hz⟩),
            indicator_of_mem (show ω ∈ {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} from ⟨hω, hz⟩), hceq ω hω hz]
        · rw [indicator_of_notMem (show ω ∉ A ∩ {ω | z ∈ (c ω).dom} from fun h => hz (hmem.1 h.2)),
            indicator_of_notMem (show ω ∉ {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} from fun h => hz h.2)]
      · rw [indicator_of_notMem (show ω ∉ A ∩ {ω | z ∈ (c ω).dom} from fun h => hω h.1),
          indicator_of_notMem (show ω ∉ {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} from fun h => hω h.1)]
    rw [e]
    exact hψm' z
  · have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω => by
      rw [← hcdom ω hω]
      exact (c ω).dom.isOpen
    have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω => by
      rw [← hcdom ω hω, (hc ω hω).coe_dom]
      exact (hc ω hω).2.1.image_subset
    exact PhaseCont.measurable_activeCompl_locPrefixSigma h𝓦 hA hγ hγm hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1)
      hCm hψm' (fun U hUo hUH => Lemma725RefMarks.measurableSet_subset_cfPocket hRm' hLm' hGm hG hA hAG hUo hUH)
      (fun ω hω => ⟨hc ω hω, hcdom ω hω, hceq ω hω⟩) q

/-- **`hdom` and `hfwd` for the reference chart at the original time `s`** (bounded outer pocket): on the reference
window, the domain events and the forward map of the relative chart at the random capacity `visitCap s` are
measurable for the reference record `σ(walls) ∨ 𝓕_s`. -/
theorem measurable_fwd_visitRef_outer [IsProbabilityMeasure P] (hX : IsMeasurableKilledDriving W' VL VR ζ')
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    (hc : ∀ ω ∈ A, (c ω).IsConformal) (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (s : ℝ≥0) (z : ℂ) :
    MeasurableSet[refInfo P hX R L s] (refWindow A R L r η s ∩
        {ω | z ∈ (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom}) ∧
      Measurable[refInfo P hX R L s] ((refWindow A R L r η s ∩
        {ω | z ∈ (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom}).indicator
          fun ω => (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).1 z) := by
  classical
  have hRm' := measurable_right_wallsSigma (P := P) hRc hLc
  have hLm' := measurable_left_wallsSigma (P := P) hRc hLc
  have h𝓦 : wallsSigma P R L ≤ mΩ := wallsSigma_le hRm hLm
  have h𝓦s : wallsSigma P R L ≤ refInfo P hX R L s := wallsSigma_le_refInfo hX R L s
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  obtain ⟨hγm, hCm, hψm', hcfwd, hKm⟩ := r7_fixed_inputs_outer hRc hLc hRm hLm hGm hG hA hAG hcfg hψ hψm hηm hc
    hcdom hceq
  have hspec := refWindow_spec_outer (ζ' := ζ') hcfg hζA hψ hc hcdom hceq s
  by_cases hs : s = 0
  · -- the zero reference: the relative chart at capacity `0`, measurable for the walls
    subst hs
    have hrel : ∀ ω ∈ A, relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω ((0 : ℝ≥0) : ℝ)).toNNReal ω =
        relChart c (travAll R L r η ψ) 0 ω := fun ω hω => by
      rw [NNReal.coe_zero, R5Out.visitCap_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω),
        Real.toNNReal_zero]
    have hfix := measurable_indicator_fwd_relChart_fixed hγ hc hcfwd 0 (hKm 0) z
    rw [PocketStopSide.locPrefixSigma_zero_of_driven hA hγ] at hfix
    have eS : refWindow A R L r η 0 ∩
        {ω | z ∈ (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω ((0 : ℝ≥0) : ℝ)).toNNReal ω).dom} =
        {ω | ω ∈ A ∧ ((0 : ℝ≥0) : ℝ≥0∞) < capLife (travAll R L r η ψ ω)} ∩
          {ω | z ∈ (relChart c (travAll R L r η ψ) 0 ω).dom} := by
      ext ω
      simp only [refWindow_zero, mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨hω, hz⟩
        refine ⟨⟨hω, ?_⟩, by rwa [hrel ω hω] at hz⟩
        rw [ENNReal.coe_zero]
        exact PocketPhaseMeans.capLife_pos (hγ ω hω)
      · rintro ⟨⟨hω, -⟩, hz⟩
        exact ⟨hω, by rwa [hrel ω hω]⟩
    rw [eS, indicator_congr (g := fun ω => (relChart c (travAll R L r η ψ) 0 ω).1 z)
      fun ω hω => by simp only [hrel ω hω.1.1]]
    exact ⟨h𝓦s _ hfix.1, hfix.2.mono h𝓦s le_rfl⟩
  -- a visit reference: the random capacity `visitCap s`
  have hG₀ := measurableSet_refWindow_outer (P := P) hX hRc hLc hGm hG hA hAG hcfg hζA s
  have hG₀A : refWindow A R L r η s ⊆ A := fun ω hω => hω.1
  have hWad : AdaptedBefore (drivingFiltration P hX) ζ' W' :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
  have htrans : ∀ (q : ℝ≥0) (M : Set Ω),
      MeasurableSet[locPrefixSigma (wallsSigma P R L) A (travAll R L r η ψ) q] M →
      MeasurableSet[refInfo P hX R L s]
        (refWindow A R L r η s ∩ {ω | q ≤ (visitCap R L r η ψ ω s).toNNReal} ∩ M) := by
    intro q M hM
    have hGpre := PocketStopMarked.Outer.isMarkedStop_stopTimeM (wallsSigma_le_drivingFiltration hX R L) hWad hRm'
      hLm' hGm hG hA hAG hcfg hζA hψ hψm q
    have h1 := measurableSet_le_inter_of_isMarkedStop hGpre s hM
    have e : refWindow A R L r η s ∩ {ω | q ≤ (visitCap R L r η ψ ω s).toNNReal} ∩ M =
        refWindow A R L r η s ∩ ({ω | stopTimeM A R L r η ψ q ω ≤ (s : ℝ≥0∞)} ∩ M) := by
      rw [refWindow_of_ne hs]
      ext ω
      simp only [mem_inter_iff, mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hω, hq⟩, hMω⟩
        exact ⟨hω, (stopTimeM_le_iff_visitCap_outer hcfg hψ hω.1 hω.2 q).2 hq, hMω⟩
      · rintro ⟨hω, hq, hMω⟩
        exact ⟨⟨hω, (stopTimeM_le_iff_visitCap_outer hcfg hψ hω.1 hω.2 q).1 hq⟩, hMω⟩
    rw [e]
    exact hG₀.inter h1
  exact measurable_indicator_fwd_relChart_rand' h𝓦 hA hγ hγm (fun ω hω => (hψ ω hω).2.2.2.1) hCm hψm'
    (fun ω hω => ⟨hc ω hω, hcdom ω hω, hceq ω hω⟩) hcfwd hKm h𝓦s hG₀ hG₀A (fun ω hω => (hspec ω hω).1) htrans z

end Fwd

/-! ### Clause 4 of `R5Out.R5ClausesCompOn` on the reference family (bounded outer pocket) -/

section Clause4

open Wire.Current.SideTest (rationalOriginalTime)

variable {Ω : Type*} {κ' : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a k c₀ : ℝ} {u₀ : ℂ → ℝ}
  {𝓕₀ : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **R.5's enlarged-stop increment law for the visit reference at the original time `s`** (bounded outer pocket;
clause 4 of `R5Out.R5ClausesCompOn`): `r7HasOldChartIncrementLawOn_outer` with the reference window, the reference
chart's facts (`refWindow_spec_outer`) and its domain events and forward map (`measurable_fwd_visitRef_outer`)
discharged, on every event `M` on which `ω` is in the test, `q` is live, `s` is a visit or `0`, and the capacity
reached at `s` is at most `q`. -/
theorem r7HasOldChartIncrementLawOn_visit_outer
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (q s : ℝ≥0) {M : Set Ω}
    (hM : ∀ ω ∈ M, ω ∈ A ∧ (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) ∧
      (η ω s ∈ cfPocket (R ω) (L ω) r ∨ s = 0) ∧ (visitCap R L r η ψ ω s).toNNReal ≤ q) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A (travAll R L r η ψ)
        (fun ω => cfPocket (R ω) (L ω) r) (regHull W' ζ' s) 0) (centredField h'' u₀') P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) (centredField h'' u₀') P g →
        HasOldChartIncrementLawOn P M (fun ω => relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
          (relChart c (travAll R L r η ψ) q) gOld g := by
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) := fun ω hω => ((hcfg ω hω).props (hψ ω hω)).1
  have hspec := refWindow_spec_outer (ζ' := ζ') hcfg hζA hψ hc hcdom hceq s
  have hle : refInfo P hX R L s ≤ germSigma (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r)
      (regHull W' ζ' s) 0) (centredField h'' u₀') ⊔ locPrefixSigma (refInfo P hX R L s) A (travAll R L r η ψ) 0 :=
    le_sup_left.trans le_sup_right
  have hmeas := measurable_fwd_visitRef_outer hX hRc hLc hRm hLm hGm hG hA hAG hcfg hζA hψ hψm hηm hc hcdom hceq s
  -- the capacity reached at `s` is at most `q` whenever `s ≤ T⁰(q)`
  have hQq : ∀ ω ∈ refWindow A R L r η s, (s : ℝ≥0∞) ≤ stopTimeM A R L r η ψ q ω → ω ∈ A →
      (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω) → (visitCap R L r η ψ ω s).toNNReal ≤ q := by
    rintro ω ⟨-, hv | hz⟩ hsT hω hl
    · exact visitCap_le_of_le_stopTimeM_outer hcfg hψ hω hv hl hsT
    · subst hz
      rw [NNReal.coe_zero, R5Out.visitCap_zero (W := fun ω (s : ℝ) => W' s.toNNReal ω) (hcfg ω hω) (hψ ω hω),
        Real.toNNReal_zero]
      exact zero_le
  refine r7HasOldChartIncrementLawOn_outer hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hcfg hζA hψ hψm hc hcdom hceq q s (G' := refWindow A R L r η s)
    (hle _ (measurableSet_refWindow_outer hX hRc hLc hGm hG hA hAG hcfg hζA s))
    (old := fun ω => relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
    (fun ω hω => (hspec ω hω).2.1) (fun z => hle _ (hmeas z).1) (fun z => (hmeas z).2.mono hle le_rfl)
    (fun ω hω => (hspec ω hω).2.2.1) (fun ω hω => (hspec ω hω).2.2.2)
    (fun ω hω hsT hωA hl => PocketStopSide.relChart_dom_antitone (hc ω hωA) (hγ ω hωA) hl
      (hQq ω hω hsT hωA hl))
    (fun ω hω => ⟨(hM ω hω).1, (hM ω hω).2.2.1⟩) (fun ω hω => ?_) (fun ω hω => ⟨(hM ω hω).1, (hM ω hω).2.1⟩)
  obtain ⟨hω, hq, hv | hz, hQ⟩ := hM ω hω
  · exact le_stopTimeM_of_visitCap_le_outer hcfg hψ hω hv hq hQ
  · rw [hz, ENNReal.coe_zero]
    exact zero_le

/-- **R.5's enlarged-stop increment law for R5-REFCHART's `i`-th reference** (bounded outer pocket; clause 4 of
`R5Out.R5ClausesCompOn` with `M = R5Ref.refEvent`, `old = R5Ref.refChart`, `F = refHull`):
`r7HasOldChartIncrementLawOn_visit_outer` at `s = rationalOriginalTime i`. -/
theorem r7HasOldChartIncrementLawOn_ref_outer
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (q : ℝ≥0) (i : ℕ) :
    ∀ gOld : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A (travAll R L r η ψ)
        (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0) (centredField h'' u₀') P gOld →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) (centredField h'' u₀') P g →
        HasOldChartIncrementLawOn P
          (R5Ref.refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i)
          (R5Ref.refChart c R L r η ψ i) (relChart c (travAll R L r η ψ) q) gOld g :=
  r7HasOldChartIncrementLawOn_visit_outer hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL hlocR
      hlocL hGm hG hA hAG hcfg hζA hψ hψm hηm hc hcdom hceq q (rationalOriginalTime i)
    fun _ hω => ⟨hω.1, hω.2.1, hω.2.2.1, hω.2.2.2.1⟩

/-- **Clause 4 of `R5Out.R5ClausesCompOn` for R5-REFCHART's reference family** (bounded outer pocket), in the
clause's own form: for local-set means of every reference and of the active complement, the conditioned increment
law on every pair event `R5Ref.refEvent … q i` with the reference chart `R5Ref.refChart … i` (whose domain is the
component of the reference complement incident to the pocket target). -/
theorem r5ClausesCompOn_clause4_ref_outer
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c₀ (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ' xL xR ρL ρR P 𝓕₀ W' VL VR B ζ' h'') (hκ' : 0 < κ')
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ' ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {G A : Set Ω}
    (hGm : MeasurableSet[wallsSigma P R L] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    (hcfg : ∀ ω ∈ A, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hζA : ∀ ω ∈ A, ζ' ω = ⊤) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hψm : @IsPointMeasurable Ω (wallsSigma P R L) R L r G ψ) (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u)
    {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (hceq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r)) (q : ℝ≥0) :
    ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
      (∀ i, IsLocalSetMean (liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0)
        (centredField h'' u₀') P (gB i)) →
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (activeCompl A (travAll R L r η ψ) c q) (centredField h'' u₀') P g →
        ∀ i, HasOldChartIncrementLawOn P
          (R5Ref.refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i)
          (R5Ref.refChart c R L r η ψ i) (relChart c (travAll R L r η ψ) q) (gB i) g :=
  fun gB hgB g hg i => r7HasOldChartIncrementLawOn_ref_outer hT' hTr hu₀ hh hC hκ' hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm
      hdetR hdetL hlocR hlocL hGm hG hA hAG hcfg hζA hψ hψm hηm hc hcdom hceq q i (gB i) (hgB i) g hg

end Clause4

end InteractingSLE.Sec7.R5OLaw
