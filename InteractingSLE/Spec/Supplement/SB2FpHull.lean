/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QtUpper

/-!
# The hull law of the upper past with its word exposed

Worker PROVE-SB2-F3LAW (round 4). `Qt.exists_hullLaw` hides how its word is built. For the base of D34's left
heights (`hL`) and for D55's root-word identity, the word has to be read off: it is the stage witness word `β₀`
(`IsStageWitness` in the run chart) shifted by `-s`, where `s` is the shift of a normalized hull model of the run
chart whose hull is `K₀` on `G₁`.

* **`exists_hullLawW`** — `Qt.exists_hullLaw` plus this description of the word (same proof).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fp

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Mf Qt

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **`Qt.exists_hullLaw` with its construction exposed**: the word is the stage witness word shifted by the run
chart's shift `s`, which is the shift of a normalized hull model of the run chart with hull `K₀` on `G₁`. -/
theorem exists_hullLawW (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    ∃ (K₀ : Ω → Set ℂ) (G₁ : Set Ω) (K : Ω → Set ℂ) (Y : Ω → DistOn upperHalfPlaneOpens)
      (β : Ω → BoundaryWord) (M : ℝ),
      Measurable[pastSigma κ b jumps spec E k, hittingSigma] K₀ ∧ (∀ ω, K₀ ω ⊆ H ∧ IsOpen (H \ K₀ ω)) ∧
      (∀ᵐ ω ∂P, K₀ ω = fillVer (WalkLaw.stageSet κ b jumps spec E k) ω) ∧
      MeasurableSet[mΩ ⊓ aeSigma (pastSigma κ b jumps spec E k) P] G₁ ∧
      G₁ ⊆ {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} ∧
      (∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none → ω ∈ G₁) ∧
      @IsDyadicHitMeasurable Ω (mΩ ⊓ aeSigma (pastSigma κ b jumps spec E k) P) K ∧
      (∀ ω, IsCompact (K ω)) ∧ (∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) ∧
      (∀ ω ∈ G₁, fillH (K ω) = K₀ ω ∧ K₀ ω = fillH (SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k) ∧
        IsHPHull (K₀ ω)) ∧
      Measurable Y ∧ (∀ ω, IsChartTransport (Mo.hullChart (fillH (K ω)) 0) 1 0 (chiC κ) (h ω) (Y ω)) ∧
      Measurable[pastSigma κ b jumps spec E k] β ∧ (∀ ω, (β ω).IsSorted) ∧ 0 ≤ M ∧
      (∀ ω, ∀ y ∉ (β ω).jumps, |(β ω).fn y| ≤ M) ∧
      (∀ᵐ ω₀ ∂P, (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none →
        IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) Y (β ω₀).fn (β ω₀).jumps) ∧
      ∃ (s : Ω → ℝ) (β₀ : Ω → BoundaryWord) (Y₀ : Ω → DistOn upperHalfPlaneOpens),
        Measurable[pastSigma κ b jumps spec E k] s ∧ IsStageWitness κ b jumps P h spec E k β₀ Y₀ ∧
        (∀ ω, β ω = BoundaryWord.shiftW (-(s ω)) (β₀ ω)) ∧
        ∀ ω ∈ G₁, ∃ Mh : WalkIntCanon.HullModel (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1,
          Mh.hull = K₀ ω ∧ WalkIntCanon.IsNormalized (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 ∧
          s ω = Mh.shift := by
  classical
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hm : pastSigma κ b jumps spec E k ≤ mΩ := hS.2.1 k
  have hmC : pastSigma κ b jumps spec E k ≤ mΩ ⊓ aeSigma (pastSigma κ b jumps spec E k) P :=
    le_inf hm fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
  have hR : StagedPiecesRegular κ b jumps P spec E := stagedPiecesRegular_of_regular h13 hκ hb hS hreg
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the stage witness
  obtain ⟨β₀, Y₀, M₀, hW, hM0, hs0, hb0⟩ := exists_stageWitness_sorted_bounded hκ hb hh hS hreg k
  have hL : MeasurableSet[pastSigma κ b jumps spec E k] L := Lv.measurableSet_launch_pastSigma hb hS.1 hreg k
  have hc : S3.RetainedChartData (pastSigma κ b jumps spec E k) (WalkInf.verChart κ b jumps spec E k) :=
    S3.retainedChartData_verChart hb hS.1 hreg k
  -- the shift, read at `i∞`
  obtain ⟨s, hsdef⟩ : ∃ s : Ω → ℝ, s = fun ω => limsup (fun n : ℕ => ((n : ℂ) * Complex.I -
      ({ω | (n : ℂ) * Complex.I ∈ (WalkInf.verChart κ b jumps spec E k ω).dom}.indicator
        (fun ω => (WalkInf.verChart κ b jumps spec E k ω).1 ((n : ℂ) * Complex.I)) ω)).re) atTop := ⟨_, rfl⟩
  have hsm : Measurable[pastSigma κ b jumps spec E k] s := by
    rw [hsdef]
    let _ : MeasurableSpace Ω := pastSigma κ b jumps spec E k
    exact Measurable.limsup fun n => Complex.measurable_re.comp (measurable_const.sub (hc.forward _))
  -- a version of the explored set and its fill
  obtain ⟨hA, ho, hlocS⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hS hreg hu₀ k
  obtain ⟨Bu, hBum, hBuc, hBuae, -⟩ := Lcd.exists_lineVersion (P := P) ⟨_, hm⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ho hA hlocS
  set K₀ : Ω → Set ℂ := fillVer Bu with hK₀def
  have hK₀m : Measurable[pastSigma κ b jumps spec E k, hittingSigma] K₀ := measurable_fillVer (fun ω => (hBuc ω).1) hBum
  have hK₀c : ∀ ω, K₀ ω ⊆ H ∧ IsOpen (H \ K₀ ω) := fun ω =>
    ⟨fillVer_subset_H (fun ω => (hBuc ω).1) ω, isOpen_H_diff_fillVer (fun ω => (hBuc ω).2) ω⟩
  have hK₀ae : ∀ᵐ ω ∂P, K₀ ω = fillVer (WalkLaw.stageSet κ b jumps spec E k) ω := by
    filter_upwards [hBuae] with ω he
    exact Qr.fillVer_congr he
  -- the good samples
  set Gd : Ω → Prop := fun ω => ω ∈ L →
    (∀ (j : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)) ∧
    Bu ω = WalkLaw.stageSet κ b jumps spec E k ω ∧
    WalkInf.verChart κ b jumps spec E k ω = Cond.runChart κ b jumps spec E k ω ∧
    ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.IsConformal ∧
      ContinuousOn (fun w => (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.2
        ((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.2.1 w)) H ∧
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (chiC κ) (h ω) (Y₀ ω))
    with hGddef
  have hGd : ∀ᵐ ω ∂P, Gd ω := by
    filter_upwards [hR.ae_pieceRegular, hBuae, Lv.ae_verChart_eq_runChart hR hreg k, hW.2.2.1] with ω h1 h2 h3 h4 hl
    exact ⟨fun j c θ hlj => h1 j c θ hlj, h2, h3, h4 hl⟩
  set N : Set Ω := toMeasurable P {ω | ¬ Gd ω} with hNdef
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hGd
  set G₁ : Set Ω := L \ N with hG₁def
  have hG₁sub : G₁ ⊆ L := sdiff_subset
  have hG₁good : ∀ ω ∈ G₁, Gd ω := fun ω hω => by
    by_contra hn
    exact hω.2 (subset_toMeasurable P _ hn)
  have hG₁ae : ∀ᵐ ω ∂P, ω ∈ L → ω ∈ G₁ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω hL' using ⟨hL', hω⟩
  have hG₁C : MeasurableSet[mΩ ⊓ aeSigma (pastSigma κ b jumps spec E k) P] G₁ := by
    rw [MeasurableSpace.measurableSet_inf]
    refine ⟨(hm _ hL).diff (measurableSet_toMeasurable P _), L, hL, ?_⟩
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    exact propext ⟨fun h' => h'.1, fun h' => ⟨h', hω⟩⟩
  -- the geometry at a good sample
  have hgeo : ∀ ω ∈ G₁, ∃ Mh : WalkIntCanon.HullModel (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1,
      Mh.hull = K₀ ω ∧ K₀ ω = fillH (SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k) ∧
      WalkIntCanon.IsNormalized (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 ∧
      s ω = Mh.shift := by
    intro ω hω
    obtain ⟨hpr, hBe, hv, -⟩ := hG₁good ω hω (hG₁sub hω)
    obtain ⟨⟨c', θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 (hG₁sub hω)
    have hnd := WalkIntRunChron.not_done_of_launch spec (fun j => E j ω) hcθ
    obtain ⟨Mh, hMh⟩ := Lw.exists_hullModel_fill spec (fun j => E j ω) hpr k hnd
    have hcpt := Lx.isCompact_prefixPhysSet_run spec (fun j => E j ω) hpr k hnd
    have hSP : WalkLaw.stageSet κ b jumps spec E k ω = SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k ∩ H := by
      ext z
      constructor
      · intro hz
        exact ⟨Or.inl (Or.inr hz.1), hz.2⟩
      · intro hz
        exact WalkLeaf.mem_stageSet_of_mem_prefixPhysSet spec E k ω hz.1 hz.2
    have hbd : Bornology.IsBounded (Bu ω) := by
      rw [hBe, hSP]
      exact hcpt.isBounded.subset inter_subset_left
    have hK₀e : K₀ ω = fillH (SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k) := by
      rw [hK₀def, fillVer_of_bounded hbd, hBe, hSP, Mo.fillH_closure_inter_H]
    refine ⟨Mh, hMh.trans hK₀e.symm, hK₀e,
      WalkIntCanon.isNormalized_runChart spec (fun j => E j ω) k fun j _ c θ hlj => hpr j c θ hlj, ?_⟩
    rw [hsdef]
    obtain ⟨ht, hev⟩ := Qr.tendsto_re_sub_fwd Mh
    refine Tendsto.limsup_eq (ht.congr' ?_)
    filter_upwards [hev] with n hn
    have hmem : (n : ℂ) * Complex.I ∈ (WalkInf.verChart κ b jumps spec E k ω).dom := by
      rw [hv]
      exact hn
    have hind : ({ω | (n : ℂ) * Complex.I ∈ (WalkInf.verChart κ b jumps spec E k ω).dom}.indicator
        (fun ω => (WalkInf.verChart κ b jumps spec E k ω).1 ((n : ℂ) * Complex.I)) ω) =
        (WalkInf.verChart κ b jumps spec E k ω).1 ((n : ℂ) * Complex.I) := Set.indicator_of_mem hmem _
    rw [hind, hv]
    rfl
  have hHP : ∀ ω ∈ G₁, IsHPHull (K₀ ω) := fun ω hω => by
    obtain ⟨Mh, hMh, -⟩ := hgeo ω hω
    exact hMh ▸ Mh.isHull
  -- the retained hull
  set K : Ω → Set ℂ := Mo.retHull K₀ G₁ with hKdef
  have hKm : @IsDyadicHitMeasurable Ω (mΩ ⊓ aeSigma (pastSigma κ b jumps spec E k) P) K :=
    @Mo.isDyadicHitMeasurable_retHull Ω K₀ G₁ (mΩ ⊓ aeSigma (pastSigma κ b jumps spec E k) P) (hK₀m.mono hmC le_rfl)
      (fun ω => (hK₀c ω).1) hG₁C
  have hKc : ∀ ω, IsCompact (K ω) := Mo.isCompact_retHull fun ω hω => (hHP ω hω).2.1
  have hXc : ∀ ω ∈ G₁, K₀ ω = closure (K₀ ω) ∩ H ∧ IsClosed (closure (K₀ ω)) ∧
      (∀ z ∈ closure (K₀ ω), 0 ≤ z.im) ∧ IsPreconnected (closure (K₀ ω) ∪ Restart.lowerHalf) := by
    intro ω hω
    refine ⟨(Sec7.SideHeight.closure_inter_H_eq (hK₀c ω).1 (hK₀c ω).2).symm, isClosed_closure, ?_,
      Sec5.Aux61Restart.isPreconnected_closure_union_lowerHalf (hHP ω hω)⟩
    have hcl : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
    intro z hz
    exact (hcl.closure_subset_iff.2 fun w hw => show 0 ≤ w.im from le_of_lt ((hK₀c ω).1 hw)) hz
  have hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf) := Mo.isPreconnected_retHull_union hXc
  have hfK : ∀ ω ∈ G₁, fillH (K ω) = K₀ ω := fun ω hω => by
    rw [hKdef, Mo.fillH_retHull_of_mem (X := fun ω => closure (K₀ ω)) hω (hXc ω hω).1]
    exact Sec5.Aux61Restart.fillH_closure_of_isHPHull (hHP ω hω)
  -- the chart field
  have hKmΩ : @IsDyadicHitMeasurable Ω mΩ K := fun n j =>
    (inf_le_left : mΩ ⊓ aeSigma (pastSigma κ b jumps spec E k) P ≤ mΩ) _ (hKm n j)
  obtain ⟨hconf, hliftc, -, hdomm, hfwdm, hliftm⟩ :=
    @Mt.hullChart_k2Inputs Ω mΩ K (fun _ => 0) hKmΩ hKc hKp measurable_const
  set Y : Ω → DistOn upperHalfPlaneOpens := fun ω =>
    Chart.chartTransport (Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω) 1 0 (chiC κ) (h ω) with hYdef
  have hYm : Measurable Y :=
    Chart.measurable_chartTransport_random' (Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp) hdomm hfwdm hliftm
      hliftc hh.1 1 0 (chiC κ)
  have hYt : ∀ ω, IsChartTransport (Mo.hullChart (fillH (K ω)) 0) 1 0 (chiC κ) (h ω) (Y ω) := fun ω =>
    Chart.isChartTransport_chartTransport (Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω)
      (Chart.locallyIntegrableOn_of_continuousOn
        (Mu.continuousOn_lift_inv_hullChart (Mo.isHPHull_fillH hKc hKp ω) 0)) 1 0 (chiC κ) (h ω)
  -- on good samples the chart field is the shifted stage field
  have hYeq : ∀ ω ∈ G₁, Y ω = Exist.flowField (-(s ω)) 0 (Y₀ ω) := by
    intro ω hω
    obtain ⟨Mh, hMh, -, hN, hse⟩ := hgeo ω hω
    obtain ⟨-, -, -, hcc, hℓ, htr⟩ := hG₁good ω hω (hG₁sub hω)
    have h1 := isChartTransport_hullChart_of_hullModel hcc hN Mh hℓ htr
    rw [hMh, ← hfK ω hω, ← hse] at h1
    exact (hYt ω).unique (Mu.isConformal_canon (fun _ => (0 : ℝ)) hKc hKp ω) h1
  -- the word
  set β : Ω → BoundaryWord := fun ω => BoundaryWord.shiftW (-(s ω)) (β₀ ω) with hβdef
  have hβm : Measurable[pastSigma κ b jumps spec E k] β := BoundaryWord.measurable_shiftW.comp (hsm.neg.prodMk hW.1)
  refine ⟨K₀, G₁, K, Y, β, M₀, hK₀m, hK₀c, hK₀ae, hG₁C, hG₁sub, hG₁ae, hKm, hKc, hKp,
    fun ω hω => ⟨hfK ω hω, (hgeo ω hω).choose_spec.2.1, hHP ω hω⟩, hYm, hYt, hβm,
    fun ω => BoundaryWord.isSorted_shiftW (hs0 ω) _, hM0, fun ω => Lv.abs_shiftW_fn_le (hb0 ω) _, ?_,
    s, β₀, Y₀, hsm, hW, fun ω => rfl, fun ω hω => by
      obtain ⟨Mh, h1, -, h3, h4⟩ := hgeo ω hω
      exact ⟨Mh, h1, h3, h4⟩⟩
  -- the conditional law
  filter_upwards [hW.2.2.2, KernelTower.ae_ae_condExpKernel_of_ae hm hG₁ae,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) hm hL,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) hm hsm] with ω₀ hg hG hLk hse hL₀
  have hgff := isGFFWithBoundaryData_shiftW (-(s ω₀)) (hg hL₀)
  refine isGFFWithBoundaryData_congr_ae hgff hYm ?_
  filter_upwards [hG, hLk hL₀, hse] with ω hGω hLω hsω
  rw [hYeq ω (hGω hLω), hsω]

end InteractingSLE.Theorem14.SB.Fp
