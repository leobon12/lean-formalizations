/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopSafeFstLine

/-!
# Item 5 of `AStopSourceInputs` for the A-stopped first continuation: the safe laws (S) and (L)

Packet PROVE-T15-ASTOP-SAFE (Theorem 1.5's leaf 3). For the processes of PROVE-T15-ASTOP-PROC at the seed `τ` (the
chart path `AStopProc.fstChart d τ η₁' ζ₁` in `d`'s chart recentred at `τ`, the capacity-time filtration `aFilt` of
`fstPhysFiltration` (lines `(u + t, r)`), the supported capacity lifetime, any continuous driver from `0` generating
`aPath` on `M`):

* **`hasSafe_aStop_fst`**: K2's (S) for the typed geometric force coordinates of the seeded stop word `shiftW τ β₀`,
  and K2's (L), for the field `flowField 0 (θ₁χ) (flowField τ 0 (chartField))` of the given retained data `d`
  (the source statement `RetOrdAStopSourceFstSeedStatement`'s field), from RETPLUMB's
  `hasSafeLaw_of_retLines_indicator` / `hasSafeMembers_of_lineLocal_indicator` with the recentred stop chart, the
  exchanged later charts (PROVE-T15-ORDDET6), the line kernels and filled lines in the filled-union complement
  (`AStopSafeFill`) and the later-line facts (`AStopSafeFstLine`).

Uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv logDerivFwd chiC zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.RLC.AStopSafe

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F MartChar.RealFlow AStopProc OrdGap OrdSwap
open DomainMarkov DomainMarkov.Aux79 DomainMarkov.K2
open Exist.StagedLaw.BoundaryWord

universe u

section Fst

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Item 5 of `AStopSourceInputs` for the A-stopped first continuation at its seed**: K2's (S) and (L) for the
processes of PROVE-T15-ASTOP-PROC, with the typed geometric force coordinates of the seeded stop word and the
translated shifted chart field of `d`, on a good stop-line event `M` of ordinary pairs of one force type. -/
theorem hasSafe_aStop_fst (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β₀ : Ω → BoundaryWord}
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β₀)
    (hsort : ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β₀ ω).IsSorted)
    {τ : Ω → ℝ} (hτm : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] τ)
    {η₁' : Ω → ℝ≥0 → ℂ} (hm₁ : ∀ t, Measurable fun ω => η₁' ω t)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMg : ∀ ω ∈ M, IsFstGood d η₁ η₂ η₁' ζ₁ ζ₂ x₁ τ ω)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    (a : ForceWordType) (htype : ∀ ω ∈ M, shiftW (τ ω) (β₀ ω) ∈ FCDet.typeSet κ θ₁ a.nL a.nR a.rhoL a.rhoR)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun q => W q ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω) (aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω)
      (aPath (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁) ω))
    (hQa : ∀ t, Measurable[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r t]
      (M.indicator (aClock (fstChart d τ η₁' ζ₁) t))) :
    HasSafeLaw κ a.rhoL a.rhoR P (aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (fstChart d τ η₁' ζ₁) hQa) M
      (M.indicator (aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁))) W
      (PocketTraversal.geomLW W fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (τ ω) (β₀ ω)))
      (PocketTraversal.geomRW W fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (τ ω) (β₀ ω)))
      (fun ω => Exist.flowField 0 (θ₁ * chiC κ) (Exist.flowField (τ ω) 0 (hd.chartField κ h ω))) ∧
    HasSafeMembers P (aFilt (fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (fstChart d τ η₁' ζ₁) hQa) M
      (M.indicator (aLife (fstChart d τ η₁' ζ₁) (fstLifeP d η₁' ζ₁))) W
      (fun ω => Exist.flowField 0 (θ₁ * chiC κ) (Exist.flowField (τ ω) 0 (hd.chartField κ h ω))) := by
  classical
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  obtain ⟨η₂'', hm₂'', ha₂''⟩ := exists_measurable_version_of_isFlowLine hη₂
  obtain ⟨G, hG⟩ := exists_retG_family_with_live hκ hκ4 hη₁ hη₂ hm₁ hm₂'' ha₁ ha₂'' d.u
  obtain ⟨G', hG'⟩ := exists_retG_family_with_live hκ hκ4 hη₂ hη₁ hm₂'' hm₁ ha₂'' ha₁ d.r
  have hb₀ : (retFam G η₁' η₂'' d.u d.r).IsMeasGood := (hG d.r).1
  have hdG' : ∀ u', (retFam G' η₂'' η₁' d.r u').IsMeasGood := fun u' => (hG' u').1
  have hagb : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ G d.r ∧
      (∀ s ≤ d.u, η₁' ω s = η₁ ω s) ∧ ∀ t ≤ d.r, η₂'' ω t = η₂ ω t := by
    filter_upwards [(hG d.r).2.2.2, ha₁, ha₂''] with ω hGω e₁ e₂ hu hr
    exact ⟨hGω hu hr, fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le),
      fun s hs => e₂ s ((ENNReal.coe_le_coe.2 hs).trans hr.le)⟩
  have hagF' : ∀ u' : ℝ≥0, ∀ᵐ ω ∂P, (d.r : ℝ≥0∞) < ζ₂ ω → (u' : ℝ≥0∞) < ζ₁ ω → ω ∈ G' u' ∧
      (∀ s ≤ d.r, η₂'' ω s = η₂ ω s) ∧ ∀ t ≤ u', η₁' ω t = η₁ ω t := by
    intro u'
    filter_upwards [(hG' u').2.2.2, ha₁, ha₂''] with ω hGω e₁ e₂ hr hu
    exact ⟨hGω hr hu, fun s hs => e₂ s ((ENNReal.coe_le_coe.2 hs).trans hr.le),
      fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le)⟩
  -- the stop chart of the family is `d`'s chart at ordinary pairs
  have hch : ∀ᵐ ω ∂P, ω ∈ {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} →
      (retFam G η₁' η₂'' d.u d.r).chart ω = d.chart ω := by
    filter_upwards [hag, hagb] with ω hagω hF hord
    obtain ⟨hG₀, a₁, a₂⟩ := hagω hord.1 hord.2.1
    obtain ⟨hG0, f₁, f₂⟩ := hF hord.1 hord.2.1
    exact (RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁') (η₂' := η₂'') hG₀ hG0
      (fun s hs => (f₁ s hs).trans (a₁ s hs).symm) (fun s hs => (f₂ s hs).trans (a₂ s hs).symm)).2.2
  have hm₀ := isRetMeanIdentOn_of_chart_eq hd hb₀ rfl rfl hch hmean
  -- the line data, the line kernels and the line words
  choose d' hd' hsw hag' using fun t : ℝ≥0 =>
    exists_isSwap hκ hκ4 hη₂ hη₁ (hdG' (d.u + t)) (hagF' (d.u + t))
  choose ηc₁ ηc₂ g hc₁ hc₂ hmc₁ hmc₂ hagc₁ hagc₂ hg hker using fun t : ℝ≥0 =>
    exists_kernel_fill hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ (d.u + t) d.r
  choose β₁ β₂ hm₁w hw₁ hm₂w hw₂ using fun t : ℝ≥0 =>
    exists_fstLateWords hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ (hd' t) (hdG' (d.u + t)) (hag' t) (hagF' (d.u + t))
  set βL : ℝ≥0 → Ω → BoundaryWord := fun t => if t = 0 then fun ω => shiftW (τ ω) (β₀ ω)
    else fstLateWord η₁ η₂ ζ₁ ζ₂ (d' t) (β₁ t) (β₂ t) with hβL
  set xL : Ω → Fin a.nL → ℝ := fun ω => FCDet.typeXL κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (τ ω) (β₀ ω))
    with hxL
  set xR : Ω → Fin a.nR → ℝ := fun ω => FCDet.typeXR κ θ₁ a.nL a.nR a.rhoL a.rhoR (shiftW (τ ω) (β₀ ω))
    with hxR
  have htype' : ∀ ω ∈ M, FCDet.IsFlowType κ θ₁ (shiftW (τ ω) (β₀ ω)) (xL ω) (xR ω) a.rhoL a.rhoR :=
    fun ω hω => FCDet.isFlowType_of_mem_typeSet (htype ω hω)
  set Γ := fstChart d τ η₁' ζ₁ with hΓ
  set L := fstLifeP d η₁' ζ₁ with hL
  -- the line facts at every line
  have hline_all : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ M → (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω →
      ((((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧
        ω ∈ (retFam G' η₂'' η₁' d.r (d.u + t)).E ∧
        (retFam G' η₂'' η₁' d.r (d.u + t)).D ω = H \ fillH (η₁ ω '' Icc 0 (d.u + t) ∪ η₂ ω '' Icc 0 d.r))) ∧
      (βL t ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hdG' (d.u + t)).isConformal_chart ω) 1 0 (chiC κ)
          (g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (βL t ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G' η₂'' η₁' d.r (d.u + t)).chart ω).2.1 w =
        (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω) w)) ∧
      (∀ w ∈ H, ((retFam G' η₂'' η₁' d.r (d.u + t)).chart ω).2.2
          (((retFam G' η₂'' η₁' d.r (d.u + t)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω) w)).im +
          (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.2
            ((((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1
              (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ a.rhoL a.rhoR
          (fun i => PocketTraversal.geomLW W xL i (aClock Γ t ω) ω - W (aClock Γ t ω) ω)
          (fun j => PocketTraversal.geomRW W xR j (aClock Γ t ω) ω - W (aClock Γ t ω) ω) y =
          (βL t ω).fn y + θ₁ * chiC κ := by
    intro t
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
    · subst h0
      have hβ0 : βL 0 = fun ω => shiftW (τ ω) (β₀ ω) := by rw [hβL]; simp
      rw [hβ0]
      filter_upwards [ae_aLine_fst_zero hκ hag hb₀ hagb hdG' hagF' hm₀ hsort hMg hMord hWc hW0 htype' (hc₁ 0)
        (hc₂ 0) (hmc₁ 0) (hmc₂ 0) (hagc₁ 0) (hagc₂ 0) (hg 0)] with ω hω hωM _
      exact hω hωM
    · have hβt : βL t = fstLateWord η₁ η₂ ζ₁ ζ₂ (d' t) (β₁ t) (β₂ t) := by rw [hβL]; simp [hpos.ne']
      rw [hβt]
      have hs' := hsw t
      exact ae_aLine_fst_pos hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ hd hag hb₀ hagb hdG' hagF' hm₀ hsort hMg hMord
        hWc hW0 hgen htype' hpos (hd' t) (hag' t) ⟨hs'.η₂_eq.symm, hs'.η₁_eq.symm, hs'.r_eq.symm, hs'.u_eq.symm⟩
        hs'.η₁_eq hs'.η₂_eq hs'.u_eq hs'.r_eq (hm₁w t) (hw₁ t) (hm₂w t) (hw₂ t) (hc₁ t) (hc₂ t) (hmc₁ t)
        (hmc₂ t) (hagc₁ t) (hagc₂ t) (hg t)
  -- observations and good samples
  have ho := fstObs_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hm₁ ha₁ hτm hM hMg
  have hgood : ∀ ω ∈ M, IsAGood Γ L ω := fun ω hω => (hMg ω hω).2.1.isAGood hd
  have hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ M → (q : ℝ≥0∞) < aLife Γ L ω → ∃ t, q ≤ aClock Γ t ω :=
    fun q => Eventually.of_forall fun ω hω hq => (hgood ω hω).exists_aClock_ge hq
  have hreg : ∀ᵐ ω ∂P, ω ∈ M → IsForceReg W (PocketTraversal.geomLW W xL) (PocketTraversal.geomRW W xR)
      (aLife Γ L) ω := Eventually.of_forall fun ω _ => FCDet.isForceReg_thr hW0 hWc xL xR _ ω
  -- the recentred stop chart is measurable at time `0`
  obtain ⟨α₁, α₂, hcα₁, hcα₂, hmα₁, hmα₂, h0α₁, h0α₂, haα₁, haα₂, -, -, -⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement
      hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR d.u d.r) d.u d.r
  obtain ⟨hdom, hfwd, hlift⟩ := chart_measurability_retSigma76 hb₀ hζ₁ hζ₂ (hG d.r).2.1 hagb
    hcα₁ hcα₂ hmα₁ hmα₂ h0α₁ h0α₂ haα₁ haα₂
  have h𝓖0 : fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0 = retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r := by
    rw [fstPhysFiltration_apply, add_zero]
  have hdom0 : ∀ z, MeasurableSet[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0]
      {ω | z ∈ (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).dom} := by
    intro z
    rw [h𝓖0]
    simp only [Chart.dom_recenter]
    exact hdom z
  have hfwd0 : ∀ z, Measurable[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0]
      ({ω | z ∈ (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).dom}.indicator
        fun ω => (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).1 z) := by
    intro z
    rw [h𝓖0]
    simp only [Chart.dom_recenter]
    have e : ({ω | z ∈ ((retFam G η₁' η₂'' d.u d.r).chart ω).dom}.indicator
        fun ω => (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).1 z) =
        ({ω | z ∈ ((retFam G η₁' η₂'' d.u d.r).chart ω).dom}.indicator
          fun ω => ((retFam G η₁' η₂'' d.u d.r).chart ω).1 z) -
        ({ω | z ∈ ((retFam G η₁' η₂'' d.u d.r).chart ω).dom}.indicator fun ω => ((τ ω : ℝ) : ℂ)) := by
      funext ω
      by_cases hω : ω ∈ {ω | z ∈ ((retFam G η₁' η₂'' d.u d.r).chart ω).dom}
      · simp only [Pi.sub_apply, indicator_of_mem hω, Chart.recenter]
      · simp only [Pi.sub_apply, indicator_of_notMem hω, sub_zero]
    rw [e]
    exact (hfwd z).sub ((Complex.measurable_ofReal.comp hτm).indicator (hdom z))
  have hlift0 : ∀ z, Measurable[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0]
      ({ω | z ∈ (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).dom}.indicator
        fun ω => (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.2 z) := by
    intro z
    rw [h𝓖0]
    simp only [Chart.dom_recenter]
    exact hlift z
  have hliftc : ∀ ω, ContinuousOn (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.2
      (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).dom := fun ω => by
    rw [Chart.dom_recenter]
    exact hb₀.continuousOn_lift_chart ω
  have hM0 : MeasurableSet[fstPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0] M := by
    rw [h𝓖0]; exact hM
  -- the later domains
  have hD : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ M → (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω →
      ((d.u + t : ℝ≥0) : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧
      H \ fillH (η₁ ω '' Icc 0 (d.u + t) ∪ η₂ ω '' Icc 0 d.r) =
        (((retFam G η₁' η₂'' d.u d.r).chart ω).recenter (τ ω)).2.1 ''
          (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω)) := by
    intro t
    filter_upwards [hline_all t] with ω hl hωM hlt
    obtain ⟨⟨hu, hr, -, hDt⟩, -, -, hIII, -⟩ := hl hωM hlt
    exact ⟨hu, hr, hDt.symm.trans (dom_eq_of_inv_eq (hdG' (d.u + t)) (hWc ω) (hW0 ω) _ hIII)⟩
  -- (S)
  have hS' := hasSafeLaw_of_retLines_indicator (P := P) (κ := κ) (ρL := a.rhoL) (ρR := a.rhoR)
    (VL := PocketTraversal.geomLW W xL) (VR := PocketTraversal.geomRW W xR) (ζ := aLife Γ L) hM0
    (fun ω => (hb₀.isConformal_chart ω).recenter (τ ω)) hdom0 hfwd0 hlift0 hliftc
    hh.1 (θ₁ * chiC κ) (continuous_aClock Γ) (monotone_aClock Γ) (aClock_zero Γ) hQa hreach hreg
    (fun ψ t => measurableSet_lineSafe_aStop ho hgood hgen ψ.hasCompactSupport.isCompact t)
    (fun t => retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ (ηc₁ t) (ηc₂ t) (d.u + t) d.r)
    (fun t => (le_sup_right : retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r ≤ _))
    (fun t => retLineSigma_le hh.1 u₀ η₁ η₂ hζ₁ hζ₂ (hc₁ t) (hc₂ t) (hmc₁ t) (hmc₂ t) (d.u + t) d.r)
    (fun t ω => g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)
    (fun t φ => by
      filter_upwards [hker t φ, hD t] with ω hk hDω hωM hlt hsupp
      obtain ⟨hu, hr, hDe⟩ := hDω hωM hlt
      rw [← hDe] at hsupp ⊢
      exact hk hu hr hsupp)
    hWc hW0 (fun t ω => (hdG' (d.u + t)).isConformal_chart ω) βL
    (fun t => by
      filter_upwards [hline_all t] with ω hl hωM hlt
      obtain ⟨-, hs, hmω, hIII, hlift, hdat⟩ := hl hωM hlt
      exact ⟨hs, hmω, hIII, hlift, hdat⟩)
  -- (L)
  choose B hBm hBc hloc hBD using fun t : ℝ≥0 =>
    exists_filled_line_fill hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ (d.u + t) d.r
  have hL' := hasSafeMembers_of_lineLocal_indicator (P := P) (ζ := aLife Γ L) (W := W)
    (VL := PocketTraversal.geomLW W xL) (VR := PocketTraversal.geomRW W xR) hh.1 hu₀.1
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀)
    (fun ω => (hb₀.isConformal_chart ω).recenter (τ ω)) hdom0 hfwd0 hlift0 hliftc
    (fun ω => by rw [Chart.dom_recenter]; exact harmonicOnNhd_lift_chart hb₀ ω) (θ₁ * chiC κ) (chiC κ)
    (continuous_aClock Γ) (monotone_aClock Γ) (aClock_zero Γ) hQa hreach hreg
    (fun Fb t => measurableSet_lineSafe_aStop ho hgood hgen (Coupling.isCompact_ballsK Fb) t)
    (fun t => retSigma76 P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r) (fun t => le_rfl)
    (fun t => retSigma76_le P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r) B
    (fun t => (hBm t).mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ (d.u + t) d.r) le_rfl) hBc hloc
    (fun t => by
      filter_upwards [hBD t, hD t] with ω hb hDω hωM hlt
      obtain ⟨hu, hr, hDe⟩ := hDω hωM hlt
      exact (hb hu hr).trans hDe)
  -- the field of `d`
  have hXe : ∀ᵐ ω ∂P, ω ∈ M →
      Exist.flowField 0 (θ₁ * chiC κ) (Exist.flowField (τ ω) 0 (hd.chartField κ h ω)) =
      Chart.chartTransport ((hb₀.isConformal_chart ω).recenter (τ ω)) 1 (θ₁ * chiC κ) (chiC κ) (h ω) := by
    filter_upwards [hch, hMord] with ω hchω hordω hωM
    rw [← RetFin.flowField_chartTransport, OrdDet.chartTransport_recenter_eq_flowField (hb₀.isConformal_chart ω)
      ((hb₀.isConformal_chart ω).continuousOn_lift_inv (hb₀.continuousOn_lift_chart ω)),
      RetData.IsMeasGood.chartField, chartTransport_congr_chart (hchω (hordω hωM)) (hb₀.isConformal_chart ω)
        (hd.isConformal_chart ω)]
  exact ⟨RetFin.hasSafeLaw_congr_field hXe hS', RetFin.hasSafeMembers_congr_field hXe hL'⟩

end Fst

end InteractingSLE.RLC.AStopSafe
