/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopSafeLine
import InteractingSLE.Spec.Restart.RetPlumbProofResidualSafe
import InteractingSLE.Spec.Restart.RetFinGlue

/-!
# Item 5 of `AStopSourceInputs` for the A-stopped second continuation: the safe laws (S) and (L)

Packet PROVE-T15-ASTOP-SAFE (Theorem 1.5's leaf 3). For the processes of PROVE-T15-ASTOP-PROC (the chart path
`AStopProc.sndChart d η₂' ζ₂`, the capacity-time filtration `aFilt` of RETPLUMB's physical filtration, the supported
capacity lifetime `M.indicator (aLife …)` and any continuous driver from `0` generating `aPath` on `M`):

* `measurableSet_lineSafe_aStop`: the safe events of the A-stopped clock are events of the physical filtration (the
  hull at the clock is the filled chart path through the physical time, `RetAux79.fwdHull_clock_eq_fillH`; compact
  sets are exhausted by compact sets inside `ℍ` as in RETPLUMB's `measurableSet_safe_compact`);
* **`hasSafe_aStop_snd`**: K2's (S) (`HasSafeLaw`) for the typed geometric force coordinates of the stop word and K2's
  (L) (`HasSafeMembers`), for the shifted chart field `flowField 0 (θ₂χ)` of the given retained data `d`, from
  RETPLUMB's `hasSafeLaw_of_retLines_indicator` / `hasSafeMembers_of_lineLocal_indicator` with the A-clock, the line
  kernels and filled lines at every live chart sample (`AStopSafeKernel`) and the later-line facts (`AStopSafeLine`).

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

open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F MartChar.RealFlow AStopProc OrdGap
open DomainMarkov DomainMarkov.Aux79 DomainMarkov.K2

universe u

/-! ### The safe events -/

section Safe

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 mΩ} {M : Set Ω} {Γ : Ω → ℝ≥0 → ℂ}
  {L : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}

/-- The safe events of the A-stopped clock for compact sets inside `ℍ`. -/
theorem measurableSet_lineSafe_aStop_H (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω) (aLife Γ L ω) (aPath Γ L ω)) {C : Set ℂ} (hC : IsCompact C)
    (hCH : C ⊆ H) (t : ℝ≥0) : MeasurableSet[𝓖 t] (M ∩ lineSafe (aClock Γ) W (aLife Γ L) C t) := by
  have hlive : MeasurableSet[𝓖 t] (M ∩ {ω | (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω}) := by
    have e : M ∩ {ω | (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω} = M ∩ {ω | (t : ℝ≥0∞) < L ω} := by
      ext ω
      constructor
      · rintro ⟨hω, ht⟩
        exact ⟨hω, (hg ω hω).aClock_lt_aLife_iff.1 ht⟩
      · rintro ⟨hω, ht⟩
        exact ⟨hω, (hg ω hω).aClock_lt_aLife_iff.2 ht⟩
    rw [e]
    exact ho.survival t
  refine @measurableSet_inter_lineSafe_of_prefix Ω (𝓖 t) M Γ (aClock Γ) W (aLife Γ L) t
    (fun ω hω => (hg ω hω).cont) (ho.coordinates t) hlive (fun ω hω ht => ?_) C hC hCH
  rw [(hg ω hω).aClock_eq t]
  exact fwdHull_clock_eq_fillH (hg ω hω).clock (hg ω hω).cont (hgen ω hω) ((hg ω hω).lt_of_aClock_lt ht)

/-- **The safe events of the A-stopped clock are events of the physical filtration**, for every compact set. -/
theorem measurableSet_lineSafe_aStop (ho : AObs 𝓖 M Γ L) (hg : ∀ ω ∈ M, IsAGood Γ L ω)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω) (aLife Γ L ω) (aPath Γ L ω)) {C : Set ℂ} (hC : IsCompact C)
    (t : ℝ≥0) : MeasurableSet[𝓖 t] (M ∩ lineSafe (aClock Γ) W (aLife Γ L) C t) := by
  let K : ℕ → Set ℂ := fun n => C ∩ {z | 1 / ((n : ℝ) + 1) ≤ z.im}
  have hK (n : ℕ) : IsCompact (K n) :=
    hC.inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hKH (n : ℕ) : K n ⊆ H := fun z hz =>
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) hz.2
  have he : M ∩ lineSafe (aClock Γ) W (aLife Γ L) C t =
      ⋂ n : ℕ, M ∩ lineSafe (aClock Γ) W (aLife Γ L) (K n) t := by
    ext ω
    constructor
    · rintro ⟨hω, hl, hdj⟩
      exact mem_iInter.2 fun n => ⟨hω, hl, hdj.mono_left inter_subset_left⟩
    · intro hω
      have hh := fun n => mem_iInter.1 hω n
      refine ⟨(hh 0).1, (hh 0).2.1, Set.disjoint_left.2 fun z hz hzh => ?_⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < z.im from hzh.1)
      exact Set.disjoint_left.1 (hh n).2.2 ⟨hz, hn.le⟩ hzh
  rw [he]
  exact MeasurableSet.iInter fun n => measurableSet_lineSafe_aStop_H ho hg hgen (hK n) (hKH n) t

end Safe

/-! ### (S) and (L) for the second continuation -/

section Snd

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- The domain of a later line is the stop chart's image of the complement of the hull at the clock. -/
theorem dom_eq_of_inv_eq {d : RetData Ω} (hd : d.IsMeasGood) {c : Chart} {W : ℝ≥0 → ℝ} (hWc : Continuous W)
    (hW0 : W 0 = 0) (Q : ℝ≥0) {ω : Ω}
    (h : ∀ w ∈ H, (d.chart ω).2.1 w = c.2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) :
    d.D ω = c.2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) := by
  rw [← hd.coe_dom_chart ω, (hd.isConformal_chart ω).coe_dom]
  refine image_H_eq_of_inv_eq (hWc.comp continuous_real_toNNReal) ?_ Q.coe_nonneg h
  show W (0 : ℝ).toNNReal = 0
  rw [Real.toNNReal_zero, hW0]

/-- **Item 5 of `AStopSourceInputs` for the A-stopped second continuation**: K2's (S) and (L) for the processes of
PROVE-T15-ASTOP-PROC (the capacity-time filtration `aFilt` of RETPLUMB's physical filtration along the A-stopped chart
path `sndChart d η₂' ζ₂`, the supported capacity lifetime and any continuous driver from `0` generating the path in
capacity time on `M`), with the typed geometric force coordinates of the stop word `β₀` and the shifted chart field
of `d`, on a good stop-line event `M` of ordinary pairs of one force type. -/
theorem hasSafe_aStop_snd (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
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
    {η₂' : Ω → ℝ≥0 → ℂ} (hm₂ : ∀ t, Measurable fun ω => η₂' ω t)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    {M : Set Ω} (hM : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] M)
    (hMg : ∀ ω ∈ M, IsSndGood d η₁ η₂ η₂' ζ₁ ζ₂ x₂ ω)
    (hMord : ∀ᵐ ω ∂P, ω ∈ M → IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r)
    (a : ForceWordType) (htype : ∀ ω ∈ M, β₀ ω ∈ FCDet.typeSet κ θ₂ a.nL a.nR a.rhoL a.rhoR)
    {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun q => W q ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hgen : ∀ ω ∈ M, IsGeneratingTrace (W · ω) (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω)
      (aPath (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂) ω))
    (hQa : ∀ t, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r t]
      (M.indicator (aClock (sndChart d η₂' ζ₂) t))) :
    HasSafeLaw κ a.rhoL a.rhoR P (aFilt (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (sndChart d η₂' ζ₂) hQa) M
      (M.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂))) W
      (PocketTraversal.geomLW W fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β₀ ω))
      (PocketTraversal.geomRW W fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β₀ ω))
      (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω)) ∧
    HasSafeMembers P (aFilt (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r) M (sndChart d η₂' ζ₂) hQa) M
      (M.indicator (aLife (sndChart d η₂' ζ₂) (sndLifeP d η₂' ζ₂))) W
      (fun ω => Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω)) := by
  classical
  have hζ₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζ₂ := measurable_lifetime_of_isFlowLine hη₂
  obtain ⟨η₁'', hm₁'', ha₁''⟩ := exists_measurable_version_of_isFlowLine hη₁
  obtain ⟨G, hG⟩ := exists_retG_family_with_live hκ hκ4 hη₁ hη₂ hm₁'' hm₂ ha₁'' ha₂ d.u
  have hdG : ∀ r', (retFam G η₁'' η₂' d.u r').IsMeasGood := fun r' => (hG r').1
  have hagF : ∀ r' : ℝ≥0, ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (r' : ℝ≥0∞) < ζ₂ ω → ω ∈ G r' ∧
      (∀ s ≤ d.u, η₁'' ω s = η₁ ω s) ∧ ∀ t ≤ r', η₂' ω t = η₂ ω t := by
    intro r'
    filter_upwards [(hG r').2.2.2, ha₁'', ha₂] with ω hGω e₁ e₂ hu hr
    exact ⟨hGω hu hr, fun s hs => e₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le),
      fun s hs => e₂ s ((ENNReal.coe_le_coe.2 hs).trans hr.le)⟩
  -- the stop chart of the family is `d`'s chart at ordinary pairs
  have hch : ∀ᵐ ω ∂P, ω ∈ {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} →
      (retFam G η₁'' η₂' d.u d.r).chart ω = d.chart ω := by
    filter_upwards [hag, hagF d.r] with ω hagω hF hord
    obtain ⟨hG', a₁, a₂⟩ := hagω hord.1 hord.2.1
    obtain ⟨hG0, f₁, f₂⟩ := hF hord.1 hord.2.1
    exact (RetData.chart_eq_of_agree (d := d) (G' := G d.r) (η₁' := η₁'') (η₂' := η₂') hG' hG0
      (fun s hs => (f₁ s hs).trans (a₁ s hs).symm) (fun s hs => (f₂ s hs).trans (a₂ s hs).symm)).2.2
  have hm₀ := isRetMeanIdentOn_of_chart_eq hd (hdG d.r) rfl rfl hch hmean
  have hm₀0 := isRetMeanIdentOn_of_chart_eq hd (hdG (d.r + 0)) rfl (add_zero d.r)
    (by filter_upwards [hch] with ω hω hord; rw [add_zero]; exact hω hord) hmean
  -- the line kernels and the line words
  choose ηc₁ ηc₂ g hc₁ hc₂ hmc₁ hmc₂ _h0₁ _h0₂ hagc₁ hagc₂ hg hker using fun t : ℝ≥0 =>
    exists_retDomain_kernel_E hL75 hκ hκ4 hb hh hη₁ hη₂ (hdG (d.r + t)) (hagF (d.r + t)) hu₀
  choose βc hβc using fun t : ℝ≥0 =>
    OrdGap.exists_ordEnclWord (θ₁ := θ₁) hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ (hdG (d.r + t)) (hagF (d.r + t))
  set βL : ℝ≥0 → Ω → BoundaryWord := fun t => if t = 0 then β₀ else βc t with hβL
  set xL : Ω → Fin a.nL → ℝ := fun ω => FCDet.typeXL κ θ₂ a.nL a.nR a.rhoL a.rhoR (β₀ ω) with hxL
  set xR : Ω → Fin a.nR → ℝ := fun ω => FCDet.typeXR κ θ₂ a.nL a.nR a.rhoL a.rhoR (β₀ ω) with hxR
  have htype' : ∀ ω ∈ M, FCDet.IsFlowType κ θ₂ (β₀ ω) (xL ω) (xR ω) a.rhoL a.rhoR := fun ω hω =>
    FCDet.isFlowType_of_mem_typeSet (htype ω hω)
  set Γ := sndChart d η₂' ζ₂ with hΓ
  set L := sndLifeP d η₂' ζ₂ with hL
  -- the line facts at every line
  have hline_all : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ M → (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω →
      ((d.u : ℝ≥0∞) < ζ₁ ω ∧ ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω ∧
        ω ∈ (retFam G η₁'' η₂' d.u (d.r + t)).E) ∧
      (βL t ω).IsSorted ∧
      (∀ φ : TestOn upperHalfPlaneOpens,
        Chart.chartTransport ((hdG (d.r + t)).isConformal_chart ω) 1 0 (chiC κ)
          (g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ w, (βL t ω).mean w * φ w) ∧
      (∀ w ∈ H, ((retFam G η₁'' η₂' d.u (d.r + t)).chart ω).2.1 w =
        ((retFam G η₁'' η₂' d.u d.r).chart ω).2.1
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω) w)) ∧
      (∀ w ∈ H, ((retFam G η₁'' η₂' d.u (d.r + t)).chart ω).2.2
          (((retFam G η₁'' η₂' d.u (d.r + t)).chart ω).2.1 w) =
        (logDerivFwd (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω)
          (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω) w)).im +
          ((retFam G η₁'' η₂' d.u d.r).chart ω).2.2 (((retFam G η₁'' η₂' d.u d.r).chart ω).2.1
            (fwdMapInv (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω) w))) ∧
      ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
        forceBoundaryData κ a.rhoL a.rhoR
          (fun i => PocketTraversal.geomLW W xL i (aClock Γ t ω) ω - W (aClock Γ t ω) ω)
          (fun j => PocketTraversal.geomRW W xR j (aClock Γ t ω) ω - W (aClock Γ t ω) ω) y =
          (βL t ω).fn y + θ₂ * chiC κ := by
    intro t
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
    · subst h0
      have hβ0 : βL 0 = β₀ := by rw [hβL]; simp
      rw [hβ0]
      filter_upwards [ae_aLine_snd_zero hκ hag hdG hagF hm₀0 hsort hMg hMord hWc hW0 htype' (hc₁ 0) (hc₂ 0)
        (hmc₁ 0) (hmc₂ 0) (hagc₁ 0) (hagc₂ 0) (hg 0)] with ω hω hωM _
      exact hω hωM
    · have hβt : βL t = βc t := by rw [hβL]; simp [hpos.ne']
      rw [hβt]
      exact ae_aLine_snd_pos hL75 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ hd hag hdG hagF hm₀ hsort hMg hMord hWc hW0
        (Eventually.of_forall hgen) htype' hpos (hβc t).1 (hβc t).2 (hc₁ t) (hc₂ t) (hmc₁ t) (hmc₂ t)
        (hagc₁ t) (hagc₂ t) (hg t)
  -- observations and good samples
  have ho := sndObs_of_flowLines hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hm₂ ha₂ hM hMg
  have hgood : ∀ ω ∈ M, IsAGood Γ L ω := fun ω hω =>
    isAGood_snd hd (hMg ω hω).2.2.1 (hMg ω hω).2.2.2.1 (hMg ω hω).agree₂ (hMg ω hω).2.1
  have hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ M → (q : ℝ≥0∞) < aLife Γ L ω → ∃ t, q ≤ aClock Γ t ω :=
    fun q => Eventually.of_forall fun ω hω hq => (hgood ω hω).exists_aClock_ge hq
  have hreg : ∀ᵐ ω ∂P, ω ∈ M → IsForceReg W (PocketTraversal.geomLW W xL) (PocketTraversal.geomRW W xR)
      (aLife Γ L) ω := Eventually.of_forall fun ω _ => FCDet.isForceReg_thr hW0 hWc xL xR _ ω
  -- the stop chart is measurable at time `0`
  obtain ⟨α₁, α₂, hcα₁, hcα₂, hmα₁, hmα₂, h0α₁, h0α₂, haα₁, haα₂, -, -, -⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement
      hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR d.u d.r) d.u d.r
  obtain ⟨hdom, hfwd, hlift⟩ := chart_measurability_retSigma76 (hdG d.r) hζ₁ hζ₂ (hG d.r).2.1 (hagF d.r)
    hcα₁ hcα₂ hmα₁ hmα₂ h0α₁ h0α₂ haα₁ haα₂
  have hdom0 : ∀ z, MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0]
      {ω | z ∈ ((retFam G η₁'' η₂' d.u d.r).chart ω).dom} := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hdom
  have hfwd0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0]
      ({ω | z ∈ ((retFam G η₁'' η₂' d.u d.r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁'' η₂' d.u d.r).chart ω).1 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hfwd
  have hlift0 : ∀ z, Measurable[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0]
      ({ω | z ∈ ((retFam G η₁'' η₂' d.u d.r).chart ω).dom}.indicator
        fun ω => ((retFam G η₁'' η₂' d.u d.r).chart ω).2.2 z) := by
    simpa +instances only [retPhysFiltration_apply, retFam, add_zero] using hlift
  have hM0 : MeasurableSet[retPhysFiltration P η₁ η₂ ζ₁ ζ₂ d.u d.r 0] M := by
    simpa +instances only [retPhysFiltration_apply, add_zero] using hM
  -- the later domains
  have hD : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ M → (aClock Γ t ω : ℝ≥0∞) < aLife Γ L ω →
      (d.u : ℝ≥0∞) < ζ₁ ω ∧ ((d.r + t : ℝ≥0) : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ (retFam G η₁'' η₂' d.u (d.r + t)).E ∧
      (retFam G η₁'' η₂' d.u (d.r + t)).D ω = ((retFam G η₁'' η₂' d.u d.r).chart ω).2.1 ''
        (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (aClock Γ t ω)) := by
    intro t
    filter_upwards [hline_all t] with ω hl hωM hlt
    obtain ⟨⟨hu, hrt, hEt⟩, -, -, hIII, -⟩ := hl hωM hlt
    exact ⟨hu, hrt, hEt, dom_eq_of_inv_eq (hdG (d.r + t)) (hWc ω) (hW0 ω) _ hIII⟩
  -- (S)
  have hS' := hasSafeLaw_of_retLines_indicator (P := P) (κ := κ) (ρL := a.rhoL) (ρR := a.rhoR)
    (VL := PocketTraversal.geomLW W xL) (VR := PocketTraversal.geomRW W xR) (ζ := aLife Γ L) hM0
    (fun ω => (hdG d.r).isConformal_chart ω) hdom0 hfwd0 hlift0 (fun ω => (hdG d.r).continuousOn_lift_chart ω)
    hh.1 (θ₂ * chiC κ) (continuous_aClock Γ) (monotone_aClock Γ) (aClock_zero Γ) hQa hreach hreg
    (fun ψ t => measurableSet_lineSafe_aStop ho hgood hgen ψ.hasCompactSupport.isCompact t)
    (fun t => retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ (ηc₁ t) (ηc₂ t) d.u (d.r + t))
    (fun t => retPhysFiltration_le_retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ (ηc₁ t) (ηc₂ t) d.u d.r t)
    (fun t => retLineSigma_le hh.1 u₀ η₁ η₂ hζ₁ hζ₂ (hc₁ t) (hc₂ t) (hmc₁ t) (hmc₂ t) d.u (d.r + t))
    (fun t ω => g t ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀)
    (fun t φ => by
      filter_upwards [hker t φ, hD t] with ω hk hDω hωM hlt hsupp
      obtain ⟨hu, hrt, hEt, hDe⟩ := hDω hωM hlt
      rw [← hDe] at hsupp ⊢
      exact hk hu hrt hEt hsupp)
    hWc hW0 (fun t ω => (hdG (d.r + t)).isConformal_chart ω) βL
    (fun t => by
      filter_upwards [hline_all t] with ω hl hωM hlt
      obtain ⟨-, hs, hmω, hIII, hlift, hdat⟩ := hl hωM hlt
      exact ⟨hs, hmω, hIII, hlift, hdat⟩)
  -- (L)
  choose B hBm hBc hloc hBD using fun t : ℝ≥0 =>
    exists_ret_filled_line_E hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ (d := retFam G η₁'' η₂' d.u (d.r + t))
      (hagF (d.r + t))
  have hL' := hasSafeMembers_of_lineLocal_indicator (P := P) (ζ := aLife Γ L) (W := W)
    (VL := PocketTraversal.geomLW W xL) (VR := PocketTraversal.geomRW W xR) hh.1 hu₀.1
    (isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀) (fun ω => (hdG d.r).isConformal_chart ω)
    hdom0 hfwd0 hlift0 (fun ω => (hdG d.r).continuousOn_lift_chart ω)
    (fun ω => harmonicOnNhd_lift_chart (hdG d.r) ω) (θ₂ * chiC κ) (chiC κ) (continuous_aClock Γ)
    (monotone_aClock Γ) (aClock_zero Γ) hQa hreach hreg
    (fun Fb t => measurableSet_lineSafe_aStop ho hgood hgen (Coupling.isCompact_ballsK Fb) t)
    (fun t => retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t))
    (fun t => (retPhysFiltration_apply P η₁ η₂ ζ₁ ζ₂ d.u d.r t).le)
    (fun t => retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)) B
    (fun t => (hBm t).mono (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u (d.r + t)) le_rfl) hBc hloc
    (fun t => by
      filter_upwards [hBD t, hD t] with ω hb hDω hωM hlt
      obtain ⟨hu, hrt, hEt, hDe⟩ := hDω hωM hlt
      exact (hb hu hrt hEt).trans hDe)
  -- the field of `d`
  have hXe : ∀ᵐ ω ∂P, ω ∈ M → Exist.flowField 0 (θ₂ * chiC κ) (hd.chartField κ h ω) =
      Chart.chartTransport ((hdG d.r).isConformal_chart ω) 1 (θ₂ * chiC κ) (chiC κ) (h ω) := by
    filter_upwards [hch, hMord] with ω hchω hordω hωM
    rw [RetData.IsMeasGood.chartField, RetFin.flowField_chartTransport]
    exact chartTransport_congr_chart (hchω (hordω hωM)).symm _ _ _ _ _ _
  exact ⟨RetFin.hasSafeLaw_congr_field hXe hS', RetFin.hasSafeMembers_congr_field hXe hL'⟩

end Snd

end InteractingSLE.RLC.AStopSafe
