/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideHeightHull
import InteractingSLE.Spec.Restart.ChartMeasRandom
import InteractingSLE.GFF.LocalSets.UnionLaw
import InteractingSLE.Spec.Sec6.CondMeanStop
import InteractingSLE.Spec.Restart.ClockTrace

/-!
# The range mean equals the hull mean on the unbounded component

Packet PROVE-SIDEHEIGHT. The single-path side heights are stated for the local-set mean of the **range**
`A₁ = η([0, q]) ∩ ℍ` of a flow line (`SinglePathSideHeightStatement`), while the frozen coupling describes the field
off the **hull** `x + K_q = fill(A₁)`. On the unbounded component `ℍ \ fill(A₁)` the two means agree:

* the union law of the range and the hull at the stop `τₙ = q ∧ σₙ` (`σₙ` announcing the lifetime) given both germs
  and both sets (`IsLocalSet.exists_condLaw_union_germs`; the range is field determined, so the two sets are
  conditionally independent given the field);
* the tower comparison (`ae_apply_eq_of_isCondZeroBoundaryGFF`) of the range mean with the union mean on
  `{supp φ ⊆ ℍ \ fill(A₁)}`, an event of `σ(A₁)` (`measurableSet_subset_H_diff_fillH`, through the dyadic covers of
  `closure A₁`), where the two Green covariances agree (`ℍ \ fill(A₁)` is a union of components of both complements);
* the tower comparison of the hull mean with the union mean on `{hcap(A₂ − x)/2 = q, supp φ ∩ A₂ = ∅}`, an event of
  `σ(A₂)`, on which `τₙ = q` and the union is the hull;
* the hull mean in the original coordinate (`ae_apply_eq_of_isLocalSetMean_flowHull`).

**`ae_apply_eq_flowMean_of_range`**: almost surely on `{q < ζ}`, for every test function `φ` supported in
`ℍ \ fill(A₁)`, `g(φ) = ∫ (𝔥_q(· − x) − c − 𝔥₀) φ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SideHeight

open QuantumZipper (H fwdMap fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open LocalSets

/-! ### Hits of the closure and the unbounded component -/

section Hits

/-- A compact set meets the closure of `S` iff every thickening of it meets `S`. -/
theorem nonempty_inter_closure_iff {Q S : Set ℂ} (hQ : IsCompact Q) :
    (Q ∩ closure S).Nonempty ↔ ∀ n : ℕ, (S ∩ thickening (1 / ((n : ℝ) + 1)) Q).Nonempty := by
  constructor
  · rintro ⟨z, hzQ, hzS⟩ n
    obtain ⟨s, hs, hzs⟩ := Metric.mem_closure_iff.1 hzS (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨s, hs, Metric.mem_thickening_iff.2 ⟨z, hzQ, by rwa [dist_comm]⟩⟩
  · intro h
    obtain ⟨s₀, hs₀, hs₀Q⟩ := h 0
    obtain ⟨q₀', -, -⟩ := Metric.mem_thickening_iff.1 hs₀Q
    have hQne : Q.Nonempty := by
      obtain ⟨z, hz, -⟩ := Metric.mem_thickening_iff.1 hs₀Q
      exact ⟨z, hz⟩
    obtain ⟨q₀, hq₀Q, hmin⟩ := hQ.exists_isMinOn hQne (Metric.continuous_infDist_pt S).continuousOn
    have hle : ∀ n : ℕ, infDist q₀ S < 1 / ((n : ℝ) + 1) := by
      intro n
      obtain ⟨s, hs, hsQ⟩ := h n
      obtain ⟨q, hqQ, hsq⟩ := Metric.mem_thickening_iff.1 hsQ
      calc infDist q₀ S ≤ infDist q S := hmin hqQ
        _ ≤ dist q s := infDist_le_dist_of_mem hs
        _ < 1 / ((n : ℝ) + 1) := by rwa [dist_comm]
    have h0 : infDist q₀ S = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) infDist_nonneg
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [hle n]
    exact ⟨q₀, hq₀Q, (mem_closure_iff_infDist_zero ⟨s₀, hs₀⟩).2 h0⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {A : Ω → Set ℂ}

/-- The hits of the closure of a random subset of `ℍ` by a compact set are events of `σ(A)`. -/
theorem measurableSet_inter_closure_nonempty (hA : Measurable[m, hittingSigma] A) (hAH : ∀ ω, A ω ⊆ H)
    {Q : Set ℂ} (hQ : IsCompact Q) : MeasurableSet[m] {ω | (Q ∩ closure (A ω)).Nonempty} := by
  have e : {ω | (Q ∩ closure (A ω)).Nonempty} =
      ⋂ n : ℕ, A ⁻¹' {S : Set ℂ | (S ∩ (thickening (1 / ((n : ℝ) + 1)) Q ∩ H)).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage, nonempty_inter_closure_iff hQ]
    refine forall_congr' fun n => ⟨fun ⟨z, hz, hzQ⟩ => ⟨z, hz, hzQ, hAH ω hz⟩, fun ⟨z, hz, hzQ, _⟩ => ⟨z, hz, hzQ⟩⟩
  rw [e]
  refine MeasurableSet.iInter fun n => hA ?_
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨_, isOpen_thickening.inter QuantumZipper.isOpen_H, inter_subset_right, rfl⟩

/-- The closure of a random subset of `ℍ` is observed through its dyadic hits. -/
theorem isDyadicHitMeasurable_closure (hA : Measurable[m, hittingSigma] A) (hAH : ∀ ω, A ω ⊆ H) :
    @Restart.IsDyadicHitMeasurable Ω m fun ω => closure (A ω) := fun n k =>
  measurableSet_inter_closure_nonempty hA hAH (Restart.isCompact_dyadicSquare n k)

/-- **`{C ⊆ ℍ \ fill(K)}` is an event** for a random compact `K` observed through its dyadic hits and a compact `C`. -/
theorem measurableSet_subset_H_diff_fillH {K : Ω → Set ℂ} (hK : @Restart.IsDyadicHitMeasurable Ω m K)
    (hKc : ∀ ω, IsCompact (K ω)) {C : Set ℂ} (hC : IsCompact C) :
    MeasurableSet[m] {ω | C ⊆ H \ fillH (K ω)} := by
  have e : {ω | C ⊆ H \ fillH (K ω)} =
      ⋃ n : ℕ, {ω | C ⊆ H \ fillH (Restart.coverOf n (Restart.dyadicIdx n (K ω)))} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, ← Restart.dyadicCover_eq_coverOf]
    constructor
    · intro hCK
      set U : ℕ → Set ℂ := fun n => H \ fillH (Restart.dyadicCover n (K ω)) with hU
      have hUo : ∀ n, IsOpen (U n) := fun n =>
        isOpen_H_diff_fillH (Restart.isCompact_dyadicCover (hKc ω).isBounded n).isBounded
      have hmono : Monotone U := fun a b hab =>
        sdiff_subset_sdiff_right (Restart.fillH_dyadicCover_antitone hab)
      have hsub : C ⊆ ⋃ n, U n := by
        intro z hz
        have hz' := hCK hz
        have : z ∉ ⋂ n, fillH (Restart.dyadicCover n (K ω)) := by
          rw [Restart.iInter_fillH_dyadicCover (hKc ω)]
          exact hz'.2
        obtain ⟨n, hn⟩ := not_forall.1 (mem_iInter.not.1 this)
        exact mem_iUnion.2 ⟨n, hz'.1, hn⟩
      obtain ⟨n, hn⟩ := hC.elim_directed_cover U hUo hsub hmono.directed_le
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩ z hz
      exact ⟨(hn hz).1, fun h => (hn hz).2 (fillH_mono (Restart.subset_dyadicCover n) h)⟩
  rw [e]
  exact MeasurableSet.iUnion fun n => Restart.measurableSet_comp_dyadicIdx hK (fun ω => (hKc ω).isBounded) n
    fun S => C ⊆ H \ fillH (Restart.coverOf n S)

/-- `fill` only sees the closure. -/
theorem fillH_closure (S : Set ℂ) : fillH (closure S) = fillH S :=
  fillH_congr (by rw [closure_closure])

/-- **The event `{supp φ ⊆ ℍ \ fill(A)}` belongs to `σ(A)`** for a bounded random subset `A` of `ℍ`. -/
theorem measurableSet_tsupport_subset_H_diff_fillH (hA : Measurable[m, hittingSigma] A) (hAH : ∀ ω, A ω ⊆ H)
    (hAb : ∀ ω, Bornology.IsBounded (A ω)) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[m] {ω | tsupport φ ⊆ H \ fillH (A ω)} := by
  have h := measurableSet_subset_H_diff_fillH (isDyadicHitMeasurable_closure hA hAH)
    (fun ω => (hAb ω).isCompact_closure) φ.hasCompactSupport.isCompact
  simpa only [fillH_closure] using h

end Hits

/-! ### Fillings of relatively closed sets -/

section Fill

theorem subset_fillH {A : Set ℂ} (hA : A ⊆ H) : A ⊆ fillH A := fun _ hz => ⟨hA hz, Or.inl (subset_closure hz)⟩

/-- A relatively closed subset of `ℍ` is its closure inside `ℍ`. -/
theorem closure_inter_H_eq {A : Set ℂ} (hA : A ⊆ H) (hAo : IsOpen (H \ A)) : closure A ∩ H = A := by
  refine Subset.antisymm (fun z ⟨hzc, hzH⟩ => ?_) fun z hz => ⟨subset_closure hz, hA hz⟩
  by_contra hzA
  obtain ⟨w, hw, hwA⟩ := mem_closure_iff_nhds.1 hzc _ (hAo.mem_nhds ⟨hzH, hzA⟩)
  exact hw.2 hwA

theorem fillH_inter_H (S : Set ℂ) : fillH (S ∩ H) = fillH S := by
  refine fillH_congr (Subset.antisymm (fun _ ⟨hz, hzH⟩ => ⟨closure_mono inter_subset_left hz, hzH⟩)
    fun z ⟨hz, hzH⟩ => ⟨?_, hzH⟩)
  have := QuantumZipper.isOpen_H.inter_closure ⟨hzH, hz⟩
  rwa [inter_comm] at this

/-- **The unbounded part is a union of components**: for a relatively closed `A ⊆ ℍ`, the component in `ℍ \ A` of a
point outside `fill(A)` stays outside `fill(A)`. -/
theorem connectedComponentIn_subset_H_diff_fillH {A : Set ℂ} (hA : A ⊆ H) (hAo : IsOpen (H \ A)) {z : ℂ}
    (hz : z ∈ H \ fillH A) : connectedComponentIn (H \ A) z ⊆ H \ fillH A := by
  have hcl : H \ closure A = H \ A := by
    ext w
    refine ⟨fun hw => ⟨hw.1, fun h => hw.2 (subset_closure h)⟩, fun hw => ⟨hw.1, fun h => hw.2 ?_⟩⟩
    rw [← closure_inter_H_eq hA hAo]
    exact ⟨h, hw.1⟩
  intro w hw
  have hzA : z ∉ closure A := fun h => hz.2 ⟨hz.1, Or.inl h⟩
  have hzb : ¬ Bornology.IsBounded (connectedComponentIn (H \ closure A) z) := fun h => hz.2 ⟨hz.1, Or.inr h⟩
  rw [← hcl] at hw
  have hwH : w ∈ H \ closure A := connectedComponentIn_subset _ _ hw
  refine ⟨hwH.1, fun hwf => ?_⟩
  rcases hwf.2 with h | h
  · exact hwH.2 h
  · rw [← connectedComponentIn_eq hw] at h
    exact hzb h

end Fill

/-! ### The range mean and the hull mean -/

section Range

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h h' : Ω → DistOn upperHalfPlaneOpens} {x c : ℝ} {u₀ u₀' : ℂ → ℝ}

/-- **The range mean is the hull mean off the filling, at a fixed stop of a single flow line.** Let `A₁` be a bounded,
hitting-measurable, field-determined local set of the centred original field `h⁰`, equal to the stopped range
`η([0, q]) ∩ ℍ` on `{q < ζ}` and containing every earlier hull `x + K_t` (`t ≤ q`) in its filling. Then, for every
local-set mean `g` of `A₁`, almost surely on `{q < ζ}`, for every test function `φ` supported in `ℍ \ fill(A₁)`,
`g(φ) = ∫ (𝔥_q(· − x) − c − 𝔥₀) φ`. -/
theorem ae_apply_eq_flowMean_of_range (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h')
    (hκ : 0 < κ) (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h' ω))
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀')
    (hrel : EqOn u₀' (fun z => u₀ (z + x) + c) H) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {η : Ω → ℝ≥0 → ℂ} (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) fun t => η ω t - x)
    {A₁ : Ω → Set ℂ} (hA₁m : Measurable[mΩ, hittingSigma] A₁) (hA₁H : ∀ ω, A₁ ω ⊆ H)
    (hA₁b : ∀ ω, Bornology.IsBounded (A₁ ω)) (hA₁loc : IsLocalSet A₁ (WholeField.centredField h u₀) P)
    (hA₁det : MeasurableSpace.comap A₁ hittingSigma ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P)
    {q : ℝ≥0} (hA₁q : ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → A₁ ω = η ω '' Icc 0 q ∩ H)
    (hA₁fill : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ q → (t : ℝ≥0∞) < ζ ω →
      (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) t ⊆ fillH (A₁ ω))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A₁ (WholeField.centredField h u₀) P g)
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω))
      (forceJumpSet (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)) (u ω)) :
    ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω → ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ fillH (A₁ ω) →
      g ω φ = ∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (u ω) (z - x) - c - u₀ z) * φ z := by
  classical
  set h0 := WholeField.centredField h u₀ with hh0_def
  have hhm := hh0.measurable
  have hE := hC.1
  -- an inadmissible seed has lifetime zero
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · filter_upwards [hE.2.2.2.2] with ω hp hlt
    rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
    exact absurd hlt (ENNReal.not_lt_zero)
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ, hσ, -⟩ := WholeField.exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX)
    (B := B) (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  -- the candidate mean
  set m : Ω → ℂ → ℝ := fun ω z =>
    couplingMean κ (fun s : ℝ => W s.toNNReal ω) q (u ω) (z - x) - c - u₀ z with hm_def
  -- the per-stop statement
  have hstop : ∀ n : ℕ, ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, q ≤ σ n ω → (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ H \ fillH (A₁ ω) → g ω φ = ∫ z, m ω z * φ z := by
    intro n φ
    -- the stop `τ = q ∧ σₙ`
    set τ : Ω → WithTop ℝ≥0 := fun ω => ((min q (σ n ω) : ℝ≥0) : WithTop ℝ≥0) with hτ_def
    have hτ : IsStoppingTime (drivingFiltration P hX) τ := by
      have h1 := (isStoppingTime_const (drivingFiltration P hX) q).min (hσ.1 n)
      have e : τ = fun ω => min ((q : WithTop ℝ≥0)) ((σ n ω : ℝ≥0) : WithTop ℝ≥0) :=
        funext fun ω => WithTop.coe_min _ _
      rw [e]
      exact h1
    have hτu : ∀ ω, (τ ω).untopD 0 = min q (σ n ω) := fun ω => WithTop.untopD_coe _ _
    have hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω := by
      filter_upwards [hσ.2.2.1 n] with ω hω
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hω
    -- the translated hull at `τ` and its mean
    obtain ⟨K', hK'm, hK'e, -⟩ := Coupling.exists_hittingVersion_hull hX hpath hτ hτζ
    set A₂ : Ω → Set ℂ := fun ω => (fun z : ℂ => z + x) '' K' ω with hA₂_def
    have hA₂m : Measurable[mΩ, hittingSigma] A₂ := fun s hs => hK'm (measurable_image_add x hs)
    have hA₂K : ∀ᵐ ω ∂P, A₂ ω =
        (fun z : ℂ => z + x) '' fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := by
      filter_upwards [hK'e] with ω hω
      simp only [hA₂_def, hω]
    have hloc₂ : IsLocalSet A₂ h0 P :=
      Coupling.IsLocalSet.congr_set (isLocalSet_flowHull hC htrans hu₀ hu₀' hrel hX hτ hτζ) hA₂K
    obtain ⟨g₂, hg₂⟩ := IsLocalSet.exists_isLocalSetMean hh0 hA₂m hloc₂
    -- the force data at `τ` (the given extension where `τ = q`)
    have hext : ∀ ω, ∃ v : ℂ → ℝ, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
        (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) v ∧
        ((τ ω).untopD 0 = q → v = u ω) := by
      intro ω
      by_cases hq : (τ ω).untopD 0 = q
      · exact ⟨u ω, by rw [hq]; exact hu ω, fun _ => rfl⟩
      · obtain ⟨v, hv⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
          (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        exact ⟨v, hv, fun h => absurd h hq⟩
    choose uτ huτ huτq using hext
    have hg₂id := ae_apply_eq_of_isLocalSetMean_flowHull hC hκ htrans hh0 hu₀ hu₀' hrel hX hτ hτζ hA₂m hA₂K
      hg₂ huτ
    -- the union law
    have hci : LQGMetric.CondIndepEv (MeasurableSpace.comap h0 inferInstance) (MeasurableSpace.comap A₁ hittingSigma)
        (MeasurableSpace.comap A₂ hittingSigma) P :=
      Sec6.condIndepEv_of_le_aeSigma hhm.comap_le hA₂m.comap_le hA₁det
    obtain ⟨g₀, hg₀m, -, hg₀c⟩ := IsLocalSet.exists_condLaw_union_germs hh0 hA₁m hA₂m hci hA₁loc hloc₂
    set A : Ω → Set ℂ := fun ω => A₁ ω ∪ A₂ ω with hA_def
    have hA : Measurable[mΩ, hittingSigma] A := measurable_union_hitting hA₁m hA₂m
    have h𝒥le : germSigma A h0 ⊔ (MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma) ⊔
        (germSigma A₁ h0 ⊔ germSigma A₂ h0) ≤ mΩ :=
      sup_le (sup_le (germSigma_le hA hhm) (sup_le hA₁m.comap_le hA₂m.comap_le))
        (sup_le (germSigma_le hA₁m hhm) (germSigma_le hA₂m hhm))
    have hA𝒥 : germSigma A h0 ≤ germSigma A h0 ⊔ (MeasurableSpace.comap A₁ hittingSigma ⊔
        MeasurableSpace.comap A₂ hittingSigma) ⊔ (germSigma A₁ h0 ⊔ germSigma A₂ h0) :=
      le_sup_left.trans le_sup_left
    have hA₁𝒥 : germSigma A₁ h0 ≤ germSigma A h0 ⊔ (MeasurableSpace.comap A₁ hittingSigma ⊔
        MeasurableSpace.comap A₂ hittingSigma) ⊔ (germSigma A₁ h0 ⊔ germSigma A₂ h0) :=
      (le_sup_left).trans le_sup_right
    have hA₂𝒥 : germSigma A₂ h0 ≤ germSigma A h0 ⊔ (MeasurableSpace.comap A₁ hittingSigma ⊔
        MeasurableSpace.comap A₂ hittingSigma) ⊔ (germSigma A₁ h0 ⊔ germSigma A₂ h0) :=
      (le_sup_right).trans le_sup_right
    -- the containment `A₂ ⊆ fill(A₁)`
    have hsub : ∀ᵐ ω ∂P, A₂ ω ⊆ fillH (A₁ ω) := by
      filter_upwards [hA₂K, hA₁fill, hτζ] with ω hω hf hlt
      rw [hω, hτu]
      exact hf _ (min_le_left _ _) (by rw [← hτu]; exact Coupling.coe_untopD_lt_zeta hlt)
    -- (a) the range mean is the union mean on `{supp φ ⊆ ℍ \ fill(A₁)}`
    set G₁ : Set Ω := {ω | tsupport φ ⊆ H \ fillH (A₁ ω)} with hG₁_def
    have hG₁m : MeasurableSet[germSigma A₁ h0] G₁ :=
      comap_le_germSigma A₁ h0 _ (measurableSet_tsupport_subset_H_diff_fillH (m := MeasurableSpace.comap A₁
        hittingSigma) (Measurable.of_comap_le le_rfl) hA₁H hA₁b φ)
    have hstepa : ∀ᵐ ω ∂P, ω ∈ G₁ → g ω φ = g₀ ω φ := by
      refine ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) hA₁𝒥 h𝒥le hhm hg.1 (hg₀m.mono hA𝒥 le_rfl) hg.2.2
        hg₀c φ hG₁m fun c' => ?_
      filter_upwards [hA₁loc.2.1, hloc₂.2.1, hsub] with ω ⟨hA₁s, ho₁⟩ ⟨hA₂s, ho₂⟩ hs hωG
      set C := H \ fillH (A₁ ω) with hC_def
      have hCo : IsOpen C := isOpen_H_diff_fillH (hA₁b ω)
      have hC₁ : C ⊆ H \ A₁ ω := fun z hz => ⟨hz.1, fun h => hz.2 (subset_fillH hA₁s h)⟩
      have hC₂ : C ⊆ H \ (A₁ ω ∪ A₂ ω) := fun z hz =>
        ⟨hz.1, fun h => h.elim (fun h1 => hz.2 (subset_fillH hA₁s h1)) fun h2 => hz.2 (hs h2)⟩
      have hcomp : ∀ z ∈ C, connectedComponentIn (H \ A₁ ω) z ⊆ C := fun z hz =>
        connectedComponentIn_subset_H_diff_fillH hA₁s ho₁ hz
      have ho : IsOpen (H \ (A₁ ω ∪ A₂ ω)) := by
        have e : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
          ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
        rw [e]
        exact ho₁.inter ho₂
      have hd₁ : IsOpen ((H \ A₁ ω) \ C) := isOpen_diff_of_forall_connectedComponentIn_subset ho₁ hcomp
      have hd : IsOpen ((H \ (A₁ ω ∪ A₂ ω)) \ C) :=
        isOpen_diff_of_forall_connectedComponentIn_subset ho fun z hz =>
          (connectedComponentIn_mono z (show H \ (A₁ ω ∪ A₂ ω) ⊆ H \ A₁ ω from
            fun w hw => ⟨hw.1, fun h => hw.2 (Or.inl h)⟩)).trans (hcomp z hz)
      have hsupp : tsupport ⇑(c' • φ) ⊆ C := (WholeField.tsupport_smul_testOn_subset c' φ).trans hωG
      rw [zeroGFFTestCov_eq_of_isClopen ho₁ sdiff_subset hCo hC₁ hd₁ (c' • φ) hsupp,
        zeroGFFTestCov_eq_of_isClopen ho sdiff_subset hCo hC₂ hd (c' • φ) hsupp]
    -- (b) the hull mean is the union mean on `{hcap(A₂ − x)/2 = q, supp φ ∩ A₂ = ∅}`
    have hΦ : Measurable[hittingSigma] fun S : Set ℂ =>
        WholeField.hullClock ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' S) :=
      @Measurable.comp _ _ _ hittingSigma hittingSigma _ _ _ WholeField.measurable_hullClock
        (measurable_image_add (-x))
    set G₂ : Set Ω := {ω | WholeField.hullClock ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' A₂ ω) = (q : ℝ≥0∞)} ∩
      {ω | Disjoint (tsupport φ) (relClosureH (A₂ ω))} with hG₂_def
    have hG₂m : MeasurableSet[germSigma A₂ h0] G₂ := by
      refine comap_le_germSigma A₂ h0 _ (MeasurableSet.inter ?_ ?_)
      · exact ⟨_, hΦ (measurableSet_singleton _), rfl⟩
      · exact ⟨_, measurableSet_disjoint_relClosureH φ.hasCompactSupport.isCompact φ.tsupport_subset, rfl⟩
    have hclock : ∀ᵐ ω ∂P, WholeField.hullClock ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' A₂ ω) =
        (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) := by
      filter_upwards [hA₂K, hE.2.2.2.2, hτζ] with ω hω hp hlt
      rw [hω, image_add_neg_image_add]
      exact WholeField.hullClock_fwdHull_rpath hp.2.2.2.1 hp.1 (Coupling.coe_untopD_lt_zeta hlt)
    -- on `{τ = q}` the range lies in the hull
    have hA₁A₂ : ∀ᵐ ω ∂P, (τ ω).untopD 0 = q → A₁ ω ⊆ A₂ ω := by
      filter_upwards [hA₂K, hτζ, hA₁q, htr] with ω hω hlt h1 htrω hτq
      have hqζ : (q : ℝ≥0∞) < ζ ω := by rw [← hτq]; exact Coupling.coe_untopD_lt_zeta hlt
      rw [h1 hqζ, hω, hτq]
      rintro _ ⟨⟨t, ht, rfl⟩, hH⟩
      refine ⟨η ω t - x, ?_, by ring⟩
      rw [fwdHull_eq_fillH_of_isGeneratingTrace htrω hqζ]
      exact ⟨show 0 < (η ω t - x).im by simpa using (show 0 < (η ω t).im from hH),
        Or.inl (subset_closure ⟨t, ht, rfl⟩)⟩
    have hstepb : ∀ᵐ ω ∂P, ω ∈ G₂ → g₂ ω φ = g₀ ω φ := by
      refine ae_apply_eq_of_isCondZeroBoundaryGFF (P := P) hA₂𝒥 h𝒥le hhm hg₂.1 (hg₀m.mono hA𝒥 le_rfl) hg₂.2.2
        hg₀c φ hG₂m fun c' => ?_
      filter_upwards [hclock, hA₁A₂] with ω hcl hsub' hωG
      have hτq : (τ ω).untopD 0 = q := by
        have h2 : WholeField.hullClock ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' A₂ ω) = (q : ℝ≥0∞) := hωG.1
        rw [hcl] at h2
        exact_mod_cast h2
      have e : A₁ ω ∪ A₂ ω = A₂ ω := union_eq_right.2 (hsub' hτq)
      simp only [e]
    -- combine
    filter_upwards [hstepa, hstepb, hg₂id, hA₂K, hE.2.2.2.2, hA₁q, htr, hloc₂.2.1, hclock]
      with ω ha hb hc hω hp h1 htrω ⟨hA₂s, ho₂⟩ hcl hσq hqζ hsupp
    have hτq : (τ ω).untopD 0 = q := by rw [hτu]; exact min_eq_left hσq
    have hA₂f : A₂ ω = fillH (A₁ ω) := by
      rw [hω, hτq, fwdHull_eq_fillH_of_isGeneratingTrace htrω hqζ, ← Restart.fillH_image_add_real,
        Restart.image_add_real_eq, h1 hqζ, fillH_inter_H]
    have hG₂ : ω ∈ G₂ := by
      refine ⟨?_, ?_⟩
      · show WholeField.hullClock ((fun z : ℂ => z + ((-x : ℝ) : ℂ)) '' A₂ ω) = (q : ℝ≥0∞)
        rw [hcl, hτq]
      · show Disjoint (tsupport φ) (relClosureH (A₂ ω))
        rw [relClosureH_eq hA₂s ho₂, hA₂f]
        exact Set.disjoint_left.2 fun z hz hzf => (hsupp hz).2 hzf
    rw [ha hsupp, ← hb hG₂, hc φ (by rw [hA₂f]; exact hsupp), huτq ω hτq, hτq]
  -- all stops at once
  have hall : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (q : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ H \ fillH (A₁ ω) → g ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [ae_all_iff.2 fun n => hstop n φ, hσ.2.2.2] with ω hω hann hq hsupp
    obtain ⟨n, hn⟩ := hann q hq
    exact hω n hn hq hsupp
  -- swap "for every test function" and "almost surely"
  set D : Ω → Set ℂ := fun ω => if (q : ℝ≥0∞) < ζ ω then fillH (A₁ ω) else H with hD
  have hDq : ∀ ω, (q : ℝ≥0∞) < ζ ω → D ω = fillH (A₁ ω) := fun ω hq => by
    simp only [hD, hq, ↓reduceIte]
  have hDn : ∀ ω, ¬ (q : ℝ≥0∞) < ζ ω → H \ D ω = ∅ := fun ω hq => by
    simp only [hD, hq, ↓reduceIte, Set.sdiff_self]
  have key := WangWu.ae_forall_apply_eq_of_forall_ae (P := P) (g := g) (A := D) (m := m)
    (by
      filter_upwards [hg.2.1] with ω hω
      by_cases hq : (q : ℝ≥0∞) < ζ ω
      · rw [hDq ω hq]
        exact IsHarmonicDistOn.mono hω fun z hz => ⟨hz.1, fun h => hz.2 (subset_fillH (hA₁H ω) h)⟩
      · rw [hDn ω hq]
        exact IsHarmonicDistOn.mono hω (empty_subset _))
    (Eventually.of_forall fun ω => by
      by_cases hq : (q : ℝ≥0∞) < ζ ω
      · rw [hDq ω hq]
        exact isOpen_H_diff_fillH (hA₁b ω)
      · rw [hDn ω hq]
        exact isOpen_empty)
    (by
      filter_upwards [hE.2.2.2.2, hA₁fill] with ω hp hf
      by_cases hq : (q : ℝ≥0∞) < ζ ω
      · rw [hDq ω hq]
        exact (harmonicOnNhd_flowMean hp.2.2.2.1 hq (hu ω).1 x c hu₀).mono fun z hz =>
          ⟨hz.1, fun h => hz.2 (hf q le_rfl hq h)⟩
      · rw [hDn ω hq]
        intro z hz
        exact absurd hz (notMem_empty z))
    (fun φ => by
      filter_upwards [hall φ] with ω hω hsupp
      by_cases hq : (q : ℝ≥0∞) < ζ ω
      · rw [hDq ω hq] at hsupp
        exact hω hq hsupp
      · rw [hDn ω hq] at hsupp
        have hφ0 : φ = 0 := by
          ext z
          exact image_eq_zero_of_notMem_tsupport fun h => hsupp h
        subst hφ0
        simp)
  filter_upwards [key] with ω hω hq φ hsupp
  exact hω φ (by rw [hDq ω hq]; exact hsupp)

end Range

end SideHeight

end Sec7

end InteractingSLE
