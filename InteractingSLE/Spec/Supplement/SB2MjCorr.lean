/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MiCap

/-!
# SB2(2)'s explored set: the explored-side clauses of the stage pull-back

Packet PROVE-SB2-LCMEAN, round 7. `Ln.IsStagePullback c g A₁ A₂ A' (fwdHull w t)` asks, on the explored side,
that the complement of B's stage chart domain lie in `A₂` (`dom₂`) and that `A₂` correspond to the chordal hull of
the stopped piece (`corr₂ : c.2.1 v ∈ A₂ ↔ v ∈ fwdHull w t` for `v ∈ ℍ`). For round 6's explored set (`ℍ ∖ c'.dom`
on the capped launch event, `c'` the post-cap chart `= c.loewner Wr T`) both are deterministic consequences of the
Loewner extension of the chart:

* `continuous_stopDrv`: a regular driver stopped before its lifetime is continuous and starts at `0`;
* **`mem_dom_loewner_iff`**: for a conformal chart `c` and a continuous driver from `0`, `c.2.1 v` lies in the domain of
  `c.loewner W T` iff `v ∉ fwdHull W T`; `dom_loewner_subset`: that domain lies in `c.dom`;
* **`exists_capMean_hind_corr`**: round 6's `Mi.exists_capMean_hind` with, almost surely on the capped launch
  event, the clauses `corr₂` and `dom₂` for B's stage chart `sb2StageChart` and the stopped piece (`sb2StopDrv`,
  `sb2StopTime`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mj

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mi

/-! ### The Loewner extension of a chart -/

/-- **The domain of the Loewner extension of a chart**: `c.2.1 v` lies in the domain of `c.loewner W T` iff
`v ∉ fwdHull W T` (for `v ∈ ℍ`). -/
theorem mem_dom_loewner_iff {c : Chart} (hc : c.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) (hcl : (c.loewner W T).IsConformal) {v : ℂ} (hv : v ∈ H) :
    c.2.1 v ∈ ((c.loewner W T).dom : Set ℂ) ↔ v ∉ fwdHull W T := by
  rw [hcl.coe_dom]
  constructor
  · rintro ⟨y, hy, e⟩
    have hm := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hy
    have e' : fwdMapInv W T y = v := hc.injOn hm.1 hv e
    exact e' ▸ hm.2
  · intro hvK
    refine ⟨fwdMap W T v, QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT ⟨hv, hvK⟩, ?_⟩
    show c.2.1 (fwdMapInv W T (fwdMap W T v)) = c.2.1 v
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT ⟨hv, hvK⟩]

/-- The domain of the Loewner extension lies in the chart's domain. -/
theorem dom_loewner_subset {c : Chart} (hc : c.IsConformal) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 ≤ T) (hcl : (c.loewner W T).IsConformal) :
    ((c.loewner W T).dom : Set ℂ) ⊆ c.dom := by
  rw [hcl.coe_dom, hc.coe_dom]
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨fwdMapInv W T y, (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hy).1, rfl⟩

/-! ### The stopped driver -/

/-- The driver of a regular piece stopped at an own time before its lifetime is continuous and starts at `0`. -/
theorem continuous_stopDrv {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hD : IsRegularDriver D) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < D.2) :
    Continuous (fun x : ℝ => D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) D.2)).toNNReal) ∧
      (fun x : ℝ => D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) D.2)).toNNReal) 0 = 0 := by
  have hm : min (τ : ℝ≥0∞) D.2 = τ := min_eq_left hτ.le
  have e : (fun x : ℝ => D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) D.2)).toNNReal) =
      fun x : ℝ => D.1 (min x.toNNReal τ) := by
    funext x
    rw [hm, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  rw [e]
  refine ⟨hD.1.comp_continuous (continuous_real_toNNReal.min continuous_const) fun x => ?_, ?_⟩
  · show ((min x.toNNReal τ : ℝ≥0) : ℝ≥0∞) < D.2
    exact (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt hτ
  · simp only [Real.toNNReal_zero, zero_le, min_eq_left]
    exact hD.2.1

/-! ### SB2(2): the explored-side clauses -/

section SB2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s explored set with the explored-side clauses of the stage pull-back**: `Mi.exists_capMean_hind`
together with, almost surely on the capped launch event, `corr₂` (B's stage chart sends `v ∈ ℍ` into `A₂` iff `v` lies
in the chordal hull of the stopped piece) and `dom₂` (the complement of B's stage chart domain lies in `A₂`). -/
theorem exists_capMean_hind_corr (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) (hℓ : ℓ < (boundaryWalkSpec b jumps θ right).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (A₂ : Ω → Set ℂ) (c' : Ω → Chart),
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        (∀ v ∈ H, (sb2StageChart κ E b jumps θ right ℓ ω).2.1 v ∈ A₂ ω ↔
          v ∈ fwdHull (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)) ∧
        H \ ((sb2StageChart κ E b jumps θ right ℓ ω).dom : Set ℂ) ⊆ A₂ ω) ∧
      Measurable[mΩ, hittingSigma] A₂ ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      (∀ᵐ ω ∂P, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω ⊆ A₂ ω) ∧
      IsLocalSet A₂ (centredField h u₀) P ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) A₂ (centredField h u₀) P ∧
      (∀ ω, (c' ω).IsConformal) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        c' ω = (ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1) ∧
      (∀ ω, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ → H \ A₂ ω = (c' ω).dom) ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g →
        ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
            (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
          ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g ω φ = ∫ z, v z * φ z) →
            EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
              (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω))).mean
                (fwdMap (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)
                  ((sb2StageChart κ E b jumps θ right ℓ ω).1 z)) -
              chiC κ * ((QuantumZipper.logDerivFwd (sb2StopDrv E b jumps θ right ℓ τ ω)
                  (sb2StopTime E b jumps θ right ℓ τ ω) ((sb2StageChart κ E b jumps θ right ℓ ω).1 z)).im +
                (sb2StageChart κ E b jumps θ right ℓ ω).2.2 z)) (H \ A₂ ω)
  := by
  obtain ⟨A₂, c', hAm, hAc, hsub, hAl, hAloc, hc'c, hc'eq, hcompl, hmean⟩ :=
    exists_capMean_hind h12p h13 hθ right hκ hκ4 hb hh hE hER ℓ hℓ hwℓ τ hu₀
  refine ⟨A₂, c', ?_, hAm, hAc, hsub, hAl, hAloc, hc'c, hc'eq, hcompl, hmean⟩
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hPR := (stagedPiecesRegular_of_regular h13 hκ hb (hE' w hw) (hreg' w)).ae_pieceRegular
  filter_upwards [hc'eq, hPR] with ω hcω hPRω hω
  set c := sb2StageChart κ E b jumps θ right ℓ ω with hcdef
  have hcC : c.IsConformal :=
    (GW1RestartFinal.chart_boundaryRange_run w (fun j => StagedReg.regFam E w j ω) hPRω ℓ).1
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω.1
  have hch := chart_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ.le hwℓ
    (fun j => StagedReg.regFam E w j ω) hl τ
  obtain ⟨hWc₀, hW0₀⟩ := continuous_stopDrv (hreg' w ℓ ω) hω.2
  have hWc : Continuous (sb2StopDrv E b jumps θ right ℓ τ ω) := hWc₀
  have hW0 : sb2StopDrv E b jumps θ right ℓ τ ω 0 = 0 := hW0₀
  have hT : (0 : ℝ) ≤ sb2StopTime E b jumps θ right ℓ τ ω := NNReal.coe_nonneg _
  have hc'l : c' ω =
      c.loewner (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω) := by
    rw [hcω hω, hch]
    rfl
  have hcl :
      (c.loewner (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)).IsConformal :=
    hc'l ▸ hc'c ω
  have hcomp := hcompl ω hω
  have hmemA : ∀ x ∈ H, x ∈ A₂ ω ↔ x ∉ ((c' ω).dom : Set ℂ) := by
    intro x hx
    constructor
    · intro hxA hxD
      rw [← hcomp] at hxD
      exact hxD.2 hxA
    · intro hxD
      by_contra hxA
      exact hxD (hcomp ▸ ⟨hx, hxA⟩)
  refine ⟨fun v hv => ?_, fun z hz => ?_⟩
  · rw [hmemA _ (hcC.2.1 hv), hc'l, mem_dom_loewner_iff hcC hWc hW0 hT hcl hv, not_not]
  · refine (hmemA z hz.1).2 fun hzD => hz.2 ?_
    rw [hc'l] at hzD
    exact dom_loewner_subset hcC hWc hW0 hT hcl hzD

end SB2

end InteractingSLE.Theorem14.SB.Mj
