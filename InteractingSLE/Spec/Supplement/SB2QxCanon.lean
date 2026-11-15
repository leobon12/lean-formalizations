/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxRec
import InteractingSLE.Spec.Supplement.SB2MzIface
import InteractingSLE.Spec.Supplement.SB2MxIdent
import InteractingSLE.Spec.Supplement.SBTail2RetainFreeze
import InteractingSLE.Spec.Supplement.WalkUnionLawMain
import InteractingSLE.Spec.Supplement.GW1WalkExitGeometry
import InteractingSLE.Spec.ZhanGT4.CrosscutA3Swallow

/-!
# Record matching for the canonical driver of a tail stage (the record clause of `Mz.CanonIdentOn`)

Worker REVIEW-FABLE-T14 (the record matching of SB2(2)'s retained-law step, R13.7 item 3 / R14.4 item 4 of
PROVE-SB2-LCMEAN's handoff). At B's stage `ℓ`, on an event `G` of the marks after the stage (`Ms.stageMarks (ℓ + 1)`)
on which B launches at `ℓ` and the canonical driver `driverOf (c, Z)` (`Z` the field read in
`Mo.hullChart (fill K) x₀`) has positive lifetime, is continuous up to it, and has the chain clause `Mx.ChainFor` of
B's piece `ℓ` in B's stage coordinates (with the domain-chart and filling facts `Mx.ident_of_chainFor` uses):

* the data of the chain clause — the stage-coordinate retained set, the stage version of the canonical chart, B's
  trace and lifetime — are functions of B's runs through `ℓ + 1`, the upper run through `k`, `K` and `x₀`
  (`chainData_eq`);
* under the regular conditional law given `Ms.stageMarks (ℓ + 1)`, these are almost surely the conditioning sample's
  (`Retain.ae_ae_run_eq` for the regularized families, `StagedReg.ae_run_regHist`,
  `Mx.ae_ae_condExpKernel_set_eq`);
* two drivers with the chain clause for the same data agree (`Mx.ident_of_chainFor`), so the canonical record is
  kernel-a.s. constant (`ae_kernel_const_canonRec`), and `Qx.exists_regular_rec_version` gives the driver:

* **`exists_canonRec`**: a driver `Dr`, measurable for `Ms.stageMarks (ℓ + 1)` and regular at every sample, whose
  record is almost surely on `G` the canonical record — the record clause of `Mz.CanonIdentOn`.

R48: Theorem 1.2 enters only through `Theorem12ParamStatement` (the canonical driver code).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qx

open Restart Exist Exist.Staged Exist.StagedLaw Lu Mx Mz

/-! ### Drivers determined by their stopped versions -/

open Classical in
/-- A choice inside a dependent `if` only depends on the predicate. -/
theorem dite_choose_congr {β γ : Type*} {Q Q' : β → Prop} (d : γ) {F : β → γ} (h : Q = Q') :
    (if hex : ∃ x, Q x then F hex.choose else d) = (if hex : ∃ x, Q' x then F hex.choose else d) := by
  subst h; rfl

/-- The trace chosen by `LuM.trOf` only sees the driver before its lifetime. -/
theorem trOf_congr {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h2 : e.2 = e'.2)
    (h1 : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e.2 → e.1 s = e'.1 s) : LuM.trOf e = LuM.trOf e' := by
  have hgen : ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace e.1 e.2 η ↔ IsGeneratingTrace e'.1 e'.2 η := by
    intro η
    rw [← h2]
    unfold IsGeneratingTrace
    refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun t => imp_congr_right fun ht => ?_
    obtain ⟨s, hs0, hts, hsT⟩ := ENNReal.lt_iff_exists_real_btwn.1 ht
    have hfw : QuantumZipper.fwdHull (fun r : ℝ => e.1 r.toNNReal) t =
        QuantumZipper.fwdHull (fun r : ℝ => e'.1 r.toNNReal) t := by
      refine ZhanGT4.A34.fwdHull_congr_of_lt (T₀ := s) t.2 ?_ fun r hr => h1 _ ?_
      · have := (ENNReal.lt_ofReal_iff_toReal_lt ENNReal.coe_ne_top).1 hts
        simpa using this
      · refine lt_of_le_of_lt ?_ hsT
        rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hr.1]
        exact ENNReal.ofReal_le_ofReal hr.2.le
    rw [hfw]
  have hpred : (fun η : ℝ≥0 → ℂ => IsGeneratingTrace e.1 e.2 η ∧ (e.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) =
      fun η => IsGeneratingTrace e'.1 e'.2 η ∧ (e'.2 = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
    funext η
    rw [hgen η, h2]
  unfold LuM.trOf
  exact dite_choose_congr (F := id) 0 hpred

/-- Equal retained data (the driver stopped at its lifetime): equal lifetimes and equal drivers up to it. -/
theorem eq_of_retOf_eq {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h : retOf ⊤ e = retOf ⊤ e') :
    e.2 = e'.2 ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ e.2 → e.1 s = e'.1 s := by
  have h2 : min ⊤ e.2 = min ⊤ e'.2 := congrArg (fun x => x.2.1) h
  rw [min_eq_right le_top, min_eq_right le_top] at h2
  refine ⟨h2, fun s hs => ?_⟩
  have h1 := congrFun (congrArg Prod.fst h) s
  simp only [retOf, min_eq_right (le_top : e.2 ≤ ⊤), min_eq_right (le_top : e'.2 ≤ ⊤)] at h1
  rw [← h2, min_eq_left hs, ENNReal.toNNReal_coe] at h1
  exact h1

/-- Records of drivers equal up to their common lifetime are equal. -/
theorem recOf_top_eq_of_eqOn {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h2 : e.2 = e'.2)
    (h1 : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ e.2 → e.1 s = e'.1 s) : recOf ⊤ e = recOf ⊤ e' := by
  unfold recOf retOf readRec
  simp only [min_eq_right (le_top : e.2 ≤ ⊤), le_top, decide_true, ← h2]
  refine Prod.ext (funext fun q => ?_) rfl
  have hne : min ((q : ℝ).toNNReal : ℝ≥0∞) e.2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  refine h1 _ ?_
  rw [ENNReal.coe_toNNReal hne]
  exact min_le_right _ _

/-- Two drivers equal before a common positive lifetime and continuous up to it are equal up to it. -/
theorem eqOn_le_of_eqOn_lt {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (h2 : e.2 = e'.2) (hpos : e.2 ≠ 0)
    (h1 : ∀ s : ℝ≥0, (s : ℝ≥0∞) < e.2 → e.1 s = e'.1 s)
    (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ e.2}) (hc' : ContinuousOn e'.1 {s | (s : ℝ≥0∞) ≤ e'.2}) :
    ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ e.2 → e.1 s = e'.1 s := by
  intro s hs
  rcases hs.lt_or_eq with hlt | heq
  · exact h1 s hlt
  have hs0 : 0 < s := by
    rw [pos_iff_ne_zero]; rintro rfl; exact hpos (by rw [← heq]; rfl)
  have hmem : s ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ e.2} := heq.le
  have hmem' : s ∈ {s : ℝ≥0 | (s : ℝ≥0∞) ≤ e'.2} := by rw [← h2]; exact heq.le
  have hlim : Tendsto e.1 (𝓝[<] s) (𝓝 (e.1 s)) :=
    ((hc s hmem).mono fun x (hx : x < s) => (by
      show (x : ℝ≥0∞) ≤ e.2; rw [← heq]; exact ENNReal.coe_le_coe.2 hx.le)).tendsto
  have hlim' : Tendsto e'.1 (𝓝[<] s) (𝓝 (e'.1 s)) :=
    ((hc' s hmem').mono fun x (hx : x < s) => (by
      show (x : ℝ≥0∞) ≤ e'.2; rw [← h2, ← heq]; exact ENNReal.coe_le_coe.2 hx.le)).tendsto
  have hev : e.1 =ᶠ[𝓝[<] s] e'.1 := by
    filter_upwards [self_mem_nhdsWithin] with x (hx : x < s)
    exact h1 x (by rw [← heq]; exact ENNReal.coe_lt_coe.2 hx)
  have : (𝓝[<] s).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Iio' (⟨0, hs0⟩ : (Iio s).Nonempty)]
    exact Set.mem_Iic.2 le_rfl
  exact tendsto_nhds_unique (hlim.congr' hev) hlim'

/-! ### Kernel constancy from pathwise determination -/

/-- **Kernel constancy from pathwise determination.** If a datum `D` is kernel-a.s. the conditioning sample's, `G` is
an event of the conditioning σ-algebra, and on `G ∩ G₁` (`G₁` almost sure) the map `f` is a function of `D`, then
`f` is kernel-a.s. the conditioning sample's on `G`. -/
theorem ae_kernel_const_of_determined {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ) {α X : Type*} {D : Ω → α}
    {f : Ω → X} {G G₁ : Set Ω} (hG : MeasurableSet[𝓜] G) (hG₁ : ∀ᵐ ω ∂P, ω ∈ G₁)
    (hD : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), D ω = D ω₀)
    (hdet : ∀ ω ω', ω ∈ G → ω ∈ G₁ → ω' ∈ G → ω' ∈ G₁ → D ω = D ω' → f ω = f ω') :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ G → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), f ω = f ω₀ := by
  have hκG : ∀ᵐ ω₀ ∂P, ω₀ ∈ G → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), ω ∈ G := by
    filter_upwards [Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator (P := P) h𝓜 hG] with ω₀ h hω₀
    rw [indicator_of_mem hω₀, Pi.one_apply] at h
    exact (prob_compl_eq_zero_iff (h𝓜 _ hG)).2 h
  filter_upwards [hD, hκG, KernelTower.ae_ae_condExpKernel_of_ae h𝓜 hG₁, hG₁] with ω₀ hD₀ hκ₀ hG₁κ hG₁₀ hω₀
  filter_upwards [hD₀, hκ₀ hω₀, hG₁κ] with ω hDω hωG hωG₁
  exact hdet ω ω₀ hωG hωG₁ hω₀ hG₁₀ hDω


/-! ### The chain data are functions of the runs, the hull and the offset -/

/-- The physical prefix is a function of the run. -/
theorem prefixPhysSet_congr {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (h : ExplState.run κ b jumps spec D n = ExplState.run κ b jumps spec D' n) :
    SB.prefixPhysSet κ b jumps spec D n = SB.prefixPhysSet κ b jumps spec D' n := by
  unfold SB.prefixPhysSet
  rw [h]

section Canon

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
  {Ω : Type u} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)

/-- **The chain data are functions of the runs, the hull and the offset**: two samples with the same lower runs at
`ℓ` and `ℓ + 1` (B launching at `ℓ`), the same upper run at `k`, the same `K` and `x₀` have the same stage-coordinate
retained set, stage chart, B-trace and B-lifetime. -/
theorem chainData_eq {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {ω ω' : Ω}
    (hw₀ : ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω') ℓ)
    (hw₁ : ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) (ℓ + 1) =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω') (ℓ + 1))
    (hu : ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k =
      ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω') k)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
      (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hK : K ω = K ω') (hx : x₀ ω = x₀ ω') :
    Mn.stageRetained (Mn.walkStageChart κ b jumps E ℓ ω) (retY (κ := κ) b jumps E u l k ℓ ω) =
        Mn.stageRetained (Mn.walkStageChart κ b jumps E ℓ ω') (retY (κ := κ) b jumps E u l k ℓ ω') ∧
      stageChartOf (Mn.walkStageChart κ b jumps E ℓ ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)) =
        stageChartOf (Mn.walkStageChart κ b jumps E ℓ ω') (Mo.hullChart (fillH (K ω')) (x₀ ω')) ∧
      LuM.trOf (lowerD b jumps E ω ℓ) = LuM.trOf (lowerD b jumps E ω' ℓ) ∧
      (lowerD b jumps E ω ℓ).2 = (lowerD b jumps E ω' ℓ).2 := by
  have hc : Mn.walkStageChart κ b jumps E ℓ ω = Mn.walkStageChart κ b jumps E ℓ ω' := by
    unfold Mn.walkStageChart
    exact congrArg _ hw₀
  have hY : retY (κ := κ) b jumps E u l k ℓ ω = retY (κ := κ) b jumps E u l k ℓ ω' := by
    have hu' : ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩
        (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω) k =
        ExplState.run κ b jumps ⟨u, true, scheduleProgram 0 l⟩ (fun j => E ⟨u, true, scheduleProgram 0 l⟩ j ω') k := hu
    change SB.upperPrefix κ b jumps E u l k ω ∪ _ = SB.upperPrefix κ b jumps E u l k ω' ∪ _
    unfold SB.upperPrefix
    rw [prefixPhysSet_congr _ hu', prefixPhysSet_congr _ hw₀]
  have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω')
      (ℓ + 1)).2.2.2.1 ℓ ≠ none := by rwa [← hw₁]
  have ht := GW1WalkExit.instrTime_walk_of_launch hl
  have hr := retained_run_succ_self (κ := κ) (b := b) (jumps := jumps)
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ
  have hr' := retained_run_succ_self (κ := κ) (b := b) (jumps := jumps)
    (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω') ℓ
  simp only [hl, ↓reduceIte, ht] at hr
  simp only [hl', ↓reduceIte, ht] at hr'
  have hret : retOf ⊤ (lowerD b jumps E ω ℓ) = retOf ⊤ (lowerD b jumps E ω' ℓ) := by
    rw [← hr, ← hr', hw₁]
  obtain ⟨h2, h1⟩ := eq_of_retOf_eq hret
  refine ⟨by rw [hc, hY], by rw [hc, hK, hx], trOf_congr h2 fun s hs => h1 s hs.le, h2⟩

/-- The canonical driver of the stage field read in `Mo.hullChart (fill K) x₀`. -/
abbrev canonDrvAt (h : Ω → DistOn upperHalfPlaneOpens) (c : Ω → BoundaryWord) {K : Ω → Set ℂ}
    (x₀ : Ω → ℝ) (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (ω : Ω) :
    (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  driverOf h12p hκ (-(Real.pi / 2))
    (c ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))

/-- The facts at one sample used by the identification: B launches at `ℓ`; the stage version of the canonical chart is
a domain chart of the stage-coordinate retained complement, which is not in the filling; the canonical driver has the
chain clause of B's piece, positive lifetime, and is continuous up to it. -/
def ChainFacts (h : Ω → DistOn upperHalfPlaneOpens) (c : Ω → BoundaryWord) {K : Ω → Set ℂ}
    (x₀ : Ω → ℝ) (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (ω : Ω) :
    Prop :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
      (ℓ + 1)).2.2.2.1 ℓ ≠ none ∧
    IsDomainChart (H \ Mn.stageRetained (Mn.walkStageChart κ b jumps E ℓ ω) (retY (κ := κ) b jumps E u l k ℓ ω))
      (stageChartOf (Mn.walkStageChart κ b jumps E ℓ ω) (Mo.hullChart (fillH (K ω)) (x₀ ω))) ∧
    (∀ z ∈ H \ Mn.stageRetained (Mn.walkStageChart κ b jumps E ℓ ω) (retY (κ := κ) b jumps E u l k ℓ ω),
      z ∉ fillH (Mn.stageRetained (Mn.walkStageChart κ b jumps E ℓ ω) (retY (κ := κ) b jumps E u l k ℓ ω))) ∧
    ChainFor (Mn.stageRetained (Mn.walkStageChart κ b jumps E ℓ ω) (retY (κ := κ) b jumps E u l k ℓ ω))
      (stageChartOf (Mn.walkStageChart κ b jumps E ℓ ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)))
      (LuM.trOf (lowerD b jumps E ω ℓ)) (lowerD b jumps E ω ℓ).2 (canonDrvAt h12p hκ h c x₀ hKc hKp ω) ∧
    (canonDrvAt h12p hκ h c x₀ hKc hKp ω).2 ≠ 0 ∧
    ContinuousOn (canonDrvAt h12p hκ h c x₀ hKc hKp ω).1
      {s | (s : ℝ≥0∞) ≤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω).2}

/-- **Two samples with the same chain data and the chain facts have the same canonical record.** -/
theorem recOf_canon_eq_of_data {h : Ω → DistOn upperHalfPlaneOpens} {c : Ω → BoundaryWord} {K : Ω → Set ℂ}
    {x₀ : Ω → ℝ} {hKc : ∀ ω, IsCompact (K ω)} {hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)} {ω ω' : Ω}
    (hf : ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω)
    (hf' : ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω')
    (hw₀ : ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) ℓ =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω') ℓ)
    (hw₁ : ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω) (ℓ + 1) =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω') (ℓ + 1))
    (hu : ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k =
      ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω') k)
    (hK : K ω = K ω') (hx : x₀ ω = x₀ ω') :
    recOf ⊤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω) = recOf ⊤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω') := by
  obtain ⟨hl, hdom, hfill, hch, hpos, hcont⟩ := hf
  obtain ⟨-, -, -, hch', hpos', hcont'⟩ := hf'
  obtain ⟨hA, hC, hβ, hBL⟩ := chainData_eq E u l k ℓ hw₀ hw₁ hu hl hK hx
  rw [← hA, ← hC, ← hβ, ← hBL] at hch'
  obtain ⟨-, h2, h1⟩ := ident_of_chainFor (d := 0) hdom hdom hfill (fun z _ => (add_zero _).symm) hch hch' hpos hpos'
  exact recOf_top_eq_of_eqOn h2 (eqOn_le_of_eqOn_lt h2 hpos h1 hcont hcont')

/-- **Record matching for the canonical driver of a stage** (the record clause of `Mz.CanonIdentOn`): on an event `G`
of `Ms.stageMarks (ℓ + 1)` carrying the chain facts almost surely, a driver measurable for `Ms.stageMarks (ℓ + 1)` and
regular at every sample has almost surely the canonical record. -/
theorem exists_canonRec [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hRw : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hRu : StagedPiecesRegular κ b jumps P (upperSpec u l) (E (upperSpec u l)))
    (h𝓜 : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {c : Ω → BoundaryWord} (hc : Measurable c) {K : Ω → Set ℂ} {x₀ : Ω → ℝ} (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hK : @IsDyadicHitMeasurable Ω (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) K)
    (hx₀ : Measurable[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] x₀) {G : Set Ω}
    (hG : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] G)
    (hfacts : ∀ᵐ ω ∂P, ω ∈ G → ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω) :
    ∃ Dr : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, Measurable[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] Dr ∧
      (∀ ω, IsRegularDriver (Dr ω)) ∧
      ∀ᵐ ω ∂P, ω ∈ G → recOf ⊤ (Dr ω) = recOf ⊤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω) := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  -- measurability of the canonical driver
  have hKΩ : @IsDyadicHitMeasurable Ω mΩ K := fun n j => h𝓜 _ (hK n j)
  have hx₀Ω : Measurable x₀ := hx₀.mono h𝓜 le_rfl
  obtain ⟨-, hliftc, -, hdom, hfwd, hlift⟩ := @Mt.hullChart_k2Inputs Ω mΩ K x₀ hKΩ hKc hKp hx₀Ω
  have hZ : Measurable fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    @Chart.measurable_chartTransport_random' Ω mΩ _ (Mu.isConformal_canon x₀ hKc hKp) hdom hfwd hlift hliftc _ hh
      1 0 (chiC κ)
  have hD : Measurable (canonDrvAt h12p hκ h c x₀ hKc hKp) :=
    (measurable_driverOf h12p hκ (-(Real.pi / 2))).comp (hc.prodMk hZ)
  -- the runs, the hull and the offset are frozen under the kernels
  have hfw : ∀ n, n ≤ ℓ + 1 → ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀),
      ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) n =
        ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω₀) n := fun n hn =>
    Retain.ae_ae_run_eq w (WalkLaw.stagedPiecesRegular_regHist hRw) h𝓜
      ((pastSigma_mono w (StagedReg.regFam E w) hn).trans le_sup_right)
  have hfu : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀),
      ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω) k =
        ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω₀) k :=
    Retain.ae_ae_run_eq (upperSpec u l) (WalkLaw.stagedPiecesRegular_regHist hRu) h𝓜 le_sup_left
  have hrw := StagedReg.ae_run_regHist hRw
  have hru := StagedReg.ae_run_regHist hRu
  have hKfr := Mx.ae_ae_condExpKernel_set_eq (μ := P) h𝓜 hK fun ω => (hKc ω).isClosed
  have hxfr := Sec7.Aux122Disint.ae_ae_condExpKernel_eq (P := P) h𝓜 hx₀
  set D : Ω → _ := fun ω =>
    (ExplState.run κ b jumps w (lowerD b jumps E ω) ℓ, ExplState.run κ b jumps w (lowerD b jumps E ω) (ℓ + 1),
      ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k, K ω, x₀ ω) with hDdef
  have hDc : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k (ℓ + 1)) ω₀), D ω = D ω₀ := by
    filter_upwards [hfw ℓ (Nat.le_succ ℓ), hfw (ℓ + 1) le_rfl, hfu, hrw, hru, hKfr, hxfr,
      KernelTower.ae_ae_condExpKernel_of_ae h𝓜 hrw, KernelTower.ae_ae_condExpKernel_of_ae h𝓜 hru]
      with ω₀ h0 h1 h2 hrw₀ hru₀ hK₀ hx₀₀ hrwκ hruκ
    filter_upwards [h0, h1, h2, hK₀, hx₀₀, hrwκ, hruκ] with ω e0 e1 e2 eK ex erw eru
    simp only [hDdef]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext eK ex)))
    · change ExplState.run κ b jumps w (fun j => E w j ω) ℓ = ExplState.run κ b jumps w (fun j => E w j ω₀) ℓ
      rw [← erw ℓ, ← hrw₀ ℓ]; exact e0
    · change ExplState.run κ b jumps w (fun j => E w j ω) (ℓ + 1) =
        ExplState.run κ b jumps w (fun j => E w j ω₀) (ℓ + 1)
      rw [← erw (ℓ + 1), ← hrw₀ (ℓ + 1)]; exact e1
    · change ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k =
        ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k
      rw [← eru k, ← hru₀ k]; exact e2
  have hconst := ae_kernel_const_of_determined (P := P) h𝓜 (D := D)
    (f := fun ω => recOf ⊤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω))
    (G₁ := {ω | ω ∈ G → ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h c x₀ hKc hKp ω}) hG hfacts hDc
    (fun ω ω' hωG hω₁ hω'G hω'₁ hDe => by
      have e := hDe
      simp only [hDdef, Prod.mk.injEq] at e
      obtain ⟨e0, e1, e2, eK, ex⟩ := e
      exact recOf_canon_eq_of_data h12p hκ E u l k ℓ (hω₁ hωG) (hω'₁ hω'G) e0 e1 e2 eK ex)
  have hcont : ∀ᵐ ω ∂P, ω ∈ G → ContinuousOn (canonDrvAt h12p hκ h c x₀ hKc hKp ω).1
      {s | (s : ℝ≥0∞) ≤ (canonDrvAt h12p hκ h c x₀ hKc hKp ω).2} := by
    filter_upwards [hfacts] with ω hω hωG
    exact (hω hωG).2.2.2.2.2
  exact exists_regular_rec_version h𝓜 hD (fun ω => Mz.isRegularDriver_driverOf h12p hκ _ _) hcont hconst

end Canon

end InteractingSLE.Theorem14.SB.Qx
