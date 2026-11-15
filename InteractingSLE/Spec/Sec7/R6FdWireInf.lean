/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdPathInf
import InteractingSLE.Spec.Sec7.R6FdHit

/-!
# R.6's non-corner input for the outer pocket opening at the flow seed, from the inner hit

Packet PROVE-R6-FACE3. `R6Fc.R6NonCornerMixedInfRemaining` (outer pocket `C` opening at the flow seed, bounded
contained `U`) from the **same** named input as the bounded shape, `R6InnerSharedHitMixedRemaining` (the inner
traversal hits its open shared arc immediately): the inner-to-outer bridge (`R6FdHit`) with the outer erasure at
infinity, then `R6FdPathInf.nonCornerLandingInf_left/_right`.

* `closure_visits_subset_imageInf`, `exists_outer_relTipInf_eq_of_inner_hit`;
* **`r6NonCornerMixedInfRemaining_of_innerHit`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Fd

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen
  PocketStopWallsFin PocketStopSide R7StopIn

universe u

section EraseInf

variable {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ}

/-- **The trace at visit times up to the fibre end of `v` lies, with its closure, on the erased path over `[0, v]`**
(junction at infinity). -/
theorem closure_visits_subset_imageInf (hP : IsErasurePocketInf η C y₀ τ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) :
    closure (η '' {t | t ∈ visitSetInf η C τ ∧ t ≤ pocketFibreInf η C τ v}) ⊆ erasedPathInf η C τ '' Icc 0 v := by
  have hcpt : IsCompact (erasedPathInf η C τ '' Icc 0 v) :=
    isCompact_Icc.image_of_continuousOn (hP.continuousOn_erasedPath.mono fun w hw => ⟨hw.1, hw.2.trans_lt hv.2⟩)
  refine hcpt.isClosed.closure_subset_iff.2 ?_
  rintro _ ⟨t, ⟨htI, htv⟩, rfl⟩
  refine ⟨pocketClockInf η C τ t, ⟨hP.clock_nonneg htI.1.le, ?_⟩, ?_⟩
  · have := hP.monotone_clock htv
    rwa [hP.clock_fibre hv] at this
  · show η (pocketFibreInf η C τ (pocketClockInf η C τ t)) = η t
    rw [hP.fibre_clock_of_mem htI]

end EraseInf

section Bridge

variable {Ω : Type*}

/-- **A point of the inner erased path before the visit time of the outer tip is a point of the outer erased path
before that tip** (outer pocket opening at the flow seed, bounded inner pocket; pathwise). -/
theorem exists_outer_relTipInf_eq_of_inner_hit {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ' : ℂ → ℂ} {ω : Ω} (hcf : IsOuterCfgInf (R ω) (L ω) r W (η ω))
    (hcfg' : IsCfPocketConfig (R' ω) (L' ω) r' W (η ω)) (hψ' : IsCfJordan (R' ω) (L' ω) r' ψ')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r) {u : ℝ} (hu0 : 0 ≤ u)
    (hrel : relTipInf R L r η u ω ∈ cfPocket (R' ω) (L' ω) r') :
    ∃ ε > 0, ∀ u' ∈ Ioo 0 ε, ∃ u₁ : ℝ, 0 ≤ u₁ ∧ u₁ ≤ u ∧ relTipInf R L r η u₁ ω = relTip R' L' r' η u' ω := by
  have hPC := hcf.erase
  set L₀ := clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) with hL₀def
  have hL₀ : 0 < L₀ := hPC.clockEnd_pos
  obtain ⟨hPU, -⟩ := R5Ref.pocket_of_cfg (Ω := Ω) (R := R') (L := L') (W := fun _ => W) (η := η)
    (ψ := fun _ => ψ') (ω := ω) hcfg' hψ'
  have hEU := isErasurePocket_of_isReversePocket hPU hcfg'.attach
  set LU := pocketClock (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1))
    (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) with hLUdef
  have hLU : 0 < LU := hEU.clock_σ_pos
  have hvC := clockOf_mem_Ico hL₀ hu0
  set T := pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
    (clockOf L₀ u) with hTdef
  have hT0 : 0 ≤ T := hPC.fibre_nonneg hvC
  have hηT : η ω T ∈ cfPocket (R' ω) (L' ω) r' := hrel
  have hTU : T ∈ visitSet (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1))
      (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) := ⟨hPU.mem_Ioo_of_mem hT0 hηT, hηT⟩
  set vT := pocketClock (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1))
    (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) T with hvTdef
  have hvT0 : 0 < vT := SideVis.erasure_clock_pos_of_visit hEU hTU
  have hvTL : vT < LU := hEU.clock_lt_clock_σ ⟨hTU.1.1.le, hTU.1.2⟩
  refine ⟨vT / (LU - vT), div_pos hvT0 (sub_pos.2 hvTL), fun u' hu' => ?_⟩
  have hcT := PocketLife.clockOf_div_sub hLU hvTL
  have hmonoU := strictMonoOn_clockOf hLU
  have hv'0 : 0 < clockOf LU u' := by
    have := hmonoU (mem_Ici.2 le_rfl) (mem_Ici.2 hu'.1.le) hu'.1
    rwa [clockOf_zero] at this
  have hv'T : clockOf LU u' < vT := by
    have := hmonoU (mem_Ici.2 hu'.1.le) (mem_Ici.2 (div_pos hvT0 (sub_pos.2 hvTL)).le) hu'.2
    rwa [hcT] at this
  have hcl := erasedPath_mem_closure_visits hEU hTU hv'0 hv'T.le
  have hsubV : η ω '' {t | t ∈ visitSet (η ω) (cfPocket (R' ω) (L' ω) r')
      (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) ∧ t ≤ T} ⊆
      η ω '' {t | t ∈ visitSetInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) ∧
        t ≤ T} := by
    rintro _ ⟨t, ⟨htI, htT⟩, rfl⟩
    exact ⟨t, ⟨hPC.mem_visitSet (hPU.nonneg.trans htI.1.1.le) (hsub htI.2), htT⟩, rfl⟩
  obtain ⟨w, hw, hwe⟩ := closure_visits_subset_imageInf hPC hvC (closure_mono hsubV hcl)
  have hwL : w < L₀ := hw.2.trans_lt hvC.2
  refine ⟨w / (L₀ - w), div_nonneg hw.1 (sub_pos.2 hwL).le, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have := strictMonoOn_clockOf hL₀ (mem_Ici.2 hu0) (mem_Ici.2 (div_nonneg hw.1 (sub_pos.2 hwL).le)) hlt
    rw [PocketLife.clockOf_div_sub hL₀ hwL] at this
    linarith [hw.2]
  · show erasedPathInf _ _ _ (clockOf L₀ (w / (L₀ - w))) = _
    rw [PocketLife.clockOf_div_sub hL₀ hwL, hwe]
    rfl

end Bridge

/-- **R.6's non-corner input for the outer pocket opening at the flow seed, from the inner traversal's immediate
shared-side hit**: `R6InnerSharedHitMixedRemaining → R6Fc.R6NonCornerMixedInfRemaining`. -/
theorem r6NonCornerMixedInfRemaining_of_innerHit {k rL rR c c' : ℝ}
    (hI : R6InnerSharedHitMixedRemaining.{u} k rL rR c c') : R6Fc.R6NonCornerMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML r A A' ψ ψ' n s q hA hA'
  filter_upwards [hI hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML A' s
    fun ω hω => (hA' ω hω).1] with ω hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  obtain ⟨ε, hε, hall⟩ := exists_outer_relTipInf_eq_of_inner_hit (hA ω hωA).1 (hA' ω hωA').1 (hA' ω hωA').2 hsub
    hu0 hrel
  obtain ⟨u', hu', hhit⟩ := hω hωA' ε hε
  obtain ⟨u₁, hu₁0, hu₁u, he⟩ := hall u' hu'
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := ((hA ω hωA).1.props (hA ω hωA).2).1
  have harc : relTipInf R L r η u₁ ω ∈
      sharedArc k rL (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) := by rw [he]; exact hhit
  have hcap₁ : capClock (travAllInf R L r η ψ ω) u₁ ≤ q := by
    rw [← hcap]
    exact hγ.strictMonoOn_capClock.monotoneOn (mem_Ici.2 hu₁0) (mem_Ici.2 hu0) hu₁u
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hU := hA' ω hωA'
  rcases hmix with ⟨hdL, hdR⟩ | ⟨hdL, hdR⟩
  · have eR : innerRight k rL R MR ω = MR ω := by simp only [innerRight, hdL, ↓reduceIte]
    have eL : innerLeft k rR L ML ω = L ω := by simp only [innerLeft, not_lt.2 hdR, ↓reduceIte]
    simp only [sharedArc, hdL, ↓reduceIte] at harc
    simp only [hdL, ↓reduceIte]
    rw [eR, eL] at hU hsub hrel harc ⊢
    exact nonCornerLandingInf_left (W := fun ω t => W' t.toNNReal ω) (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) hωA hU.1 hU.2 hq0' hqlive hsub hu0 (by rw [hrtq]; exact hcap) hrel hu₁0
      (by rw [hrtq]; exact hcap₁) harc
  · have eR : innerRight k rL R MR ω = R ω := by simp only [innerRight, not_lt.2 hdL, ↓reduceIte]
    have eL : innerLeft k rR L ML ω = ML ω := by simp only [innerLeft, hdR, ↓reduceIte]
    simp only [sharedArc, not_lt.2 hdL, ↓reduceIte] at harc
    simp only [not_lt.2 hdL, ↓reduceIte]
    rw [eR, eL] at hU hsub hrel harc ⊢
    exact nonCornerLandingInf_right (W := fun ω t => W' t.toNNReal ω) (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) hωA hU.1 hU.2 hq0' hqlive hsub hu0 (by rw [hrtq]; exact hcap) hrel hu₁0
      (by rw [hrtq]; exact hcap₁) harc

end InteractingSLE.Sec7.R6Fd
