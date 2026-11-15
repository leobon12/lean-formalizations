/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdWire
import InteractingSLE.Spec.Sec7.SideVisClock

/-!
# The corner exclusion from the inner traversal's immediate shared-side hit

Packet PROVE-R6-FACE3, item (F2). `R6FdWire.R6SharedArcVisitMixedRemaining` asks that the *outer* relative trace has
visited the inner pocket's open shared arc by the relative time of the nested event. Here it is reduced to a
statement about the **inner pocket's own relative traversal alone**:

> `R6InnerSharedHitMixedRemaining`: almost surely on the inner test, the erased traversal of `U` lies on `U`'s open
> shared arc at relative times arbitrarily close to `0` (immediate shared-side hitting).

This is the standard boundary-hitting property of the two-seed SLE_κ′ of `U` (shared-side weight `ρ ≤ κ′/2 − 4 <
κ′/2 − 2`: the force-point process is a Bessel process of dimension `1 + 2(ρ + 2)/κ′ < 2` from `0`, whose zero set
accumulates at `0⁺`); it involves neither the outer pocket nor any chart.

* `erasedPath_mem_closure_visits`: a point of an erased path at a positive clock value below the clock of a visit time
  `T` is a limit of the trace at earlier visit times (the clock grows only on visits);
* `closure_visits_subset_image`: the trace at visit times up to the fibre end of `v` lies, with its closure, on the
  erased path over `[0, v]`;
* `exists_outer_relTip_eq_of_inner_hit` (pathwise): a point of `U`'s erased path before the visit time of the outer
  tip is a point of the outer erased path before that tip;
* **`r6SharedArcVisitMixedRemaining_of_innerHit`**, and with `R6FdWire`
  **`r6NonCornerMixedRemaining_of_innerHit`**: `R6InnerSharedHitMixedRemaining → R6Fc.R6NonCornerMixedRemaining`.
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

/-! ### Erased paths are limits of visits -/

section Erase

variable {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ}

/-- **A point of the erased path at a positive clock value `v ≤ ℓ(T)` (`T` a visit time) is a limit of the trace at
visit times `≤ T`.** -/
theorem erasedPath_mem_closure_visits (hP : IsErasurePocket η C x₀ y₀ τ σ) {T : ℝ} (hT : T ∈ visitSet η C τ σ)
    {v : ℝ} (hv0 : 0 < v) (hvT : v ≤ pocketClock η C τ σ T) :
    erasedPath η C τ σ v ∈ closure (η '' {t | t ∈ visitSet η C τ σ ∧ t ≤ T}) := by
  have hTσ : pocketClock η C τ σ T ≤ pocketClock η C τ σ σ := hP.monotone_clock hT.1.2.le
  have hvI : v ∈ Icc 0 (pocketClock η C τ σ σ) := ⟨hv0.le, hvT.trans hTσ⟩
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨ρ, hρ, hρE⟩ := Metric.continuousWithinAt_iff.1 (hP.continuousOn_erasedPath v hvI) δ hδ
  set v₁ := max (v - ρ / 2) 0 with hv₁
  have hv₁v : v₁ < v := max_lt (by linarith) hv0
  have hv₁I : v₁ ∈ Icc 0 (pocketClock η C τ σ σ) := ⟨le_max_right _ _, hv₁v.le.trans hvI.2⟩
  set a := pocketFibre η C τ σ v₁
  set b := pocketFibre η C τ σ v
  have ha := hP.clock_fibre hv₁I
  have hb := hP.clock_fibre hvI
  have hab : a < b := lt_of_le_of_ne (hP.monotone_fibre hv₁v.le) fun he => by
    have : pocketClock η C τ σ a = pocketClock η C τ σ b := by rw [he]
    rw [ha, hb] at this
    exact hv₁v.ne this
  obtain ⟨t, ht, htI⟩ := hP.exists_mem_of_clock_lt hab (by rw [ha, hb]; exact hv₁v.ne)
  have hta := hP.monotone_clock ht.1.le
  have htb := hP.monotone_clock ht.2.le
  rw [ha] at hta
  rw [hb] at htb
  have htT : t ≤ T := by
    have h1 : b ≤ pocketFibre η C τ σ (pocketClock η C τ σ T) := hP.monotone_fibre hvT
    rw [hP.fibre_clock_of_mem hT] at h1
    exact ht.2.le.trans h1
  refine ⟨η t, ⟨t, ⟨htI, htT⟩, rfl⟩, ?_⟩
  have he : erasedPath η C τ σ (pocketClock η C τ σ t) = η t := by
    show η (pocketFibre η C τ σ (pocketClock η C τ σ t)) = η t
    rw [hP.fibre_clock_of_mem htI]
  rw [← he, dist_comm]
  refine hρE ⟨(le_max_right _ _).trans hta, htb.trans hvI.2⟩ ?_
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [le_max_left (v - ρ / 2) 0]

/-- **The trace at visit times up to the fibre end of `v` lies, with its closure, on the erased path over
`[0, v]`.** -/
theorem closure_visits_subset_image (hP : IsErasurePocket η C x₀ y₀ τ σ) {v : ℝ}
    (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) :
    closure (η '' {t | t ∈ visitSet η C τ σ ∧ t ≤ pocketFibre η C τ σ v}) ⊆ erasedPath η C τ σ '' Icc 0 v := by
  have hcpt : IsCompact (erasedPath η C τ σ '' Icc 0 v) :=
    isCompact_Icc.image_of_continuousOn (hP.continuousOn_erasedPath.mono fun w hw => ⟨hw.1, hw.2.trans hv.2⟩)
  refine hcpt.isClosed.closure_subset_iff.2 ?_
  rintro _ ⟨t, ⟨htI, htv⟩, rfl⟩
  refine ⟨pocketClock η C τ σ t, ⟨hP.clock_nonneg htI.1.1.le, ?_⟩, ?_⟩
  · have := hP.monotone_clock htv
    rwa [hP.clock_fibre hv] at this
  · show η (pocketFibre η C τ σ (pocketClock η C τ σ t)) = η t
    rw [hP.fibre_clock_of_mem htI]

end Erase

/-! ### From the inner traversal to the outer one -/

section Bridge

variable {Ω : Type*}

/-- **A point of the inner erased path before the visit time of the outer tip is a point of the outer erased path
before that tip** (pathwise): if the outer relative tip at `u` lies in the contained pocket `U`, then for some `ε > 0`
every inner relative tip at a relative time in `(0, ε)` is an outer relative tip at a relative time in `[0, u]`. -/
theorem exists_outer_relTip_eq_of_inner_hit {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ' : ℂ → ℂ} {ω : Ω} (hcf : IsOuterCfg (R ω) (L ω) r W (η ω))
    (hcfg' : IsCfPocketConfig (R' ω) (L' ω) r' W (η ω)) (hψ' : IsCfJordan (R' ω) (L' ω) r' ψ')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r) {u : ℝ} (hu0 : 0 ≤ u)
    (hrel : relTip R L r η u ω ∈ cfPocket (R' ω) (L' ω) r') :
    ∃ ε > 0, ∀ u' ∈ Ioo 0 ε, ∃ u₁ : ℝ, 0 ≤ u₁ ∧ u₁ ≤ u ∧ relTip R L r η u₁ ω = relTip R' L' r' η u' ω := by
  have hPC := hcf.erase
  set L₀ := pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) with hL₀def
  have hL₀ : 0 < L₀ := hPC.clock_σ_pos
  obtain ⟨hPU, -⟩ := R5Ref.pocket_of_cfg (Ω := Ω) (R := R') (L := L') (W := fun _ => W) (η := η)
    (ψ := fun _ => ψ') (ω := ω) hcfg' hψ'
  have hEU := isErasurePocket_of_isReversePocket hPU hcfg'.attach
  set LU := pocketClock (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1))
    (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0)) with hLUdef
  have hLU : 0 < LU := hEU.clock_σ_pos
  set T := pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (clockOf L₀ u) with hTdef
  have hT0 : 0 ≤ T := hPC.nonneg.trans (hPC.fibre_mem _).1
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
      η ω '' {t | t ∈ visitSet (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) ∧ t ≤ T} := by
    rintro _ ⟨t, ⟨htI, htT⟩, rfl⟩
    exact ⟨t, ⟨hPC.mem_visitSet (hPU.nonneg.trans htI.1.1.le) (hsub htI.2), htT⟩, rfl⟩
  have hvC := clockOf_mem_Ico hL₀ hu0
  obtain ⟨w, hw, hwe⟩ := closure_visits_subset_image hPC ⟨hvC.1, hvC.2.le⟩ (closure_mono hsubV hcl)
  have hwL : w < L₀ := hw.2.trans_lt hvC.2
  refine ⟨w / (L₀ - w), div_nonneg hw.1 (sub_pos.2 hwL).le, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have := strictMonoOn_clockOf hL₀ (mem_Ici.2 hu0) (mem_Ici.2 (div_nonneg hw.1 (sub_pos.2 hwL).le)) hlt
    rw [PocketLife.clockOf_div_sub hL₀ hwL] at this
    linarith [hw.2]
  · show erasedPath _ _ _ _ (clockOf L₀ (w / (L₀ - w))) = _
    rw [PocketLife.clockOf_div_sub hL₀ hwL, hwe]
    rfl

end Bridge

/-! ### The named input and the wiring -/

/-- **Named, unproved: the inner pocket's traversal hits its open shared arc immediately** (the corrected (F2) input,
mixed shapes; the binders of `R6Fc.R6NonCornerMixedRemaining` that concern the inner pocket): almost surely on the
inner test, the erased traversal of `U = cfPocket (innerRight k rL R M_R) (innerLeft k rR L M_L) (rt s)` lies on `U`'s
open shared arc (`sharedArc`) at relative times in `(0, ε)` for every `ε > 0`. Mathematically: `U`'s relative
traversal is the two-seed SLE_κ′ with shared-side weight `≤ κ′/2 − 4 < κ′/2 − 2`, whose shared-side force-point
process is a Bessel process of dimension `< 2` from `0` (zero set accumulating at `0⁺`). -/
def R6InnerSharedHitMixedRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (A' : Set Ω) (s : ℚ),
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω)) →
      ∀ᵐ ω ∂P, ω ∈ A' → ∀ ε : ℝ, 0 < ε → ∃ u' ∈ Ioo 0 ε,
        relTip (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η u' ω ∈
          sharedArc k rL (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)

/-- **The outer trace visits the inner open shared arc, from the inner traversal's immediate hit.** -/
theorem r6SharedArcVisitMixedRemaining_of_innerHit {k rL rR c c' : ℝ}
    (hI : R6InnerSharedHitMixedRemaining.{u} k rL rR c c') : R6SharedArcVisitMixedRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML r A A' ψ ψ' s q hA hA'
  filter_upwards [hI hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML A' s
    fun ω hω => (hA' ω hω).1] with ω hω hωA hωA' hωN
  obtain ⟨-, -, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  obtain ⟨ε, hε, hall⟩ := exists_outer_relTip_eq_of_inner_hit (hA ω hωA).1 (hA' ω hωA').1 (hA' ω hωA').2 hsub hu0
    hrel
  obtain ⟨u', hu', hhit⟩ := hω hωA' ε hε
  obtain ⟨u₁, hu₁0, hu₁u, he⟩ := hall u' hu'
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := ((hA ω hωA).1.props (hA ω hωA).2).1
  refine ⟨u₁, hu₁0, ?_, by rw [he]; exact hhit⟩
  rw [← hcap]
  exact hγ.strictMonoOn_capClock.monotoneOn (mem_Ici.2 hu₁0) (mem_Ici.2 hu0) hu₁u

/-- **R.6's non-corner input from the inner traversal's immediate shared-side hit** (bounded outer pocket, mixed
shapes): `R6InnerSharedHitMixedRemaining → R6Fc.R6NonCornerMixedRemaining`. -/
theorem r6NonCornerMixedRemaining_of_innerHit {k rL rR c c' : ℝ}
    (hI : R6InnerSharedHitMixedRemaining.{u} k rL rR c c') : R6Fc.R6NonCornerMixedRemaining.{u} k rL rR c c' :=
  r6NonCornerMixedRemaining_of_sharedArcVisit (r6SharedArcVisitMixedRemaining_of_innerHit hI)

end InteractingSLE.Sec7.R6Fd
