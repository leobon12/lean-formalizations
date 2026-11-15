/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkHull
import InteractingSLE.Spec.Supplement.GW2OmxUnion2
import InteractingSLE.Spec.Supplement.GW2TjRoot

/-!
# The root-`x` kernel port (D38): the launch image of the root-`x` union

Packet PROVE-GW2-GEOM2, round 11 (STAGEMEAN's `GW2Omx.launchUnion_eq_of_launch` at a root `x`). At the root
`x = rootPt r.1` the launch chart's inverse is `x + fwdMapInv` (`Swc.succChart_inv_eq x`), and the explored hull of
the union is translated to `x` (RELDET's `GW2Rd.schedUnionX`, the union of RELDET's root-`x` kernel).

* `transChart` (the chart pre-composed with the translation by `x`), `isConformal_transChart`,
  `coe_dom_transChart`, `image_transChart`;
* **`launchImage_union_eqX`**: STAGEMEAN's `launchImage_union_eq` for a chart whose inverse is `x + fwdMapInv`;
* `launchUnionX` (the launch image of `GW2Rd.schedUnionX`), **`launchUnion_eq_of_launchX`**: per sample at a root
  `x ≥ 0`, under the root-`0` hypotheses with the explored hull translated to `x`, the counterflow's trace off the pole
  `−1/x` on `[0, s]` and the pole off its closed hull at `s`, the launch image of the root-`x` union at stage time `t`
  is `invHull W_k t₀` together with the current piece's hull at `t` (`GW2Xk.chartInv_image_invHullX`).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Xk

open GW2Omx GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist
  Exist.Staged Exist.StagedLaw Sec5.Prop513Schedule

/-! ### A chart pre-composed with a translation -/

/-- **The chart pre-composed with the translation by `x`**: forward map `z ↦ c(z + x)`, inverse `w ↦ c⁻¹(w) − x`. -/
def transChart (c : Chart) (x : ℝ) : Chart :=
  (fun z => c.1 (z + x), fun w => c.2.1 w - x, fun z => c.2.2 (z + x))

theorem isConformal_transChart {c : Chart} (hc : c.IsConformal) (x : ℝ) : (transChart c x).IsConformal := by
  refine ⟨hc.1.sub_const _, fun w hw => ?_, fun w hw => ?_⟩
  · show (0 : ℝ) < (c.2.1 w - x).im
    have h : (0 : ℝ) < (c.2.1 w).im := hc.2.1 hw
    simpa using h
  · show c.1 (c.2.1 w - x + x) = w
    rw [sub_add_cancel]
    exact hc.2.2 w hw

theorem coe_dom_transChart {c : Chart} (hc : c.IsConformal) (x : ℝ) :
    ((transChart c x).dom : Set ℂ) = (fun z : ℂ => z - x) '' (c.dom : Set ℂ) := by
  rw [(isConformal_transChart hc x).coe_dom, hc.coe_dom, image_image]
  rfl

/-- The chart's image of a set through its domain, read in the translated chart. -/
theorem image_transChart {c : Chart} (hc : c.IsConformal) (x : ℝ) (S : Set ℂ) :
    c.1 '' (S ∩ (c.dom : Set ℂ)) =
      (transChart c x).1 '' ((fun z : ℂ => z - x) '' S ∩ ((transChart c x).dom : Set ℂ)) := by
  rw [coe_dom_transChart hc x, ← image_inter (sub_left_injective (b := (x : ℂ))), image_image]
  refine image_congr fun z _ => ?_
  show c.1 z = c.1 (z - x + x)
  rw [sub_add_cancel]

/-- **STAGEMEAN's launch image of the stage union, for a chart whose inverse is `x + fwdMapInv J T`.** -/
theorem launchImage_union_eqX {cL : Chart} (hc : cL.IsConformal) {x : ℝ} {J J' : ℝ → ℝ} (hJ : Continuous J)
    (hJ0 : J 0 = 0) (hJ' : Continuous J') (hJ'0 : J' 0 = 0) {T t : ℝ} (hT : 0 ≤ T) (ht : 0 ≤ t)
    (hinv : ∀ w ∈ H, cL.2.1 w = (x : ℂ) + fwdMapInv J T w) (heq : EqOn J J' (Icc 0 T)) {Ak Aret : Set ℂ}
    (hAk : Ak ⊆ H) (himg : cL.2.1 '' Ak = Aret) {Pd : ℝ → ℝ} (hP : Continuous Pd)
    (hPeq : EqOn (fun r => J' (T + r) - J' T) Pd (Icc 0 t)) :
    cL.1 '' ((Aret ∪ (fun z : ℂ => (x : ℂ) + z) '' fwdHull J' (T + t)) ∩ (cL.dom : Set ℂ)) =
      Ak ∪ fwdHull Pd t := by
  have hc' := isConformal_transChart hc x
  have hinv' : ∀ w ∈ H, (transChart cL x).2.1 w = fwdMapInv J T w := fun w hw => by
    show cL.2.1 w - x = fwdMapInv J T w
    rw [hinv w hw]; ring
  have himg' : (transChart cL x).2.1 '' Ak = (fun z : ℂ => z - x) '' Aret := by
    rw [← himg, image_image]
    rfl
  have hset : (fun z : ℂ => z - x) '' (Aret ∪ (fun z : ℂ => (x : ℂ) + z) '' fwdHull J' (T + t)) =
      (fun z : ℂ => z - x) '' Aret ∪ fwdHull J' (T + t) := by
    rw [image_union, image_image]
    simp only [add_sub_cancel_left, image_id']
  rw [image_transChart hc x, hset]
  exact launchImage_union_eq hc' hJ hJ0 hJ' hJ'0 hT ht hinv' heq hAk himg' hP hPeq

/-! ### The launch image of the root-`x` union -/

/-- **The launch image of RELDET's root-`x` union** `GW2Rd.schedUnionX` (the root-`x` analogue of
`GW2Olm.launchUnion`). -/
def launchUnionX {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (cL : Chart) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  cL.1 '' (GW2Rd.schedUnionX c r l a (historyTime c r l) t ω ∩ (cL.dom : Set ℂ))

/-- **The launch image of the root-`x` union** (root `x ≥ 0`, strictly time-ordered history, one sample). -/
theorem launchUnion_eq_of_launchX {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx0 : 0 ≤ rootPt r.1)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2))
    (t : ℝ≥0) (ω : Ω) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL) (htcap : t < candidateCap c r a)
    (htζ : (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : Monotone ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (hℓs : ℓ t₀ = c.s)
    (hden : ∀ u ≤ c.s, (rootPt r.1 : ℂ) * γ' u + 1 ≠ 0)
    (hpole : 0 < rootPt r.1 → ((Sec5.CrossRestart.mobPole (rootPt r.1) 1 : ℝ) : ℂ) ∉
      closure (fwdHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ)))
    (hd : Disjoint (closure ((fun z : ℂ => z + (rootPt r.1 : ℝ)) ''
        fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ)))) :
    launchUnionX c r l a cL t ω = Supp8.Q3Rel.invHull (fun u : ℝ => Wk u.toNNReal) (t₀ : ℝ) ∪
      fwdHull (fun u : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 u.toNNReal) (t : ℝ) := by
  set spec := GW2Olm.futSpec c r l a with hspec
  set Δ := specDelta spec with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set k := GW2Olm.curIdx c r l with hk
  set L := futureProgram c r l a with hL
  set T : ℝ≥0 := historyTime c r l with hT
  have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
  have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
  have hgw : spec.2.1 = true := rfl
  have hprog := isFlowProg_spec (rootPt r.1) true L
  have hΔt : ∀ j, Δ j ≠ ⊤ := specDelta_ne_top _
  have hs : AllSucc Δ D k := by
    by_contra hn
    have h0 := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog hΔt D
      (show k < spec.2.2.length by omega)).2 hn
    have h1 : GW2Olm.curLaunch c r l a ω = none := h0
    rw [h1] at hl
    simp at hl
  have hl' := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) hgw hprog hΔt D
    (show k < spec.2.2.length by omega)).1 hs
  have hcL : cL = succChart (rootPt r.1) Δ D k := by
    have h1 : GW2Olm.curLaunch c r l a ω = some (succChart spec.1 Δ D k, GW2Tip.specAngle spec k) := hl'
    rw [hl] at h1
    have h2 := (Prod.mk.inj (Option.some.inj h1)).1
    rw [h2]
  have hck : ∀ j < k, Continuous (stopDrv (Δ j) (D j)) ∧ stopDrv (Δ j) (D j) 0 = 0 :=
    fun j hj => hc j (Nat.lt_succ_of_lt hj)
  obtain ⟨hJ, hJ0⟩ := continuous_joinDrv hck
  obtain ⟨hJ1, hJ10⟩ := continuous_joinDrv hc
  have hTOh : TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  have hTOf : TimeOrdered 0 L := Gm.timeOrdered_of_pairwise_lt (GW2Olm.pairwise_lt_futureProgram c r l a hord)
  have hJT : joinTime Δ D k = (T : ℝ) := by
    have h1 : joinTime (specDelta (schedSpec (rootPt r.1) L)) D k = schedTime 0 L k :=
      Gm.joinTime_eq_schedTime (rootPt r.1) hTOf (by omega) hs
    refine h1.trans ?_
    have h2 : schedTime 0 L k = schedTime 0 (historyProgram c r l) (historyProgram c r l).length :=
      schedTime_append 0 _ le_rfl
    rw [h2, Gm.schedTime_length_eq_lastTime, ← GW2Sde.historyTime_eq_lastTime]
  have hTn : (0 : ℝ) ≤ T := T.coe_nonneg
  -- the launch chart's inverse
  have hinv : ∀ w ∈ H, cL.2.1 w = (rootPt r.1 : ℂ) + fwdMapInv (joinDrv Δ D k) (T : ℝ) w := by
    intro w hw
    rw [hcL, succChart_inv_eq (rootPt r.1) hck hw, hJT]
  -- the explored driver
  set J' : ℝ → ℝ := fun u => GW2Rd.schedW c r l a u.toNNReal ω with hJ'def
  have hJ'f : ∀ u : ℝ, J' u = Gm.futureJoined c r l a ω u.toNNReal := fun u => by
    rw [hJ'def]
    exact congrFun (GW2Rd.schedW_of_oldSuccess c r l a hold) u.toNNReal
  obtain ⟨hFc, hF0⟩ := Gm.continuous_futureJoined c r l a ω
  have hJ'c : Continuous J' := by
    have e : J' = fun u => Gm.futureJoined c r l a ω u.toNNReal := funext hJ'f
    rw [e]
    exact hFc.comp continuous_real_toNNReal
  have hJ'0 : J' 0 = 0 := by rw [hJ'f, Real.toNNReal_zero, hF0]
  have hJ'j : ∀ u : ℝ, 0 ≤ u → u ≤ (T : ℝ) + candidateCap c r a → J' u = joinDrv Δ D (k + 1) u := by
    intro u hu0 hu
    rw [hJ'f]
    have hle : u.toNNReal ≤ historyTime c r l + candidateCap c r a := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact_mod_cast hu
    have h := Gm.futureJoined_eq_joinDrv c r l a ω hTOh hold hgood hle
    rw [h, Real.coe_toNNReal _ hu0]
    rfl
  have heq : EqOn (joinDrv Δ D k) J' (Icc 0 (T : ℝ)) := by
    intro u hu
    rw [hJ'j u hu.1 (hu.2.trans (le_add_of_nonneg_right (candidateCap c r a).coe_nonneg))]
    exact (joinDrv_eqOn (Δ := Δ) (D := D) k ⟨hu.1, hJT ▸ hu.2⟩).symm
  -- the retained set through the launch chart
  have hKT : fwdHull (joinDrv Δ D k) (joinTime Δ D k) = fwdHull J' (T : ℝ) := by
    rw [hJT]
    exact QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn hJ hJ'c hTn heq
  have hd' : Disjoint (closure ((fun z : ℂ => z + (rootPt r.1 : ℝ)) '' fwdHull (joinDrv Δ D k) (T : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ t₀ : ℝ))) := by
    have hKT' : fwdHull (joinDrv Δ D k) (T : ℝ) = fwdHull J' (T : ℝ) := by
      have h := hKT; rw [hJT] at h; exact h
    rw [hKT', hℓs]
    exact hd
  have himg0 := chartInv_image_invHullX hx0 hJ hJ0 hTn hinv hext hWk hWk0 hγk hW' hW'0 hγ' hℓc hℓm hℓ0 hiff
    (fun u hu => hden u (hℓs ▸ hu)) (fun hx => by rw [hℓs]; exact hpole hx) hd'
  rw [hℓs] at himg0
  have hWc : ContinuousOn (fun u => c.W u ω) {u | (u : ℝ≥0∞) < c.ζ ω} := hW'.continuousOn
  have hret := Supp8.RelSafeS.invHull_record_eq (s := c.s) (Wα := c.W) (ζα := c.ζ) (ω := ω) hW'0 hWc hsζ
  have himg : cL.2.1 '' Supp8.Q3Rel.invHull (fun u : ℝ => Wk u.toNNReal) (t₀ : ℝ) =
      Supp8.Q3Rel.invHull (rdrv (Supp8.GB6.gb6Rec c.s c.W c.ζ ω)) c.s := by
    rw [hret]
    exact himg0
  have hAk : Supp8.Q3Rel.invHull (fun u : ℝ => Wk u.toNNReal) (t₀ : ℝ) ⊆ H :=
    GW2Shr.invHull_subset_H (hWk.comp continuous_real_toNNReal) t₀.coe_nonneg
  -- the current piece
  have hΔk : Δ k = (candidateCap c r a : ℝ≥0∞) := futureProgram_delta c r l a
  obtain ⟨hPc, hP0⟩ := hc k (Nat.lt_succ_self k)
  have hmin_ne : min (Δ k) (D k).2 ≠ ⊤ := ne_top_of_le_ne_top (hΔt k) (min_le_left _ _)
  have htst : (t : ℝ) < stopTime (Δ k) (D k) := by
    have h1 : (t : ℝ≥0∞) < min (Δ k) (D k).2 := lt_min (by rw [hΔk]; exact_mod_cast htcap) htζ
    have h2 : t < (min (Δ k) (D k).2).toNNReal := by
      rwa [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hmin_ne]
    exact_mod_cast h2
  have hPeq : EqOn (fun u => J' ((T : ℝ) + u) - J' (T : ℝ)) (stopDrv (Δ k) (D k)) (Icc 0 (t : ℝ)) := by
    intro u hu
    have hcap : (t : ℝ) ≤ candidateCap c r a := by exact_mod_cast htcap.le
    have h1 : J' ((T : ℝ) + u) = joinDrv Δ D (k + 1) ((T : ℝ) + u) :=
      hJ'j _ (add_nonneg hTn hu.1) (by linarith [hu.2])
    have h2 : J' (T : ℝ) = joinDrv Δ D (k + 1) (T : ℝ) :=
      hJ'j _ hTn (le_add_of_nonneg_right (candidateCap c r a).coe_nonneg)
    have h3 := shiftDrive_joinDrv_eqOn (Δ := Δ) (D := D) hP0 ⟨hu.1, hu.2.trans htst.le⟩
    simp only [QuantumZipper.RS.shiftDrive, hJT] at h3
    simp only
    rw [h1, h2]
    exact h3
  have hU := launchImage_union_eqX hconf hJ hJ0 hJ'c hJ'0 hTn t.coe_nonneg hinv heq hAk himg hPc hPeq
  -- the instance's union on the history's success
  have hB : GW2Rd.schedUnionX c r l a T t ω = Supp8.Q3Rel.invHull (rdrv (Supp8.GB6.gb6Rec c.s c.W c.ζ ω)) c.s ∪
      (fun z : ℂ => (rootPt r.1 : ℂ) + z) '' fwdHull J' ((T : ℝ) + t) := by
    simp only [GW2Rd.schedUnionX, GW2Rd.schedHullX, hold, ↓reduceIte, GW2Rd.schedHull, NNReal.coe_add]
    rfl
  have hK : fwdHull (stopDrv (Δ k) (D k)) (t : ℝ) = fwdHull (fun u : ℝ => (D k).1 u.toNNReal) (t : ℝ) := by
    refine fwdHull_eq_of_eqOn t.coe_nonneg htst fun u hu => ?_
    refine Gm.stopDrv_eq_of_le ?_
    have h1 : u.toNNReal ≤ (min (Δ k) (D k).2).toNNReal := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hu.2
    calc ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((min (Δ k) (D k).2).toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.2 h1
      _ = min (Δ k) (D k).2 := ENNReal.coe_toNNReal hmin_ne
  change cL.1 '' (GW2Rd.schedUnionX c r l a T t ω ∩ (cL.dom : Set ℂ)) = _
  rw [hB, hU, hK]

end InteractingSLE.Theorem14.GW2Xk
