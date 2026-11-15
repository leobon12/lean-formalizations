/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxUnion
import InteractingSLE.Spec.Supplement.GW2OlmChain
import InteractingSLE.Spec.Supplement.GW2ShrFill
import InteractingSLE.Spec.Supplement.GW2GmPrefix
import InteractingSLE.Spec.Supplement.RelSafeS7
import InteractingSLE.Spec.Dimension.TraceBridge


/-!
# GW2's open lines: the launch image of the instance's union

Packet PROVE-GW2-STAGEMEAN, R120 round. Per sample, for the corrected schedule instance at root `0` with a strictly
time-ordered history:

* **`launchUnion_eq_of_launch`**: where the history succeeded, the current piece is launched in the chart `cL`, the
  conditional counterflow `Wk` has the launch datum's tip relation with the original counterflow (clock `ℓ`,
  `ℓ t₀ = s`), and the explored hull at the launch misses the retained hull (closures), the launch image of the
  instance's union at stage time `t` (below the candidate's cap and lifetime) is the conditional counterflow's inverted
  hull at `t₀` together with the current piece's own hull at `t` — the union of `GW2OmxPack.kernel_means`.

Ingredients: `GW2Omx.launchImage_union_eq`, `GW2Shr.invHull_eq_launch`, `Swc.succChart_inv_eq`,
`Gm.futureJoined_eq_joinDrv`, `Gm.joinTime_eq_schedTime`, `Swc.shiftDrive_joinDrv_eqOn`,
`RelSafeS.invHull_record_eq`. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule

/-- **The launch image of the instance's union** (root `0`, strictly time-ordered history, one sample). -/
theorem launchUnion_eq_of_launch {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
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
    (hd : Disjoint (closure (fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ)))) :
    GW2Olm.launchUnion c r l a cL t ω = Supp8.Q3Rel.invHull (fun u : ℝ => Wk u.toNNReal) (t₀ : ℝ) ∪
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
  have hcL : cL = succChart 0 Δ D k := by
    have h1 : GW2Olm.curLaunch c r l a ω = some (succChart spec.1 Δ D k, GW2Tip.specAngle spec k) := hl'
    rw [hl] at h1
    have h2 := (Prod.mk.inj (Option.some.inj h1)).1
    rw [h2]
    change succChart (rootPt r.1) Δ D k = succChart 0 Δ D k
    rw [hr0]
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
  have hinv : ∀ w ∈ H, cL.2.1 w = fwdMapInv (joinDrv Δ D k) (T : ℝ) w := by
    intro w hw
    rw [hcL, succChart_inv_eq 0 hck hw, hJT]
    simp only [Complex.ofReal_zero, zero_add]
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
  have hiff' : ∀ (q : ℝ≥0) (z : ℂ), ((succChart 0 Δ D k).trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z := by
    rw [← hcL]
    exact hiff
  have hd' : Disjoint (closure (fwdHull (joinDrv Δ D k) (joinTime Δ D k)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ t₀ : ℝ))) := by
    rw [hKT, hℓs]
    exact hd
  have himg0 := GW2Shr.invHull_eq_launch hck (hcL ▸ hext) hWk hWk0 hγk hW' hW'0 hγ' hℓc hℓm hℓ0 hiff' hd'
  rw [hℓs] at himg0
  have hWc : ContinuousOn (fun u => c.W u ω) {u | (u : ℝ≥0∞) < c.ζ ω} := hW'.continuousOn
  have hret := Supp8.RelSafeS.invHull_record_eq (s := c.s) (Wα := c.W) (ζα := c.ζ) (ω := ω) hW'0 hWc hsζ
  have himg : cL.2.1 '' Supp8.Q3Rel.invHull (fun u : ℝ => Wk u.toNNReal) (t₀ : ℝ) =
      Supp8.Q3Rel.invHull (rdrv (Supp8.GB6.gb6Rec c.s c.W c.ζ ω)) c.s := by
    rw [hret, hcL]
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
  have hU := launchImage_union_eq hconf hJ hJ0 hJ'c hJ'0 hTn t.coe_nonneg hinv heq hAk himg hPc hPeq
  -- the instance's union on the history's success
  have hB : GW2Sdi.schedUnionS c r l a t ω = Supp8.Q3Rel.invHull (rdrv (Supp8.GB6.gb6Rec c.s c.W c.ζ ω)) c.s ∪
      fwdHull J' ((T : ℝ) + t) := by
    simp only [GW2Sdi.schedUnionS, hold, ↓reduceIte, GW2Sdh.schedPhysUnion, NNReal.coe_add]
    rfl
  have hK : fwdHull (stopDrv (Δ k) (D k)) (t : ℝ) = fwdHull (fun u : ℝ => (D k).1 u.toNNReal) (t : ℝ) := by
    refine fwdHull_eq_of_eqOn t.coe_nonneg htst fun u hu => ?_
    refine Gm.stopDrv_eq_of_le ?_
    have h1 : u.toNNReal ≤ (min (Δ k) (D k).2).toNNReal := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hu.2
    calc ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((min (Δ k) (D k).2).toNNReal : ℝ≥0∞) := ENNReal.coe_le_coe.2 h1
      _ = min (Δ k) (D k).2 := ENNReal.coe_toNNReal hmin_ne
  change cL.1 '' (GW2Sdi.schedUnionS c r l a t ω ∩ (cL.dom : Set ℂ)) = _
  rw [hB, hU, hK]

end InteractingSLE.Theorem14.GW2Omx
