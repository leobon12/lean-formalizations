/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxUnion2

/-!
# GW2's open lines: the launch chart's domain and the continuation of the retained counterflow

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start dilation). Per sample (root `0`, strict history), at a launch
`cL` of the current piece with the launch datum's tip relation:

* **`launch_dom_cont`**: the domain of `cL` is `ℍ ∖ K_T` (the explored hull at the launch), and wherever the
  explored hull at `T` and the original counterflow's hull at `ℓ q` have disjoint closures, `cL⁻¹` carries the
  conditional counterflow's hull at `q` onto the original counterflow's hull at `ℓ q` (`GW2Shr.invHull_eq_launch`).
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

/-- **The launch chart's domain and the continuation of the retained counterflow** (per sample). -/
theorem launch_dom_cont {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2))
    (ω : Ω) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ')
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : Monotone ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) :
    ((cL.dom : Set ℂ) = H \ fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)) ∧
      ∀ q : ℝ≥0, Disjoint (closure (fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
          (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ))) →
        cL.2.1 '' Supp8.Q3Rel.invHull (fun u : ℝ => Wk u.toNNReal) (q : ℝ) =
          Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ) := by
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
  have hdom : (cL.dom : Set ℂ) = H \ fwdHull J' (T : ℝ) := by
    rw [hconf.coe_dom, ← hKT, hJT]
    have himgH : cL.2.1 '' H = fwdMapInv (joinDrv Δ D k) (T : ℝ) '' H :=
      image_congr fun w hw => hinv w hw
    rw [himgH, QuantumZipper.RS.image_fwdMapInv_H hJ hJ0 hTn]
  refine ⟨hdom, fun q hq => ?_⟩
  have hd' : Disjoint (closure (fwdHull (joinDrv Δ D k) (joinTime Δ D k)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ))) := by
    rw [hKT]
    exact hq
  have h := GW2Shr.invHull_eq_launch hck (hcL ▸ hext) hWk hWk0 hγk hW' hW'0 hγ' hℓc hℓm hℓ0 hiff' hd'
  rw [hcL]
  exact h

end InteractingSLE.Theorem14.GW2Omx
