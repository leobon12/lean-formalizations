/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkGap
import InteractingSLE.Spec.Supplement.GW2OmxDil2

/-!
# The root-`x` kernel port (D38): the launch chart's domain and the continuation of the retained counterflow

Packet PROVE-GW2-GEOM2, round 11 (STAGEMEAN's `GW2Omx.launch_dom_cont` and `GW2Omx.disjoint_closure_of_lt_firstTipTime`
at a root `x`). On the datum's clock range, i.e. before the counterflow's first tip in the explored trace image
translated to `x`, and given the counterflow's visit to `x` (when `x > 0`):

* `den_of_lt_firstTipTimeX` (the trace is off the pole `−1/x`), `pole_of_lt_firstTipTimeX` (the pole is off the closed
  counterflow hull), **`disjoint_closure_of_lt_firstTipTimeX`** (the closed translated explored hull and the closed
  retained hull are disjoint);
* **`launch_dom_contX`**: the domain of `cL` is `ℍ ∖ (x + K_T)`, and `cL⁻¹` carries the conditional counterflow's
  hull at `q` onto the original counterflow's hull at `ℓ q` under the root-`x` conditions;
* **`launch_cont_of_rangeX`**: the continuation at every `q`, from the clock's range.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Xk

open GW2Omx GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist
  Exist.Staged Exist.StagedLaw Sec5.Prop513Schedule GW2Rd

variable {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-! ### The clock's range at a root `x` -/

section Range

variable {ω : Ω} {η ηe : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η)
  (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0) (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe)
  {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
    ((fun z : ℂ => (rootPt r.1 : ℂ) + z) '' (ηe '' Icc 0 (historyTime c r l))))
include hη hc h0 hηe hσ

omit hηe in
/-- Before the first tip in the translated explored image, the counterflow misses the translated explored trace. -/
theorem sep_of_lt_firstTipTimeX :
    ∀ t ∈ Icc 0 σ, ∀ u ∈ Icc 0 (historyTime c r l), η t * ((rootPt r.1 : ℂ) + ηe u) + 1 ≠ 0 := by
  intro t ht u hu hzero
  have hγt : η t ≠ 0 := by
    intro h0'
    rw [h0', zero_mul, zero_add] at hzero
    exact one_ne_zero hzero
  refine noContact_of_lt_firstTipTime hη hc h0 hσ ht.2 hγt ⟨ηe u, ⟨u, hu, rfl⟩, ?_⟩
  have e : η t * ((rootPt r.1 : ℂ) + ηe u) = -1 := eq_neg_of_add_eq_zero_left hzero
  calc (rootPt r.1 : ℂ) + ηe u = (η t)⁻¹ * (η t * ((rootPt r.1 : ℂ) + ηe u)) := by field_simp
    _ = -(η t)⁻¹ := by rw [e]; ring

/-- **Before the first tip in the translated explored image, the counterflow is off the pole `−1/x`.** -/
theorem den_of_lt_firstTipTimeX : ∀ u ≤ σ, (rootPt r.1 : ℂ) * η u + 1 ≠ 0 := by
  intro u hu
  have h := sep_of_lt_firstTipTimeX c r l hη hc h0 hσ u ⟨zero_le, hu⟩ 0 ⟨le_rfl, zero_le⟩
  rw [hηe.1, add_zero, mul_comm] at h
  exact h

/-- **With the counterflow's visit to `x > 0`, the pole `−1/x` is off the closed counterflow hull at `σ`.** -/
theorem pole_of_lt_firstTipTimeX (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * η τ + 1 = 0) :
    0 < rootPt r.1 → ((Sec5.CrossRestart.mobPole (rootPt r.1) 1 : ℝ) : ℂ) ∉
      closure (fwdHull (fun u : ℝ => c.W u.toNNReal ω) (σ : ℝ)) := by
  intro hx
  obtain ⟨τ, hτ⟩ := hvis hx
  exact pole_notMem_closure_of_visit hη hc h0 hx (den_of_lt_firstTipTimeX c r l a hη hc h0 hηe hσ) hτ

/-- **Before the first tip in the translated explored image, the closed translated explored hull and the closed
retained hull are disjoint** (given the counterflow's visit to `x > 0`). -/
theorem disjoint_closure_of_lt_firstTipTimeX (hx0 : 0 ≤ rootPt r.1) (hce : Continuous fun u => schedW c r l a u ω)
    (h0e : schedW c r l a 0 ω = 0) (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * η τ + 1 = 0) :
    Disjoint (closure ((fun z : ℂ => z + (rootPt r.1 : ℝ)) ''
        fwdHull (fun u : ℝ => schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (σ : ℝ))) := by
  set x := rootPt r.1 with hx
  have hUe : Continuous fun u : ℝ => schedW c r l a u.toNNReal ω := hce.comp continuous_real_toNNReal
  have hUe0 : (fun u : ℝ => schedW c r l a u.toNNReal ω) 0 = 0 := by simpa using h0e
  have hU : Continuous fun u : ℝ => c.W u.toNNReal ω := hc.comp continuous_real_toNNReal
  rcases (historyTime c r l).coe_nonneg.eq_or_lt with hT0 | hTpos
  · rw [← hT0, fwdHull_zero_eq_empty hUe hUe0, image_empty, closure_empty]
    exact Set.empty_disjoint _
  have hsep : Disjoint (η '' Icc 0 σ)
      ((fun z : ℂ => -z⁻¹) '' ((fun t => ηe t + x) '' Icc 0 (historyTime c r l) \ {0})) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ ⟨_, ⟨⟨u, hu, rfl⟩, hu0⟩, he⟩
    have hne : ηe u + x ≠ 0 := hu0
    have h := sep_of_lt_firstTipTimeX c r l hη hc h0 hσ t ht u hu
    apply h
    rw [← he]
    field_simp
    ring
  have hseg : ∀ u ∈ Icc 0 σ, ∀ y : ℝ, 0 < y → y ≤ x → η u ≠ -((y : ℂ))⁻¹ := by
    intro u hu y hy hyx
    rcases hx0.eq_or_lt with hxz | hxp
    · exact absurd (hyx.trans hxz.symm.le) (not_le.2 hy)
    · obtain ⟨τ, hτ⟩ := hvis hxp
      exact seg_of_visit hη hc h0 hxp (den_of_lt_firstTipTimeX c r l a hη hc h0 hηe hσ) hτ u hu.2 y hy hyx
  have hd := disjoint_closure_translated_hull_seg hη hc h0 hηe hce h0e (NNReal.coe_pos.1 hTpos) hx0 hseg hsep
  have e : fwdHull (fun t => Ito.rpath (fun u => schedW c r l a u ω) t + x) (historyTime c r l : ℝ) =
      (fun z : ℂ => z + (x : ℝ)) '' fwdHull (fun u : ℝ => schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ) :=
    ConformalImageFull.fwdHull_add_const _ x _
  rw [e] at hd
  have hAH : fwdHull (Ito.rpath fun u => c.W u ω) (σ : ℝ) ⊆ H := (isHPHull_fwdHull hU σ.coe_nonneg).1
  have hAb : Bornology.IsBounded (fwdHull (Ito.rpath fun u => c.W u ω) (σ : ℝ)) :=
    (isHPHull_fwdHull hU σ.coe_nonneg).2.1
  exact disjoint_closure_negInv_swap hAH hAb hd

end Range

/-! ### The launch chart's domain and the continuation -/

/-- **The launch chart's domain and the continuation of the retained counterflow at a root `x`** (per sample). -/
theorem launch_dom_contX (hx0 : 0 ≤ rootPt r.1)
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
    ((cL.dom : Set ℂ) = H \ (fun z : ℂ => (rootPt r.1 : ℂ) + z) ''
        fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)) ∧
      ∀ q : ℝ≥0, (∀ u ≤ ℓ q, (rootPt r.1 : ℂ) * γ' u + 1 ≠ 0) →
        (0 < rootPt r.1 → ((Sec5.CrossRestart.mobPole (rootPt r.1) 1 : ℝ) : ℂ) ∉
          closure (fwdHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ))) →
        Disjoint (closure ((fun z : ℂ => z + (rootPt r.1 : ℝ)) ''
            fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
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
  have hcL : cL = succChart (rootPt r.1) Δ D k := by
    have h1 : GW2Olm.curLaunch c r l a ω = some (succChart spec.1 Δ D k, GW2Tip.specAngle spec k) := hl'
    rw [hl] at h1
    exact (Prod.mk.inj (Option.some.inj h1)).1
  have hck : ∀ j < k, Continuous (stopDrv (Δ j) (D j)) ∧ stopDrv (Δ j) (D j) 0 = 0 :=
    fun j hj => hc j (Nat.lt_succ_of_lt hj)
  obtain ⟨hJ, hJ0⟩ := continuous_joinDrv hck
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
  -- the explored hull through the launch chart
  have hKT : fwdHull (joinDrv Δ D k) (T : ℝ) = fwdHull J' (T : ℝ) :=
    QuantumZipper.Thm14FromThm13.fwdHull_eq_of_eqOn hJ hJ'c hTn heq
  have hdom : (cL.dom : Set ℂ) = H \ (fun z : ℂ => (rootPt r.1 : ℂ) + z) '' fwdHull J' (T : ℝ) := by
    rw [hconf.coe_dom, ← hKT]
    have himgH : cL.2.1 '' H =
        (fun z : ℂ => (rootPt r.1 : ℂ) + z) '' (fwdMapInv (joinDrv Δ D k) (T : ℝ) '' H) := by
      rw [image_image]
      exact image_congr fun w hw => hinv w hw
    rw [himgH, QuantumZipper.RS.image_fwdMapInv_H hJ hJ0 hTn, image_sdiff (add_right_injective _)]
    congr 1
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change 0 < ((rootPt r.1 : ℂ) + w).im
      have : 0 < w.im := hw
      simpa using this
    · intro hz
      refine ⟨z - (rootPt r.1 : ℂ), ?_, by ring⟩
      change 0 < (z - (rootPt r.1 : ℂ)).im
      have : 0 < z.im := hz
      simpa using this
  refine ⟨hdom, fun q hden hpole hq => ?_⟩
  have hd' : Disjoint (closure ((fun z : ℂ => z + (rootPt r.1 : ℝ)) '' fwdHull (joinDrv Δ D k) (T : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ))) := by
    rw [hKT]
    exact hq
  exact chartInv_image_invHullX hx0 hJ hJ0 hTn hinv hext hWk hWk0 hγk hW' hW'0 hγ' hℓc hℓm hℓ0 hiff hden hpole hd'

/-- **The continuation at every `q`, from the clock's range** (root `x`, the counterflow's visit to `x > 0`). -/
theorem launch_cont_of_rangeX (hx0 : 0 ≤ rootPt r.1)
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
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') {ηe : ℝ≥0 → ℂ}
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      ((fun z : ℂ => (rootPt r.1 : ℂ) + z) '' (ηe '' Icc 0 (historyTime c r l)))})
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * γ' τ + 1 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) (q : ℝ≥0) :
    cL.2.1 '' Supp8.Q3Rel.invHull (fun u : ℝ => Wk u.toNNReal) (q : ℝ) =
      Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ) := by
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  obtain ⟨-, hcont⟩ := launch_dom_contX c r l a hx0 hord ω hold hgood hl hc hconf hext hWk hWk0 hγk hW' hW'0 hγ'
    hℓc hℓm.monotone hℓ0 hiff
  have hq : ℓ q ∈ range ℓ := ⟨q, rfl⟩
  rw [hℓr] at hq
  exact hcont q (den_of_lt_firstTipTimeX c r l a hγ' hW' hW'0 hηe hq)
    (pole_of_lt_firstTipTimeX c r l a hγ' hW' hW'0 hηe hq hvis)
    (disjoint_closure_of_lt_firstTipTimeX c r l a hγ' hW' hW'0 hηe hq hx0 hce h0e hvis)

end InteractingSLE.Theorem14.GW2Xk
