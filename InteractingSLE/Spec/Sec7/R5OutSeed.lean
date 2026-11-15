/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutFibre
import InteractingSLE.Spec.Sec7.R5OutAccess
import InteractingSLE.Spec.Sec7.Lemma71PTrace
import InteractingSLE.Spec.Sec7.SideC8NativeWord
import InteractingSLE.Spec.Restart.FlowStopIdentLLTerminal

/-! # The relative prefix behind a coordinate in the open seed interval -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open PocketTraversal Lemma71C PocketStop PocketStopField PocketStopSide PocketUnionPt
  PocketStopMarked PocketStopMarked.Outer Sec6 PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen PocketCoupling

/-- A middle coordinate approaches a point of the relative trace prefix in the initial chart.
Only the local driver is used; a finite slit extension permits application of Lemma 7.1. -/
theorem exists_base_prefix_landing {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}
    (hc : (c ω).IsConformal) (hγ : IsDrivenCurve (γ ω))
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q)) :
    ∃ b ∈ γ ω '' Icc 0 (capInv (γ ω) q),
      Tendsto (fun y => (c ω).1 ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 b) := by
  obtain ⟨q₂, hqq₂, hq₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqq₂' : (q : ℝ) < q₂ := by exact_mod_cast hqq₂
  set W₁ := Ito.clampDrv (Ito.rpath fun s => segDriver (γ ω) s) q₂
  have hW₁ : Continuous W₁ := Ito.continuous_clampDrv q₂.coe_nonneg
    (Ito.continuousOn_rpath hγ.segDriver_spec.2.1 hq₂)
  have heq₁ : EqOn W₁ (Ito.rpath fun s => segDriver (γ ω) s) (Icc 0 q₂) := Ito.clampDrv_eqOn
  have hW₁0 : W₁ 0 = 0 := by
    rw [heq₁ ⟨le_rfl, q₂.coe_nonneg⟩]
    simpa only [Ito.rpath, Real.toNNReal_zero] using hγ.segDriver_spec.1
  have hLT := Theorem14.CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (hγ.isGeneratingTrace hq₂)
  have hLT₁ : IsLoewnerTraceLT W₁ q₂ (fun s : ℝ => capTrace (γ ω) s.toNNReal) :=
    ⟨hLT.1, hLT.2.1, fun s hs hsq => by
      rw [← hLT.2.2 s hs hsq]
      exact fwdHull_eq_of_eqOn hs hsq fun r hr => heq₁ hr⟩
  set q₁ : ℝ := ((q : ℝ) + q₂) / 2
  have hqq₁ : (q : ℝ) < q₁ := by dsimp [q₁]; linarith
  have hq₁q₂ : q₁ < q₂ := by dsimp [q₁]; linarith
  have hq₁0 : 0 ≤ q₁ := q.coe_nonneg.trans hqq₁.le
  set W := YuanCorollary13.extDrive W₁ q₁
  set γ₁ := YuanCorollary13.extTrace W₁ (fun s : ℝ => capTrace (γ ω) s.toNNReal) q₁
  have hW : Continuous W := YuanCorollary13.continuous_extDrive hW₁
  have hW0 : W 0 = 0 := YuanCorollary13.extDrive_zero hW₁0 hq₁0
  have htrace : IsLoewnerTrace W γ₁ := hLT₁.isLoewnerTrace_ext hW₁ hW₁0 hq₁0 hq₁q₂
  have heq : ∀ s ∈ Icc (0 : ℝ) q₁, segDriver (γ ω) s.toNNReal = W s := by
    intro s hs
    dsimp [W]
    rw [YuanCorollary13.extDrive_eq hs.2]
    exact (heq₁ ⟨hs.1, hs.2.trans hq₁q₂.le⟩).symm
  have hrel : relChart c γ q ω = (c ω).loewner W q :=
    loewner_congr (c ω) q.coe_nonneg hqq₁ heq
  have hseed := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hW
    (fun s hs => heq s ⟨hs.1, hs.2.trans hqq₁.le⟩)
  have hL := congrFun hseed.1 (0 : Fin (nL + 1))
  have hR := congrFun hseed.2 (0 : Fin (nR + 1))
  simp only [hxL, hxR, neg_zero] at hL hR
  have hWq : segDriver (γ ω) q = W q := by
    simpa only [Real.toNNReal_coe] using heq q ⟨q.coe_nonneg, hqq₁.le⟩
  rw [hL, hR] at hξ
  set b := extendFrom H (fwdMapInv W q) ξ
  have hb := Lemma71P.mem_image_of_mid htrace hW hW0 q.coe_nonneg hξ.1 hξ.2
  have hb' : b ∈ γ ω '' Icc 0 (capInv (γ ω) q) := by
    obtain ⟨s, hs, hsb⟩ := hb
    rw [← hγ.image_capTrace hq]
    refine ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hs.2⟩, ?_⟩
    exact (YuanCorollary13.extTrace_eq (hs.2.trans hqq₁.le)).symm.trans hsb
  refine ⟨b, hb', ?_⟩
  have hlim := (htrace.hasBdryLimits hW hW0 q.coe_nonneg).tendsto
    (show (ξ : ℂ) ∈ Hbar from by change (0 : ℝ) ≤ (ξ : ℂ).im; simp)
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun y hy => by
    rw [hrel]
    exact (hc.2.2 _ (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 q.coe_nonneg hy)).symm)

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {c : Ω → Chart} {ω : Ω}

/-- An exposed physical landing, including a wall landing, occurs before the left stop. -/
theorem mem_trace_of_seed_interval
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : PocketWordAssembly.IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω - segDriver (travAll R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q))
    (hExit : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠
      PocketJordan.cfPt (openPt (R ω) (L ω) r)) :
    extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈
      η ω '' Icc 0 (R5Ref.leftStop R L r η ψ q ω) := by
  have hP := hcfg.toPocket hψ
  obtain ⟨b, hb, hblim⟩ := exists_base_prefix_landing hc hP.driven hxL hxR hq hξ
  obtain ⟨hland, hpcl, -⟩ := current_landing hcfg hψ hc hdom heq hq ξ
  have hsub := current_dom_subset_ambient (A := univ) (mem_univ ω) hcfg hψ hc hdom heq hq
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hP.driven hq hc
  have hψlim := (hψ.1 _ ⟨hpcl, hExit⟩).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hland, eventually_nhdsWithin_of_forall fun y hy =>
      ⟨subset_closure (hsub (hNow.inv_mem_dom hy)).1,
        fun h => hcfg.conf.cfPt_openPt_notMem (h ▸ (hsub (hNow.inv_mem_dom hy)).1)⟩⟩)
  have hpb : ψ ω (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) = b := by
    have : NeBot (𝓝[H] (ξ : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      change (0 : ℝ) ≤ (ξ : ℂ).im
      simp)
    exact tendsto_nhds_unique hψlim (hblim.congr' (eventually_nhdsWithin_of_forall fun y hy =>
      heq (hsub (hNow.inv_mem_dom hy)).1))
  dsimp only [travAll, cfTraversal, trav] at hb
  rw [image_relCurve_Icc _ hP.erase.clock_σ_pos (capInv_nonneg _ _)] at hb
  obtain ⟨v, hv, hvb⟩ := hb
  have hu := clockOf_mem_Ico hP.erase.clock_σ_pos (capInv_nonneg (travAll R L r η ψ ω) q)
  have hv' : v ∈ Ico 0 (pocketClock (η ω) (cfPocket (R ω) (L ω) r) _ _ _) :=
    ⟨hv.1, hv.2.trans_lt hu.2⟩
  have hvmem := hP.erase.erasedPath_mem hv'
  have he : erasedPath (η ω) (cfPocket (R ω) (L ω) r) _ _ v =
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ :=
    hψ.2.1 ⟨hvmem.1, fun h => hvmem.2 (mem_singleton_iff.2
      ((mem_singleton_iff.1 h).trans IsChangeConfigInc.cfArcR_zero.symm))⟩
      ⟨hpcl, hExit⟩ (hvb.trans hpb.symm)
  exact he ▸ erasedPath_prefix_subset_left hP hu ⟨v, hv, rfl⟩

/-- An exposed physical landing, including a wall landing, occurs before the left stop. -/
theorem mem_trace_of_seed_intervalInf
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : PocketSeedOpen.IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω - segDriver (travAllInf R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q)) :
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈
      η ω '' Icc 0 (R5Ref.leftStopInf R L r η ψ q ω) := by
  have hP := hcfg.toPocketInf hψ
  obtain ⟨b, hb, hblim⟩ := exists_base_prefix_landing hc hP.driven hxL hxR hq hξ
  obtain ⟨hland, hpcl, -⟩ := current_landingInf hcfg hψ hc hdom heq hq ξ
  have hsub := current_dom_subset_ambientInf (A := univ) (mem_univ ω) hcfg hψ hc hdom heq hq
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hP.driven hq hc
  have hψlim := (hψ.1 _ hpcl).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hland, eventually_nhdsWithin_of_forall fun y hy =>
      subset_closure (hsub (hNow.inv_mem_dom hy)).1⟩)
  have hpb : ψ ω (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) = b := by
    have : NeBot (𝓝[H] (ξ : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 (by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      change (0 : ℝ) ≤ (ξ : ℂ).im
      simp)
    exact tendsto_nhds_unique hψlim (hblim.congr' (eventually_nhdsWithin_of_forall fun y hy =>
      heq (hsub (hNow.inv_mem_dom hy)).1))
  dsimp only [travAllInf, cfTraversalInf, travInf] at hb
  rw [image_relCurve_Icc _ hP.erase.clockEnd_pos (capInv_nonneg _ _)] at hb
  obtain ⟨v, hv, hvb⟩ := hb
  have hu := clockOf_mem_Ico hP.erase.clockEnd_pos (capInv_nonneg (travAllInf R L r η ψ ω) q)
  have hv' : v ∈ Ico 0 (clockEnd (η ω) (cfPocket (R ω) (L ω) r) _) :=
    ⟨hv.1, hv.2.trans_lt hu.2⟩
  have he : erasedPathInf (η ω) (cfPocket (R ω) (L ω) r) _ v =
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ :=
    hψ.2.1 (hP.erase.erasedPath_mem hv') hpcl (hvb.trans hpb.symm)
  exact he ▸ erasedPathInf_prefix_subset_left hP hu ⟨v, hv, rfl⟩

end InteractingSLE.Sec7.R5Out
