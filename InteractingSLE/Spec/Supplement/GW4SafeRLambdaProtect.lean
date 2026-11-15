/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaTrace
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaWall
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaTail

/-! # GW4: the actual protected exposed-access reference cover -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GB11Chart Sec7.PocketStopSide MartChar.RealFlow
open SB.FinRel (freeNear)

/-- Outside four physical points, every nonzero exposed access has an
actual rational interior reference with an exposed old coordinate and an
incident collar. The current approach lies in the component missing every
set disjoint from the physical component, precisely the Prop. 3.8 condition.
Original-real landings are included. -/
theorem Frame.exists_protected_seed_reference_cover {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hq : 0 < q) (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t) :
    ∃ E : Set ℂ, E.Finite ∧ ∀ ξ ∈ Ioo
      (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
      (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q), ξ ≠ 0 → ∀ p : ℂ,
      Tendsto (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1
        (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ∉ E →
      ∃ s : ℚ, (F.ent w : ℝ) < s ∧ (s : ℝ) < t ∧ trc w (s : ℝ).toNNReal ≠ 0 ∧
        -(trc w (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
        0 < F.rcap w (s : ℝ).toNNReal ∧ F.rcap w (s : ℝ).toNNReal < F.rcap w t ∧
        p ∈ trc w '' Icc 0 (s : ℝ).toNNReal ∧
        p ≠ trc w (s : ℝ).toNNReal ∧ ∃ x r ρ : ℝ,
        x ∈ Ioo
          (-rightImg (fun u : ℝ => -R u.toNNReal) 0 (F.rcap w (s : ℝ).toNNReal) -
            R (F.rcap w (s : ℝ).toNNReal).toNNReal)
          (rightImg (fun u : ℝ => R u.toNNReal) 0 (F.rcap w (s : ℝ).toNNReal) -
            R (F.rcap w (s : ℝ).toNNReal).toNNReal) ∧ 0 < r ∧ 0 < ρ ∧
        (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) (F.rcap w (s : ℝ).toNNReal)).2.1 ''
          (H ∩ ball (x : ℂ) r) ⊆ ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).dom : Set ℂ) ∧
        Tendsto (fun z => (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal)
          (F.rcap w (s : ℝ).toNNReal)).1
          ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 z))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun z => (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.2
            ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 z) -
          (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) (F.rcap w (s : ℝ).toNNReal)).2.2
            ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
        ∀ A : Set ℂ, Disjoint (relDom F.C) A →
          ∀ᶠ y in 𝓝[H] (ξ : ℂ), (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y ∈
            freeNear A (fwdHull (fun u : ℝ => w u.toNNReal) (s : ℝ)) p ρ := by
  have hη := Frame.continuous_trc hw
  have hB := hw.2.2.2.2
  obtain ⟨cutR, -, hcutR, -⟩ := exists_wall_visit_cut hη hB.1.1 hB.1.2.2.1 hB.2.2.2.2.2.1 t
  obtain ⟨cutL, -, hcutL, -⟩ := exists_wall_visit_cut hη hB.2.1.1 hB.2.1.2.2.1 hB.2.2.2.2.2.2 t
  refine ⟨{0, trc w t, WangWu.negInv (F.αR cutR.toNNReal), WangWu.negInv (F.αL cutL.toNNReal)},
    (((Set.finite_singleton _).insert _).insert _).insert _, fun ξ hξ hξ0 p hland hBad => ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hBad
  obtain ⟨hp0, hpTip, hpR, hpL⟩ := hBad
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun u : ℝ => R u.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun u : ℝ => R u.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  obtain ⟨v, hv⟩ := hVer q hqV
  have hDom := componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0
    (Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 hv htEnt htExit hqt)
  have hCur := hBase.loewner hRR hRR0 q.coe_nonneg
  have hKT : ((componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).dom : Set ℂ) ⊆
      H \ fwdHull (fun u : ℝ => w u.toNNReal) t := hDom ▸ inter_subset_right
  have hpK := Frame.current_seed_landing_mem_closure_hull hF hw hR hR0 hVer htEnt htExit hq hqV hqt hξ hland
  have := Sec7.R5Lift.nhdsWithin_H_neBot ξ
  have hpD := mem_closure_of_tendsto hland (eventually_nhdsWithin_of_forall fun y hy => hKT (hCur.inv_mem_dom hy))
  have hpTrace := Frame.mem_trace_of_common_hull_closures hw hpK hpD
  obtain ⟨r₀, hr₀, hFront⟩ := Frame.exists_ball_frontier_relDom_subset_trace hF hw hcutR hcutL hpTrace hp0 hpR hpL
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsCap0, hsCapLt, ⟨ρ, hρ, hTail⟩, x, r, hx, hr, hCol, hTr, hLift⟩ :=
    Frame.exists_seed_reference_avoiding_tail hF hw hBase hRR hRR0 htExit
      (by rw [← hqt]; exact NNReal.coe_pos.2 hq) hξ0
      (by rw [← hqt]; simpa only [Real.toNNReal_coe] using hξ) hpTip
  have hsNonneg : 0 ≤ (s : ℝ) := (F.ent w).coe_nonneg.trans hsEnt.le
  have hnear : ∀ z ∈ trc w '' Icc 0 t, z ∈ closedBall p ρ → z ∈ trc w '' Icc 0 (s : ℝ).toNNReal := by
    rintro z ⟨u, hu, rfl⟩ hzb
    by_cases hus : u ≤ (s : ℝ).toNNReal
    · exact ⟨u, ⟨hu.1, hus⟩, rfl⟩
    · apply (disjoint_left.1 hTail _ hzb).elim
      refine ⟨(u : ℝ), ⟨?_, NNReal.coe_le_coe.2 hu.2⟩, by simp only [Real.toNNReal_coe]⟩
      have hsu := NNReal.coe_lt_coe.2 (not_le.1 hus)
      rw [Real.coe_toNNReal _ hsNonneg] at hsu
      exact hsu.le
  have hρ' : 0 < min r₀ ρ := lt_min hr₀ hρ
  have hfill := Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling
    (isCompact_Icc.image hη) (hw.2.2.1.2.2 (s : ℝ).toNNReal ENNReal.coe_lt_top)
  have hfrK : frontier (relDom F.C) ∩ ball p (min r₀ ρ) ∩ H ⊆
      fwdHull (fun u : ℝ => w u.toNNReal) (s : ℝ) := by
    rintro z ⟨⟨hzF, hzb⟩, hzH⟩
    have hzTrace := hnear z (hFront ⟨⟨hzF, ball_subset_ball (min_le_left _ _) hzb⟩, hzH⟩)
      (ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hzb))
    rw [← Real.coe_toNNReal (s : ℝ) hsNonneg, hfill]
    exact ⟨hzH, Or.inl (subset_closure hzTrace)⟩
  rw [← hqt] at hCol hTr hLift
  have hpOldTip : p ≠ trc w (s : ℝ).toNNReal := by
    intro he
    exact Set.disjoint_left.1 hTail ⟨(s : ℝ), ⟨le_rfl, hst.le⟩, he.symm⟩
      (mem_closedBall_self hρ.le)
  refine ⟨s, hsEnt, hst, hs0, hsC, hsCap0, hsCapLt,
    hnear p hpTrace (mem_closedBall_self hρ.le), hpOldTip, x, r, min r₀ ρ, hx, hr, hρ', hCol, hTr, hLift, ?_⟩
  intro A hA
  have hDo : IsOpen (relDom F.C) := by
    rw [← component_base_domain hF.2.2.2.1 hCo hCH]
    exact ((infinitySourceChart.trans F.c).trans infinitySourceChart).dom.isOpen
  apply Sec7.R5Wall.eventually_mem_freeNear hDo (fun z hz => Set.disjoint_left.1 hA hz) hfrK hland _ hρ'
  refine eventually_nhdsWithin_of_forall fun y hy => ?_
  have hz := hCur.inv_mem_dom hy
  have hz' := hKT hz
  have hzD : (componentAmbientChart F.c (fun u : ℝ => R u.toNNReal) q).2.1 y ∈
      relDom F.C ∩ (H \ fwdHull (fun u : ℝ => w u.toNNReal) t) := by
    rw [← hDom]
    exact hz
  exact ⟨hz'.1, hzD.1, fun h => hz'.2
    (QuantumZipper.fwdHull_mono.1 (show (s : ℝ) ≤ (t : ℝ) from hst.le) h)⟩

end InteractingSLE.Theorem14.GW4Fix
