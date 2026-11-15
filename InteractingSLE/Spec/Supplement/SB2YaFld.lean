/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YaRel
import InteractingSLE.Spec.Supplement.SB2JvRootAS
import InteractingSLE.Spec.Supplement.SB2LxObs
import InteractingSLE.Spec.Supplement.SB2UxProf

/-!
# The relative root fields of a piece start

Packet PROVE-T14-SB2LIFT (round 31; item 4). **`rootFields`**: at a launched actual piece of positive shifted
lifetime whose shifted part (after the visit of `R` at `t₀`) lifts to the relative root (`StageFacts` at shift `t₀`,
LIFTSET's `RootFactsAt`, and the lift relation of the two pieces), the relative fields of `PieceStartV`: `top`, `zero`,
`hitR`, `hitL₂` and `recR`. The finite case uses the actual right end-hit (GW1's `sb2LowerRightHits`), `actual_end`,
`rel_hit`, `rel_lRecR` and `rel_noLeftHit`; at an infinite piece both pieces are infinite and no point is hit.
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → Drv}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {c : Chart} {m : ℝ} {n : ℕ} {t₀ : ℝ≥0}

theorem stChart_init_zero : stChart (ExplState.init 0) = Chart.id.recenter 0 := rfl

/-- **The relative root fields of a piece start.** -/
theorem rootFields (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hD : LiftCurveData β₀ γ tL R ι)
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hU : UpperChartOK c)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hrec₁ : ∀ k, k ≤ n → RecInv κ b₁ J₁ θ D₁ k) (hlm₁ : ∀ k, NoLeftMove κ b₁ J₁ θ D₁ k)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)).2.2.2.1 n ≠ none)
    (hlen : n + 1 ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hpt₁ : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤
      stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n))
    (hRH : (D₁ n).2 ≠ ⊤ → (D₁ n).2 ≠ 0 → ∃ x : ℝ,
      stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x)
    (hpR : pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n) t₀ = R)
    (hL0 : (D₁ n).2 - t₀ ≠ 0)
    (hPc : ContinuousOn (fun t => pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n) (t₀ + t))
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D₁ n).2 - t₀})
    (htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D₁ n).2 - t₀},
      pcPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n) (t₀ + t) ∈ β₀ '' Ici tL)
    (hreg₂ : IsRegularDriver (D₂ 0))
    (hF : Mn.StageFacts c m (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n) t₀
      (ExplState.init 0) (D₂ 0))
    (hgood : (D₂ 0).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D₂ 0)))) (hpos₂ : (D₂ 0).2 ≠ 0)
    (hL : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n))
      (newPc (ExplState.init 0) (D₂ 0)))
    (htip₂ : (D₂ 0).2 ≠ ⊤ → (newPc (ExplState.init 0) (D₂ 0)).1.tipSet (newPc (ExplState.init 0) (D₂ 0)).2.1
      (newPc (ExplState.init 0) (D₂ 0)).2.2 = trOf (D₂ 0) '' Icc 0 (D₂ 0).2.toNNReal) :
    ((D₂ 0).2 = ⊤ ↔ (D₁ n).2 = ⊤) ∧ ((D₂ 0).2 = 0 ↔ (D₁ n).2 = 0) ∧
    ((∃ x : ℝ, 0 < x ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ↔
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)) ⊤ (D₁ n) x) ∧
    (¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ∧
    ((D₁ n).2 ≠ ⊤ → lRecR (ExplState.init 0) ⊤ (D₂ 0) =
      ι (max (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ⊤ (D₁ n)) R)) := by
  set s₁ := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n with hs₁
  have hpr₂ : GW1P.PieceRegular (D₂ 0).1 (D₂ 0).2 := hF.2.2.2.2.2.2
  have hpos₁ : (D₁ n).2 ≠ 0 := fun h => hL0 (by rw [h]; exact zero_tsub _)
  have hc₁ := (GW1P.isClosed_pieces_run (κ := κ) (b := b₁) (jumps := J₁) _ D₁ hP₁ n).1
  have hr₁ := LuM.pieceRegular_of_launch hP₁ hl₁
  obtain ⟨⟨c₁, θ₁⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
  have hsucc := prefixPhysSet_succ_of_launch hl₁'
  have hpre : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) ⊆ range β₀ := by
    rw [hβr]; exact prefix_subset_physSet D₁ hlen
  have htip₁sub : (newPc s₁ (D₁ n)).1.tipSet (newPc s₁ (D₁ n)).2.1 (newPc s₁ (D₁ n)).2.2 ⊆
      SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) := by
    rw [hsucc]; exact subset_union_right
  have hPH : SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) ⊆ Hbar := by
    intro w hw
    obtain ⟨t, rfl⟩ := hpre hw
    exact hβ.2.2.1 t
  obtain ⟨_, -, -, -, htip₁⟩ := tipSet_newPc_launch hP₁ hl₁
  have hH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D₁ n).2 → pcPt s₁ (D₁ n) t ∈ Hbar := fun t ht =>
    hPH (htip₁sub (by rw [htip₁]; exact ⟨t, ht, rfl⟩))
  have htop : (D₂ 0).2 = ⊤ ↔ (D₁ n).2 = ⊤ :=
    top_iff_of_liftRel' hβ hγ.2.1 hc₁ (GW1P.hasProperBdryExt_recenter_id 0)
      (by rw [min_eq_right le_top]; exact hr₁) (by rw [min_eq_right le_top]; exact hpr₂)
      (htip₁sub.trans hpre) hL
  have hzero : (D₂ 0).2 = 0 ↔ (D₁ n).2 = 0 := ⟨fun h => absurd h hpos₂, fun h => absurd h hpos₁⟩
  by_cases hT : (D₁ n).2 = ⊤
  · -- an infinite start piece: no hits at all
    have hT₂ : (D₂ 0).2 = ⊤ := htop.2 hT
    have hT0 : stopTime ⊤ (D₂ 0) = 0 := by simp [stopTime, hT₂]
    have hno₁ := not_lHit_of_top (κ := κ) (b := b₁) (J := J₁) (θ := θ) (D := D₁) hr₁.1 hT (hrec₁ n le_rfl)
    have hc1 : ∀ w, (stChart (ExplState.init 0)).1 w = w := (root_chart_facts stChart_init_zero).1
    have hno₂ : ∀ x : ℝ, x ≠ 0 → ¬ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x := by
      rintro x hx ⟨-, hna⟩
      exact hna (lAlive_of_stopTime_zero hreg₂.2.1 hT0 (by rw [hc1]; exact_mod_cast hx))
    refine ⟨htop, hzero, ⟨fun ⟨x, hx, h⟩ => absurd h (hno₂ x hx.ne'), fun h => absurd h hno₁⟩,
      fun ⟨x, hx, h⟩ => hno₂ x hx.ne h, fun h => absurd hT h⟩
  · -- a finite start piece: the right end-hit and its lift
    have hT₂ : (D₂ 0).2 ≠ ⊤ := fun h => hT (htop.1 h)
    obtain ⟨x, hx, hhit⟩ := hRH hT hpos₁
    obtain ⟨hbef, z, hz, hxz, hmax⟩ := actual_end hP₁ hW₁ hrec₁ hlm₁ hl₁ hT hpos₁ hpt₁ hH hPH hx hhit
    have ht₀e : (t₀ : ℝ≥0∞) < (D₁ n).2 := by
      by_contra h
      push Not at h
      exact hL0 (tsub_eq_zero_of_le h)
    have hRx : R < x := hbef t₀ ht₀e R hpR
    have hRz : R < z := lt_of_lt_of_le hRx hxz
    have hLfin : (D₁ n).2 - t₀ ≠ ⊤ := ENNReal.sub_ne_top hT
    have hrel := rel_trace_lift hγ hβ hU stChart_init_zero hF hLfin hPc htl
    -- the end point lies on the tail and lifts to `ι z`
    have hzend : ∃ sz : ℝ≥0, β₀ (tL + sz) = z := by
      have hend := htl ((D₁ n).2 - t₀).toNNReal
        (show ((((D₁ n).2 - t₀).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (D₁ n).2 - t₀ from ENNReal.coe_toNNReal_le_self)
      obtain ⟨y, hy, hye⟩ := hend
      refine ⟨y - tL, ?_⟩
      rw [add_tsub_cancel_of_le (show tL ≤ y from hy), hye, ← hz]
      congr 1
      have h1 : ((t₀ + ((D₁ n).2 - t₀).toNNReal : ℝ≥0) : ℝ≥0∞) = (D₁ n).2 := by
        push_cast
        rw [ENNReal.coe_toNNReal hLfin, add_tsub_cancel_of_le ht₀e.le]
      exact ENNReal.coe_inj.1 (h1.trans (ENNReal.coe_toNNReal hT).symm)
    obtain ⟨sz, hsz⟩ := hzend
    have hzmem₁ : (z : ℂ) ∈ (newPc s₁ (D₁ n)).1.tipSet (newPc s₁ (D₁ n)).2.1 (newPc s₁ (D₁ n)).2.2 := by
      rw [htip₁, ← hz]
      exact ⟨(D₁ n).2.toNNReal, show ((D₁ n).2.toNNReal : ℝ≥0∞) ≤ (D₁ n).2 from ENNReal.coe_toNNReal_le_self, rfl⟩
    have hend : ((ι z : ℝ) : ℂ) ∈ trOf (D₂ 0) '' Icc 0 (D₂ 0).2.toNNReal := by
      rw [← htip₂ hT₂, hL]
      exact ⟨sz, show β₀ (tL + sz) ∈ _ by rw [hsz]; exact hzmem₁, hD.ray sz z hRz hsz⟩
    have hrhit := rel_hit hι hD stChart_init_zero hpr₂ hT₂ hrel hbef hxz hRz hend
    have hιz : 0 < ι z := by
      have := hι.mono (mem_Ici.2 le_rfl) (mem_Ici.2 hRz.le) hRz
      rwa [hι.map_base] at this
    refine ⟨htop, hzero, ⟨fun _ => ⟨x, hx, hhit⟩, fun _ => ⟨ι z, hιz, hrhit⟩⟩,
      rel_noLeftHit (θ := θ) hreg₂ hgood hT₂ hpos₂ hιz hrhit, fun _ => ?_⟩
    have hnd := Lx.stStatus_ne_done_of_launches _ D₁ hl₁'
    have hzcl : (z : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1))) :=
      mem_closure_prefix_succ_of_mem hP₁ hl₁' hT hrec₁ hlm₁ hnd (lt_of_lt_of_le hx hxz) (htip₁sub hzmem₁)
    rw [lRecR_eq_end hP₁ hrec₁ hl₁ hT hPH (lt_of_lt_of_le hx hxz) hzcl hmax, max_eq_left hRz.le]
    exact rel_lRecR hι hD stChart_init_zero rfl hpr₂ hT₂ hL (htip₂ hT₂) hRz hend
      (fun w hw hw0 => hmax w (htip₁sub hw) hw0)

end InteractingSLE.Theorem14.SB.Lk
