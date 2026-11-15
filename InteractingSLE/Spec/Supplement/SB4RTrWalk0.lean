/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrRestart
import InteractingSLE.Spec.Supplement.SB5
import InteractingSLE.Spec.Supplement.GW1
import InteractingSLE.Spec.Supplement.GW6Reduction

/-!
# The lower walk on its initial forced arc: the first two instructions

Packet PROVE-T14-SB4LEAF (ruling R104, the initial-arc version). On the initial forced arc of the lower walk (the
right seed at `0` and every genuine jump in `(0, v]` keep the outward height low, `b(·⁺) − πχ/2 ≤ −λ`):

* **`ae_walk_zero_lifetime`**: the first piece of a staged walk has zero lifetime almost surely when its root seed is
  inadmissible (GW0; the conditional field at the first launch is the field itself, `GW1.seed_lims_eq`);
* `rightLim_low_of_arc`: the outward height at `v` is low too (`SB.le_of_low_arc`);
* **`restartRel_two`**: in the translated plane (data `b(· + v)`), the walk from `−v` (the original walk) and the walk
  from `0` (the walk restarted at `v`), with first pieces of zero lifetime, are in `RestartRel` after their first two
  instructions when the arc ends at a genuine admissible jump (`walkMark`); otherwise both have followed the boundary to
  `∞` (`done_two`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar IsForwardSol fwdMap fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lf

open Exist.Staged Exist.StagedLaw FlowDilate
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-! ### The first piece has zero lifetime -/

/-- **The first piece of a staged walk has zero lifetime at an inadmissible root**, almost surely. -/
theorem ae_walk_zero_lifetime {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b J)
    {θ : ℝ} {right : Bool} {D : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hD : IsStagedHistory κ b J P h (boundaryWalkSpec b J θ right) D)
    (hbad : ¬ ExplState.IsAdmissibleSeed κ (leftLim b 0) (rightLim b 0) θ) : ∀ᵐ ω ∂P, (D 0 ω).2 = 0 := by
  obtain ⟨ω₀, hω₀⟩ := (hD.2.2.2 0).exists
  obtain ⟨b', jumps', h', hb', hT, hF⟩ :=
    hω₀ _ _ (GW1.launches_run_one_boundaryWalkSpec κ b J θ right (fun j => D j ω₀))
  rw [GW1.pastSigma_zero_eq_bot, GW1.condExpKernel_bot_apply] at hF
  obtain ⟨h'', 𝓕, VL, VR, B, htr, hC⟩ := hF
  have hshift : ∀ ω φ, h'' ω φ = h ω φ + θ * QuantumZipper.chiC κ * ∫ z, φ z := by
    intro ω φ
    have e1 : h' ω φ = h ω φ := by
      have := hT ω φ φ (by
        intro z hz
        refine ⟨z, ?_, by simp [Chart.recenter, Chart.id]⟩
        exact φ.tsupport_subset hz) (by
        intro z _
        simp [Chart.recenter, Chart.id])
      simpa [Chart.recenter, Chart.id] using this
    rw [htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero]), e1]
  have hseed := GW1.seed_lims_eq hκ hb hb' θ hh hshift hC.2.2.1
  have hthr : ForceWord.ThresholdCondition (flowLineRhoL κ b' jumps' 0 θ) (flowLineRhoR κ b' jumps' 0 θ) 0
      (flowLineXL b' jumps' 0) (flowLineXR b' jumps' 0) := by
    rw [GW1.thresholdCondition_flowLine_zero_iff hκ, hseed.1, hseed.2]
    exact hbad
  exact IsIntegratedSLEEvolution.ae_lifetime_eq_zero_of_threshold hC.1 hthr

theorem not_admissible_of_low {κ : ℝ} {hL hR : ℝ} (hlow : hR - Real.pi / 2 * chiC κ ≤ -sleLambda κ) :
    ¬ ExplState.IsAdmissibleSeed κ hL hR (-(Real.pi / 2)) := fun h => by
  have := h.2
  linarith

/-! ### The outward height at `v` -/

/-- **The outward height at the end `v` of the arc is low.** -/
theorem rightLim_low_of_arc {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) {v : ℝ}
    (hv : 0 < v) (hlow0 : rightLim b 0 - Real.pi / 2 * chiC κ ≤ -sleLambda κ)
    (hlow : ∀ x ∈ jumpSet b J, 0 < x → x ≤ v → rightLim b x - Real.pi / 2 * chiC κ ≤ -sleLambda κ) :
    rightLim b v - Real.pi / 2 * chiC κ ≤ -sleLambda κ := by
  by_cases hvJ : v ∈ jumpSet b J
  · exact hlow v hvJ hv le_rfl
  · have hlr : leftLim b v = rightLim b v := by
      by_cases hvJ' : v ∈ J
      · by_contra hne
        exact hvJ (Finset.mem_filter.2 ⟨hvJ', hne⟩)
      · obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.1 (hb v hvJ')
        obtain ⟨δ, hδ, hδ'⟩ := Supp7.exists_pos_eq_lims hb v
        set ε := min (δ / 2) (ε₀ / 2) with hε
        have hε0 : 0 < ε := by positivity
        have hε1 : ε ≤ δ / 2 := min_le_left _ _
        have hε2 : ε ≤ ε₀ / 2 := min_le_right _ _
        obtain ⟨-, -, hr, hl⟩ := hδ' ε hε0 (by linarith)
        have e1 : b (v + ε) = b v := hball (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hε0]; linarith)
        have e2 : b (v - ε) = b v := hball (by
          rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hε0]; linarith)
        rw [← hr, ← hl, e1, e2]
    obtain ⟨δ, hδ, hδ'⟩ := Supp7.exists_pos_eq_lims hb v
    set ε := min (δ / 2) (v / 2) with hε
    have hε0 : 0 < ε := by positivity
    obtain ⟨-, hJ, -, hl⟩ := hδ' ε hε0 (by have := min_le_left (δ / 2) (v / 2); linarith)
    rw [← hlr, ← hl]
    exact le_of_low_arc hb hlow0 hlow (by have := min_le_right (δ / 2) (v / 2); linarith) (by linarith) hJ

/-! ### The walk program -/

/-- The program of the lower walk. -/
def walkProg (b : ℝ → ℝ) (J : Finset ℝ) : List Instr := (boundaryWalkSpec b J (-(Real.pi / 2)) true).2.2

theorem walkProg_zero (b : ℝ → ℝ) (J : Finset ℝ) : (walkProg b J)[0]? = some (.inl (-(Real.pi / 2), ⊤)) := by
  simp [walkProg, boundaryWalkSpec, List.replicate_succ]

theorem walkProg_one (b : ℝ → ℝ) (J : Finset ℝ) : (walkProg b J)[1]? = some (.inr (.inl true)) := by
  simp [walkProg, boundaryWalkSpec, List.replicate_succ]

theorem trInstr_walkProg (v : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) : (walkProg b J).map (trInstr v) = walkProg b J := by
  unfold walkProg boundaryWalkSpec
  simp only [List.map_flatten, List.map_replicate, List.map_cons, List.map_nil]
  rfl

theorem trSpec_walk (v : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) :
    trSpec v (boundaryWalkSpec b J (-(Real.pi / 2)) true) = (-v, false, walkProg b J) := by
  show ((0 : ℝ) - v, false, (walkProg b J).map (trInstr v)) = _
  rw [trInstr_walkProg, zero_sub]

theorem walkSpec_tr {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J) (v : ℝ) :
    boundaryWalkSpec (affData 1 (-v) b) (affJumps 1 (-v) J) (-(Real.pi / 2)) true = (0, false, walkProg b J) := by
  unfold walkProg boundaryWalkSpec
  rw [jumpSet_trData hb, Finset.card_map]

theorem run_two_walk {κ : ℝ} {B : ℝ → ℝ} {JB : Finset ℝ} (x₀ : ℝ) (prog : List Instr)
    (h0 : prog[0]? = some (.inl (-(Real.pi / 2), ⊤))) (h1 : prog[1]? = some (.inr (.inl true)))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ B JB (x₀, false, prog) D 2 =
      ExplState.contStep κ B JB (ExplState.launch (ExplState.init x₀) 0 (D 0) (-(Real.pi / 2)) ⊤) none true := by
  rw [run_succ, show (x₀, false, prog).2.2[1]? = some (.inr (.inl true)) from h1, run_succ,
    show (x₀, false, prog).2.2[0]? = some (.inl (-(Real.pi / 2), ⊤)) from h0]
  rfl

/-! ### The zero-lifetime first launch -/

section Zero

variable {d : (ℝ≥0 → ℝ) × ℝ≥0∞}

theorem stopDrv_eq_zero_of (hreg : IsRegularDriver d) (h0 : d.2 = 0) : stopDrv ⊤ d = fun _ => 0 := by
  funext r
  show d.1 (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ⊤ d.2)).toNNReal = 0
  have e : min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) (min ⊤ (0 : ℝ≥0∞)) = 0 := by simp
  rw [h0, e, ENNReal.toNNReal_zero]
  exact hreg.2.1

theorem lAlive_zero (c : Chart) (hreg : IsRegularDriver d) (h0 : d.2 = 0) {z : ℂ} (hz : c.1 z ≠ 0) :
    lAlive c ⊤ d z := by
  have hT : stopTime ⊤ d = 0 := by
    rw [stopTime, h0, min_eq_right le_top, ENNReal.toNNReal_zero, NNReal.coe_zero]
  unfold lAlive
  rw [stopDrv_eq_zero_of hreg h0, hT]
  refine ⟨fun _ => c.1 z, continuousOn_const, fun t ht => ?_⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst ht0
  simp [hz]

/-- The zero-lifetime launch from the initial state `x₀`. -/
theorem launch_init_zero (x₀ : ℝ) (hreg : IsRegularDriver d) (h0 : d.2 = 0) (θ : ℝ) :
    stStatus (ExplState.launch (ExplState.init x₀) 0 d θ ⊤) = stThr none ∧
      stPt (ExplState.launch (ExplState.init x₀) 0 d θ ⊤) = x₀ ∧
      stAngle (ExplState.launch (ExplState.init x₀) 0 d θ ⊤) = θ ∧
      stRecR (ExplState.launch (ExplState.init x₀) 0 d θ ⊤) = x₀ ∧
      stChart (ExplState.launch (ExplState.init x₀) 0 d θ ⊤) =
        (Chart.id.recenter x₀).loewner (fun _ => 0) 0 := by
  have hmin : min ⊤ d.2 ≠ ⊤ := by rw [h0]; simp
  obtain ⟨hc, ha, hR, -, hst, hpt⟩ := launch_eq_of_ne_top (ExplState.init x₀) 0 d θ ⊤ hmin
  have hT : stopTime ⊤ d = 0 := by
    rw [stopTime, h0, min_eq_right le_top, ENNReal.toNNReal_zero, NNReal.coe_zero]
  have hnlt : ¬ (⊤ : ℝ≥0∞) < d.2 := not_top_lt
  refine ⟨?_, ?_, ha, ?_, ?_⟩
  · rw [hst, lStatus]; simp only [h0, ↓reduceIte]; rfl
  · rw [hpt, lPt]; simp only [h0, ↓reduceIte]; rfl
  · rw [hR, lRecR]
    have hset : {x : ℝ | stRecR (ExplState.init x₀) < x ∧
        ¬ lAlive (stChart (ExplState.init x₀)) ⊤ d x} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      refine lAlive_zero _ hreg h0 ?_
      show (x : ℂ) - (x₀ : ℂ) ≠ 0
      rw [sub_ne_zero, Ne, Complex.ofReal_inj]
      exact (ne_of_lt hx).symm
    rw [hset]
    simp [ExplState.init]
  · rw [hc, stopDrv_eq_zero_of hreg h0, hT]
    rfl

end Zero

end InteractingSLE.Theorem14.SB.Lf
