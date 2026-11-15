/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1TermKernel

/-!
# BW1 at a walk launch: lifting the identification to the original probability

Packet PROVE-BW1. `ae_kernel_isTermRelOf` identifies the canonical post-piece counterflow `Q` with the relative
counterflow of the launch counterflow `V` under the regular conditional laws. The relation is not a measurable event
(ruling R51); with `DetTerminalStatement` the event "`(V, D) ∈ G` and `Q = R(V, D)` at rational times" is measurable,
holds under almost every conditional law, hence (twice the tower property) `P`-almost surely, and gives the relation
back for the continuous `Q`.

* **`ae_isTermRelOf_pos`**: `P`-almost surely at a next launch whose piece has positive lifetime, `Q` is regular and is
  the relative counterflow of `V` after the piece.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Term

open Exist Exist.StagedLaw Exist.Staged GW1RestartPair

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- The record lifetime of the piece at a launch is its lifetime. -/
theorem pastMap_last_snd_fst {right : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hl : (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (k + 1)).2.2.2.1 k ≠ none) :
    (((fun i : Fin (k + 1) =>
      let r := (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) D (k + 1)).2.2.1 i
      ((fun q : ℚ => r.1 (q : ℝ).toNNReal), r.2.1, r.2.2)) (Fin.last k)).2.1) = (D k).2 := by
  simp only [Fin.val_last]
  rw [retained_run_walk hl]
  simp [retOf]

/-- **`P`-almost surely at a next launch whose piece has positive lifetime, the canonical post-piece counterflow is
regular and is the relative counterflow of the launch counterflow after the piece.** -/
theorem ae_isTermRelOf_pos (hBW1 : BW1.BW1Statement.{u}) (hDet : DetTerminalStatement)
    (h12p : Exist.Staged.Theorem12ParamStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {right : Bool} {n : ℕ}
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hdata : RestartData κ b jumps P h W' ζ' E right n V ζV ℓ) {Q : ℝ≥0 → Ω → ℝ} {ζQ : Ω → ℝ≥0∞}
    (hQ : GW1Laws.IsTerminalRestartCond κ b jumps P h right (E (GW1Z.walkSpec b jumps right)) n Q ζQ)
    (hQreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      ζQ ω = ⊤ ∧ Continuous (fun t => Q t ω) ∧ Q 0 ω = 0) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
        (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2 ≠ 0 →
      GW1Path.IsRegCf (fun t => Q t ω) ∧
        IsTermRelOf (fun t => Q t ω) (fun t => V t ω) (E (GW1Z.walkSpec b jumps right) (2 * n) ω) := by
  classical
  obtain ⟨R, G, hRm, hGm, hRG⟩ := hDet
  have hκ := hdata.pos
  have hb := hdata.boundary
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (GW1Z.walkAngle_mem_Icc right) right
  have hE := hdata.staged _ hprog
  have hreg := hdata.regular (GW1Z.walkSpec b jumps right)
  have hRp := hdata.pieces _ hprog
  -- the measurable identification event
  have hVm : ∀ t, Measurable (V t) := hdata.current.1
  have hpair : Measurable fun ω => ((fun t => V t ω), E (GW1Z.walkSpec b jumps right) (2 * n) ω) :=
    (measurable_pi_iff.mpr hVm).prodMk (hE.1 (2 * n))
  set M : Set Ω := ((fun ω => ((fun t => V t ω), E (GW1Z.walkSpec b jumps right) (2 * n) ω)) ⁻¹' G) ∩
    ⋂ q : ℚ, {ω | Q (Real.toNNReal q) ω =
      R (fun t => V t ω) (E (GW1Z.walkSpec b jumps right) (2 * n) ω) (Real.toNNReal q)} with hMdef
  have hM : MeasurableSet M :=
    (hpair hGm).inter (MeasurableSet.iInter fun q => measurableSet_eq_fun (hQ.1 _) ((hRm _).comp hpair))
  -- the events
  have hpm : ∀ k, Measurable[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k]
      (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) k) := fun k s hs => by
    rw [pastSigma_eq_comap]
    exact ⟨s, hs, rfl⟩
  have hL0 := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * n)
  have hLn := GW1W.measurableSet_pastSigma_launch (κ := κ) hb (GW1Z.walkSpec b jumps right) hE.1 hreg (2 * (n + 1))
  rw [GW1RestartPair.pastSigma_walk_connector] at hLn
  set L' : Set Ω := {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none} ∩
    {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none} ∩
    {ω | (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω
      (Fin.last (2 * n))).2.1 ≠ 0} with hL'def
  have hL' : MeasurableSet[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right))
      (2 * n + 1)] L' := by
    refine ((pastSigma_mono (κ := κ) (b := b) (jumps := jumps) _ _ (Nat.le_succ (2 * n)) _ hL0).inter hLn).inter ?_
    have hc : Measurable[pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right))
        (2 * n + 1)] fun ω => (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right))
          (2 * n + 1) ω (Fin.last (2 * n))).2.1 :=
      measurable_fst.comp (measurable_snd.comp ((measurable_pi_apply _).comp (hpm (2 * n + 1))))
    exact (hc (measurableSet_singleton 0)).compl
  -- the regularity
  have hVreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      GW1Path.IsRegCf (fun t => V t ω) := by
    filter_upwards [hdata.current.2.2] with ω hω hl
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    obtain ⟨-, hc, h0, htr, -⟩ := hω c θ hcθ
    exact ⟨hc, h0, htr⟩
  have hDreg : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none →
      GW1P.PieceRegular (E (GW1Z.walkSpec b jumps right) (2 * n) ω).1
        (min ⊤ (E (GW1Z.walkSpec b jumps right) (2 * n) ω).2) := by
    filter_upwards [hRp] with ω hω hl
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    have := hω (2 * n) θ _ c (eq_launch_of_launches _ _ hcθ).1 hcθ
    rwa [GW1W.instrTime_walk hl] at this
  have hcg : @MeasurableSpace.CountablyGenerated Ω
      (pastSigma κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) := by
    rw [pastSigma_eq_comap]
    exact MeasurableSpace.CountablyGenerated.comap _
  -- (1) under the conditional laws given the retained past before `2n + 1`
  have hT1 : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none} →
      ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), ω₁ ∈ L' →
        ∀ᵐ ω ∂(condExpKernel (condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀) (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
            (E (GW1Z.walkSpec b jumps right)) (2 * n + 1)) ω₁), ω ∈ M := by
    filter_upwards [ae_kernel_isTermRelOf hBW1 h12p hT13 hT13₀ hdata hQ,
      KernelTower.ae_ae_condExpKernel_condExpKernel_eq (P := P)
        (pastSigma_mono (κ := κ) (b := b) (jumps := jumps) (GW1Z.walkSpec b jumps right)
          (E (GW1Z.walkSpec b jumps right)) (Nat.le_succ (2 * n))) (hE.2.1 (2 * n + 1)) hcg,
      Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n))
        (Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n + 1)) (hVreg.and (hDreg.and hQreg))),
      Sec7.Aux122Disint.ae_ae_condExpKernel (hE.2.1 (2 * n))
        (Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) (hE.2.1 (2 * n + 1)) hL')]
      with ω₀ hk hkk hreg2 hmem2 hl0
    filter_upwards [hk hl0, hkk, hreg2, hmem2] with ω₁ hk1 hkk1 hreg1 hmem1 hL1
    rw [hkk1]
    obtain ⟨⟨hl1, hn1⟩, hp1⟩ := hL1
    have hpos : (E (GW1Z.walkSpec b jumps right) (2 * n) ω₁).2 ≠ 0 := by
      have e := pastMap_last_snd_fst (κ := κ) (b := b) (jumps := jumps) hl1
      rw [← e]
      exact hp1
    filter_upwards [hk1 hn1 hpos, hreg1, hmem1 ⟨⟨hl1, hn1⟩, hp1⟩] with ω hrel hregω hmemω
    obtain ⟨⟨hlω, hnω⟩, -⟩ := hmemω
    obtain ⟨hVr, hDr, hQr⟩ := hregω
    have hVr' := hVr hlω
    have hDr' := hDr hlω
    have hQc := (hQr hnω).2.1
    have hG := ((hRG _ _ hVr' (hreg (2 * n) ω) hDr').1).2 ⟨_, hQc, hrel⟩
    have hQR := (((hRG _ _ hVr' (hreg (2 * n) ω) hDr').2 hG).2 _ hQc).1 hrel
    exact ⟨hG, mem_iInter.2 fun q => congrFun hQR _⟩
  -- (2) under the conditional laws given the retained past before `2n`
  have hT2 : ∀ᵐ ω₀ ∂P, ω₀ ∈ {ω | (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
      (fun j => E (GW1Z.walkSpec b jumps right) j ω) (2 * n + 1)).2.2.2.1 (2 * n) ≠ none} →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (GW1Z.walkSpec b jumps right)
        (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀), ω ∈ L'ᶜ ∪ M := by
    filter_upwards [hT1] with ω₀ hω₀ hl0
    have h2 := GW2Later.ae_of_ae_condExpKernel_on' (P := condExpKernel P (pastSigma κ b jumps
      (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n)) ω₀) (hE.2.1 (2 * n + 1)) hL' hM
      (hω₀ hl0)
    filter_upwards [h2] with ω hω
    by_cases hωL : ω ∈ L'
    · exact Or.inr (hω hωL)
    · exact Or.inl hωL
  -- (3) under `P`
  have hT3 := GW2Later.ae_of_ae_condExpKernel_on' (hE.2.1 (2 * n)) hL0
    ((hE.2.1 (2 * n + 1) _ hL').compl.union hM) hT2
  -- (4) the conclusion
  have hprev : ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * (n + 1) + 1)).2.2.2.1 (2 * (n + 1)) ≠ none →
      (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right) (fun j => E (GW1Z.walkSpec b jumps right) j ω)
        (2 * n + 1)).2.2.2.1 (2 * n) ≠ none := by
    filter_upwards [hdata.stages, hRp] with ω hs hp
    apply GW1LaunchClock.previous_launch_of_next hκ hb _ (fun j => hreg j ω) hs ?_ hdata.lt_card
    intro j c θ hl
    exact hp j θ _ c (eq_launch_of_launches _ _ hl).1 hl
  filter_upwards [hT3, hprev, hVreg, hDreg, hQreg] with ω hω hpv hVr hDr hQr hn hpos
  have hl := hpv hn
  have hωL : ω ∈ L' := by
    refine ⟨⟨hl, hn⟩, ?_⟩
    change (pastMap κ b jumps (GW1Z.walkSpec b jumps right) (E (GW1Z.walkSpec b jumps right)) (2 * n + 1) ω
      (Fin.last (2 * n))).2.1 ≠ 0
    have e := pastMap_last_snd_fst (κ := κ) (b := b) (jumps := jumps) hl
    simp only [pastMap]
    rw [e]
    exact hpos
  obtain ⟨hG, hq⟩ := (hω hl).resolve_left (fun h => h hωL)
  rw [mem_iInter] at hq
  have hVr' := hVr hl
  have hDr' := hDr hl
  obtain ⟨hRc, hiff⟩ := (hRG _ _ hVr' (hreg (2 * n) ω) hDr').2 hG
  have hQR : (fun t => Q t ω) = R (fun t => V t ω) (E (GW1Z.walkSpec b jumps right) (2 * n) ω) :=
    Continuous.ext_on denseRange_toNNReal_rat (hQr hn).2.1 hRc.1 (by rintro _ ⟨q, rfl⟩; exact hq q)
  refine ⟨hQR ▸ hRc, (hiff _ (hQr hn).2.1).2 hQR⟩

end InteractingSLE.Theorem14.BW1Term
