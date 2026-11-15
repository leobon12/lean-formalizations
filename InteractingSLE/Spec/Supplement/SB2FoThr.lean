/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoLow
import InteractingSLE.Spec.Supplement.SB2FlCore
import InteractingSLE.Spec.Supplement.GW1ActiveThr
import InteractingSLE.Spec.Exist.StagedLaw3Cond
import InteractingSLE.Spec.Supplement.GB6RestartProofWord
import InteractingSLE.Spec.Sec5.Lemma56Stages
import InteractingSLE.Spec.Supplement.SB2LwStop
import InteractingSLE.Spec.Supplement.SB2MzMain
import InteractingSLE.Spec.Supplement.SB2DrvCells
import InteractingSLE.Spec.Supplement.SB2KcPartition

/-!
# D34's left heights: the relative piece's right side is swallowed at its lifetime

Worker PROVE-SB2-F3LAW (round 3, handoff §R2.7 item 3, input (ii)). Under the retained kernel the masked canonical
driver of F3's step is a flow-line driver of the conditional field (`Fl.ae_isFlowLineDriver_maskDrv`), so almost every
path with a finite lifetime is a good stop path (`Exist.StagedLaw.ae_isGoodStopPath`). With the word admissible left
of `0` (D34's left heights) and its seed not at threshold (the seed cell), the lifetime is a right threshold and the
stop word is low just right of `0` (GW1's `GW1W.lowStart_of_goodStopPath`), so the record's first right mark is at
the tip: `markPos 0 = 0` (`markPos_zero_of_lowStart`). The kernel statement is brought back to `P` through a
measurable event (`Supp8.GB6.measurable_markPos_rec`, `Sec5.Lemma56Stages.ae_of_ae_condExpKernel`).

* `markPos_zero_of_lowStart`, **`ae_markPos_zero_driverOf`**, `not_thr_of_mem_seedCell`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Exist Exist.Staged Exist.StagedLaw

/-- **A stop word low just right of `0` has its right side swallowed**: `markPos 0 = 0`. -/
theorem markPos_zero_of_lowStart {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} {θ : ℝ} {r : RecData} {ε : ℝ}
    (hε : 0 < ε) (hlow : ∀ z ∈ Ioo (0 : ℝ) ε, (stopWord κ (c, θ, r)).fn z + θ * chiC κ ≤ -sleLambda κ) :
    markPos (rdrv r) (rtime r) 0 = 0 := by
  have hnn := GW1W.markPos_nonneg (continuous_rdrv r) (rdrv_zero r) (rtime_nonneg r) (le_refl (0 : ℝ))
  by_contra hne
  have hpos : 0 < markPos (rdrv r) (rtime r) 0 := lt_of_le_of_ne hnn (Ne.symm hne)
  set z := min ε (markPos (rdrv r) (rtime r) 0) / 2 with hz
  have hz0 : 0 < z := by positivity
  have hzε : z < ε := by have := min_le_left ε (markPos (rdrv r) (rtime r) 0); linarith
  have hzm : z < markPos (rdrv r) (rtime r) 0 := by
    have := min_le_right ε (markPos (rdrv r) (rtime r) 0); linarith
  have h1 := hlow z ⟨hz0, hzε⟩
  rcases Lh.stopWord_fn_pos_cases c θ r hz0 with h | h
  · rw [h] at h1
    have hl := Sec4.sleLambda_pos hκ
    linarith
  · linarith

/-- **The relative piece's right side is swallowed at its lifetime** (almost surely): for a word `c` measurable for the
marks `𝓜` and a field `Z` that is, under the kernel on `L ∈ 𝓜`, a GFF with data `c`, the canonical flow-line driver
of angle `θ` with a finite lifetime ends at a right threshold whenever the word is admissible left of `0` and its seed
is not at threshold: the record's first right mark is at the tip, `markPos 0 = 0` (GW1's `lowStart_of_goodStopPath`
on the good stop paths of the kernel law, `ae_isGoodStopPath`; back to `P` by
`Lemma56Stages.ae_of_ae_condExpKernel`). -/
theorem ae_markPos_zero_driverOf (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ) {c : Ω → BoundaryWord}
    (hc : Measurable[𝓜] c) {Z : Ω → DistOn upperHalfPlaneOpens} (hZ : Measurable Z) {L : Set Ω}
    (hL : MeasurableSet[𝓜] L)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Z (c ω₀).fn (c ω₀).jumps) :
    ∀ᵐ ω ∂P, ω ∈ L →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL κ (c ω).fn (c ω).jumps 0 θ)
        (flowLineRhoR κ (c ω).fn (c ω).jumps 0 θ) 0 (flowLineXL (c ω).fn (c ω).jumps 0)
        (flowLineXR (c ω).fn (c ω).jumps 0) →
      (∀ y, y < 0 → y ∉ (c ω).jumps → (c ω).fn y + θ * chiC κ < sleLambda κ) →
      (driverOf h12p hκ θ (c ω, Z ω)).2 ≠ ⊤ →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ θ (c ω, Z ω)))) ∧
      markPos (rdrv (recOf ⊤ (driverOf h12p hκ θ (c ω, Z ω)))) (rtime (recOf ⊤ (driverOf h12p hκ θ (c ω, Z ω)))) 0 =
        0 := by
  set Dm := Fl.maskDrv L (fun ω => driverOf h12p hκ θ (c ω, Z ω)) with hDm
  have hcm : Measurable c := hc.mono h𝓜 le_rfl
  have hD : Measurable fun ω => driverOf h12p hκ θ (c ω, Z ω) :=
    (measurable_driverOf h12p hκ θ).comp (hcm.prodMk hZ)
  have hDmm : Measurable Dm := Fl.measurable_maskDrv (h𝓜 _ hL) hD
  have hreg : ∀ ω, IsRegularDriver (Dm ω) :=
    Fl.isRegularDriver_maskDrv fun ω => Mz.isRegularDriver_driverOf h12p hκ _ _
  set Sg : Set Ω := {ω | (Dm ω).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (Dm ω))) ∧
    markPos (rdrv (recOf ⊤ (Dm ω))) (rtime (recOf ⊤ (Dm ω))) 0 = 0} with hSg
  have hSm : MeasurableSet Sg := by
    have h1 : Measurable fun ω => markPos (rdrv (recOf ⊤ (Dm ω))) (rtime (recOf ⊤ (Dm ω))) 0 :=
      Supp8.GB6.measurable_markPos_rec.comp (measurable_recOf hDmm hreg ⊤)
    have h2 : MeasurableSet {ω | (Dm ω).2 = ⊤} := measurableSet_eq_fun (measurable_snd.comp hDmm) measurable_const
    have h3 : MeasurableSet {ω | LocalExt.IsDrvGood (recHist (recOf ⊤ (Dm ω)))} :=
      (measurable_recHist.comp (measurable_recOf hDmm hreg ⊤)) LocalExt.measurableSet_isDrvGood
    exact (h2.union (h3.inter (measurableSet_eq_fun h1 measurable_const))).congr (by
      ext ω; simp only [hSg, mem_union, mem_inter_iff, mem_ofPred_eq]; tauto)
  -- (K1) at a good `ω₀` the kernel puts no mass off `Sg`
  have hK1 : ∀ᵐ ω₀ ∂P, ω₀ ∈ L →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL κ (c ω₀).fn (c ω₀).jumps 0 θ)
        (flowLineRhoR κ (c ω₀).fn (c ω₀).jumps 0 θ) 0 (flowLineXL (c ω₀).fn (c ω₀).jumps 0)
        (flowLineXR (c ω₀).fn (c ω₀).jumps 0) →
      (∀ y, y < 0 → y ∉ (c ω₀).jumps → (c ω₀).fn y + θ * chiC κ < sleLambda κ) →
      condExpKernel P 𝓜 ω₀ Sgᶜ = 0 := by
    filter_upwards [Fl.ae_isFlowLineDriver_maskDrv h12p h13 hκ θ h𝓜 hc hZ hL hlaw] with ω₀ hfl hω₀ hseed hLadm
    obtain ⟨h', 𝓕, VL, VR, B, -, hcoup⟩ := hfl hω₀
    have hgood := ae_isGoodStopPath hκ hreg hcoup.1 hseed ⊤
    refine ae_iff.1 ?_
    filter_upwards [hgood] with ω hgp hfin
    have hgp' := hgp (by rwa [min_eq_right le_top])
    obtain ⟨ε, hε, hlow⟩ := GW1W.lowStart_of_goodStopPath hκ hgp' hLadm
    exact ⟨hgp'.2.2.2.1, markPos_zero_of_lowStart hκ hε hlow⟩
  -- (K2) the kernel law of the event `Sg ∪ Lᶜ ∪ {κ(Sgᶜ) ≠ 0}`
  have hκm : Measurable[𝓜] fun ω₀ => condExpKernel P 𝓜 ω₀ Sgᶜ := measurable_condExpKernel hSm.compl
  set Bad : Set Ω := {ω₀ | condExpKernel P 𝓜 ω₀ Sgᶜ ≠ 0} with hBad
  have hBadm : MeasurableSet[𝓜] Bad := (measurableSet_eq_fun hκm measurable_const).compl
  set E : Set Ω := Sg ∪ (Lᶜ ∪ Bad) with hE
  have hEm : MeasurableSet E := hSm.union ((h𝓜 _ hL).compl.union (h𝓜 _ hBadm))
  have hK2 : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), ω ∈ E := by
    filter_upwards [Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝓜 hBadm,
      Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝓜 hL.compl] with ω₀ hbad hnotL
    by_cases hb : ω₀ ∈ Bad
    · filter_upwards [hbad hb] with ω hω using Or.inr (Or.inr hω)
    · have h0 : condExpKernel P 𝓜 ω₀ Sgᶜ = 0 := by simpa [hBad] using hb
      have h1 : ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), ω ∈ Sg := ae_iff.2 h0
      filter_upwards [h1] with ω hω using Or.inl hω
  have hK3 := Sec5.Lemma56Stages.ae_of_ae_condExpKernel h𝓜 hEm hK2
  filter_upwards [hK1, hK3] with ω h1 h3 hωL hseed hLadm hfin
  have h0 := h1 hωL hseed hLadm
  have hωS : ω ∈ Sg := by
    rcases h3 with h | h | h
    · exact h
    · exact absurd hωL h
    · exact absurd h0 h
  have hDω : Dm ω = driverOf h12p hκ θ (c ω, Z ω) := Fl.maskDrv_of_mem hωL
  have := hωS (by rw [hDω]; exact hfin)
  rwa [hDω] at this

/-- **A seed cell's seed is not at threshold, in flow-line form.** -/
theorem not_thr_of_mem_seedCell {Ω : Type*} {κ θ : ℝ} {cw : Ω → BoundaryWord} {F : Set Ω} {w : Supp8.Q3Stop.WordType}
    {ω : Ω} (hω : ω ∈ Lv.seedCell κ θ cw F w) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ (cw ω).fn (cw ω).jumps 0 θ)
      (flowLineRhoR κ (cw ω).fn (cw ω).jumps 0 θ) 0 (flowLineXL (cw ω).fn (cw ω).jumps 0)
      (flowLineXR (cw ω).fn (cw ω).jumps 0) := by
  have hmem := Lv.mem_typeSet_of_mem_wordTypeCell hω.1
  have hthr := hω.2
  have hw : Lv.angleWordType κ θ (cw ω) = w := hω.1.2
  subst hw
  have h1 : Supp8.Q3Stop.typedRhoL (Lv.angleWordType κ θ (cw ω)) = flowLineRhoL κ (cw ω).fn (cw ω).jumps 0 θ := by
    funext i
    simp only [Supp8.Q3Stop.typedRhoL, Lv.angleWordType, padFL]
    rw [dite_eq_left_of_eq_true (eq_true (show (i : ℕ) < flowLineNL (cw ω).fn (cw ω).jumps 0 from i.2))]
    rfl
  have h2 : Supp8.Q3Stop.typedRhoR (Lv.angleWordType κ θ (cw ω)) = flowLineRhoR κ (cw ω).fn (cw ω).jumps 0 θ := by
    funext j
    simp only [Supp8.Q3Stop.typedRhoR, Lv.angleWordType, padFL]
    rw [dite_eq_left_of_eq_true (eq_true (show (j : ℕ) < flowLineNR (cw ω).fn (cw ω).jumps 0 from j.2))]
    rfl
  have h3 : Lv.cellXL κ θ cw (Lv.angleWordType κ θ (cw ω)) ω = flowLineXL (cw ω).fn (cw ω).jumps 0 := by
    funext i
    simp only [Lv.cellXL, FCDet.typeXL, hmem, ↓reduceIte, Restart.flowPad]
    rw [dite_eq_left_of_eq_true (eq_true (show (i : ℕ) < flowLineNL (cw ω).fn (cw ω).jumps 0 from i.2))]
    rfl
  have h4 : Lv.cellXR κ θ cw (Lv.angleWordType κ θ (cw ω)) ω = flowLineXR (cw ω).fn (cw ω).jumps 0 := by
    funext j
    simp only [Lv.cellXR, FCDet.typeXR, hmem, ↓reduceIte, Restart.flowPad]
    rw [dite_eq_left_of_eq_true (eq_true (show (j : ℕ) < flowLineNR (cw ω).fn (cw ω).jumps 0 from j.2))]
    rfl
  simp only [Set.mem_ofPred_eq] at hthr
  rw [h1, h2, h3, h4] at hthr
  exact hthr

end InteractingSLE.Theorem14.SB.Fo
