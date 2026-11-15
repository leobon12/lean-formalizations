/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefChartWord

/-!
# Lemma 7.25's pocket field data from a random change pocket: the word-shape selection

Packet PROVE-LEMMA725REF4, item 1 (a). Specification §7.4.1, Aux. lemmas 119–122 and 130, Lemma 7.25's proof
(`source/spec/p385-432.md` L401–L515, pp. 408–414: "The inversion in Aux. lemma 120 gives the two near-entry seed
weights … Every actual angle-change mark on a selected open arc remains present").

As `PocketWordAssembly.pocketWordEvolution_of_cfPocketConfig`, `PocketSeedOpen.pocketWordEvolution_of_cfPocketConfigInf`
and `…_of_changeConfig` (PROVE-STRIPSYS20, 26), with `PocketChartFieldStatement` as the conclusion: one walls-measurable
Jordan coordinate `ψ` with its marks (`exists_measurable_pocketMarks_pts`, `…Inf_pts`), the four-mark word
`(wordL2; wordR2)` on the event where the right wall's change point is on the selected right arc and the three-mark word
`(wordL1; wordR2)` off it (whichever has positive probability), and the bounded pocket or the pocket opening at the flow
seed (whichever has positive probability).

## Main results

* `pocketChartField_of_cfPocketConfig`, `pocketChartField_of_cfPocketConfigInf`;
* `pocketChartField_of_changeConfig`, **`pocketChartField_of_changeConfig'`** (`κ′ = 16/κ`, both-low seed weights).

Conditional helpers; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefChart

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C
  PocketCoupling PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField Lemma725RefSafe

universe u

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketChartFieldStatement` from a random bounded change pocket** (the word-shape selection of
`pocketWordEvolution_of_cfPocketConfig`): `PocketChartFieldStatement (16/κ) r_L r_R` from `PocketStopWallsInput` and
`PocketDetInput` on `G`. -/
theorem pocketChartField_of_cfPocketConfig [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G)
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) (hin : PocketStopWallsInput κ rL rR 𝓦 P R L r W η G h₀ u)
    (hdet : PocketDetInput κ 𝓦 P R L r η G fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :
    PocketChartFieldStatement.{u} (16 / κ) rL rR := by
  have hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hG0 : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r := fun ω hω => (hcfg ω hω).bounded
  obtain ⟨ψ, hψ, hψm, -, hxRp, -, hxL2n⟩ := exists_measurable_pocketMarks_pts (mΩ := 𝓦) hRm hLm hGm hconf
    (fun ω hω => zero_notMem_closure_of_rightLo_pos (hcfg ω hω).conf (hcfg ω hω).bounded)
    (fun ω hω => (hcfg ω hω).oriented) (discTime 1)
  obtain ⟨hρL2, hρL1, hρR, hsL2, hsL1, hsR, -, -⟩ := lemma725_word hκ hκ4 hL hR
  set E := {ω | ω ∈ G ∧ discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)} with hEdef
  have hEm : MeasurableSet[𝓦] E := (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).2 _
  have hxRd : ∀ A ⊆ G, ∀ ω ∈ A, ∀ j : Fin 1, 0 < marksRAll L r ψ ω j.succ := fun A hAG ω hω j => by
    have hj : j.succ = (1 : Fin 2) := by fin_cases j; rfl
    rw [hj]
    simpa [marksRAll] using hxRp ω (hAG hω)
  by_cases hE : 0 < P E
  · -- the four-mark word: `R(1)` on the selected right arc
    have hmk := measurable_marks (m := 𝓦) hRm hLm hconf hG0 hψm hEm (fun ω hω => hω.1)
    refine pocketChartField_cfPocket hρL2 hρR hsL2 hsR h𝓦 hRm hLm hGm hcfg hηm hEm (fun ω hω => hω.1) hE
      (fun ω hω => hψ ω hω.1) hψm (hmk.2 fun ω hω => hω.2) hmk.1 (fun ω _ => by simp [marksL2All])
      (fun ω _ => by simp [marksRAll]) (fun ω hω i => ?_) (hxRd E fun ω hω => hω.1)
      (fun ω hω => antitone_vec_two (hxL2n ω hω.1 hω.2).le)
      (fun ω hω => monotone_vec_two (hxRp ω hω.1).le) hh₀ hu hub
      ((hin E hEm (fun ω hω => hω.1) hE ψ (fun ω hω => hψ ω hω.1) hψm).1 fun ω hω => hω.2)
      ((hdet E hEm (fun ω hω => hω.1) hE ψ (fun ω hω => hψ ω hω.1) hψm).1 fun ω hω => hω.2)
    have hi : i.succ = (1 : Fin 2) := by fin_cases i; rfl
    rw [hi]
    simpa [marksL2All] using hxL2n ω hω.1 hω.2
  · -- the three-mark word: `R(1)` off the selected right arc
    have hPE : P E = 0 := le_antisymm (not_lt.1 hE) zero_le
    have hPA : 0 < P (G \ E) := by
      have h1 : P G ≤ P (G ∩ E) + P (G \ E) := measure_le_inter_add_sdiff P G E
      have h2 : P (G ∩ E) = 0 := measure_mono_null inter_subset_right hPE
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    have hmk := measurable_marks (m := 𝓦) hRm hLm hconf hG0 hψm (hGm.diff hEm) sdiff_subset
    exact pocketChartField_cfPocket hρL1 hρR hsL1 hsR h𝓦 hRm hLm hGm hcfg hηm (hGm.diff hEm) sdiff_subset hPA
      (fun ω hω => hψ ω hω.1) hψm measurable_const hmk.1 (fun ω _ => rfl) (fun ω _ => by simp [marksRAll])
      (fun ω _ i => i.elim0) (hxRd _ sdiff_subset) (fun ω _ => antitone_vec_one)
      (fun ω hω => monotone_vec_two (hxRp ω hω.1).le) hh₀ hu hub
      ((hin (G \ E) (hGm.diff hEm) sdiff_subset hPA ψ (fun ω hω => hψ ω hω.1) hψm).2
        fun ω hω hc => hω.2 ⟨hω.1, hc⟩)
      ((hdet (G \ E) (hGm.diff hEm) sdiff_subset hPA ψ (fun ω hω => hψ ω hω.1) hψm).2
        fun ω hω hc => hω.2 ⟨hω.1, hc⟩)

/-- **`PocketChartFieldStatement` from a random change pocket opening at the flow seed** (the word-shape selection
of `pocketWordEvolution_of_cfPocketConfigInf`). -/
theorem pocketChartField_of_cfPocketConfigInf [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G)
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) (hin : PocketStopWallsInputInf κ rL rR 𝓦 P R L r W η G h₀ u)
    (hdet : PocketDetInputInf κ 𝓦 P R L r η G fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :
    PocketChartFieldStatement.{u} (16 / κ) rL rR := by
  have hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hG0 : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 := fun ω hω => (hcfg ω hω).seed
  obtain ⟨ψ, hψ, hψm, -, hxRp, -, hxL2n⟩ := exists_measurable_pocketMarksInf_pts (mΩ := 𝓦) hRm hLm hGm hconf
    hG0 (fun ω hω => (hcfg ω hω).oriented) (discTime 1)
  obtain ⟨hρL2, hρL1, hρR, hsL2, hsL1, hsR, -, -⟩ := lemma725_word hκ hκ4 hL hR
  set E := {ω | ω ∈ G ∧ discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)} with hEdef
  have hEm : MeasurableSet[𝓦] E := (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).2 _
  have hxRd : ∀ A ⊆ G, ∀ ω ∈ A, ∀ j : Fin 1, 0 < marksRAll L r ψ ω j.succ := fun A hAG ω hω j => by
    have hj : j.succ = (1 : Fin 2) := by fin_cases j; rfl
    rw [hj]
    simpa [marksRAll] using hxRp ω (hAG hω)
  by_cases hE : 0 < P E
  · have hmk := measurable_marksInf (m := 𝓦) hRm hLm hconf hG0 hψm hEm (fun ω hω => hω.1)
    refine pocketChartField_cfPocketInf hρL2 hρR hsL2 hsR h𝓦 hRm hLm hGm hcfg hηm hEm (fun ω hω => hω.1) hE
      (fun ω hω => hψ ω hω.1) hψm (hmk.2 fun ω hω => hω.2) hmk.1 (fun ω _ => by simp [marksL2All])
      (fun ω _ => by simp [marksRAll]) (fun ω hω i => ?_) (hxRd E fun ω hω => hω.1)
      (fun ω hω => antitone_vec_two (hxL2n ω hω.1 hω.2).le)
      (fun ω hω => monotone_vec_two (hxRp ω hω.1).le) hh₀ hu hub
      ((hin E hEm (fun ω hω => hω.1) hE ψ (fun ω hω => hψ ω hω.1) hψm).1 fun ω hω => hω.2)
      ((hdet E hEm (fun ω hω => hω.1) hE ψ (fun ω hω => hψ ω hω.1) hψm).1 fun ω hω => hω.2)
    have hi : i.succ = (1 : Fin 2) := by fin_cases i; rfl
    rw [hi]
    simpa [marksL2All] using hxL2n ω hω.1 hω.2
  · have hPE : P E = 0 := le_antisymm (not_lt.1 hE) zero_le
    have hPA : 0 < P (G \ E) := by
      have h1 : P G ≤ P (G ∩ E) + P (G \ E) := measure_le_inter_add_sdiff P G E
      have h2 : P (G ∩ E) = 0 := measure_mono_null inter_subset_right hPE
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    have hmk := measurable_marksInf (m := 𝓦) hRm hLm hconf hG0 hψm (hGm.diff hEm) sdiff_subset
    exact pocketChartField_cfPocketInf hρL1 hρR hsL1 hsR h𝓦 hRm hLm hGm hcfg hηm (hGm.diff hEm) sdiff_subset hPA
      (fun ω hω => hψ ω hω.1) hψm measurable_const hmk.1 (fun ω _ => rfl) (fun ω _ => by simp [marksRAll])
      (fun ω _ i => i.elim0) (hxRd _ sdiff_subset) (fun ω _ => antitone_vec_one)
      (fun ω hω => monotone_vec_two (hxRp ω hω.1).le) hh₀ hu hub
      ((hin (G \ E) (hGm.diff hEm) sdiff_subset hPA ψ (fun ω hω => hψ ω hω.1) hψm).2
        fun ω hω hc => hω.2 ⟨hω.1, hc⟩)
      ((hdet (G \ E) (hGm.diff hEm) sdiff_subset hPA ψ (fun ω hω => hψ ω hω.1) hψm).2
        fun ω hω hc => hω.2 ⟨hω.1, hc⟩)

/-- **`PocketChartFieldStatement` from a random change pocket of either kind** (as
`PocketSeedOpen.pocketWordEvolution_of_changeConfig`): the bounded pocket where it has positive probability, the pocket
opening at the flow seed otherwise. -/
theorem pocketChartField_of_changeConfig [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hL : rL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : rR ∈ Ioo (-2) (counterflowA κ - 2))
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G)
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketStopWallsInput κ rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h₀ u)
    (hinI : PocketStopWallsInputInf κ rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h₀ u)
    (hdet : PocketDetInput κ 𝓦 P R L r η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r}
      fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u)
    (hdetI : PocketDetInputInf κ 𝓦 P R L r η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r}
      fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :
    PocketChartFieldStatement.{u} (16 / κ) rL rR := by
  set Gp := {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} with hGpdef
  have hGpm : MeasurableSet[𝓦] Gp := (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).1
  have hG0 : {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} = G \ Gp := by
    ext ω
    simp only [hGpdef, mem_ofPred_eq, Set.mem_sdiff, not_and]
    exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
  have hseed : ∀ ω ∈ G \ Gp, rightLo (R ω) (L ω) r = 0 := fun ω hω =>
    le_antisymm (not_lt.1 fun h => hω.2 ⟨hω.1, h⟩) ((hconf ω hω.1).changeCorner_props.1.1)
  by_cases hp : 0 < P Gp
  · exact pocketChartField_of_cfPocketConfig hκ hκ4 hL hR h𝓦 hRm hLm hGpm hp (fun ω hω => hcfg ω hω.1 hω.2) hηm
      hh₀ hu hub hin hdet
  · have hPA : 0 < P (G \ Gp) := by
      have h1 : P G ≤ P (G ∩ Gp) + P (G \ Gp) := measure_le_inter_add_sdiff P G Gp
      have h2 : P (G ∩ Gp) = 0 := measure_mono_null inter_subset_right (le_antisymm (not_lt.1 hp) zero_le)
      rw [h2, zero_add] at h1
      exact lt_of_lt_of_le hPG h1
    rw [hG0] at hinI hdetI
    exact pocketChartField_of_cfPocketConfigInf hκ hκ4 hL hR h𝓦 hRm hLm (hGm.diff hGpm) hPA
      (fun ω hω => hcfgI ω hω.1 (hseed ω hω)) hηm hh₀ hu hub hinI hdetI

/-- **`PocketChartFieldStatement κ′ r_L r_R` from a random change pocket of either kind** (`κ′ > 4`, both-low seed
weights; the form of `pocketWordEvolution_of_changeConfig'` for the flow parameter `κ = 16/κ′`). -/
theorem pocketChartField_of_changeConfig' [StandardBorelSpace Ω] [IsProbabilityMeasure P] {κ' rL rR : ℝ}
    (hκ' : 4 < κ') (hL : -2 < rL) (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t)
    (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G)
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M)
    (hin : PocketStopWallsInput (16 / κ') rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h₀ u)
    (hinI : PocketStopWallsInputInf (16 / κ') rL rR 𝓦 P R L r W η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h₀ u)
    (hdet : PocketDetInput (16 / κ') 𝓦 P R L r η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r}
      fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u)
    (hdetI : PocketDetInputInf (16 / κ') 𝓦 P R L r η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r}
      fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) :
    PocketChartFieldStatement.{u} κ' rL rR := by
  have hκ0 : 0 < κ' := by linarith
  have hκ : 0 < 16 / κ' := by positivity
  have hκ4 : 16 / κ' < 4 := by rw [div_lt_iff₀ hκ0]; linarith
  have hinv : 16 / (16 / κ') = κ' := by field_simp
  have hA : counterflowA (16 / κ') - 2 = κ' / 2 - 4 := by
    show 16 / (16 / κ') / 2 - 2 - 2 = κ' / 2 - 4
    rw [hinv]; ring
  have h := pocketChartField_of_changeConfig hκ hκ4 ⟨hL, by rw [hA]; exact hLd⟩ ⟨hR, by rw [hA]; exact hRd⟩
    h𝓦 hRm hLm hGm hPG hconf hcfg hcfgI hηm hh₀ hu hub hin hinI hdet hdetI
  rwa [hinv] at h

end InteractingSLE.Sec7.Lemma725RefChart
