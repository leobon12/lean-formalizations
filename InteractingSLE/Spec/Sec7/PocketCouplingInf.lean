/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketCoupling

/-!
# Theorem 1.3's pocket word: the coupling input at infinity and hPW from the pocket chart inputs

Packet PROVE-STRIPSYS26. Specification §7.4.1, Aux. lemma 130's proof (`source/spec/p385-432.md` L482–L489,
pp. 412–413, the case `x₀ = x`), Lemma 7.25's proof (pp. 413–414).

* `travAllInf`, `PocketChartInputInf`: the traversal at infinity and the pocket chart inputs at infinity;
* `changePtL_memInf`, `changePtR_memInf`, `measurable_marksInf`, `measurable_indicator_applyInf`;
* **`pocketCouplingInputInf_of_chartInputInf`**: STRIPSYS23's `PocketSeedOpen.PocketCouplingInputInf` from
  `PocketChartInputInf`;
* **`pocketWordEvolution_of_chartInput'`**: hPW (`Lemma725Ref.PocketWordEvolution κ′ r_L r_R`, `κ′ > 4`, both-low seed
  weights) from a random change pocket of either kind, the counterflow measurable at fixed times, a measurable
  physical field and the pocket chart inputs of both kinds (`PocketSeedOpen.pocketWordEvolution_of_changeConfig'`).

Conditional helpers; they replace no source theorem. Ruling R48 respected (as in `PocketCoupling`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketCoupling

open PocketTraversal PocketAdapt PhaseSel Lemma71C

section InfDefs

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen

variable {Ω : Type*}

/-- The erased counterflow traversal at infinity in the Jordan coordinate `ψ`, read on all of `Ω`. -/
def travAllInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) : Ω → ℝ → ℂ :=
  fun ω => cfTraversalInf (R ω) (L ω) r (η ω) (ψ ω)

theorem travSubInf_eq (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (A : Set Ω) :
    travSubInf R L r η ψ A = fun ω : A => travAllInf R L r η ψ ω := rfl

/-- **The pocket inputs on every word-shape event, pocket opening at the flow seed** (the field-level form of
`PocketSeedOpen.PocketCouplingInputInf`): `PocketChartInput` with the Jordan coordinates at infinity and the traversal
at infinity. -/
def PocketChartInputInf (κ rL rR : ℝ) (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (G : Set Ω) (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ A : Set Ω, MeasurableSet[𝓦] A → A ⊆ G → 0 < P A → ∀ ψ : Ω → ℂ → ℂ,
    (∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω)) → @IsPointMeasurableInf Ω 𝓦 R L r G ψ →
    ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketChartLaw (16 / κ) (wordL2 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) (marksL2All R ψ) (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h) ∧
    ((∀ ω ∈ A, discTime 1 ∉ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
      PocketChartLaw (16 / κ) (wordL1 κ (rs136Theta1 κ rL)) (wordR2 κ (rs136Theta2 κ rR)) 𝓦 P A
        (travAllInf R L r η ψ) marksL1All (marksRAll L r ψ) (fun ω => cfPocket (R ω) (L ω) r) ψ h)

end InfDefs

section InfArcs

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The left wall's change point lies in the closure of a pocket opening at the flow seed. -/
theorem changePtL_memInf (hG : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) :
    cfPt (toDisc (realPath L) (discTime r)) ∈ closure (cfPocket R L r) := by
  have hP := hG.isCfPocketInf h0
  have hd := hG.changeCorners.2.2.2.2.1
  rw [hG.leftLo_eq_zero_of_rightLo_eq_zero h0] at hd
  obtain ⟨v, hv, he⟩ := exists_div_one_add_eq hd.1 hd.2.le
  have hm : cfPt (toDisc (realPath L) (discTime r)) ∈ frontier (cfPocket R L r) := by
    rw [hP.frontier_eq]
    exact Or.inr ⟨v, hv, by simp only [cfArcLInf, he]⟩
  exact frontier_subset_closure hm

/-- The right wall's point at disc time `c₁` lies in the closure of a pocket opening at the flow seed when `c₁` is
between the ends of the selected right arc. -/
theorem changePtR_memInf (hG : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {c₁ : ℝ}
    (hc : c₁ ∈ Ioo (rightLo R L r) (rightHi R L r)) :
    cfPt (toDisc (realPath R) c₁) ∈ closure (cfPocket R L r) := by
  have hP := hG.isCfPocketInf h0
  rw [h0] at hc
  obtain ⟨v, hv, he⟩ := exists_div_one_add_eq hc.1 hc.2.le
  have hm : cfPt (toDisc (realPath R) c₁) ∈ frontier (cfPocket R L r) := by
    rw [hP.frontier_eq]
    exact Or.inl ⟨v, hv, by simp only [cfArcRInf, he]⟩
  exact frontier_subset_closure hm

end InfArcs

section InfMarks

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketSeedOpen

variable {Ω : Type*} [m : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}

/-- **The marks of a measurable Jordan coordinate at infinity are measurable for the walls.** -/
theorem measurable_marksInf (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hG0 : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0)
    {ψ : Ω → ℂ → ℂ} (hψm : IsPointMeasurableInf R L r G ψ) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G) :
    Measurable[MeasurableSpace.comap Subtype.val m] (fun ω : A => marksRAll L r ψ ω) ∧
      ((∀ ω ∈ A, discTime 1 ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r)) →
        Measurable[MeasurableSpace.comap Subtype.val m] (fun ω : A => marksL2All R ψ ω)) := by
  have hpL : Measurable fun ω => cfPt (toDisc (realPath (L ω)) (discTime r)) :=
    measurable_cfPt.comp (measurable_toDisc_apply hLm _)
  have hpR : Measurable fun ω => cfPt (toDisc (realPath (R ω)) (discTime 1)) :=
    measurable_cfPt.comp (measurable_toDisc_apply hRm _)
  refine ⟨?_, fun hs => ?_⟩
  · exact PocketWordAssembly.measurable_vec_two (measurable_sub_re (hψm A hA hAG _ hpL fun ω hω =>
      changePtL_memInf (hG ω (hAG hω)) (hG0 ω (hAG hω))))
  · exact PocketWordAssembly.measurable_vec_two (measurable_sub_re (hψm A hA hAG _ hpR fun ω hω =>
      changePtR_memInf (hG ω (hAG hω)) (hG0 ω (hAG hω)) (hs ω hω)))

/-- **The Jordan coordinate at infinity at fixed points of the pocket is measurable for the walls.** -/
theorem measurable_indicator_applyInf (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    {ψ : Ω → ℂ → ℂ} (hψm : IsPointMeasurableInf R L r G ψ) {A : Set Ω} (hA : MeasurableSet A) (hAG : A ⊆ G)
    (z : ℂ) :
    MeasurableSet {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} ∧
      Measurable ({ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r}.indicator fun ω => ψ ω z) := by
  have hE : {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} = A ∩ {ω | ω ∈ G ∧ z ∈ cfPocket (R ω) (L ω) r} := by
    ext ω
    exact ⟨fun h => ⟨h.1, hAG h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hEm : MeasurableSet {ω | ω ∈ A ∧ z ∈ cfPocket (R ω) (L ω) r} := by
    rw [hE]
    exact hA.inter (PocketTraversalMeasRand.measurableSet_mem_cfPocket hRm hLm hGm hG z)
  exact ⟨hEm, hψm _ hEm (fun ω hω => hAG hω.1) (fun _ => z) measurable_const fun ω hω => subset_closure hω.2⟩

end InfMarks

section InfInput

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketWordAssembly PocketSeedOpen

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`PocketCouplingInputInf` from the pocket chart inputs at infinity** (packet PROVE-STRIPSYS26; Aux. lemma 130's
case `x₀ = x`, p. 412–413). -/
theorem pocketCouplingInputInf_of_chartInputInf {κ rL rR : ℝ} (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hcfg : ∀ ω ∈ G, IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hin : PocketChartInputInf κ rL rR 𝓦 P R L r η G h) :
    PocketCouplingInputInf κ rL rR 𝓦 P R L r η G := by
  intro A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hG0 : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 := fun ω hω => (hcfg ω hω).seed
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) := fun ω hω =>
    ((hcfg ω (hAG hω)).isDrivenCurve (hψ ω hω)).1
  have hmk := measurable_marksInf (m := 𝓦) hRm hLm hG hG0 hψm hA hAG
  have hpt := fun z => measurable_indicator_applyInf (m := 𝓦) hRm hLm hGm hG hψm hA hAG z
  rw [travSubInf_eq, marksR_eq, marksL2_eq, marksL1_eq]
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · exact pocketCouplingClause_of_chartLaw h𝓦 hA hPA hγ (hmk.2 hs) hmk.1 (fun z => (hpt z).1)
      (fun z => (hpt z).2) hh ((hin A hA hAG hPA ψ hψ hψm).1 hs)
  · exact pocketCouplingClause_of_chartLaw h𝓦 hA hPA hγ measurable_const hmk.1 (fun z => (hpt z).1)
      (fun z => (hpt z).2) hh ((hin A hA hAG hPA ψ hψ hψm).2 hs)

/-- **hPW from the pocket chart inputs** (`κ′ > 4`, both-low seed weights; Lemma 7.25's proof with Aux. lemmas
119–125 and 130): `PocketSeedOpen.pocketWordEvolution_of_changeConfig'` with the two coupling inputs derived from the
pocket chart inputs of both kinds of change pocket, for one measurable physical field `h`. -/
theorem pocketWordEvolution_of_chartInput'.{v} {κ' rL rR : ℝ} (hκ' : 4 < κ') (hL : -2 < rL)
    (hLd : rL < κ' / 2 - 4) (hR : -2 < rR) (hRd : rR < κ' / 2 - 4)
    {Ω : Type v} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝓦 : 𝓦 ≤ mΩ) {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0}
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t)
    {G : Set Ω} (hGm : MeasurableSet[𝓦] G) (hPG : 0 < P G) {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ}
    (hconf : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hcfg : ∀ ω ∈ G, 0 < rightLo (R ω) (L ω) r → IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hcfgI : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0 → IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hηm : ∀ u, 0 ≤ u → Measurable fun ω => η ω u) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hin : PocketChartInput (16 / κ') rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} h)
    (hinI : PocketChartInputInf (16 / κ') rL rR 𝓦 P R L r η {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} h) :
    Lemma725Ref.PocketWordEvolution.{v} κ' rL rR := by
  have hGp : MeasurableSet[𝓦] {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} :=
    (measurableSet_rightLo_pos_and (mΩ := 𝓦) hRm hLm hGm hconf).1
  have hG0 : MeasurableSet[𝓦] {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} := by
    have e : {ω | ω ∈ G ∧ ¬ 0 < rightLo (R ω) (L ω) r} = G \ {ω | ω ∈ G ∧ 0 < rightLo (R ω) (L ω) r} := by
      ext ω
      simp only [mem_ofPred_eq, Set.mem_sdiff, not_and]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
    rw [e]
    exact hGm.diff hGp
  refine pocketWordEvolution_of_changeConfig' hκ' hL hLd hR hRd h𝓦 hRm hLm hGm hPG hconf hcfg hcfgI hηm
    (pocketCouplingInput_of_chartInput h𝓦 hRm hLm hGp (fun ω hω => hcfg ω hω.1 hω.2) hh hin)
    (pocketCouplingInputInf_of_chartInputInf h𝓦 hRm hLm hG0 (fun ω hω => hcfgI ω hω.1 ?_) hh hinI)
  exact le_antisymm (not_lt.1 hω.2) (hconf ω hω.1).changeCorner_props.1.1

end InfInput

end InteractingSLE.Sec7.PocketCoupling
