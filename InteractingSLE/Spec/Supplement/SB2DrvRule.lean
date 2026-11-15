/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1StopLine
import InteractingSLE.Spec.Supplement.WalkUnionLaw

/-!
# A marked local set with one more flow path stopped at a parameterized Galmarino rule

Packet PROVE-T14-SB2DRV (round 3). SB2(1)'s entrance σ-algebra `𝒢' = pastSigma ⊔ σ(killed record at T_L)` and the
physical K2 lines from `T_L` (supplement p. 631, "At every rational ordinary time of the other history, its marked union
with `A` has the Gaussian local-set kernel") need the union of the retained lower prefix `A` (a marked local set for the
retained past `𝒢`) with the remaining flow path `η` stopped at a time `τ = S(Y, η)` which reads the retained past
through a `𝒢`-measurable parameter `Y` (the visited real point `L`, a later physical time) and the path in Galmarino
form. This file proves the union step in the "almost surely an event of the complementary projection" form, which
iterates:

* `IsParamGalmarino S`: for each parameter, `S y` reads the path coordinates only up to its own value;
  `IsParamGalmarino.le_iff_stop`, `IsParamGalmarino.eq_stop`: the rule is recovered from any longer stopped history;
* `rangeUpTo γ τ`: the `ℍ`-part of `γ([0, τ])`; `disjoint_rangeUpTo_iff`;
* **`mem_complSigma_union_rule`**: if the marked avoidance events of `A` (marks `𝒢`) are almost surely events of the
  complementary projection, so are those of `A ∪ η([0, τ])` for the marks `𝒢 ⊔ σ(killed history of η through τ)`,
  for every capped flow path `η` that is history-sensitively local at first entrance times with its killing record
  (`Restart.IsEntranceKilledHistoryLocal`);
* `isHistoryAvoidanceLocal_union_rule`: the history-marked avoidance criterion of the union;
* `measurableSet_disjoint_union_rule`, `union_rule_marks_le_aeSigma`: the union's avoidance events are marks, and the
  new marks are almost surely events of the field.

Everything is generic in the marked local set; no Theorem 1.2–1.3 input is used here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.SB.Lv

open LocalSets Sec6 Restart

/-! ### Parameterized Galmarino rules -/

section Rule

variable {𝒴 : Type*}

/-- **A parameterized Galmarino rule**: for every parameter `y`, the stopping time `S y c` reads the path coordinates
`c` only up to its own value. -/
def IsParamGalmarino (S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞) : Prop :=
  ∀ y c c', (∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ S y c) → c q = c' q) → S y c' = S y c

variable {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- Below a longer recording time the rule is read off the stopped coordinates. -/
theorem IsParamGalmarino.eq_stop (hS : IsParamGalmarino S) {y : 𝒴} {c : ℚ≥0 → ℂ} {T : ℝ≥0∞}
    (hle : S y c ≤ T) : S y (stopCoord c T) = S y c :=
  hS y c (stopCoord c T) fun _ hq => (stopCoord_of_le (hq.trans hle)).symm

/-- The stopped coordinates decide whether the rule has occurred by the recording time. -/
theorem IsParamGalmarino.le_iff_stop (hS : IsParamGalmarino S) (y : 𝒴) (c : ℚ≥0 → ℂ) (T : ℝ≥0∞) :
    S y c ≤ T ↔ S y (stopCoord c T) ≤ T := by
  constructor
  · intro hle
    rw [hS.eq_stop hle]
    exact hle
  · intro hle
    have e : S y c = S y (stopCoord c T) :=
      hS y (stopCoord c T) c fun _ hq => stopCoord_of_le (hq.trans hle)
    rw [e]
    exact hle

end Rule

/-! ### Ranges up to a time -/

/-- The `ℍ`-part of `γ([0, τ])`. -/
def rangeUpTo (γ : ℝ≥0 → ℂ) (τ : ℝ≥0∞) : Set ℂ := γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ} ∩ H

theorem disjoint_rangeUpTo_iff {γ : ℝ≥0 → ℂ} {τ : ℝ≥0∞} {U : Set ℂ} (hUH : U ⊆ H) :
    Disjoint (rangeUpTo γ τ) U ↔ ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ → γ t ∉ U := by
  constructor
  · intro hd t ht htU
    exact Set.disjoint_left.1 hd ⟨⟨t, ht, rfl⟩, hUH htU⟩ htU
  · intro hall
    rw [Set.disjoint_left]
    rintro z ⟨⟨t, ht, rfl⟩, -⟩ hz
    exact hall t ht hz

/-- For a continuous path started outside the open `U`, avoiding `U` up to `τ` is read off the history through
`τ`: no rational time strictly before `τ` lies in `U`. -/
theorem disjoint_rangeUpTo_iff_hist {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {U : Set ℂ} (hU : IsOpen U)
    (hUH : U ⊆ H) (h0 : γ 0 ∉ U) (τ : ℝ≥0∞) :
    Disjoint (rangeUpTo γ τ) U ↔
      ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) < τ) → stopCoord (pathCoord γ) τ q ∉ U := by
  rw [disjoint_rangeUpTo_iff hUH, disjoint_range_iff_le_firstEntrance hU hγ h0, firstEntrance, le_iInf₂_iff]
  constructor
  · intro hall q hq hqU
    rw [stopCoord_of_le hq.le] at hqU
    exact absurd (hall q hqU) (not_le.2 hq)
  · intro hall q hqU
    by_contra hlt
    rw [not_le] at hlt
    exact hall q hlt (by rw [stopCoord_of_le hlt.le]; exact hqU)

/-- The histories through their own time whose coordinates avoid `U` strictly before it. -/
def avoidHist (U : Set ℂ) : Set KHist :=
  {k | ∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) < k.1.1) → k.1.2 q ∉ U}

theorem measurableSet_avoidHist {U : Set ℂ} (hU : MeasurableSet U) : MeasurableSet (avoidHist U) := by
  have e : avoidHist U = ⋂ q : ℚ≥0,
      ({k : KHist | k.1.1 ≤ (((q : ℝ≥0) : ℝ≥0∞))} ∪ {k : KHist | k.1.2 q ∉ U}) := by
    ext k
    simp only [avoidHist, mem_ofPred_eq, mem_iInter, mem_union, ← not_lt]
    exact forall_congr' fun q => imp_iff_not_or
  rw [e]
  refine MeasurableSet.iInter fun q => MeasurableSet.union ?_ ?_
  · exact measurableSet_le (measurable_fst.comp measurable_fst) measurable_const
  · exact ((measurable_pi_apply q).comp (measurable_snd.comp measurable_fst) :
      Measurable fun k : KHist => k.1.2 q) hU.compl

/-! ### The union step -/

section Union

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ}
  {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {𝒴 : Type*} [MeasurableSpace 𝒴] {Y : Ω → 𝒴}
  {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- The killed history of the path `η` through the rule `S(Y, η)`. -/
def ruleHist (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (Y : Ω → 𝒴) (S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞) (ω : Ω) : KHist :=
  khistOf (pathCoord (η ω)) (ζ ω) (S (Y ω) (pathCoord (η ω)))

/-- The marks of the union: the marks of `A` and the killed history of the path through the rule. -/
@[instance_reducible]
def ruleMarks (𝒢 : MeasurableSpace Ω) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (Y : Ω → 𝒴)
    (S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞) : MeasurableSpace Ω :=
  𝒢 ⊔ MeasurableSpace.comap (ruleHist η ζ Y S) inferInstance

/-- **The union step.** If the marked avoidance events of `A` (marks `𝒢`) are almost surely events of the
complementary projection, so are those of `A ∪ η([0, τ])`, `τ = S(Y, η)`, for the marks `𝒢 ⊔ σ(killed history of η
through τ)`: on the avoidance event of the path, `τ` and the killed history through `τ` are read off the killed
history through the first entrance time `T^U` and the `𝒢`-measurable parameter `Y` (Galmarino), and the former is
almost surely an event family of the complementary projection (`Restart.measurable_entranceKHist`). -/
theorem mem_complSigma_union_rule (hhm : Measurable h)
    (hA : ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ F : Set Ω, MeasurableSet[𝒢] F →
        MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (A ω) U} ∩ F))
    (hc : ∀ ω, Continuous (η ω)) (hηm : ∀ t, Measurable fun ω => η ω t) (hζm : Measurable ζ)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η ω t) =ᵐ[P] fun ω => f (h ω))
    (hdetζ : ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ =ᵐ[P] fun ω => f (h ω))
    (hloc : IsEntranceKilledHistoryLocal η ζ h P) (h0 : ∀ ω, η ω 0 ∉ H)
    (hY : Measurable[𝒢] Y) (hSm : Measurable (Function.uncurry S)) (hSg : IsParamGalmarino S)
    (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (hUH : (U : Set ℂ) ⊆ H)
    (hG : Measurable G) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (F : Set Ω) (hF : MeasurableSet[ruleMarks 𝒢 η ζ Y S] F) :
    MeasurableSet[WalkLaw.complSigma P G h]
      ({ω | Disjoint (A ω ∪ rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U} ∩ F) := by
  set EA : Set Ω := {ω | Disjoint (A ω) U} with hEA
  have hEA𝒦 : MeasurableSet[WalkLaw.complSigma P G h] EA := by
    have h1 := hA U G hUH hG hd univ (@MeasurableSet.univ _ 𝒢)
    rwa [inter_univ] at h1
  set X : Ω → KHist := fun ω => khistOf (pathCoord (η ω)) (ζ ω) (firstEntrance U (pathCoord (η ω))) with hXdef
  have h0U : ∀ ω, η ω 0 ∉ (U : Set ℂ) := fun ω hω => h0 ω (hUH hω)
  have hX : Measurable[WalkLaw.complSigma P G h] X :=
    measurable_entranceKHist hhm hc hηm hζm hdet hdetζ hloc U G hUH hG hd h0U
  -- the trace σ-algebra of `EA` contains the marks of `A` and the entrance history
  have hGTr : 𝒢 ⊔ MeasurableSpace.comap X inferInstance ≤
      WalkLaw.traceSigma (WalkLaw.complSigma P G h) EA hEA𝒦 := by
    refine sup_le (fun F₁ hF₁ => hA U G hUH hG hd F₁ hF₁) ?_
    rintro _ ⟨B, hB, rfl⟩
    exact hEA𝒦.inter (hX hB)
  have hYX : Measurable[𝒢 ⊔ MeasurableSpace.comap X inferInstance] fun ω => (Y ω, X ω) :=
    Measurable.prodMk (hY.mono le_sup_left le_rfl) ((comap_measurable X).mono le_sup_right le_rfl)
  -- the reading of the rule off the entrance history
  set Ψ : Set (𝒴 × KHist) := {p | S p.1 p.2.1.2 ≤ p.2.1.1} with hΨ
  have hSm' : Measurable fun p : 𝒴 × KHist => S p.1 p.2.1.2 :=
    hSm.comp (measurable_fst.prodMk (measurable_snd.comp (measurable_fst.comp measurable_snd)))
  have hΨm : MeasurableSet Ψ := measurableSet_le hSm' (measurable_fst.comp (measurable_fst.comp measurable_snd))
  set Φ : 𝒴 × KHist → KHist := fun p => khistRestrict p.2 (S p.1 p.2.1.2) with hΦ
  have hΦm : Measurable Φ := measurable_khistRestrict.comp (measurable_snd.prodMk hSm')
  have hpt : ∀ ω, (Disjoint (rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U ↔ (Y ω, X ω) ∈ Ψ) ∧
      ((Y ω, X ω) ∈ Ψ → Φ (Y ω, X ω) = ruleHist η ζ Y S ω) := by
    intro ω
    have hav : Disjoint (rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U ↔
        S (Y ω) (pathCoord (η ω)) ≤ firstEntrance U (pathCoord (η ω)) := by
      rw [disjoint_rangeUpTo_iff hUH]
      exact disjoint_range_iff_le_firstEntrance U.isOpen (hc ω) (h0U ω) _
    have hiff := hSg.le_iff_stop (Y ω) (pathCoord (η ω)) (firstEntrance U (pathCoord (η ω)))
    refine ⟨hav.trans hiff, fun hω => ?_⟩
    have hle : S (Y ω) (pathCoord (η ω)) ≤ firstEntrance U (pathCoord (η ω)) := hiff.2 hω
    show khistRestrict (X ω) (S (Y ω) (stopCoord (pathCoord (η ω)) (firstEntrance U (pathCoord (η ω))))) = _
    rw [hSg.eq_stop hle]
    exact khistRestrict_khistOf hle
  -- the avoidance event of the union
  have hEu : {ω | Disjoint (A ω ∪ rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U} =
      EA ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ := by
    ext ω
    simp only [mem_ofPred_eq, disjoint_union_left, hEA, mem_inter_iff, mem_preimage, (hpt ω).1]
  have hm : ∀ F₁ : Set (𝒴 × KHist), MeasurableSet F₁ → ∀ F₂, MeasurableSet[𝒢] F₂ →
      MeasurableSet[WalkLaw.complSigma P G h] (EA ∩ (F₂ ∩ (fun ω => (Y ω, X ω)) ⁻¹' F₁)) :=
    fun F₁ hF₁ F₂ hF₂ =>
      hGTr _ ((le_sup_left (b := MeasurableSpace.comap X inferInstance) _ hF₂).inter (hYX hF₁))
  have hEu𝒦 : MeasurableSet[WalkLaw.complSigma P G h] (EA ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ) := by
    have h1 := hm Ψ hΨm univ (@MeasurableSet.univ _ 𝒢)
    rwa [univ_inter] at h1
  have hle : ruleMarks 𝒢 η ζ Y S ≤
      WalkLaw.traceSigma (WalkLaw.complSigma P G h) (EA ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ) hEu𝒦 := by
    refine sup_le (fun F₂ hF₂ => ?_) ?_
    · change MeasurableSet[WalkLaw.complSigma P G h] ((EA ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ) ∩ F₂)
      have e : (EA ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ) ∩ F₂ = EA ∩ (F₂ ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ) := by
        ext ω; simp only [mem_inter_iff]; tauto
      rw [e]
      exact hm Ψ hΨm F₂ hF₂
    · rintro _ ⟨B, hB, rfl⟩
      change MeasurableSet[WalkLaw.complSigma P G h]
        ((EA ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ) ∩ ruleHist η ζ Y S ⁻¹' B)
      have e : (EA ∩ (fun ω => (Y ω, X ω)) ⁻¹' Ψ) ∩ ruleHist η ζ Y S ⁻¹' B =
          EA ∩ (univ ∩ (fun ω => (Y ω, X ω)) ⁻¹' (Ψ ∩ Φ ⁻¹' B)) := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, h2, by rw [(hpt ω).2 h2]; exact h3⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2⟩, by rw [← (hpt ω).2 h2]; exact h3⟩
      rw [e]
      exact hm _ (hΨm.inter (hΦm hB)) univ (@MeasurableSet.univ _ 𝒢)
  rw [hEu]
  exact hle F hF

/-- **The union is a history-marked local set** for the joined marks (the history-marked avoidance criterion). -/
theorem isHistoryAvoidanceLocal_union_rule (hhm : Measurable h)
    (hA : ∀ (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P →
      ∀ F : Set Ω, MeasurableSet[𝒢] F →
        MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (A ω) U} ∩ F))
    (hc : ∀ ω, Continuous (η ω)) (hηm : ∀ t, Measurable fun ω => η ω t) (hζm : Measurable ζ)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η ω t) =ᵐ[P] fun ω => f (h ω))
    (hdetζ : ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ =ᵐ[P] fun ω => f (h ω))
    (hloc : IsEntranceKilledHistoryLocal η ζ h P) (h0 : ∀ ω, η ω 0 ∉ H)
    (hY : Measurable[𝒢] Y) (hSm : Measurable (Function.uncurry S)) (hSg : IsParamGalmarino S) :
    WholeField.IsHistoryAvoidanceLocal (ruleMarks 𝒢 η ζ Y S)
      (fun ω => A ω ∪ rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) h P :=
  WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF =>
    mem_complSigma_union_rule hhm hA hc hηm hζm hdet hdetζ hloc h0 hY hSm hSg U G hUH hG hd F hF

omit mΩ [MeasurableSpace 𝒴] in
/-- The killed history through the rule decides whether the path has avoided `U` by then. -/
theorem ruleHist_preimage_avoidHist (hc : ∀ ω, Continuous (η ω)) (h0 : ∀ ω, η ω 0 ∉ H) {U : Set ℂ}
    (hU : IsOpen U) (hUH : U ⊆ H) :
    {ω | Disjoint (rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U} = ruleHist η ζ Y S ⁻¹' avoidHist U := by
  ext ω
  rw [mem_ofPred_eq, disjoint_rangeUpTo_iff_hist (hc ω) hU hUH (fun h' => h0 ω (hUH h'))]
  rfl

omit [IsProbabilityMeasure P] [MeasurableSpace 𝒴] in
/-- **The union's avoidance events are (almost surely) marks** of the joined marks. -/
theorem measurableSet_disjoint_union_rule (hc : ∀ ω, Continuous (η ω)) (h0 : ∀ ω, η ω 0 ∉ H)
    {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) (hev : MeasurableSet[aeSigma 𝒢 P] {ω | Disjoint (A ω) U}) :
    MeasurableSet[aeSigma (ruleMarks 𝒢 η ζ Y S) P]
      {ω | Disjoint (A ω ∪ rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U} := by
  have e : {ω | Disjoint (A ω ∪ rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U} =
      {ω | Disjoint (A ω) U} ∩ {ω | Disjoint (rangeUpTo (η ω) (S (Y ω) (pathCoord (η ω)))) U} := by
    ext ω
    simp only [mem_ofPred_eq, disjoint_union_left, mem_inter_iff]
  rw [e, ruleHist_preimage_avoidHist hc h0 U.isOpen hUH]
  refine MeasurableSet.inter (WalkLaw.aeSigma_mono le_sup_left _ hev) ?_
  exact le_aeSigma _ P _ (le_sup_right (a := 𝒢) _
    ⟨avoidHist (U : Set ℂ), measurableSet_avoidHist U.isOpen.measurableSet, rfl⟩)

omit [IsProbabilityMeasure P] in
/-- **The joined marks are almost surely events of the field**, once the marks of `A` are and the path, its lifetime
and the parameter are field-determined. -/
theorem ruleMarks_le_aeSigma (h𝒢 : 𝒢 ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η ω t) =ᵐ[P] fun ω => f (h ω))
    (hdetζ : ∃ f : DistOn upperHalfPlaneOpens → ℝ≥0∞, Measurable f ∧ ζ =ᵐ[P] fun ω => f (h ω))
    (hY : Measurable[𝒢] Y) (hSm : Measurable (Function.uncurry S)) :
    ruleMarks 𝒢 η ζ Y S ≤ aeSigma (MeasurableSpace.comap h inferInstance) P := by
  have hae : ∀ {β : Type} [MeasurableSpace β] {Z : Ω → β} {f : DistOn upperHalfPlaneOpens → β},
      Measurable f → Z =ᵐ[P] (fun ω => f (h ω)) →
        Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] Z := by
    intro β _ Z f hf hZ B hB
    refine ⟨h ⁻¹' (f ⁻¹' B), ⟨f ⁻¹' B, hf hB, rfl⟩, ?_⟩
    filter_upwards [hZ] with ω hω
    simp only [mem_preimage, hω]
  have hcm : Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] fun ω => pathCoord (η ω) := by
    refine @Measurable.of_eval Ω ℚ≥0 (fun _ => ℂ) (aeSigma (MeasurableSpace.comap h inferInstance) P)
      (fun _ => inferInstance) _ fun q => ?_
    obtain ⟨f, hf, hfe⟩ := hdet q
    exact hae hf hfe
  obtain ⟨fζ, hfζ, hfζe⟩ := hdetζ
  have hζ' := hae hfζ hfζe
  have hY' : Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] Y := hY.mono h𝒢 le_rfl
  have hk : Measurable fun p : 𝒴 × (ℚ≥0 → ℂ) × ℝ≥0∞ => khistOf p.2.1 p.2.2 (S p.1 p.2.1) := by
    have hτ : Measurable fun p : 𝒴 × (ℚ≥0 → ℂ) × ℝ≥0∞ => S p.1 p.2.1 :=
      hSm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    exact (measurable_histOf.comp (hτ.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_lifeRec.comp ((measurable_snd.comp measurable_snd).prodMk hτ))
  have hR : Measurable[aeSigma (MeasurableSpace.comap h inferInstance) P] (ruleHist η ζ Y S) :=
    hk.comp (hY'.prodMk (hcm.prodMk hζ'))
  exact sup_le h𝒢 hR.comap_le

/-- **Bridge from the history-marked criterion**: the "almost surely an event of the complementary projection" form
of a marked local set whose avoidance events and marks are almost surely events of the field. -/
theorem complSigma_of_isHistoryAvoidanceLocal (hhm : Measurable h)
    (hloc : WholeField.IsHistoryAvoidanceLocal 𝒢 A h P)
    (hev : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] {ω | Disjoint (A ω) U})
    (h𝒢 : 𝒢 ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (U : Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (hUH : (U : Set ℂ) ⊆ H)
    (hG : Measurable G) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (F : Set Ω) (hF : MeasurableSet[𝒢] F) :
    MeasurableSet[WalkLaw.complSigma P G h] ({ω | Disjoint (A ω) U} ∩ F) :=
  WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hUH hG hd hF ((hev U hUH).inter (h𝒢 F hF))

end Union

end InteractingSLE.Theorem14.SB.Lv
