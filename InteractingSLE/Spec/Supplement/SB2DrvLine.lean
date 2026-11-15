/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEntrEv

/-!
# SB2(1)'s union locality at the physical times `T_L + s`

Packet PROVE-T14-SB2DRV (round 3), the locality input of K2's physical lines from `T_L` (supplement p. 631, "At every
rational ordinary time of the other history, its marked union with `A` has the Gaussian local-set kernel"):

* `hitQAdd s`: the rule `T_L + s` (first visit of the parameter point, plus `s`); `isParamGalmarino_hitQAdd`,
  `measurable_hitQAdd`;
* **`ruleMarks_mono_rule`**, `iterMarks_mono_rule`, **`limMarks_mono_rule`** (generic): marks of a smaller Galmarino
  rule are contained in those of a larger one;
* for an entrance construction `D`: `D.lineSet s = A ∪ ⋃ₙ η_n([0, T_n + s])`, `D.lineMarks s`, with
  **`D.isHistoryAvoidanceLocal_line`** (a history-marked local set of the centred field for `D.lineMarks s`),
  `D.measurableSet_disjoint_line`, `D.lineMarks_le_aeSigma`, `D.lineMarks_le`, and the nesting
  **`D.marks_le_lineMarks`**, **`D.lineMarks_mono`** (an increasing family of σ-algebras from `𝒢' = D.marks`).

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart

/-! ### The rule `T + s` -/

/-- The first hit of `y`, plus `s`. -/
def hitQAdd (s : ℝ≥0∞) (y : ℂ) (c : ℚ≥0 → ℂ) : ℝ≥0∞ := hitQ y c + s

theorem isParamGalmarino_hitQAdd (s : ℝ≥0∞) : IsParamGalmarino (hitQAdd s) := by
  intro y c c' hag
  have h1 : hitQ y c' = hitQ y c :=
    isParamGalmarino_hitQ y c c' fun q hq => hag q (hq.trans le_self_add)
  simp only [hitQAdd, h1]

theorem measurable_hitQAdd (s : ℝ≥0∞) : Measurable (Function.uncurry (hitQAdd s)) :=
  measurable_hitQ.add_const s

theorem hitQAdd_zero : hitQAdd 0 = hitQ := by
  funext y c
  simp [hitQAdd]

/-! ### Monotonicity of the marks in the rule -/

section Mono

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {𝒴 : Type*} [MeasurableSpace 𝒴]
  {Y : Ω → 𝒴} {S S' : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞}

omit mΩ in
/-- **The killed history through a smaller Galmarino rule is read off that through a larger one.** -/
theorem ruleMarks_mono_rule {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hY : Measurable[𝒢] Y)
    (hSm : Measurable (Function.uncurry S)) (hSg : IsParamGalmarino S) (hle : ∀ y c, S y c ≤ S' y c) :
    ruleMarks 𝒢 η ζ Y S ≤ ruleMarks 𝒢 η ζ Y S' := by
  refine sup_le le_sup_left ?_
  set Φ : 𝒴 × KHist → KHist := fun p => khistRestrict p.2 (S p.1 p.2.1.2) with hΦ
  have hΦm : Measurable Φ := measurable_khistRestrict.comp (measurable_snd.prodMk
    (hSm.comp (measurable_fst.prodMk (measurable_snd.comp (measurable_fst.comp measurable_snd)))))
  have heq : ruleHist η ζ Y S = Φ ∘ fun ω => (Y ω, ruleHist η ζ Y S' ω) := by
    funext ω
    have h1 := hle (Y ω) (pathCoord (η ω))
    show _ = khistRestrict (khistOf _ _ _) (S (Y ω) (stopCoord (pathCoord (η ω)) (S' (Y ω) (pathCoord (η ω)))))
    rw [hSg.eq_stop h1, khistRestrict_khistOf h1]
    rfl
  have hpair : Measurable[ruleMarks 𝒢 η ζ Y S'] fun ω => (Y ω, ruleHist η ζ Y S' ω) :=
    Measurable.prodMk (hY.mono le_sup_left le_rfl) ((comap_measurable _).mono le_sup_right le_rfl)
  rw [heq, ← MeasurableSpace.comap_comp]
  exact (MeasurableSpace.comap_mono hΦm.comap_le).trans hpair.comap_le

omit mΩ in
theorem iterMarks_mono_rule {η : ℕ → Ω → ℝ≥0 → ℂ} {ζ : ℕ → Ω → ℝ≥0∞} (hY : Measurable[𝒢] Y)
    (hSm : Measurable (Function.uncurry S)) (hSg : IsParamGalmarino S) (hle : ∀ y c, S y c ≤ S' y c) (n : ℕ) :
    iterMarks 𝒢 η ζ Y S n ≤ iterMarks 𝒢 η ζ Y S' n := by
  induction n with
  | zero => exact ruleMarks_mono_rule hY hSm hSg hle
  | succ n ih =>
    refine (sup_le_sup_right ih _).trans ?_
    exact ruleMarks_mono_rule ((hY.mono (le_iterMarks n) le_rfl)) hSm hSg hle

omit mΩ in
theorem limMarks_mono_rule {η : ℕ → Ω → ℝ≥0 → ℂ} {ζ : ℕ → Ω → ℝ≥0∞} (hY : Measurable[𝒢] Y)
    (hSm : Measurable (Function.uncurry S)) (hSg : IsParamGalmarino S) (hle : ∀ y c, S y c ≤ S' y c) :
    limMarks 𝒢 η ζ Y S ≤ limMarks 𝒢 η ζ Y S' :=
  iSup_mono fun n => iterMarks_mono_rule hY hSm hSg hle n

end Mono

/-! ### SB2(1): the lines from `T_L` -/

namespace EntranceUnion

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

/-- The union at the physical time `T_L + s`. -/
def lineSet (s : ℝ≥0∞) : Ω → Set ℂ :=
  limSet (WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc D.point (hitQAdd s)

/-- Its marks: the retained past and the killed histories of the capped upper flows through `T_n + s`. -/
@[instance_reducible]
def lineMarks (s : ℝ≥0∞) : MeasurableSpace Ω :=
  limMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point (hitQAdd s)

/-- **The union at `T_L + s` is a history-marked local set** of the centred field for its marks. -/
theorem isHistoryAvoidanceLocal_line (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (s : ℝ≥0∞) :
    WholeField.IsHistoryAvoidanceLocal (D.lineMarks s) (D.lineSet s) (WholeField.centredField h u₀) P :=
  isHistoryAvoidanceLocal_limSet (WholeField.measurable_centredField HP.field.1 u₀)
    (walk_complSigma h12p h13 HP hu₀) D.paths D.point_meas (measurable_hitQAdd s) (isParamGalmarino_hitQAdd s)

theorem measurableSet_disjoint_line (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (s : ℝ≥0∞)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[aeSigma (D.lineMarks s) P] {ω | Disjoint (D.lineSet s ω) U} :=
  measurableSet_disjoint_limSet D.paths.cont D.paths.start hUH
    ((walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)).1 U hUH)

theorem lineMarks_le_aeSigma (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (s : ℝ≥0∞) :
    D.lineMarks s ≤ aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P :=
  limMarks_le_aeSigma (past_le_aeSigma h12p h13 HP u₀) D.paths D.point_meas (measurable_hitQAdd s)

theorem lineMarks_le (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (s : ℝ≥0∞) : D.lineMarks s ≤ mΩ := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  exact limMarks_le ((HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)).2.1 (k + 1))
    D.paths D.point_meas (measurable_hitQAdd s)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The lines are nested**: the marks grow with `s`. -/
theorem lineMarks_mono {s s' : ℝ≥0∞} (hss' : s ≤ s') : D.lineMarks s ≤ D.lineMarks s' :=
  limMarks_mono_rule D.point_meas (measurable_hitQAdd s) (isParamGalmarino_hitQAdd s)
    fun y c => show hitQ y c + s ≤ hitQ y c + s' from add_le_add le_rfl hss'

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The entrance σ-algebra is the line at `s = 0` and lies below every line.** -/
theorem marks_le_lineMarks (s : ℝ≥0∞) : D.marks ≤ D.lineMarks s := by
  have e : D.marks = D.lineMarks 0 := by
    simp only [marks, lineMarks, hitQAdd_zero]
  rw [e]
  exact D.lineMarks_mono zero_le

end EntranceUnion

end InteractingSLE.Theorem14.SB.Lv
