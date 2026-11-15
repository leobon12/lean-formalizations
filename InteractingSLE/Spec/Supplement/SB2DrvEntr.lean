/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvIter
import InteractingSLE.Spec.Supplement.SB2DrvHit
import InteractingSLE.Spec.Supplement.SB2DrvLocal
import InteractingSLE.Spec.Supplement.SB2KEntry
import InteractingSLE.Spec.Supplement.SB2KPast
import InteractingSLE.Spec.Supplement.SB2JK2
import InteractingSLE.Spec.Restart.FCThresholdDriverPremises

/-!
# SB2(1)'s entrance union: the retained lower prefix and the upper flow up to its first visit of `L`

Packet PROVE-T14-SB2DRV (round 3), clause (E1) of `SB2EntranceK2NStatement` and the locality behind (E2). Supplement
p. 632: "Its first visit [of `L`] is a stopping rule of this retained staged history. The initial erased portion
adds no set in `D_A`". Here:

* **`exists_past_realMin`**: a `pastSigma (k + 1)`-measurable version `Lp` of `L = min(A ∩ ℝ)` on the launch event
  (`exists_measurable_realMin` with the frozen-run argument `exists_measurable_eq_of_frozen`, as for the entry point);
* **`EntranceUnion`** (data) and **`exists_entranceUnion`**: `Lp` with capped versions `η_n` (cap `n`, lifetime
  `cutLife ζ n`) of the upper flow, `Restart.exists_capped_version` with Lemma 7.5 from Theorems 1.2–1.3 and the proved
  killed entrance locality `WholeField.retainedRangeEntranceStatement`;
* `EntranceUnion.set`, `EntranceUnion.marks`: the limit `A ∪ ⋃ n η_n([0, T_n])` (`T_n` the first visit of `Lp` by
  `η_n`, `hitQ`) and its marks `𝒢' = pastSigma (k + 1) ⊔ σ(killed histories of the η_n through T_n)`;
* **`EntranceUnion.isHistoryAvoidanceLocal`**, `measurableSet_disjoint`, `marks_le_aeSigma`, `marks_le`,
  `past_le_marks`: the union is a history-marked local set of the centred field for `𝒢'`, its avoidance events are
  a.s. marks, `𝒢'` is a.s. an event family of the field.

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

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **A past-measurable version of `L = min(A ∩ ℝ)`** on the launch event. -/
theorem exists_past_realMin (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    ∃ Lp : Ω → ℝ, Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] Lp ∧
      ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Lp ω = realMin (lowerPrefix κ b jumps E (k + 1) u ω) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hS := HP.staged _ hw
  have hR := HP.pieces_regular _ hw
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft HP.kappa_pos (HP.admissible t ht htJ)
  obtain ⟨M, Lm, -, hMae, hLm, -, hLmeq⟩ := exists_measurable_realMin HP.kappa_pos HP.boundary HP.field rfl hS hR
    (HP.drivers_regular _) hamb (k + 1) HP.seed_nonpos
  refine exists_measurable_eq_of_frozen (hS.2.1 (k + 1)) hLm ?_ ?_
  · filter_upwards [hMae] with ω hω hl using hLmeq ω hω hl
  · filter_upwards [ae_ae_run_eq runMeasStatement HP.boundary (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (k := k + 1) (fun j _ => hS.1 j) (fun j _ => HP.drivers_regular _ j)] with ω₀ h₀ hF
    filter_upwards [h₀] with ω hω
    have e := launchEntry_eq_of_run_eq (u := u) hω
    refine ⟨e.1.2 hF, ?_⟩
    have hp : lowerPrefix κ b jumps E (k + 1) u ω = lowerPrefix κ b jumps E (k + 1) u ω₀ := by
      simp only [lowerPrefix, prefixPhysSet, hω]
    rw [hp]

/-! ### The entrance union data -/

/-- The lifetimes of the capped versions. -/
def capLife (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0∞ := cutLife (ζ ω) (n : ℝ≥0)

/-- **SB2(1)'s entrance union data**: a past-measurable version of `L` and capped versions `η_n` (cap `n`, lifetime
`cutLife ζ n`) of the upper flow, with their standing hypotheses for the centred field `h − u₀`. -/
structure EntranceUnion (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ)
    (u : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) where
  Lp : Ω → ℝ
  ηc : ℕ → Ω → ℝ≥0 → ℂ
  Lp_meas : Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] Lp
  Lp_eq : ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → Lp ω = realMin (lowerPrefix κ b jumps E (k + 1) u ω)
  paths : IterPaths (WholeField.centredField h u₀) P ηc (capLife ζ)
  start : ∀ n ω, ηc n ω 0 = u
  frozen : ∀ (n : ℕ) ω t, (n : ℝ≥0) ≤ t → ηc n ω t = ηc n ω n
  version : ∀ᵐ ω ∂P, ∀ (n : ℕ) t, ηc n ω t = η ω (capTime (n : ℝ≥0) (ζ ω) t)

/-- **The entrance union data exist** (Lemma 7.5 from Theorems 1.2–1.3; killed entrance locality is proved). -/
theorem exists_entranceUnion (h12p : Theorem12ParamStatement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (u₀ : ℂ → ℝ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    Nonempty (EntranceUnion κ b jumps P h E k u η ζ u₀) := by
  have hL75 : Theorem15.Lemma75Statement.{u} :=
    lemma75Statement_of_lemma75DataStatement (FCPlumb.lemma75DataStatement_of_param h12p)
  obtain ⟨Lp, hLp, hLpe⟩ := exists_past_realMin HP
  have hcap := fun n : ℕ => exists_capped_version hL75 HP.kappa_pos HP.kappa_lt_four HP.boundary HP.field
    HP.flow u₀ (n : ℝ≥0)
  choose ηc hc hm h0 hfz hae hdet hdetζ using hcap
  have hζm : Measurable ζ := measurable_lifetime_of_isFlowLine HP.flow
  refine ⟨⟨Lp, ηc, hLp, hLpe, ⟨hc, hm, fun n => (measurable_cutLife (n : ℝ≥0)).comp hζm, hdet, hdetζ,
    fun n => WholeField.retainedRangeEntranceStatement κ HP.kappa_pos HP.kappa_lt_four b jumps HP.boundary u ψ P h
      HP.field η ζ HP.flow u₀ hu₀ (n : ℝ≥0) (ηc n) (hc n) (hm n) (hae n), fun n ω hω => ?_⟩, h0, hfz,
    ae_all_iff.2 hae⟩⟩
  rw [h0 n ω] at hω
  have him : (0 : ℝ) < ((u : ℝ) : ℂ).im := hω
  simp at him

namespace EntranceUnion

variable {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)

/-- The visited real point, as a complex number. -/
def point (ω : Ω) : ℂ := (D.Lp ω : ℂ)

/-- **The entrance union** `A ∪ ⋃ n η_n([0, T_n])`. -/
def set : Ω → Set ℂ :=
  limSet (WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc D.point hitQ

/-- **The entrance σ-algebra** `𝒢' = pastSigma (k + 1) ⊔ σ(killed histories of the η_n through T_n)`. -/
@[instance_reducible]
def marks : MeasurableSpace Ω :=
  limMarks (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)) D.ηc (capLife ζ) D.point hitQ

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem point_meas : Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] D.point :=
  Complex.measurable_ofReal.comp D.Lp_meas

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
theorem past_le_marks : pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤ D.marks :=
  le_limMarks

theorem marks_le (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) : D.marks ≤ mΩ := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  exact limMarks_le ((HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)).2.1 (k + 1))
    D.paths D.point_meas measurable_hitQ

/-- The retained past is a.s. an event family of the centred field. -/
theorem past_le_aeSigma (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (u₀ : ℂ → ℝ) :
    pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ≤
      aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  obtain ⟨f, hf, hp⟩ := WalkLaw.pastDetRegStatement_of_thm12_thm13 h12p h13 κ HP.kappa_pos HP.kappa_lt_four b jumps
    HP.boundary P h HP.field _ _ (HP.staged _ hw) (HP.pieces_regular _ hw) (k + 1)
  exact WalkLaw.pastSigma_le_aeSigma_centred hf hp u₀

/-- **The entrance σ-algebra is a.s. an event family of the centred field.** -/
theorem marks_le_aeSigma (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) :
    D.marks ≤ aeSigma (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P :=
  limMarks_le_aeSigma (past_le_aeSigma h12p h13 HP u₀) D.paths D.point_meas measurable_hitQ

/-- The retained lower prefix in the form of the union step's hypothesis. -/
theorem walk_complSigma (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens)
    (hUH : (U : Set ℂ) ⊆ H) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens (WholeField.centredField h u₀)
      (fun ω => G (WholeField.centredField h u₀ ω)) P)
    (F : Set Ω) (hF : MeasurableSet[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] F) :
    MeasurableSet[WalkLaw.complSigma P G (WholeField.centredField h u₀)]
      ({ω | Disjoint (WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) U} ∩ F) := by
  obtain ⟨hev, -, hloc⟩ := walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)
  have hdet := past_le_aeSigma h12p h13 HP u₀
  refine complSigma_of_isHistoryAvoidanceLocal (WholeField.measurable_centredField HP.field.1 u₀) hloc
    (fun U' hU' => ?_) hdet U G hUH hG hd F hF
  obtain ⟨E', hE', hEE'⟩ := hev U' hU'
  obtain ⟨K, hK, hE'K⟩ := hdet E' hE'
  exact ⟨K, hK, hEE'.trans hE'K⟩

/-- **The entrance union is a history-marked local set** of the centred field for the entrance σ-algebra. -/
theorem isHistoryAvoidanceLocal (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    WholeField.IsHistoryAvoidanceLocal D.marks D.set (WholeField.centredField h u₀) P :=
  isHistoryAvoidanceLocal_limSet (WholeField.measurable_centredField HP.field.1 u₀)
    (walk_complSigma h12p h13 HP hu₀) D.paths D.point_meas measurable_hitQ isParamGalmarino_hitQ

/-- **The entrance union's avoidance events are a.s. events of the entrance σ-algebra.** -/
theorem measurableSet_disjoint (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {U : TopologicalSpace.Opens ℂ} (hUH : (U : Set ℂ) ⊆ H) :
    MeasurableSet[aeSigma D.marks P] {ω | Disjoint (D.set ω) U} :=
  measurableSet_disjoint_limSet D.paths.cont D.paths.start hUH
    ((walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)).1 U hUH)

end EntranceUnion

end InteractingSLE.Theorem14.SB.Lv
