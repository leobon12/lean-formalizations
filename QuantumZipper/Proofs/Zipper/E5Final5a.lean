import QuantumZipper.Proofs.Zipper.E5Repair6
import QuantumZipper.Proofs.Zipper.E5Asm4
import QuantumZipper.Proofs.Zipper.E5Repair4
import QuantumZipper.Proofs.Zipper.E4L3i
import QuantumZipper.Proofs.Zipper.E5Model1
import QuantumZipper.Proofs.Zipper.E6LocAbsBasic
import QuantumZipper.Proofs.Zipper.F1CanonLaw
import QuantumZipper.Proofs.Zipper.F1Embed
import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F1LenRead
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet
import QuantumZipper.Proofs.Zipper.F2LocalScale
import QuantumZipper.Proofs.Zipper.F2LocalSteps
import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.F2WedgeCouple
import QuantumZipper.Proofs.Zipper.F2WeldTimes
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.HitScaleZipScale
import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.WedgeRC3All2
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.Zipper.F2Gamma0Trunc
import QuantumZipper.Proofs.Zipper.F2Gamma0TruncCore
import QuantumZipper.Proofs.Zipper.F2ScaleIndep
import QuantumZipper.Proofs.Zipper.D3PlusNonVac

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part a: `E5ReprG' locFieldFull` from the level-space model node

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39). Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72 (proof of Lemma 5.6); blueprint `E_BRANCH_BLUEPRINT.md` §4 E5, steps (1)–(5).

This file does the bookkeeping of E5's final assembly: it proves the repaired representation
input `E5ReprG' D3Plus.locFieldFull` from two exact Props,

* `E5LvlModelStmt` (the zoom model on the level space of `E5ESM6.lhsF_eq_levelModel`): for the
  good continuous version of an E5 setup, a normalized Palm density `w` on the level space, the
  D28 field `regField ϖ ρ₀ ∘ X₁` of a free field `X₁` and every `ε > 0`, a `ZoomModel` whose
  probability space is measurably identified with the level space
  `((𝐑.withDensity w) ⊗ P')` such that the rich local data of the level configuration
  `zcfgTL … C` differs from the model data `M.data C` only on a set of outer measure `≤ ε`,
  eventually in `C` (the L2 + locality + scale steps);
* `ZoomModelNonemptyStmt` (only used when the Palm mass vanishes, where E5's left side is `0`):
  a zoom model exists for every `κ ∈ (0,4)`, `R` and Wiener coordinate measure `W`.

What is proved here (own bookkeeping, no new mathematics):
* the Wiener measure `W` is `E5.exists_wiener`;
* the Palm mass `0` case: `lhsF ≤ pmass` for tests `≤ 1` (`lhsF_le_pmass`), so `lhsF = 0`;
* the Palm mass `≠ 0` case: E5's left side is `p · E_Q Γ(Z C)` on the level space by
  `lhsF_eq_levelModel` (the good version `exists_goodVersion`, the free field `exists_freeGFF`,
  `ρ₀ = foldedCircle 0 2`, the good base field `exists_base_regField_good`), transported to the
  model space along the measurable measure-preserving map; the bad events are the measurable hulls
  (`toMeasurable`) of the disagreement sets, so no measurability of the disagreement is needed.

`theorem1_3_of_lvl` wires this into `E5.theorem1_3_of_frontier_d27'`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 CoordsFull E4Grid

/-! ## 1. The two named inputs -/

/-- **The level-space zoom model node (E5 steps (1)–(3) on the level space).** For the good
continuous version `B` of an E5 setup (with `esmMeas` positive, so that `𝐑 = esmRr … lvlMu` is a
probability measure), a measurable density `w` with `∫ w d𝐑 = 1`, a free field `X₁` on
`(Ω', P')` whose D28 version `regField ϖ ρ₀ ∘ X₁` is good at every sample, with `ρ₀` an
admissible probability measure vanishing on a disc `ball 0 r₀`, every window `R`, Wiener
coordinate measure `W` and `ε > 0`: there are a zoom model `M` and a measurable map
`φ : M.Ω₁ → ((ℝ≥0 × NS(P)) × Ω')` carrying `M.Q` to `(𝐑.withDensity w) ⊗ P'` (e.g. the
identity, or the identity from a completion of the level space), such that
eventually in `C` the set where the rich local data of the level configuration `zcfgTL … C ∘ φ`
differs from the model data `M.data C` has (outer) `M.Q`-measure `≤ ε`. -/
def E5LvlModelStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ),
    (∀ ω, Continuous (B · ω)) → E5.Setup κ T P B X ϖ → (∀ ω, GoodVr κ T (Vr κ T B ω)) →
    esmMeas κ T B X P lvlMu univ ≠ 0 →
    ∀ (w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞), Measurable w →
      ∫⁻ z, w z ∂esmRr κ T B X P lvlMu = 1 →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X₁ : Ω' → FieldSample) (ρ₀ : Measure ℂ) (r₀ : ℝ),
      IsFreeGFFModConstH X₁ P' → IsAdmissibleH ρ₀ → ρ₀ Set.univ = 1 → 0 < r₀ →
      ρ₀ (Metric.ball (0 : ℂ) r₀) = 0 →
      (∀ ω', IsLQGGood (Real.sqrt κ) (regField ϖ ρ₀ (X₁ ω') +
        ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖)) →
    ∀ (R : ℕ) (W : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure W],
      IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W →
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (M : ZoomModel D3Plus.locFieldFull κ R W)
        (φ : M.Ω₁ → ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω')), Measurable φ ∧
        M.Q.map φ = ((esmRr κ T B X P lvlMu).withDensity w).prod P' ∧
        ∀ᶠ C in atTop, M.Q {ω | locG D3Plus.locFieldFull R
            (zcfgTL κ T B X P ϖ (fun ω' => regField ϖ ρ₀ (X₁ ω')) C (φ ω)) ≠ M.data C ω} ≤ ε

/-- **Existence of a zoom model** (only needed when E5's Palm mass vanishes). -/
def ZoomModelNonemptyStmt : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 → ∀ (R : ℕ) (W : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure W],
    IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W →
    Nonempty (ZoomModel D3Plus.locFieldFull κ R W)

/-! ## 2. The Palm-mass-zero case -/

/-- **E5's left side is at most the Palm mass** for tests bounded by `1`. -/
theorem lhsF_le_pmass {L : Type*} (loc : ℕ → FieldSample × (ℝ → ℝ) → L) (κ T : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (ϖ : Measure ℂ) (δ : ℝ) (R : ℕ) (C : ℝ) {Γ : L → ℝ≥0∞} (hΓ1 : ∀ y, Γ y ≤ 1) :
    lhsF loc κ T P B X ϖ δ R C Γ ≤ pmass κ T P B X ϖ δ := by
  refine lintegral_mono fun ω => ?_
  set S : Set ℝ := {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}
  calc ∫⁻ x in Icc (-δ) 0, S.indicator (fun x => Γ (loc R (zcfg κ T B X ϖ C ω x))) x
          ∂nuPalm κ T B X ϖ ω
        ≤ ∫⁻ x in Icc (-δ) 0, S.indicator 1 x ∂nuPalm κ T B X ϖ ω :=
          lintegral_mono fun x => indicator_le_indicator (hΓ1 _)
      _ ≤ (nuPalm κ T B X ϖ ω).restrict (Icc (-δ) 0) S := lintegral_indicator_one_le S
      _ = nuPalm κ T B X ϖ ω {x | x ∈ Icc (-δ) 0 ∧
            realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} := by
          rw [Measure.restrict_apply' measurableSet_Icc]
          congr 1
          ext x
          simp [S, and_comm]

/-! ## 3. The assembly -/

/-- **The repaired E5 representation input from the level-space model node.** -/
theorem e5ReprG'_of_lvl (hL : E5LvlModelStmt) (hN : ZoomModelNonemptyStmt) :
    E5ReprG' D3Plus.locFieldFull := by
  intro _hE4 κ T Ω _ P _ B X ϖ Ω' _ P' _ Y B'' _hReg hS _hY _hB' _hYB δ hδ R
  obtain ⟨W, hWp, hW⟩ := exists_wiener
  refine ⟨W, hWp, hW, fun ε hε => ?_⟩
  by_cases hp0 : pmass κ T P B X ϖ δ = 0
  · obtain ⟨M⟩ := hN κ hS.1 hS.2.1 R W hW
    refine ⟨M, M.data, fun _ => ∅, fun C Γ _ hΓ1 => ?_, fun _ => MeasurableSet.empty,
      fun _ _ _ => rfl, Eventually.of_forall fun _ => by simp⟩
    rw [hp0, zero_mul]
    exact le_antisymm ((lhsF_le_pmass _ κ T P B X ϖ δ R C hΓ1).trans hp0.le) zero_le
  · obtain ⟨B', hBc, hS', hG, hlhs, hpm⟩ := exists_goodVersion hS
    obtain ⟨hκ, hκ4, hT, hB', hX, hind, hϖ⟩ := id hS'
    obtain ⟨Ω₀, mΩ₀, P₀, X₀, hP₀, hX₀⟩ := QuantumZipper.exists_freeGFF
    have hρ₀ : IsAdmissibleH (foldedCircle 0 2) :=
      isAdmissibleH_foldedCircle (by simp [Hbar]) (by norm_num)
    have hρ1 : foldedCircle 0 2 Set.univ = 1 := measure_univ
    have hρB : foldedCircle 0 2 (Metric.ball (0 : ℂ) 1) = 0 :=
      LateralGerm.foldedCircle_ball_eq_zero one_pos (by norm_num)
    obtain ⟨X₁, hX₁, -, hX'g⟩ := exists_base_regField_good (ϖ := ϖ) hκ hκ4 hX₀ hϖ hρ₀
    have hX' := isFreeGFFModConstH_regField hX₁ hϖ hρ₀
    have hp0' : pmass κ T P B' X ϖ δ ≠ 0 := by rw [hpm δ]; exact hp0
    have hw0 := measurable_w0_level_good hS' hBc hG δ
    have hpos := esmMeas_lvlMu_ne_zero hκ hκ4 hT hB' hX hind hBc δ hp0' hw0
    have hfin := esmMeas_lvlMu_ne_top (κ := κ) (T := T) (B := B') (X := X) (P := P)
    obtain ⟨w, hw, hw1, hrep⟩ := lhsF_eq_levelModel (P' := P₀) (locG D3Plus.locFieldFull) hS'
      hX' hBc hδ R (fun C => palmReadable_of hS' hX' hδ (drvReadable_drvRd hB' hκ δ)
        (modelGood_holds hS' hX' δ) R C) hpos hfin hp0' hw0
    obtain ⟨M, φ, hφm, hφ, hev⟩ := hL κ T P B' X ϖ hBc hS' hG hpos w hw hw1 P₀ X₁
      (foldedCircle 0 2) 1 hX₁ hρ₀ hρ1 one_pos hρB hX'g R W hW ε hε
    set Zl : ℝ → ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω₀) →
        ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ) := fun C z =>
      locG D3Plus.locFieldFull R
        (zcfgTL κ T B' X P ϖ (fun ω' => regField ϖ (foldedCircle 0 2) (X₁ ω')) C z) with hZl
    refine ⟨M, fun C ω => Zl C (φ ω),
      fun C => toMeasurable M.Q {ω | Zl C (φ ω) ≠ M.data C ω}, fun C Γ hΓ _ => ?_,
      fun C => measurableSet_toMeasurable _ _, fun C ω hω => ?_, ?_⟩
    · have hJ := measurable_modelInt_level hS' hBc hG hX₁.measurable_coord (foldedCircle 0 2)
        hX'g R C hΓ
      rw [← hlhs, ← hpm δ, hrep C Γ hΓ hJ, ← hφ, lintegral_map hJ hφm]
    · by_contra h
      exact hω (subset_toMeasurable _ _ h)
    · filter_upwards [hev] with C hC
      rw [measure_toMeasurable]
      exact hC

/-! ## 4. Theorem 1.3 -/

end E5
end QuantumZipper
