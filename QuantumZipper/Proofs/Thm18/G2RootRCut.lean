import QuantumZipper.Proofs.Thm18.G2FixMixRootR
import QuantumZipper.Proofs.Thm18.G2RootXCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2, `R(x)` side: Sheffield's smoothing step (cut length `ν_h[0, y − κ]`)

The twin of `G2RootXCut.lean` for `G2FixMixRootRStmt γ ν` (`G2FixMixRootR.lean`): the rooted
point is `y ∈ [0, t₂ + r₂]` (region 2), the length is `ν_h[0, y]`, and the event carries the
truncation `ν_h[0, y] ≤ M = g3Mass` (a function of the field outside region 2). Sheffield
(arXiv:1012.4797, proof of Thm. 1.8, p. 71: "the same applies when we zoom in near `R(x)`"; proof
of Prop. 5.5, pp. 65–66) again splits it into

1. **cut length** (`G2RootRCutStmt`): the length `ν_h[0, y]` (in the outside event and in the
   truncation) replaced by `ν_h[0, y − κ]`, a function of the field outside `B_κ(y)`;
2. **smoothing** (`G2RootRLenSmoothStmt`, p. 66): the two conditionings differ in total variation
   by `o(1)` as `κ → 0`, eventually in `C` (bump in region 2 between `0` and `y − κ`).

`g2FixMixRootRStmt_of_cut` is the triangle inequality `abs_sub_mul_le_of_three` (own elementary
bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The **cut length** at `y`: `ν_h[0, y − κ]`. -/
def g3CutLenR (γ κ : ℝ) (ω : Ω₀) (y : ℝ) : ℝ := (g3Hν γ ω (Icc 0 (y - κ))).toReal

/-- The rooted event with the cut length, in the outside event and in the truncation. -/
def g3RootEvRc (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ gffBase.X q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, g3CutLenR γ κ q.1 q.2.2) ∈ G ∧ ENNReal.ofReal (g3CutLenR γ κ q.1 q.2.2) ≤ g3Mass γ i q.1}

/-- The same without the zoom. -/
def g3RootEvRc0 (γ : ℝ) (i : G3Idx) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) : Set (Ω₀ × ℝ × ℝ) :=
  {q | |q.2.2 - i.t₂| + m < i.r₂ ∧
    (q.1, g3CutLenR γ κ q.1 q.2.2) ∈ G ∧ ENNReal.ofReal (g3CutLenR γ κ q.1 q.2.2) ≤ g3Mass γ i q.1}

theorem g3RootEvR_univ (γ : ℝ) (i : G3Idx) (m : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvR γ i univ m G = g3RootEvR0 i m G := by
  ext q; simp [g3RootEvR, g3RootEvR0]

theorem g3RootEvRc_univ (γ : ℝ) (i : G3Idx) (m κ : ℝ) (G : Set (Ω₀ × ℝ)) :
    g3RootEvRc γ i univ m κ G = g3RootEvRc0 γ i m κ G := by
  ext q; simp [g3RootEvRc, g3RootEvRc0]

/-- **Node 1, `R` side (cut length).** As `G2RootXCutStmt`, at `y` in region 2, with the cut
length `ν_h[0, y − κ]` in the outside event and in the truncation `≤ M` (Sheffield,
arXiv:1012.4797, Prop. 1.6, p. 24; proofs of Prop. 5.5 and Thm. 1.8, pp. 65, 71). -/
def G2RootRCutStmt (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ ε > 0, ∀ᶠ C in (atTop : Filter ℝ),
    ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvRc γ i t m κ G).indicator 1)).toReal -
        ν.real t * (g3RootIntR γ i ((g3RootEvRc0 γ i m κ G).indicator 1)).toReal| ≤ ε

/-- **Node 2, `R` side (smoothing of the length coordinate; Sheffield, arXiv:1012.4797, proof of
Prop. 5.5, p. 66).** -/
def G2RootRLenSmoothStmt (γ : ℝ) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m : ℝ, 0 < m → ∀ ε > 0, ∃ ε₀ > 0, ∀ κ ∈ Ioo 0 ε₀,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) → ∀ G : Set (gffBase.Ω × ℝ),
      MeasurableSet[outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] G →
      |(g3RootIntR γ i ((g3RootEvR γ i t m G ∩ g3TM γ i).indicator 1)).toReal -
        (g3RootIntR γ i ((g3RootEvRc γ i t m κ G).indicator 1)).toReal| ≤ ε

/-- **`G2FixMixRootRStmt` from Sheffield's two steps** (cut length + smoothing). -/
theorem g2FixMixRootRStmt_of_cut {γ : ℝ} {ν : Measure LawD} [IsProbabilityMeasure ν]
    (hS : G2RootRLenSmoothStmt γ) (hC : G2RootRCutStmt γ ν) : G2FixMixRootRStmt γ ν := by
  intro t ht δ η m hm ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨ε₁, hε₁, h₁⟩ := hS t ht δ η m hm (ε / 3) hε3
  obtain ⟨ε₂, hε₂, h₂⟩ := hS univ univ_mem_lawCyl δ η m hm (ε / 3) hε3
  set κ : ℝ := min (min ε₁ ε₂) m / 2 with hκ
  have hmin : 0 < min (min ε₁ ε₂) m := lt_min (lt_min hε₁ hε₂) hm
  have hκ0 : 0 < κ := by positivity
  have hκlt : κ < min (min ε₁ ε₂) m := by rw [hκ]; linarith
  have hκ1 : κ < ε₁ := hκlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hκ2 : κ < ε₂ := hκlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hκm : κ < m := hκlt.trans_le (min_le_right _ _)
  filter_upwards [h₁ κ ⟨hκ0, hκ1⟩, h₂ κ ⟨hκ0, hκ2⟩, hC t ht δ η m κ hκ0 hκm (ε / 3) hε3]
    with C hC₁ hC₂ hC₃ i hi G hG
  have a1 := hC₁ i hi G hG
  have a2 := hC₃ i hi G hG
  have a3 := hC₂ i hi G hG
  rw [g3RootEvR_univ, g3RootEvRc_univ] at a3
  exact abs_sub_mul_le_of_three measureReal_nonneg measureReal_le_one a1 a2 a3

end Thm18Asm
end QuantumZipper
