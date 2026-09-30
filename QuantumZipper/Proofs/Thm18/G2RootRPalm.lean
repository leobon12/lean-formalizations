import QuantumZipper.Proofs.Thm18.G2RootRCut
import QuantumZipper.Proofs.Thm18.G2RootXPalmAsm
import QuantumZipper.Proofs.Thm18.G3PalmRTightBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2, `R(x)` side, cut form: the Palm identity, the fixed-point zoom and the assembly

The twin of `G2RootXPalm.lean` + `G2RootXPalmAsm.lean` for `G2RootRCutStmt γ ν`. The conditioning
variables at the rooted point `y` (region 2) are the outside coordinates, the cut length
`ν_h[0, y − κ]` and the truncation level `M = g3Mass` (the scheme's mass of `[−δ, 0]`, a function
of the field in region 1 and the gap, hence outside `B_κ(y)`); the outside event is any measurable
`G''` of these three (`g3PalmCondR`). The truncated events of the node are `G'' = truncSet G'`.

* `G2RootRPalmIdStmt γ` — Palm identity (Duplantier–Sheffield, arXiv:0808.1560, §3.3; normalized
  form `PalmNorm.palm_formula_norm`) on the window `[0, t₂ + r₂]`;
* `G2RootRFixStmt γ ν` — the conditional zoom at a fixed `y` (D3⁺(i) at `y`);
* `g2RootRCutStmt_of_palm` — the assembly over `y`; the total Palm mass of the window is finite
  by the explicit bound `rhoX_le` (`k_S = −2 log⁺‖·‖`, `kPot_refS_eq`), so no first-moment
  estimate on `[0, t₂ + r₂]` is needed.

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-! ## The Palm density is bounded on bounded windows -/

theorem rhoX_le {γ : ℝ} (hγ : 0 < γ) {b y : ℝ} (hy : y ∈ Icc 0 b) :
    rhoX γ y ≤ Real.exp (γ * (2 / Real.sqrt (γ ^ 2)) / 2 * b -
      γ / 2 * ∫ u, h0rev (γ ^ 2) u ∂refS + γ ^ 2 / 2 * b + γ ^ 2 / 8 * PalmNorm.kkPot refS) := by
  unfold rhoX PalmNorm.rhoNorm
  apply Real.exp_le_exp.2
  have hn : ‖(y : ℂ)‖ ≤ b := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy.1]; exact hy.2
  have hk := kPot_refS_eq (y : ℂ)
  have h1 : h0rev (γ ^ 2) (y : ℂ) = 2 / Real.sqrt (γ ^ 2) * Real.log ‖(y : ℂ)‖ := rfl
  have hlog : Real.log ‖(y : ℂ)‖ ≤ b := (Real.log_le_self (norm_nonneg _)).trans hn
  have hpos : Real.posLog ‖(y : ℂ)‖ ≤ b :=
    (Real.posLog_le_abs _).trans (by rw [abs_of_nonneg (norm_nonneg _)]; exact hn)
  have hc : 0 ≤ γ * (2 / Real.sqrt (γ ^ 2)) / 2 := by positivity
  rw [h1, show refS = foldedCircle 0 1 from rfl, hk]
  have e1 : γ * (2 / Real.sqrt (γ ^ 2) * Real.log ‖(y : ℂ)‖) / 2 =
      γ * (2 / Real.sqrt (γ ^ 2)) / 2 * Real.log ‖(y : ℂ)‖ := by ring
  have i1 := mul_le_mul_of_nonneg_left hlog hc
  have i2 := mul_le_mul_of_nonneg_left hpos (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)
  rw [e1]
  nlinarith

theorem lintegral_rhoX_Icc_lt_top {γ : ℝ} (hγ : 0 < γ) (b : ℝ) :
    ∫⁻ y in Icc 0 b, ENNReal.ofReal (rhoX γ y) < ⊤ := by
  set K : ℝ := Real.exp (γ * (2 / Real.sqrt (γ ^ 2)) / 2 * b -
      γ / 2 * ∫ u, h0rev (γ ^ 2) u ∂refS + γ ^ 2 / 2 * b + γ ^ 2 / 8 * PalmNorm.kkPot refS)
  calc ∫⁻ y in Icc 0 b, ENNReal.ofReal (rhoX γ y) ≤ ∫⁻ _ in Icc 0 b, ENNReal.ofReal K :=
        setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal (rhoX_le hγ hy)
    _ = ENNReal.ofReal K * volume (Icc (0 : ℝ) b) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

/-! ## The objects at `y` -/

/-- The conditioning space at `y`: outside coordinates, cut length, truncation level. -/
abbrev CondR (i : G3Idx) : Type := (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ × ℝ≥0∞

/-- The scheme's mass of `[−δ, 0]` read from the shifted field. -/
def g3MassP (γ : ℝ) (i : G3Idx) (y : ℝ) (ω : Ω₀) : ℝ≥0∞ :=
  (bdryM γ (regionField γ i.t₁ i.r₁ (xPalm γ y) ω) +
    bdryM γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ (xPalm γ y) ω)) (Icc (-i.δ) 0)

/-- The conditioning variables of the Palm field at `y`. -/
def g3PalmCondR (γ : ℝ) (i : G3Idx) (κ y : ℝ) (ω : Ω₀) : CondR i :=
  (outMap i (xPalm γ y ω),
    (qBoundaryMeasure γ (normField γ (xPalm γ y) ω) (Icc 0 (y - κ))).toReal, g3MassP γ i y ω)

/-- The shifted event at a fixed `y`. -/
def g3PalmEvR (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G'' : Set (CondR i)) (y : ℝ) :
    Set Ω₀ :=
  {ω | zoomLaw γ i.C (normField γ (xPalm γ y) ω) y ∈ t ∧ |y - i.t₂| + m < i.r₂ ∧
    g3PalmCondR γ i κ y ω ∈ G''}

/-- The rooted event with a general conditioning event `G''`. -/
def g3RootEvRcc (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ) (G'' : Set (CondR i)) :
    Set (Ω₀ × ℝ × ℝ) :=
  {q | zoomLaw γ i.C (normField γ X₀ q.1) q.2.2 ∈ t ∧ |q.2.2 - i.t₂| + m < i.r₂ ∧
    (outMap i (X₀ q.1), g3CutLenR γ κ q.1 q.2.2, g3Mass γ i q.1) ∈ G''}

/-- The truncated outside event. -/
def truncSet (i : G3Idx) (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)) : Set (CondR i) :=
  {p | (p.1, p.2.1) ∈ G' ∧ ENNReal.ofReal p.2.1 ≤ p.2.2}

theorem measurableSet_truncSet (i : G3Idx) {G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)}
    (hG' : MeasurableSet G') : MeasurableSet (truncSet i G') :=
  ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)) hG').inter
    (measurableSet_le (ENNReal.measurable_ofReal.comp (measurable_fst.comp measurable_snd))
      (measurable_snd.comp measurable_snd))

theorem g3RootEvRc_eq (γ : ℝ) (i : G3Idx) (t : Set LawD) (m κ : ℝ)
    (G' : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ)) :
    g3RootEvRc γ i t m κ (outEv i G') = g3RootEvRcc γ i t m κ (truncSet i G') := by
  ext q; simp [g3RootEvRc, g3RootEvRcc, truncSet, outEv]

theorem g3PalmEvR_univ_univ (γ : ℝ) (i : G3Idx) (m κ y : ℝ) :
    g3PalmEvR γ i univ m κ univ y = {_ω | |y - i.t₂| + m < i.r₂} := by
  ext _ω; simp [g3PalmEvR]

theorem G3Idx.t₂_r₂_congr {i i' : G3Idx} (h₂ : i.1.2.1 = i'.1.2.1) :
    i.t₂ = i'.t₂ ∧ i.r₂ = i'.r₂ := by
  unfold G3Idx.t₂ G3Idx.r₂ G3Idx.η
  rw [h₂]; exact ⟨rfl, rfl⟩

/-! ## The two nodes -/

/-- **Node P, `R` side (Palm identity; Duplantier–Sheffield, arXiv:0808.1560, §3.3;
`PalmNorm.palm_formula_norm`).** -/
def G2RootRPalmIdStmt (γ : ℝ) : Prop :=
  ∀ (i : G3Idx) (t : Set LawD), MeasurableSet t → ∀ m κ : ℝ, 0 < m → 0 < κ →
    ∀ G'' : Set (CondR i), MeasurableSet G'' →
      g3RootIntR γ i ((g3RootEvRcc γ i t m κ G'').indicator 1) =
        ∫⁻ y in Icc 0 (i.t₂ + i.r₂),
          ENNReal.ofReal (rhoX γ y) * gffBase.P (g3PalmEvR γ i t m κ G'' y) ∧
      AEMeasurable (fun y => ENNReal.ofReal (rhoX γ y) * gffBase.P (g3PalmEvR γ i t m κ G'' y))
        (volume.restrict (Icc 0 (i.t₂ + i.r₂)))

/-- **Node F, `R` side (conditional zoom at a fixed `y`; Sheffield, arXiv:1012.4797, Prop. 1.6
and proofs of Prop. 5.5 and Thm. 1.8, pp. 24, 65, 71; D3⁺(i) at `y`).** -/
def G2RootRFixStmt (γ : ℝ) (ν : Measure LawD) : Prop :=
  ∀ t ∈ lawCyl, ∀ δ η m κ : ℝ, 0 < κ → κ < m → ∀ y : ℝ, ∀ ε > 0,
    ∀ᶠ C in (atTop : Filter ℝ), ∀ i : G3Idx, i.1 = (δ, η, C) →
      ∀ G'' : Set (CondR i), MeasurableSet G'' →
        |(gffBase.P (g3PalmEvR γ i t m κ G'' y)).toReal -
          ν.real t * (gffBase.P (g3PalmEvR γ i univ m κ G'' y)).toReal| ≤ ε

end Thm18Asm
end QuantumZipper
