/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import QuantumZipper.LQG.Wedge
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Wedge, cone and zipping parameters (DMS Tables 1.1–1.3)

Duplantier–Miller–Sheffield (arXiv:1409.7055v4), L428–471 and L629–660.
For `γ ∈ (0,2)`, `Q = 2/γ + γ/2` (QuantumZipper's `Qc`) and `χ = 2/γ − γ/2` (QuantumZipper's
`chiC` at `κ = γ²`), every parameter of a quantum wedge or cone is an affine function of its
weight `W`. We take `W` as the primary coordinate and define the other parameters from it; each
table entry is then a lemma (`Foundations/ParamsWedge.lean`, `ParamsCone.lean`, `ParamsZip.lean`).

Here: the definitions, `chi`, the thick/thin thresholds, and the bridge to QuantumZipper's
α-wedge (`QuantumZipper.IsQuantumWedge γ α` is parameterized by `α`, the same convention as DMS
(1.4): `W = γ(γ + 2/γ − α)`, so the weight-2 wedge is the γ-wedge).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper Real

/-- `χ = 2/γ − γ/2` as QuantumZipper's `chiC κ` at `κ = γ²`. -/
abbrev chi (γ : ℝ) : ℝ := chiC (γ ^ 2)

theorem chi_eq {γ : ℝ} (hγ : 0 < γ) : chi γ = 2 / γ - γ / 2 := by
  simp [chi, chiC, Real.sqrt_sq hγ.le]

theorem chi_eq' {γ : ℝ} (hγ : 0 < γ) : chi γ = (4 - γ ^ 2) / (2 * γ) := by
  rw [chi_eq hγ]; field_simp; ring

theorem Qc_eq_chi_add {γ : ℝ} (hγ : 0 < γ) : Qc γ = chi γ + γ := by
  rw [chi_eq hγ, Qc]; ring

theorem chi_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : 0 < chi γ := by
  rw [chi_eq' hγ]; apply div_pos <;> nlinarith

/-! ## Table 1.1: wedge parameters as functions of the weight `W` (DMS (1.4), Table 1.1) -/

/-- `α = γ/2 + Q − W/γ` (DMS (1.4): `W = γ(γ/2 + Q − α)`). -/
def wedgeAlpha (γ W : ℝ) : ℝ := γ / 2 + Qc γ - W / γ
/-- Imaginary-geometry angle gap `θ = πW/(χγ)`. -/
def wedgeTheta (γ W : ℝ) : ℝ := π * W / (chi γ * γ)
/-- Bessel dimension `δ = 1 + 2W/γ²`. -/
def wedgeDelta (γ W : ℝ) : ℝ := 1 + 2 * W / γ ^ 2
/-- Strip drift `a = W/γ − γ/2`. -/
def wedgeA (γ W : ℝ) : ℝ := W / γ - γ / 2
/-- Boundary quantum scaling exponent `Δ = (W − 2)/γ²`. -/
def wedgeDeltaExp (γ W : ℝ) : ℝ := (W - 2) / γ ^ 2

/-! ## Table 1.2: cone parameters as functions of the weight `W` (DMS (1.5), Table 1.2) -/

/-- `α = Q − W/(2γ)` (DMS (1.5): `W = 2γ(Q − α)`). -/
def coneAlpha (γ W : ℝ) : ℝ := Qc γ - W / (2 * γ)
/-- Space of angles `θ = πW/(γχ)`. -/
def coneTheta (γ W : ℝ) : ℝ := π * W / (γ * chi γ)
/-- Bessel dimension `δ = 2 + 2W/γ²`. -/
def coneDelta (γ W : ℝ) : ℝ := 2 + 2 * W / γ ^ 2
/-- Cylinder drift `a = W/(2γ)`. -/
def coneA (γ W : ℝ) : ℝ := W / (2 * γ)
/-- Interior quantum scaling exponent `Δ = 1/2 + (W − 4)/(2γ²)`. -/
def coneDeltaExp (γ W : ℝ) : ℝ := 1 / 2 + (W - 4) / (2 * γ ^ 2)

/-! ## Table 1.3: zipping -/

/-- The `ρ` of the whole-plane `SLE_κ(ρ)` obtained by zipping a weight-`W` wedge (Thm 1.5). -/
def zipRho (W : ℝ) : ℝ := W - 2
/-- DMS (1.10) `eqn::cone_wedge_value`: zipping an `α`-wedge gives an `(α/2 + 1/γ)`-cone. -/
def coneOfWedgeAlpha (γ α : ℝ) : ℝ := α / 2 + 1 / γ
/-- Inverse of `coneOfWedgeAlpha` (Table 1.3(b), entry `α` of `α'`). -/
def wedgeOfConeAlpha (γ α' : ℝ) : ℝ := 2 * α' - 2 / γ

set_option hygiene false in
/-- Normalization tactic for the table identities. -/
macro "params_tac" : tactic => `(tactic| (
  have hγ0 : (γ : ℝ) ≠ 0 := ne_of_gt ‹0 < γ›
  have hχ4 : (4 : ℝ) - γ ^ 2 ≠ 0 := by nlinarith
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [wedgeAlpha, wedgeTheta, wedgeDelta, wedgeA, wedgeDeltaExp, coneAlpha, coneTheta,
    coneDelta, coneA, coneDeltaExp, zipRho, chi_eq' ‹0 < γ›, Qc] <;> (try field_simp) <;> ring))

variable {γ W : ℝ}

theorem coneAlpha_eq_coneOfWedgeAlpha (hγ : 0 < γ) (hγ2 : γ < 2) :
    coneAlpha γ W = coneOfWedgeAlpha γ (wedgeAlpha γ W) := by
  simp only [coneOfWedgeAlpha]; params_tac

theorem wedgeAlpha_eq_wedgeOfConeAlpha (hγ : 0 < γ) (hγ2 : γ < 2) :
    wedgeAlpha γ W = wedgeOfConeAlpha γ (coneAlpha γ W) := by
  simp only [wedgeOfConeAlpha]; params_tac

theorem wedgeOfConeAlpha_coneOfWedgeAlpha (α : ℝ) :
    wedgeOfConeAlpha γ (coneOfWedgeAlpha γ α) = α := by
  simp only [wedgeOfConeAlpha, coneOfWedgeAlpha]; ring

theorem coneOfWedgeAlpha_wedgeOfConeAlpha (α' : ℝ) :
    coneOfWedgeAlpha γ (wedgeOfConeAlpha γ α') = α' := by
  simp only [wedgeOfConeAlpha, coneOfWedgeAlpha]; ring

/-- Table 1.3: the angle is unchanged by zipping. -/
theorem coneTheta_eq_wedgeTheta : coneTheta γ W = wedgeTheta γ W := by
  simp only [coneTheta, wedgeTheta, mul_comm γ]

/-! ## Thick/thin thresholds (DMS L397–418, Table 1.1 caption) -/

theorem wedge_thick_iff_alpha (hγ : 0 < γ) : γ ^ 2 / 2 ≤ W ↔ wedgeAlpha γ W ≤ Qc γ := by
  rw [wedgeAlpha, show γ / 2 + Qc γ - W / γ ≤ Qc γ ↔ γ / 2 ≤ W / γ by constructor <;> intro <;> linarith,
    le_div_iff₀ hγ]; constructor <;> intro <;> nlinarith

theorem wedge_thick_iff_delta (hγ : 0 < γ) : γ ^ 2 / 2 ≤ W ↔ 2 ≤ wedgeDelta γ W := by
  have h : 0 < γ ^ 2 := by positivity
  rw [wedgeDelta, show 2 ≤ 1 + 2 * W / γ ^ 2 ↔ 1 ≤ 2 * W / γ ^ 2 by constructor <;> intro <;> linarith,
    le_div_iff₀ h]; constructor <;> intro <;> linarith

theorem wedge_thick_iff_a (hγ : 0 < γ) : γ ^ 2 / 2 ≤ W ↔ 0 ≤ wedgeA γ W := by
  rw [wedgeA, sub_nonneg, le_div_iff₀ hγ]; constructor <;> intro <;> nlinarith

theorem wedge_pos_iff_alpha (hγ : 0 < γ) : 0 < W ↔ wedgeAlpha γ W < Qc γ + γ / 2 := by
  rw [wedgeAlpha]; constructor <;> intro h
  · have := div_pos h hγ; linarith
  · have : 0 < W / γ := by linarith
    exact (div_pos_iff_of_pos_right hγ).1 this

theorem wedge_pos_iff_delta (hγ : 0 < γ) : 0 < W ↔ 1 < wedgeDelta γ W := by
  have h : 0 < γ ^ 2 := by positivity
  rw [wedgeDelta, lt_add_iff_pos_right, div_pos_iff_of_pos_right h]; constructor <;> intro <;> linarith

theorem wedge_pos_iff_a (hγ : 0 < γ) : 0 < W ↔ -(γ / 2) < wedgeA γ W := by
  rw [wedgeA]; constructor <;> intro h
  · have := div_pos h hγ; linarith
  · exact (div_pos_iff_of_pos_right hγ).1 (by linarith)

/-- Thin wedges: `W ∈ (0, γ²/2) ⇔ α ∈ (Q, Q + γ/2)`. -/
theorem wedge_thin_iff_alpha (hγ : 0 < γ) :
    (0 < W ∧ W < γ ^ 2 / 2) ↔ (Qc γ < wedgeAlpha γ W ∧ wedgeAlpha γ W < Qc γ + γ / 2) := by
  have h1 := wedge_pos_iff_alpha hγ (W := W)
  have h2 := (wedge_thick_iff_alpha hγ (W := W)).not
  push Not at h2
  rw [h1, h2]; tauto

theorem wedge_thin_iff_delta (hγ : 0 < γ) :
    (0 < W ∧ W < γ ^ 2 / 2) ↔ (1 < wedgeDelta γ W ∧ wedgeDelta γ W < 2) := by
  have h1 := wedge_pos_iff_delta hγ (W := W)
  have h2 := (wedge_thick_iff_delta hγ (W := W)).not
  push Not at h2
  rw [h1, h2]

theorem wedge_thin_iff_a (hγ : 0 < γ) :
    (0 < W ∧ W < γ ^ 2 / 2) ↔ (-(γ / 2) < wedgeA γ W ∧ wedgeA γ W < 0) := by
  have h1 := wedge_pos_iff_a hγ (W := W)
  have h2 := (wedge_thick_iff_a hγ (W := W)).not
  push Not at h2
  rw [h1, h2]

theorem cone_pos_iff_alpha (hγ : 0 < γ) : 0 < W ↔ coneAlpha γ W < Qc γ := by
  rw [coneAlpha, sub_lt_self_iff, div_pos_iff_of_pos_right (by positivity)]

/-! ## Bridge to QuantumZipper's α-wedge -/

/-- The weight-2 wedge is the `γ`-wedge (`QuantumZipper.IsQuantumWedge γ γ`). -/
theorem wedgeAlpha_two (hγ : 0 < γ) : wedgeAlpha γ 2 = γ := by
  have := hγ.ne'; simp only [wedgeAlpha, Qc]; field_simp; ring

/-- DMS (1.4): QuantumZipper's `α`-wedge has weight `γ(γ + 2/γ − α)`. -/
theorem wedgeAlpha_weight (hγ : 0 < γ) (α : ℝ) : wedgeAlpha γ (γ * (γ + 2 / γ - α)) = α := by
  have := hγ.ne'; simp only [wedgeAlpha, Qc]; field_simp; ring

end MatedCRTHarmonic.MoTPort
