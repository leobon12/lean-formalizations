import QuantumZipper.Proofs.Thm18.G3ConcreteField
import QuantumZipper.Proofs.Thm18.G3ConcreteMaps
import QuantumZipper.Proofs.NonVacuityFinal
import Mathlib.Probability.Distributions.Exponential

/-!
# G3 concrete scheme (part 3): the scheme map and `G3MarkovStmt`

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 70–71), Figure 1.7: sample `h` from
the `ν_h[−δ, 0]`-weighted law, `x` from `ν_h|[−δ,0]`, let `R(x)` be its welding partner, and zoom
in at `x` and `R(x)`. "The conditional law of the restrictions of `h` to the two halves … are
independent by the standard GFF Markov property." The concrete scheme (handoff `G3.md`, G3-SCH):

* base: a free-boundary GFF modulo constants `X₀` on `(Ω₀, P₀)` (`gffBase`, from
  `exists_BM_indep_freeGFF_uncond`); field `h = 𝔥₀ + X₀ − X₀(S)` (`normField`);
* index `i = (δ, η, C)`, `0 < η < δ ≤ 1/4`; half-discs `B(t₁, r₁)` around `[−δ, −η]` and
  `B(t₂, r₂)` around `[η, 1/2]`, disjoint and inside the unit disc (`geom_*`);
* boundary lengths from the region fields only: `ν₁, ν₂` (regions), `ν₀` (gap);
* Palm point by length on `Ω₀ × ℝ`: law `w · (P₀ ⊗ Exp(1))`, `w ∝ e^ℓ 1{0 < ℓ ≤ (ν₁+ν₀)[−δ,0]}`
  (normalized by its total mass `Z`; junk weight `1` if `Z ∉ (0,∞)`); `x = lenLeft (ν₁+ν₀) ℓ`,
  `R = lenRight (ν₀+ν₂) ℓ`;
* zooms `U = zoomLaw γ C (region field 1) x`, `V = zoomLaw γ C (region field 2) R`;
* conditioning `𝒢 = outsideSigmaPalm` (field outside both regions, and `ℓ`).

The filter on the index set is a parameter `l` (only `NeBot` is used here; the order of the
limits `C → ∞`, `η → 0`, `δ → 0` is to be fixed by G2 and G3-Transfer).

`g3MarkovStmt_concrete`: `G3MarkovStmt (g3ConcreteMap l)`, from `condIndepCE_twoHalfDisc_palm`
and the exact measurability of the region fields (M1), the zoom maps (M2), and the normalization
of the Palm weight (M3). Own arguments for the bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set MeasurableSpace Filter
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open K3

/-! ## The base sample -/

/-- A free-boundary GFF modulo constants on its own probability space. -/
structure GFFBase where
  Ω : Type
  [m : MeasurableSpace Ω]
  P : Measure Ω
  X : Ω → FieldSample
  prob : IsProbabilityMeasure P
  gff : IsFreeGFFModConstH X P

attribute [instance] GFFBase.m

theorem nonempty_gffBase : Nonempty GFFBase := by
  obtain ⟨Ω, m, P, -, X, hP, -, hX, -⟩ := NonVacuity.exists_BM_indep_freeGFF_uncond
  exact ⟨@GFFBase.mk Ω m P X hP hX⟩

/-- The chosen base sample. -/
def gffBase : GFFBase := Classical.choice nonempty_gffBase

instance : IsProbabilityMeasure gffBase.P := gffBase.prob

/-! ## Index and geometry -/

/-- Scheme index `(δ, η, C)` with `0 < η < δ ≤ 1/4`. -/
def G3Idx : Type := {p : ℝ × ℝ × ℝ // 0 < p.2.1 ∧ p.2.1 < p.1 ∧ p.1 ≤ 1 / 4}

namespace G3Idx

variable (i : G3Idx)

def δ : ℝ := i.1.1
def η : ℝ := i.1.2.1
def C : ℝ := i.1.2.2
/-- Centre and radius of the half-disc around `[−δ, −η]`. -/
def t₁ : ℝ := -(i.δ + i.η) / 2
def r₁ : ℝ := (i.δ - i.η) / 2 + i.η / 4
/-- Centre and radius of the half-disc around `[η, 1/2]`. -/
def t₂ : ℝ := (1 / 2 + i.η) / 2
def r₂ : ℝ := (1 / 2 - i.η) / 2 + i.η / 4

theorem hη : 0 < i.η := i.2.1
theorem hηδ : i.η < i.δ := i.2.2.1
theorem hδ : i.δ ≤ 1 / 4 := i.2.2.2

theorem r₁_pos : 0 < i.r₁ := by
  have := i.hη; have := i.hηδ; unfold r₁; linarith

theorem r₂_pos : 0 < i.r₂ := by
  have := i.hη; have := i.hηδ; have := i.hδ; unfold r₂; linarith

theorem dist_le : i.r₁ + i.r₂ ≤ dist (i.t₁ : ℂ) i.t₂ := by
  have := i.hη; have := i.hηδ
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (by unfold t₁ t₂; linarith)]
  unfold r₁ r₂ t₁ t₂; linarith

theorem inUnit₁ : |i.t₁| + i.r₁ ≤ 1 := by
  have := i.hη; have := i.hηδ; have := i.hδ
  rw [abs_of_neg (by unfold t₁; linarith)]; unfold t₁ r₁; linarith

theorem inUnit₂ : |i.t₂| + i.r₂ ≤ 1 := by
  have := i.hη; have := i.hηδ; have := i.hδ
  rw [abs_of_pos (by unfold t₂; linarith)]; unfold t₂ r₂; linarith

end G3Idx

/-! ## The scheme -/

section Scheme

variable (γ : ℝ) (i : G3Idx)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The exponential law of the Palm length. -/
abbrev L₀ : Measure ℝ := expMeasure 1

instance : IsProbabilityMeasure L₀ := isProbabilityMeasure_expMeasure one_pos

/-- Boundary length measures read from region 1, region 2, and the gap. -/
def g3ν₁ (ω : Ω₀) : Measure ℝ := bdryM γ (regionField γ i.t₁ i.r₁ X₀ ω)
def g3ν₂ (ω : Ω₀) : Measure ℝ := bdryM γ (regionField γ i.t₂ i.r₂ X₀ ω)
def g3ν₀ (ω : Ω₀) : Measure ℝ := bdryM γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ X₀ ω)

/-- The Palm point `x ≤ 0` (`ν[x, 0] = ℓ`) and its length partner `R ≥ 0` (`ν[0, R] = ℓ`). -/
def g3X (p : Ω₀ × ℝ) : ℝ := lenLeft (g3ν₁ γ i p.1 + g3ν₀ γ i p.1) p.2
def g3R (p : Ω₀ × ℝ) : ℝ := lenRight (g3ν₀ γ i p.1 + g3ν₂ γ i p.1) p.2

/-- The zoom near `x` (region 1 only) and near `R(x)` (region 2 only). -/
def g3U (p : Ω₀ × ℝ) : LawD := zoomLaw γ i.C (regionField γ i.t₁ i.r₁ X₀ p.1) (g3X γ i p)
def g3V (p : Ω₀ × ℝ) : LawD := zoomLaw γ i.C (regionField γ i.t₂ i.r₂ X₀ p.1) (g3R γ i p)

/-- The Palm mass `ν_h[−δ, 0]`. -/
def g3Mass (ω : Ω₀) : ℝ≥0∞ := (g3ν₁ γ i ω + g3ν₀ γ i ω) (Icc (-i.δ) 0)

open Classical in
/-- The unnormalized Palm density `e^ℓ 1{0 < ℓ ≤ ν_h[−δ,0]}` w.r.t. `P₀ ⊗ Exp(1)`. -/
def g3W0 (p : Ω₀ × ℝ) : ℝ≥0∞ :=
  if 0 < p.2 ∧ ENNReal.ofReal p.2 ≤ g3Mass γ i p.1 then ENNReal.ofReal (Real.exp p.2) else 0

/-- Its total mass (`= E ν_h[−δ, 0]`). -/
def g3Z : ℝ≥0∞ := ∫⁻ p, g3W0 γ i p ∂(gffBase.P.prod L₀)

open Classical in
/-- The normalized Palm density (junk `1` if the total mass is `0` or `∞`). -/
def g3W : Ω₀ × ℝ → ℝ≥0 :=
  if 0 < g3Z γ i ∧ g3Z γ i < ⊤ then fun p => ((g3Z γ i)⁻¹ * g3W0 γ i p).toNNReal
  else fun _ => 1

/-- The Palm law on `Ω₀ × ℝ`. -/
def g3PalmLaw : Measure (Ω₀ × ℝ) := (gffBase.P.prod L₀).withDensity fun p => (g3W γ i p : ℝ≥0∞)

/-- The concrete scheme for `γ`, with filter `l` on the index set. -/
def g3ConcreteScheme (l : Filter G3Idx) : G3Scheme where
  ι := G3Idx
  l := l
  Ω' := fun _ => Ω₀ × ℝ
  𝒢 := fun i => outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂
  m := fun _ => inferInstance
  P' := fun i => g3PalmLaw γ i
  U := fun i => g3U γ i
  V := fun i => g3V γ i

end Scheme

/-- **The concrete G3 scheme map** (the Theorem 1.8 sample is used only through `γ`). -/
def g3ConcreteMap (l : ℝ → Filter G3Idx) : G3SchemeMap :=
  fun γ _ _ _ _ _ => g3ConcreteScheme γ (l γ)

end Thm18Asm
end QuantumZipper
