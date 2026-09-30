import QuantumZipper.Proofs.Thm18.LWFarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route (D60): excursion measure and Lawler–Werness Lemmas 4.3–4.5

Task LW-EXC. Source: G. F. Lawler, B. M. Werness, *Multi-point Green's functions for SLE and an
estimate of Beffara*, Ann. Probab. 41 (2013), §4.1, pp. 23–25 (`literature/1011.3551.pdf`).

**Excursion measure (LW p. 23).** For boundary arcs `V₁, V₂` of a domain, `ℰ_D(V₁, V₂)` is the
Brownian excursion measure; LW recall it through its conformal invariance and the half-plane
formula `ℰ = ∫ ∂_y h_{V₁}(x) dx` over the part of `ℝ` forming `V₂`, `h_{V₁}` the harmonic measure
of `V₁` (LW cite Lawler, *Conformally invariant processes in the plane*, §5.2). We formalize it
in exactly this form, through a conformal map onto `ℍ` when `V₂` is not already a real interval:
* `yDer h x = lim_{y↓0} h(x + iy)/y` (`= ∂_y h(x)` when `h(x) = 0`, which is the case for a
  harmonic measure at a real boundary point outside `V₁`);
* `excR h J = ∫_J ∂_y h(x) dx` (in `ℝ≥0∞`);
* harmonic measure `IsHarmMeas U A h`: `h` harmonic on `U`, `0 ≤ h ≤ 1`, `h → 1` at the points of
  `A` away from the rest of the frontier, `h → 0` at the frontier points off `closure A` and at `∞`
  (for bounded `A`). This is the Dirichlet characterization of `P^z{BM exits U through A}`.

**Audit (D60 rule), against pp. 23–25 and the horseshoe of D60.**
* `LW43Stmt` — verbatim Lemma 4.3 (p. 23): crosscut `η` of `ℍ`, `−∞ < η(1−) ≤ η(0+) = −1`,
  `diam η ≤ 1/2`, `ℰ(η) = ℰ_{H_η}(η, [0,∞))`. Deterministic; the horseshoe is irrelevant
  (no separation issue: both endpoints lie on `(−∞, −1]`). VERDICT: faithful.
* `LW44Stmt` — Lemma 4.4 (p. 24) after LW's normalization `H = ℍ`; stated in majorant form: for
  every harmonic `0 ≤ h ≤ 1` on `D` tending to `0` at the frontier points at distance `> ε` from
  `z` and at `∞` (the harmonic measure of `V = ∂D ∩ B̄(z, ε)` is one such `h`), which is stronger
  than LW's statement; the proof LW give (Beurling + gambler's ruin) proves this form. "Simply
  connected" is replaced by the weaker condition LW's proof uses: `z` lies in an unbounded
  connected subset of `ℂ \ D` (true for simply connected `D ⊆ ℍ`: every component of `ℂ \ D`
  is unbounded). **LW's hypothesis `d(z, L) > 1/2` with `ε < 1/2` is FALSE as stated**: take
  `Im z = 1/2 + δ`, `ε = 1/2 − δ` and `D = ℍ \ O`, `O` = the circle `|w − z| = ε` minus a short arc
  near its top, the radius from `z` to its top point and the vertical ray above it (`D` simply
  connected, `z ∈ ∂D`); the lower arc of the circle, at height `2δ`, lies in `V`, and the
  excursion flux from `ℝ` into it through the gap of width `≈ 2δ + (x − Re z)²/(2ε)` is
  `≍ (ε/δ)^{1/2} → ∞`. Repair used here: `d(z, L) ≥ 1` (all of LW's uses: (15) gives
  `dist(z, 𝓘) ≥ 1`, Lemmas 4.10, 4.11, pp. 29–30, take `ε ≤ 1/2`). `I` is any set of real points reached vertically from `D` (LW: a subinterval
  of `L ∩ ∂D`; the vertical access makes `∂_y h` meaningful). Deterministic. VERDICT: false as
  printed; repaired (`d(z, L) ≥ 1`), otherwise faithful (stronger majorant form).
* `LW45Stmt` — Lemma 4.5 (p. 24) in the half-plane form LW reduce to in the first line of the
  proof ("by conformal invariance, we may assume `D = ℍ, z₁ = 0, z₂ = ∞`"): `ξ` a crosscut of `ℍ`
  from `ξ(0+) = 0` to a finite real point, `D₁` the bounded component of `ℍ \ ξ` (so
  `z₂ = ∞ ∈ ∂D₂`), `η ⊆ D₁`. `ℰ_ℍ(η, ξ)` is the excursion measure between `η` and `ξ` in
  `D₁ \ η`, computed through a conformal map `ψ : ℍ → D₁` carrying an interval `(p, q)` onto `ξ`.
  Horseshoe: there the offending crosscut separates the tip from `∞` in the future domain; the
  hypothesis `η ⊆ D₁` excludes this (the endpoints of `η` lie in `∂D₁ ∩ ℝ`, one side of `0`), as
  LW require. VERDICT: faithful; the general-domain version is the definition of SLE and of
  `ℰ_D` in `D` via a conformal map, so consumers apply it after the map `Z_t`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Complex
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- A crosscut of `ℍ` with finite real endpoints: `η : (0,1) → ℍ` continuous, injective, with
real limits at `0+` and `1−` (LW p. 23). -/
def IsCrosscutH (η : ℝ → ℂ) : Prop :=
  ContinuousOn η (Ioo 0 1) ∧ InjOn η (Ioo 0 1) ∧ MapsTo η (Ioo 0 1) H ∧
    (∃ a : ℝ, Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) ∧ (∃ b : ℝ, Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))

/-- The point set `η(0,1)` of a crosscut. -/
def arcH (η : ℝ → ℂ) : Set ℂ := η '' Ioo 0 1

/-- The union of the unbounded components of `S` (for `S = ℍ \ η`: LW's `H_η`). -/
def unbddPart (S : Set ℂ) : Set ℂ := {z | z ∈ S ∧ ¬ Bornology.IsBounded (connectedComponentIn S z)}

/-- LW's `H_η`: the unbounded component of `ℍ \ η`. -/
def hullComp (η : ℝ → ℂ) : Set ℂ := unbddPart (H \ arcH η)

/-- `h` is the harmonic measure of the boundary set `A` in the open set `U` (Dirichlet
characterization of `P^z{Brownian motion exits U through A}`). -/
structure IsHarmMeas (U A : Set ℂ) (h : ℂ → ℝ) : Prop where
  harm : InnerProductSpace.HarmonicOnNhd h U
  mem01 : ∀ z ∈ U, 0 ≤ h z ∧ h z ≤ 1
  one : ∀ x₀ ∈ A, x₀ ∉ closure (frontier U \ A) → Tendsto h (𝓝[U] x₀) (𝓝 1)
  zero : ∀ x₀ ∈ frontier U, x₀ ∉ closure A → Tendsto h (𝓝[U] x₀) (𝓝 0)
  infty : Bornology.IsBounded A → Tendsto h (Bornology.cobounded ℂ ⊓ 𝓟 U) (𝓝 0)

/-- `∂_y h(x) = lim_{y↓0} h(x + iy)/y` at a real point `x` (`0` if the limit does not exist;
for a harmonic measure vanishing on a real boundary interval it exists there, by Schwarz
reflection). -/
def yDer (h : ℂ → ℝ) (x : ℝ) : ℝ :=
  open Classical in
  if ∃ L : ℝ, Tendsto (fun y : ℝ => h ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 L) then
    limUnder (𝓝[>] (0 : ℝ)) fun y : ℝ => h ((x : ℂ) + (y : ℂ) * I) / y
  else 0

/-- LW's excursion integral `∫_J ∂_y h(x) dx` (p. 23). -/
def excR (h : ℂ → ℝ) (J : Set ℝ) : ℝ≥0∞ := ∫⁻ x in J, ENNReal.ofReal (yDer h x)

end LWFar
end Thm18Asm
end QuantumZipper
