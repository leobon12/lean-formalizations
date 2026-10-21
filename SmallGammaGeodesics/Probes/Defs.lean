import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The analytic probes of source §4.1: definitions

The definitions of planning audit GA2, Details (c), copied verbatim, with three renamings that avoid
clashes with §7: GA2's `rectU j`, `rectV j` and `strip j` are `probeRectU j`, `probeRectV j` and
`probeStrip j` here.

* `chi` is a fixed even smooth cutoff, `= 1` on `[-1, 1]` and supported in `[-2, 2]`;
  `rho s = chi s - chi (2 s)`; `ell j = 2⁻ʲ`.
* `probeH j a` is the entire probe `H_{j,a}` of (4.2).
* `sineCoef`, `bandProbe`, `band`, `lowPass` are `b_k`, `B_{j,a}` of (4.3), the band `B_j` of (4.4)
  and the low-pass truncation `S_J`.
* `modulus y r` is the modulus of continuity of `y` on `[0, 1]`.
* `envelope j a x = ∑_± (ℓ_j / max(ℓ_j, dist(x ∓ a, 2ℤ)))² = ∑_± min{1, (ℓ_j/dist(x ∓ a, 2ℤ))²}`
  (GA2 D4.2, with `min{1, ℓ/0} = 1`). **Authorized correction** (orchestrator ruling for P-B1):
  GA2 (c) wrote `min 1 ((ℓ / dist)²)`, which in Lean (`ℓ / 0 = 0`) vanishes at the points
  `x ∓ a ∈ 2ℤ` and makes `lemma41_envelope` false (counterexample `a = x = 1/2`, `k = 0`,
  `j → ∞`; formalized in `Probes/Erratum.lean`). The junk-free form agrees with GA2's formula
  wherever `dist(x ∓ a, 2ℤ) > 0`.
* `probeMap j a θ z = z + i θ H_{j,a}(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Real

namespace SmallGammaGeodesics

/-- The fixed cutoff `χ`: smooth, even, `= 1` on `[-1,1]`, supported in `[-2,2]`. -/
def chiBump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff `χ` as a real function. -/
def chi (s : ℝ) : ℝ := chiBump s

/-- `ρ(s) = χ(s) - χ(2s)`. -/
def rho (s : ℝ) : ℝ := chi s - chi (2 * s)

/-- `ℓ_j = 2^{-j}`. -/
def ell (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹

/-- The probe `H_{j,a}` of (4.2) (entire; the sum is over `1 ≤ k ≤ 2^{j+1}`, which contains the
support of `k ↦ ρ(k ℓ_j)`). -/
def probeH (j : ℕ) (a : ℝ) (z : ℂ) : ℂ :=
  -((2 / ell j : ℝ) : ℂ) * ∑ k ∈ Finset.Icc (1 : ℕ) (2 ^ (j + 1)),
    ((rho ((k : ℝ) * ell j) * Real.sin ((k : ℝ) * π * a) / ((k : ℝ) * π) ^ 2 : ℝ) : ℂ) *
      Complex.sin ((k : ℂ) * π * z)

/-- `b_k = 2 ∫_0^1 y(t) sin(kπt) dt`. -/
def sineCoef (y : ℝ → ℝ) (k : ℕ) : ℝ := 2 * ∫ t in (0 : ℝ)..1, y t * Real.sin (k * π * t)

/-- `B_{j,a} = ℓ_j ∫_0^1 y(t) H''_{j,a}(t) dt` (4.3). -/
def bandProbe (y : ℝ → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  ell j * ∫ t in (0 : ℝ)..1, y t * (iteratedDeriv 2 (fun x : ℝ => (probeH j a x).re) t)

/-- The band `B_j(a) = ∑_k ρ(kℓ_j) b_k sin(kπa)` (4.4). -/
def band (y : ℝ → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) (2 ^ (j + 1)),
    rho ((k : ℝ) * ell j) * sineCoef y k * Real.sin ((k : ℝ) * π * a)

/-- The low-pass truncation `S_J(t) = ∑_k χ(kℓ_J) b_k sin(kπt)`. -/
def lowPass (y : ℝ → ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (1 : ℕ) (2 ^ (J + 1)),
    chi ((k : ℝ) * ell J) * sineCoef y k * Real.sin ((k : ℝ) * π * t)

/-- Modulus of continuity on `[0,1]`. -/
def modulus (y : ℝ → ℝ) (r : ℝ) : ℝ :=
  ⨆ s : Icc (0 : ℝ) 1, ⨆ t : Icc (0 : ℝ) 1, ⨆ (_ : |(s : ℝ) - t| ≤ r), |y s - y t|

/-- The localized envelope `E_{j,a}(x) = ∑_± min{1, (ℓ_j/dist(x ∓ a, 2ℤ))²}` (GA2 D4.2), written
junk-free as `∑_± (ℓ_j / max(ℓ_j, dist(x ∓ a, 2ℤ)))²` so that it equals `1` (not `0`) at the
points `x ∓ a ∈ 2ℤ` (authorized correction of GA2 (c); see the module docstring). -/
def envelope (j : ℕ) (a x : ℝ) : ℝ :=
  (ell j / max (ell j) (Metric.infDist (x - a) (Set.range fun m : ℤ => (2 * m : ℝ)))) ^ 2 +
    (ell j / max (ell j) (Metric.infDist (x + a) (Set.range fun m : ℤ => (2 * m : ℝ)))) ^ 2

/-- The probe map `ϕ(z) = z + iθH(z)`. -/
def probeMap (j : ℕ) (a θ : ℝ) (z : ℂ) : ℂ := z + Complex.I * θ * probeH j a z

/-- `U_j = (-1/4, 5/4) × (-ℓ_j/4, ℓ_j/4)` (GA2's `rectU`). -/
def probeRectU (j : ℕ) : Set ℂ := {z | z.re ∈ Ioo (-1 / 4 : ℝ) (5 / 4) ∧ |z.im| < ell j / 4}

/-- `V_j = (-1/8, 9/8) × (-ℓ_j/8, ℓ_j/8)` (GA2's `rectV`). -/
def probeRectV (j : ℕ) : Set ℂ := {z | z.re ∈ Ioo (-1 / 8 : ℝ) (9 / 8) ∧ |z.im| < ell j / 8}

/-- The strip `S_j = {|Im z| < ℓ_j}` on which `ϕ` is injective (GA2's `strip`). -/
def probeStrip (j : ℕ) : Set ℂ := {z | |z.im| < ell j}

end SmallGammaGeodesics
