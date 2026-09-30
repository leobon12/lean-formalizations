import QuantumZipper.Proofs.LQG.CoordChangeAvg
import QuantumZipper.LQG.Measures
import QuantumZipper.GFF.Defs
import QuantumZipper.Proofs.Zipper.AreaWinDefs
import QuantumZipper.Proofs.Zipper.BdryAllMapsSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-CORE: the Sheffield–Wang "uniform in all conformal maps" cores (statements only)

Task SW-CONSOLIDATE (Theorems 1.3/1.8). Decision and derivations: `handoff/SW-CORE.md`.

Source: S. Sheffield, M. Wang, *Field-measure correspondence in Liouville quantum gravity almost
surely commutes with all conformal maps simultaneously*, arXiv:1605.06171
(`literature/1605.06171.pdf`): Theorem 1.4 (p. 4, proof pp. 11–15), Lemma 3.4 ((3.17)–(3.19),
p. 15), Lemma 3.5 ((3.20)–(3.23), p. 16), Theorems 4.2–4.3 (pp. 18–19, (4.4)–(4.6)).

SW control the distortion between the pushed and the round regularization **in the mean**
((3.11), (4.6)), for *mollifier* regularizations, where continuity in the map is automatic
("`h` is a.s. a distribution", SW Remark 3.3, p. 11). In this repository the regularization is by
(semi)circle averages (`avgReg`/`evalReg`, adaptation SW-A3), so the values
`evalReg x (fc(t, 2^{-k}).map ψ)` at all maps `ψ` at once are themselves a pathwise statement
about an infinite-dimensional Gaussian family. The cores below state the pathwise, uniform-over-a-
class form of the distortion estimate that SW's Lemmas 3.4–3.5 give after adding the base point to
the index set and applying the Borell–TIS inequality (SW [Bor75], [CIS76]) and Borel–Cantelli.

**Map classes.** A class is fixed by rational data, so the a.s. statements are countable
intersections. Boundary: `ψ` holomorphic on the open `ρ`-thickening of `[a,b] ⊂ ℂ`, bounded by
`M` there, real and strictly increasing on `[a,b]`, `‖ψ'‖ ≥ m` on `[a,b]` (Cauchy's estimates give
uniform `C^n` bounds on the `ρ/2`-thickening; this plays the role of SW's normalized family `Λ*`
with de Branges/Koebe bounds (3.18)–(3.19)). Area: `ψ` holomorphic and injective on the
`ρ`-thickening of a closed rational rectangle `K = [a,b] × [c,d]` (`c > 0`), bounded by `M`,
`Im ψ ≥ ρ` there, `‖ψ'‖ ≥ m` on `K`.

**Cores** (field-only, free field, a.s., all maps of a class at once):
* `BdryDistClassStmt` — boundary distortion, uniform over the class and over `t ∈ [a,b]`;
* `AreaDistClassStmt` — area distortion, uniform over the class and over `z ∈ K`;
together with the field-only window statements already in the repository
(`F1.BdryWindowStmt` via `F1.SWBdryWindowSplitStmt`; `E6.FreeWindowStmt` via
`E6.SWWindowSplitStmt`).

**Uniform transport forms** (consumer-facing, derived from the cores and the windows by the
deterministic change of variables of `BdryAllMapsMain.lean`, made uniform over the class):
* `BdryTransportUnifStmt`, `AreaTransportUnifStmt`.

No proofs here: this file only fixes the statements (see `handoff/SW-CORE.md` for the tasks).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

/-! ## Map classes -/

/-- The real segment `[a,b]` as a subset of `ℂ`. -/
def segC (a b : ℝ) : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Icc a b

/-- **Boundary map class** `Λ_∂(a,b,ρ,M,m)`: holomorphic on the open `ρ`-thickening of `[a,b]`,
bounded by `M` there, real and strictly increasing on `[a,b]`, with `‖ψ'‖ ≥ m` on `[a,b]`. -/
def BdryClass (a b ρ M m : ℝ) : Set (ℂ → ℂ) :=
  {ψ | DifferentiableOn ℂ ψ (thickening ρ (segC a b)) ∧
    (∀ z ∈ thickening ρ (segC a b), ‖ψ z‖ ≤ M) ∧
    (∀ t ∈ Icc a b, (ψ t).im = 0) ∧
    StrictMonoOn (fun t : ℝ => (ψ t).re) (Icc a b) ∧
    ∀ t ∈ Icc a b, m ≤ ‖deriv ψ t‖}

/-- The closed rectangle `[a,b] × [c,d] ⊂ ℂ`. -/
def rectC (a b c d : ℝ) : Set ℂ := {z | z.re ∈ Icc a b ∧ z.im ∈ Icc c d}

/-- **Area map class** `Λ(K,ρ,M,m)`, `K = [a,b] × [c,d]`: holomorphic and injective on the open
`ρ`-thickening of `K`, bounded by `M` and with `Im ψ ≥ ρ` there, and `‖ψ'‖ ≥ m` on `K`. -/
def AreaClass (a b c d ρ M m : ℝ) : Set (ℂ → ℂ) :=
  {ψ | DifferentiableOn ℂ ψ (thickening ρ (rectC a b c d)) ∧
    InjOn ψ (thickening ρ (rectC a b c d)) ∧
    (∀ z ∈ thickening ρ (rectC a b c d), ‖ψ z‖ ≤ M ∧ ρ ≤ (ψ z).im) ∧
    ∀ z ∈ rectC a b c d, m ≤ ‖deriv ψ z‖}

/-! ## The two field cores -/

/-! ## Uniform transport (consumer-facing forms) -/

/-! ## Window splits with the normalization radius outside the test support

The window splits `E6.SWWindowSplitStmt`, `F1.SWBdryWindowSplitStmt` normalize by
`X(fc(0,1)) = 0`, which is not measurable w.r.t. the field outside the grid half-discs meeting
the unit semicircle (the exceptional strip `T_j` of `E6.SWWinMarkovStmt`). Normalizing at a
radius `R` with the test support inside `B(0, R−1)` removes the strip: the normalizing variable
is then outside-measurable for every grid disc of radius `< 1`, so it only shifts the harmonic
part (SW's Markov step before (3.8), p. 13, and p. 18 for the boundary). The consumers (a.s.
window limits, `E6.FreeWindowStmt`, `F1.BdryWindowStmt`) are invariant under additive constants,
so this is a change of the proof node only (decision proposed in `handoff/SW-CORE.md`). -/

open E6 VagueH in
/-- `E6.SWWindowSplitStmt` with normalization `X(fc(0,R)) = 0` and `tsupport φ ⊆ B(0,R−1)`. -/
def SWWindowSplitStmtR (γ : ℝ) (c c' : ℕ → ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ R : ℕ, 2 ≤ R →
    (∀ ω, X ω (foldedCircle 0 R) = 0) →
    ∀ N : ℕ, 1 ≤ N → ∀ φ : ℂ → ℝ, IsTestH φ → (∀ w, 0 ≤ φ w) →
      tsupport φ ⊆ ball (0 : ℂ) ((R : ℝ) - 1) →
      WinSplit P (fun j ω => ENNReal.ofReal (c N) *
          ∫⁻ w in H, supWin γ (X ω) N j w * ENNReal.ofReal (φ w))
          (fun j ω => winRef γ (X ω) N j φ) ∧
      WinSplit P (fun j ω => ENNReal.ofReal (c' N) *
          ∫⁻ w in H, infWin γ (X ω) N j w * ENNReal.ofReal (φ w))
          (fun j ω => winRef γ (X ω) N j φ)

open E6 F1 in
/-- `F1.SWBdryWindowSplitStmt` with normalization `X(fc(0,R)) = 0` and
`tsupport φ ⊆ (−(R−1), R−1)`. -/
def SWBdryWindowSplitStmtR (γ : ℝ) (c c' : ℕ → ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ R : ℕ, 2 ≤ R →
    (∀ ω, X ω (foldedCircle 0 R) = 0) →
    ∀ N : ℕ, 1 ≤ N → ∀ φ : ℝ → ℝ, Continuous φ → HasCompactSupport φ → (∀ u, 0 ≤ φ u) →
      tsupport φ ⊆ Ioo (-((R : ℝ) - 1)) ((R : ℝ) - 1) →
      WinSplit P (fun j ω => bWinInt (c N) (bSupWin γ (X ω) N j) φ)
          (fun j ω => bWinRef γ (X ω) N j φ) ∧
      WinSplit P (fun j ω => bWinInt (c' N) (bInfWin γ (X ω) N j) φ)
          (fun j ω => bWinRef γ (X ω) N j φ)

end SWCore
end QuantumZipper
