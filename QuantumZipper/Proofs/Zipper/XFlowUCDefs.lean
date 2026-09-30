import QuantumZipper.Proofs.Zipper.XFlowRC3Phi

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# XFLOW-UC: definitions and the two nodes of the five-parameter uniform convergence

`F1.XFlowUCStmt` asks that, a.s., `Φ_j(p) = ∫ avgReg x_u j dν_p` converge locally uniformly on
`flowPar` (`p = (u, s, d, r)`, `ν_p = (R_{u,s})_* fc(d, r)`, `x = X + α₀(−log|·|)`). Since
`x = y − √κ log|·|` with the `Γ⁰` field `y = 𝔥₀ + X`, the pairing splits (pathwise, on one full
event, `XFlowUCSplit.lean`) as

`Φ_j(p) = Φ^y_j(p) − √κ · L_j(p)`, `L_j(p) = ∫∫ log|f_u⁻¹| dfc(w, 2^{-j}) dν_p(w)`,

so `XFlowUCStmt` reduces to

* `XFlowGamUCQStmt`: the `Γ⁰` pairings `Φ^y_j` are a.s. uniformly Cauchy at the rational points
  of every box `flowBox m` (the five-parameter form of the D33 node `RegUnif.UnifUCStmt`;
  Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I,
  Thm (2.1));
* `XFlowLogUCStmt`: the purely deterministic uniform convergence of `L_j` on every box (the
  analogue of `RegUnif.DetUnifStmt` for `log|f_u⁻¹|`, with the circle parameters added).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open RegUnif

/-- The compact boxes exhausting `flowPar`: `u, s ∈ [0, m+1]`, `Re d ∈ [−(m+1), m+1]`,
`Im d ∈ [0, m+1]`, `r ∈ [1/(m+2), m+2]`. -/
def flowBox (m : ℕ) : Set (ℝ × ℝ × ℂ × ℝ) :=
  {p | p.1 ∈ Icc 0 ((m : ℝ) + 1) ∧ p.2.1 ∈ Icc 0 ((m : ℝ) + 1) ∧
    p.2.2.1.re ∈ Icc (-((m : ℝ) + 1)) ((m : ℝ) + 1) ∧ p.2.2.1.im ∈ Icc 0 ((m : ℝ) + 1) ∧
    p.2.2.2 ∈ Icc (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2)}

/-- The real point of a rational parameter `(u, s, Re d, Im d, r) ∈ ℚ⁵`. -/
def flowQ (q : ℚ × ℚ × ℚ × ℚ × ℚ) : ℝ × ℝ × ℂ × ℝ :=
  ((q.1 : ℝ), (q.2.1 : ℝ), ⟨(q.2.2.1 : ℝ), (q.2.2.2.1 : ℝ)⟩, (q.2.2.2.2 : ℝ))

/-- The `Γ⁰` pairings `Φ^y_j(p) = ∫ avgReg y_u j dν_p`, `y = 𝔥₀ + x` (the D33 `PhiW` with the
circle parameters free). -/
def flowPhiY (κ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (j : ℕ) (p : ℝ × ℝ × ℂ × ℝ) : ℝ :=
  ∫ z, avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) p.1) j z ∂flowNu W p

/-- The log part `L_j(p) = ∫ (∫ log|f_u⁻¹| dfc(w, 2^{-j})) dν_p(w)`. -/
def flowLogJ (W : ℝ → ℝ) (j : ℕ) (p : ℝ × ℝ × ℂ × ℝ) : ℝ :=
  ∫ w, (∫ v, Real.log ‖fwdMapInv W p.1 v‖ ∂foldedCircle w (radius j)) ∂flowNu W p

/-- **(Γ⁰ node, five parameters.)** A.s., on every box, the `Γ⁰` pairings are uniformly Cauchy
at the rational points of the box. -/
def XFlowGamUCQStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ m : ℕ, ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ j' : ℕ, N ≤ j' →
      ∀ q : ℚ × ℚ × ℚ × ℚ × ℚ, flowQ q ∈ flowBox m →
        |flowPhiY κ (X ω) (drive κ B ω) j (flowQ q) - flowPhiY κ (X ω) (drive κ B ω) j' (flowQ q)|
          ≤ 1 / ((n : ℝ) + 1)

/-- **(Deterministic log node.)** For a continuous driver with `W 0 = 0`, `L_j` converges to
`∫ log|f_u⁻¹| dν_p` uniformly on every box. -/
def XFlowLogUCStmt : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ m : ℕ,
    TendstoUniformlyOn (fun j p => flowLogJ W j p)
      (fun p => ∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂flowNu W p) atTop (flowBox m)

end F1
end QuantumZipper
