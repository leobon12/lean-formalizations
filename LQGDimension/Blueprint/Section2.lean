import LQGDimension.Blueprint.Gaussian

/-!
# Blueprint: Section 2 (the Gaussian variational problem)

Proof obligations for the first assertion of Theorem 1.1, discharged in
`LQGDimension/Section2/`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real

namespace LQGDimension.Blueprint

/-- The covariance (1.2) is positive semidefinite on every finite family of functions that are
integrable on `[0,1]` (it is `2π` times the Gram kernel of the signed indicators `A_f` in
`L²((0,1) × ℝ)`). -/
def ZCovPSD : Prop :=
  ∀ F : Finset (ℝ → ℝ), (∀ f ∈ F, IntervalIntegrable f volume 0 1) → PSDOn F zCov

/-- Lemma 2.1, finiteness: `a_1 < ∞`.  (With `ASubadditiveE`, this gives `a_n ≤ n a_1 < ∞`.) -/
def AOneFinite : Prop :=
  aE 1 ≠ ⊤

/-- Lemma 2.1, subadditivity: `a_{n+m} ≤ a_n + a_m` (in `EReal`). -/
def ASubadditiveE : Prop :=
  ∀ n m : ℕ, aE (n + m) ≤ aE n + aE m

/-- Lemma 2.2: `a_n ≥ 3 · 2^{-13/3} n`. -/
def ALinearLowerBound : Prop :=
  ∀ n : ℕ, (((3 * (2 : ℝ) ^ (-13 / 3 : ℝ)) * n : ℝ) : EReal) ≤ aE n

end LQGDimension.Blueprint
