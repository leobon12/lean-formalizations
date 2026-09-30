import QuantumZipper.Proofs.Zipper.AreaVarWin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# W-A-var (3): the sandwich — SW Cor. 3.2 from the window measures of SW Thm 1.1

Source: S. Sheffield, M. Wang, arXiv:1605.06171 (literature/1605.06171.pdf).
* **Proof of Theorem 1.1, p. 9**: for each `N`, a.s. the measures
  `C(N) sup_{ε ∈ window} e^{h̄_ε(z)} dz` and `C̲(N) inf_{ε ∈ window} e^{h̄_ε(z)} dz` converge weakly
  to `μ` (display "the measures `μ̄_{k,N}` converge weakly to `μ`"), and `C(N), C̲(N) → 1`
  ("The monotone convergence theorem implies that both `C(N)` and `C̲(N)` converge to 1").
* **Corollary 3.2, p. 11** ("Using a similar argument"): the approximations at the spatially
  varying scale `ε g(z)` converge to the same `μ`.

Here: the open node **`WedgeWindowStmt`** is exactly the p. 9 display for the unscaled wedge
field (circle averages, `ℍ`, test functions compactly supported in `ℍ`, integrals in `ℝ≥0∞`;
windows of two lattice steps, see `AreaVarWin.lean`), and the deterministic sandwich
`varScaleLimit_of_window` proves the circle-average Cor. 3.2 for **all** continuous positive
scale functions at once from it: a partition of unity subordinate to the sets where `s` is within
a factor `2^{2/N}` of a lattice point puts `2^{-k} s(w)` inside one window on each piece, so the
variable-scale density lies between `infWin` and `supWin` there. Hence
`wedgeVarScaleStmt_of_window` and **`wedgeAreaVarStmt_of_window`** (W-A-var from the SW window
node). The localization and the `ε`-bookkeeping are own work (SW give no details for Cor. 3.2).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

/-- **SW Thm 1.1 window convergence (p. 9)** for one field `x`, with normalizing constants
`c N` (sup windows) and `c' N` (inf windows): tested against nonnegative test functions with
compact support in `ℍ`, the normalized window measures converge to the quantum area measure. -/
def WindowLimits (γ : ℝ) (x : FieldSample) (c c' : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ H →
    (∀ w, 0 ≤ φ w) →
    Tendsto (fun j => ENNReal.ofReal (c N) * ∫⁻ w in H, supWin γ x N j w * ENNReal.ofReal (φ w))
        atTop (𝓝 (ENNReal.ofReal (∫ w, φ w ∂(qAreaMeasure γ x)))) ∧
      Tendsto (fun j => ENNReal.ofReal (c' N) * ∫⁻ w in H, infWin γ x N j w * ENNReal.ofReal (φ w))
        atTop (𝓝 (ENNReal.ofReal (∫ w, φ w ∂(qAreaMeasure γ x))))

/-- **W-A-var-win** (open node; SW proof of Thm 1.1, p. 9, for the unscaled wedge field):
deterministic constants `c N, c' N → 1` such that a.s. the window limits hold. -/
def WedgeWindowStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ c c' : ℕ → ℝ, Tendsto c atTop (𝓝 1) ∧ Tendsto c' atTop (𝓝 1) ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P →
    ∀ᵐ ω ∂P, WindowLimits (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) c c'

/-- Test functions with compact support in `ℍ` are integrable for a measure finite on the
compact subsets of `ℍ`. -/
theorem integrable_of_areaTest {μ : Measure ℂ} (hμK : ∀ K, IsCompact K → K ⊆ H → μ K < ⊤)
    {ψ : ℂ → ℝ} (hψ : Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ H) : Integrable ψ μ := by
  obtain ⟨hc, hs, hH⟩ := hψ
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  have h1 : IntegrableOn ψ (tsupport ψ) μ :=
    Measure.integrableOn_of_bounded (hμK _ hs.isCompact hH).ne hc.aestronglyMeasurable
      (ae_of_all _ fun w => hC w)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport ψ)).1 h1

variable {γ : ℝ} {x : FieldSample} {c c' : ℕ → ℝ}

end QuantumZipper.E6
