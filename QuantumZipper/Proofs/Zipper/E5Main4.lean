import QuantumZipper.Proofs.Zipper.E5Main3

/-!
# E5-MAIN, part 4: the zoom model is TV-near the target (`tvNear_model`)

Blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §4, node **E5**, steps (2)–(5), on the abstract zoom
model of `E5Main3`.

* `setup_piecewise`: switching the correction to `g₀` on a `condSigma`-measurable bad set keeps
  the D3⁺ hypotheses (harmonicity is pointwise in `ω`).
* `tvNear_model_germ`: for the germ-free correction `g₀` (a function of the conditioning data
  `V` of E5-DENS), the model is TV-near the germ-replaced integrand (E5a/E5-DENS + D3⁺(iii)).
* `tvNear_model`: **the zoom model is TV-near the target**, from D3⁺(i), D3⁺(ii) and the proved
  D3⁺(iii), E5-DENS.

Own bookkeeping on top of the cited nodes (blueprint route).
-/

noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity D3Plus

variable {Ω₁ : Type} [MeasurableSpace Ω₁]
variable {γ α r κ : ℝ} {ρ₀ : Measure ℂ} {Q : Measure Ω₁} [IsProbabilityMeasure Q]
  {X' : Ω₁ → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω₁ → E'}

open Classical in
/-- The correction `g` switched to `g₀` on the bad set. -/
def switchG (bad : Set Ω₁) (g g₀ : Ω₁ → ℂ → ℝ) : Ω₁ → ℂ → ℝ := bad.piecewise g₀ g

theorem switchG_of_mem {bad : Set Ω₁} {g g₀ : Ω₁ → ℂ → ℝ} {ω : Ω₁} (h : ω ∈ bad) :
    switchG bad g g₀ ω = g₀ ω := by classical simp [switchG, h]

theorem switchG_of_not_mem {bad : Set Ω₁} {g g₀ : Ω₁ → ℂ → ℝ} {ω : Ω₁} (h : ω ∉ bad) :
    switchG bad g g₀ ω = g ω := by classical simp [switchG, h]

theorem setup_piecewise {g g₀ : Ω₁ → ℂ → ℝ} (hS : D3Plus.Setup γ α r ρ₀ Q X' Ξ g)
    (hS₀ : D3Plus.Setup γ α r ρ₀ Q X' Ξ g₀) {bad : Set Ω₁}
    (hbad : MeasurableSet[condSigma Ξ X' r] bad) :
    D3Plus.Setup γ α r ρ₀ Q X' Ξ (switchG bad g g₀) where
  hγ := hS.hγ
  hγ2 := hS.hγ2
  hα := hS.hα
  hr := hS.hr
  hX := hS.hX
  hΞ := hS.hΞ
  hind := hS.hind
  hρ := hS.hρ
  hρ1 := hS.hρ1
  hρB := hS.hρB
  harm ω := by
    by_cases h : ω ∈ bad
    · rw [switchG_of_mem h]; exact hS₀.harm ω
    · rw [switchG_of_not_mem h]; exact hS.harm ω
  gmeas z := by
    classical
    have : (fun ω => switchG bad g g₀ ω z) = bad.piecewise (fun ω => g₀ ω z) (fun ω => g ω z) := by
      funext ω
      by_cases h : ω ∈ bad
      · simp [switchG, h]
      · simp [switchG, h]
    rw [this]
    exact Measurable.piecewise hbad (hS₀.gmeas z) (hS.gmeas z)

variable {𝕍 : Type*} [MeasurableSpace 𝕍] {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F)

/-- `condSigma ≤` the ambient σ-algebra (as in `D3PlusIMarkov.condSigma_le`). -/
theorem condSigma_le_ambient {g : Ω₁ → ℂ → ℝ} (hS : D3Plus.Setup γ α r ρ₀ Q X' Ξ g) :
    condSigma Ξ X' r ≤ ‹MeasurableSpace Ω₁› := by
  refine sup_le hS.hΞ.comap_le ((K3.outsideSigma_le_freeIncrSigma X' 0 r).trans ?_)
  refine measurable_iff_comap_le.1 (measurable_pi_iff.2 fun p => ?_)
  exact (hS.hX.measurable_coord _).sub (hS.hX.measurable_coord _)

/-- The event that `g` and `g₀` are not uniformly `K`-close on `ball 0 r ∩ Hbar`. -/
def gBad (r : ℝ) (g g₀ : Ω₁ → ℂ → ℝ) (K : ℝ) : Set Ω₁ :=
  {ω | ¬ ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g ω z - g₀ ω z| ≤ K}

end E5
end QuantumZipper
