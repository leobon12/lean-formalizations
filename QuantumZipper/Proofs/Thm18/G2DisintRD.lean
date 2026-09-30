import QuantumZipper.Proofs.Thm18.G2DisintRC
import QuantumZipper.Proofs.Thm18.G2DisintXD

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `R` side: the rooted integral as an integral against the root kernel

For the bump coefficient `α` and `h₀ = g2Y φ α`: almost surely the root kernel `κ_M(h₀)` is
`ν_h|_M`, so a rooted integral of an event supported on margin roots is
`E ∫ H(h₀, x, α) κ_M(h₀)(dx)` (`g2r_root_eq`), and the root kernel has finite total expected mass
(`g2r_kernel_mass_lt_top`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The margin root kernel. -/
def g2rκM (γ : ℝ) (i : G3Idx) (m : ℝ) : Kernel (AdmIdx → ℝ) ℝ :=
  g2FinKer (g2ν₀ γ (g2rφ i m)) (measurable_g2ν₀ _ _) (measurableSet_g2rM i m)

instance g2rκM_sfinite (γ : ℝ) (i : G3Idx) (m : ℝ) : IsSFiniteKernel (g2rκM γ i m) := by
  unfold g2rκM; infer_instance

/-- **The pointwise identifications hold almost surely.** -/
theorem g2r_ae_pw {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (α : Ω₀ → ℝ) :
    ∀ᵐ ω ∂gffBase.P,
      (∀ x ∈ g2rM i m, (g2Y (g2rφ i m) α ω, x) ∈ g2rGood γ i m) ∧
      g2rκM γ i m (g2Y (g2rφ i m) α ω) = (g3Hν γ ω).restrict (g2rM i m) ∧
      (∀ x ∈ g2rM i m, g2rf γ i m (g2Y (g2rφ i m) α ω, x) (α ω) = (g3Hν γ ω (Icc 0 x)).toReal) ∧
      (∀ κ : ℝ, 0 ≤ κ → κ < g2rR i m → ∀ x ∈ g2rM i m,
        (g3Hν γ ω (Icc 0 (x - κ))).toReal =
          g2rf γ i m (g2Y (g2rφ i m) α ω, x) (α ω) - g2rgap γ i m κ (g2Y (g2rφ i m) α ω, x)) ∧
      g3Hν γ ω (Icc 0 (g2rW i m)) < ⊤ := by
  filter_upwards [g2r_ae_ident hγ hγ2 i hm α] with ω ⟨hA, hB, hW, hJ⟩
  obtain ⟨h1, h2, h3, h4⟩ := g2r_pw hγ i hm (g2Y (g2rφ i m) α ω) hA hB hW hJ
  exact ⟨h1, h2, h3, h4, hW⟩

/-- **A rooted integral over margin roots is a root-kernel integral.** -/
theorem g2r_root_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (α : Ω₀ → ℝ) (T : Set (Ω₀ × ℝ × ℝ)) (H : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞)
    (hT : ∀ᵐ ω ∂gffBase.P, (∀ x ∈ g2rM i m, (g2Y (g2rφ i m) α ω, x) ∈ g2rGood γ i m) →
      g2rκM γ i m (g2Y (g2rφ i m) α ω) = (g3Hν γ ω).restrict (g2rM i m) →
      (∀ x ∈ g2rM i m, g2rf γ i m (g2Y (g2rφ i m) α ω, x) (α ω) =
        (g3Hν γ ω (Icc 0 x)).toReal) →
      (∀ κ : ℝ, 0 ≤ κ → κ < g2rR i m → ∀ x ∈ g2rM i m,
        (g3Hν γ ω (Icc 0 (x - κ))).toReal =
          g2rf γ i m (g2Y (g2rφ i m) α ω, x) (α ω) - g2rgap γ i m κ (g2Y (g2rφ i m) α ω, x)) →
      ∀ x ∈ Icc 0 (i.t₂ + i.r₂), T.indicator 1 (ω, (g3Hν γ ω (Icc 0 x)).toReal, x) =
        (g2rM i m).indicator (fun x => H (g2Y (g2rφ i m) α ω, x, α ω)) x) :
    g3RootIntR γ i (T.indicator 1) =
      ∫⁻ ω, ∫⁻ x, H (g2Y (g2rφ i m) α ω, x, α ω) ∂(g2rκM γ i m (g2Y (g2rφ i m) α ω))
        ∂gffBase.P := by
  unfold g3RootIntR
  refine lintegral_congr_ae ?_
  filter_upwards [g2r_ae_pw hγ hγ2 i hm α, hT] with ω ⟨h1, h2, h3, h4, _⟩ hTω
  rw [setLIntegral_congr_fun measurableSet_Icc (hTω h1 h2 h3 h4),
    lintegral_indicator (measurableSet_g2rM i m), Measure.restrict_restrict (measurableSet_g2rM i m),
    inter_eq_left.2 (fun x hx => hx.2), h2]

end Thm18Asm
end QuantumZipper
