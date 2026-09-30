import QuantumZipper.Proofs.Thm18.G2DisintXC
import QuantumZipper.Proofs.Thm18.G2ClipReduce

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `x` side: the rooted integral as an integral against the root kernel

For the bump coefficient `α` and `h₀ = g2Y φ α`: almost surely the root kernel `κ_M(h₀)` is
`ν_h|_M`, so a rooted integral of an event supported on margin roots is
`E ∫ H(h₀, x, α) κ_M(h₀)(dx)` (`g2x_root_eq`), and the root kernel has finite total expected mass
(`g2x_kernel_mass_lt_top`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The margin root kernel. -/
def g2xκM (γ : ℝ) (i : G3Idx) (m : ℝ) : Kernel (AdmIdx → ℝ) ℝ :=
  g2FinKer (g2ν₀ γ (g2xφ i m)) (measurable_g2ν₀ _ _) (measurableSet_g2xM i m)

instance g2xκM_sfinite (γ : ℝ) (i : G3Idx) (m : ℝ) : IsSFiniteKernel (g2xκM γ i m) := by
  unfold g2xκM; infer_instance

/-- **The pointwise identifications hold almost surely.** -/
theorem g2x_ae_pw {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (α : Ω₀ → ℝ) :
    ∀ᵐ ω ∂gffBase.P,
      (∀ x ∈ g2xM i m, (g2Y (g2xφ i m) α ω, x) ∈ g2xGood γ i m) ∧
      g2xκM γ i m (g2Y (g2xφ i m) α ω) = (g3Hν γ ω).restrict (g2xM i m) ∧
      (∀ x ∈ g2xM i m, g2xf γ i m (g2Y (g2xφ i m) α ω, x) (α ω) = (g3Hν γ ω (Icc x 0)).toReal) ∧
      (∀ κ : ℝ, 0 ≤ κ → κ < g2xR i m → ∀ x ∈ g2xM i m,
        (g3Hν γ ω (Icc (x + κ) 0)).toReal =
          g2xf γ i m (g2Y (g2xφ i m) α ω, x) (α ω) - g2xgap γ i m κ (g2Y (g2xφ i m) α ω, x)) ∧
      g3Hν γ ω (Icc (-i.δ) 0) < ⊤ := by
  filter_upwards [g2x_ae_ident hγ hγ2 i hm α] with ω ⟨hA, hB, hW, hJ⟩
  obtain ⟨h1, h2, h3, h4⟩ := g2x_pw hγ i hm (g2Y (g2xφ i m) α ω) hA hB hW hJ
  exact ⟨h1, h2, h3, h4, hW⟩

/-- **A rooted integral over margin roots is a root-kernel integral.** -/
theorem g2x_root_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (α : Ω₀ → ℝ) (T : Set (Ω₀ × ℝ × ℝ)) (H : (AdmIdx → ℝ) × ℝ × ℝ → ℝ≥0∞)
    (hT : ∀ᵐ ω ∂gffBase.P, (∀ x ∈ g2xM i m, (g2Y (g2xφ i m) α ω, x) ∈ g2xGood γ i m) →
      g2xκM γ i m (g2Y (g2xφ i m) α ω) = (g3Hν γ ω).restrict (g2xM i m) →
      (∀ x ∈ g2xM i m, g2xf γ i m (g2Y (g2xφ i m) α ω, x) (α ω) =
        (g3Hν γ ω (Icc x 0)).toReal) →
      (∀ κ : ℝ, 0 ≤ κ → κ < g2xR i m → ∀ x ∈ g2xM i m,
        (g3Hν γ ω (Icc (x + κ) 0)).toReal =
          g2xf γ i m (g2Y (g2xφ i m) α ω, x) (α ω) - g2xgap γ i m κ (g2Y (g2xφ i m) α ω, x)) →
      ∀ x ∈ Icc (-i.δ) 0, T.indicator 1 (ω, (g3Hν γ ω (Icc x 0)).toReal, x) =
        (g2xM i m).indicator (fun x => H (g2Y (g2xφ i m) α ω, x, α ω)) x) :
    g3RootInt γ i (T.indicator 1) =
      ∫⁻ ω, ∫⁻ x, H (g2Y (g2xφ i m) α ω, x, α ω) ∂(g2xκM γ i m (g2Y (g2xφ i m) α ω))
        ∂gffBase.P := by
  unfold g3RootInt
  refine lintegral_congr_ae ?_
  filter_upwards [g2x_ae_pw hγ hγ2 i hm α, hT] with ω ⟨h1, h2, h3, h4, _⟩ hTω
  rw [setLIntegral_congr_fun measurableSet_Icc (hTω h1 h2 h3 h4),
    lintegral_indicator (measurableSet_g2xM i m), Measure.restrict_restrict (measurableSet_g2xM i m),
    inter_eq_left.2 (fun x hx => hx.2), h2]

end Thm18Asm
end QuantumZipper
