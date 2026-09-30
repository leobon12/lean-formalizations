import QuantumZipper.Proofs.Thm18.G3ZqNodes
import QuantumZipper.Proofs.RS.TraceMain
import QuantumZipper.Proofs.Thm18.R18AreaNullRef

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (11): good Brownian paths

The fixed-path statements are proved for every **good** path `a`: continuous, with a simple-chord
trace, a continuous driving function starting at `0`, and radial limits of the inverse Loewner
maps (the SLE trace exists). Path properties like continuity are not measurable in the product
σ-algebra of `ℝ≥0 → ℝ`, so they cannot hold a.e. for the image law `P.map (pathOf B)`; they hold
a.s. **on the sample space** (`ae_goodPathF`), which is how the fixed-path statements are consumed
(`ae_of_ae_map`, then dominated convergence over `P`).

* `ae_goodPathF`: for a Brownian motion with a.s. simple-chord traces (Theorem 1.8 inputs), a.s.
  the path is good (trace existence: `RS.ae_sleTrace_good`, Rohde–Schramm Thm 3.6/5.1,
  Kemppainen Thm 5.2; as in `R18.ref_curveAreaNull`).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

/-- **Good path** (full form). -/
def G3ZqGoodPathF (γ : ℝ) (a : ℝ≥0 → ℝ) : Prop :=
  Continuous a ∧ IsSimpleChord (pathTrace (γ ^ 2) a) ∧
    Continuous (pathDrive (γ ^ 2) a) ∧ pathDrive (γ ^ 2) a 0 = 0 ∧
    (∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
      Tendsto (fun y : ℝ => fwdMapInv (pathDrive (γ ^ 2) a) t (y * Complex.I)) (𝓝[>] 0) (𝓝 p))

theorem G3ZqGoodPathF.good {γ : ℝ} {a : ℝ≥0 → ℝ} (h : G3ZqGoodPathF γ a) : G3ZqGoodPath γ a :=
  ⟨h.1, h.2.1⟩

/-- **A.s. the Brownian path is good.** -/
theorem ae_goodPathF {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hsc : ∀ᵐ ω ∂P, IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω))) :
    ∀ᵐ ω ∂P, G3ZqGoodPathF γ (pathOf B ω) := by
  have hκ : 0 < γ ^ 2 := by positivity
  obtain ⟨δ, hδ, hgood⟩ := RS.ae_sleTrace_good hB hκ (by nlinarith)
  filter_upwards [hgood, hB.cont, hB.eval_zero_ae_eq_zero, hsc] with ω hg hc h0 hs
  have hW : Continuous (drive (γ ^ 2) B ω) := drive_continuous hc
  have hW0 : drive (γ ^ 2) B ω 0 = 0 := drive_zero h0
  refine ⟨hc, hs, hW, hW0, fun t ht => ?_⟩
  obtain ⟨C, hC⟩ := hg.2.2 ⌈t⌉₊
  exact ⟨_, RS.tendsto_fwdMapInv_of_rpow_bound hδ (hC t ⟨ht, Nat.le_ceil t⟩)⟩

end G3Zq
end Thm18Asm
end QuantumZipper
