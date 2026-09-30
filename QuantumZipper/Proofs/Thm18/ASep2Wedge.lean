import QuantumZipper.Proofs.Thm18.ASep2Sing
import QuantumZipper.Proofs.Thm18.ASepWedgeCongr
import QuantumZipper.Proofs.Thm18.ASepTr1
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.Wire2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP2: the per-path A-sep statement for the wedge — profile done, canonical scale open

* `continuousOn_wedgeProfile_compl`: the wedge profile `-h_{|z|}(0) - Q log |z| + A(-log |z|)` is
  continuous on `ℂ \ {0}` (radial; `GoodRad` witness, continuous wedge process).
* **`ae_concl0_wedgeUnc` (D1 closed)**: for every good driver, almost surely in the wedge sample,
  the `τ' = 0` conclusion holds for the **uncanonical** wedge sample `ofFun prof_ω + X ω`
  (from `ae_concl0_prof`: the null set does not depend on the profile, so the profile may depend
  on `X ω`).
* `G4SepScale0Stmt` (remaining node, D2) and `g4SepPath0Stmt_of_scale`: the canonical
  representative `wedgeRep = rescale (ofFun prof + X) Q s_ω` (ASepWedgeCongr) has a random scale
  `s_ω` that depends on `X`; the dyadic regularization `evalReg` is not covariant under
  non-dyadic rescalings, so the fixed-scale results do not transfer. `G4SepScale0Stmt` asks for
  the free-field conclusion uniformly in the scale.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

open Thm18Asm Thm18Asm.G4Core

/-- The wedge profile is continuous off `0`. -/
theorem continuousOn_wedgeProfile_compl {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F) {A : ℝ → ℝ} (hA : Continuous A) (Q : ℝ) :
    ContinuousOn (WedgeCan.wedgeProfile x A Q) ({0}ᶜ : Set ℂ) := by
  have hne : ∀ z ∈ ({0}ᶜ : Set ℂ), z ≠ 0 := fun z hz => hz
  have hrad : ContinuousOn (fun z : ℂ => radAvgReg x ‖z‖) ({0}ᶜ : Set ℂ) :=
    ContinuousOn.congr (ContinuousOn.comp hG.1.1
        (continuousOn_const.prodMk continuous_norm.continuousOn)
        fun z hz => ⟨GaussTK.zero_mem_Hbar, norm_pos_iff.2 (hne z hz)⟩)
      fun z hz => hG.radAvgReg_eq (norm_pos_iff.2 (hne z hz))
  have hlogc : ContinuousOn (fun z : ℂ => -Real.log ‖z‖) ({0}ᶜ : Set ℂ) := fun z hz =>
    ((Real.continuousAt_log (norm_ne_zero_iff.2 (hne z hz))).comp
      continuous_norm.continuousAt).neg.continuousWithinAt
  have hAc : ContinuousOn (fun z : ℂ => A (-Real.log ‖z‖)) ({0}ᶜ : Set ℂ) :=
    hA.comp_continuousOn hlogc
  unfold WedgeCan.wedgeProfile
  exact (hrad.neg.add (continuousOn_const.mul hlogc)).add hAc

/-- **Remaining node (D2): the free-field conclusion uniformly in the scale.** For a free field
and a good driver, almost surely, for every scale `s > 0` and every profile continuous off `0`,
the `τ' = 0` conclusion holds for the rescaled field `rescale (ofFun g + X ω) Q s`. -/
def G4SepScale0Stmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → FieldSample), IsFreeGFFModConstH X P →
      ∀ W : ℝ → ℝ, DrvGood W → ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ g : ℂ → ℝ,
        ContinuousOn g {0}ᶜ → G4SepConcl0 γ (rescale (ofFun g + X ω) (Qc γ) s, W)

/-- **The per-path statement from the uniform-scale node.** -/
theorem g4SepPath0Stmt_of_scale (h : G4SepScale0Stmt) : G4SepPath0Stmt := by
  intro γ hγ hγ2 Ω' _ P' _ X A hX hA hXA W hWg
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [ae_concl0_wedgeRep_iff γ hX hA hXA, h γ hγ hγ2 P' X hX W hWg, hG.ae_good,
    WedgeCan4.ae_continuous_wedgeProcess hA,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (alpha_lt_Qc hγ hγ2) hX hA hXA] with ω h1 h2 h3 h4 h5
  rw [h1 W]
  exact h2 _ h5.1 _ (continuousOn_wedgeProfile_compl h3 h4 _)

end ASep
end QuantumZipper
