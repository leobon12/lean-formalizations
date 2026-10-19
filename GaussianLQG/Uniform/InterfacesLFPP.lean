import GaussianLQG.Uniform.Interfaces
import GaussianLQG.Core.Defs
import LQGMetric.LFPP.DistOn

/-!
# Interface of the LFPP-level Hölder moments (Phase B, orchestrator-owned)

The ledger statement U12 (`holder_moment_unif`, `blueprint/phaseB/uniform-ledger.tex`): uniform
moments of the 1/2-Hölder constant of the internal LFPP distance of the DDDF field `φ_{0,n}` on the
box `V_R = [-R-1, R+1]²`, over pairs in `V'_R = [-R, R]²`, normalized by `λ_n`. The packet proving
U12 exports a theorem implying it; the (★) packet (U15) takes it as a hypothesis meanwhile.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise
open scoped ENNReal

namespace GaussianLQG.Uniform

/-- `V'_R = [-R, R]²`. -/
def boxIn (R : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ |z.im| ≤ R}

/-- `V_R = [-R-1, R+1]²`. -/
def boxOut (R : ℝ) : Set ℂ := {z | |z.re| ≤ R + 1 ∧ |z.im| ≤ R + 1}

/-- U12 (ledger `holder_moment_unif`). -/
def IfaceHolderMomentU : Prop :=
  ∀ q : ℝ, 1 ≤ q → ∃ ξq : ℝ, 0 < ξq ∧ ∀ R : ℝ, 0 < R → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) ξq, ∀ n : ℕ,
        (∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
            (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) (boxOut R) z.1 z.2).toReal) (boxIn R) ^ q ∂P)
          ≤ C

end GaussianLQG.Uniform
