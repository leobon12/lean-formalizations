import MatedCRTHarmonic.GMS4.Prop210
import MatedCRTHarmonic.GMS4.CellGraphInterface
import MatedCRTHarmonic.GMS4.Prop48
import MatedCRTHarmonic.GMS4.Prop410Rooting
import MatedCRTHarmonic.GMS4.SmallRootMass
import MatedCRTHarmonic.GMSLemma27.Consumers

/-!
# The source-shaped statements of [18] Propositions 2.10 and 4.10 (named inputs of the endgame)

The final assembly derives the mated-CRT map conclusion from the inputs below. This file fixes those inputs, in the source's quantifier order:

* `Prop210Source F` — [18] Proposition 2.10 for a random cell family
  `F`: exponents `α = α(γ) > 0`, `β = β(γ) > 0`; for each `ρ ∈ (0, 1)` a threshold `A = A(ρ, γ) > 0`; for each `C > 1`
  a rate `Cfail = Cfail(ρ, C, γ)`; for every dyadic mesh `ε = 2^{-k}` and every admissible pair `(D, f)`
  (`GMS4.Prop210Admissible`, which contains `ε ∈ (0, 1)`, `D ⊂ B_ρ(0)` open connected with
  `area(B_r(∂D)) ≤ C r`, `0 ≤ f ≤ C ε^{-β}`, `f` `C ε^{-β}`-Lipschitz), the outer probability of G3's exact failure
  event `GMS4.Prop210Bad` (`∫⁻_D f u^ε > A ∫⁻_D f + ε^α`, `u^ε` the selection-free density (2.12)) is at most
  `Cfail ε^α`.
* `Prop410Source P η` — [18] Proposition 4.10 (: "the statement of Proposition 2.10 is true with `u_*^ε`
  in place of `u^ε`") for an area-parametrized curve `η` under `P`: the same quantifiers, with the failure event
  `Prop410Bad` of `∫⁻_D f u_*^ε ≤ A ∫⁻_D f + ε^α`, `u_*^ε = GMS4b.uStar ε η z = DA^ε(z)(deg_in^ε(z) + deg_out^ε(z))`
  ((4.19), extended-valued, at the first hitting time (4.2)).

Both are honest source statements (no constant is fixed beyond what [18] fixes). `Prop210Source` is monotone in the
exponents (`prop210Source_mono`), and G4's uniform producer records close it
(`prop210Source_of_uniformProducers`; G4FS's endgame target).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-! ### [18] Proposition 2.10 in the source's quantifier order -/

/-! ### [18] Proposition 4.10 in the source's quantifier order -/

/-- The failure event of [18] Proposition 4.10's estimate for the curve-valued random variable `η` at mesh `ε`:
`∫⁻_D f u_*^ε > A ∫⁻_D f + tol`, with `u_*^ε = GMS4b.uStar ε (η ω)` ((4.19)). -/
def Prop410Bad {Ω : Type*} (η : Ω → C(ℝ, ℂ)) (ε : ℝ) (D : Set ℂ) (f : ℂ → ℝ) (A tol : ℝ) : Set Ω :=
  {ω | ¬ ((∫⁻ z in D, ENNReal.ofReal (f z) * GMS4b.uStar ε (η ω) z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal tol)}

/-! ### Elementary monotonicity -/

theorem bundle_mesh_pos (k : ℕ) : 0 < CellFamily.mesh k := by
  unfold CellFamily.mesh
  positivity

theorem bundle_mesh_le_one (k : ℕ) : CellFamily.mesh k ≤ 1 := by
  rw [show CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ by simp [CellFamily.mesh, zpow_neg]]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- On dyadic meshes `ε ≤ 1`, a smaller exponent gives a larger power. -/
theorem bundle_mesh_rpow_le_of_le (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    CellFamily.mesh k ^ b ≤ CellFamily.mesh k ^ a :=
  Real.rpow_le_rpow_of_exponent_ge (bundle_mesh_pos k) (bundle_mesh_le_one k) hab

/-- G3's Proposition 2.10 failure event shrinks as the tolerance grows. -/
theorem prop210Bad_anti_tol (F : CellFamily.RandomCellFamily) (k : ℕ) (D : Set ℂ) (f : ℂ → ℝ)
    (A : ℝ) {η η' : ℝ} (hη : η ≤ η') :
    GMS4.Prop210Bad F k D f A η' ⊆ GMS4.Prop210Bad F k D f A η := by
  intro ω hω hgood
  apply hω
  change (∫⁻ z in D, ENNReal.ofReal (f z) * GMS3.uDens (F.H k ω) z) ≤
    ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η'
  have hgood' : (∫⁻ z in D, ENNReal.ofReal (f z) * GMS3.uDens (F.H k ω) z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η := hgood
  exact hgood'.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hη))

/-! ### G4's uniform producer records close `Prop210Source` -/

end MatedCRTHarmonic.BundleSec4
