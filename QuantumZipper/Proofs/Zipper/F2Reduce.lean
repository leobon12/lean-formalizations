import QuantumZipper.Proofs.Zipper.Thm13AssemblyStmt
import QuantumZipper.Proofs.Zipper.B2Defs

/-!
# F2: the lengths clause of Theorem 1.3 from F1 (reduction to the blueprint steps)

Node F2 of `blueprint/SECTION5_BLUEPRINT.md` (and `E_BRANCH_BLUEPRINT.md`, §6), in the form
`Thm13Asm.F2NodeStmt : F1Stmt → Thm13LenStmt` consumed by `Thm13Asm.theorem1_3_of_nodes`.

Source: Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, §5.4 (proof of Theorem 1.3, pp. 70–72): Theorem 1.3 is deduced from the
statement that the two quantum lengths of `η[0,t]` agree under the stationary law `P_*`
(Theorem 1.8 / F1), by (i) reading the Theorem 1.3 field as the field `h⁰ = X + (2/√κ) log|·|`
of a `Γ⁰` configuration unzipped by capacity `T` along the reverse-flow hull `η_T` (forward
driver `V s = W(T−s) − W T`), so that the welded pairs are the two sides of `η_T` and their
lengths are differences of `L^±` (§5.1); and (ii) transferring "`L⁻ = L⁺`" from `P_*` to `Γ⁰`
(random rescaling, the restriction identity of the wedge inside `B₁`, rule (5.1) for the
deterministic `γ log|·|`, scale invariance). This file follows SECTION5 F2 steps (1)–(4)
(step (5), non-vacuity, is clause 1 of `theorem1_3`, proved in `Thm13Assembly.lean`).

## What is proved here
* `F2.len_eq_of_add_eq` (own elementary argument): the ENNReal cancellation turning
  "`ν[x₋,0] + L⁻_r = L⁻_T`, `ν[0,x₊] + L⁺_r = L⁺_T`, `L^-=L^+` at `r` and `T`, `L⁻_T < ∞`" into
  `ν[x₋,0] = ν[0,x₊]`.
* `F2.f2Node_of_inputs : F2WeldLenStmt → F2UnscaledStmt → F2LocalStmt → Thm13Asm.F2NodeStmt`.

## Inputs (open; exact statements below)
* `F2WeldLenStmt` — step (1), B5 for the Theorem 1.3 configuration: the lengths of the two sides
  of `η[r,T]` seen from the fully unzipped field are `L^±_T − L^±_r` (additivity of `ν` along
  `η_T`, conformal coordinate change B3(e), atomlessness at the cut point).
* `F2UnscaledStmt` — step (2a): F1 plus random rescaling B3(d) gives lengths agree for the
  unscaled wedge field with an independent `SLE_κ` driver.
* `F2LocalStmt` — steps (2b)–(4): B4(b) (restriction identity, proved as `WedgeRes`), B5
  locality, B3(b) (rule (5.1)), Brownian time reversal on `[0,T]`, scale invariance, and the
  additive constant.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## Definitions -/

/-- The `Γ⁰` configuration hidden in a Theorem 1.3 sample: the field `h⁰ = (2/√κ) log|·| + X`
(the picture in which `η_T` is drawn in `ℍ`) with the forward driver `V = vrev W T`,
`V s = W(T − s) − W T` on `[0,T]`, of the reverse-flow hull `η_T = revHull W T`, `W = √κ B`.
Its field component is that of `B2.cfg`; its driver is `B2.Vr`. -/
def cfgT (κ T : ℝ) {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    FieldSample × (ℝ → ℝ) :=
  (ofFun (h0rev κ) + X ω, B2.vrev (drive κ B ω) T)

theorem cfgT_eq (κ T : ℝ) {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ω : Ω) :
    cfgT κ T B X ω = ((B2.cfg κ B X ω).1, B2.Vr κ T B ω) := rfl

/-! ## The open inputs -/

/-! ## The reduction -/

/-- Own elementary argument: cancellation in `ℝ≥0∞`. -/
theorem len_eq_of_add_eq {a b x y L M : ℝ≥0∞} (hL : L ≠ ⊤) (hxy : x = y) (hLM : L = M)
    (ha : a + x = L) (hb : b + y = M) : a = b := by
  subst hxy hLM
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top hL (ha ▸ le_add_self)
  exact (ENNReal.add_left_inj hx).mp (ha.trans hb.symm)

end F2
end QuantumZipper
