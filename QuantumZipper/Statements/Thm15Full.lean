import QuantumZipper.Statements.Thm15
import QuantumZipper.Zipper.Maps

/-!
# Corollary 1.5 (capacity quantum zipper), with the well-definedness clause (D97)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (PDF pp. 17–18).
Specification only. Companion of `theorem1_5` (`Statements/Thm15.lean`, unchanged): same setting,
same clauses (a) and (b), plus the italic sentence inside the corollary as clause (c).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

/-- **Corollary 1.5, full form** (Sheffield, arXiv:1012.4797, pp. 17–18). Setting and clauses
(a), (b) exactly as in `theorem1_5`. Clause (c) formalizes the italic sentence of the corollary:

> "Note that both h and η are determined by the pair ((D₁, h^{D₁}), (D₂, h^{D₂})), and that
> f^h_t and f^η_t are also a.s. determined by this pair, so that the maps Z^CAP_t and Z^CAP_{−t}
> are well defined for almost all pairs ((D₁, h^{D₁}), (D₂, h^{D₂})) chosen in the manner
> described above."

* (c) for every `t ≥ 0`, almost surely the field `h = 𝔥₀ + X ω` has a welding driver at
  capacity time `t` (`IsWeldingDriver`: a continuous `W'` with `W' 0 = 0` whose reverse flow
  zips up a simple-curve hull, `t > 0`, with welding homeomorphism equal to the paper's `R_h`),
  and any two welding drivers agree on `[0,t]`. Hence `f^h_t`, and so `Z^CAP_t = zipCap γ t`,
  which reads the chosen driver `weldDriver γ h t` only on `[0,t]`, is a.s. determined by `h`.
  (`Z^CAP_{−t}` unzips by the forward flow of the given driver, which the configuration carries
  explicitly, so it needs no clause.)

Quantifier order: fixed `t`, then almost surely, as in the Theorem 1.8 statement
(`theorem1_8_zipperStationarityPaperMO`, uniqueness of `IsLenWeldingDriver`) and as the paper's
"for almost all pairs" refers to the map `Z^CAP_t` for a given `t`. -/
def theorem1_5_full : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    let γ := Real.sqrt κ
    let c : Ω → FieldSample × (ℝ → ℝ) := fun ω => (ofFun (h0rev κ) + X ω, drive κ B ω)
    -- (a) law invariance under `Z^CAP_t`, `t ∈ ℝ`
    (∀ t : ℝ, configLawMod0 (fun ω => zipCap γ t (c ω)) P = configLawMod0 c P) ∧
    -- (b) group property, almost surely for each fixed `s, t`
    (∀ s t : ℝ, ∀ᵐ ω ∂P, ConfigEq (zipCap γ (s + t) (c ω)) (zipCap γ s (zipCap γ t (c ω)))) ∧
    -- (c) the welding driver of `f^h_t` exists and is unique on `[0,t]`, a.s. for each `t ≥ 0`
    (∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P,
      (∃ W : ℝ → ℝ, IsWeldingDriver γ (c ω).1 t W) ∧
      ∀ W₁ W₂ : ℝ → ℝ, IsWeldingDriver γ (c ω).1 t W₁ → IsWeldingDriver γ (c ω).1 t W₂ →
        ∀ s ∈ Set.Icc 0 t, W₁ s = W₂ s)

end QuantumZipper
