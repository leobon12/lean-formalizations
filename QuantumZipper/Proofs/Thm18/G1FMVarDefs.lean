import QuantumZipper.Proofs.Thm18.G1FMMain
import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FM-KOLM5, definitions: pushed first-mode measures and the three nodes

Task G1-FM-KOLM5. The 5-parameter analogue of `D3PlusN2FMVarDefs.lean` for the pushed free field
`V(d, r, S) = X((S ψ)_* fc(d, r))`: the first-mode arc measures `D3Plus.fmMeas w v s` are pushed
by `z ↦ S ψ(z)` (`pfmMeas`). Nodes stated here (analogues of `D3Plus.FMReprStmt`,
`D3Plus.FMAdmStmt`, `D3Plus.N2ZFMEnergyStmt`, with the extra scale parameter `S`):

* `G1FMReprStmt`: a.s. the `k`-th part of the first mode of `V(·, ·, S)` is the pair
  `X(pfmMeas ψ S w (τ u_k) s) − X(pfmMeas ψ S w (−τ u_k) s)`;
* `G1FMAdmStmt`: the pushed first-mode measures are admissible;
* `G1FMEnergyStmt`: Neumann energies of the pairs `≤ c`, of increments
  `≤ c (‖Δw‖ + |Δτ| + |Δs| + |ΔS|) / τ`.

`G1FM.pfmPos`/`G1FM.pfmNeg`: the pairs in the rescaled clamped coordinates `q ∈ ℝ⁵`; the first
four coordinates are clamped exactly as in `D3Plus.fmCq/fmRq/fmSq` (via `G1FM.fmPr`), the fifth
gives `S = 2^{-n} clamp_{[2^n/(m+1), (m+1) 2^n]}(q 4) ∈ [1/(m+1), m+1]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- Pushed first-mode measure. -/
def pfmMeas (ψ : ℂ → ℂ) (S : ℝ) (w v : ℂ) (s : ℝ) : Measure ℂ :=
  (D3Plus.fmMeas w v s).map fun z => (S : ℂ) * ψ z

/-- **Node G1-FM-REPR** (stochastic Fubini for the pushed first mode). -/
def G1FMReprStmt : Prop :=
  ∀ ψ : ℂ → ℂ, G1RC.PsiGood ψ →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∀ V : ℂ × ℝ × ℝ → Ω → ℝ, (∀ ω, ContinuousOn (fun p => V p ω) (univ ×ˢ Ioi 0 ×ˢ Ioi 0)) →
      (∀ (d : ℂ) (r S : ℝ), 0 < r → r < d.im → 0 < S → (fun ω => V (d, r, S) ω) =ᵐ[P]
        fun ω => X ω ((foldedCircle d r).map fun z => (S : ℂ) * ψ z)) →
      ∀ (k : Fin 2) (w : ℂ) (τ s S : ℝ), 0 < τ → 0 < s → τ + s < w.im → 0 < S →
        ∀ᵐ ω ∂P, D3Plus.fmPart k (D3Plus.fmInt (fun p => V (p.1, p.2, S) ω) w τ s) =
          X ω (pfmMeas ψ S w ((τ : ℂ) * D3Plus.fmDir k) s) -
            X ω (pfmMeas ψ S w (-((τ : ℂ) * D3Plus.fmDir k)) s)

/-- **Node G1-FM-ADM** (admissibility of the pushed first-mode measures). -/
def G1FMAdmStmt : Prop :=
  ∀ ψ : ℂ → ℂ, G1RC.PsiGood ψ → ∀ (w v : ℂ) (s S : ℝ), 0 ≤ s → 0 < ‖v‖ → ‖v‖ + s < w.im →
    0 < S → IsAdmissibleH (pfmMeas ψ S w v s)

/-- **Node G1-FM-ENERGY** (Neumann energies of the pushed first-mode pairs). -/
def G1FMEnergyStmt : Prop :=
  ∀ ψ : ℂ → ℂ, G1RC.PsiGood ψ → ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧
    ∀ u : ℂ, ‖u‖ = 1 → ∀ w w' : ℂ, ‖w‖ ≤ 2 * ((m : ℝ) + 1) → ‖w'‖ ≤ 2 * ((m : ℝ) + 1) →
      1 / ((m : ℝ) + 1) ≤ w.im → 1 / ((m : ℝ) + 1) ≤ w'.im →
      ∀ τ τ' : ℝ, 0 < τ → τ ≤ τ₀ → τ ≤ 2 * τ' → τ' ≤ 2 * τ →
      ∀ s s' : ℝ, 0 ≤ s → s ≤ τ → 0 ≤ s' → s' ≤ τ' →
      ∀ S S' : ℝ, S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) →
        S' ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) →
        kernelCov2 neumannH (pfmMeas ψ S w ((τ : ℂ) * u) s, pfmMeas ψ S w (-((τ : ℂ) * u)) s)
            (pfmMeas ψ S w ((τ : ℂ) * u) s, pfmMeas ψ S w (-((τ : ℂ) * u)) s) ≤ c ∧
        kernelCov2 neumannH
            (pfmMeas ψ S w ((τ : ℂ) * u) s + pfmMeas ψ S' w' (-((τ' : ℂ) * u)) s',
              pfmMeas ψ S w (-((τ : ℂ) * u)) s + pfmMeas ψ S' w' ((τ' : ℂ) * u) s')
            (pfmMeas ψ S w ((τ : ℂ) * u) s + pfmMeas ψ S' w' (-((τ' : ℂ) * u)) s',
              pfmMeas ψ S w (-((τ : ℂ) * u)) s + pfmMeas ψ S' w' ((τ' : ℂ) * u) s') ≤
          c * (‖w - w'‖ + |τ - τ'| + |s - s'| + |S - S'|) / τ

namespace G1FM

open D3Plus

/-- The first four coordinates. -/
def fmPr (q : Fin 5 → ℝ) : Fin 4 → ℝ := fun i => q (Fin.castSucc i)

/-- Clamped rescaled scale `S ∈ [1/(m+1), m+1]`. -/
def fmSSq (m n : ℕ) (q : Fin 5 → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ n * fmCl (2 ^ n / ((m : ℝ) + 1)) (((m : ℝ) + 1) * 2 ^ n) (q 4)

/-- Positive pushed first-mode measure at the rescaled parameter `q`. -/
def pfmPos (ψ : ℂ → ℂ) (m n : ℕ) (k : Fin 2) (q : Fin 5 → ℝ) : Measure ℂ :=
  pfmMeas ψ (fmSSq m n q) (fmCq m n (fmPr q)) ((fmRq n (fmPr q) : ℂ) * fmDir k) (fmSq n (fmPr q))

/-- Negative pushed first-mode measure at the rescaled parameter `q`. -/
def pfmNeg (ψ : ℂ → ℂ) (m n : ℕ) (k : Fin 2) (q : Fin 5 → ℝ) : Measure ℂ :=
  pfmMeas ψ (fmSSq m n q) (fmCq m n (fmPr q)) (-((fmRq n (fmPr q) : ℂ) * fmDir k))
    (fmSq n (fmPr q))

end G1FM
end Thm18Asm
end QuantumZipper
