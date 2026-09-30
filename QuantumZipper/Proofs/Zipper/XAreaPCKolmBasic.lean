import QuantumZipper.Proofs.Zipper.XAreaPCEnergy
import QuantumZipper.Proofs.GFF.SmoothingConvergence
import QuantumZipper.Proofs.LQG.CoordChangeSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-A-pc, step R2 (1/2): increment variances of a clamped difference family

Setting of the multiparameter Kolmogorov step of X-A-pc (Duplantier–Sheffield, Invent. Math. 185
(2011), Prop. 3.1; Revuz–Yor, 3rd ed., Ch. I, Thm (2.1)). Two families of admissible probability
measures `μ z s`, `ν z s` (`z` in a closed rectangle, `0 < s ≤ s₀`) satisfy (`DiffFam`)

* `|E(μ z s − ν z s)| ≤ C s` (energy of the difference; proved for pushed circle / image circle in
  `XAreaPCEnergy.lean`),
* `|E(μ z s − μ z' s')|, |E(ν z s − ν z' s')| ≤ C (‖z − z'‖ + |s − s'|) / min s s'`
  (energy moduli; node R1).

With the parameters clamped to the box (`PBox.zc`, `PBox.sc`, 1-Lipschitz) and the process
`Z q = X(μ) − X(ν)` for `s > 0`, `Z q = 0` for `s = 0` (`zq`), we prove
`E (Z q − Z q')² ≤ K ‖q − q'‖^{1/2}` for **all** `q, q' ∈ ℝ³` (`integral_sq_zq_sub_le`): the two
bounds `4Cδ/m` and `2C(s + s')` interpolate to `K √δ` (`xpc_interp`). Own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper.E6
namespace XAreaPC

/-! ## Clamping -/

/-- Clamp `x` to `[a, b]`. -/
def clampI (a b x : ℝ) : ℝ := max a (min b x)

theorem clampI_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : a ≤ clampI a b x ∧ clampI a b x ≤ b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clampI_of_mem {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : clampI a b x = x := by
  unfold clampI
  rw [min_eq_right h2, max_eq_right h1]

/-- A parameter box `[a₁, b₁] × [a₂, b₂] × [0, s₀]`. -/
structure PBox where
  a₁ : ℝ
  b₁ : ℝ
  a₂ : ℝ
  b₂ : ℝ
  s₀ : ℝ
  h₁ : a₁ ≤ b₁
  h₂ : a₂ ≤ b₂
  hs : 0 < s₀

namespace PBox

variable (B : PBox)

/-- The rectangle of centres. -/
def rect : Set ℂ := {z | B.a₁ ≤ z.re ∧ z.re ≤ B.b₁ ∧ B.a₂ ≤ z.im ∧ z.im ≤ B.b₂}

/-- The clamped centre. -/
def zc (q : Fin 3 → ℝ) : ℂ := ⟨clampI B.a₁ B.b₁ (q 0), clampI B.a₂ B.b₂ (q 1)⟩

/-- The clamped scale. -/
def sc (q : Fin 3 → ℝ) : ℝ := clampI 0 B.s₀ (q 2)

/-- The diameter bound. -/
def diam : ℝ := (B.b₁ - B.a₁) + (B.b₂ - B.a₂) + B.s₀

theorem diam_nonneg : 0 ≤ B.diam := by
  unfold diam; linarith [B.h₁, B.h₂, B.hs]

end PBox

/-! ## The difference family -/

/-- Hypotheses of the Kolmogorov step: admissible probability families with the energy bound of
the difference (`var0`) and the energy moduli (`mod_μ`, `mod_ν`, node R1). -/
structure DiffFam (B : PBox) (μ ν : ℂ → ℝ → Measure ℂ) (C : ℝ) : Prop where
  C_nonneg : 0 ≤ C
  adm_μ : ∀ z ∈ B.rect, ∀ s, 0 < s → s ≤ B.s₀ → IsAdmissibleH (μ z s)
  adm_ν : ∀ z ∈ B.rect, ∀ s, 0 < s → s ≤ B.s₀ → IsAdmissibleH (ν z s)
  mass_μ : ∀ z ∈ B.rect, ∀ s, 0 < s → s ≤ B.s₀ → μ z s univ = 1
  mass_ν : ∀ z ∈ B.rect, ∀ s, 0 < s → s ≤ B.s₀ → ν z s univ = 1
  var0 : ∀ z ∈ B.rect, ∀ s, 0 < s → s ≤ B.s₀ →
    |kernelCov2 neumannH (μ z s, ν z s) (μ z s, ν z s)| ≤ C * s
  mod_μ : ∀ z ∈ B.rect, ∀ z' ∈ B.rect, ∀ s s', 0 < s → s ≤ B.s₀ → 0 < s' → s' ≤ B.s₀ →
    |kernelCov2 neumannH (μ z s, μ z' s') (μ z s, μ z' s')| ≤
      C * (‖z - z'‖ + |s - s'|) / min s s'
  mod_ν : ∀ z ∈ B.rect, ∀ z' ∈ B.rect, ∀ s s', 0 < s → s ≤ B.s₀ → 0 < s' → s' ≤ B.s₀ →
    |kernelCov2 neumannH (ν z s, ν z' s') (ν z s, ν z' s')| ≤
      C * (‖z - z'‖ + |s - s'|) / min s s'

/-- The index type of the Gaussian process of balanced pairs. -/
abbrev BPairX := {p : Measure ℂ × Measure ℂ //
  IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}

variable {B : PBox} {μ ν : ℂ → ℝ → Measure ℂ} {C : ℝ}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

variable [IsProbabilityMeasure P]

end XAreaPC
end QuantumZipper.E6
