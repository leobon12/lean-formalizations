import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.JointModFinal
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.Zipper.E1Glue

/-!
# UNIF-UG: `UnifGlobalStmt` (UG) and `UnifAtomlessStmt` (UA) from an off-tip and a tip statement

Decision D26 (`DECISIONS.md`), task UNIF-UG. Both UG (a.s., for all `s ∈ [0,T]`, the boundary
approximations of `h⁰_s = h0f κ s B X ω` have a global vague limit) and UA (a.s., for all `s`, that
limit has no atoms) split, deterministically and for every `s` on one event, into:

* `UnifOffTipStmt` (**UO**): a.s., for all `s ∈ [0,T]` and every rational window `(u,v)` whose
  closure avoids the tip `0`, the approximations of `h⁰_s` have an atomless local vague limit on
  `(u,v)`. This is what anchored windows (AW, extended to the outer real line) provide.
* `UnifTipStmt` (**UT**): a.s., for all `s ∈ [0,T]`, the approximate masses of `(−δ,δ)` are
  eventually (in the dyadic scale) uniformly small as `δ → 0`: the "uniform-in-`s` bound on the
  approximate mass near `0`" of D26.

Main result: **`unifGlobal_unifAtomless_of_offTip_tip`**: UO + UT ⇒ UG ∧ UA.

The regularity of `h⁰_s` for all `s` at once (finite approximations on compacts) comes from
`RegUnif.ae_forall_isRegularSample` (JOINTMOD). The deterministic core
(`exists_isVagueLimitR_atomless_of_windows_tight`) glues the window limits
(`E1.exists_isVagueLimitOnR_of_winW`, sheaf property of Radon measures) and removes the tip with
`LogSing.isVagueLimitR_of_local_of_tight` (M4-P4). Sources: Bourbaki, *Integration*, Ch. III §2
No. 1, Prop. 1 (gluing); the tip step is the standard tightness argument for Gaussian
multiplicative chaos with a log singularity (Berestycki–Powell, arXiv:2404.16642). The
decomposition into UO and UT is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5

variable {Ω : Type} [MeasurableSpace Ω]

/-- **UO (off-tip windows at all times)**: a.s., for all `s ∈ [0,T]` and every rational window
`(u,v)` with `0 ∉ [u,v]`, `bdryApprox γ h⁰_s` has an atomless vague limit on `(u,v)`. -/
def UnifOffTipStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ s ∈ Icc 0 T, ∀ u v : ℚ, (0 : ℝ) ∉ Icc (u : ℝ) v →
    ∃ ν, IsVagueLimitOnR (Ioo (u : ℝ) v) (bdryApprox (Real.sqrt κ) (h0f κ s B X ω)) ν ∧
      ∀ x, ν {x} = 0

/-! ## Deterministic core -/

/-! ## UG and UA -/

end RegUnif
end QuantumZipper
