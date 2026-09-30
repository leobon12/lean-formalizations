import QuantumZipper.Proofs.Thm18.LWBeurlingMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWF-6 ingredient: the Beurling estimate seen from far away (inversion form)

Task LWF-6 (plan `handoff/LW-FAR.md`). The proved Beurling estimate `beurlingHarmStmt_holds`
(LW Prop 2.1, p. 5; Lawler, *Conformally Invariant Processes in the Plane*, Thm 3.69, p. 77)
bounds a harmonic function at the CENTER `w` of the disk near which a continuum passes. In the
pocket argument (Lawler–Werness, *Multi-point Green's functions for SLE and an estimate of
Beffara*, Ann. Probab. 41 (2013), proof of Lemma 4.4, p. 24: "from there we need to hit `V`
which contributes a factor of `O(ε^{1/2})` by the Beurling estimate") the estimate is used
from a FAR point `x`: a Brownian motion started at `x` must reach the small disk `B̄(w, ρ)`.

`pocketBeurlingFar` is this form: if `V` is a bounded open set outside `B̄(w, ρ)`, `h ∈ [0, 1]`
is harmonic on `V` and tends to `0` at the points of `∂V` outside `B̄(w, ρ)`, and an unbounded
continuum `A` disjoint from `V` (not containing `w`) meets `B̄(w, ρ)`, then
`h(x) ≤ C (ρ / |x − w|)^{1/2}` for `|x − w| ≥ 4ρ`. Proof: apply `beurlingHarmStmt_holds` to
`h ∘ ψ`, `ψ(v) = w + 1/v`, at the center `1/(x − w)` (the inversion `u ↦ 1/(u − w)` maps the
exterior of `B̄(w, ρ)` into `B(0, 1/ρ)` and `∞` to `0`). Standard inversion argument
(own elementary reduction to the cited Beurling estimate).
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- A harmonic function composed with a complex-analytic map is harmonic. -/
theorem pocket_harmonicAt_comp {h : ℂ → ℝ} {ψ : ℂ → ℂ} {u : ℂ} (hψ : AnalyticAt ℂ ψ u)
    (hh : InnerProductSpace.HarmonicAt h (ψ u)) : InnerProductSpace.HarmonicAt (h ∘ ψ) u := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (InnerProductSpace.isOpen_setOfPred_harmonicAt (f := h)) _ hh
  obtain ⟨F, hF, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := h)
      (z := ψ u) (R := r) (fun y hy => hball hy)
  have hFψ : AnalyticAt ℂ (F ∘ ψ) u := (hF _ (mem_ball_self hr)).comp hψ
  have hre := hFψ.harmonicAt_re
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hre
  have hev : ∀ᶠ v in 𝓝 u, ψ v ∈ ball (ψ u) r :=
    hψ.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  filter_upwards [hev] with v hv
  exact hFeq hv

end LWFar
end Thm18Asm
end QuantumZipper
