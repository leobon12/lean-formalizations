import QuantumZipper.Proofs.Thm18.G3Cv2Reg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 3 (one-point core, circle data): the zoom of a free field through a G0 map is
# a D3⁺ model

`exists_g0Model`: for an admissible local map `ψ` of G0 (`Thm18Asm.IsG0Map r₀ ψ`) and `Q : ℝ`
there is `r' > 0` and, on one probability space, free fields `W, X'`, variables `Ξ` independent
of the increments of `X'`, and a random function `g` with `g ω ∘ foldH` harmonic on
`closedBall 0 r'` for every `ω` and `g z` measurable for the D3⁺ conditioning σ-algebra
`σ(Ξ) ⊔ outsideSigma X' 0 r'` (`D3Plus.condSigma`), such that for all folded circles
`fc(c, s), fc(c', s')` with `‖c‖ + s, ‖c'‖ + s' ≤ r'`, a.s.

  `coordChange (W ω) ψ Q fc(c,s) − coordChange (W ω) ψ Q fc(c',s')`
    `= X'(fc(c,s)) − X'(fc(c',s')) + ∫ g ω dfc(c,s) − ∫ g ω dfc(c',s')`.

So, at the circle coordinates and modulo additive constants, the free field seen through `ψ`
(`coordChange`, which is what `zoomFieldVia` reads) is the D3⁺ model field `X' + g`: `g` is the
harmonic part of the Markov coupling (`exists_pullSetup`) plus the coordinate-change term
`Q log |ψ'|` (`harmonicOnNhd_logDeriv_foldH`); the regularized evaluation is the raw pairing
(`ae_coordChange_pullCircle`); `ψ` is replaced near `0` by the map with `PullData`
(`pullData_of_isG0Map`). Sources as in G3CvSetup.lean (Sheffield 2007 §2.2, Thm 2.17;
arXiv:1012.4797 pp. 70–71). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm

theorem foldedCircle_compl_null0 {c : ℂ} {r R : ℝ} (hr : 0 < r)
    (hcr : ‖c‖ + r ≤ R) : foldedCircle c r (closedBall (0 : ℂ) R ∩ Hbar)ᶜ = 0 := by
  have h := foldedCircle_compl_null (b := 0) hr (by simpa using hcr)
  simpa using h

end G3Cv
end QuantumZipper
