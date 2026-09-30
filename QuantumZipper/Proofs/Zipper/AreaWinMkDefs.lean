import QuantumZipper.Proofs.Zipper.AreaWinSWConst
import QuantumZipper.Proofs.LQG.AreaOffsetsBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINMARKOV (0): the objects of the window Markov structure

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 1.1, p. 9 (the display
`C(N) sup_{ε} e^{h̄_ε(z)} = e^{h̄_{2^{-k/N}}(z)} (1 + G)`), and B. Duplantier, S. Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), §3.1: for a disc `B_r(w)` inside
the domain, `t ↦ h_{r e^{-t}}(w) − h_r(w)` is a standard Brownian motion independent of the
field outside `B_r(w)`.

Objects, for the `j`-th window `[2^{-(j+2)/N}, 2^{-j/N}]` (`r = winHi N j`, Brownian time
`t = log (r/ρ) ∈ [0, 2 log 2 / N]`):

* `mkRad N j t = r e^{-t}`;
* `mkIncr X N j w t = X(fc(w, r e^{-t})) − X(fc(w, r))` (raw coordinates: a Gaussian process);
* `mkIncrR X N j w t`: the same with `evalReg` (the values entering `areaDens`);
* `mkPhi γ X N b j w`: the sup (`b = true`) / inf over the rational times of the window of
  `e^{γ B_t − γ² t/2}` for `B = mkIncrR` (SW's `sup_{t ≤ s} e^{γ B_t − γ² t/2}`);
* `mkU X N j w = evalReg (X ω) (fc(w, r))` (the coarse value) and `mkG c Φ = c Φ − 1`;
* `mkT N j = {w : |‖w‖ − 1| ≤ 2 r}` (the exceptional strip).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

/-- The radius `2^{-j/N} e^{-t}` at Brownian time `t` of the `j`-th window. -/
def mkRad (N j : ℕ) (t : ℝ≥0) : ℝ := winHi N j * rexp (-(t : ℝ))

/-- The raw circle-average increment `X(fc(w, r e^{-t})) − X(fc(w, r))`, `r = 2^{-j/N}`. -/
def mkIncr {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (w : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  GaussTK.fcPairVal X (w, mkRad N j t, w, winHi N j) ω

/-- The regularized circle-average increment (`evalReg`). -/
def mkIncrR {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (w : ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  evalReg (X ω) (foldedCircle w (mkRad N j t)) - evalReg (X ω) (foldedCircle w (winHi N j))

/-- The window exponential `e^{γ v_t − γ² t/2}` of a path `v` on the rational window times. -/
def mkE (γ : ℝ) (N : ℕ) (v : swWinSet N → ℝ) (q : swWinSet N) : ℝ≥0∞ :=
  ENNReal.ofReal (rexp (γ * v q - γ ^ 2 / 2 * ((q : ℝ≥0) : ℝ)))

/-- SW's window functional: the supremum (`b = true`) or infimum (`b = false`) of `mkE`. -/
def mkF (γ : ℝ) (N : ℕ) (b : Bool) (v : swWinSet N → ℝ) : ℝ≥0∞ :=
  if b then ⨆ q, mkE γ N v q else ⨅ q, mkE γ N v q

/-- The regularized increment path of the window at `w`. -/
def mkFam {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (w : ℂ) (ω : Ω) : swWinSet N → ℝ :=
  fun q => mkIncrR X N j w q ω

/-- The raw increment path of the window at `w`. -/
def mkFamRaw {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (w : ℂ) (ω : Ω) : swWinSet N → ℝ :=
  fun q => mkIncr X N j w q ω

/-- SW's window factor `Φ = sup/inf_{t ∈ window ∩ ℚ} e^{γ B_t − γ² t/2}`. -/
def mkPhi {Ω : Type} (γ : ℝ) (X : Ω → FieldSample) (N : ℕ) (b : Bool) (j : ℕ) (w : ℂ)
    (ω : Ω) : ℝ≥0∞ :=
  mkF γ N b (mkFam X N j w ω)

/-- The window of the `WinMarkovData` instance: `supWin` for `b = true`, `infWin` otherwise. -/
def mkWin (γ : ℝ) (N : ℕ) (b : Bool) (x : FieldSample) (j : ℕ) (w : ℂ) : ℝ≥0∞ :=
  if b then supWin γ x N j w else infWin γ x N j w

/-- The coarse value `h_{2^{-j/N}}(w)`. -/
def mkU {Ω : Type} (X : Ω → FieldSample) (N j : ℕ) (w : ℂ) (ω : Ω) : ℝ :=
  evalReg (X ω) (foldedCircle w (winHi N j))

/-- The centred window factor `G = c Φ − 1`. -/
def mkG {Ω : Type} (c : ℝ) (Φ : ℂ → Ω → ℝ≥0∞) (w : ℂ) (ω : Ω) : ℝ := c * (Φ w ω).toReal - 1

theorem winHi_pos (N j : ℕ) : 0 < winHi N j := Real.rpow_pos_of_pos (by norm_num) _

theorem mkRad_pos (N j : ℕ) (t : ℝ≥0) : 0 < mkRad N j t :=
  mul_pos (winHi_pos N j) (Real.exp_pos _)

theorem mkRad_le (N j : ℕ) (t : ℝ≥0) : mkRad N j t ≤ winHi N j := by
  unfold mkRad
  have : rexp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
  nlinarith [winHi_pos N j]

end QuantumZipper.E6
