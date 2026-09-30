import QuantumZipper.Proofs.Thm18.G3CvAsm
import QuantumZipper.Proofs.Thm18.G1G0Stmt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1 → G0: the coupling for the admissible local maps of G0

`pullData_of_isG0Map`: an admissible local map of G0 (`Thm18Asm.IsG0Map r₀ ψ`: holomorphic and
injective on `B(0, r₀)`, real on `(−r₀, r₀)`, `ψ 0 = 0`, `ψ'(0) > 0`) agrees near `0` with a map
carrying the data `PullData` of the local conformal coupling (`exists_pullSetup`): Schwarz
symmetry and bi-Lipschitz bounds from `locConf_of_real`, and `ψ(closedBall 0 ρ ∩ Hbar) ⊆ Hbar`
because `Im ψ` does not vanish on the connected upper half-disc (injectivity and symmetry) and is
positive near `0` (`ψ'(0) > 0`). Hence `exists_pullSetup` applies to the zoom through any G0 map,
in particular (with `G0Map.g1zLocMap_g0Ext`) to the local maps of the curve. Own elementary
argument.
-/

noncomputable section

open MeasureTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate Topology

namespace QuantumZipper
namespace G3Cv

variable {Φ : ℂ → ℂ} {b r₀ : ℝ}

/-- **G0 maps carry the pull-back data.** -/
theorem pullData_of_isG0Map {r₀ : ℝ} {ψ : ℂ → ℂ} (hr₀ : 0 < r₀) (h : Thm18Asm.IsG0Map r₀ ψ) :
    ∃ (Ψ : ℂ → ℂ) (r₀' ρ r₁ m M : ℝ), 0 < r₁ ∧ PullData Ψ 0 r₀' ρ r₁ m M ∧
      EqOn Ψ ψ (ball (0 : ℂ) r₀') := by
  obtain ⟨hdiff, hinj, hreal, h0, hdim, hdre⟩ := h
  have hd : deriv ψ 0 ≠ 0 := fun e => by rw [e] at hdre; simp at hdre
  obtain ⟨Ψ, r₀', m, M, hL, heq, hBL⟩ := locConf_of_real (U := ball (0 : ℂ) r₀) isOpen_ball
    hdiff (b := 0) (by simpa using hr₀) hr₀ (fun t ht => hreal t (by simpa using ht))
    (by simpa using hd)
  have hpos : 0 < r₀' := hL.pos
  have heq' : EqOn Ψ ψ (ball (0 : ℂ) r₀') := by simpa using heq
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) r₀' := mem_ball_self hpos
  set ρ := r₀' / 2 with hρ
  set r₁ := r₀' / 4 with hr₁
  have hρr : ρ < r₀' := by linarith
  -- Schwarz symmetry and injectivity ⇒ `Im Ψ ≠ 0` on the upper half-disc
  set S : Set ℂ := ball (0 : ℂ) r₀' ∩ H with hS
  have hne : ∀ z ∈ S, (Ψ z).im ≠ 0 := by
    intro z hz him
    have hzc : conj z ∈ ball (0 : ℂ) r₀' := by
      have := conj_mem_ball_g3cv (b := 0) (by simpa using hz.1)
      simpa using this
    have e : Ψ (conj z) = Ψ z := by
      rw [hL.symm z (by simpa using hz.1), Complex.conj_eq_iff_im.2 him]
    have := hL.inj (by simpa using hzc) (by simpa using hz.1) e
    have him' := congrArg Complex.im this
    simp only [Complex.conj_im] at him'
    have hzH : 0 < z.im := hz.2
    linarith
  -- a point of `S` with `Im Ψ > 0`
  have hΨ0 : Ψ 0 = 0 := by rw [heq' h0b, h0]
  have hdΨ : deriv Ψ 0 = deriv ψ 0 :=
    Filter.EventuallyEq.deriv_eq (eventually_of_mem (isOpen_ball.mem_nhds h0b) heq')
  have hD : HasDerivAt Ψ (deriv ψ 0) 0 := by
    rw [← hdΨ]
    have hdiff' : DifferentiableOn ℂ Ψ (ball (0 : ℂ) r₀') := by simpa using hL.diff
    exact (hdiff'.differentiableAt (isOpen_ball.mem_nhds h0b)).hasDerivAt
  set d := deriv ψ 0 with hd_def
  have hdr : d = (d.re : ℂ) := Complex.ext rfl (by simpa using hdim)
  have hc : 0 < d.re / 2 := by linarith
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (hD.isLittleO.def hc)
  set ε : ℝ := min δ r₀' / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεδ : ε < δ := by have := min_le_left δ r₀'; linarith
  have hεr : ε < r₀' := by have := min_le_right δ r₀'; linarith
  set w : ℂ := Complex.I * ε with hw
  have hwn : ‖w‖ = ε := by simp [hw, abs_of_pos hε0]
  have hwS : w ∈ S := ⟨by rw [mem_ball_zero_iff, hwn]; exact hεr, by show (0 : ℝ) < (Complex.I * (ε : ℂ)).im; simpa using hε0⟩
  have hwpos : 0 < (Ψ w).im := by
    have hb := hδb (y := w) (by rw [dist_zero_right, hwn]; exact hεδ)
    simp only [hΨ0, sub_zero, smul_eq_mul, hwn] at hb
    have him := abs_le.1 ((Complex.abs_im_le_norm (Ψ w - w * d)).trans hb)
    have e : (Ψ w - w * d).im = (Ψ w).im - ε * d.re := by
      rw [Complex.sub_im, hdr, hw]; simp
    rw [e] at him
    nlinarith [him.1]
  -- constant sign on the connected set `S`
  have hSc : IsPreconnected S := ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hcont : ContinuousOn (fun z => (Ψ z).im) S :=
    Complex.continuous_im.comp_continuousOn ((hL.diff.continuousOn).mono (fun z hz => by
      simpa using hz.1))
  have hSpos : ∀ z ∈ S, 0 < (Ψ z).im := by
    intro z hz
    by_contra hneg
    push Not at hneg
    have hlt : (Ψ z).im < 0 := lt_of_le_of_ne hneg (hne z hz)
    obtain ⟨v, hv, hv0⟩ := hSc.intermediate_value hz hwS hcont ⟨hlt.le, hwpos.le⟩
    exact hne v hv hv0
  refine ⟨Ψ, r₀', ρ, r₁, m, M, by positivity, ⟨hL, by positivity, hρr, hBL ρ hρr,
    by linarith, fun z hz => ?_⟩, heq⟩
  have hzb : z ∈ ball (0 : ℂ) r₀' := closedBall_subset_ball hρr (by simpa using hz.1)
  rcases (show (0 : ℝ) ≤ z.im from hz.2).eq_or_lt with h0' | hlt
  · -- real point: `Ψ z` is real by the Schwarz symmetry
    have hzc : conj z = z := Complex.conj_eq_iff_im.2 h0'.symm
    have e := hL.symm z (by simpa using hzb)
    rw [hzc] at e
    have him := congrArg Complex.im e
    simp only [Complex.conj_im] at him
    show 0 ≤ (Ψ z).im
    linarith
  · exact (hSpos z ⟨hzb, hlt⟩).le

/-- `|Φ'|` is even across `ℝ` for a Schwarz-symmetric local conformal map. -/
theorem norm_deriv_conj (hΦ : LocConf Φ b r₀) {z : ℂ} (hz : z ∈ ball (b : ℂ) r₀) :
    ‖deriv Φ (conj z)‖ = ‖deriv Φ z‖ := by
  have hev : Φ =ᶠ[𝓝 z] (conj ∘ Φ ∘ conj) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    have := hΦ.symm (conj w) (conj_mem_ball_g3cv hw)
    simp only [Complex.conj_conj] at this
    simp only [Function.comp_apply, this, Complex.conj_conj]
  rw [hev.deriv_eq, deriv_conj_conj]
  simp

/-- **The coordinate-change term is a D3⁺ correction**: `Q log |Φ'|`, folded, is harmonic on the
disc (so it can be added to the model function `g` of `exists_pullSetup`). -/
theorem harmonicOnNhd_logDeriv_foldH (hΦ : LocConf Φ b r₀) (Q : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun z => Q * Real.log ‖deriv Φ (foldH z)‖)
      (ball (b : ℂ) r₀) := by
  intro z hz
  have hA : ∀ w ∈ ball (b : ℂ) r₀, HarmonicAt (fun v => Real.log ‖deriv Φ v‖) w := fun w hw =>
    ((hΦ.diff.analyticAt (isOpen_ball.mem_nhds hw)).deriv).harmonicAt_log_norm (hΦ.deriv_ne w hw)
  have hev : (fun v => Q * Real.log ‖deriv Φ (foldH v)‖) =ᶠ[𝓝 z]
      (Q • fun v => Real.log ‖deriv Φ v‖) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    simp only [Pi.smul_apply, smul_eq_mul, foldH]
    split_ifs
    · rfl
    · rw [norm_deriv_conj hΦ hw]
  exact (harmonicAt_congr_nhds hev).2 ((hA z hz).const_smul)

end G3Cv
end QuantumZipper
