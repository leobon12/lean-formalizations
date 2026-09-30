import QuantumZipper.Proofs.Thm18.G2DisintXGeom
import QuantumZipper.Proofs.Thm18.G3G2LocZoom
import QuantumZipper.Proofs.Thm18.G3AreaPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 zoom locality (`G2ZoomLocStmt`)

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 65: "the restriction of h to an extremely small
neighborhood of x … tells us what the quantum surface looks like when we zoom in near x", and
p. 66). We prove `G2ZoomLocStmt γ` for `0 < γ < 2` (`g2ZoomLocStmt_holds`), with one almost-sure
event for all `s`, `φ`, `r`, `x`, `b`: the event that `normField γ gffBase.X ω` is area-good
(`ae_isAreaGood_normField`: good, and its quantum area charges every nonempty open subset of `ℍ`).

* Deterministic part: `zoomLaw_mem_lawCyl_iff` (`G3G2LocZoom.lean`, the Duplantier–Sheffield
  locality of circle averages): a cylinder event of the zoom only sees the field on folded circles
  inside `B(x, q₀ R)` once the zoomed area of the half-ball of radius `q₀` is `≥ 1`. The fields
  `h + b φ` and `h` agree on every folded circle inside `B(x, r)` (`fcAgree_add_ofFun_ball`),
  because a folded circle about a point of `Hbar` is carried by its closed disc
  (`foldedCircle_ae_dist_le_zl`).
* Area part: area-goodness is translation invariant (`IsAreaGood.translate`), so the half-ball of
  radius `q₀` around **every** real `x` has positive area; the zoom adds `C/γ`, multiplying that
  area by `e^C` (`eventually_one_le_areaProxy_addConst_of_good`), so it is `≥ 1` for large `C`.
  No "almost every `x`" restriction arises: positivity holds at all `x` on the one good event.

Own elementary bookkeeping on top of the cited lemmas (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open Prop16Area.G

/-- A folded circle about a point of `Hbar` is carried by its closed disc (own copy of
`foldedCircle_ae_dist_le'`, avoiding a heavy import). -/
theorem foldedCircle_ae_dist_le_zl {c : ℂ} (hc : c ∈ Hbar) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ᵐ u ∂foldedCircle c ρ, dist u c ≤ ρ := by
  unfold foldedCircle
  refine (ae_map_iff (p := fun u => dist u c ≤ ρ) measurable_foldH.aemeasurable
    (measurableSet_closedBall (x := c) (ε := ρ))).2 ?_
  filter_upwards [CoordReg.ae_mem_closedBall_circleUnif c hρ] with z hz
  have hfc : foldH c = c := by
    have : 0 ≤ c.im := hc
    simp [foldH, this]
  have h := TwoPoint.norm_foldH_sub_le z c
  rw [hfc] at h
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [dist_eq_norm]
  linarith

/-- Adding `ofFun g` with `g = 0` on `W` does not change the field on folded circles inside `W`. -/
theorem fcAgree_add_ofFun_zero {W : Set ℂ} (y : FieldSample) {g : ℂ → ℝ}
    (hg : ∀ z ∈ W, g z = 0) : FcAgree W (y + ofFun g) y := by
  intro d hd ρ hρ hW
  show y (foldedCircle d ρ) + ∫ z, g z ∂foldedCircle d ρ = y (foldedCircle d ρ)
  rw [integral_eq_zero_of_ae, add_zero]
  filter_upwards [foldedCircle_ae_dist_le_zl hd hρ.le, RegClosure.fc_ae_mem_Hbar d ρ]
    with u hu hH
  exact hg u (hW ⟨hu, hH⟩)

/-- **G2 zoom locality** (`G2ZoomLocStmt`), for `0 < γ < 2`. -/
theorem g2ZoomLocStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2ZoomLocStmt γ := by
  intro s hs φ _hφc r hr
  obtain ⟨R, hR, hRs⟩ := zoomLaw_mem_lawCyl_iff hs
  have := gffBase.prob
  filter_upwards [ae_isAreaGood_normField gffBase.gff hγ hγ2] with ω hω
  intro x hx0 b
  have hR0 : 0 < R := by linarith
  obtain ⟨q₀, hq0, hq1⟩ := exists_rat_btwn (div_pos hr hR0)
  have hgood := hω.translate x
  have hev := eventually_one_le_areaProxy_addConst_of_good hγ hgood.1
    (pos_areaProxy_of_isAreaGood hgood hq0)
  filter_upwards [(tendsto_div_const_atTop hγ).eventually hev] with C hC
  refine hRs γ C _ _ x (ball (x : ℂ) r) isOpen_ball
    (fcAgree_add_ofFun_zero _ fun z hz => by rw [hx0 z hz, mul_zero]) q₀ hq0 ?_ hC
  intro z hz
  have hz1 : ‖z‖ ≤ q₀ * R := by simpa [dist_zero_right] using hz.1
  have hlt : (q₀ : ℝ) * R < r := (lt_div_iff₀ hR0).1 hq1
  show dist (z + (x : ℂ)) x < r
  rw [dist_eq_norm, add_sub_cancel_right]
  linarith

end Thm18Asm
end QuantumZipper
