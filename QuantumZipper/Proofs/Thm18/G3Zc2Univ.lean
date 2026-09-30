import QuantumZipper.Proofs.Thm18.G3Zc2Law
import QuantumZipper.Proofs.Thm18.G3Zc2Sep
import QuantumZipper.Proofs.Thm18.G3Za2
import QuantumZipper.Proofs.LQG.WedgeRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: the dyadic data of a zoom have a universal law among free fields

`dyadLaw_eq_free`: let `ψ` agree near `0` with a local conformal datum `Ψ` (`PullData Ψ 0 …`,
`Ψ 0 = 0`), `f = a(−log‖·‖) + h` near `0` (`h` continuous), `S` an admissible probability measure
and `r ≤ ρ`. For **any two** free fields `W` (on `P`) and `V` (on `P'`) the dyadic data inside
`ball 0 r` of the zooms

  `addConst (coordChange (ofFun f + Y ω) ψ Q) (L/γ − Y ω S)`,  `Y = W, V`,

have the same law. Indeed, a.s. each dyadic value is `Y(Ψ_* c_i) − Y(S)` plus a deterministic
constant (`ae_coordChange_ofFun_add_pullCircle`, ZOOM-A; `ae_coordChange_pullCircle`), and the
joint law of a countable family of balanced increments of a free field is universal
(`WedgeRes.map_gaussFam_eq₂`).

With `tendsto_zoom_of_lawEq` (G3Zc2Law) this transfers the Palm-case one-point core of ZOOM-A
(`G3Za.exists_g0Setup_palmField`, its own field `W`) to the free field `V` of the Palm identity.
Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus K3 GFFExist LQGDimension.ExistAsm

/-- The zoom field normalized at `S` (ZOOM-A's form). -/
def zoomS (γ L Q : ℝ) (f : ℂ → ℝ) (ψ : ℂ → ℂ) (S : Measure ℂ) (y : FieldSample) : FieldSample :=
  addConst (coordChange (ofFun f + y) ψ Q) (L / γ - y S)

/-- **Universality of the dyadic law of the zooms.** -/
theorem dyadLaw_eq_free {ψ Ψ : ℂ → ℂ} {r₀ ρ r₁ m M : ℝ} (hD : PullData Ψ 0 r₀ ρ r₁ m M)
    (hΨ0 : Ψ 0 = 0) (heq : EqOn Ψ ψ (ball (0 : ℂ) r₀)) {a ρf : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = a * -Real.log ‖u‖ + h u)
    (hh : Continuous h) (hfm : Measurable f) (hMρ : M * ρ < ρf) (γ L Q : ℝ)
    {S : Measure ℂ} (hS : IsAdmissibleH S) (hS1 : S Set.univ = 1) {r : ℝ} (hrρ : r ≤ ρ)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {W : Ω → FieldSample}
    {V : Ω' → FieldSample} (hW : IsFreeGFFModConstH W P) (hV : IsFreeGFFModConstH V P') :
    AEMeasurable (fun ω => dyadData r (zoomS γ L Q f ψ S (W ω))) P ∧
      AEMeasurable (fun ω => dyadData r (zoomS γ L Q f ψ S (V ω))) P' ∧
      (P.map fun ω => dyadData r (zoomS γ L Q f ψ S (W ω))) =
        P'.map fun ω => dyadData r (zoomS γ L Q f ψ S (V ω)) := by
  have hρr : ρ < r₀ := hD.hρr
  -- the balanced pairs
  have hbd : ∀ i : DyIdxIn r, ‖dyC i.1‖ + radius i.1.2.1 ≤ ρ := fun i => by
    have := i.2; linarith
  have hbd' : ∀ i : DyIdxIn r, ‖dyC i.1 - ((0 : ℝ) : ℂ)‖ + radius i.1.2.1 ≤ ρ := fun i => by
    simpa using hbd i
  have hmass : ∀ i : DyIdxIn r, (pullCircle Ψ (dyC i.1) (radius i.1.2.1)) Set.univ = S Set.univ :=
    fun i => by
      rw [pullCircle, Measure.map_apply hD.conf.meas MeasurableSet.univ, preimage_univ,
        measure_univ, hS1]
  let p : DyIdxIn r → WedgeTK.BPair := fun i =>
    ⟨(pullCircle Ψ (dyC i.1) (radius i.1.2.1), S),
      hD.isAdmissibleH_pullCircle (radius_pos _) (hbd' i), hS, hmass i⟩
  set κ : DyIdxIn r → ℝ := fun i =>
    Q * (∫ z, Real.log ‖deriv Ψ z‖ ∂(dyCirc i.1)) + (∫ u, f (Ψ u) ∂(dyCirc i.1)) + L / γ with hκ
  set T : (DyIdxIn r → ℝ) → (DyIdxIn r → ℝ) := fun ξ i => ξ i + κ i with hT
  have hTm : Measurable T := measurable_pi_iff.2 fun i => (measurable_pi_apply i).add_const _
  -- a.s. identity
  have hid : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
      {Y : Ω₀ → FieldSample}, IsFreeGFFModConstH Y P₀ →
      ∀ᵐ ω ∂P₀, dyadData r (zoomS γ L Q f ψ S (Y ω)) =
        T (fun i => WedgeTK.gaussFam Y p i ω) := by
    intro Ω₀ _ P₀ _ Y hY
    have hi : ∀ i : DyIdxIn r, ∀ᵐ ω ∂P₀, dyadData r (zoomS γ L Q f ψ S (Y ω)) i =
        T (fun i => WedgeTK.gaussFam Y p i ω) i := by
      intro i
      have ht : 0 < radius i.1.2.1 := radius_pos _
      filter_upwards [G3Za.ae_coordChange_ofFun_add_pullCircle hY hD hΨ0 hf hh hfm hMρ Q ht
          (hbd i), ae_coordChange_pullCircle hY hD Q ht (hbd' i)] with ω h1 h2
      simp only [dyadData, zoomS, addConst, dyCirc, hT, hκ, WedgeTK.gaussFam, p]
      rw [coordChange_swap heq hρr (foldedCircle_compl_null0 ht (hbd i)), h1, h2,
        measure_univ, ENNReal.toReal_one, mul_one]
      ring
    rw [← ae_all_iff] at hi
    filter_upwards [hi] with ω h
    funext i
    exact h i
  refine ⟨((hTm.comp (WedgeTK.measurable_gaussFam_pi hW p)).aemeasurable).congr
      ((hid hW).mono fun ω h => h.symm), ((hTm.comp (WedgeTK.measurable_gaussFam_pi hV p)).aemeasurable).congr
      ((hid hV).mono fun ω h => h.symm), ?_⟩
  rw [Measure.map_congr (hid hW), Measure.map_congr (hid hV)]
  have e1 := Measure.map_map (μ := P) hTm (WedgeTK.measurable_gaussFam_pi hW p)
  have e2 := Measure.map_map (μ := P') hTm (WedgeTK.measurable_gaussFam_pi hV p)
  simp only [Function.comp_def] at e1 e2
  rw [← e1, ← e2, WedgeRes.map_gaussFam_eq₂ hW hV p]

/-- A local conformal datum restricted to a smaller disc. -/
theorem PullData.shrink {Ψ : ℂ → ℂ} {r₀ ρ r₁ m M : ℝ} (hD : PullData Ψ 0 r₀ ρ r₁ m M) {ρ' : ℝ}
    (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) : PullData Ψ 0 r₀ ρ' (ρ' / 2) m M where
  conf := hD.conf
  hρ := hρ'
  hρr := hle.trans_lt hD.hρr
  bl := ⟨hD.bl.1, hD.bl.2.1, fun z hz w hw =>
    hD.bl.2.2 z (closedBall_subset_closedBall hle hz) w (closedBall_subset_closedBall hle hw)⟩
  hr₁ := by linarith
  up := fun z hz => hD.up z ⟨closedBall_subset_closedBall hle hz.1, hz.2⟩

theorem AgreeNear.mono_radius {y y' : FieldSample} {r r' : ℝ} (h : AgreeNear y y' r)
    (hle : r' ≤ r) : AgreeNear y y' r' := fun n k z hz => h n k z (lt_of_lt_of_le hz hle)

end G3Cv
end QuantumZipper
