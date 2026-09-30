import QuantumZipper.Proofs.Thm18.G3Zc2Univ
import QuantumZipper.Proofs.Thm18.G3Zc2Law2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: the joint dyadic law of two zooms of one free field is universal

`dyadLaw2_eq_free`: for the zoom of `y` at `0` through `ψ₁` and the zoom of `y` at `x₂` through
`ψ₂` (i.e. of `rawTranslate y x₂`), each in ZOOM-A's normalization `zoomS` (profiles `f₁`, `f₂`,
normalizing measures `S₁`, `S₂`), the joint law of the two dyadic data vectors is the same for any
two free fields. A.s. both vectors are deterministic shifts of balanced increments of `y`
(`ae_coordChange_ofFun_add_pullCircle`, `ae_coordChange_pullCircle`, applied to `y` and to its
translate), and a countable family of balanced increments of a free field has a universal law
(`WedgeRes.map_gaussFam_eq₂`). With `tendsto_twoPoint_of_lawEq` (G3Zc2Law2) this moves a
two-point zoom limit between free fields. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus K3 GFFExist LQGDimension.ExistAsm

/-- The pairs and shifts of the dyadic data of one zoom (at `0`, of the field `y ∘ (· + x)`). -/
theorem ae_dyadData_zoomS {ψ Ψ : ℂ → ℂ} {r₀ ρ r₁ m M : ℝ} (hD : PullData Ψ 0 r₀ ρ r₁ m M)
    (hΨ0 : Ψ 0 = 0) (heq : EqOn Ψ ψ (ball (0 : ℂ) r₀)) {a ρf : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = a * -Real.log ‖u‖ + h u)
    (hh : Continuous h) (hfm : Measurable f) (hMρ : M * ρ < ρf) (γ L Q : ℝ)
    {S : Measure ℂ} (x : ℝ) (hS : IsAdmissibleH (S.map (· + (x : ℂ)))) (hS1 : S Set.univ = 1)
    {r : ℝ} (hrρ : r ≤ ρ) :
    ∃ (p : DyIdxIn r → WedgeTK.BPair) (κ : DyIdxIn r → ℝ),
      ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
        {Y : Ω₀ → FieldSample}, IsFreeGFFModConstH Y P₀ →
        ∀ᵐ ω ∂P₀, dyadData r (zoomS γ L Q f ψ S (rawTranslate (Y ω) x)) =
          fun i => WedgeTK.gaussFam Y p i ω + κ i := by
  have hρr : ρ < r₀ := hD.hρr
  have hbd : ∀ i : DyIdxIn r, ‖dyC i.1‖ + radius i.1.2.1 ≤ ρ := fun i => by
    have := i.2; linarith
  have hbd' : ∀ i : DyIdxIn r, ‖dyC i.1 - ((0 : ℝ) : ℂ)‖ + radius i.1.2.1 ≤ ρ := fun i => by
    simpa using hbd i
  have hmt : Measurable fun z : ℂ => z + (x : ℂ) := measurable_id.add_const _
  have hΨm : Measurable Ψ := hD.conf.meas
  have hDx := hD.addReal x
  have hmapx : ∀ ν : Measure ℂ, (ν.map Ψ).map (· + (x : ℂ)) = ν.map fun z => Ψ z + (x : ℂ) :=
    fun ν => Measure.map_map hmt hΨm
  have hmass : ∀ i : DyIdxIn r, ((pullCircle Ψ (dyC i.1) (radius i.1.2.1)).map (· + (x : ℂ)))
      Set.univ = (S.map (· + (x : ℂ))) Set.univ := fun i => by
    rw [Measure.map_apply hmt MeasurableSet.univ, Measure.map_apply hmt MeasurableSet.univ,
      preimage_univ, pullCircle, Measure.map_apply hΨm MeasurableSet.univ, preimage_univ,
      measure_univ, hS1]
  have hadm : ∀ i : DyIdxIn r,
      IsAdmissibleH ((pullCircle Ψ (dyC i.1) (radius i.1.2.1)).map (· + (x : ℂ))) := fun i => by
    have h := hDx.isAdmissibleH_pullCircle (radius_pos _) (hbd' i)
    rw [pullCircle, hmapx]
    exact h
  let p : DyIdxIn r → WedgeTK.BPair := fun i =>
    ⟨((pullCircle Ψ (dyC i.1) (radius i.1.2.1)).map (· + (x : ℂ)), S.map (· + (x : ℂ))),
      hadm i, hS, hmass i⟩
  let κ : DyIdxIn r → ℝ := fun i => Q * (∫ z, Real.log ‖deriv Ψ z‖ ∂(dyCirc i.1)) +
      (∫ u, f (Ψ u) ∂(dyCirc i.1)) + L / γ
  refine ⟨p, κ, ?_⟩
  intro Ω₀ _ P₀ _ Y hY
  have hYx : IsFreeGFFModConstH (fun ω => rawTranslate (Y ω) x) P₀ := isFree_rawTranslate hY x
  have hi : ∀ i : DyIdxIn r, ∀ᵐ ω ∂P₀, dyadData r (zoomS γ L Q f ψ S (rawTranslate (Y ω) x)) i =
      WedgeTK.gaussFam Y p i ω + κ i := by
    intro i
    have ht : 0 < radius i.1.2.1 := radius_pos _
    filter_upwards [G3Za.ae_coordChange_ofFun_add_pullCircle hYx hD hΨ0 hf hh hfm hMρ Q ht
        (hbd i), ae_coordChange_pullCircle hYx hD Q ht (hbd' i)] with ω h1 h2
    simp only [dyadData, zoomS, addConst, dyCirc, WedgeTK.gaussFam, p, κ]
    rw [coordChange_swap heq hρr (foldedCircle_compl_null0 ht (hbd i)), h1, h2,
      measure_univ, ENNReal.toReal_one, mul_one]
    simp only [rawTranslate]
    ring
  rw [← ae_all_iff] at hi
  filter_upwards [hi] with ω h
  funext i
  exact h i

end G3Cv
end QuantumZipper
