import QuantumZipper.Proofs.Thm18.G3Zc2Univ2
import QuantumZipper.Proofs.Thm18.G3Zc2Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: joint universality of (zoom dyadic data, far increments)

`dyadLawCond_eq_free`: for the zoom of `y` at `x` through `ψ` (ZOOM-A's normalization `zoomS`,
applied to `rawTranslate y x`) and any countable family `q` of balanced pairs of admissible
measures (the conditioning increments, e.g. outside coordinates), the joint law of

  `(dyadData r (zoomS … (rawTranslate y x)), (y(q k).1 − y(q k).2)_k)`

is the same for any two free fields. This supplies the joint-law hypothesis of
`cond_zoom_of_lawEq` (G3Zc2Cond) when the conditioning variable is a measurable function of
countably many balanced increments. Proof: `ae_dyadData_zoomS` and
`WedgeRes.map_gaussFam_eq₂` on the combined family. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus K3 GFFExist LQGDimension.ExistAsm

theorem dyadLawCond_eq_free {ψ Ψ : ℂ → ℂ} {r₀ ρ r₁ m M : ℝ} (hD : PullData Ψ 0 r₀ ρ r₁ m M)
    (hΨ0 : Ψ 0 = 0) (heq : EqOn Ψ ψ (ball (0 : ℂ) r₀)) {a ρf : ℝ} {f h : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar, f u = a * -Real.log ‖u‖ + h u)
    (hh : Continuous h) (hfm : Measurable f) (hMρ : M * ρ < ρf) (γ L Q : ℝ)
    {S : Measure ℂ} (x : ℝ) (hS : IsAdmissibleH (S.map (· + (x : ℂ)))) (hS1 : S Set.univ = 1)
    {r : ℝ} (hrρ : r ≤ ρ) {K : Type} (q : K → WedgeTK.BPair)
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {W : Ω → FieldSample}
    {V : Ω' → FieldSample} (hW : IsFreeGFFModConstH W P) (hV : IsFreeGFFModConstH V P') :
    AEMeasurable (fun ω => (dyadData r (zoomS γ L Q f ψ S (rawTranslate (W ω) x)),
        fun k => WedgeTK.gaussFam W q k ω)) P ∧
      AEMeasurable (fun ω => (dyadData r (zoomS γ L Q f ψ S (rawTranslate (V ω) x)),
        fun k => WedgeTK.gaussFam V q k ω)) P' ∧
      (P.map fun ω => (dyadData r (zoomS γ L Q f ψ S (rawTranslate (W ω) x)),
          fun k => WedgeTK.gaussFam W q k ω)) =
        P'.map fun ω => (dyadData r (zoomS γ L Q f ψ S (rawTranslate (V ω) x)),
          fun k => WedgeTK.gaussFam V q k ω) := by
  obtain ⟨p, κ, hp⟩ := ae_dyadData_zoomS hD hΨ0 heq hf hh hfm hMρ γ L Q x hS hS1 hrρ
  set pq : DyIdxIn r ⊕ K → WedgeTK.BPair := Sum.elim p q with hpq
  set T : (DyIdxIn r ⊕ K → ℝ) → (DyIdxIn r → ℝ) × (K → ℝ) :=
    fun ξ => (fun i => ξ (Sum.inl i) + κ i, fun k => ξ (Sum.inr k)) with hT
  have hTm : Measurable T :=
    (measurable_pi_iff.2 fun i => (measurable_pi_apply _).add_const _).prodMk
      (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  have hid : ∀ {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
      {Y : Ω₀ → FieldSample}, IsFreeGFFModConstH Y P₀ →
      ∀ᵐ ω ∂P₀, (dyadData r (zoomS γ L Q f ψ S (rawTranslate (Y ω) x)),
          fun k => WedgeTK.gaussFam Y q k ω) = T (fun i => WedgeTK.gaussFam Y pq i ω) := by
    intro Ω₀ _ P₀ _ Y hY
    filter_upwards [hp hY] with ω e
    simp only [e, hT, hpq, WedgeTK.gaussFam, Sum.elim_inl, Sum.elim_inr]
  refine ⟨((hTm.comp (WedgeTK.measurable_gaussFam_pi hW pq)).aemeasurable).congr
      ((hid hW).mono fun ω h => h.symm),
    ((hTm.comp (WedgeTK.measurable_gaussFam_pi hV pq)).aemeasurable).congr
      ((hid hV).mono fun ω h => h.symm), ?_⟩
  rw [Measure.map_congr (hid hW), Measure.map_congr (hid hV)]
  have e1 := Measure.map_map (μ := P) hTm (WedgeTK.measurable_gaussFam_pi hW pq)
  have e2 := Measure.map_map (μ := P') hTm (WedgeTK.measurable_gaussFam_pi hV pq)
  simp only [Function.comp_def] at e1 e2
  rw [← e1, ← e2, WedgeRes.map_gaussFam_eq₂ hW hV pq]

end G3Cv
end QuantumZipper
