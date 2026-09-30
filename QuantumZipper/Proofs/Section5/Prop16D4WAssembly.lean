import QuantumZipper.Proofs.Section5.Prop16D4WScale
import QuantumZipper.Proofs.Section5.Prop16WeakAssembly

/-!
# Proposition 1.6: D4⁺ʷ from its remaining inputs

Decision D24 (`DECISIONS.md`). `prop16TVWeak_of_inputs` proves the node
`Prop16Asm.Prop16TVWeakStmt` (D4⁺ʷ) from the node `Prop16NuMeasStmt` and
`Prop16D4WInputsStmt`, which asks, for the data of `theorem1_6`, for a `γ`-wedge `W` and an
"unperturbed zoomed field" `x C p` (the zoomed field without the continuous remainder
`ψ_p = 𝔥₀(· + p.2) − 𝔥₀(p.2)`) with:

1. `coords (canonicalOn (x C p) (D − p.2))` a.e.-measurable, and TV-local convergence of
   `locField R (canonicalOn (x C p) (D − p.2))` to `locField R W` (D3⁺(i) on the Palm law);
2. `hloc`: a.s. `x C p` and the actual zoomed field `Y C p` are locally good on some
   `V ⊇ D − p.2` on which `ψ_p` is continuous, and `μ^{D−p.2}_{Y} = μ^{D−p.2}_{ofFun ψ_p + x}`;
3. `hsc0`: the local scale `a` of `x` tends to `0` in probability (D3⁺(iii));
4. `hgrow`: the canonical area of `B_s ∩ ℍ` crosses `1` strictly at `s = 1`, uniformly in
   probability (for the wedge: the area profile is continuous and strictly increasing);
5. `htight`: the canonical area of `B_ρ ∩ ℍ` is tight.

Clause (2) of D4⁺ʷ is `prop16_weak_clause2` (with `hscale` from `tendsto_scale_ratio`, and
`φ(a·) → 0` from the continuity of `𝔥₀`). Own assembly (D24's route; Sheffield,
arXiv:1012.4797, proof of Prop. 1.6, p. 25).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization Prop16Area.G

/-- The remaining inputs of D4⁺ʷ (see the module docstring). -/
def Prop16D4WInputsStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W : Ω' → FieldSample),
      IsProbabilityMeasure P' ∧ IsQuantumWedge γ γ W P' ∧
      ∃ (x : ℝ → Ω × ℝ → FieldSample) (V : ℝ → Ω × ℝ → Set ℂ),
        (∀ C, AEMeasurable (fun p => coords (canonicalOn γ (x C p) (zoomDomain D p.2)))
          (prop16Q γ h0 a b P X)) ∧
        (∀ R : ℕ, Tendsto (fun C => tvDist ((prop16Q γ h0 a b P X).map fun p =>
          locField R (canonicalOn γ (x C p) (zoomDomain D p.2)))
          (P'.map fun ω => locField R (W ω))) atTop (𝓝 0)) ∧
        (∀ C, ∀ᵐ p ∂(prop16Q γ h0 a b P X), IsLocallyGoodOn γ (V C p) (x C p) ∧
          zoomDomain D p.2 ⊆ V C p ∧ ContinuousOn (fun z => h0 (z + p.2) - h0 p.2) (V C p) ∧
          IsLocallyGoodOn γ (V C p) (zoomField γ C (ofFun h0 + X p.1) p.2) ∧
          qAreaMeasureOn γ (zoomField γ C (ofFun h0 + X p.1) p.2) (zoomDomain D p.2) =
            qAreaMeasureOn γ (ofFun (fun z => h0 (z + p.2) - h0 p.2) + x C p)
              (zoomDomain D p.2)) ∧
        (∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
          {p | ¬ (0 < scaleParamOn γ (x C p) (zoomDomain D p.2) ∧
            scaleParamOn γ (x C p) (zoomDomain D p.2) < δ)}) atTop (𝓝 0)) ∧
        (∀ κ > 0, κ < 1 → ∀ θ > 0, ∃ c > 1, ∀ᶠ C in atTop, prop16Q γ h0 a b P X {p | ¬ (
          qAreaMeasureOn γ (x C p) (zoomDomain D p.2)
              (ball 0 ((1 - κ) * scaleParamOn γ (x C p) (zoomDomain D p.2)) ∩ H) <
            ENNReal.ofReal c⁻¹ ∧ ENNReal.ofReal c <
          qAreaMeasureOn γ (x C p) (zoomDomain D p.2)
              (ball 0 ((1 + κ) * scaleParamOn γ (x C p) (zoomDomain D p.2)) ∩ H))} ≤ θ) ∧
        (∀ ρ > 0, ∀ θ > 0, ∃ M : ℝ, ∀ᶠ C in atTop, prop16Q γ h0 a b P X
          {p | ¬ qAreaMeasureOn γ (x C p) (zoomDomain D p.2)
            (ball 0 (ρ * scaleParamOn γ (x C p) (zoomDomain D p.2))) ≤ ENNReal.ofReal M} ≤ θ)

/-- `φ(a·) → 0` for Proposition 1.6's remainder (as inside `prop16_weak_clause2`). -/
theorem prop16_remainder_small {γ : ℝ} {D : Set ℂ} {c d a b : ℝ} {h0 : ℂ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}
    (hdat : Prop16Data γ D c d a b h0 P X)
    (hν : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω)) P) (x : ℝ → Ω × ℝ → FieldSample)
    (hsc0 : ∀ δ > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ (0 < scaleParamOn γ (x C p) (zoomDomain D p.2) ∧
        scaleParamOn γ (x C p) (zoomDomain D p.2) < δ)}) atTop (𝓝 0)) :
    ∀ ρ > 0, ∀ ε > 0, Tendsto (fun C => prop16Q γ h0 a b P X {p | ¬ ∀ z ∈ zoomDomain D p.2,
      ‖z‖ < ρ * scaleParamOn γ (x C p) (zoomDomain D p.2) →
        |h0 (z + p.2) - h0 p.2| ≤ ε}) atTop (𝓝 0) := by
  obtain ⟨-, -, -, -, -, -, hh0, -, -, hpos, hfin⟩ := hdat
  have hQ : IsProbabilityMeasure (prop16Q γ h0 a b P X) :=
    isProbabilityMeasure_prop16Law' hν hpos hfin
  have hta : ∀ᵐ p ∂(prop16Q γ h0 a b P X), p.2 ∈ Ioo a b :=
    ae_prop16Law_of_ae (G := fun _ t => t ∈ Ioo a b) (aemeasurable_prop16Kernel' hν hfin)
      (fun ω => sFinite_prop16Nu γ h0 a b (X ω)) (fun ω => prop16Nu_compl_Ioo γ h0 a b (X ω))
      (ae_of_all _ fun _ _ ht => ht)
  intro ρ hρ ε hε
  have hs' : ∀ r > 0, Tendsto (fun C => prop16Q γ h0 a b P X
      {p | ¬ scaleParamOn γ (x C p) (zoomDomain D p.2) < r}) atTop (𝓝 0) := fun r hr =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hsc0 r hr) (fun _ => bot_le)
      fun C => measure_mono fun p hp h => hp h.2
  have := tendsto_prob_osc (prop16Q γ h0 a b P X) hh0 subset_union_right Prod.snd
    measurable_snd hta (fun C p => scaleParamOn γ (x C p) (zoomDomain D p.2)) hs' hρ hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le)
    fun C => measure_mono fun p hp h => hp fun z hz hzn => h z (Or.inl hz) hzn

/-- **D4⁺ʷ from its remaining inputs.** -/
theorem prop16TVWeak_of_inputs (hMeas : Prop16NuMeasStmt) (hIn : Prop16D4WInputsStmt) :
    Prop16TVWeakStmt := by
  intro γ D c d a b h0 Ω _ P X hdat
  have hν := hMeas γ D c d a b h0 P X hdat
  obtain ⟨Ω', _, P', W, hP', hW, x, V, hZm, hTV, hloc, hsc0, hgrow, htight⟩ :=
    hIn γ D c d a b h0 P X hdat
  obtain ⟨hγ, -, ⟨hDo, -, -, hDH, -⟩, -⟩ := id hdat
  have hZo : ∀ t : ℝ, IsOpen (zoomDomain D t) := fun t =>
    hDo.preimage (continuous_id.add continuous_const)
  have hZH : ∀ t : ℝ, zoomDomain D t ⊆ H := fun t z hz => by
    have h1 : (0 : ℝ) < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using h1
  have hφ := prop16_remainder_small hdat hν x hsc0
  have hscale := tendsto_scale_ratio (prop16Q γ h0 a b P X) hγ x
    (fun _ p => fun z => h0 (z + p.2) - h0 p.2) (fun _ p => zoomDomain D p.2) V
    (fun C => (hloc C).mono fun p h => ⟨h.1, hZo p.2, hZH p.2, h.2.1, h.2.2.1⟩) hφ
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hsc0 1 one_pos)
      (fun _ => bot_le) fun C => measure_mono fun p hp h => hp h.1) hgrow
  exact ⟨Ω', _, P', W, hP', hW, fun C p => canonicalOn γ (x C p) (zoomDomain D p.2), hZm, hTV,
    prop16_weak_clause2 hdat hν x V hloc hsc0 hscale htight⟩

end Prop16Asm

end QuantumZipper
