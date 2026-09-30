import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocDet
import QuantumZipper.Proofs.Zipper.D3PlusN2TmZScale

/-!
# N2-zero, node N2Z-MODELLOC from the model's almost sure regularity

Task N2-MODELLOC. `n2ZModelLoc_of_reg : N2ZModelRegStmt → N2ZModelLocStmt`.

`N2ZModelRegStmt` collects the almost sure properties of the model field
`h_L = n2Model γ α L r X ω` used by the deterministic window transfer `n2_modelLoc_det`
(`D3PlusN2ModelLocDet.lean`):

* local goodness on `halfDisc r` (`Prop16Area.G.IsLocallyGoodOn`: on dyadic circles inside the
  half-disc, `h_L = X + (−H_ω + α(−log‖·‖) + L/γ)` with `X` good and `H_ω` the harmonic part,
  `d3PlusN2HarmPart_holds`);
* agreement near `0` (radius `r/2`) with a regular sample `y'` (witness `F`) whose test pairings
  have continuum radius limits `lim_{t→0⁺} ∫ F(c u, t) f(u) du` for every scale `c > 0` and every
  test function `f = ±ρ`, `ρ ∈ TestFun H`.

The last clause is needed because the window reader `gK` reads the embedded field through the
dyadic radii `2^{-k}`, i.e. the model through the radii `a 2^{-k}` (`a` = embedding scale), while
`TmRichN1` reads the model through `2^{-k}`: the two regularized pairings agree when the
continuum limit exists (`F1.rescale_rescale_eq_of_lim`). Since the node's event quantifies over
all test functions at once, the limit is needed simultaneously for all `ρ` (per-test-function
versions, e.g. `F1.ae_contPair_plain`, do not suffice).

Proof of the reduction (own elementary argument): off the null set of `N2ZModelRegStmt`, the
disagreement on the window event forces `n2EmbScale > r/(2K)`, whose probability tends to `0`
(`tendsto_prob_n2EmbScale_gt`). Source for the route: Duplantier–Miller–Sheffield
arXiv:1409.7055, proof of Prop. 4.8 (p. 79).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

open Prop16Area.G

/-- **Node N2Z-MODELREG**: almost sure local goodness and regularity (with continuum pairing
limits) of the model field, simultaneously for all levels `L`. -/
def N2ZModelRegStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ᵐ ω ∂P, ∀ L : ℝ, IsLocallyGoodOn γ (halfDisc r) (n2Model γ α L r X ω) ∧
      ∃ (y' : FieldSample) (F : ℂ × ℝ → ℝ), AgreeNear (n2Model γ α L r X ω) y' (r / 2) ∧
        IsRegularWith y' F ∧ ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H,
          ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L' : ℝ, Tendsto (fun t => ∫ u, F ((c : ℂ) * u, t)
            ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L')

theorem n2EmbScale_pos {γ α L r : ℝ} (hr : 0 < r) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) :
    0 < n2EmbScale γ α L r X ω := mul_pos hr (Real.exp_pos _)

/-- **N2Z-MODELLOC from the model's almost sure regularity.** -/
theorem n2ZModelLoc_of_reg (hReg : N2ZModelRegStmt) : N2ZModelLocStmt := by
  intro γ α r Ω _ P _ X hγ hγ2 hα hr hX K R hK
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hδ : 0 < r / 2 / K := by positivity
  set N := {ω | ¬ ∀ L : ℝ, IsLocallyGoodOn γ (halfDisc r) (n2Model γ α L r X ω) ∧
      ∃ (y' : FieldSample) (F : ℂ × ℝ → ℝ), AgreeNear (n2Model γ α L r X ω) y' (r / 2) ∧
        IsRegularWith y' F ∧ ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H,
          ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L' : ℝ, Tendsto (fun t => ∫ u, F ((c : ℂ) * u, t)
            ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L')} with hN
  have hN0 : P N = 0 := ae_iff.1 (hReg γ α r P X hγ hγ2 hα hr hX)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_prob_n2EmbScale_gt hγ hα hr hX hδ) (fun _ => bot_le) (fun L => ?_)
  calc _ ≤ P ({ω | r / 2 / K < n2EmbScale γ α L r X ω} ∪ N) := measure_mono ?_
    _ ≤ P {ω | r / 2 / K < n2EmbScale γ α L r X ω} + P N := measure_union_le _ _
    _ = P {ω | r / 2 / K < n2EmbScale γ α L r X ω} := by rw [hN0, add_zero]
  intro ω hω
  obtain ⟨hG, hne⟩ := hω
  by_cases hbad : ω ∈ N
  · exact Or.inr hbad
  refine Or.inl ?_
  by_contra hle
  simp only [mem_ofPred_eq, not_lt] at hle
  have hgood : ∀ L : ℝ, IsLocallyGoodOn γ (halfDisc r) (n2Model γ α L r X ω) ∧
      ∃ (y' : FieldSample) (F : ℂ × ℝ → ℝ), AgreeNear (n2Model γ α L r X ω) y' (r / 2) ∧
        IsRegularWith y' F ∧ ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H,
          ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L' : ℝ, Tendsto (fun t => ∫ u, F ((c : ℂ) * u, t)
            ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L') := by
    by_contra h; exact hbad h
  obtain ⟨hloc, y', F, hag, hF, hlim⟩ := hgood L
  have ha := n2EmbScale_pos (γ := γ) (α := α) (L := L) hr X ω
  have hKa : n2EmbScale γ α L r X ω * K ≤ r / 2 := by
    rwa [le_div_iff₀ hK'] at hle
  exact hne (n2_modelLoc_det (p := (localZ X r ω, circData α fun _ => 0)) hγ ha hK hKa
    (half_le_self hr.le) hloc hag hF (fun c hc ρ _ f hf => hlim c hc ρ f hf) hG)

end D3Plus
end QuantumZipper
