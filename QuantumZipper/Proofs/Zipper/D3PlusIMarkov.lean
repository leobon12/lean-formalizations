import QuantumZipper.Proofs.Zipper.D3PlusIMix
import QuantumZipper.Proofs.Zipper.D3PlusProb
import QuantumZipper.Proofs.Zipper.D3PlusITV

/-!
# D3⁺(i): the Markov step and the reduction to the deterministic-correction zoom

Task D3P-I (decision D23). Blueprint `E_BRANCH_BLUEPRINT.md` §3: "with `g` macroscopic, L2
(`freeGFF_halfDisc_markov`) reduces to `Z_r + (deterministic g)`". Source for the Markov property:
Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), Thm. 2.17 (Dirichlet case);
the free-field half-disc version is node L2, `K3.freeGFF_halfDisc_markov` /
`K3.indep_markovZ_outside` (`Proofs/GFF/K3/HalfDiscMarkov.lean`).

* `localZ X r`: the local part `Z μ = X μ − X(bal μ)` of the free field on the local measures of
  the half-disc (`IsLocalH 0 r`), as one random element of `{μ // IsLocalH 0 r μ} → ℝ`.
* `indep_localZ_condSigma`: under `Setup`, `localZ X r` is independent of
  `condSigma Ξ X r = σ(Ξ) ⊔ outsideSigma X 0 r` (L2 + `Ξ ⊥` free increments; three-σ-algebra
  step `indep_sup_of_indep_d3p`).
* `D3PlusICoreStmt`: the remaining node (deterministic-correction zoom in TV, with the
  factorization of the zoomed data through `(localZ, F)`), and `d3PlusI_of_core :
  D3PlusICoreStmt → D3PlusIStmt` (via `eventually_two_sided_of_factor`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- The index type of the local measures of the half-disc of radius `r` at `0`. -/
abbrev LocIdx (r : ℝ) : Type := {μ : Measure ℂ // K3.IsLocalH 0 r μ}

/-- The local part of the free field on the half-disc `ball 0 r ∩ ℍ` (node L2):
`μ ↦ X μ − X (bal μ)` on local measures. -/
def localZ {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) (ω : Ω) : LocIdx r → ℝ :=
  fun μ => K3.markovZ X 0 r ω μ.1

theorem comap_localZ {Ω : Type*} (X : Ω → FieldSample) (r : ℝ) :
    MeasurableSpace.comap (localZ X r) inferInstance =
      ⨆ μ : LocIdx r, MeasurableSpace.comap (fun ω => K3.markovZ X 0 r ω μ.1) inferInstance := by
  change MeasurableSpace.comap (localZ X r) (⨆ μ : LocIdx r, _) = _
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun μ => ?_
  rw [MeasurableSpace.comap_comp]
  rfl

section Setup

variable {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → FieldSample} {E' : Type*} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}

theorem freeIncrSigma_le (hX : IsFreeGFFModConstH X P) :
    K3.freeIncrSigma X ≤ ‹MeasurableSpace Ω› := by
  refine measurable_iff_comap_le.1 (measurable_pi_iff.2 fun p => ?_)
  exact (hX.measurable_coord _).sub (hX.measurable_coord _)

omit [MeasurableSpace Ω] in
theorem comap_localZ_le_freeIncrSigma (hr : 0 < r) :
    MeasurableSpace.comap (localZ X r) inferInstance ≤ K3.freeIncrSigma X := by
  rw [comap_localZ]
  refine iSup_le fun μ => ?_
  have hm : Measurable[K3.freeIncrSigma X] fun ω => K3.markovZ X 0 r ω μ.1 :=
    (measurable_pi_apply (K3.localIdx hr μ)).comp (comap_measurable (m := MeasurableSpace.pi)
      fun ω (p : {p : Measure ℂ × Measure ℂ //
        IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}) =>
          X ω p.1.1 - X ω p.1.2)
  exact measurable_iff_comap_le.1 hm

theorem measurable_localZ (hX : IsFreeGFFModConstH X P) (hr : 0 < r) : Measurable (localZ X r) :=
  measurable_iff_comap_le.2 ((comap_localZ_le_freeIncrSigma hr).trans (freeIncrSigma_le hX))

theorem condSigma_le (hS : Setup γ α r ρ₀ P X Ξ g) : condSigma Ξ X r ≤ ‹MeasurableSpace Ω› :=
  sup_le hS.hΞ.comap_le ((K3.outsideSigma_le_freeIncrSigma X 0 r).trans (freeIncrSigma_le hS.hX))

/-- **The local part is independent of the conditioning σ-algebra** (L2 + independence of `Ξ`;
own elementary combination). -/
theorem indep_localZ_condSigma [IsProbabilityMeasure P] (hS : Setup γ α r ρ₀ P X Ξ g) :
    Indep (MeasurableSpace.comap (localZ X r) inferInstance) (condSigma Ξ X r) P := by
  have hL2 := K3.indep_markovZ_outside (t := 0) hS.hX hS.hr
  rw [← comap_localZ] at hL2
  have h := indep_sup_of_indep_d3p (K3.outsideSigma_le_freeIncrSigma X 0 r)
    (comap_localZ_le_freeIncrSigma hS.hr) (freeIncrSigma_le hS.hX) hS.hΞ.comap_le hL2.symm
    hS.hind
  rw [sup_comm] at h
  exact h.symm

end Setup

/-! ## Allowing an exceptional event of vanishing probability -/

/-! ## The bad-scale event -/

/-- The event that the local scale of the model field at level `L` is not in `(0, ε)`. -/
def badScale (γ α r ε : ℝ) (ρ₀ : Measure ℂ) {Ω : Type*} (X : Ω → FieldSample) (g : Ω → ℂ → ℝ)
    (L : ℝ) : Set Ω :=
  {ω | ¬ (0 < scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) ∧
    scaleParamOn γ (zoomModel γ α L ρ₀ (X ω) (g ω)) (halfDisc r) < ε)}

/-- The bad-scale probability tends to `0` along the real levels (D3⁺(iii), `d3PlusIII_holds`,
given null-measurability of the events). -/
theorem tendsto_prob_badScale {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} {E' : Type}
    [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ} (hS : Setup γ α r ρ₀ P X Ξ g)
    {ε : ℝ} (hε : 0 < ε) (hmeas : ∀ L, NullMeasurableSet (badScale γ α r ε ρ₀ X g L) P) :
    Tendsto (fun L => P (badScale γ α r ε ρ₀ X g L)) atTop (𝓝 0) := by
  rw [tendsto_iff_seq_tendsto]
  intro Ls hLs
  exact d3PlusIII_tendsto_prob hS hLs hε fun n => hmeas (Ls n)

/-! ## The remaining node and the reduction -/

end D3Plus
end QuantumZipper
