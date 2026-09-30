import QuantumZipper.Proofs.Section5.Prop16DomCouple
import QuantumZipper.Proofs.Section5.Prop16DomCoupleFubini

/-!
# Proposition 1.6, node DOM-COUPLE (part 4): DOM-b from a continuous version

`gaussContFubini_of_version`: the sub-node `GaussContFubiniStmt` (continuous version + stochastic
Fubini, `Prop16DomCoupleNodes.lean`) follows from its version half `GaussContVersionStmt`
(Kolmogorov: a version of `z ↦ W(H z)` with continuous paths on `O ∩ Hbar`, measurable
coordinates), by the stochastic Fubini theorem `gaussFubini_core` applied on the compact carrier
`K` (as a subtype; joint measurability by `measurable_uncurry_of_continuous_of_measurable`).

`GaussContVersionStmt` is proved in `Prop16DomCoupleGlue.lean` (`gaussContVersion_holds`).
Source: Kolmogorov's continuity criterion,
Revuz–Yor, *Continuous martingales and Brownian motion*, Ch. I, Thm (2.1) (index set a cube in
`ℝ^d`), Karatzas–Shreve Problem 2.2.9; the repository has the `d ≤ 4` dyadic version with
global moment bounds, `KolmD.exists_continuous_modification_D`
(`Proofs/LQG/RegularSampleKolmogorov.lean`); what remains is localisation to `O ∩ Hbar` (e.g.
compose `H` with coordinatewise clamps onto countably many closed squares inside `O ∩ Hbar`,
apply the global theorem to each, and glue the versions, which agree a.s. on overlaps).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped RealInnerProductSpace NNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Sub-node DOM-b1: continuous version** (proved as `gaussContVersion_holds`). For an
isonormal process `W` on `E` and
`H` Lipschitz on the compact subsets of `O ∩ Hbar` (`O` open), `z ↦ W(H z)` has a version `G`
with `G ω` continuous on `O ∩ Hbar` for every `ω` and measurable coordinates. Source: Revuz–Yor
Ch. I Thm (2.1) (Kolmogorov's continuity criterion). -/
def GaussContVersionStmt : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : E → Ω → ℝ) (O : Set ℂ) (H : ℂ → E),
    IsOpen O → (∀ x, Measurable (W x)) →
    (∀ {ι : Type} [Fintype ι] (τ : ι → E) (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * W (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) P) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ O ∩ Hbar → ∃ C : ℝ≥0, LipschitzOnWith C H K) →
    ∃ G : Ω → ℂ → ℝ, (∀ ω, ContinuousOn (G ω) (O ∩ Hbar)) ∧
      (∀ z, Measurable fun ω => G ω z) ∧
      ∀ z ∈ O ∩ Hbar, (fun ω => G ω z) =ᵐ[P] W (H z)

/-- Integrals over a carrier, as integrals over the subtype. -/
theorem integral_comap_subtype_of_carrier {μ : Measure ℂ} {K : Set ℂ} (hKm : MeasurableSet K)
    (hμK : μ Kᶜ = 0) (f : ℂ → ℝ) :
    ∫ z : K, f z ∂(μ.comap Subtype.val) = ∫ z, f z ∂μ := by
  rw [integral_subtype_comap hKm f, Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμK)]

/-- **DOM-b from DOM-b1** (stochastic Fubini, `gaussFubini_core`). -/
theorem gaussContFubini_of_version (hV : GaussContVersionStmt) : GaussContFubiniStmt := by
  intro E _ _ _ Ω _ P _ W O H hO hWm hW hLip
  obtain ⟨G, hGc, hGm, hGv⟩ := hV P W O H hO hWm hW hLip
  refine ⟨G, hGc, fun μ _ hK k hk => ?_⟩
  obtain ⟨K, hKc, hKO, hμK⟩ := hK
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  set ν : Measure K := μ.comap Subtype.val with hν
  have : IsFiniteMeasure ν :=
    ⟨by rw [hν, (MeasurableEmbedding.subtype_coe hKm).comap_apply]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := hLip K hKc hKO
  have hHc : Continuous fun z : K => H z := hC.continuousOn.domRestrict
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hC.continuousOn
  have hGK : Measurable (uncurry fun ω (z : K) => G ω z) := by
    have h1 : Measurable (uncurry fun (z : K) ω => G ω z) :=
      measurable_uncurry_of_continuous_of_measurable
        (fun ω => ((hGc ω).mono hKO).domRestrict) (fun z => hGm z)
    exact h1.comp measurable_swap
  have hcore := gaussFubini_core hW ν (fun z : K => H z) (M := M) (fun z => hM z z.2)
    ((hHc.comp continuous_fst).inner (hHc.comp continuous_snd)).measurable
    (fun x => (hHc.inner continuous_const).measurable) (fun ω (z : K) => G ω z) hGK
    (fun z => hGv z (hKO z.2)) hWm k
    (fun x => by rw [hk x, integral_comap_subtype_of_carrier hKm hμK (fun z => ⟪H z, x⟫)])
  filter_upwards [hcore] with ω hω
  rw [← integral_comap_subtype_of_carrier hKm hμK]
  exact hω

end Prop16Asm

end QuantumZipper
