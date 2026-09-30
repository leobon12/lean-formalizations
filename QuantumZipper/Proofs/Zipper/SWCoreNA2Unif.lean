import QuantumZipper.Proofs.Thm18.G1RCEval

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2 (N1): uniform convergence of the regularized pairings along a finite-parameter family

Task SWC-NA (`handoff/SW-CORE.md` §5), step N1 for finite-parameter families. For a jointly
continuous family `Φ : ℝⁿ × Θ → ℍ̄` (a pushed-circle family, `μ_q = m.map (Φ q)`) whose
circle-smoothed family has the Kolmogorov bounds `G1RC.FamilyBounds` (energy Hölder in all
parameters, uniformly on boxes), almost surely, for **every compact** set `K` of parameters,

  `∫ avgReg x j dμ_q → Y₀(q)` as `j → ∞`, **uniformly in `q ∈ K`**
  (`swcNA2_tendstoUniformlyOn_avgReg`, hence `UniformCauchySeqOn`, `swcNA2_uniformCauchy`),

where `Y₀` is a continuous modification of `q ↦ X(μ_q)`. The continuous smoothing radius version
(`swcNA2_tendstoUniformlyOn_smoothing`) is the uniform form of the repository's
`Thm18Asm.G1RC.exists_smoothing_limit`: the same proof (the `(n+1)`-parameter Kolmogorov
modification `Y` agrees with the smoothed pairings on `{t > 0}`), plus Heine–Cantor for `Y` on
`K × [0,1]` (mathlib `Continuous.tendstoUniformly`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (Kolmogorov continuity of
circle averages); Sheffield–Wang arXiv:1605.06171, Lemma 3.5 (pathwise control of the
regularization over a family of maps). The bookkeeping is an own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC KolmD KolmG CircleFubini WedgeTK

variable {n : ℕ} {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
  {m : Measure Θ} [IsProbabilityMeasure m] {S : Set Θ} {Φ : (Fin n → ℝ) → Θ → ℂ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample} {G : Ω → ℂ × ℝ → ℝ}

/-- **Uniform smoothing limit along a finite-parameter family.** -/
theorem swcNA2_tendstoUniformlyOn_smoothing (hΦ : Continuous (uncurry Φ))
    (hΦH : ∀ q θ, Φ q θ ∈ Hbar) (hS : IsCompact S) (hmS : m Sᶜ = 0)
    {β : ℝ} (hβ : 0 < β) (hB : FamilyBounds (smoothFam m Φ) β) (hX : IsFreeGFFModConstH X P)
    (hG : IsRegVersion X P G) :
    ∃ Y₀ : (Fin n → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y₀ q ω) ∧
      (∀ q, (fun ω => Y₀ q ω) =ᵐ[P] fun ω => X ω (m.map (Φ q))) ∧
      ∀ᵐ ω ∂P, ∀ K : Set (Fin n → ℝ), IsCompact K →
        TendstoUniformlyOn (fun t q => ∫ u, G ω (u, t) ∂(m.map (Φ q))) (fun q => Y₀ q ω)
          (𝓝[>] 0) K := by
  obtain ⟨Y, hYc, hYV, -⟩ := exists_modification_family hβ hB hX
  have hsnoc : Continuous fun x : (Fin n → ℝ) × ℝ => (Fin.snoc x.1 x.2 : Fin (n + 1) → ℝ) :=
    continuous_fst.finSnoc (A := fun _ => ℝ) continuous_snd
  refine ⟨fun q ω => Y (Fin.snoc q 0) ω, fun ω => (hYc ω).comp
    (continuous_id.finSnoc (A := fun _ => ℝ) continuous_const), fun q => ?_, ?_⟩
  · filter_upwards [hYV (Fin.snoc q 0)] with ω h
    rw [h, smoothFam_snoc_zero]
  set U : Set (Fin (n + 1) → ℝ) := {p | 0 < p (Fin.last n)} with hU
  set L : Ω → (Fin (n + 1) → ℝ) → ℝ := fun ω p =>
    ∫ θ, G ω (Φ (Fin.init p) θ, p (Fin.last n)) ∂m with hL
  obtain ⟨D, hDc, hDU, hUD⟩ := TopologicalSpace.exists_countable_dense_subset U
  have hpt : ∀ p ∈ D, ∀ᵐ ω ∂P, L ω p = Y p ω := by
    intro p hp
    have hp' : 0 < p (Fin.last n) := hDU hp
    have hc := continuous_Phi hΦ (Fin.init p)
    have hsub : Φ (Fin.init p) '' S ⊆ Hbar := by rintro _ ⟨θ, -, rfl⟩; exact hΦH _ θ
    filter_upwards [ae_integral_G_eq hX hG hp' (m.map (Φ (Fin.init p))) (hS.image hc)
      hsub (map_compl_image hΦ hS hmS _), hYV p] with ω h1 h2
    simp only [L]
    rw [← integral_map_Phi hΦ hΦH hS hmS _ (hG.continuousOn_slice ω hp'), h1, h2,
      smoothFam_of_pos m Φ hp']
  have hall : ∀ᵐ ω ∂P, ∀ p ∈ D, L ω p = Y p ω :=
    (eventually_countable_ball hDc).2 hpt
  filter_upwards [hall] with ω hω K hK
  have hEq : EqOn (L ω) (fun p => Y p ω) U :=
    Set.EqOn.of_subset_closure hω (continuousOn_smoothed hΦ hΦH hS hmS hG ω)
      (hYc ω).continuousOn hDU hUD
  -- Heine–Cantor on `ℝ × K`
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  set f : ℝ → K → ℝ := fun t q => Y (Fin.snoc (q : Fin n → ℝ) t) ω with hf
  have hfc : Continuous (uncurry f) :=
    (hYc ω).comp (hsnoc.comp ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))
  have hunif : TendstoUniformly f (f 0) (𝓝 0) := hfc.tendstoUniformly f 0
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  intro u hu
  filter_upwards [nhdsWithin_le_nhds (hunif u hu), self_mem_nhdsWithin] with t h (ht : 0 < t) q
  have htU : (Fin.snoc (q : Fin n → ℝ) t : Fin (n + 1) → ℝ) ∈ U := by simp [U, ht]
  have := hEq htU
  simp only [L, Fin.init_snoc, Fin.snoc_last] at this
  have e : ∫ u, G ω (u, t) ∂(m.map (Φ q)) = f t q := by
    simp only [f]
    rw [integral_map_Phi hΦ hΦH hS hmS _ (hG.continuousOn_slice ω ht)]
    exact this
  simp only [Function.comp_apply, e]
  exact h q

/-- On a regular sample, `avgReg x k` is the regular version at radius `2^{-k}` on `ℍ̄`. -/
theorem swcNA2_avgReg_eq {x : FieldSample} {F : ℂ × ℝ → ℝ} (h : IsRegularWith x F) (k : ℕ)
    {z : ℂ} (hz : z ∈ Hbar) : avgReg x k z = F (z, radius k) :=
  (h.2.1 k z hz).limUnder_eq

omit [IsProbabilityMeasure P] in
/-- **(N1) for finite-parameter families**: a.s., for every compact set `K` of parameters, the
pairings `∫ avgReg x j dμ_q` converge as `j → ∞`, uniformly in `q ∈ K`, to a continuous
modification of `q ↦ X(μ_q)`. -/
theorem swcNA2_tendstoUniformlyOn_avgReg [IsProbabilityMeasure P] (hΦ : Continuous (uncurry Φ))
    (hΦH : ∀ q θ, Φ q θ ∈ Hbar) (hS : IsCompact S) (hmS : m Sᶜ = 0)
    {β : ℝ} (hβ : 0 < β) (hB : FamilyBounds (smoothFam m Φ) β) (hX : IsFreeGFFModConstH X P) :
    ∃ Y₀ : (Fin n → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y₀ q ω) ∧
      (∀ q, (fun ω => Y₀ q ω) =ᵐ[P] fun ω => X ω (m.map (Φ q))) ∧
      ∀ᵐ ω ∂P, ∀ K : Set (Fin n → ℝ), IsCompact K →
        TendstoUniformlyOn (fun j q => ∫ u, avgReg (X ω) j u ∂(m.map (Φ q)))
          (fun q => Y₀ q ω) atTop K := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  obtain ⟨Y₀, hc, hV, hU⟩ := swcNA2_tendstoUniformlyOn_smoothing hΦ hΦH hS hmS hβ hB hX hG
  refine ⟨Y₀, hc, hV, ?_⟩
  filter_upwards [hU, hG.reg] with ω hω hreg K hK
  have hrad : Tendsto (fun j : ℕ => radius j) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨by
      have : Tendsto (fun j : ℕ => (2 : ℝ)⁻¹ ^ j) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa [radius] using this, Eventually.of_forall fun j => radius_pos j⟩
  intro u hu
  filter_upwards [hrad.eventually ((hω K hK) u hu)] with j hj q hq
  have hae : ∀ᵐ v ∂(m.map (Φ q)), v ∈ Hbar := by
    refine (ae_map_iff (p := fun v => v ∈ Hbar) (continuous_Phi hΦ q).aemeasurable
      (measurableSet_le measurable_const Complex.measurable_im)).2 ?_
    exact Eventually.of_forall fun θ => hΦH q θ
  have e : ∫ v, avgReg (X ω) j v ∂(m.map (Φ q)) = ∫ v, G ω (v, radius j) ∂(m.map (Φ q)) :=
    integral_congr_ae (hae.mono fun v hv => swcNA2_avgReg_eq hreg j hv)
  simp only [e]
  exact hj q hq

end SWCore
end QuantumZipper
