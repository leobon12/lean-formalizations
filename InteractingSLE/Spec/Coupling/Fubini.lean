import MathFin.Probability.Martingales.MartingaleSetIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Integrals of martingale families against a parameter (Fubini for martingales)

Packet PROVE-T11-L311 (Specification §3.3, L542–L548: "Stochastic Fubini then gives `d(𝔥_t, φ) = …`"). The
test-function averages `(𝔥_t, φ) = ∫ φ(z) 𝔥_t(z) dz` and `∬ φ(y) φ(z) (𝔥_t(y) 𝔥_t(z) + G_t(y, z))` are integrals of
families of martingales against a parameter. For bounded (dominated) families no stochastic Fubini theorem is needed:
set integrals commute with the parameter integral.

* `measurable_uncurry_of_continuousOn`: Carathéodory's criterion when continuity in the parameter only holds on a
  closed set `K` and the family is constant off `K`;
* `martingale_integral_of_forall`: if `(i, ω) ↦ Y_t(i, ω)` is `(Borel ⊗ 𝓖_t)`-measurable, dominated by an
  integrable `g(i)`, and almost every `Y(i)` has constant set integrals over `𝓖_s`-sets, then
  `t ↦ ∫ Y_t(i, ·) dμ(i)` is a martingale.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

/-- **Carathéodory's criterion on a closed set.** Let `g : ι → α → β` be continuous in the parameter on a closed
set `K` (for each `a`), measurable in `a` for each parameter in `K`, and equal to a constant `c` off `K`. Then
`(i, a) ↦ g i a` is jointly measurable. -/
theorem measurable_uncurry_of_continuousOn {ι α β : Type*} [TopologicalSpace ι]
    [TopologicalSpace.MetrizableSpace ι] [SecondCountableTopology ι] [MeasurableSpace ι]
    [OpensMeasurableSpace ι] [mα : MeasurableSpace α] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    {K : Set ι} (hK : IsClosed K) {g : ι → α → β} (c : β)
    (hcont : ∀ a, ContinuousOn (fun i => g i a) K) (hmeas : ∀ i ∈ K, Measurable (g i))
    (hout : ∀ i ∉ K, ∀ a, g i a = c) : Measurable (fun p : ι × α => g p.1 p.2) := by
  classical
  set gK : K → α → β := fun i a => g i a with hgK
  have hgKm : Measurable (Function.uncurry gK) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun a => (hcont a).domRestrict) (fun i => hmeas i i.2)
  have hS : MeasurableSet (K ×ˢ (univ : Set α)) := hK.measurableSet.prod MeasurableSet.univ
  have hf : Measurable (fun q : ↥(K ×ˢ (univ : Set α)) =>
      Function.uncurry gK (⟨q.1.1, (mem_prod.1 q.2).1⟩, q.1.2)) :=
    hgKm.comp ((measurable_subtype_coe.fst.subtype_mk).prodMk measurable_subtype_coe.snd)
  have e : (fun p : ι × α => g p.1 p.2) = fun p => if hp : p ∈ K ×ˢ (univ : Set α) then
      Function.uncurry gK (⟨p.1, (mem_prod.1 hp).1⟩, p.2) else
      (fun _ : ↥((K ×ˢ (univ : Set α))ᶜ) => c) ⟨p, hp⟩ := by
    funext p
    by_cases hp : p ∈ K ×ˢ (univ : Set α)
    · simp only [hp, ↓reduceDIte]; rfl
    · simp only [hp, ↓reduceDIte]
      exact hout p.1 (fun h => hp ⟨h, mem_univ _⟩) p.2
  rw [e]
  exact Measurable.dite hf measurable_const hS

/-- The parameter integral of a jointly measurable function is measurable (any measurable space on `Ω'`). -/
theorem measurable_integral_param {ι Ω' : Type*} [MeasurableSpace ι] [MeasurableSpace Ω']
    {μ : Measure ι} [SFinite μ] {f : ι → Ω' → ℝ} (hf : Measurable fun p : ι × Ω' => f p.1 p.2) :
    Measurable (fun ω => ∫ i, f i ω ∂μ) :=
  hf.stronglyMeasurable.integral_prod_left.measurable

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Fubini for martingales.** Let `Y_t(i, ω)` be `(m_ι ⊗ 𝓖_t)`-measurable, dominated by an integrable `g(i)`
for almost every `i`, and let almost every `Y(i)` have constant set integrals over `𝓖_s`-sets. Then
`t ↦ ∫ Y_t(i, ·) dμ(i)` is a `𝓖`-martingale. -/
theorem martingale_integral_of_forall [IsFiniteMeasure P] {ι : Type*} [mι : MeasurableSpace ι]
    {μ : Measure ι} [SFinite μ] {𝓖 : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → ι → Ω → ℝ}
    (hmeas : ∀ t, Measurable[mι.prod (𝓖 t)] (fun p : ι × Ω => Y t p.1 p.2))
    {g : ι → ℝ} (hg : Integrable g μ) (hbd : ∀ᵐ i ∂μ, ∀ t ω, |Y t i ω| ≤ g i)
    (hset : ∀ᵐ i ∂μ, ∀ ⦃s t : ℝ≥0⦄, s ≤ t → ∀ S : Set Ω, MeasurableSet[𝓖 s] S →
      ∫ ω in S, Y s i ω ∂P = ∫ ω in S, Y t i ω ∂P) :
    Martingale (fun t ω => ∫ i, Y t i ω ∂μ) 𝓖 P := by
  have hle : ∀ t, mι.prod (𝓖 t) ≤ mι.prod mΩ := fun t =>
    sup_le_sup_left (MeasurableSpace.comap_mono (𝓖.le t)) _
  have hmeas' : ∀ t, Measurable (fun p : ι × Ω => Y t p.1 p.2) := fun t =>
    (hmeas t).mono (hle t) le_rfl
  have hbd' : ∀ᵐ p ∂(μ.prod P), ∀ t ω, |Y t p.1 ω| ≤ g p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hbd
  have hgP : Integrable (fun p : ι × Ω => g p.1 * (1 : ℝ)) (μ.prod P) :=
    hg.mul_prod (integrable_const (1 : ℝ))
  have hint : ∀ t, Integrable (fun p : ι × Ω => Y t p.1 p.2) (μ.prod P) := fun t =>
    Integrable.mono' hgP (hmeas' t).aestronglyMeasurable (by
      filter_upwards [hbd'] with p hp
      rw [Real.norm_eq_abs, mul_one]; exact hp t p.2)
  have hgi : ∀ t ω, |∫ i, Y t i ω ∂μ| ≤ ∫ i, |g i| ∂μ := fun t ω => by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (ae_of_all _ fun _ => norm_nonneg _) hg.abs ?_)
    filter_upwards [hbd] with i hi
    rw [Real.norm_eq_abs]; exact (hi t ω).trans (le_abs_self _)
  refine (martingale_iff_setIntegral_eq).2 ⟨fun t => ?_, fun t => ?_, fun s t hst S hS => ?_⟩
  · exact (@measurable_integral_param ι Ω mι (𝓖 t) μ _ (Y t) (hmeas t)).stronglyMeasurable
  · exact Integrable.of_bound (measurable_integral_param (hmeas' t)).aestronglyMeasurable _
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgi t ω)
  · have hswap : ∀ r, ∫ ω in S, ∫ i, Y r i ω ∂μ ∂P = ∫ i, ∫ ω in S, Y r i ω ∂P ∂μ := fun r => by
      have h : Integrable (Function.uncurry (Y r)) (μ.prod (P.restrict S)) := by
        have := (hint r).restrict (s := univ ×ˢ S)
        rwa [← Measure.prod_restrict, Measure.restrict_univ] at this
      exact (integral_integral_swap h).symm
    rw [hswap s, hswap t]
    refine integral_congr_ae ?_
    filter_upwards [hset] with i hi
    exact hi hst S hS

end Martingale

end Coupling

end InteractingSLE
