/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA32Law

/-!
# A.3.2, (G3) in the strip, part 2: the law of the strip driver is the `f(u) du`-mixture of the forced laws

Packet PROVE-ZHAN-A32. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L686–L697, ruling R38; follow-up note p. 13): "Consequently the
original strip law is the mixture, with density `f(u)du`, of these forced laws, first on each finite-time
sigma-algebra and then on the full path sigma-algebra by a monotone class."

The strip driver path is `ξ = (√κ B_t + σ t)_{t ≥ 0}` (a point of `ℝ≥0 → ℝ`, product σ-algebra). The forced law of
parameter `u` is the law of the forced driver `forcedDrv κ σ u B` (strip SLE with charge `−4` at `u + iπ`, `2` at the right
end, `κ − 4` at the left end, driven by the same Brownian motion `B`; `MixtureA32Law.lean`). The mixture is realized
on the product space `ℝ × Ω` with the probability measure `f(u) du ⊗ P` (`mixLaw`):

* **`map_stripPath_eq_mixLaw`**: `Law_P(ξ) = mixLaw`, i.e. for every measurable set `C` of paths,
  `P(ξ ∈ C) = ∫ f(u) P(forcedDrv(u, B) ∈ C) du` (**`measure_stripPath_eq_lintegral`**).

Proof: on a cylinder with times in `[0, T]`, the finite-horizon mixture `P(A) = ∫ f(u) Q_u^T(A) du`
(`measure_eq_lintegral_mixMeasure`), the identification `ξ = forcedDrv(u, B̂)` on `[0, T]` under `Q_u^T`
(`forcedDrv_mixBM_eq`), and the equality of the laws of the Brownian motions `B̂` under `Q_u^T` and `B` under `P`
(`map_pathOf_eq_of_isPreBrownianReal`); cylinders form a π-system generating the path σ-algebra.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.Mix

variable {κ σ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ}

/-- `Sec2.markFlow` is natural in the sample space: it only reads the driving path at the given sample. -/
theorem markFlow_comp {Ω' : Type*} (F : ℝ → ℝ) (y : ℝ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (g : Ω' → Ω)
    (t : ℝ≥0) (ω' : Ω') :
    Sec2.markFlow F y (fun ω' => ζ (g ω')) (fun s ω' => W s (g ω')) t ω' = Sec2.markFlow F y ζ W t (g ω') := by
  unfold Sec2.markFlow Sec2.markEuler Girsanov.killed
  rfl

/-- The forced driver as a map of paths, `γ ↦ ξ̂(u, γ)`. -/
@[irreducible] def forcedPath (κ σ u : ℝ) : (ℝ≥0 → ℝ) → ℝ≥0 → ℝ :=
  pathOf (forcedDrv κ σ (fun _ => u) (fun s (γ : ℝ≥0 → ℝ) => γ s))

/-- The mixing density `f(u) du` as a measure on `ℝ`. -/
def mixMeasureU (κ σ : ℝ) : Measure ℝ := volume.withDensity fun u => ENNReal.ofReal (mixDensity κ σ u)

/-- **The mixture of the forced laws**: the law of `forcedDrv(U, B)` under `f(u) du ⊗ P`. -/
def mixLaw (P : Measure Ω) (κ σ : ℝ) (B : ℝ≥0 → Ω → ℝ) : Measure (ℝ≥0 → ℝ) :=
  ((mixMeasureU κ σ).prod P).map (fun p : ℝ × Ω => forcedPath κ σ p.1 (pathOf B p.2))

theorem measurable_forcedPath (u : ℝ) : Measurable (forcedPath κ σ u) := by
  unfold forcedPath
  exact measurable_pathOf fun t => measurable_forcedDrv measurable_const (fun s => measurable_pi_apply s) t

theorem measurable_forcedPath_uncurry : Measurable fun p : ℝ × (ℝ≥0 → ℝ) => forcedPath κ σ p.1 p.2 := by
  unfold forcedPath
  exact measurable_pathOf fun t => measurable_forcedDrv (U := fun p : ℝ × (ℝ≥0 → ℝ) => p.1)
    (β := fun s (p : ℝ × (ℝ≥0 → ℝ)) => p.2 s) measurable_fst (fun s => (measurable_pi_apply s).comp measurable_snd) t

theorem forcedPath_eq {β : ℝ≥0 → Ω → ℝ} (u : ℝ) (ω : Ω) :
    forcedPath κ σ u (pathOf β ω) = pathOf (forcedDrv κ σ (fun _ => u) β) ω := by
  unfold forcedPath
  funext t
  show Real.sqrt κ * pathOf β ω t - σ * t - 2 * forcedLam κ σ (fun _ => u) (fun s (γ : ℝ≥0 → ℝ) => γ s) t (pathOf β ω) =
    Real.sqrt κ * β t ω - σ * t - 2 * forcedLam κ σ (fun _ => u) β t ω
  rw [show forcedLam κ σ (fun _ => u) (fun s (γ : ℝ≥0 → ℝ) => γ s) t (pathOf β ω) = forcedLam κ σ (fun _ => u) β t ω
    from (markFlow_comp (fun z => -Real.tanh (z / 2)) 0 (fun _ => ⊤)
      (fun s (γ : ℝ≥0 → ℝ) => Real.sqrt κ * γ s - σ * s - u) (pathOf β) t ω).symm]
  rfl

theorem isProbabilityMeasure_mixMeasureU (hκ : 0 < κ) (hσ : |σ| < 1) : IsProbabilityMeasure (mixMeasureU κ σ) :=
  ⟨by rw [mixMeasureU, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_mixDensity hκ hσ]⟩

/-- **(G3) in the strip, on every measurable set of paths**: `P(ξ ∈ C) = ∫ f(u) P(ξ̂(u, B) ∈ C) du`. -/
theorem map_stripPath_eq_mixLaw {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} (hκ : 0 < κ) (hσ : |σ| < 1)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) :
    P.map (pathOf fun t ω => stripDrv κ σ B ω t) = mixLaw P κ σ B := by
  have hP := hB.isProbabilityMeasure'
  have hU := isProbabilityMeasure_mixMeasureU hκ hσ
  have hBm : ∀ t, Measurable[𝓕 t] (B t) := fun t => hB.2.1 t
  have hBm' : ∀ t, Measurable (B t) := fun t => (hBm t).mono (𝓕.le t) le_rfl
  have hξm : Measurable (pathOf fun t ω => stripDrv κ σ B ω t) := measurable_pathOf fun t => by
    simp only [stripDrv, Real.toNNReal_coe]
    exact ((hBm' t).const_mul _).add_const _
  have hΦm : Measurable fun p : ℝ × Ω => forcedPath κ σ p.1 (pathOf B p.2) :=
    measurable_forcedPath_uncurry.comp (measurable_fst.prodMk ((measurable_pathOf hBm').comp measurable_snd))
  have hfin : IsProbabilityMeasure (P.map (pathOf fun t ω => stripDrv κ σ B ω t)) :=
    inferInstance
  refine ext_of_generate_finite (measurableCylinders _) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders (fun C hC => ?_) ?_
  · have hCm' := MeasurableSet.of_mem_measurableCylinders hC
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hC
    have hCm := hCm'
    set T : ℝ≥0 := I.sup id with hT
    have hIT : ∀ i ∈ I, i ≤ T := fun i hi => Finset.le_sup (f := id) hi
    rw [Measure.map_apply hξm hCm, mixLaw, Measure.map_apply hΦm hCm, Measure.prod_apply (hΦm hCm),
      measure_eq_lintegral_mixMeasure hκ hσ hBm hBc T (hξm hCm), mixMeasureU,
      lintegral_withDensity_eq_lintegral_mul _ (f := fun u => ENNReal.ofReal (mixDensity κ σ u))
        (ENNReal.measurable_ofReal.comp continuous_mixDensity.measurable)
        (measurable_measure_prodMk_left (hΦm hCm))]
    refine lintegral_congr fun u => ?_
    simp only [Pi.mul_apply]
    congr 1
    -- the tilted measure of the event is the forced law of the event
    obtain ⟨hQ, hBQ⟩ := isFilteredBrownianReal_mixBM hκ hσ hB hBc hB0 u T
    have hβm : ∀ t, Measurable (mixBM κ σ B u T t) := fun t => (hBQ.2.1 t).mono (𝓕.le t) le_rfl
    have hev : (pathOf fun t ω => stripDrv κ σ B ω t) ⁻¹' cylinder I S =
        pathOf (mixBM κ σ B u T) ⁻¹' (forcedPath κ σ u ⁻¹' cylinder I S) := by
      ext ω
      simp only [mem_preimage, mem_cylinder, forcedPath_eq]
      have e : I.restrict (pathOf (fun t ω => stripDrv κ σ B ω t) ω) =
          I.restrict (pathOf (forcedDrv κ σ (fun _ => u) (mixBM κ σ B u T)) ω) := by
        funext i
        simp only [Finset.restrict, pathOf]
        exact (forcedDrv_mixBM_eq hκ (hBc ω) u (hIT i i.2)).symm
      rw [e]
    have hpre : Prod.mk u ⁻¹' ((fun p : ℝ × Ω => forcedPath κ σ p.1 (pathOf B p.2)) ⁻¹' cylinder I S) =
        pathOf B ⁻¹' (forcedPath κ σ u ⁻¹' cylinder I S) := rfl
    rw [hev, hpre, ← Measure.map_apply (measurable_pathOf hβm) ((measurable_forcedPath u) hCm),
      ← Measure.map_apply (measurable_pathOf hBm') ((measurable_forcedPath u) hCm),
      map_pathOf_eq_of_isPreBrownianReal hBQ.1.toIsPreBrownianReal hB.1.toIsPreBrownianReal hβm hBm']
  · rw [measure_univ, mixLaw, Measure.map_apply hΦm MeasurableSet.univ, preimage_univ, ← univ_prod_univ,
      Measure.prod_prod,
      measure_univ, measure_univ, one_mul]

/-- **(G3) in the strip, evaluated**: for every measurable set `C` of paths,
`P(ξ ∈ C) = ∫ f(u) P(ξ̂(u, B) ∈ C) du`. -/
theorem measure_stripPath_eq_lintegral {𝓕 : Filtration ℝ≥0 mΩ} {P : Measure Ω} (hκ : 0 < κ) (hσ : |σ| < 1)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {C : Set (ℝ≥0 → ℝ)} (hC : MeasurableSet C) :
    P {ω | (fun t : ℝ≥0 => stripDrv κ σ B ω t) ∈ C} =
      ∫⁻ u, ENNReal.ofReal (mixDensity κ σ u) *
        P {ω | (fun t : ℝ≥0 => forcedDrv κ σ (fun _ => u) B t ω) ∈ C} := by
  have hP := hB.isProbabilityMeasure'
  have hBm' : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕.le t) le_rfl
  have hξm : Measurable (pathOf fun t ω => stripDrv κ σ B ω t) := measurable_pathOf fun t => by
    simp only [stripDrv, Real.toNNReal_coe]
    exact ((hBm' t).const_mul _).add_const _
  have hΦm : Measurable fun p : ℝ × Ω => forcedPath κ σ p.1 (pathOf B p.2) :=
    measurable_forcedPath_uncurry.comp (measurable_fst.prodMk ((measurable_pathOf hBm').comp measurable_snd))
  have h := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ C) (map_stripPath_eq_mixLaw hκ hσ hB hBc hB0)
  rw [Measure.map_apply hξm hC, mixLaw, Measure.map_apply hΦm hC, Measure.prod_apply (hΦm hC), mixMeasureU,
    lintegral_withDensity_eq_lintegral_mul _ (f := fun u => ENNReal.ofReal (mixDensity κ σ u))
        (ENNReal.measurable_ofReal.comp continuous_mixDensity.measurable)
      (measurable_measure_prodMk_left (hΦm hC))] at h
  have e2 : ∀ u, {ω | (fun t : ℝ≥0 => forcedDrv κ σ (fun _ => u) B t ω) ∈ C} =
      Prod.mk u ⁻¹' ((fun p : ℝ × Ω => forcedPath κ σ p.1 (pathOf B p.2)) ⁻¹' C) := fun u => by
    ext ω
    exact Iff.of_eq (congrArg (· ∈ C) (forcedPath_eq (κ := κ) (σ := σ) (β := B) u ω)).symm
  simp_rw [e2]
  exact h

end InteractingSLE.ZhanGT4.Mix
