import QuantumZipper.Proofs.RS.TransienceCanon

/-!
# F2 step (2a), probabilistic core: Brownian scaling by an independent random factor

Theorem 1.3, node F2, step (2a) (`F2.F2UnscaledStmt`), and the embedding step `F1.F1EmbedStmt`:
the canonical (`P_*`) configuration is the unscaled one rescaled by the random canonical scale
`a = scaleParam`, and the driver `B` is Brownian-rescaled by `a`. Since `a` is a function of the
field and the field is independent of `B`, conditioning on the field makes `a` deterministic and
Brownian scaling applies (Sheffield, arXiv:1012.4797, §5.1, pp. 60–62, uses this tacitly).

Main result (`randScale_isBrownian_indep`): let `B` be a pre-Brownian motion with measurable
coordinates and continuous paths, `ξ` a measurable random variable independent of the path of
`B`, and `c` a measurable, nowhere-zero scale function of `ξ`. Then the randomly rescaled process
`t ↦ (√c(ξ))⁻¹ B(c(ξ) t)` is a Brownian motion independent of `ξ`.

Proof (own, standard): the joint law of `(ξ, B)` is a product (independence); on the space
`CPath` of continuous paths the evaluation `(s, f) ↦ f s` is jointly measurable, so Fubini
(`Measure.prod_apply`) reduces the joint law of `(ξ, B')` to deterministic Brownian scaling
(`IsPreBrownianReal.smul`) and Kolmogorov uniqueness (`Williams.map_eq_of_forall_finset`).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- Brownian rescaling by a random factor `c ω`: `t ↦ (√(c ω))⁻¹ B(c ω · t)`. -/
def rscale {Ω : Type*} (c : Ω → ℝ≥0) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (√(c ω))⁻¹ * B (c ω * t) ω

/-- The rescaling map on `scale × CPath`. -/
def rscMap (p : ℝ≥0 × RS.CPath) : ℝ≥0 → ℝ := fun t => (√p.1)⁻¹ * p.2.1 (p.1 * t)

theorem measurable_evalCPath : Measurable fun q : ℝ≥0 × RS.CPath => q.2.1 q.1 := by
  have := measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ≥0) (f : RS.CPath) =>
    f.1 s) (fun f => f.2) (fun s => (measurable_pi_apply s).comp measurable_subtype_coe)
  exact this

theorem measurable_rscMap : Measurable rscMap := by
  refine measurable_pi_iff.2 fun t => ?_
  refine Measurable.mul ?_ (measurable_evalCPath.comp
    ((measurable_fst.mul_const t).prodMk measurable_snd))
  exact (NNReal.continuous_coe.measurable.comp measurable_fst).sqrt.inv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ}

theorem measurable_pathOf_rscale {c : Ω → ℝ≥0} (hcm : Measurable c) (hBm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) : Measurable (pathOf (rscale c B)) := by
  rw [show pathOf (rscale c B) = fun ω => rscMap (c ω, RS.toCPath B hc ω) from rfl]
  exact measurable_rscMap.comp (hcm.prodMk (RS.measurable_toCPath hBm hc))

/-- Deterministic Brownian scaling at the level of path laws. -/
theorem map_pathOf_smul_eq (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    {c : ℝ≥0} (hc0 : c ≠ 0) :
    P.map (pathOf fun t ω => (√c)⁻¹ * B (c * t) ω) = P.map (pathOf B) := by
  refine Williams.map_eq_of_forall_finset
    (measurable_pi_iff.2 fun t => measurable_const.mul (hBm _)).aemeasurable
    (measurable_pi_iff.2 hBm).aemeasurable fun I => ?_
  exact ((hB.smul hc0).hasLaw I).map_eq.trans (hB.hasLaw I).map_eq.symm

/-- **Joint law of `(ξ, B')`**: for measurable `S, R`,
`P(ξ ∈ S, B' ∈ R) = P(ξ ∈ S) P(B ∈ R)`. -/
theorem measure_inter_rscale {β : Type*} [MeasurableSpace β] {ξ : Ω → β} (hξ : Measurable ξ)
    {c : β → ℝ≥0} (hcm : Measurable c) (hc0 : ∀ b, c b ≠ 0) (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (B · ω))
    (hind : IndepFun ξ (pathOf B) P) {S : Set β} (hS : MeasurableSet S)
    {R : Set (ℝ≥0 → ℝ)} (hR : MeasurableSet R) :
    P (ξ ⁻¹' S ∩ pathOf (rscale (c ∘ ξ) B) ⁻¹' R) = P (ξ ⁻¹' S) * P (pathOf B ⁻¹' R) := by
  set V := RS.toCPath B hc with hV
  have hVm : Measurable V := RS.measurable_toCPath hBm hc
  -- independence of `ξ` and the continuous path
  have hindV : IndepFun ξ V P := by
    rw [IndepFun_iff_Indep] at hind ⊢
    have : MeasurableSpace.comap V inferInstance = MeasurableSpace.comap (pathOf B)
        MeasurableSpace.pi := by
      rw [show (inferInstance : MeasurableSpace RS.CPath) =
        MeasurableSpace.comap Subtype.val MeasurableSpace.pi from rfl, MeasurableSpace.comap_comp]
      rfl
    rwa [this]
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hξ.aemeasurable hVm.aemeasurable).1 hindV
  set E : Set (β × RS.CPath) := {p | p.1 ∈ S ∧ rscMap (c p.1, p.2) ∈ R} with hE
  have hEm : MeasurableSet E :=
    (measurable_fst hS).inter (measurable_rscMap.comp
      ((hcm.comp measurable_fst).prodMk measurable_snd) hR)
  have hpre : ξ ⁻¹' S ∩ pathOf (rscale (c ∘ ξ) B) ⁻¹' R = (fun ω => (ξ ω, V ω)) ⁻¹' E := rfl
  have hslice : ∀ b, (P.map V) (Prod.mk b ⁻¹' E) = S.indicator (fun _ => P (pathOf B ⁻¹' R)) b := by
    intro b
    by_cases hb : b ∈ S
    · rw [indicator_of_mem hb]
      have hsm : MeasurableSet {f : RS.CPath | rscMap (c b, f) ∈ R} :=
        measurable_rscMap.comp (measurable_const.prodMk measurable_id) hR
      have hset : Prod.mk b ⁻¹' E = {f : RS.CPath | rscMap (c b, f) ∈ R} := by
        ext f; simp [hE, hb]
      rw [hset, Measure.map_apply hVm hsm]
      have hl := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ R) (map_pathOf_smul_eq hB hBm (hc0 b))
      have hpm : Measurable (pathOf B) := measurable_pi_iff.2 hBm
      have hsm2 : Measurable (pathOf fun t ω => (√(c b : ℝ))⁻¹ * B (c b * t) ω) :=
        measurable_pi_iff.2 fun t => measurable_const.mul (hBm _)
      rw [Measure.map_apply hsm2 hR, Measure.map_apply hpm hR] at hl
      exact hl
    · rw [indicator_of_notMem hb]
      have hset : Prod.mk b ⁻¹' E = ∅ := by ext f; simp [hE, hb]
      rw [hset, measure_empty]
  rw [hpre, ← Measure.map_apply (hξ.prodMk hVm) hEm, hprod, Measure.prod_apply hEm]
  simp_rw [hslice]
  rw [lintegral_indicator_const hS, Measure.map_apply hξ hS, mul_comm]

/-- **Brownian scaling by an independent random factor**: `B' = rscale (c ∘ ξ) B` is a Brownian
motion and is independent of `ξ`. -/
theorem randScale_isBrownian_indep {β : Type*} [MeasurableSpace β] {ξ : Ω → β}
    (hξ : Measurable ξ) {c : β → ℝ≥0} (hcm : Measurable c) (hc0 : ∀ b, c b ≠ 0)
    (hB : IsPreBrownianReal B P) (hBm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (B · ω))
    (hind : IndepFun ξ (pathOf B) P) :
    IsBrownianReal (rscale (c ∘ ξ) B) P ∧ IndepFun ξ (pathOf (rscale (c ∘ ξ) B)) P := by
  have hm := measurable_pathOf_rscale (hcm.comp hξ) hBm hc
  have hpm : Measurable (pathOf B) := measurable_pi_iff.2 hBm
  have huniv : ∀ R, MeasurableSet R →
      P (pathOf (rscale (c ∘ ξ) B) ⁻¹' R) = P (pathOf B ⁻¹' R) := by
    intro R hR
    have := measure_inter_rscale hξ hcm hc0 hB hBm hc hind MeasurableSet.univ hR
    simpa using this
  have hlaw : P.map (pathOf (rscale (c ∘ ξ) B)) = P.map (pathOf B) := by
    ext R hR
    rw [Measure.map_apply hm hR, Measure.map_apply hpm hR, huniv R hR]
  refine ⟨⟨⟨fun I => ⟨((Finset.measurable_restrict I).comp hm).aemeasurable, ?_⟩⟩, ?_⟩, ?_⟩
  · have h1 : (fun ω => I.restrict (fun t => rscale (c ∘ ξ) B t ω)) =
        I.restrict ∘ pathOf (rscale (c ∘ ξ) B) := rfl
    have h2 : (fun ω => I.restrict (fun t => B t ω)) = I.restrict ∘ pathOf B := rfl
    rw [h1, ← Measure.map_map (Finset.measurable_restrict I) hm, hlaw,
      Measure.map_map (Finset.measurable_restrict I) hpm, ← h2]
    exact (hB.hasLaw I).map_eq
  · exact ae_of_all _ fun ω => continuous_const.mul ((hc ω).comp (continuous_const.mul
      continuous_id))
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro S R hS hR
    rw [measure_inter_rscale hξ hcm hc0 hB hBm hc hind hS hR, huniv R hR]

end F2
end QuantumZipper
