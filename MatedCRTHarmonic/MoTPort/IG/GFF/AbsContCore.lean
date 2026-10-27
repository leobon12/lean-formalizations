/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.IG.GFF.AbsContCM
import MatedCRTHarmonic.MoTPort.Foundations.GFF

/-!
# IG1 Prop. 3.4, the Cameron–Martin argument given Markov decompositions (task IGR-2a, part 2)

Miller–Sheffield, *Imaginary geometry I*, arXiv:1201.1496, , Prop. 3.4
(`prop::gff_abs_continuity`, l. 1233–1238) and its proof (l. 1260–1264). The proof writes, on a
neighbourhood `Ũ` (here `V`) of `Ū`, `(hᵢ + Fᵢ)|_Ũ = hᵢ^Ũ + Kᵢ` with `hᵢ^Ũ` a zero-boundary GFF on
`Ũ` and `Kᵢ = (hᵢ^{Ũᶜ} + Fᵢ)|_Ũ` harmonic on `Ũ` and independent of `hᵢ^Ũ` (IG1 Prop. 3.1,
`gff::prop::markov`), puts `g = φ (K₂ − K₁)` with `φ ∈ C_0^∞(Ũ)`, `φ|_U ≡ 1`, so that
`(h₁^Ũ + K₁ + g)|_U = (h₁^Ũ + K₂)|_U`, and concludes by Cameron–Martin for the shift `g`.

* `absCont_resOn_of_markov` : the conclusion of Prop. 3.4 for any two fields given on `V` in the
  Markov form `Zᵢ + Kᵢ` (`Zᵢ` zero-boundary GFF on `V`, `Kᵢ` a.s. a harmonic function on `V`,
  `Zᵢ ⫫ Kᵢ`): `law((Z₁ + K₁)|_B) ≪ law((Z₂ + K₂)|_B)` whenever `B̄ ⊆ V` is compact;
  `mutuallyAbsCont_resOn_of_markov` : both directions.

Departure from the written proof (same mathematics, recorded for DEVIATIONS): IG1 couples `h₁, h₂`
so that `h₁^Ũ = h₂^Ũ` and reweights by the random density `𝒵⁻¹ exp((h₁, g)_∇)`. We instead
disintegrate over the harmonic parts: by independence, `law((Z + K)|_B)(A) = ∫ ν{k : (k + K)|_B ∈ A}`
(`ν` = the law of the zero-boundary GFF on `V`, unique by LQGMetric `IsZeroBoundaryGFF.map_eq`),
and for each pair of fixed harmonic parts the deterministic Cameron–Martin theorem
(`GFFAbsCont.map_add_absCont`) compares the integrands. This avoids the measurability of
`(h₁, g)_∇` that IG1 discusses (l. 1261).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

open LQGMetric QuantumZipper

/-- the restriction `𝒟'(V) → 𝒟'(B)` (composition with `𝓓(B) ⊆ 𝓓(V)`) -/
def resOn (B V : Opens ℂ) (k : DistOn V) : DistOn B := k.comp (GM.testIncl B V)

lemma resOn_apply (B V : Opens ℂ) (k : DistOn V) (φ : TestOn B) :
    resOn B V k φ = k (GM.testIncl B V φ) := rfl

lemma measurable_resOn (B V : Opens ℂ) : Measurable (resOn B V) :=
  measurable_distOn_iff.2 fun φ => measurable_distOn_apply (GM.testIncl B V φ)

/-- `resOn B V ∘ restrictTo V = restrictTo B` -/
lemma resOn_restrictTo {B V : Opens ℂ} (hBV : B ≤ V) (h : Field) :
    resOn B V (restrictTo V h) = restrictTo B h :=
  DFunLike.ext _ _ fun φ => (GM.restrictTo_apply_testIncl hBV h φ).symm

lemma measurable_add_distOn (V : Opens ℂ) :
    Measurable fun q : DistOn V × DistOn V => q.1 + q.2 :=
  measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp measurable_fst).add ((measurable_distOn_apply φ).comp measurable_snd)

lemma measurable_add_const_distOn {V : Opens ℂ} (T : DistOn V) :
    Measurable fun k : DistOn V => k + T :=
  measurable_distOn_iff.2 fun φ => (measurable_distOn_apply φ).add_const (T φ)

/-- `k ∈ 𝒟'(V)` is (integration against) a harmonic function on `V` -/
def IsHarmRep (V : Opens ℂ) (k : DistOn V) : Prop :=
  ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧ ∀ φ : TestOn V, k φ = ∫ x, g x * φ x

lemma continuous_mul_test {V : Opens ℂ} {g : ℂ → ℝ} (hg : ContDiffOn ℝ 0 g (V : Set ℂ))
    (ψ : TestOn V) : Continuous fun x => ψ x * g x :=
  (contDiff_mul_of_tsupport V.isOpen (ψ.contDiff.of_le bot_le) hg ψ.tsupport_subset).continuous_zero

lemma integrable_mul_test {V : Opens ℂ} {g : ℂ → ℝ} (hg : ContDiffOn ℝ 0 g (V : Set ℂ))
    (ψ : TestOn V) : Integrable fun x => g x * ψ x := by
  have h := (continuous_mul_test hg ψ).integrable_of_hasCompactSupport (μ := volume)
    (ψ.hasCompactSupport.mul_right (f' := g))
  simpa only [mul_comm] using h

/-- the shift identity of IG1 l. 1261: `(k + K₁)|_B = (k + T + K₂)|_B` for `T = ∫ χ (g₁ − g₂) ·` -/
lemma resOn_add_shift {B V : Opens ℂ} (hBV : B ≤ V) {χ : ℂ → ℝ} (hχ1 : ∀ x ∈ (B : Set ℂ), χ x = 1)
    {c₁ c₂ T : DistOn V} {g₁ g₂ : ℂ → ℝ}
    (hg₂ : InnerProductSpace.HarmonicOnNhd g₂ (V : Set ℂ))
    (hr₁ : ∀ φ : TestOn V, c₁ φ = ∫ x, g₁ x * φ x) (hr₂ : ∀ φ : TestOn V, c₂ φ = ∫ x, g₂ x * φ x)
    (hF : Continuous fun x => χ x * (g₁ x - g₂ x))
    (hFc : HasCompactSupport fun x => χ x * (g₁ x - g₂ x))
    (hT : ∀ φ : TestOn V, T φ = ∫ x, χ x * (g₁ x - g₂ x) * φ x) (k : DistOn V) :
    resOn B V (k + c₁) = resOn B V (k + T + c₂) := by
  refine DFunLike.ext _ _ fun φ => ?_
  simp only [resOn_apply, add_apply]
  set ψ := GM.testIncl B V φ
  rw [hr₁, hr₂, hT, add_assoc, ← integral_add]
  · congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ (B : Set ℂ)
    · simp only [hχ1 x hx]; ring
    · have : ψ x = 0 := by
        rw [GM.coe_testIncl hBV]
        exact image_eq_zero_of_notMem_tsupport fun h => hx (φ.tsupport_subset h)
      simp [this]
  · exact (hF.mul ψ.continuous).integrable_of_hasCompactSupport (μ := volume) (hFc.mul_right)
  · exact integrable_mul_test (contDiffOn_of_harmonicOnNhd hg₂) ψ

/-- the law of `(Z + K)|_B` as a mixture over `K`, for `Z ⫫ K` and `law Z = ν` -/
lemma map_resOn_apply_eq {B V : Opens ℂ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z K : Ω → DistOn V} (hZ : Measurable Z) (hK : Measurable K)
    (hi : IndepFun Z K P) {A : Set (DistOn B)} (hA : MeasurableSet A) :
    P.map (fun ω => resOn B V (Z ω + K ω)) A =
      ∫⁻ ω, (P.map Z) {k | resOn B V (k + K ω) ∈ A} ∂P := by
  set Φ : DistOn V × DistOn V → DistOn B := fun q => resOn B V (q.1 + q.2)
  have hΦ : Measurable Φ := (measurable_resOn B V).comp (measurable_add_distOn V)
  have hpair : Measurable fun ω => (Z ω, K ω) := hZ.prodMk hK
  have e : (fun ω => resOn B V (Z ω + K ω)) = Φ ∘ fun ω => (Z ω, K ω) := rfl
  rw [e, ← Measure.map_map hΦ hpair, Measure.map_apply hΦ hA,
    (indepFun_iff_map_prod_eq_prod_map_map hZ.aemeasurable hK.aemeasurable).1 hi,
    Measure.prod_apply_symm (hΦ hA), lintegral_map (measurable_measure_prodMk_right (hΦ hA)) hK]
  rfl

/-- **IG1 Prop. 3.4, core** (proof l. 1260–1264): fields given on `V` in Markov form
`Zᵢ + Kᵢ` (zero-boundary GFF plus an independent harmonic function) have mutually absolutely
continuous restrictions to any open `B` with `B̄ ⊆ V` compact; here the direction `≪`. -/
theorem absCont_resOn_of_markov {V B : Opens ℂ} (hadm : ZBAdmissible V)
    (hBc : IsCompact (closure (B : Set ℂ))) (hBV : closure (B : Set ℂ) ⊆ V)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {Z₁ K₁ : Ω₁ → DistOn V} {Z₂ K₂ : Ω₂ → DistOn V}
    (hZ₁ : IsZeroBoundaryGFF V Z₁ P₁) (hZ₂ : IsZeroBoundaryGFF V Z₂ P₂)
    (hK₁ : Measurable K₁) (hK₂ : Measurable K₂)
    (hi₁ : IndepFun Z₁ K₁ P₁) (hi₂ : IndepFun Z₂ K₂ P₂)
    (hh₁ : ∀ᵐ ω ∂P₁, IsHarmRep V (K₁ ω)) (hh₂ : ∀ᵐ ω ∂P₂, IsHarmRep V (K₂ ω)) :
    P₁.map (fun ω => resOn B V (Z₁ ω + K₁ ω)) ≪ P₂.map (fun ω => resOn B V (Z₂ ω + K₂ ω)) := by
  have hB : B ≤ V := fun x hx => hBV (subset_closure hx)
  obtain ⟨χ, hχ, hχ1⟩ := exists_cutoff_of_isCompact hBc V.isOpen hBV
  have hν : P₂.map Z₂ = P₁.map Z₁ := hZ₂.map_eq hZ₁
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  have hS : ∀ c : DistOn V, MeasurableSet {k : DistOn V | resOn B V (k + c) ∈ A} := fun c =>
    ((measurable_resOn B V).comp (measurable_add_const_distOn c)) hA
  have hmeas : ∀ {Ω : Type _} [MeasurableSpace Ω] {K : Ω → DistOn V}, Measurable K →
      Measurable fun ω => (P₁.map Z₁) {k | resOn B V (k + K ω) ∈ A} := fun hK =>
    (measurable_measure_prodMk_right (μ := P₁.map Z₁)
      (((measurable_resOn B V).comp (measurable_add_distOn V)) hA)).comp hK
  rw [map_resOn_apply_eq hZ₂.measurable hK₂ hi₂ hA, hν,
    lintegral_eq_zero_iff (hmeas hK₂)] at hA0
  obtain ⟨ω₂, h0, g₂, hg₂, hr₂⟩ := (hA0.and hh₂).exists
  rw [map_resOn_apply_eq hZ₁.measurable hK₁ hi₁ hA]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [hh₁] with ω ⟨g₁, hg₁, hr₁⟩
  set F : ℂ → ℝ := fun x => χ x * (g₁ x - g₂ x)
  have hFs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    contDiff_mul_of_tsupport V.isOpen hχ.1
      ((contDiffOn_of_harmonicOnNhd hg₁).sub (contDiffOn_of_harmonicOnNhd hg₂)) hχ.2.2
  have hFc : HasCompactSupport F := hχ.2.1.mul_right
  have hFV : F ∈ zeroSpace (V : Set ℂ) :=
    ⟨hFs, hFc, (tsupport_mul_subset_left).trans hχ.2.2⟩
  set T : DistOn V := ofFunOn V F
  have hT : ∀ φ : TestOn V, T φ = ∫ x, F x * φ x := fun φ => by
    rw [GFFBdry.ofFunOn_apply (hFs.continuous.locallyIntegrable.locallyIntegrableOn _)]
    simp only [mul_comm]
  have hset : {k : DistOn V | resOn B V (k + K₁ ω) ∈ A} =
      (fun k => k + T) ⁻¹' {k | resOn B V (k + K₂ ω₂) ∈ A} := by
    ext k
    simp only [mem_ofPred_eq, mem_preimage]
    rw [resOn_add_shift hB (fun x hx => hχ1 x (subset_closure hx)) hg₂ hr₁ hr₂
      hFs.continuous hFc hT k]
  rw [hset, ← Measure.map_apply (measurable_add_const_distOn T) (hS _),
    Measure.map_map (measurable_add_const_distOn T) hZ₁.measurable]
  exact map_add_absCont hadm hZ₁ hFV hT h0

/-- **IG1 Prop. 3.4, core**, both directions. -/
theorem mutuallyAbsCont_resOn_of_markov {V B : Opens ℂ} (hadm : ZBAdmissible V)
    (hBc : IsCompact (closure (B : Set ℂ))) (hBV : closure (B : Set ℂ) ⊆ V)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {Z₁ K₁ : Ω₁ → DistOn V} {Z₂ K₂ : Ω₂ → DistOn V}
    (hZ₁ : IsZeroBoundaryGFF V Z₁ P₁) (hZ₂ : IsZeroBoundaryGFF V Z₂ P₂)
    (hK₁ : Measurable K₁) (hK₂ : Measurable K₂)
    (hi₁ : IndepFun Z₁ K₁ P₁) (hi₂ : IndepFun Z₂ K₂ P₂)
    (hh₁ : ∀ᵐ ω ∂P₁, IsHarmRep V (K₁ ω)) (hh₂ : ∀ᵐ ω ∂P₂, IsHarmRep V (K₂ ω)) :
    P₁.map (fun ω => resOn B V (Z₁ ω + K₁ ω)) ≪ P₂.map (fun ω => resOn B V (Z₂ ω + K₂ ω)) ∧
      P₂.map (fun ω => resOn B V (Z₂ ω + K₂ ω)) ≪ P₁.map (fun ω => resOn B V (Z₁ ω + K₁ ω)) :=
  ⟨absCont_resOn_of_markov hadm hBc hBV hZ₁ hZ₂ hK₁ hK₂ hi₁ hi₂ hh₁ hh₂,
    absCont_resOn_of_markov hadm hBc hBV hZ₂ hZ₁ hK₂ hK₁ hi₂ hi₁ hh₂ hh₁⟩

end MatedCRTHarmonic.MoTPort.IG.GFFAbsCont
