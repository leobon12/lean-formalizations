/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux122DisintL2
import MathFin.Probability.Brownian.LevyCharacterization

/-!
# §7.4, Aux. lemma 122: the Brownian motion stays Brownian under almost every conditional law

Packet PROVE-AUX119-130. Specification §7.4.1, Aux. lemma 122, last paragraph of its proof
(`source/spec/p385-432.md` L111–L139, p. 391): "The Brownian motion in that proof is Brownian in the retained
filtration, so it is independent of its time-zero sigma-algebra. Disintegration over that initial information
preserves … this Brownian property."

Let `B` be a Brownian motion in a filtration `𝓕` with `𝓔 ≤ 𝓕 0`, on a standard Borel space, and let `N` be a
measurable null set off which `B` is continuous with `B 0 = 0`. With the data filtration `dataFilt N ζ B X` of
`Aux122DisintFilt.lean` (countably generated at every time, the data processes adapted, every event agreeing off `N`
with an event of `𝓕`):

* `ae_isFilteredBrownianReal_condExpKernel`: for `P`-almost every `ω₀`, the modified Brownian motion `zeroOn N B` is a
  Brownian motion in `dataFilt N ζ B X` under the conditional law `condExpKernel P 𝓔 ω₀`.

The proof: at countably many rational times and events of a countable generating π-system (`piClosure`), the
conditional identities of `Aux122Disint.lean` hold simultaneously for almost every `ω₀`; under each such conditional
law they extend to all events (Dynkin) and to real times (`Aux122DisintL2.lean`), so `B̂` and `B̂² − t` are
martingales; Lévy's characterization (`MathFin.LevyCharacterization`) concludes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux122Disint

/-! ### Finite intersections -/

section PiClosure

variable {Ω : Type*}

/-- The finite intersections of members of `S` (including `univ`, the empty intersection). -/
def piClosure (S : Set (Set Ω)) : Set (Set Ω) := {A | ∃ T : Set (Set Ω), T.Finite ∧ T ⊆ S ∧ A = ⋂₀ T}

theorem univ_mem_piClosure (S : Set (Set Ω)) : univ ∈ piClosure S :=
  ⟨∅, finite_empty, empty_subset _, sInter_empty.symm⟩

theorem subset_piClosure (S : Set (Set Ω)) : S ⊆ piClosure S := fun A hA =>
  ⟨{A}, finite_singleton A, singleton_subset_iff.2 hA, sInter_singleton A |>.symm⟩

theorem isPiSystem_piClosure (S : Set (Set Ω)) : IsPiSystem (piClosure S) := by
  rintro _ ⟨T₁, hT₁, hT₁S, rfl⟩ _ ⟨T₂, hT₂, hT₂S, rfl⟩ -
  exact ⟨T₁ ∪ T₂, hT₁.union hT₂, union_subset hT₁S hT₂S, (sInter_union T₁ T₂).symm⟩

theorem countable_piClosure {S : Set (Set Ω)} (hS : S.Countable) : (piClosure S).Countable := by
  have h : piClosure S = (fun T => ⋂₀ T) '' {T | T.Finite ∧ T ⊆ S} := by
    ext A
    simp only [piClosure, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨T, hT, hTS, rfl⟩
      exact ⟨T, ⟨hT, hTS⟩, rfl⟩
    · rintro ⟨T, ⟨hT, hTS⟩, rfl⟩
      exact ⟨T, hT, hTS, rfl⟩
  rw [h]
  exact (countable_ofPred_finite_subset hS).image _

theorem generateFrom_piClosure (S : Set (Set Ω)) :
    MeasurableSpace.generateFrom (piClosure S) = MeasurableSpace.generateFrom S := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) (MeasurableSpace.generateFrom_mono (subset_piClosure S))
  rintro _ ⟨T, hT, hTS, rfl⟩
  exact hT.measurableSet_sInter fun A hA => MeasurableSpace.measurableSet_generateFrom (hTS hA)

end PiClosure

/-! ### Countability of the generating events -/

section Count

variable {Ω : Type*} {ι : Type*} [Countable ι]

theorem countable_dataGens (N : Set Ω) (ζ : Ω → ℝ≥0∞) (B : ℝ≥0 → Ω → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) :
    (dataGens N ζ B X t).Countable := by
  unfold dataGens
  refine ((countable_singleton _).union (countable_singleton _)).union
    (countable_iUnion fun q => countable_iUnion fun _ => ?_)
  exact ((countable_singleton _).union (countable_range _)).union (countable_iUnion fun i => countable_range _)

end Count

/-! ### Dynkin's extension of a set-integral identity -/

section Dynkin

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ν : Measure Ω}

/-- **An integral identity on a generating π-system containing `univ` holds on the generated σ-algebra.** -/
theorem setIntegral_eq_zero_of_piSystem {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {S : Set (Set Ω)}
    (h_eq : m = MeasurableSpace.generateFrom S) (hS : IsPiSystem S) (huniv : univ ∈ S) {f : Ω → ℝ}
    (hf : Integrable f ν) (h : ∀ A ∈ S, ∫ ω in A, f ω ∂ν = 0) :
    ∀ A, MeasurableSet[m] A → ∫ ω in A, f ω ∂ν = 0 := by
  refine MeasurableSpace.induction_on_inter h_eq hS (by simp) (fun A hA => h A hA) ?_ ?_
  · intro A hA hA0
    rw [setIntegral_compl (hm A hA) hf, hA0, sub_zero, ← setIntegral_univ]
    exact h univ huniv
  · intro f' hdisj hf'm hf'0
    rw [integral_iUnion (fun i => hm _ (hf'm i)) hdisj hf.integrableOn]
    simp [hf'0]

end Dynkin

/-! ### The standing hypotheses -/

section Main

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  {N : Set Ω} {ζ : Ω → ℝ≥0∞} {ι : Type*} [Countable ι] {X : ι → ℝ≥0 → Ω → ℝ}

omit [StandardBorelSpace Ω] in
/-- Two set integrals agree when the sets agree off a null set `N` and the integrands agree off `N`. -/
theorem setIntegral_congr_off {ν : Measure Ω} (hN : ν N = 0) {A A' : Set Ω} (hA' : MeasurableSet A')
    (hAA : A \ N = A' \ N) {f g : Ω → ℝ} (hfg : ∀ ω, ω ∉ N → f ω = g ω) :
    ∫ ω in A, f ω ∂ν = ∫ ω in A', g ω ∂ν := by
  have hsub : ∀ {C C' : Set Ω}, C \ N = C' \ N → C \ C' ⊆ N := fun {C C'} hCC ω hω => by
    by_contra hωN
    have : ω ∈ C \ N := ⟨hω.1, hωN⟩
    rw [hCC] at this
    exact hω.2 this.1
  have hset : A =ᵐ[ν] A' := by
    rw [ae_eq_set]
    exact ⟨measure_mono_null (hsub hAA) hN, measure_mono_null (hsub hAA.symm) hN⟩
  rw [setIntegral_congr_set hset]
  refine setIntegral_congr_ae hA' ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with ω hω _ using hfg ω hω

/-- **The standing hypotheses of the disintegration**: `𝓔 ≤ 𝓕 0`, `B` a Brownian motion in `𝓕`, `N` a measurable
null set off which `B` is continuous with `B 0 = 0`, and the data `{t < ζ}`, killed `Xᵢ` adapted to `𝓕`. -/
structure DisintSetting (P : Measure Ω) (𝓔 : MeasurableSpace Ω) (𝓕 : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (N : Set Ω) (ζ : Ω → ℝ≥0∞) (X : ι → ℝ≥0 → Ω → ℝ) : Prop where
  le0 : 𝓔 ≤ 𝓕 0
  brown : IsFilteredBrownianReal 𝓕 B P
  measN : MeasurableSet[mΩ] N
  nullN : P N = 0
  contB : ∀ ω, ω ∉ N → Continuous fun t => B t ω
  zeroB : ∀ ω, ω ∉ N → B 0 ω = 0
  lt : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω}
  killX : ∀ i t, Measurable[𝓕 t] (killAt ζ (X i) t)

namespace DisintSetting

variable (h : DisintSetting P 𝓔 𝓕 B N ζ X)
include h

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [Countable ι] in
theorem le_mΩ : 𝓔 ≤ mΩ := h.le0.trans (𝓕.le 0)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [Countable ι] in
theorem le_t (t : ℝ≥0) : 𝓔 ≤ 𝓕 t := h.le0.trans (𝓕.mono (by positivity))

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [Countable ι] in
theorem dataMeas : DataMeas N ζ B X :=
  ⟨h.measN, fun t => 𝓕.le t _ (h.lt t), measurable_eval h.brown, fun i t => (h.killX i t).mono (𝓕.le t) le_rfl⟩

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [Countable ι] in
theorem dataFilt_eq (t : ℝ≥0) :
    dataFilt N ζ B X t = MeasurableSpace.generateFrom (piClosure (dataGens N ζ B X t)) := by
  rw [generateFrom_piClosure]
  exact inf_eq_left.2 (MeasurableSpace.generateFrom_le fun A hA => h.dataMeas.measurableSet_of_mem hA)

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] [Countable ι] in
theorem measurableSet_piClosure {t : ℝ≥0} {A : Set Ω} (hA : A ∈ piClosure (dataGens N ζ B X t)) :
    MeasurableSet[dataFilt N ζ B X t] A := by
  obtain ⟨T, hT, hTS, rfl⟩ := hA
  exact @Set.Finite.measurableSet_sInter Ω (dataFilt N ζ B X t) T hT
    fun C hC => h.dataMeas.measurableSet_dataFilt (hTS hC)

omit [Countable ι] in
theorem ae_condExpKernel_N : ∀ᵐ ω₀ ∂P, condExpKernel P 𝓔 ω₀ N = 0 := by
  have h1 : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 h.nullN
  filter_upwards [ae_ae_condExpKernel h.le_mΩ h1] with ω₀ hω₀
  exact measure_eq_zero_iff_ae_notMem.2 hω₀

omit [Countable ι] in
/-- **The three conditional identities on one event of the data filtration** (for almost every `ω₀`). -/
theorem ae_setIntegral_identities {q q' : ℚ} (hqq : rt q ≤ rt q') {A : Set Ω}
    (hA : MeasurableSet[dataFilt N ζ B X (rt q)] A) :
    ∀ᵐ ω₀ ∂P,
      ∫ ω in A, (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ∂(condExpKernel P 𝓔 ω₀) = 0 ∧
      ∫ ω in A, ((zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q))
        ∂(condExpKernel P 𝓔 ω₀) = 0 ∧
      ∫ ω in A, zeroOn N B (rt q) ω * (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω)
        ∂(condExpKernel P 𝓔 ω₀) = 0 := by
  obtain ⟨A', hA'm, hAA⟩ := exists_eq_diff_of_measurableSet_dataFilt h.lt (fun t => h.brown.2.1 t) h.killX hA
  have hA'mΩ : MeasurableSet A' := 𝓕.le _ A' hA'm
  have hle := h.le_t (rt q)
  have hi1 : Integrable (fun ω => B (rt q') ω - B (rt q) ω) P :=
    (memLp_two h.brown (rt q) (rt q')).integrable one_le_two
  have hi2 : Integrable (fun ω => (B (rt q') ω - B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q)) P :=
    (memLp_two h.brown (rt q) (rt q')).integrable_sq.sub (integrable_const _)
  have hi3 : Integrable (fun ω => B (rt q) ω * (B (rt q') ω - B (rt q) ω)) P :=
    (memLp_two_eval h.brown (rt q)).integrable_mul (memLp_two h.brown (rt q) (rt q'))
  filter_upwards [h.ae_condExpKernel_N, ae_setIntegral_condExpKernel h.le_mΩ hi1 hA'mΩ,
    ae_setIntegral_condExpKernel h.le_mΩ hi2 hA'mΩ, ae_setIntegral_condExpKernel h.le_mΩ hi3 hA'mΩ,
    condExp_indicator_increment h.brown hqq hle hA'm, condExp_indicator_increment_sq h.brown hqq hle hA'm,
    condExp_indicator_mul_increment h.brown hqq hle hA'm] with ω₀ hN e1 e2 e3 z1 z2 z3
  refine ⟨?_, ?_, ?_⟩
  · rw [setIntegral_congr_off hN hA'mΩ hAA (g := fun ω => B (rt q') ω - B (rt q) ω)
      (fun ω hω => by simp only [zeroOn_of_notMem hω]), e1, z1, Pi.zero_apply]
  · rw [setIntegral_congr_off hN hA'mΩ hAA
      (g := fun ω => (B (rt q') ω - B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q))
      (fun ω hω => by simp only [zeroOn_of_notMem hω]), e2, z2, Pi.zero_apply]
  · rw [setIntegral_congr_off hN hA'mΩ hAA (g := fun ω => B (rt q) ω * (B (rt q') ω - B (rt q) ω))
      (fun ω hω => by simp only [zeroOn_of_notMem hω]), e3, z3, Pi.zero_apply]

/-- **The identities at all rational times and all events of the generating π-systems, simultaneously.** -/
theorem ae_forall_identities :
    ∀ᵐ ω₀ ∂P, ∀ q q' : ℚ, rt q ≤ rt q' → ∀ A ∈ piClosure (dataGens N ζ B X (rt q)),
      ∫ ω in A, (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ∂(condExpKernel P 𝓔 ω₀) = 0 ∧
      ∫ ω in A, ((zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q))
        ∂(condExpKernel P 𝓔 ω₀) = 0 ∧
      ∫ ω in A, zeroOn N B (rt q) ω * (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω)
        ∂(condExpKernel P 𝓔 ω₀) = 0 := by
  rw [ae_all_iff]
  intro q
  rw [ae_all_iff]
  intro q'
  by_cases hqq : rt q ≤ rt q'
  · have hall := (ae_ball_iff (countable_piClosure (countable_dataGens N ζ B X (rt q)))).2
      fun A hA => h.ae_setIntegral_identities hqq (h.measurableSet_piClosure hA)
    filter_upwards [hall] with ω₀ hω₀ _ A hA using hω₀ A hA
  · exact Eventually.of_forall fun _ hq => absurd hq hqq

omit [Countable ι] in
/-- **The modified Brownian motion is in `L²` at rational times under almost every conditional law.** -/
theorem ae_memLp_two : ∀ᵐ ω₀ ∂P, ∀ q : ℚ, MemLp (zeroOn N B (rt q)) 2 (condExpKernel P 𝓔 ω₀) := by
  rw [ae_all_iff]
  intro q
  have hi : Integrable (fun ω => B (rt q) ω ^ 2) P := (memLp_two_eval h.brown (rt q)).integrable_sq
  filter_upwards [hi.condExpKernel_ae (μ := P) (m := 𝓔), h.ae_condExpKernel_N] with ω₀ hi' hN
  have hae : zeroOn N B (rt q) =ᵐ[condExpKernel P 𝓔 ω₀] B (rt q) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with ω hω using zeroOn_of_notMem hω _
  have hm : AEStronglyMeasurable (zeroOn N B (rt q)) (condExpKernel P 𝓔 ω₀) :=
    (Measurable.ite h.measN measurable_const (measurable_eval h.brown _)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  refine hi'.congr ?_
  filter_upwards [hae] with ω hω
  rw [hω]

end DisintSetting

end Main

/-! ### Under one good conditional law -/

section Good

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {ι : Type*} {N : Set Ω} {ζ : Ω → ℝ≥0∞} {B : ℝ≥0 → Ω → ℝ}
  {X : ι → ℝ≥0 → Ω → ℝ} {ν : Measure Ω}

/-- **The properties of a good conditional law** `ν`: the data are measurable, `N` is `ν`-null, `B̂ = zeroOn N B` is
in `L²(ν)` at rational times, and the three identities hold on the generating π-systems. -/
structure GoodLaw (ν : Measure Ω) (N : Set Ω) (ζ : Ω → ℝ≥0∞) (B : ℝ≥0 → Ω → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) :
    Prop where
  dm : DataMeas N ζ B X
  contB : ∀ ω, ω ∉ N → Continuous fun t => B t ω
  zeroB : ∀ ω, ω ∉ N → B 0 ω = 0
  memLp : ∀ q : ℚ, MemLp (zeroOn N B (rt q)) 2 ν
  eq : ∀ t, dataFilt N ζ B X t = MeasurableSpace.generateFrom (piClosure (dataGens N ζ B X t))
  ident : ∀ q q' : ℚ, rt q ≤ rt q' → ∀ A ∈ piClosure (dataGens N ζ B X (rt q)),
    ∫ ω in A, (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ∂ν = 0 ∧
    ∫ ω in A, ((zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q)) ∂ν = 0 ∧
    ∫ ω in A, zeroOn N B (rt q) ω * (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ∂ν = 0

omit mΩ in
theorem continuous_zeroOn (hBc : ∀ ω, ω ∉ N → Continuous fun t => B t ω) (ω : Ω) :
    Continuous fun t => zeroOn N B t ω := by
  by_cases hω : ω ∈ N
  · simp only [zeroOn_of_mem hω]
    exact continuous_const
  · simp only [zeroOn_of_notMem hω]
    exact hBc ω hω

omit mΩ in
theorem zeroOn_zero (hB0 : ∀ ω, ω ∉ N → B 0 ω = 0) (ω : Ω) : zeroOn N B 0 ω = 0 := by
  by_cases hω : ω ∈ N
  · exact zeroOn_of_mem hω 0
  · rw [zeroOn_of_notMem hω, hB0 ω hω]

namespace GoodLaw

variable (G : GoodLaw ν N ζ B X)
include G

theorem measurable_eval (t : ℝ≥0) : Measurable (zeroOn N B t) :=
  Measurable.ite G.dm.N measurable_const (G.dm.B t)

/-- The `L²` isometry at rational times. -/
theorem ratIsometry [IsProbabilityMeasure ν] : RatIsometry ν (zeroOn N B) := by
  have key : ∀ q q' : ℚ, rt q ≤ rt q' →
      ∫⁻ ω, ‖zeroOn N B (rt q') ω - zeroOn N B (rt q) ω‖ₑ ^ 2 ∂ν = (nndist (rt q) (rt q') : ℝ≥0∞) := by
    intro q q' hqq
    have hm := (G.memLp q').sub (G.memLp q)
    have hsq : Integrable (fun ω => (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2) ν := hm.integrable_sq
    have h0 := (G.ident q q' hqq univ (univ_mem_piClosure _)).2.1
    rw [setIntegral_univ, integral_sub hsq (integrable_const _), integral_const, smul_eq_mul, measureReal_def,
      measure_univ, ENNReal.toReal_one, one_mul, sub_eq_zero] at h0
    have e1 : ∀ ω, ‖zeroOn N B (rt q') ω - zeroOn N B (rt q) ω‖ₑ ^ 2 =
        ENNReal.ofReal ((zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2) := fun ω => by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    simp_rw [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun ω => sq_nonneg _), h0,
      ← ENNReal.ofReal_coe_nnreal, coe_nndist, NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (by
        rw [sub_nonneg]; exact_mod_cast hqq)]
  intro q q'
  rcases le_total (rt q) (rt q') with hqq | hqq
  · exact key q q' hqq
  · have e : ∀ ω, ‖zeroOn N B (rt q') ω - zeroOn N B (rt q) ω‖ₑ = ‖zeroOn N B (rt q) ω - zeroOn N B (rt q') ω‖ₑ :=
      fun ω => enorm_sub_rev _ _
    simp_rw [e]
    rw [key q' q hqq, nndist_comm]

/-- **The martingale identities at rational times, on every event of the data filtration.** -/
theorem setIntegral_rat [IsProbabilityMeasure ν] {q q' : ℚ} (hqq : rt q ≤ rt q') {A : Set Ω}
    (hA : MeasurableSet[dataFilt N ζ B X (rt q)] A) :
    ∫ ω in A, (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ∂ν = 0 ∧
      ∫ ω in A, ((zeroOn N B (rt q') ω ^ 2 - (rt q' : ℝ)) - (zeroOn N B (rt q) ω ^ 2 - (rt q : ℝ))) ∂ν = 0 := by
  have hm := (G.memLp q').sub (G.memLp q)
  have hi1 : Integrable (fun ω => zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ν := hm.integrable one_le_two
  have hi3 : Integrable (fun ω => zeroOn N B (rt q) ω * (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω)) ν :=
    (G.memLp q).integrable_mul hm
  have hi2 : Integrable (fun ω => (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q)) ν :=
    hm.integrable_sq.sub (integrable_const _)
  have e : ∀ ω, (zeroOn N B (rt q') ω ^ 2 - (rt q' : ℝ)) - (zeroOn N B (rt q) ω ^ 2 - (rt q : ℝ)) =
      ((zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q)) +
        2 * (zeroOn N B (rt q) ω * (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω)) := fun ω => by ring
  have hi23 : Integrable (fun ω => ((zeroOn N B (rt q') ω - zeroOn N B (rt q) ω) ^ 2 - ((rt q' : ℝ) - rt q)) +
      2 * (zeroOn N B (rt q) ω * (zeroOn N B (rt q') ω - zeroOn N B (rt q) ω))) ν := hi2.add (hi3.const_mul 2)
  have hle : dataFilt N ζ B X (rt q) ≤ mΩ := (dataFilt N ζ B X).le _
  refine ⟨setIntegral_eq_zero_of_piSystem hle (G.eq _) (isPiSystem_piClosure _) (univ_mem_piClosure _) hi1
    (fun C hC => (G.ident q q' hqq C hC).1) A hA, ?_⟩
  simp_rw [e]
  refine setIntegral_eq_zero_of_piSystem hle (G.eq _) (isPiSystem_piClosure _) (univ_mem_piClosure _) hi23
    (fun C hC => ?_) A hA
  rw [integral_add hi2.integrableOn (hi3.const_mul 2).integrableOn, integral_const_mul,
    (G.ident q q' hqq C hC).2.1, (G.ident q q' hqq C hC).2.2, mul_zero, add_zero]

variable [IsProbabilityMeasure ν]

theorem memLp_eval (t : ℝ≥0) : MemLp (zeroOn N B t) 2 ν :=
  memLp_two_eval_of_iso (continuous_zeroOn G.contB) G.measurable_eval G.ratIsometry (zeroOn_zero G.zeroB) t

/-- **The martingale identity at real times.** -/
theorem setIntegral_eval_eq {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[dataFilt N ζ B X s] A) :
    ∫ ω in A, zeroOn N B t ω ∂ν = ∫ ω in A, zeroOn N B s ω ∂ν := by
  refine setIntegral_eq_of_rat (fun x r hr => tendsto_setIntegral_eval (continuous_zeroOn G.contB)
    G.measurable_eval G.ratIsometry (zeroOn_zero G.zeroB) hr A) hst ?_
  intro q q' hsq hqq
  have hA' : MeasurableSet[dataFilt N ζ B X (rt q)] A := (dataFilt N ζ B X).mono hsq _ hA
  have h1 := (G.setIntegral_rat hqq hA').1
  rwa [integral_sub ((G.memLp q').integrable one_le_two).integrableOn
    ((G.memLp q).integrable one_le_two).integrableOn, sub_eq_zero] at h1

/-- **The identity for `B̂² − t` at real times.** -/
theorem setIntegral_sq_eq {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[dataFilt N ζ B X s] A) :
    ∫ ω in A, (zeroOn N B t ω ^ 2 - (t : ℝ)) ∂ν = ∫ ω in A, (zeroOn N B s ω ^ 2 - (s : ℝ)) ∂ν := by
  refine setIntegral_eq_of_rat (F := fun x ω => zeroOn N B x ω ^ 2 - (x : ℝ))
    (fun x r hr => tendsto_setIntegral_sq_sub (continuous_zeroOn G.contB)
      G.measurable_eval G.ratIsometry (zeroOn_zero G.zeroB) hr A) hst ?_
  intro q q' hsq hqq
  have hA' : MeasurableSet[dataFilt N ζ B X (rt q)] A := (dataFilt N ζ B X).mono hsq _ hA
  have h1 := (G.setIntegral_rat hqq hA').2
  have hi' : Integrable (fun ω => zeroOn N B (rt q') ω ^ 2 - (rt q' : ℝ)) ν :=
    (G.memLp q').integrable_sq.sub (integrable_const _)
  have hi : Integrable (fun ω => zeroOn N B (rt q) ω ^ 2 - (rt q : ℝ)) ν :=
    (G.memLp q).integrable_sq.sub (integrable_const _)
  rwa [integral_sub hi'.integrableOn hi.integrableOn, sub_eq_zero] at h1

/-- **`B̂` is a martingale in the data filtration under the good law.** -/
theorem martingale : Martingale (zeroOn N B) (dataFilt N ζ B X) ν := by
  refine ⟨fun t => (G.dm.measurable_zeroOn G.contB t).stronglyMeasurable, fun s t hst => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((dataFilt N ζ B X).le s)
    ((G.memLp_eval t).integrable one_le_two)
    (fun A _ _ => ((G.memLp_eval s).integrable one_le_two).integrableOn)
    (fun A hA _ => (G.setIntegral_eval_eq hst hA).symm)
    (G.dm.measurable_zeroOn G.contB s).stronglyMeasurable.aestronglyMeasurable).symm

/-- **`B̂² − t` is a martingale in the data filtration under the good law.** -/
theorem martingale_sq : Martingale (fun t ω => zeroOn N B t ω ^ 2 - (t : ℝ)) (dataFilt N ζ B X) ν := by
  have hm : ∀ t, Measurable[dataFilt N ζ B X t] fun ω => zeroOn N B t ω ^ 2 - (t : ℝ) := fun t =>
    ((G.dm.measurable_zeroOn G.contB t).pow_const 2).sub_const _
  refine ⟨fun t => (hm t).stronglyMeasurable, fun s t hst => ?_⟩
  exact (ae_eq_condExp_of_forall_setIntegral_eq ((dataFilt N ζ B X).le s)
    ((G.memLp_eval t).integrable_sq.sub (integrable_const _))
    (fun A _ _ => ((G.memLp_eval s).integrable_sq.sub (integrable_const _)).integrableOn)
    (fun A hA _ => (G.setIntegral_sq_eq hst hA).symm)
    (hm s).stronglyMeasurable.aestronglyMeasurable).symm

/-- **Lévy's characterization: `B̂` is a Brownian motion in the data filtration under the good law.** -/
theorem isFilteredBrownianReal : IsFilteredBrownianReal (dataFilt N ζ B X) (zeroOn N B) ν := by
  have hc := continuous_zeroOn G.contB
  have hM := G.martingale
  have hM2 := G.martingale_sq
  have hfp := MathFin.LevyCharacterization.isFilteredPreBrownian_of_localMartingale hM.stronglyAdapted hc
    (zeroOn_zero G.zeroB) (Martingale.IsLocalMartingale hM fun ω => (hc ω).isCadlag)
    (Martingale.IsLocalMartingale hM2 fun ω => (((hc ω).pow 2).sub NNReal.continuous_coe).isCadlag)
  exact ⟨⟨hfp.toIsPreBrownianReal, Eventually.of_forall hc⟩, hM.stronglyAdapted.adapted,
    fun s t hst => hfp.indep s t hst⟩

end GoodLaw

namespace DisintSetting

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  {N : Set Ω} {ζ : Ω → ℝ≥0∞} {ι : Type*} [Countable ι] {X : ι → ℝ≥0 → Ω → ℝ}

/-- **Almost every conditional law is good.** -/
theorem ae_goodLaw (h : DisintSetting P 𝓔 𝓕 B N ζ X) :
    ∀ᵐ ω₀ ∂P, GoodLaw (condExpKernel P 𝓔 ω₀) N ζ B X := by
  filter_upwards [h.ae_memLp_two, h.ae_forall_identities] with ω₀ hm hid
  exact ⟨h.dataMeas, h.contB, h.zeroB, hm, h.dataFilt_eq, hid⟩

/-- **The Brownian motion stays Brownian under almost every conditional law** (Aux. lemma 122, p. 391:
"Disintegration over that initial information preserves … this Brownian property"): for `P`-almost every `ω₀`,
`B̂ = zeroOn N B` is a Brownian motion in the data filtration under `condExpKernel P 𝓔 ω₀`. -/
theorem ae_isFilteredBrownianReal (h : DisintSetting P 𝓔 𝓕 B N ζ X) :
    ∀ᵐ ω₀ ∂P, IsFilteredBrownianReal (dataFilt N ζ B X) (zeroOn N B) (condExpKernel P 𝓔 ω₀) := by
  filter_upwards [h.ae_goodLaw] with ω₀ G
  exact G.isFilteredBrownianReal

end DisintSetting

end Good

end Aux122Disint

end Sec7

end InteractingSLE
