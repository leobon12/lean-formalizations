import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.Spec.Coupling.Locality11Hull
import InteractingSLE.Spec.Coupling.Assembly11Tau

/-!
# Theorem 1.1, locality of `K_τ` (obligation 6; Astra (1.14), p. 7)

Packet PROVE-T11-LOC. A coupling is **family-local** (`IsFamilyLocal`) when it carries a countable family of open
regions `U_i ⊆ ℍ` and stops `s_i` of the usual augmentation such that

* projection independence holds at every member (Astra (1.10), second half): for a Borel version `G_i` of the
  projection of the centred field `h` onto `H(U_i)`, every event `D` of the stopped σ-algebra at `s_i` and every
  measurable `Y` with `‖Y‖ ≤ 1`,
    `E[e^{i G_i h(Φ)} Y(h − G_i h) 1_D] = E[e^{i G_i h(Φ)}] E[Y(h − G_i h) 1_D]`;
* the stops exhaust avoidance locally (Astra (1.12)): almost surely, for every `t < ζ`, every compact `K ⊆ ℍ ∖ K_t` and
  every open `O ⊇ K`, some member has `K ⊆ U_i ⊆ O` and `t ≤ s_i`.

`isLocalSet_hull_of_isFamilyLocal`: for such a coupling, `K_τ` is a local set of `h` at every stopping time `τ < ζ` of
the frozen driving filtration. Proof (Astra p. 7): for an open `U ⊆ ℍ` and `f ∈ C_c^∞(U)`, cut the avoidance event
`{K_τ ∩ U = ∅} ∈ 𝓕_τ` along the members `K_f ⊆ U_i ⊆ U` with `τ ≤ s_i` (`setIntegral_eq_mul_of_pieces`); on each piece
(1.14) holds because the Dirichlet pairing `(h, f)_∇` is a pairing of `G_i h` (the harmonic part annihilates it) and
every function of `h − G_U h` is a function of `h − G_i h` (`exists_measurable_markovCompl_comp`). The locality
criterion (`isAvoidanceLocal_of_setIntegral_lapTest`) gives Lemma 3.6 (i) for a hitting-measurable version of `K_τ`,
and Lemma 3.6 (`isLocalSet_tfae`) gives locality.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper TopologicalSpace
open scoped NNReal ENNReal Classical RealInnerProductSpace

namespace InteractingSLE

namespace Coupling

open Ito LQGMetric LQGMetric.MarkovZB LocalSets QuantumZipper.K3 QuantumZipper.Thm11Asm

universe u

/-! ### Cutting an event into pieces -/

section Pieces

variable {Ω : Type*}

/-- **Linear identities on a countable cover.** If `∫_D F₁ = c ∫_D F₂` for every `m`-event `D` inside one of countably
many `m`-events `C i ⊆ A` that cover `A` almost surely, then `∫_A F₁ = c ∫_A F₂`. -/
theorem setIntegral_eq_mul_of_pieces {ι : Type*} [Countable ι] {m mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hm : m ≤ mΩ)
    {F₁ F₂ : Ω → ℂ} (hF₁ : Integrable F₁ P) (hF₂ : Integrable F₂ P) (c : ℂ) {A : Set Ω}
    (C : ι → Set Ω) (hC : ∀ i, MeasurableSet[m] (C i)) (hCA : ∀ i, C i ⊆ A)
    (hAC : ∀ᵐ ω ∂P, ω ∈ A → ∃ i, ω ∈ C i)
    (hpiece : ∀ i D, MeasurableSet[m] D → D ⊆ C i → ∫ ω in D, F₁ ω ∂P = c * ∫ ω in D, F₂ ω ∂P) :
    ∫ ω in A, F₁ ω ∂P = c * ∫ ω in A, F₂ ω ∂P := by
  let _ : Encodable ι := Encodable.ofCountable ι
  set C' : ℕ → Set Ω := fun n => ⋃ b ∈ Encodable.decode₂ ι n, C b with hC'_def
  have hC'm : ∀ n, MeasurableSet[m] (C' n) := fun n => by
    simp only [hC'_def]
    cases Encodable.decode₂ ι n with
    | none => simp
    | some b => simpa using hC b
  have hpiece' : ∀ n D, MeasurableSet[m] D → D ⊆ C' n →
      ∫ ω in D, F₁ ω ∂P = c * ∫ ω in D, F₂ ω ∂P := by
    intro n D hD hDC
    simp only [hC'_def] at hDC
    cases hb : Encodable.decode₂ ι n with
    | none =>
      have hD0 : D = ∅ := Set.subset_empty_iff.1 (hDC.trans (by simp [hb]))
      simp [hD0]
    | some b => exact hpiece b D hD (by simpa [hb] using hDC)
  set D : ℕ → Set Ω := disjointed C' with hD_def
  have hDm : ∀ n, MeasurableSet[m] (D n) := fun n => @MeasurableSet.disjointed Ω m C' hC'm n
  have hUnion : ⋃ n, D n = ⋃ i, C i := by
    rw [hD_def, iUnion_disjointed, hC'_def, Encodable.iUnion_decode₂]
  have hAU : A =ᵐ[P] (⋃ n, D n : Set Ω) := by
    rw [hUnion]
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hAC)
      obtain ⟨hωA, hωC⟩ := hω
      intro hgood
      obtain ⟨i, hi⟩ := hgood hωA
      exact hωC (mem_iUnion.2 ⟨i, hi⟩)
    · rw [sdiff_eq_empty.2 (iUnion_subset hCA), measure_empty]
  have hdisj : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed C'
  have hDm' : ∀ n, MeasurableSet (D n) := fun n => hm _ (hDm n)
  rw [setIntegral_congr_set hAU, setIntegral_congr_set hAU]
  have h1 := hasSum_integral_iUnion hDm' hdisj hF₁.integrableOn
  have h2 := (hasSum_integral_iUnion hDm' hdisj hF₂.integrableOn).mul_left c
  have h3 : HasSum (fun n => ∫ ω in D n, F₁ ω ∂P) (c * ∫ ω in ⋃ n, D n, F₂ ω ∂P) := by
    refine h2.congr_fun fun n => ?_
    exact hpiece' n (D n) (hDm n) (disjointed_subset C' n)
  exact h1.unique h3

/-- An event of `𝓖_σ` on which `σ ≤ π` is an event of `𝓖_π`. -/
theorem measurableSet_stopped_of_le {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {σ π : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime 𝓖 σ) (hπ : IsStoppingTime 𝓖 π) {D : Set Ω}
    (hD : MeasurableSet[hσ.measurableSpace] D) (hDle : ∀ ω ∈ D, σ ω ≤ π ω) :
    MeasurableSet[hπ.measurableSpace] D := by
  rw [IsStoppingTime.measurableSet] at hD ⊢
  refine ⟨hD.1, fun t => ?_⟩
  have e : D ∩ {ω | π ω ≤ t} = (D ∩ {ω | σ ω ≤ t}) ∩ {ω | π ω ≤ t} := by
    ext ω
    constructor
    · rintro ⟨hω, hπt⟩; exact ⟨⟨hω, (hDle ω hω).trans hπt⟩, hπt⟩
    · rintro ⟨⟨hω, -⟩, hπt⟩; exact ⟨hω, hπt⟩
  rw [e]
  exact (hD.2 t).inter (hπ t)

end Pieces

/-! ### Family-local couplings -/

section Family

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- **Family-local coupling** (Astra (1.10), second half, and (1.12)), in a form free of projection versions. The
field `h` and the evolution data `(𝓕, W, ζ)` on `(Ω, P)` carry a countable family of open regions `U i ⊆ ℍ` and stops
`s i` of the usual augmentation of `𝓕` such that, on every event `D` of the stopped σ-algebra at `s i`, every
Dirichlet direction `−Δf/2π`, `f ∈ C_c^∞(U i)`, enters the characteristic functional with the Gaussian factor of the
projection onto `H(U i)`:
  `∫_D e^{i h(−Δf/2π + Ξ)} = exp(−‖∇f‖²/2 − ⟪∇f, covVec_{U i} Ξ⟫) ∫_D e^{i h(Ξ)}`   (`Ξ` any test function)
(equivalent, for a zero-boundary GFF, to `P_{U i} h ⫫ (h − P_{U i} h, 𝓕_{s i})`), and the stops exhaust avoidance
locally. -/
def IsFamilyLocal (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (h : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (U : ι → Opens ℂ) (s : ι → Ω → ℝ≥0)
    (hs : ∀ i, IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s i ω : WithTop ℝ≥0)),
    (∀ i, (U i : Set ℂ) ⊆ H) ∧
    (∀ i (f : zsSub (U i : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) (D : Set Ω),
      MeasurableSet[(hs i).measurableSpace] D →
        ∫ ω in D, Complex.exp (Complex.I * (h ω (lapTest (U i) f + Ξ) : ℂ)) ∂P =
          Complex.exp (((-(1 / 2) * ‖gradFeat (U i : Set ℂ) f.1‖ ^ 2 -
              ⟪gradFeat (U i : Set ℂ) f.1, covVec (U i : Set ℂ) Ξ⟫ : ℝ) : ℂ)) *
            ∫ ω in D, Complex.exp (Complex.I * (h ω Ξ : ℂ)) ∂P) ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ K : Set ℂ, IsCompact K → K ⊆ H →
      Disjoint K (fwdHull (fun r : ℝ => W r.toNNReal ω) t) → ∀ O : Set ℂ, IsOpen O → K ⊆ O →
        ∃ i, K ⊆ U i ∧ (U i : Set ℂ) ⊆ O ∧ t ≤ s i ω

variable {P : Measure Ω} {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Locality of `K_τ`** (Theorem 1.1, obligation 6; Astra p. 7). For a family-local coupling with field `h` (a
zero-boundary GFF on `ℍ`) and every stopping time `τ < ζ` of the frozen driving filtration, the hull `K_τ` is a local set
of `h`. -/
theorem isLocalSet_hull_of_isFamilyLocal
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hfam : IsFamilyLocal P 𝓕 W ζ h)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) h P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  obtain ⟨ι, hι, U, s, hs, hUH, hind, hexh⟩ := hfam
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hE.2.2.2.2] with ω hP using ⟨hP.2.2.2.1, hP.1⟩
  obtain ⟨A, hAm, hAK, hAev⟩ := exists_hittingVersion_hull hX hpath hτ hτζ
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hτ𝓖 : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ' ω : WithTop ℝ≥0) :=
    isStoppingTime_untopD_of_drivingFiltration hE hX hτ hτζ
  have hσle := measurableSpace_driving_le_untopD hE hX hτ hτζ
  have hτζ' : ∀ᵐ ω ∂P, (τ' ω : ℝ≥0∞) < ζ ω := hτζ.mono fun ω h => coe_untopD_lt_zeta h
  have hhm := hh.measurable
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [ae_hull_subset_isOpen (hpath.mono fun ω h => h.1) hτζ', hAK] with ω h1 h2
    rw [h2]
    exact h1
  have hnorm1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have hav : IsAvoidanceLocal A h P := by
    refine isAvoidanceLocal_of_setIntegral_lapTest hh hAm fun V hVH => ?_
    have hV : V ≤ upperHalfPlaneOpens := hVH
    obtain ⟨GV, hGV, hGVd⟩ := exists_markovMap V hVH
    have hdV := hGVd hh
    refine ⟨GV, hGV, hdV, fun f Ψ => ?_⟩
    set E : Set Ω := {ω | Disjoint (A ω) (V : Set ℂ)} with hEdef
    have hEm : MeasurableSet E := hAm (measurableSet_avoid V.isOpen hVH)
    obtain ⟨E', hE'm, hEE'⟩ := hAev V V.isOpen hVH
    have hEτ : MeasurableSet[hτ𝓖.measurableSpace] E :=
      measurableSet_stopped_of_ae_eq hτ𝓖 hEm (hσle _ hE'm) hEE'
    set Kf : Set ℂ := tsupport f.1 with hKf
    have hKfV : Kf ⊆ V := f.2.2.2
    have hKfc : IsCompact Kf := f.2.2.1.isCompact
    set Φ : TestOn upperHalfPlaneOpens := lapTest V f with hΦ
    set c : ℂ := ∫ ω, Complex.exp (Complex.I * (h ω Φ : ℂ)) ∂P with hc_def
    have hQVm : Measurable fun ω => markovCompl GV (h ω) := (measurable_markovCompl hGV).comp hhm
    set b : Ω → ℝ := fun ω => markovCompl GV (h ω) Ψ with hb_def
    have hbm : Measurable b := (measurable_distOn_apply Ψ).comp hQVm
    have hhΦm : Measurable fun ω => h ω Φ := (measurable_distOn_apply Φ).comp hhm
    have hF₂m : Measurable fun ω => Complex.exp (Complex.I * (b ω : ℂ)) := GFF.measurable_exp_I_mul hbm
    have hF₁m : Measurable fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ)) *
        Complex.exp (Complex.I * (b ω : ℂ)) := (GFF.measurable_exp_I_mul hhΦm).mul hF₂m
    have hF₁i : Integrable (fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ)) *
        Complex.exp (Complex.I * (b ω : ℂ))) P :=
      Integrable.of_bound hF₁m.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by
        rw [norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal, one_mul])
    have hF₂i : Integrable (fun ω => Complex.exp (Complex.I * (b ω : ℂ))) P :=
      Integrable.of_bound hF₂m.aestronglyMeasurable 1 (Eventually.of_forall fun ω => hnorm1 _)
    -- the Dirichlet approximation of the complementary projection
    obtain ⟨g, hg, hgL2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hV hdV Ψ
    set Ξ : ℕ → TestOn upperHalfPlaneOpens := fun n => Ψ - lapTest V (g n) with hΞ
    set a : ℕ → Ω → ℝ := fun n ω => h ω (Ξ n) with ha_def
    have ham : ∀ n, Measurable (a n) := fun n => (measurable_distOn_apply _).comp hhm
    have hab : ∀ n ω, a n ω - b ω = GV (h ω) Ψ - h ω (lapTest V (g n)) := fun n ω => by
      simp only [a, b, hΞ, map_sub, markovCompl, sub_apply]
      ring
    have hmem : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P := fun n => by
      have h1 := memLp_markov_sub_lapTest hV hdV Ψ (g n)
      convert h1 using 1
      funext ω
      exact hab n ω
    have hlim : Tendsto (fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂P) atTop (𝓝 0) := by
      refine hgL2.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hab n ω]
    set C : ι → Set Ω := fun i =>
      if Kf ⊆ U i ∧ (U i : Set ℂ) ⊆ V then E ∩ {ω | τ' ω ≤ s i ω} else ∅ with hC
    have hCm : ∀ i, MeasurableSet[hτ𝓖.measurableSpace] (C i) := fun i => by
      by_cases hi : Kf ⊆ U i ∧ (U i : Set ℂ) ⊆ V
      · simp only [hC, hi, and_self, ↓reduceIte]
        have h1 := hτ𝓖.measurableSet_le_stopping_time (hs i)
        simp only [WithTop.coe_le_coe] at h1
        exact @MeasurableSet.inter Ω hτ𝓖.measurableSpace _ _ hEτ h1
      · simp only [hC, hi, ↓reduceIte]; exact @MeasurableSet.empty Ω hτ𝓖.measurableSpace
    have hCE : ∀ i, C i ⊆ E := fun i => by
      by_cases hi : Kf ⊆ U i ∧ (U i : Set ℂ) ⊆ V
      · simp only [hC, hi, and_self, ↓reduceIte]; exact inter_subset_left
      · simp only [hC, hi, ↓reduceIte]; exact empty_subset _
    have hEC : ∀ᵐ ω ∂P, ω ∈ E → ∃ i, ω ∈ C i := by
      filter_upwards [hexh, hAK, hτζ'] with ω hω hAω hτω hωE
      have hdis : Disjoint Kf (fwdHull (fun r : ℝ => W r.toNNReal ω) (τ' ω)) := by
        have h1 : Disjoint (A ω) (V : Set ℂ) := hωE
        rw [hAω] at h1
        exact (h1.mono_right hKfV).symm
      obtain ⟨i, hi1, hi2, hi3⟩ := hω (τ' ω) hτω Kf hKfc (hKfV.trans hVH) hdis V V.isOpen hKfV
      refine ⟨i, ?_⟩
      simp only [hC, hi1, hi2, and_self, ↓reduceIte]
      exact ⟨hωE, hi3⟩
    have hpiece : ∀ i D, MeasurableSet[hτ𝓖.measurableSpace] D → D ⊆ C i →
        ∫ ω in D, Complex.exp (Complex.I * (h ω Φ : ℂ)) * Complex.exp (Complex.I * (b ω : ℂ)) ∂P =
          c * ∫ ω in D, Complex.exp (Complex.I * (b ω : ℂ)) ∂P := by
      intro i D hD hDC
      by_cases hi : Kf ⊆ U i ∧ (U i : Set ℂ) ⊆ V
      swap
      · have hD0 : D = ∅ := Set.subset_empty_iff.1 (hDC.trans (by simp only [hC, hi, ↓reduceIte]; rfl))
        simp [hD0]
      have hDC' : D ⊆ E ∩ {ω | τ' ω ≤ s i ω} := by simpa only [hC, hi, and_self, ↓reduceIte] using hDC
      have hDs : MeasurableSet[(hs i).measurableSpace] D :=
        measurableSet_stopped_of_le hτ𝓖 (hs i) hD fun ω hω => WithTop.coe_le_coe.2 (hDC' hω).2
      have hDm : MeasurableSet D := hτ𝓖.measurableSpace_le _ hD
      have hUi : U i ≤ upperHalfPlaneOpens := hUH i
      set f' : zsSub (U i : Set ℂ) := ⟨f.1, ⟨f.2.1, f.2.2.1, hi.1⟩⟩ with hf'
      have hΦ' : Φ = lapTest (U i) f' := by
        ext z
        rw [hΦ, coe_lapTest hV, coe_lapTest hUi]
        rfl
      set r : ℕ → ℝ := fun n => -(1 / 2) * ‖gradFeat (U i : Set ℂ) f'.1‖ ^ 2 -
        ⟪gradFeat (U i : Set ℂ) f'.1, covVec (U i : Set ℂ) (Ξ n)⟫ with hr_def
      -- the member identity along the approximations
      have hmemb : ∀ n, ∫ ω in D, Complex.exp (Complex.I * (h ω Φ : ℂ)) *
          Complex.exp (Complex.I * (a n ω : ℂ)) ∂P =
            Complex.exp ((r n : ℝ) : ℂ) * ∫ ω in D, Complex.exp (Complex.I * (a n ω : ℂ)) ∂P := by
        intro n
        have key := hind i f' (Ξ n) D hDs
        rw [← hΦ'] at key
        rw [← key]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [a, map_add, Complex.ofReal_add, mul_add, Complex.exp_add]
      -- the exponents converge
      have hfV : f'.1 ∈ zeroSpace (U i : Set ℂ) := f'.2
      have hinner : ∀ n, ⟪gradFeat (U i : Set ℂ) f'.1, covVec (U i : Set ℂ) (Ξ n)⟫ =
          ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ψ⟫ - ⟪gradFeat (V : Set ℂ) f.1,
            gradFeat (V : Set ℂ) (g n).1⟫ := fun n => by
        rw [hΞ, covVec_sub (U i).isOpen (hUH i), inner_sub_right,
          ← inner_gradFeat_covVec_eq (U i).isOpen V.isOpen hVH hi.2 hfV Ψ,
          ← inner_gradFeat_covVec_eq (U i).isOpen V.isOpen hVH hi.2 hfV (lapTest V (g n)),
          covVec_lapTest hV V.isOpen hVH subset_rfl (g n)]
      have hr : Tendsto r atTop (𝓝 (-(1 / 2) * ‖gradFeat (U i : Set ℂ) f'.1‖ ^ 2)) := by
        have h1 : Tendsto (fun n => ⟪gradFeat (V : Set ℂ) f.1, gradFeat (V : Set ℂ) (g n).1⟫) atTop
            (𝓝 ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ψ⟫) :=
          tendsto_const_nhds.inner hg
        have h2 : Tendsto (fun n => ⟪gradFeat (U i : Set ℂ) f'.1, covVec (U i : Set ℂ) (Ξ n)⟫) atTop
            (𝓝 0) := by
          simp_rw [hinner]
          simpa using (tendsto_const_nhds (x := ⟪gradFeat (V : Set ℂ) f.1, covVec (V : Set ℂ) Ψ⟫)).sub h1
        have h3 := (tendsto_const_nhds (x := -(1 / 2) * ‖gradFeat (U i : Set ℂ) f'.1‖ ^ 2)).sub h2
        rw [sub_zero] at h3
        exact h3
      -- the constant `c`
      have hc : c = Complex.exp (((-(1 / 2) * ‖gradFeat (U i : Set ℂ) f'.1‖ ^ 2 : ℝ) : ℂ)) := by
        have key := hind i f' 0 univ (@MeasurableSet.univ _ (hs i).measurableSpace)
        rw [← hΦ', add_zero] at key
        simp only [Measure.restrict_univ] at key
        rw [hc_def, key, covVec_zero _ (U i).isOpen (hUH i), inner_zero_right, sub_zero]
        simp
      -- the limits
      have hZ1 : ∀ ω, ‖D.indicator (fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ))) ω‖ ≤ 1 := fun ω => by
        by_cases hω : ω ∈ D
        · rw [indicator_of_mem hω]; exact hnorm1 _
        · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
      have hZ2 : ∀ ω, ‖D.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := fun ω => by
        by_cases hω : ω ∈ D
        · rw [indicator_of_mem hω, norm_one]
        · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
      have hZ1m : Measurable (D.indicator fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ))) :=
        (GFF.measurable_exp_I_mul hhΦm).indicator hDm
      have hZ2m : Measurable (D.indicator fun _ => (1 : ℂ)) := measurable_const.indicator hDm
      have e1 : ∀ x : Ω → ℝ, ∫ ω in D, Complex.exp (Complex.I * (h ω Φ : ℂ)) *
          Complex.exp (Complex.I * (x ω : ℂ)) ∂P = ∫ ω, Complex.exp (Complex.I * (x ω : ℂ)) *
            D.indicator (fun ω => Complex.exp (Complex.I * (h ω Φ : ℂ))) ω ∂P := fun x => by
        rw [← setIntegral_eq_integral_indicator_mul hDm]
        exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
      have e2 : ∀ x : Ω → ℝ, ∫ ω in D, Complex.exp (Complex.I * (x ω : ℂ)) ∂P =
          ∫ ω, Complex.exp (Complex.I * (x ω : ℂ)) * D.indicator (fun _ => (1 : ℂ)) ω ∂P := fun x => by
        rw [← setIntegral_eq_integral_indicator_mul hDm]
        exact integral_congr_ae (Eventually.of_forall fun ω => (mul_one _).symm)
      have hL1 := tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZ1
        (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hZ1m).aestronglyMeasurable)
        ((GFF.measurable_exp_I_mul hbm).mul hZ1m).aestronglyMeasurable
      have hL2 := tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZ2
        (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hZ2m).aestronglyMeasurable)
        ((GFF.measurable_exp_I_mul hbm).mul hZ2m).aestronglyMeasurable
      simp_rw [← e1] at hL1
      simp_rw [← e2] at hL2
      have hR := ((Complex.continuous_exp.comp Complex.continuous_ofReal).tendsto _).comp hr
      have hRL := hR.mul hL2
      simp_rw [Function.comp_apply, ← hmemb] at hRL
      rw [hc]
      exact tendsto_nhds_unique hL1 hRL
    exact setIntegral_eq_mul_of_pieces hτ𝓖.measurableSpace_le hF₁i hF₂i c C hCm hCE hEC hpiece
  have hloc : IsLocalSet A h P := ((isLocalSet_tfae hh hAm hAc).out 1 4).1 hav
  exact IsLocalSet.congr_set hloc hAK.symm

end Family

end Coupling

end InteractingSLE
