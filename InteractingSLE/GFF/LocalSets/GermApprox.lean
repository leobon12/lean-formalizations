import InteractingSLE.GFF.LocalSets.CoverLaw
import QuantumZipper.Proofs.Probability.GermZeroOne

/-!
# From the covers to the germ σ-algebra (Lemma 3.6, (i) ⇒ (iii), the limit `j → ∞`)

Specification §3.2, pp. 50–53: the covers `C_j` are "sandwiched between `A_{δ_j}` and
`A_{(1+√2)δ_j}`", so the germ σ-algebra `𝒜` sits inside every `𝒢_j` and the conditional means
`Q_j h` only see the germ of the field. Here:

* `germSigmaAt_le_aeSigma` : `𝒜_{1/(j+2)} ⊆ 𝒢_j` up to null sets (the field on the germ
  neighbourhood of radius `1/(j+2)` is a pairing of `Q_j h`, since `G_T h` vanishes off `W_T`);
* `exists_tendsto_condExp_antitone` : `E[f | 𝒢_j] → ` a limit in `L²` for a decreasing family
  (the `L²` form of reverse martingale convergence, via QuantumZipper's monotone projections);
* `exists_cutoff_coverOpen`, `exists_measurable_coverProj_germSigmaAt` : for `j ≥ ⌈6/δ⌉`, each
  pairing of `Q_j h` is a.s. `𝒜_δ`-measurable (germ lemma `exists_measurable_markovCompl_germ` on
  each value of the cover, with a cutoff at distance `δ/8` from `ℍ ∖ W_T`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

section AeSigma

variable {Ω : Type*}

/-- The sets that coincide almost surely with a set of `m`. -/
@[instance_reducible]
def aeSigma (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : @Measure Ω mΩ) :
    MeasurableSpace Ω where
  MeasurableSet' G := ∃ G', MeasurableSet[m] G' ∧ G =ᵐ[P] G'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ m, EventuallyEqSet.rfl⟩
  measurableSet_compl G := by
    rintro ⟨G', hG', he⟩
    exact ⟨G'ᶜ, hG'.compl, he.compl⟩
  measurableSet_iUnion f hf := by
    choose G' hG' he using hf
    exact ⟨⋃ i, G' i, MeasurableSet.iUnion hG', EventuallyEqSet.countable_iUnion he⟩

lemma le_aeSigma (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : @Measure Ω mΩ) :
    m ≤ aeSigma m P :=
  fun G hG => ⟨G, hG, EventuallyEqSet.rfl⟩

end AeSigma

section Germ1

variable {Ω : Type u} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

lemma coverRad_eq (j : ℕ) : coverRad j = 1 / (((j + 1 : ℕ) : ℝ) + 1) := by
  unfold coverRad; push_cast; ring_nf

/-- **The germ σ-algebra is contained in every `𝒢_j`, up to null sets** (specification p. 53:
`𝒜 ⊆ 𝒜_δ`, and the field on a germ neighbourhood inside the cover is a pairing of `Q_j h`). -/
theorem germSigmaAt_le_aeSigmaM (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hAℳ : MeasurableSpace.comap A hittingSigma ≤ ℳ) (j : ℕ) :
    germSigmaAt A h (coverRad j) ≤ aeSigma (coverSigmaM ℳ j A h) P := by
  have hAc : MeasurableSpace.comap A hittingSigma ≤ coverSigmaM ℳ j A h := hAℳ.trans le_sup_left
  refine sup_le (hAc.trans (le_aeSigma _ P)) (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨φ, B, hB, rfl⟩
  have hδ := coverRad_pos j
  have hsub : MeasurableSet[coverSigmaM ℳ j A h] {ω | tsupport φ ⊆ germNbhd (coverRad j) (A ω)} :=
    hAc _
      ⟨_, measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset hδ, rfl⟩
  have hP : Measurable[coverSigmaM ℳ j A h] fun ω => coverProj j A h ω φ :=
    (measurable_distOn_apply φ).comp ((comap_measurable (coverProj j A h)).mono
      (le_sup_of_le_right (le_iSup₂_of_le (f := fun (k : ℕ) (_ : j ≤ k) =>
        MeasurableSpace.comap (coverProj k A h) inferInstance) j le_rfl le_rfl)) le_rfl)
  refine ⟨{ω | tsupport φ ⊆ germNbhd (coverRad j) (A ω)} ∩
    (fun ω => coverProj j A h ω φ) ⁻¹' B, hsub.inter (hP hB), ?_⟩
  have hzero : ∀ᵐ ω ∂P, ∀ T ∈ (coverIdx j).powerset,
      GFF.restrictDist (GFF.outsideOpens (markovOpen T) upperHalfPlaneOpens)
        (coverMarkov.{u} T (h ω)) = 0 :=
    (eventually_all_finset _).2 fun T _ =>
      (isMarkovDecomposition_coverMarkov hh T).ae_restrictDist_outside_eq_zero
  filter_upwards [hzero] with ω hω
  show (ω ∈ _ ∩ _) = (ω ∈ _ ∩ _)
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
  refine propext ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩ <;>
  · set T := removedIdx j (A ω)
    have hT := mem_coverAtom_powerset (j := j) (A := A) ω
    have hφout : tsupport φ ⊆ GFF.outsideOpens (markovOpen T) upperHalfPlaneOpens := by
      intro z hz
      refine ⟨φ.tsupport_subset hz, ?_⟩
      show z ∉ closure (markovOpen T : Set ℂ)
      rw [coe_markovOpen (Finset.mem_powerset.1 hT)]
      exact Set.disjoint_left.1 ((disjoint_germNbhd_coverCompl j (A ω)).closure_right
        (isOpen_H.inter (isOpen_thickening.union (isOpen_lt continuous_const continuous_norm))))
        (h1 hz)
    have h0 : coverMarkov.{u} T (h ω) φ = 0 := by
      have := congrArg (fun S => S (testOnOfSubset φ hφout)) (hω T hT)
      simp only [GFF.restrictDist_apply, testIncl_testOnOfSubset (GFF.outsideOpens_le _ _)] at this
      exact this
    have e : coverProj j A h ω φ = h ω φ := by
      simp only [coverProj, markovCompl, sub_apply]
      rw [show coverMarkov.{u} (removedIdx j (A ω)) (h ω) φ = 0 from h0, sub_zero]
    first | (rw [e]; exact h2) | (rw [← e]; exact h2)

omit ℳ in
/-- **The germ σ-algebra is contained in every `𝒢_j`, up to null sets.** -/
theorem germSigmaAt_le_aeSigma (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (j : ℕ) :
    germSigmaAt A h (coverRad j) ≤ aeSigma (coverSigma j A h) P :=
  germSigmaAt_le_aeSigmaM hh le_rfl j

end Germ1

section L2Conv

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`L²` convergence of conditional expectations along a decreasing sequence of σ-algebras**
(the `L²` form of the reverse martingale convergence theorem, from the monotone convergence of
orthogonal projections, QuantumZipper `GermZeroOne.exists_tendsto_starProjection_antitone`). -/
theorem exists_tendsto_condExp_antitone {𝒢 : ℕ → MeasurableSpace Ω} (hle : ∀ n, 𝒢 n ≤ mΩ)
    (hanti : Antitone 𝒢) {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∃ y : Ω → ℝ, MemLp y 2 P ∧
      Tendsto (fun n => ∫ ω, ((P[f|𝒢 n]) ω - y ω) ^ 2 ∂P) atTop (𝓝 0) := by
  have : ∀ n, CompleteSpace (lpMeas ℝ ℝ (𝒢 n) 2 P) := fun n => by
    have : Fact (𝒢 n ≤ mΩ) := ⟨hle n⟩; infer_instance
  set F : Lp ℝ 2 P := hf.toLp f
  have hKanti : Antitone (fun n => lpMeas ℝ ℝ (𝒢 n) 2 P) := by
    intro a b hab u hu
    rw [mem_lpMeas_iff_aestronglyMeasurable] at hu ⊢
    obtain ⟨g, hg, he⟩ := hu
    exact ⟨g, hg.mono (hanti hab), he⟩
  obtain ⟨y, hy, -⟩ := QuantumZipper.GermZeroOne.exists_tendsto_starProjection_antitone _ hKanti F
  have hyn : ∀ n, (lpMeas ℝ ℝ (𝒢 n) 2 P).starProjection F
      = (condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) := fun n => by
    rw [Submodule.starProjection_apply]; rfl
  have hae : ∀ n, ((condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] P[f | 𝒢 n] :=
    fun n => hf.condExpL2_ae_eq_condExp (hle n)
  refine ⟨y, Lp.memLp y, ?_⟩
  have hnorm : Tendsto (fun n => ‖(lpMeas ℝ ℝ (𝒢 n) 2 P).starProjection F - y‖ ^ 2) atTop
      (𝓝 (0 ^ 2)) := ((tendsto_iff_norm_sub_tendsto_zero).1 hy).pow 2
  rw [zero_pow two_ne_zero] at hnorm
  refine hnorm.congr fun n => ?_
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, hyn n]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (condExpL2 ℝ ℝ (hle n) F : Lp ℝ 2 P) y, hae n] with ω h1 h2
  rw [h1, Pi.sub_apply, h2, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

end L2Conv

section Cutoff

/-- A smooth cutoff for the cover value `W = W_T`: `χ = 1` where `dist(·, Wᶜ) ≥ 2ε`, `χ = 0` where
`dist(·, Wᶜ) ≤ ε`. -/
theorem exists_cutoff_coverOpen {j : ℕ} {T : Finset (ℕ × ℂ)} (hT : T ⊆ coverIdx j) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ z, χ z ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ coverOpen T ∧
      tsupport (fun z => 1 - χ z) ∩ H ⊆ {z | z ∈ H ∧ infDist z (coverOpen T)ᶜ < 3 * ε} := by
  set W := coverOpen T
  have hWo : IsOpen W := isOpen_coverOpen T
  have hs : IsOpen {z : ℂ | ε < infDist z Wᶜ} := isOpen_lt continuous_const (continuous_infDist_pt Wᶜ)
  have ht : IsClosed {z : ℂ | 2 * ε ≤ infDist z Wᶜ} :=
    isClosed_le continuous_const (continuous_infDist_pt Wᶜ)
  have hts : {z : ℂ | 2 * ε ≤ infDist z Wᶜ} ⊆ {z : ℂ | ε < infDist z Wᶜ} := fun z hz => by
    simp only [mem_ofPred_eq] at hz ⊢; linarith
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hs ht hts
  have hsubW : {z : ℂ | ε ≤ infDist z Wᶜ} ⊆ W := fun z hz => by
    by_contra hzW
    have : infDist z Wᶜ = 0 := infDist_zero_of_mem hzW
    simp only [mem_ofPred_eq] at hz; linarith
  have htsupp : tsupport χ ⊆ W := by
    rw [tsupport, hχs]
    exact (closure_lt_subset_le continuous_const (continuous_infDist_pt Wᶜ)).trans hsubW
  refine ⟨χ, hχ, fun z => hχr ⟨z, rfl⟩, ?_, htsupp, ?_⟩
  · exact (isCompact_closure_coverOpen hT).of_isClosed_subset (isClosed_tsupport _)
      (htsupp.trans subset_closure)
  · rintro z ⟨hz, hzH⟩
    refine ⟨hzH, ?_⟩
    have hsupp : Function.support (fun z => 1 - χ z) ⊆ {z : ℂ | infDist z Wᶜ < 2 * ε} := by
      intro w hw
      simp only [Function.mem_support, ne_eq, sub_eq_zero] at hw
      simp only [mem_ofPred_eq]
      by_contra hc
      exact hw ((hχ1 w).1 (not_lt.1 hc)).symm
    have := closure_mono hsupp hz
    have h2 := (closure_lt_subset_le (continuous_infDist_pt Wᶜ) continuous_const) this
    simp only [mem_ofPred_eq] at h2
    linarith

end Cutoff


section Trace

variable {Ω : Type*}

/-- The trace σ-algebra: the sets whose intersection with `F ∈ m` is `m`-measurable. -/
@[instance_reducible]
def traceSigma (m : MeasurableSpace Ω) (F : Set Ω) (hF : MeasurableSet[m] F) :
    MeasurableSpace Ω where
  MeasurableSet' E := MeasurableSet[m] (E ∩ F)
  measurableSet_empty := by simp
  measurableSet_compl E hE := by
    have e : Eᶜ ∩ F = F \ (E ∩ F) := by
      ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]; exact hF.diff hE
  measurableSet_iUnion f hf := by
    rw [iUnion_inter]; exact MeasurableSet.iUnion hf

end Trace

section GermMeas

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
lemma germSigmaAt_le' (hA : Measurable[mΩ, hittingSigma] A) (hh : Measurable h) {δ : ℝ}
    (hδ : 0 < δ) : germSigmaAt A h δ ≤ mΩ := by
  refine sup_le hA.comap_le (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨φ, B, hB, rfl⟩
  exact (hA (measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset hδ)).inter
    ((measurable_distOn_apply φ).comp hh hB)

omit mΩ in
lemma germNbhd_mono {δ δ' : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ) (S : Set ℂ) :
    germNbhd δ' S ⊆ germNbhd δ S := by
  rintro z ⟨hz, h1 | h1⟩
  · exact ⟨hz, Or.inl (thickening_mono hδ _ h1)⟩
  · refine ⟨hz, Or.inr ?_⟩
    have : 1 / δ ≤ 1 / δ' := one_div_le_one_div_of_le hδ' hδ
    exact lt_of_le_of_lt this h1

omit mΩ [IsProbabilityMeasure P] in
lemma germSigmaAt_mono {δ δ' : ℝ} (hδ' : 0 < δ')
    (hδ : δ' ≤ δ) : germSigmaAt A h δ' ≤ germSigmaAt A h δ := by
  refine sup_le le_sup_left (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨φ, B, hB, rfl⟩
  have e : {ω | tsupport φ ⊆ germNbhd δ' (A ω)} ∩ (fun ω => h ω φ) ⁻¹' B =
      {ω | tsupport φ ⊆ germNbhd δ' (A ω)} ∩
        ({ω | tsupport φ ⊆ germNbhd δ (A ω)} ∩ (fun ω => h ω φ) ⁻¹' B) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h1.trans (germNbhd_mono hδ' hδ _), h2⟩, fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩⟩
  rw [e]
  refine MeasurableSet.inter (le_sup_left (b := MeasurableSpace.generateFrom _) _
    ⟨_, measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset hδ', rfl⟩) ?_
  exact le_sup_right (a := MeasurableSpace.comap A hittingSigma) _
    (MeasurableSpace.measurableSet_generateFrom ⟨φ, B, hB, rfl⟩)

omit mΩ [IsProbabilityMeasure P] in
lemma germSigma_eq_iInf : germSigma A h = ⨅ n : ℕ, germSigmaAt A h (1 / ((n : ℝ) + 1)) := rfl

omit mΩ [IsProbabilityMeasure P] in
/-- A function that is, on a `σ(A)`-event `F`, measurable for the field on an open set `O` lying in
the germ neighbourhood of every `A ω`, `ω ∈ F`, is `𝒜_δ`-measurable once multiplied by `1_F`. -/
lemma measurable_indicator_germSigmaAt {δ : ℝ} {O : Set ℂ} {F : Set Ω}
    (hF : MeasurableSet[MeasurableSpace.comap A hittingSigma] F)
    (hFO : ∀ ω ∈ F, O ⊆ germNbhd δ (A ω)) {Z : Ω → ℝ} (hZ : Measurable[fieldSigmaOn h O] Z) :
    Measurable[germSigmaAt A h δ] (F.indicator Z) := by
  have hF' : MeasurableSet[germSigmaAt A h δ] F := le_sup_left (b := MeasurableSpace.generateFrom _) _ hF
  let 𝒞 : MeasurableSpace Ω := traceSigma (germSigmaAt A h δ) F hF'
  have hle : fieldSigmaOn h O ≤ 𝒞 := by
    refine iSup₂_le fun ψ hψ => ?_
    rintro _ ⟨B, hB, rfl⟩
    show MeasurableSet[germSigmaAt A h δ] ((fun ω => h ω ψ) ⁻¹' B ∩ F)
    have e : (fun ω => h ω ψ) ⁻¹' B ∩ F =
        ({ω | tsupport ψ ⊆ germNbhd δ (A ω)} ∩ (fun ω => h ω ψ) ⁻¹' B) ∩ F := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨hψ.trans (hFO ω h2), h1⟩, h2⟩, fun ⟨⟨_, h1⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e]
    refine MeasurableSet.inter ?_ hF'
    exact le_sup_right (a := MeasurableSpace.comap A hittingSigma) _
      (MeasurableSpace.measurableSet_generateFrom ⟨ψ, B, hB, rfl⟩)
  intro B hB
  have e : F.indicator Z ⁻¹' B = (Z ⁻¹' B ∩ F) ∪ (Fᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
    ext ω
    by_cases hω : ω ∈ F <;> simp [hω, indicator]
  rw [e]
  have h1 : MeasurableSet[germSigmaAt A h δ] (Z ⁻¹' B ∩ F) := hle _ (hZ hB)
  refine h1.union (hF'.compl.inter ?_)
  by_cases h0 : (0 : ℝ) ∈ B
  · simp only [h0, ofPred_true]; exact @MeasurableSet.univ _ (germSigmaAt A h δ)
  · simp only [h0, ofPred_false]; exact @MeasurableSet.empty _ (germSigmaAt A h δ)

/-- **`Q_j h` only sees the germ**: for `0 < δ ≤ 1` and `j ≥ ⌈6/δ⌉`, each pairing of `Q_j h`
is almost surely `𝒜_δ`-measurable (germ lemma on each value of the cover). -/
theorem exists_measurable_coverProj_germSigmaAt (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {j : ℕ}
    (hj : ⌈6 / δ⌉₊ ≤ j) (φ : TestOn upperHalfPlaneOpens) :
    ∃ Z : Ω → ℝ, Measurable[germSigmaAt A h δ] Z ∧
      (fun ω => coverProj j A h ω φ) =ᵐ[P] Z := by
  have hε : 0 < δ / 8 := by positivity
  have key : ∀ T ∈ (coverIdx j).powerset, ∃ Z : Ω → ℝ,
      Measurable[germSigmaAt A h δ] ((coverAtom j A T).indicator Z) ∧
      (fun ω => markovCompl (coverMarkov.{u} T) (h ω) φ) =ᵐ[P] Z := by
    intro T hT
    have hT' := Finset.mem_powerset.1 hT
    obtain ⟨χ, hχ, hχ01, hχc, hχW, hχO⟩ := exists_cutoff_coverOpen hT' hε
    set O : Set ℂ := {z | z ∈ H ∧ infDist z (coverOpen T)ᶜ < 3 * (δ / 8)}
    have hχW' : tsupport χ ⊆ (markovOpen T : Set ℂ) := by rwa [coe_markovOpen hT']
    obtain ⟨Z, hZ, hZe⟩ := exists_measurable_markovCompl_germ hh (markovOpen_subset_H T)
      (isMarkovDecomposition_coverMarkov hh T) hχ hχ01 hχc hχW' hχO φ
    refine ⟨Z, measurable_indicator_germSigmaAt ⟨_, measurableSet_removedIdx_eq j T, rfl⟩ ?_ hZ,
      hZe⟩
    intro ω hω z ⟨hzH, hz⟩
    have hne : ((coverOpen T)ᶜ).Nonempty := ⟨-Complex.I, fun hI =>
      absurd (show (0 : ℝ) < (-Complex.I).im from coverOpen_subset_H hT' hI) (by simp)⟩
    obtain ⟨w, hw, hzw⟩ := (infDist_lt_iff hne).1 hz
    have hwc : w ∉ coverCompl j (A ω) := by
      have hω' : removedIdx j (A ω) = T := hω
      rw [coverCompl, hω']; exact hw
    exact mem_germNbhd_of_dist_lt hδ hδ1 hj hzH hwc hzw
  choose! Z hZm hZe using key
  refine ⟨fun ω => ∑ T ∈ (coverIdx j).powerset, (coverAtom j A T).indicator (Z T) ω,
    Finset.measurable_sum _ fun T hT => hZm T hT, ?_⟩
  filter_upwards [(eventually_all_finset _).2 hZe] with ω hω
  have hT0 := mem_coverAtom_powerset (j := j) (A := A) ω
  rw [Finset.sum_eq_single (removedIdx j (A ω))]
  · rw [indicator_of_mem (show ω ∈ coverAtom j A (removedIdx j (A ω)) from rfl)]
    exact hω _ hT0
  · intro T _ hT
    rw [indicator_of_notMem]
    simp only [coverAtom, mem_ofPred_eq]
    exact fun h' => hT h'.symm
  · exact fun h' => absurd hT0 h'

end GermMeas

end LocalSets
end InteractingSLE
