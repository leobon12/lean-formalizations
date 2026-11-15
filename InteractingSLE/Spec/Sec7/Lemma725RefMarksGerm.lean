/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.Prop32
import InteractingSLE.GFF.LocalSets.MarkovNesting
import InteractingSLE.Spec.Sec7.PocketStopWallsCore
import InteractingSLE.Spec.Coupling.WholeFieldMarked
import InteractingSLE.Spec.Coupling.WholeField2Germ
import InteractingSLE.Spec.Sec7.Lemma72

/-!
# The germ of a smaller marked set can be added to the marks of a larger local set

Packet PROVE-LEMMA725REF6 (PROVE-LEMMA725REF5 §5 item 1, ruling R68 as amended). Specification §7.4, Aux. lemma 124
(`source/spec/p385-432.md` L171–L196: "project the marked decomposition of `B ∪ R_T` onto the Dirichlet space of `C`"),
and §3.1, Propositions 3.1–3.2 (pp. 42–44).

**`isHistoryAvoidanceLocal_sup_germSigma`.** Let `h` be a zero-boundary GFF on `ℍ`, let `E` satisfy the
history-marked avoidance criterion (Aux. lemma 18) for marks `ℋ`, and let `E₀` be an `ℋ`-measurable random set with
`E₀ ∩ ℍ ⊆ E`. Then `E` satisfies the criterion for the marks `ℋ ∨ 𝒜_{E₀}` (`𝒜_{E₀}` the germ σ-algebra of `E₀` and
`h`, p. 50).

## Proof (own argument)

Fix an open `U ⊆ ℍ`, the Markov decomposition `h = G h + Y` along `U` (`Y = h − G h`), and the avoidance events
`D = {E ∩ U = ∅} ⊆ D₀ = {E₀ ∩ U = ∅}`.

1. *Exhaustion with margins* (`exhOpen`): `Uₙ = B(0, n) ∖ cthickening_{1/(n+1)}(Uᶜ)` has compact closure in `Uₙ₊₁ ⊆ U`,
   every compact subset of `U` lies in some `Uₙ`, and on `D₀` the germ neighbourhood `germNbhd (1/(n+1)) E₀` misses
   `Uₙ` (`disjoint_germNbhd_exhOpen`).
2. *Traces of germ events* (`le_traceSigma`): with `Yₙ = h − Gₙ h` the Markov decomposition along `Uₙ`, every event `F`
   of `ℋ ∨ 𝒜^{1/(n+1)}_{E₀}` has `D₀ ∩ F = D₀ ∩ F'` a.s. for some `F' ∈ σ(Yₙ) ∨ ℋ`: a germ generator
   `{supp φ ⊆ germNbhd E₀} ∩ {h(φ) ∈ B}` is empty on `D₀` unless `supp φ ∩ Uₙ = ∅`, and then `h(φ) = Yₙ(φ)` a.s. (the
   zero-boundary part along `Uₙ` has variance `0` against `φ`, `ae_apply_eq_zero_of_disjoint`).
3. *Dynkin* (`isCompEvent_inter_comap_sup`): `P[D ∩ F | h]` is a function of `Y`, hence of `Yₙ` (Markov nesting), for
   `F ∈ ℋ`, and `P[D ∩ Yₙ⁻¹B ∩ F | h] = 1_B(Yₙ) P[D ∩ F | h]`; the π–λ theorem extends this to `F ∈ σ(Yₙ) ∨ ℋ`.
   Hence, for every `n`, `P[D ∩ F | h]` is a.s. a function of `Yₙ`, for every `F ∈ ℋ ∨ 𝒜_{E₀}`.
4. *Intersection over `n`* (`exists_comp_markovCompl_of_isCompEvent`): every level set of `P[D ∩ F | h]` lies, up to
   null sets, in `σ(Yₙ₊₁) ⊆ σ(h|_{ℍ ∖ cl Uₙ})` (Proposition 3.2 for the relatively compact `Uₙ₊₁`), hence in
   `⋂ₙ σ(h|_{ℍ ∖ cl Uₙ})`, hence in `σ(Y)` (Proposition 3.2's other inclusion, from the germ zero-one law of the
   zero-boundary part along `U`); Doob–Dynkin up to null sets gives the Borel function of `Y`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefMarks

open LocalSets WholeField PocketStopWalls

/-! ### A compact exhaustion with germ margins -/

section Exhaustion

/-- The `n`-th exhaustion set of `U`: the points of norm `< n` at distance `> 1/(n+1)` from `Uᶜ`. -/
def exhOpen (U : Set ℂ) (n : ℕ) : Opens ℂ :=
  ⟨ball 0 n \ cthickening (1 / ((n : ℝ) + 1)) Uᶜ, isOpen_ball.sdiff isClosed_cthickening⟩

theorem coe_exhOpen (U : Set ℂ) (n : ℕ) :
    (exhOpen U n : Set ℂ) = ball 0 n \ cthickening (1 / ((n : ℝ) + 1)) Uᶜ := rfl

theorem closure_exhOpen_subset (U : Set ℂ) (n : ℕ) :
    closure (exhOpen U n : Set ℂ) ⊆ closedBall 0 n \ thickening (1 / ((n : ℝ) + 1)) Uᶜ := by
  intro z hz
  refine ⟨closure_ball_subset_closedBall (closure_mono sdiff_subset hz), fun hzt => ?_⟩
  have hdis : Disjoint (thickening (1 / ((n : ℝ) + 1)) Uᶜ) (exhOpen U n : Set ℂ) :=
    Set.disjoint_left.2 fun w hw hw' => hw'.2 (thickening_subset_cthickening _ _ hw)
  exact Set.disjoint_left.1 (hdis.closure_right isOpen_thickening) hzt hz

theorem isCompact_closure_exhOpen (U : Set ℂ) (n : ℕ) : IsCompact (closure (exhOpen U n : Set ℂ)) :=
  (isCompact_closedBall 0 (n : ℝ)).of_isClosed_subset isClosed_closure
    ((closure_exhOpen_subset U n).trans sdiff_subset)

theorem closure_exhOpen_subset_self (U : Set ℂ) (n : ℕ) : closure (exhOpen U n : Set ℂ) ⊆ U := fun z hz => by
  by_contra hzU
  exact (closure_exhOpen_subset U n hz).2 (self_subset_thickening (by positivity) _ hzU)

theorem exhOpen_subset (U : Set ℂ) (n : ℕ) : (exhOpen U n : Set ℂ) ⊆ U :=
  subset_closure.trans (closure_exhOpen_subset_self U n)

theorem closure_exhOpen_subset_succ (U : Set ℂ) (n : ℕ) :
    closure (exhOpen U n : Set ℂ) ⊆ exhOpen U (n + 1) := fun z hz => by
  obtain ⟨h1, h2⟩ := closure_exhOpen_subset U n hz
  refine ⟨?_, fun h3 => h2 ?_⟩
  · rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball, dist_zero_right]
    push_cast
    linarith
  · refine cthickening_subset_thickening' (by positivity) ?_ _ h3
    exact one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)

theorem exhOpen_mono (U : Set ℂ) : Monotone fun n => (exhOpen U n : Set ℂ) :=
  monotone_nat_of_le_succ fun n => subset_closure.trans (closure_exhOpen_subset_succ U n)

theorem exists_subset_exhOpen {U : Set ℂ} (hU : IsOpen U) {C : Set ℂ} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ n, C ⊆ exhOpen U n := by
  obtain ⟨δ, hδ, hdis⟩ := (Set.disjoint_compl_right_iff_subset.2 hCU).exists_cthickenings hC hU.isClosed_compl
  obtain ⟨R, hR⟩ := hC.isBounded.subset_ball (0 : ℂ)
  obtain ⟨n₁, hn₁⟩ := exists_nat_gt R
  obtain ⟨n₂, hn₂⟩ := exists_nat_one_div_lt hδ
  refine ⟨max n₁ n₂, fun z hz => ⟨?_, fun hzc => ?_⟩⟩
  · have h1 := hR hz
    rw [mem_ball, dist_zero_right] at h1 ⊢
    have : (n₁ : ℝ) ≤ (max n₁ n₂ : ℕ) := Nat.cast_le.2 (le_max_left _ _)
    linarith
  · have hle : 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) ≤ δ := by
      refine le_trans ?_ hn₂.le
      exact one_div_le_one_div_of_le (by positivity) (by gcongr; exact le_max_right _ _)
    exact Set.disjoint_left.1 hdis (self_subset_cthickening C hz) (cthickening_mono hle _ hzc)

/-- **On the avoidance event the germ neighbourhood misses the exhaustion set**: if `S` does not meet `U ⊆ ℍ`, then
`germNbhd (1/(n+1)) S` does not meet `Uₙ`. -/
theorem disjoint_germNbhd_exhOpen {U : Set ℂ} (hUH : U ⊆ H) (n : ℕ) {S : Set ℂ} (hS : Disjoint S U) :
    Disjoint (germNbhd (1 / ((n : ℝ) + 1)) S) (exhOpen U n) := by
  refine Set.disjoint_left.2 fun z hz hzU => ?_
  obtain ⟨-, hz | hz⟩ := hz
  · have hsub : (S ∩ H) ∪ {w : ℂ | w.im = 0} ⊆ Uᶜ := by
      rintro w (hw | hw) hwU
      · exact Set.disjoint_left.1 hS hw.1 hwU
      · have h0 : w.im = 0 := hw
        have : 0 < w.im := hUH hwU
        rw [h0] at this
        exact lt_irrefl _ this
    exact hzU.2 (thickening_subset_cthickening _ _ (thickening_subset_of_subset _ hsub hz))
  · have h1 := hzU.1
    rw [mem_ball, dist_zero_right] at h1
    rw [mem_ofPred_eq, one_div_one_div] at hz
    linarith

end Exhaustion

/-! ### The zero-boundary part vanishes against tests supported off its domain -/

section Vanish

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`h_V(φ) = 0` almost surely when `supp φ ∩ V = ∅`** (variance `0`, Proposition 3.1). -/
theorem ae_apply_eq_zero_of_disjoint {V D : Opens ℂ} {X : Ω → DistOn D} (hX : GFF.IsZBGFFExtOn V D X P)
    {ψ : TestOn D} (hψ : Disjoint (tsupport ψ) (V : Set ℂ)) : ∀ᵐ ω ∂P, X ω ψ = 0 := by
  have hind : (V : Set ℂ).indicator (ψ : ℂ → ℝ) = 0 := by
    funext x
    by_cases hx : x ∈ (V : Set ℂ)
    · rw [indicator_of_mem hx]
      exact image_eq_zero_of_notMem_tsupport (Set.disjoint_right.1 hψ hx)
    · rw [indicator_of_notMem hx]
      rfl
  have hG : HasGaussianLaw (fun ω => X ω ψ) P := hX.gaussian.hasGaussianLaw_eval ψ
  have hvar : Var[fun ω => X ω ψ; P] = 0 := by
    rw [← covariance_self hG.aemeasurable, hX.covariance_eq, hind, GFF.zeroGFFTestCov_zero_zero]
  have hmap := hG.map_eq_gaussianReal
  rw [hX.centered, hvar, Real.toNNReal_zero, gaussianReal_zero_var] at hmap
  have h0 : ∀ᵐ x ∂(P.map fun ω => X ω ψ), x = 0 := by
    rw [hmap]
    exact (ae_dirac_iff (measurableSet_singleton 0)).2 rfl
  exact ae_of_ae_map hG.aemeasurable h0

/-- For a Markov decomposition along `V`, the field and its complementary projection agree almost surely against a
test function supported off `V`. -/
theorem ae_apply_eq_markovCompl {V : Opens ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition V upperHalfPlaneOpens h (fun ω => G (h ω)) P) {φ : TestOn upperHalfPlaneOpens}
    (hφ : Disjoint (tsupport φ) (V : Set ℂ)) : ∀ᵐ ω ∂P, h ω φ = markovCompl G (h ω) φ := by
  filter_upwards [ae_apply_eq_zero_of_disjoint hd.isZBGFFExtOn hφ] with ω hω
  rw [markovCompl, sub_apply, hω, sub_zero]

end Vanish

/-! ### Traces of the germ events on the avoidance event -/

section Trace

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- The σ-algebra of the events `Q` whose trace on `D₀` agrees almost surely with the trace of an event of
`σ(Y) ∨ ℋ`. -/
@[instance_reducible]
def traceSigma (P : Measure Ω) (Y : Ω → DistOn upperHalfPlaneOpens) (ℋ : MeasurableSpace Ω) (D₀ : Set Ω) :
    MeasurableSpace Ω where
  MeasurableSet' Q := ∃ Q', MeasurableSet[MeasurableSpace.comap Y inferInstance ⊔ ℋ] Q' ∧ D₀ ∩ Q =ᵐ[P] D₀ ∩ Q'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ (MeasurableSpace.comap Y inferInstance ⊔ ℋ), EventuallyEq.rfl⟩
  measurableSet_compl Q := by
    rintro ⟨Q', hQ', he⟩
    refine ⟨Q'ᶜ, hQ'.compl, ?_⟩
    have e1 : ∀ S : Set Ω, D₀ ∩ Sᶜ = D₀ \ (D₀ ∩ S) := fun S => by
      ext ω
      simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]
      tauto
    rw [e1 Q, e1 Q']
    exact EventuallyEqSet.diff EventuallyEq.rfl he
  measurableSet_iUnion f hf := by
    choose g hg hfg using hf
    refine ⟨⋃ i, g i, MeasurableSet.iUnion hg, ?_⟩
    rw [inter_iUnion, inter_iUnion]
    exact EventuallyEqSet.countable_iUnion hfg

/-- **The germ events of `E₀` at scale `δ`, traced on `D₀`, are events of `σ(Y) ∨ ℋ`** when `E₀` is `ℋ`-measurable,
the germ neighbourhood misses `V` on `D₀`, and `h(φ) = Y(φ)` a.s. for every test `φ` supported off `V`. -/
theorem le_traceSigma {P : Measure Ω} {E₀ : Ω → Set ℂ}
    (hE₀ : Measurable[ℋ, hittingSigma] E₀) {h Y : Ω → DistOn upperHalfPlaneOpens} {δ : ℝ} (hδ : 0 < δ)
    {V : Set ℂ} {D₀ : Set Ω} (hD₀ : ∀ ω ∈ D₀, Disjoint (germNbhd δ (E₀ ω)) V)
    (hY : ∀ φ : TestOn upperHalfPlaneOpens, Disjoint (tsupport φ) V → ∀ᵐ ω ∂P, h ω φ = Y ω φ) :
    ℋ ⊔ germSigmaAt E₀ h δ ≤ traceSigma P Y ℋ D₀ := by
  have hℋ : ℋ ≤ traceSigma P Y ℋ D₀ := fun Q hQ =>
    ⟨Q, (le_sup_right : ℋ ≤ MeasurableSpace.comap Y inferInstance ⊔ ℋ) Q hQ, EventuallyEq.rfl⟩
  refine sup_le hℋ (sup_le (hE₀.comap_le.trans hℋ) (MeasurableSpace.generateFrom_le ?_))
  rintro _ ⟨φ, B, hB, rfl⟩
  have hK : MeasurableSet[ℋ] {ω | tsupport φ ⊆ germNbhd δ (E₀ ω)} :=
    hE₀ (measurableSet_subset_germNbhd φ.hasCompactSupport φ.tsupport_subset hδ)
  by_cases hφ : Disjoint (tsupport φ) V
  · refine ⟨{ω | tsupport φ ⊆ germNbhd δ (E₀ ω)} ∩ (fun ω => Y ω φ) ⁻¹' B, ?_, ?_⟩
    · exact ((le_sup_right : ℋ ≤ MeasurableSpace.comap Y inferInstance ⊔ ℋ) _ hK).inter
        ((le_sup_left : MeasurableSpace.comap Y inferInstance ≤ MeasurableSpace.comap Y inferInstance ⊔ ℋ) _
          ((LQGMetric.measurable_distOn_apply φ).comp (comap_measurable Y) hB))
    · filter_upwards [hY φ hφ] with ω hω
      show (ω ∈ D₀ ∩ ({ω | tsupport φ ⊆ germNbhd δ (E₀ ω)} ∩ (fun ω => h ω φ) ⁻¹' B)) =
        (ω ∈ D₀ ∩ ({ω | tsupport φ ⊆ germNbhd δ (E₀ ω)} ∩ (fun ω => Y ω φ) ⁻¹' B))
      simp only [mem_inter_iff, mem_preimage, hω]
  · refine ⟨∅, @MeasurableSet.empty _ (MeasurableSpace.comap Y inferInstance ⊔ ℋ), Eventually.of_forall fun ω => ?_⟩
    show (ω ∈ D₀ ∩ ({ω | tsupport φ ⊆ germNbhd δ (E₀ ω)} ∩ (fun ω => h ω φ) ⁻¹' B)) = (ω ∈ D₀ ∩ ∅)
    simp only [inter_empty, mem_empty_iff_false, eq_iff_iff, iff_false]
    rintro ⟨hω, hsub, -⟩
    exact hφ ((hD₀ ω hω).mono_left hsub)

end Trace

/-! ### The Dynkin step: marks `σ(Y) ∨ ℋ` -/

section Dynkin

variable {Ω β : Type*} {m ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace β] {Y : Ω → β}

/-- **Good events with marks `σ(Y) ∨ ℋ`**: if `D ∩ F` is good (its conditional probability given `m` is a function
of `Y`) for every `F ∈ ℋ`, and `Y` is `m`-measurable, then `D ∩ Q` is good for every `Q ∈ σ(Y) ∨ ℋ`. -/
theorem isCompEvent_inter_comap_sup (hm : m ≤ mΩ) (hYm : Measurable[m] Y) {D : Set Ω}
    (hgood : ∀ F, MeasurableSet[ℋ] F → IsCompEvent m P Y (D ∩ F)) {Q : Set Ω}
    (hQ : MeasurableSet[MeasurableSpace.comap Y inferInstance ⊔ ℋ] Q) : IsCompEvent m P Y (D ∩ Q) := by
  have hYm' : Measurable Y := hYm.mono hm le_rfl
  set p : Set (Set Ω) := {s | ∃ F, MeasurableSet[ℋ] F ∧ s = D ∩ F} with hp_def
  have hp : IsPiSystem p := by
    rintro _ ⟨F, hF, rfl⟩ _ ⟨F', hF', rfl⟩ -
    refine ⟨F ∩ F', hF.inter hF', ?_⟩
    ext ω
    simp only [mem_inter_iff]
    tauto
  have hpD : ∀ F, MeasurableSet[ℋ] F →
      MeasurableSet[MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.generateFrom p] (D ∩ F) :=
    fun F hF => (le_sup_right : MeasurableSpace.generateFrom p ≤ _) _
      (MeasurableSpace.measurableSet_generateFrom ⟨F, hF, rfl⟩)
  have hD' : MeasurableSet[MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.generateFrom p] D := by
    simpa using hpD univ (@MeasurableSet.univ _ ℋ)
  have hDQ : MeasurableSet[MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.generateFrom p] (D ∩ Q) := by
    refine measurableSet_inter_of_sup (𝒜 := ℋ) hD' (fun B hB => ?_) hpD hQ
    exact hD'.inter ((le_sup_left : MeasurableSpace.comap Y inferInstance ≤ _) _ ⟨B, hB, rfl⟩)
  have h := isCompEvent_inter_of_isPiSystem (m := m) (P := P) (Y := Y) hm hYm hYm' (X := Y) hYm'
    (S₀ := univ) MeasurableSet.univ (fun B hB => ⟨B, hB, by rw [univ_inter]⟩) hp
    (by rintro _ ⟨F, hF, rfl⟩; exact hgood F hF) hDQ
  simpa only [univ_inter] using h

end Dynkin

/-! ### The intersection over the exhaustion -/

section Limit

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The open sets `ℍ ∖ cl Uₙ`, decreasing to `ℍ ∖ U` from outside. -/
def outerOpen (U : Set ℂ) (n : ℕ) : Opens ℂ :=
  ⟨(upperHalfPlaneOpens : Set ℂ) \ closure (exhOpen U n : Set ℂ), upperHalfPlaneOpens.isOpen.sdiff isClosed_closure⟩

theorem antitone_outerOpen (U : Set ℂ) : Antitone (outerOpen U) := fun _ _ hmn =>
  sdiff_subset_sdiff_right (closure_mono (exhOpen_mono U hmn))

theorem outerOpen_le (U : Set ℂ) (n : ℕ) : outerOpen U n ≤ upperHalfPlaneOpens := fun _ hz => hz.1

/-- **The intersection step** (Proposition 3.2 twice): if `S` is good for the complementary projection along every
exhaustion set `Uₙ` of `U`, then `P[S | h]` is almost surely a Borel function of the complementary projection along
`U`. -/
theorem exists_comp_markovCompl_of_isCompEvent {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) (hG : Measurable G)
    {Gn : ℕ → DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hdn : ∀ n, GFF.IsMarkovDecomposition (exhOpen U n) upperHalfPlaneOpens h (fun ω => Gn n (h ω)) P)
    {S : Set Ω} (hS : ∀ n, IsCompEvent (MeasurableSpace.comap h inferInstance) P
      (fun ω => markovCompl (Gn n) (h ω)) S) :
    ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
      P⟦S | MeasurableSpace.comap h inferInstance⟧ =ᵐ[P] fun ω => g (markovCompl G (h ω)) := by
  set f := P⟦S | MeasurableSpace.comap h inferInstance⟧ with hf_def
  have hhm := hh.measurable
  have hmle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hfm : Measurable f := (stronglyMeasurable_condExp.mono hmle).measurable
  have hYm : Measurable fun ω => markovCompl G (h ω) := (measurable_markovCompl hG).comp hhm
  have hUle : U ≤ upperHalfPlaneOpens := hUH
  have hsep : ∀ C : Set ℂ, IsCompact C → C ⊆ (U : Set ℂ) → ∃ n, Disjoint C (outerOpen U n : Set ℂ) := by
    intro C hC hCU
    obtain ⟨n, hn⟩ := exists_subset_exhOpen U.isOpen hC hCU
    exact ⟨n, Set.disjoint_left.2 fun z hz hz' => hz'.2 (subset_closure (hn hz))⟩
  have hlev : ∀ B : Set ℝ, MeasurableSet B →
      MeasurableSet[MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance ⊔ Ito.nullSets P]
        (f ⁻¹' B) := by
    intro B hB
    have hn : ∀ n, MeasurableSet[QuantumZipper.LateralGerm.aeClosure
        (GFF.restrictSigma (outerOpen (U : Set ℂ) n) h) P] (f ⁻¹' B) := by
      intro n
      obtain ⟨-, g, hg, hge⟩ := hS (n + 1)
      have h1 : MeasurableSet[QuantumZipper.LateralGerm.aeClosure
          (GFF.complSigma h fun ω => Gn (n + 1) (h ω)) P] (f ⁻¹' B) := by
        refine ⟨(fun ω => markovCompl (Gn (n + 1)) (h ω)) ⁻¹' (g ⁻¹' B), ⟨g ⁻¹' B, hg hB, rfl⟩, ?_⟩
        filter_upwards [hge] with ω hω
        show (f ω ∈ B) = (g (markovCompl (Gn (n + 1)) (h ω)) ∈ B)
        rw [hf_def, hω]
      rw [GFF.aeClosure_complSigma_eq_iInf_aeClosure_restrictSigma_of_isCompact_closure
        (isCompact_closure_exhOpen _ _) ((closure_exhOpen_subset_self _ _).trans hUH) hh (hdn (n + 1))] at h1
      simp only [MeasurableSpace.measurableSet_iInf] at h1
      refine h1 (outerOpen U n) (outerOpen_le U n) fun z hz => ⟨hz.1, fun hzc => hz.2 ?_⟩
      exact closure_exhOpen_subset_succ _ n hzc
    obtain ⟨E', hE', hfE'⟩ := GFF.exists_ae_eq_mem_iInf_restrictSigma (antitone_outerOpen _) (outerOpen_le _) hn
    obtain ⟨E'', hE'', hE'E''⟩ := hd.exists_ae_eq_complSigma_of_mem_iInf_restrictSigma_of_disjoint
      (LQGMetric.zbAdmissible_of_subset_H subset_rfl) hUle hhm (antitone_outerOpen _) (outerOpen_le _) hsep hE'
    refine WholeField.measurableSet_of_ae_eq (sup_le hYm.comap_le (Ito.nullSets_le P)) (fun N hN hPN =>
      (le_sup_right : Ito.nullSets P ≤ _) _ (MeasurableSpace.measurableSet_generateFrom ⟨hN, hPN⟩)) (hfm hB)
      ((le_sup_left : MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance ≤ _) _ hE'')
      (hfE'.trans hE'E'')
  obtain ⟨g, hg, hge⟩ := Lemma72.isAEDeterminedBy_of_measurable_sup_nullSets (P := P) hYm
    (fun B hB => hlev B hB)
  exact ⟨g, hg, hge⟩

end Limit

/-! ### The main theorem -/

section Main

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The germ of a smaller `ℋ`-measurable set can be added to the marks of a larger marked local set** (Aux. lemma 124,
first paragraph; PROVE-LEMMA725REF5 §5 item 1): if `E` satisfies the history-marked avoidance criterion for `ℋ`, `E₀`
is `ℋ`-measurable and `E₀ ∩ ℍ ⊆ E`, then `E` satisfies the criterion for `ℋ ∨ 𝒜_{E₀}`. -/
theorem isHistoryAvoidanceLocal_sup_germSigma {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋ : ℋ ≤ mΩ) {E E₀ : Ω → Set ℂ}
    (hE : Measurable[mΩ, hittingSigma] E) (hloc : IsHistoryAvoidanceLocal ℋ E h P)
    (hE₀ : Measurable[ℋ, hittingSigma] E₀) (hsub : ∀ ω, E₀ ω ∩ H ⊆ E ω) :
    IsHistoryAvoidanceLocal (ℋ ⊔ germSigma E₀ h) E h P := by
  intro U G hUH hG hd F hF
  have hhm := hh.measurable
  have hmle : MeasurableSpace.comap h inferInstance ≤ mΩ := hhm.comap_le
  have hUnH : ∀ n, (exhOpen U n : Set ℂ) ⊆ H := fun n => (exhOpen_subset U n).trans hUH
  have hex : ∀ n, ∃ G' : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable G' ∧
      GFF.IsMarkovDecomposition (exhOpen U n) upperHalfPlaneOpens h (fun ω => G' (h ω)) P := fun n => by
    obtain ⟨G', hG', hd'⟩ := LocalSets.exists_markovMap (exhOpen U n) (hUnH n)
    exact ⟨G', hG', hd' hh⟩
  choose Gn hGn hdn using hex
  set D : Set Ω := {ω | Disjoint (E ω) (U : Set ℂ)} with hD_def
  set D₀ : Set Ω := {ω | Disjoint (E₀ ω) (U : Set ℂ)} with hD₀_def
  have hDD₀ : D ⊆ D₀ := fun ω hω => Set.disjoint_left.2 fun z hz hzU =>
    Set.disjoint_left.1 hω (hsub ω ⟨hz, hUH hzU⟩) hzU
  have hDm : MeasurableSet D := hE (measurableSet_avoid U.isOpen hUH)
  have hFm : MeasurableSet F :=
    sup_le hℋ (germSigma_le (hE₀.mono hℋ le_rfl) hhm) F hF
  have key : ∀ n, IsCompEvent (MeasurableSpace.comap h inferInstance) P (fun ω => markovCompl (Gn n) (h ω))
      (D ∩ F) := by
    intro n
    have hYm : Measurable[MeasurableSpace.comap h inferInstance] fun ω => markovCompl (Gn n) (h ω) :=
      (measurable_markovCompl (hGn n)).comp (comap_measurable h)
    obtain ⟨Ψ, hΨ, hΨe⟩ := exists_measurable_markovCompl_comp (exhOpen_subset U n) hUH hhm (hdn n) hd
    have hgood : ∀ F₁, MeasurableSet[ℋ] F₁ → IsCompEvent (MeasurableSpace.comap h inferInstance) P
        (fun ω => markovCompl (Gn n) (h ω)) (D ∩ F₁) := by
      intro F₁ hF₁
      obtain ⟨g, hg, hge⟩ := hloc U G hUH hG hd F₁ hF₁
      refine ⟨hDm.inter (hℋ _ hF₁), fun y => g (Ψ y), hg.comp hΨ, ?_⟩
      filter_upwards [hge, hΨe] with ω h1 h2
      rw [h1, h2]
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hF' : MeasurableSet[ℋ ⊔ germSigmaAt E₀ h (1 / ((n : ℝ) + 1))] F :=
      sup_le_sup_left (iInf_le (fun k : ℕ => germSigmaAt E₀ h (1 / ((k : ℝ) + 1))) n) ℋ F hF
    obtain ⟨Q, hQ, hQe⟩ := le_traceSigma (P := P) (Y := fun ω => markovCompl (Gn n) (h ω)) hE₀ hδ
      (V := (exhOpen U n : Set ℂ)) (D₀ := D₀)
      (fun ω hω => disjoint_germNbhd_exhOpen hUH n hω) (fun φ hφ => ae_apply_eq_markovCompl (hdn n) hφ) F hF'
    have hDQ := isCompEvent_inter_comap_sup (P := P) hmle hYm hgood hQ
    refine hDQ.congr_ae (hDm.inter hFm) ?_
    have e1 : D ∩ F = D ∩ (D₀ ∩ F) := by
      rw [← inter_assoc, inter_eq_left.2 hDD₀]
    have e2 : D ∩ Q = D ∩ (D₀ ∩ Q) := by
      rw [← inter_assoc, inter_eq_left.2 hDD₀]
    rw [e1, e2]
    exact (EventuallyEqSet.inter EventuallyEq.rfl hQe).symm
  exact exists_comp_markovCompl_of_isCompEvent hh hUH hd hG hdn key

end Main

end InteractingSLE.Sec7.Lemma725RefMarks
