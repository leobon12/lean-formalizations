/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.Prop32
import InteractingSLE.GFF.LocalSets.MarkovNesting
import InteractingSLE.Spec.Supplement.WalkMarkedLocalGlue
import InteractingSLE.Spec.Supplement.KernelTower2

/-!
# Conditional probabilities that factor through a Markov complement

Packet PROVE-GW4-CLOC (generic GFF tools). For a random distribution `X` on `ℍ`, a Borel version `G` of the
projection onto `H(U)` and an event `S`, `Fac Q X G S` says that the conditional probability of `S` given `X` is a
measurable function of `X − G X` (the history-marked avoidance criterion is this property for the events
`{A ∩ U = ∅} ∩ F`). This file proves:

* `fac_iff_charFac`: under a Markov decomposition, `Fac` is the characteristic-function factorization of
  `WalkLaw.setIntegral_exp_markov_of_condExp_self` / `WalkLaw.exists_condExp_eq_comp_of_setIntegral_exp`;
* `Fac.iUnion`, `Fac.iInter`: `Fac` passes to monotone limits of events (dominated convergence);
* `Fac.mono_open`: `Fac` for a larger open set gives `Fac` for a smaller one (Markov nesting,
  `LocalSets.exists_measurable_markovCompl_comp`);
* **`fac_of_exhaust`** (the canonical criterion): if `S` factors through the complements along every member of an
  exhaustion of `U` by open sets with compact closures in `ℍ`, it factors through the complement along `U`, for every
  Markov map of `U`. This is Proposition 3.2 (`GFF.aeClosure_complSigma_le_aeClosure_restrictSigma_of_isCompact`,
  `GFF.IsMarkovDecomposition.exists_ae_eq_complSigma_of_mem_iInf_restrictSigma_of_disjoint`), used as the Gaussian
  tail identity `⋂ₘ σ(X − P_{Wₘ} X) = σ(X − P_U X)` up to null sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix.CLoc

open LocalSets

section Fac

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- The conditional probability of `S` given `X` is a measurable function of the complementary Markov projection
`X − G X`. -/
def Fac (Q : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (S : Set Ω) : Prop :=
  ∃ g : DistOn upperHalfPlaneOpens → ℝ, Measurable g ∧
    Q⟦S | MeasurableSpace.comap X inferInstance⟧ =ᵐ[Q] fun ω => g (markovCompl G (X ω))

/-- The characteristic-function form of `Fac`. -/
def CharFac (Q : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) (S : Set Ω) : Prop :=
  ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
    ∫ ω in S, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (X ω) Ψ : ℂ)) ∂Q =
      (∫ ω, Complex.exp (Complex.I * (G (X ω) Φ : ℂ)) ∂Q) *
        ∫ ω in S, Complex.exp (Complex.I * (markovCompl G (X ω) Ψ : ℂ)) ∂Q

theorem fac_iff_charFac (hX : Measurable X) {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) Q)
    {S : Set Ω} (hS : MeasurableSet S) : Fac Q X G S ↔ CharFac Q X G S := by
  constructor
  · rintro ⟨g, hg, hge⟩
    exact WalkLaw.setIntegral_exp_markov_of_condExp_self hX hG hd hS hg hge
  · intro h
    exact WalkLaw.exists_condExp_eq_comp_of_setIntegral_exp hX hG hd hS h

theorem integrable_cexp_apply {Y : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    (Φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Complex.exp (Complex.I * (Y ω Φ : ℂ))) Q :=
  GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply Φ).comp hY)

theorem integrable_cexp_mul_cexp {Y Z : Ω → DistOn upperHalfPlaneOpens} (hY : Measurable Y)
    (hZ : Measurable Z) (Φ Ψ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => Complex.exp (Complex.I * (Y ω Φ : ℂ)) *
      Complex.exp (Complex.I * (Z ω Ψ : ℂ))) Q := by
  refine (integrable_cexp_apply (Q := Q) hZ Ψ).bdd_mul
    (GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply Φ).comp hY)).aestronglyMeasurable
    (c := 1) (Eventually.of_forall fun ω => ?_)
  exact (Complex.norm_exp_I_mul_ofReal _).le

/-- `Fac` passes to increasing unions. -/
theorem Fac.iUnion (hX : Measurable X) {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) Q)
    {S : ℕ → Set Ω} (hS : ∀ n, MeasurableSet (S n)) (hmono : Monotone S)
    (hf : ∀ n, Fac Q X G (S n)) : Fac Q X G (⋃ n, S n) := by
  have hXm : Measurable fun ω => G (X ω) := hG.comp hX
  have hYm : Measurable fun ω => markovCompl G (X ω) := (measurable_markovCompl hG).comp hX
  refine (fac_iff_charFac hX hG hd (MeasurableSet.iUnion hS)).2 fun Φ Ψ => ?_
  have hc : ∀ n, CharFac Q X G (S n) := fun n => (fac_iff_charFac hX hG hd (hS n)).1 (hf n)
  have h1 := tendsto_setIntegral_of_monotone (μ := Q) hS hmono
    (integrable_cexp_mul_cexp (Q := Q) hXm hYm Φ Ψ).integrableOn
  have h2 := tendsto_setIntegral_of_monotone (μ := Q) hS hmono
    (integrable_cexp_apply (Q := Q) hYm Ψ).integrableOn
  refine tendsto_nhds_unique h1 ?_
  simp_rw [fun n => hc n Φ Ψ]
  exact h2.const_mul _

/-- `Fac` passes to decreasing intersections. -/
theorem Fac.iInter (hX : Measurable X) {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) Q)
    {S : ℕ → Set Ω} (hS : ∀ n, MeasurableSet (S n)) (hanti : Antitone S)
    (hf : ∀ n, Fac Q X G (S n)) : Fac Q X G (⋂ n, S n) := by
  have hXm : Measurable fun ω => G (X ω) := hG.comp hX
  have hYm : Measurable fun ω => markovCompl G (X ω) := (measurable_markovCompl hG).comp hX
  refine (fac_iff_charFac hX hG hd (MeasurableSet.iInter hS)).2 fun Φ Ψ => ?_
  have hc : ∀ n, CharFac Q X G (S n) := fun n => (fac_iff_charFac hX hG hd (hS n)).1 (hf n)
  have h1 := tendsto_setIntegral_of_antitone (μ := Q) hS hanti
    ⟨0, (integrable_cexp_mul_cexp (Q := Q) hXm hYm Φ Ψ).integrableOn⟩
  have h2 := tendsto_setIntegral_of_antitone (μ := Q) hS hanti
    ⟨0, (integrable_cexp_apply (Q := Q) hYm Ψ).integrableOn⟩
  refine tendsto_nhds_unique h1 ?_
  simp_rw [fun n => hc n Φ Ψ]
  exact h2.const_mul _

omit [IsProbabilityMeasure Q] in
/-- **Markov nesting**: factoring through the complement along a larger open set implies factoring through the
complement along a smaller one. -/
theorem Fac.mono_open (hX : Measurable X) {W V : Opens ℂ} (hWV : W ≤ V)
    (hV : V ≤ upperHalfPlaneOpens)
    {GW GV : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hdW : GFF.IsMarkovDecomposition W upperHalfPlaneOpens X (fun ω => GW (X ω)) Q)
    (hdV : GFF.IsMarkovDecomposition V upperHalfPlaneOpens X (fun ω => GV (X ω)) Q)
    {S : Set Ω} (h : Fac Q X GV S) : Fac Q X GW S := by
  obtain ⟨g, hg, hge⟩ := h
  obtain ⟨Ψ, hΨ, hΨe⟩ := exists_measurable_markovCompl_comp hWV hV hX hdW hdV
  refine ⟨g ∘ Ψ, hg.comp hΨ, ?_⟩
  filter_upwards [hge, hΨe] with ω h1 h2
  rw [h1, h2]
  rfl

end Fac

section LevelSets

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- The rational level sets of a function generate its σ-algebra; if they are almost surely events of `m`, the
function is almost surely equal to its conditional expectation given `m`. -/
theorem condExp_ae_eq_self_of_levelSets (hm : m ≤ mΩ) {f : Ω → ℝ}
    (hfm : Measurable f) (hfi : Integrable f Q)
    (hlev : ∀ q : ℚ, MeasurableSet[aeSigma m Q] (f ⁻¹' Ioi (q : ℝ))) : Q[f | m] =ᵐ[Q] f := by
  have hm₂ : MeasurableSpace.comap f inferInstance ≤ aeSigma m Q := by
    rw [BorelSpace.measurable_eq (α := ℝ), Real.borel_eq_generateFrom_Ioi_rat,
      MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨q, hsq⟩ := mem_iUnion.1 hs
    rw [mem_singleton_iff.1 hsq]
    exact hlev q
  have hm₁ : m ≤ aeSigma m Q := fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
  have hle : m ⊔ MeasurableSpace.comap f inferInstance ≤ mΩ := sup_le hm hfm.comap_le
  have h1 := KernelTower.condExp_ae_eq_of_le_aeSigma_sup (P := Q) le_sup_left hle (sup_le hm₁ hm₂) hfi
  refine h1.trans (EventuallyEq.of_eq ?_)
  refine condExp_of_stronglyMeasurable hle ?_ hfi
  have hfm' : Measurable[m ⊔ MeasurableSpace.comap f inferInstance] f :=
    Measurable.of_comap_le le_sup_right
  exact hfm'.stronglyMeasurable

end LevelSets

/-! ### The canonical criterion (Proposition 3.2) -/

section Canonical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {X : Ω → DistOn upperHalfPlaneOpens}

theorem coe_upperHalfPlaneOpens : ((upperHalfPlaneOpens : Opens ℂ) : Set ℂ) = H := rfl

/-- The open neighbourhoods of `ℍ ∖ W n` used in the canonical criterion. -/
def nbhdOpens (W : ℕ → Opens ℂ) (n : ℕ) : Opens ℂ :=
  GFF.germOpens upperHalfPlaneOpens (H \ (W n : Set ℂ)) n

theorem nbhdOpens_le (W : ℕ → Opens ℂ) (n : ℕ) : nbhdOpens W n ≤ upperHalfPlaneOpens :=
  GFF.germOpens_le _ _ _

theorem antitone_nbhdOpens {W : ℕ → Opens ℂ} (hW : Monotone W) : Antitone (nbhdOpens W) := by
  intro m n hmn
  refine inf_le_inf_left _ ?_
  intro z hz
  obtain ⟨k, hk, hzk⟩ := mem_thickening_iff.1 hz
  refine mem_thickening_iff.2 ⟨k, ⟨hk.1, fun hkW => hk.2 (hW hmn hkW)⟩, hzk.trans_le ?_⟩
  gcongr

theorem exists_disjoint_nbhdOpens {W : ℕ → Opens ℂ} (hW : Monotone W)
    (hWH : ∀ n, (W n : Set ℂ) ⊆ H) {C : Set ℂ} (hC : IsCompact C) {n₀ : ℕ} (hCW : C ⊆ W n₀) :
    ∃ n, Disjoint C (nbhdOpens W n) := by
  have hK : IsOpen ((upperHalfPlaneOpens : Set ℂ) \ (H \ (W n₀ : Set ℂ))) := by
    rw [coe_upperHalfPlaneOpens, Set.sdiff_sdiff_right_self, inter_eq_right.2 (hWH n₀)]
    exact (W n₀).isOpen
  have hCV : C ⊆ (upperHalfPlaneOpens : Set ℂ) \ (H \ (W n₀ : Set ℂ)) := by
    rw [coe_upperHalfPlaneOpens, Set.sdiff_sdiff_right_self, inter_eq_right.2 (hWH n₀)]
    exact hCW
  obtain ⟨n₁, hn₁⟩ := GFF.exists_disjoint_germOpens hK hC hCV
  refine ⟨max n₀ n₁, hn₁.mono_right ?_⟩
  refine inf_le_inf_left _ ?_
  intro z hz
  obtain ⟨k, hk, hzk⟩ := mem_thickening_iff.1 hz
  refine mem_thickening_iff.2 ⟨k, ⟨hk.1, fun hkW => hk.2 (hW (le_max_left _ _) hkW)⟩, hzk.trans_le ?_⟩
  have : (n₁ : ℝ) ≤ (max n₀ n₁ : ℕ) := by exact_mod_cast le_max_right _ _
  gcongr

/-- **The canonical criterion.** Let `X` be a zero-boundary GFF on `ℍ`, `U ⊆ ℍ` open with a Markov map `G`, and
`W n` open sets with compact closures in `ℍ`, increasing, such that every compact subset of `U` lies in some `W n`.
If `S` factors through the complement along every `W n`, it factors through `X − G X`. -/
theorem fac_of_exhaust (hX : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X Q) {U : Opens ℂ}
    (hUH : U ≤ upperHalfPlaneOpens) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hG : Measurable G) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens X (fun ω => G (X ω)) Q)
    {W : ℕ → Opens ℂ} (hWmono : Monotone W) (hWc : ∀ n, IsCompact (closure (W n : Set ℂ)))
    (hWH : ∀ n, closure (W n : Set ℂ) ⊆ H)
    (hWex : ∀ C : Set ℂ, IsCompact C → C ⊆ (U : Set ℂ) → ∃ n, C ⊆ (W n : Set ℂ))
    {GW : ℕ → DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hdW : ∀ n, GFF.IsMarkovDecomposition (W n) upperHalfPlaneOpens X (fun ω => GW n (X ω)) Q)
    {S : Set Ω} (hf : ∀ n, Fac Q X (GW n) S) : Fac Q X G S := by
  have hXm := hX.measurable
  have hWH' : ∀ n, (W n : Set ℂ) ⊆ H := fun n => subset_closure.trans (hWH n)
  set f : Ω → ℝ := Q⟦S | MeasurableSpace.comap X inferInstance⟧ with hf_def
  have hm₁ : MeasurableSpace.comap (fun ω => markovCompl G (X ω)) inferInstance ≤ mΩ :=
    ((measurable_markovCompl hG).comp hXm).comap_le
  have hfm : Measurable f :=
    (stronglyMeasurable_condExp.mono hXm.comap_le).measurable
  have hfi : Integrable f Q := integrable_condExp
  -- every rational level set of `f` is almost surely an event of `σ(X − G X)`
  have hlev : ∀ q : ℚ, MeasurableSet[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (X ω))
      inferInstance) Q] (f ⁻¹' Ioi (q : ℝ)) := by
    intro q
    -- an event of the germ outside each `W n`
    have hn : ∀ n, MeasurableSet[QuantumZipper.LateralGerm.aeClosure
        (GFF.restrictSigma (nbhdOpens W n) X) Q] (f ⁻¹' Ioi (q : ℝ)) := by
      intro n
      obtain ⟨g, hg, hge⟩ := hf n
      have hK : IsOpen ((upperHalfPlaneOpens : Set ℂ) \ (H \ (W n : Set ℂ))) := by
        rw [coe_upperHalfPlaneOpens, Set.sdiff_sdiff_right_self, inter_eq_right.2 (hWH' n)]
        exact (W n).isOpen
      have hKe : ((upperHalfPlaneOpens : Set ℂ) \ (H \ (W n : Set ℂ))) = (W n : Set ℂ) := by
        rw [coe_upperHalfPlaneOpens, Set.sdiff_sdiff_right_self, inter_eq_right.2 (hWH' n)]
      have hOe : (⟨(upperHalfPlaneOpens : Set ℂ) \ (H \ (W n : Set ℂ)), hK⟩ : Opens ℂ) = W n :=
        Opens.ext hKe
      have hdn : GFF.IsMarkovDecomposition ⟨(upperHalfPlaneOpens : Set ℂ) \ (H \ (W n : Set ℂ)), hK⟩
          upperHalfPlaneOpens X (fun ω => GW n (X ω)) Q := by
        rw [hOe]; exact hdW n
      have hcl : IsCompact (closure ((upperHalfPlaneOpens : Set ℂ) \ (H \ (W n : Set ℂ)))) := by
        rw [hKe]; exact hWc n
      have hclH : closure ((upperHalfPlaneOpens : Set ℂ) \ (H \ (W n : Set ℂ))) ⊆ upperHalfPlaneOpens := by
        rw [hKe]; exact hWH n
      have hincl := GFF.aeClosure_complSigma_le_aeClosure_restrictSigma_of_isCompact hK hcl hclH hX hdn
        (nbhdOpens_le W n) (GFF.subset_germOpens (fun z hz => hz.1) n)
      refine hincl _ ⟨{ω | (q : ℝ) < g (markovCompl (GW n) (X ω))}, ?_, ?_⟩
      · exact ⟨g ⁻¹' Ioi (q : ℝ), hg measurableSet_Ioi, rfl⟩
      · filter_upwards [hge] with ω hω
        simp only [eq_iff_iff, mem_preimage, mem_Ioi]
        rw [← hω]
    obtain ⟨E', hE', hEE'⟩ := GFF.exists_ae_eq_mem_iInf_restrictSigma (P := Q) (h := X)
      (antitone_nbhdOpens hWmono) (nbhdOpens_le W) hn
    obtain ⟨E'', hE'', hE'E''⟩ :=
      hd.exists_ae_eq_complSigma_of_mem_iInf_restrictSigma_of_disjoint
        (LQGMetric.zbAdmissible_of_subset_H subset_rfl) hUH hXm (antitone_nbhdOpens hWmono)
        (nbhdOpens_le W)
        (fun C hC hCU => by
          obtain ⟨n₀, hn₀⟩ := hWex C hC hCU
          exact exists_disjoint_nbhdOpens hWmono hWH' hC hn₀) hE'
    exact ⟨E'', hE'', hEE'.trans hE'E''⟩
  have hce := condExp_ae_eq_self_of_levelSets hm₁ hfm hfi hlev
  obtain ⟨g, hg, hge⟩ := (stronglyMeasurable_condExp (m := MeasurableSpace.comap
    (fun ω => markovCompl G (X ω)) inferInstance) (μ := Q) (f := f)).exists_eq_measurable_comp
  refine ⟨g, hg.measurable, ?_⟩
  filter_upwards [hce] with ω hω
  change f ω = _
  rw [← hω, hge]
  rfl

end Canonical

end InteractingSLE.Theorem14.GW4Fix.CLoc
