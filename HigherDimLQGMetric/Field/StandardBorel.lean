import HigherDimLQGMetric.Field.StandardBorelDist
import LQGMetric.Field.StandardBorelExt
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Finsupp.Encodable

/-!
# `𝒟'(U)` with the cylinder σ-algebra is a standard Borel space

Packet F1 (measurability for the frozen cylinder σ-algebras; ruling M10). Port of LQGMetric's
`lqg_metric/LQGMetric/Field/StandardBorelDistOn.lean` and `Field/StandardBorelRange.lean` from `ℂ`
to `Rd d`; the generic tools `exists_clm_extend` (density extension of a seminorm-dominated additive
functional) and `standardBorelSpace_of_measurableEquiv` are imported from LQGMetric's
`Field/StandardBorelExt.lean` (generic layer, imported as is).

Coordinates: `J = (ℕ × ℕ) →₀ ℤ` indexes the integer combinations `comb c = Σ c_j φ_j` of the
countable family `φ_j = distGen U j` (dense sequences in `𝓓_{K_n}`, `K_n` an exhaustion of `U`),
and `pairJ h = (⟨h, comb c⟩)_{c ∈ J} ∈ ℝ^J`. The range of `pairJ` is the Borel set `rangeSet U`
(`range_pairJ_eq`): `a ∈ ℝ^J` is in the range iff `a` is additive, depends only on `comb c`, and
for every `n` there are `C, N ∈ ℕ` with `|a c| ≤ C ‖comb c‖_{C^N}` whenever `comb c` is supported in
`K_n`. The converse direction extends `a` by density to each `𝓓_{K_n}` and glues
(`TestFunction.mkCLM`); the forward direction uses that a continuous linear functional on `𝓓_K`
is bounded by finitely many seminorms. Since the σ-algebra is `comap pairJ`
(`distOn_measurableSpace_eq_comap_pairJ`) and `pairJ` is injective, `pairJ` is a measurable
embedding onto a Borel subset of the Polish space `ℝ^J` (`measurableEmbedding_pairJ`), so
`DistOn U` is standard Borel (`standardBorelSpace_distOn`).

Published background: `𝒟'` is a Lusin space (L. Schwartz, *Radon measures on arbitrary
topological spaces and cylindrical measures*, Part II); the coordinate argument is an own
elementary proof (as in the 2D layer).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

section
variable (U : Opens (Rd d))

lemma exhaustK_mono {n m : ℕ} (h : n ≤ m) : (exhaustK U n : Set (Rd d)) ⊆ exhaustK U m :=
  image_mono ((CompactExhaustion.choice U).subset h)

/-- `φ ∈ 𝓓(U)` supported in `K`, as an element of `𝓓_K` -/
def mkT {K : Compacts (Rd d)} (φ : TestOn U) (h : tsupport (φ : Rd d → ℝ) ⊆ K) :
    𝓓^{⊤}_{K}(Rd d, ℝ) where
  toFun := φ
  contDiff' := φ.contDiff
  zero_on_compl' := fun _ hx => image_eq_zero_of_notMem_tsupport fun h' => hx (h h')

/-- the inclusion `𝓓_{K_n} → 𝓓(U)` -/
def iotaK (n : ℕ) : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) →L[ℝ] TestOn U :=
  TestFunction.ofSupportedInCLM ℝ (exhaustK_subset U n)

/-- coordinates `J = (ℕ × ℕ) →₀ ℤ` -/
abbrev CoordJ : Type := (ℕ × ℕ) →₀ ℤ

/-- `c ↦ Σ_j c_j φ_j` -/
def comb : CoordJ →+ TestOn U :=
  Finsupp.liftAddHom fun j => zmultiplesHom (TestOn U) (distGen U j)

lemma comb_single (j : ℕ × ℕ) : comb U (Finsupp.single j 1) = distGen U j := by
  simp [comb]

/-- `h ↦ (⟨h, comb c⟩)_c` -/
def pairJ (h : DistOn U) : CoordJ → ℝ := fun c => h (comb U c)

/-- the Borel set which is the range of `pairJ` -/
def rangeSet : Set (CoordJ → ℝ) :=
  {a | ∀ c c', a (c + c') = a c + a c'} ∩ {a | ∀ c c', comb U c = comb U c' → a c = a c'} ∩
    ⋂ n : ℕ, ⋃ C : ℕ, ⋃ N : ℕ, {a | ∀ c (hc : tsupport (comb U c : Rd d → ℝ) ⊆ exhaustK U n),
      |a c| ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ (exhaustK U n) N (mkT U _ hc)}

theorem measurableSet_rangeSet : MeasurableSet (rangeSet U) := by
  refine ((IsClosed.measurableSet ?_).inter (IsClosed.measurableSet ?_)).inter
    (MeasurableSet.iInter fun n => MeasurableSet.iUnion fun C => MeasurableSet.iUnion fun N =>
      IsClosed.measurableSet ?_)
  · simp only [ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun c' =>
      isClosed_eq (continuous_apply _) ((continuous_apply c).add (continuous_apply c'))
  · simp only [ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply _) (continuous_apply _)
  · simp only [ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply _).abs continuous_const

lemma supSeminorm_mono (K : Compacts (Rd d)) {i j : ℕ} (h : i ≤ j) :
    ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ K i ≤
      ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ K j :=
  Finset.sup_mono (Finset.Iic_subset_Iic.2 h)

/-- forward direction: every distribution satisfies the conditions -/
theorem range_pairJ_subset : range (pairJ U) ⊆ rangeSet U := by
  rintro _ ⟨h, rfl⟩
  refine ⟨⟨fun c c' => by simp [pairJ, map_add], fun c c' e => by simp [pairJ, e]⟩, ?_⟩
  refine mem_iInter.2 fun n => ?_
  let L : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) →L[ℝ] ℝ :=
    (h : TestOn U →L[ℝ] ℝ).comp (iotaK U n)
  let q : Seminorm ℝ 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) := (normSeminorm ℝ ℝ).comp L.toLinearMap
  have hq : Continuous q := continuous_norm.comp L.continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms' ℝ (Rd d) ℝ ⊤ (exhaustK U n)) q hq
  refine mem_iUnion.2 ⟨⌈(C : ℝ)⌉₊, mem_iUnion.2 ⟨s.sup id, fun c hc => ?_⟩⟩
  set x := mkT U (comb U c) hc
  have h1 : |pairJ U h c| = q x := by
    have : iotaK U n x = comb U c := by ext; rfl
    simp only [q, L, pairJ, Seminorm.comp_apply, coe_normSeminorm, Real.norm_eq_abs]
    show |h (comb U c)| = |h (iotaK U n x)|
    rw [this]
  have h2 : q x ≤ C * (s.sup (ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ (exhaustK U n))) x :=
    hC x
  have h3 : (s.sup (ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ (exhaustK U n))) x ≤
      ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ (exhaustK U n) (s.sup id) x :=
    (Finset.sup_le fun i hi => supSeminorm_mono _ (Finset.le_sup (f := id) hi)) x
  have h4 : 0 ≤ ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ (exhaustK U n) (s.sup id) x :=
    apply_nonneg _ _
  rw [h1]
  calc q x ≤ C * _ := h2.trans (mul_le_mul_of_nonneg_left h3 C.2)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) h4

end

section
variable (U : Opens (Rd d))

/-- the additive subgroup of `𝓓_{K_n}` of the elements `comb c` -/
def combSub (n : ℕ) : AddSubgroup 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) where
  carrier := {ψ | ∃ c, comb U c = iotaK U n ψ}
  add_mem' := by
    rintro _ _ ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [map_add, map_add, hc, hc']⟩
  zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
  neg_mem' := by
    rintro _ ⟨c, hc⟩
    exact ⟨-c, by rw [map_neg, map_neg, hc]⟩

lemma dense_combSub (n : ℕ) : Dense (combSub U n : Set 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ)) := by
  refine (denseRange_denseSeqK U n).mono ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨Finsupp.single (n, k) 1, by rw [comb_single]; rfl⟩

/-- converse direction: every admissible coordinate vector is the image of a distribution -/
theorem rangeSet_subset_range : rangeSet U ⊆ range (pairJ U) := by
  rintro a ⟨⟨hadd, hcons⟩, hB⟩
  have hT : ∀ n, ∃ T : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) →L[ℝ] ℝ,
      ∀ ψ c, comb U c = iotaK U n ψ → T ψ = a c := by
    intro n
    obtain ⟨C, N, hCN⟩ : ∃ C N : ℕ, ∀ c (hc : tsupport (comb U c : Rd d → ℝ) ⊆ exhaustK U n),
        |a c| ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ (exhaustK U n) N
          (mkT U _ hc) := by
      have := mem_iInter.1 hB n
      simp only [mem_iUnion] at this
      exact this
    have hbound : ∀ ψ c, comb U c = iotaK U n ψ →
        |a c| ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ (Rd d) ℝ ⊤ (exhaustK U n) N ψ := by
      intro ψ c e
      have hc : tsupport (comb U c : Rd d → ℝ) ⊆ exhaustK U n := by
        rw [e]; exact ψ.tsupport_subset
      have hx : mkT U _ hc = ψ := by ext x; exact DFunLike.congr_fun e x
      have := hCN c hc
      rwa [hx] at this
    let g : combSub U n →+ ℝ := AddMonoidHom.mk' (fun s => a (Classical.choose s.2)) (by
      intro s t
      have e : comb U (Classical.choose (s + t).2) =
          comb U (Classical.choose s.2 + Classical.choose t.2) := by
        rw [Classical.choose_spec (s + t).2, map_add, Classical.choose_spec s.2,
          Classical.choose_spec t.2, AddSubgroup.coe_add, map_add]
      rw [hcons _ _ e, hadd])
    have hg : ∀ s : combSub U n, ∀ c, comb U c = iotaK U n s → g s = a c := fun s c e =>
      hcons _ _ ((Classical.choose_spec s.2).trans e.symm)
    obtain ⟨T, hT⟩ := LQGMetric.exists_clm_extend _
      ((ContDiffMapSupportedIn.withSeminorms' ℝ (Rd d) ℝ ⊤ (exhaustK U n)).continuous_seminorm N)
      (combSub U n) (dense_combSub U n) g (C : ℝ)
      (fun s => hbound s _ (Classical.choose_spec s.2))
    refine ⟨T, fun ψ c e => ?_⟩
    have hs : ψ ∈ combSub U n := ⟨c, e⟩
    exact (hT ⟨ψ, hs⟩).trans (hg _ c e)
  choose T hT using hT
  have hcompat : ∀ n m (hnm : n ≤ m) (ψ : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ)),
      T m (inclK (exhaustK_mono U hnm) ψ) = T n ψ := by
    intro n m hnm ψ
    have := Continuous.ext_on (dense_combSub U n)
      ((T m).continuous.comp (continuous_inclK (exhaustK_mono U hnm))) (T n).continuous
      (fun s hs => by
        obtain ⟨c, e⟩ := hs
        simp only [Function.comp_apply]
        rw [hT n s c e, hT m _ c (e.trans (by ext; rfl))])
    exact congrFun this ψ
  let V : ∀ (φ : TestOn U) (n : ℕ), tsupport (φ : Rd d → ℝ) ⊆ exhaustK U n → ℝ :=
    fun φ n h => T n (mkT U φ h)
  have hVle : ∀ φ n m (hnm : n ≤ m) h h', V φ m h' = V φ n h := by
    intro φ n m hnm h h'
    have : mkT U φ h' = inclK (exhaustK_mono U hnm) (mkT U φ h) := by ext; rfl
    simp only [V]
    rw [this, hcompat n m hnm]
  have hV : ∀ φ n m h h', V φ n h = V φ m h' := by
    intro φ n m h h'
    have h'' : tsupport (φ : Rd d → ℝ) ⊆ exhaustK U (max n m) :=
      h.trans (exhaustK_mono U (le_max_left _ _))
    rw [← hVle φ n (max n m) (le_max_left _ _) h h'', hVle φ m (max n m) (le_max_right _ _) h' h'']
  have hex : ∀ φ : TestOn U, ∃ n, tsupport (φ : Rd d → ℝ) ⊆ exhaustK U n := fun φ =>
    exists_exhaustK_superset U φ.hasCompactSupport.isCompact φ.tsupport_subset
  let F : TestOn U → ℝ := fun φ => V φ (Classical.choose (hex φ)) (Classical.choose_spec (hex φ))
  have hF : ∀ φ n h, F φ = V φ n h := fun φ n h => hV _ _ _ _ _
  have hFadd : ∀ φ φ', F (φ + φ') = F φ + F φ' := by
    intro φ φ'
    obtain ⟨n, hn⟩ := hex φ
    obtain ⟨n', hn'⟩ := hex φ'
    have h1 : tsupport (φ : Rd d → ℝ) ⊆ exhaustK U (max n n') :=
      hn.trans (exhaustK_mono U (le_max_left _ _))
    have h2 : tsupport (φ' : Rd d → ℝ) ⊆ exhaustK U (max n n') :=
      hn'.trans (exhaustK_mono U (le_max_right _ _))
    have hc : ((φ + φ' : TestOn U) : Rd d → ℝ) = ⇑φ + ⇑φ' := rfl
    have h3 : tsupport ((φ + φ' : TestOn U) : Rd d → ℝ) ⊆ exhaustK U (max n n') := by
      rw [hc]
      exact ((closure_mono (Function.support_add _ _)).trans closure_union.subset).trans
        (union_subset h1 h2)
    rw [hF _ _ h3, hF _ _ h1, hF _ _ h2]
    simp only [V]
    rw [← map_add]
    congr 1
  have hFsmul : ∀ (r : ℝ) φ, F (r • φ) = r • F φ := by
    intro r φ
    obtain ⟨n, hn⟩ := hex φ
    have hc : ((r • φ : TestOn U) : Rd d → ℝ) = fun x => (fun _ => r) x • φ x := rfl
    have h3 : tsupport ((r • φ : TestOn U) : Rd d → ℝ) ⊆ exhaustK U n := by
      rw [hc]; exact (tsupport_smul_subset_right (fun _ => r) φ).trans hn
    rw [hF _ _ h3, hF _ _ hn]
    simp only [V]
    rw [← map_smul]
    congr 1
  have hFcont : ∀ (K : Compacts (Rd d)) (hK : (K : Set (Rd d)) ⊆ U),
      Continuous (F ∘ TestFunction.ofSupportedIn hK) := by
    intro K hK
    obtain ⟨n, hn⟩ := exists_exhaustK_superset U K.isCompact hK
    have : F ∘ TestFunction.ofSupportedIn hK = T n ∘ inclK hn := by
      funext ψ
      have hs : tsupport ((TestFunction.ofSupportedIn hK ψ : TestOn U) : Rd d → ℝ) ⊆
          exhaustK U n := ψ.tsupport_subset.trans hn
      simp only [Function.comp_apply]
      rw [hF _ n hs]
      simp only [V]
      congr 1
    rw [this]
    exact (T n).continuous.comp (continuous_inclK hn)
  let L : TestOn U →L[ℝ] ℝ := TestFunction.mkCLM ℝ F hFadd hFsmul hFcont
  refine ⟨L, funext fun c => ?_⟩
  show F (comb U c) = a c
  obtain ⟨n, hn⟩ := hex (comb U c)
  rw [hF _ n hn]
  exact hT n _ c (by ext; rfl)

theorem range_pairJ_eq : range (pairJ U) = rangeSet U :=
  (range_pairJ_subset U).antisymm (rangeSet_subset_range U)

/-- the range of the coordinate map is Borel -/
theorem measurableSet_range_pairJ : MeasurableSet (range (pairJ U)) := by
  rw [range_pairJ_eq]; exact measurableSet_rangeSet U

theorem measurable_pairJ : Measurable (pairJ U) :=
  measurable_pi_iff.2 fun _ => measurable_distOn_apply _

theorem injective_pairJ : Function.Injective (pairJ U) := by
  intro h₁ h₂ e
  apply injective_distOn_pairings U
  funext j
  have := congrFun e (Finsupp.single j 1)
  simpa [pairJ, comb_single] using this

theorem distOn_measurableSpace_eq_comap_pairJ :
    DistOn.measurableSpace U = MeasurableSpace.comap (pairJ U) MeasurableSpace.pi := by
  refine le_antisymm ?_ (measurable_pairJ U).comap_le
  let proj : (CoordJ → ℝ) → (ℕ × ℕ → ℝ) := fun a j => a (Finsupp.single j 1)
  have hproj : Measurable proj := measurable_pi_iff.2 fun j => measurable_pi_apply _
  calc DistOn.measurableSpace U = MeasurableSpace.comap
        (fun (h : DistOn U) (j : ℕ × ℕ) => h (distGen U j)) MeasurableSpace.pi :=
        distOn_measurableSpace_eq_comap U
    _ = MeasurableSpace.comap (proj ∘ pairJ U) MeasurableSpace.pi := by
        congr 1; funext h j; simp [proj, pairJ, comb_single]
    _ = MeasurableSpace.comap (pairJ U) (MeasurableSpace.comap proj MeasurableSpace.pi) := by
        rw [MeasurableSpace.comap_comp]
    _ ≤ _ := MeasurableSpace.comap_mono hproj.comap_le

theorem measurableEmbedding_pairJ : MeasurableEmbedding (pairJ U) where
  injective := injective_pairJ U
  measurable := measurable_pairJ U
  measurableSet_image' := by
    intro s hs
    have hs' : MeasurableSet[MeasurableSpace.comap (pairJ U) MeasurableSpace.pi] s := by
      rw [← distOn_measurableSpace_eq_comap_pairJ]; exact hs
    obtain ⟨t, ht, rfl⟩ := hs'
    rw [image_preimage_eq_inter_range]
    exact ht.inter (measurableSet_range_pairJ U)

/-- `𝒟'(U)` with the cylinder σ-algebra is a standard Borel space -/
instance standardBorelSpace_distOn : StandardBorelSpace (DistOn U) := by
  have := (measurableSet_range_pairJ U).standardBorel
  exact LQGMetric.standardBorelSpace_of_measurableEquiv (measurableEmbedding_pairJ U).equivRange

end

example : StandardBorelSpace (DistRd d) := inferInstance

end HigherDimLQGMetric
