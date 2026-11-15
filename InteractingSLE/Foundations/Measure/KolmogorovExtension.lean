import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Kolmogorov extension for countable inverse systems of standard Borel spaces

Packet PROVE-EXT (graph node `EXT.MEAS.kolmogorov-extension`: "a projectively consistent family of
laws on finite (or increasing) products of standard Borel spaces extends to a unique law on the
countable product"). Infrastructure, not a frozen source-facing file.

Mathlib (`a4c8ef0a`) has the Ionescu-Tulcea theorem (`ProbabilityTheory.Kernel.traj`,
`Kernel.trajMeasure`), regular conditional kernels on standard Borel spaces
(`MeasureTheory.Measure.condKernel`) and uniqueness of projective limits
(`MeasureTheory.IsProjectiveLimit.unique`), but no existence theorem for projective limits. We
derive it from Ionescu-Tulcea: for an inverse system `π n : Y (n + 1) → Y n` with consistent laws
`μ n`, the Markov kernels `y_n ↦ law of y_{n+1} given π n y_{n+1} = y_n` (the conditional kernel of
the joint law of `(π n y, y)`, `y ∼ μ (n + 1)`) drive a Markov chain whose one-dimensional laws are
the `μ n` and which is almost surely consistent.

## Main results

* `exists_map_eval_eq_of_inverseSystem`: inverse-limit form (sequential inverse systems of
  standard Borel spaces, arbitrary measurable bonding maps);
* `exists_map_eval_eq_of_lawConsistent`: the same with the laws given as image laws `Q n ∘ O n⁻¹`
  of observations on one space that agree on `σ(O n)` (the form used for stopped histories);
* `exists_isProjectiveLimit`: the classical Kolmogorov extension theorem for a projective family
  indexed by the finite subsets of a countable index set, all coordinate spaces standard Borel;
* `exists_map_frestrictLe_eq`, `exists_map_frestrictLe_eq_of_succ`: the versions for families on
  the initial segments `Iic n` of `ℕ`;
* `eq_of_map_eval_eq_of_inverseSystem`: uniqueness of the inverse-limit law.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InteractingSLE.Kolmogorov

/-! ### A composition-product identity -/

section CompProd

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- Pushing `ν ⊗ₘ (κ ∘ f)` forward along `f × id` gives `f_* ν ⊗ₘ κ`. -/
theorem map_prodMap_compProd_comap (ν : Measure α) [SFinite ν] (κ : Kernel β γ)
    [IsSFiniteKernel κ] {f : α → β} (hf : Measurable f) :
    (ν ⊗ₘ κ.comap f hf).map (Prod.map f id) = ν.map f ⊗ₘ κ := by
  ext s hs
  have hs' : MeasurableSet (Prod.map f id ⁻¹' s) := (hf.prodMap measurable_id) hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs, Measure.compProd_apply hs',
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

end CompProd

/-! ### Inverse systems -/

section InverseSystem

variable {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]

/-- The joint law of `(π n y, y)` for `y ∼ μ (n + 1)`. -/
def stepLaw (π : ∀ n, Y (n + 1) → Y n) (μ : ∀ n, Measure (Y n)) (n : ℕ) :
    Measure (Y n × Y (n + 1)) :=
  (μ (n + 1)).map (fun y => (π n y, y))

instance (π : ∀ n, Y (n + 1) → Y n) (μ : ∀ n, Measure (Y n)) [∀ n, IsFiniteMeasure (μ n)]
    (n : ℕ) : IsFiniteMeasure (stepLaw π μ n) := by
  rw [stepLaw]
  infer_instance

variable [∀ n, StandardBorelSpace (Y n)] [∀ n, Nonempty (Y n)]

/-- The transition kernel of the Markov chain realizing an inverse system: from the history up to
time `n`, sample `y_{n+1}` from the conditional law of `y` given `π n y = y_n`. -/
def chainKernel (π : ∀ n, Y (n + 1) → Y n) (μ : ∀ n, Measure (Y n))
    [∀ n, IsProbabilityMeasure (μ n)] (n : ℕ) :
    Kernel (∀ i : Finset.Iic n, Y i) (Y (n + 1)) :=
  (stepLaw π μ n).condKernel.comap (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩)
    (measurable_pi_apply _)

instance (π : ∀ n, Y (n + 1) → Y n) (μ : ∀ n, Measure (Y n)) [∀ n, IsProbabilityMeasure (μ n)]
    (n : ℕ) : IsMarkovKernel (chainKernel π μ n) := by
  rw [chainKernel]
  infer_instance

/-- The law of the Markov chain realizing an inverse system. -/
def chainMeasure (π : ∀ n, Y (n + 1) → Y n) (μ : ∀ n, Measure (Y n))
    [∀ n, IsProbabilityMeasure (μ n)] : Measure (∀ n, Y n) :=
  Kernel.trajMeasure (μ 0) (chainKernel π μ)

variable (π : ∀ n, Y (n + 1) → Y n) (μ : ∀ n, Measure (Y n)) [∀ n, IsProbabilityMeasure (μ n)]

instance : IsProbabilityMeasure (chainMeasure π μ) := by
  rw [chainMeasure]
  infer_instance

theorem chainMeasure_map_eval_zero : (chainMeasure π μ).map (fun y => y 0) = μ 0 := by
  have h1 : (fun y : ∀ n, Y n => y 0) =
      (fun x : ∀ i : Finset.Iic 0, Y i => x ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘
        Preorder.frestrictLe 0 := rfl
  have h2 : (chainMeasure π μ).map (Preorder.frestrictLe 0) =
      (μ 0).map (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => Y i)).symm := by
    rw [chainMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have h3 : (fun x : ∀ i : Finset.Iic 0, Y i => x ⟨0, Finset.mem_Iic.2 le_rfl⟩) ∘
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => Y i)).symm = id := by
    funext y
    rfl
  rw [h1, ← Measure.map_map (measurable_pi_apply _) (Preorder.measurable_frestrictLe 0), h2,
    Measure.map_map (measurable_pi_apply _) (MeasurableEquiv.measurable _), h3, Measure.map_id]

variable {π μ}

/-- If the chain has law `μ n` at time `n`, its two-step law at `(n, n + 1)` is `stepLaw π μ n`. -/
theorem chainMeasure_map_pair (hπ : ∀ n, Measurable (π n))
    (hμ : ∀ n, (μ (n + 1)).map (π n) = μ n) {n : ℕ}
    (hn : (chainMeasure π μ).map (fun y => y n) = μ n) :
    (chainMeasure π μ).map (fun y => (y n, y (n + 1))) = stepLaw π μ n := by
  set e : (∀ i : Finset.Iic n, Y i) → Y n := fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩ with he
  have hem : Measurable e := measurable_pi_apply _
  have h1 : (fun y : ∀ n, Y n => (y n, y (n + 1))) =
      Prod.map e id ∘ (fun y => (Preorder.frestrictLe n y, y (n + 1))) := rfl
  have h2 : (chainMeasure π μ).map (Preorder.frestrictLe n) ⊗ₘ chainKernel π μ n =
      (chainMeasure π μ).map (fun y => (Preorder.frestrictLe n y, y (n + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have hfst : (stepLaw π μ n).fst = μ n := by
    rw [stepLaw, Measure.fst_map_prodMk (hπ n) measurable_id', hμ n]
  rw [h1, ← Measure.map_map (hem.prodMap measurable_id) (by fun_prop), ← h2, chainKernel,
    map_prodMap_compProd_comap _ _ hem, Measure.map_map hem (Preorder.measurable_frestrictLe n)]
  have h3 : e ∘ Preorder.frestrictLe n = fun y : ∀ n, Y n => y n := rfl
  rw [h3, hn, ← hfst, Measure.disintegrate]

/-- The chain has law `μ n` at every time `n`. -/
theorem chainMeasure_map_eval (hπ : ∀ n, Measurable (π n))
    (hμ : ∀ n, (μ (n + 1)).map (π n) = μ n) (n : ℕ) :
    (chainMeasure π μ).map (fun y => y n) = μ n := by
  induction n with
  | zero => exact chainMeasure_map_eval_zero π μ
  | succ n ih =>
    have h := chainMeasure_map_pair hπ hμ ih
    have h' := congrArg Measure.snd h
    rw [Measure.snd_map_prodMk (measurable_pi_apply _) (measurable_pi_apply _), stepLaw,
      Measure.snd_map_prodMk (hπ n) measurable_id', Measure.map_id'] at h'
    exact h'

/-- The chain is almost surely consistent with the bonding maps. -/
theorem ae_chainMeasure_consistent (hπ : ∀ n, Measurable (π n))
    (hμ : ∀ n, (μ (n + 1)).map (π n) = μ n) :
    ∀ᵐ y ∂(chainMeasure π μ), ∀ n, π n (y (n + 1)) = y n := by
  rw [ae_all_iff]
  intro n
  have hS : MeasurableSet {p : Y n × Y (n + 1) | π n p.2 = p.1} :=
    measurableSet_eq_fun ((hπ n).comp measurable_snd) measurable_fst
  have hpair : Measurable (fun y : ∀ n, Y n => (y n, y (n + 1))) := by fun_prop
  have h := chainMeasure_map_pair hπ hμ (chainMeasure_map_eval hπ hμ n)
  have h0 : (stepLaw π μ n) {p | π n p.2 = p.1}ᶜ = 0 := by
    rw [stepLaw, Measure.map_apply (by fun_prop) hS.compl]
    convert measure_empty (μ := μ (n + 1))
    ext y
    simp
  rw [← h, Measure.map_apply hpair hS.compl] at h0
  exact measure_mono_null (fun y hy => hy) h0

/-- **Kolmogorov extension, inverse-limit form.** A sequential inverse system of standard Borel
spaces `π n : Y (n + 1) → Y n` (measurable) with consistent probability laws `μ n`
(`π n` pushes `μ (n + 1)` to `μ n`) carries a probability measure on the product `∀ n, Y n` with
one-dimensional marginals `μ n`, concentrated on the inverse limit `{y | ∀ n, π n (y (n + 1)) = y n}`. -/
theorem exists_map_eval_eq_of_inverseSystem {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    [∀ n, StandardBorelSpace (Y n)] (π : ∀ n, Y (n + 1) → Y n) (hπ : ∀ n, Measurable (π n))
    (μ : ∀ n, Measure (Y n)) [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ n, (μ (n + 1)).map (π n) = μ n) :
    ∃ ν : Measure (∀ n, Y n), IsProbabilityMeasure ν ∧ (∀ n, ν.map (fun y => y n) = μ n) ∧
      ∀ᵐ y ∂ν, ∀ n, π n (y (n + 1)) = y n := by
  have : ∀ n, Nonempty (Y n) := fun n => nonempty_of_isProbabilityMeasure (μ n)
  exact ⟨chainMeasure π μ, inferInstance, chainMeasure_map_eval hπ hμ,
    ae_chainMeasure_consistent hπ hμ⟩

/-- **Kolmogorov extension for laws of nested observations.** Let `Q n` be probability measures on
one space and `O n` measurable observations with values in standard Borel spaces, nested through
measurable maps (`π n ∘ O (n + 1) = O n`, `Q (n + 1)`-a.e.), and suppose `Q n` and `Q (n + 1)` give
`O n` the same law. Then some probability measure on `∀ n, Y n` has `n`-th marginal the `Q n`-law of
`O n`, and is concentrated on the inverse limit. -/
theorem exists_map_eval_eq_of_lawConsistent {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)] [∀ n, StandardBorelSpace (Y n)]
    (Q : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (Q n)] (O : ∀ n, Ω → Y n)
    (hO : ∀ n, Measurable (O n)) (π : ∀ n, Y (n + 1) → Y n) (hπ : ∀ n, Measurable (π n))
    (hnest : ∀ n, ∀ᵐ ω ∂(Q (n + 1)), π n (O (n + 1) ω) = O n ω)
    (hcons : ∀ n, (Q (n + 1)).map (O n) = (Q n).map (O n)) :
    ∃ ν : Measure (∀ n, Y n), IsProbabilityMeasure ν ∧
      (∀ n, ν.map (fun y => y n) = (Q n).map (O n)) ∧ ∀ᵐ y ∂ν, ∀ n, π n (y (n + 1)) = y n := by
  refine exists_map_eval_eq_of_inverseSystem π hπ (fun n => (Q n).map (O n)) fun n => ?_
  rw [Measure.map_map (hπ n) (hO (n + 1)), ← hcons n]
  exact Measure.map_congr (hnest n)

/-- **Uniqueness for nested observations.** If `π n ∘ O (n + 1) = O n` and two finite measures give
every `O n` the same law, they agree on `⨆ n, σ(O n)`. -/
theorem eq_of_map_eq_of_nested {Ω : Type*} {mΩ : MeasurableSpace Ω} {Y : ℕ → Type*}
    [∀ n, MeasurableSpace (Y n)] {P₁ P₂ : Measure Ω} [IsFiniteMeasure P₁]
    (O : ∀ n, Ω → Y n) (hO : ∀ n, Measurable (O n)) (π : ∀ n, Y (n + 1) → Y n)
    (hπ : ∀ n, Measurable (π n)) (hnest : ∀ n, π n ∘ O (n + 1) = O n)
    (hlaw : ∀ n, P₁.map (O n) = P₂.map (O n)) {s : Set Ω}
    (hs : MeasurableSet[⨆ n, MeasurableSpace.comap (O n) inferInstance] s) : P₁ s = P₂ s := by
  set m : MeasurableSpace Ω := ⨆ n, MeasurableSpace.comap (O n) inferInstance with hm
  have hmle : m ≤ mΩ := iSup_le fun n => (hO n).comap_le
  have hmono : Monotone fun n => MeasurableSpace.comap (O n) inferInstance := by
    refine monotone_nat_of_le_succ fun n => ?_
    rw [← hnest n, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (hπ n).comap_le
  set C : ℕ → Set (Set Ω) := fun n => {t | MeasurableSet[MeasurableSpace.comap (O n) inferInstance] t}
  have hCpi : IsPiSystem (⋃ n, C n) :=
    isPiSystem_iUnion_of_monotone C
      (fun n => @MeasurableSpace.isPiSystem_measurableSet Ω (MeasurableSpace.comap (O n) inferInstance))
      fun a b hab t ht => hmono hab t ht
  have hgen : m = MeasurableSpace.generateFrom (⋃ n, C n) :=
    (MeasurableSpace.generateFrom_iUnion_measurableSet _).symm
  have huniv : P₁ univ = P₂ univ := by
    have h := congrArg (fun ν : Measure (Y 0) => ν univ) (hlaw 0)
    simpa [Measure.map_apply (hO 0) MeasurableSet.univ] using h
  have : IsFiniteMeasure (P₁.trim hmle) := isFiniteMeasure_trim hmle
  have htrim : P₁.trim hmle = P₂.trim hmle := by
    refine @ext_of_generate_finite Ω m _ _ (⋃ n, C n) hgen hCpi _ (fun t ht => ?_) ?_
    · have htm : MeasurableSet[m] t := by rw [hgen]; exact MeasurableSpace.measurableSet_generateFrom ht
      rw [trim_measurableSet_eq hmle htm, trim_measurableSet_eq hmle htm]
      obtain ⟨n, hn⟩ := mem_iUnion.1 ht
      obtain ⟨A, hA, rfl⟩ := hn
      have h := congrArg (fun ν : Measure (Y n) => ν A) (hlaw n)
      simpa [Measure.map_apply (hO n) hA] using h
    · rw [trim_measurableSet_eq hmle MeasurableSet.univ, trim_measurableSet_eq hmle MeasurableSet.univ,
        huniv]
  rw [← trim_measurableSet_eq hmle hs, htrim, trim_measurableSet_eq hmle hs]

end InverseSystem

/-! ### Projective families on countable products -/

section Projective

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, StandardBorelSpace (X i)]

/-- **Kolmogorov extension theorem** (countable index set, standard Borel coordinate spaces): a
projective family of probability measures on the finite subproducts has a projective limit, which
is a probability measure (and is unique, `MeasureTheory.IsProjectiveLimit.unique`). -/
theorem exists_isProjectiveLimit [Countable ι] (P : ∀ J : Finset ι, Measure (∀ j : J, X j))
    [∀ J, IsProbabilityMeasure (P J)] (hP : IsProjectiveMeasureFamily P) :
    ∃ μ : Measure (∀ i, X i), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ P := by
  classical
  obtain ⟨J, hJmono, hJtop⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop (Finset ι)
  have hev : ∀ I : Finset ι, ∃ n, I ⊆ J n := fun I =>
    (hJtop.eventually (eventually_ge_atTop I)).exists
  have hmem : ∀ i, ∃ n, i ∈ J n := fun i =>
    (hev {i}).imp fun n h => h (Finset.mem_singleton_self i)
  let N : ι → ℕ := fun i => Nat.find (hmem i)
  have hN : ∀ i, i ∈ J (N i) := fun i => Nat.find_spec (hmem i)
  let π : ∀ n, (∀ j : J (n + 1), X j) → (∀ j : J n, X j) := fun n =>
    Finset.restrict₂ (hJmono n.le_succ)
  obtain ⟨ν, hν, hmarg, hcons⟩ := exists_map_eval_eq_of_inverseSystem π
    (fun n => Finset.measurable_restrict₂ _) (fun n => P (J n))
    (fun n => (hP _ _ (hJmono n.le_succ)).symm)
  let g : (∀ n, ∀ j : J n, X j) → ∀ i, X i := fun y i => y (N i) ⟨i, hN i⟩
  have hg : Measurable g :=
    Measurable.of_eval fun i => (measurable_pi_apply _).comp (measurable_pi_apply (N i))
  have hchain : ∀ᵐ y ∂ν, ∀ n k (j : J n), y (n + k) ⟨j, hJmono (Nat.le_add_right n k) j.2⟩ = y n j := by
    filter_upwards [hcons] with y hy n k
    induction k with
    | zero => exact fun j => rfl
    | succ k ih =>
      intro j
      exact (congrFun (hy (n + k)) ⟨j, hJmono (Nat.le_add_right n k) j.2⟩).trans (ih j)
  have hchain' : ∀ᵐ y ∂ν, ∀ m n (h : m ≤ n) (i : ι) (hi : i ∈ J m),
      y n ⟨i, hJmono h hi⟩ = y m ⟨i, hi⟩ := by
    filter_upwards [hchain] with y hy m n h i hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    exact hy m k ⟨i, hi⟩
  refine ⟨ν.map g, inferInstance, fun I => ?_⟩
  obtain ⟨n, hIn⟩ := hev I
  have hae : (fun y => Finset.restrict I (g y)) =ᵐ[ν] fun y => Finset.restrict₂ hIn (y n) := by
    filter_upwards [hchain'] with y hy
    funext i
    rcases le_total (N i) n with h | h
    · exact (hy (N i) n h i (hN i)).symm
    · exact hy n (N i) h i (hIn i.2)
  rw [Measure.map_map (Finset.measurable_restrict I) hg]
  change ν.map (fun y => Finset.restrict I (g y)) = P I
  rw [Measure.map_congr hae]
  change ν.map (Finset.restrict₂ hIn ∘ fun y => y n) = P I
  rw [← Measure.map_map (Finset.measurable_restrict₂ hIn) (measurable_pi_apply n), hmarg n,
    ← hP (J n) I hIn]

/-- **Kolmogorov extension on `ℕ`-indexed products**, for families on the initial segments
`Iic n`: consistent probability measures `μ n` on `∀ i : Iic n, X i` are the marginals of one
probability measure on `∀ n, X n`. -/
theorem exists_map_frestrictLe_eq {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, StandardBorelSpace (X n)] (μ : ∀ n, Measure (∀ i : Finset.Iic n, X i))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ m n (hmn : m ≤ n), (μ n).map (Preorder.frestrictLe₂ hmn) = μ m) :
    ∃ ν : Measure (∀ n, X n), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (Preorder.frestrictLe n) = μ n := by
  obtain ⟨ν, hν, hlim⟩ :=
    exists_isProjectiveLimit (inducedFamily μ) (isProjectiveMeasureFamily_inducedFamily μ hμ)
  exact ⟨ν, hν, fun n => by rw [← inducedFamily_Iic μ n]; exact hlim (Finset.Iic n)⟩

/-- The version of `exists_map_frestrictLe_eq` with one-step consistency
`(μ (n + 1)).map (frestrictLe₂ _) = μ n`. -/
theorem exists_map_frestrictLe_eq_of_succ {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    [∀ n, StandardBorelSpace (X n)] (μ : ∀ n, Measure (∀ i : Finset.Iic n, X i))
    [∀ n, IsProbabilityMeasure (μ n)]
    (hμ : ∀ n, (μ (n + 1)).map (Preorder.frestrictLe₂ n.le_succ) = μ n) :
    ∃ ν : Measure (∀ n, X n), IsProbabilityMeasure ν ∧
      ∀ n, ν.map (Preorder.frestrictLe n) = μ n := by
  refine exists_map_frestrictLe_eq μ fun m n hmn => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => exact Measure.map_id
  | succ k ih =>
    rw [← ih (Nat.le_add_right m k), ← hμ (m + k), Measure.map_map
      (Preorder.measurable_frestrictLe₂ _) (Preorder.measurable_frestrictLe₂ _),
      Preorder.frestrictLe₂_comp_frestrictLe₂]
    rfl

end Projective

end InteractingSLE.Kolmogorov
