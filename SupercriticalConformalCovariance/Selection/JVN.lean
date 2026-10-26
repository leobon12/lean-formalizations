import LQGMetric.Meas.UM

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set Filter

namespace SupercriticalConformalCovariance.Selection

/-! The analytic uniformization step at source lines 323–328. -/

theorem analyticSet_um {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : AnalyticSet s) :
    LQGMetric.UMeasurableSet s := by
  intro μ hμ
  letI : IsFiniteMeasure μ := hμ
  exact QuantumZipper.Thm18Asm.G4Core.analyticSet_nullMeasurableSet hs μ

theorem analytic_projection_um {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    {A : Set (X × Y)} (hA : AnalyticSet A) :
    LQGMetric.UMeasurableSet (Prod.fst '' A) :=
  analyticSet_um (hA.image_of_continuous continuous_fst)

theorem umap_aemeasurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] {f : X → Y}
    (hf : ∀ s : Set Y, MeasurableSet s → LQGMetric.UMeasurableSet (f ⁻¹' s))
    (μ : Measure X) [IsFiniteMeasure μ] : AEMeasurable f μ :=
  (show NullMeasurable f μ from fun _ hs => hf _ hs μ inferInstance).aemeasurable

theorem umap_comp_aemeasurable {Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
    {f : X → Y} (hf : ∀ s : Set Y, MeasurableSet s →
      LQGMetric.UMeasurableSet (f ⁻¹' s))
    {Z : Ω → X} (hZ : Measurable Z) (P : Measure Ω) [IsFiniteMeasure P] :
    AEMeasurable (f ∘ Z) P := by
  apply MeasureTheory.NullMeasurable.aemeasurable
  intro s hs
  exact (hf s hs).nullMeasurableSet_preimage hZ.aemeasurable

theorem umap_fst {X Y₁ Y₂ : Type*} [MeasurableSpace X]
    [MeasurableSpace Y₁] [MeasurableSpace Y₂] {f : X → Y₁ × Y₂}
    (hf : ∀ s : Set (Y₁ × Y₂), MeasurableSet s →
      LQGMetric.UMeasurableSet (f ⁻¹' s)) :
    ∀ s : Set Y₁, MeasurableSet s →
      LQGMetric.UMeasurableSet ((Prod.fst ∘ f) ⁻¹' s) := by
  intro s hs
  exact hf (Prod.fst ⁻¹' s) (measurable_fst hs)

private def HasPrefix {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) {n : ℕ} (p : Fin n → ℕ) : Prop :=
  ∃ σ : ℕ → ℕ, (g σ).1 = x ∧ ∀ i : Fin n, σ i = p i

private theorem hasPrefix_um {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (g : (ℕ → ℕ) → X × Y) (hg : Continuous g) {n : ℕ} (p : Fin n → ℕ) :
    LQGMetric.UMeasurableSet {x : X | HasPrefix g x p} := by
  let C : Set (ℕ → ℕ) := {σ | ∀ i : Fin n, σ i = p i}
  have hC : MeasurableSet C := by
    have h : MeasurableSet (⋂ i : Fin n, {σ : ℕ → ℕ | σ i = p i}) :=
      MeasurableSet.iInter (fun i => by
        have heval : Measurable (fun σ : ℕ → ℕ => σ (i : ℕ)) :=
          measurable_pi_apply (i : ℕ)
        simpa only [Set.preimage, Set.mem_singleton_iff] using
          (heval (measurableSet_singleton (p i))))
    convert h using 1
    ext σ
    simp [C]
  have hImage : LQGMetric.UMeasurableSet ((fun σ => (g σ).1) '' C) :=
    LQGMetric.UMeasurableSet.image (measurable_fst.comp hg.measurable) hC
  convert hImage using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, C, HasPrefix]
  constructor
  · rintro ⟨σ, hσx, hσp⟩
    exact ⟨σ, hσp, hσx⟩
  · rintro ⟨σ, hσp, hσx⟩
    exact ⟨σ, hσx, hσp⟩

private theorem hasPrefix_extend {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) {n : ℕ} {p : Fin n → ℕ} (h : HasPrefix g x p) :
    ∃ k : ℕ, HasPrefix g x (Fin.snoc p k) := by
  obtain ⟨σ, hσx, hσp⟩ := h
  refine ⟨σ n, σ, hσx, ?_⟩
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simpa using hσp j

private def nextPred {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) {n : ℕ} (p : Fin n → ℕ) (k : ℕ) : Prop :=
  HasPrefix g x (Fin.snoc p k) ∨
    (k = 0 ∧ ¬ ∃ j : ℕ, HasPrefix g x (Fin.snoc p j))

private theorem nextPred_exists {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) {n : ℕ} (p : Fin n → ℕ) : ∃ k, nextPred g x p k := by
  by_cases h : ∃ k : ℕ, HasPrefix g x (Fin.snoc p k)
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, Or.inl hk⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

private noncomputable def nextDigit {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) {n : ℕ} (p : Fin n → ℕ) : ℕ := by
  classical
  exact Nat.find (nextPred_exists g x p)

private theorem nextDigit_hasPrefix {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) {n : ℕ} {p : Fin n → ℕ} (h : HasPrefix g x p) :
    HasPrefix g x (Fin.snoc p (nextDigit g x p)) := by
  classical
  have hnext := Nat.find_spec (nextPred_exists g x p)
  change nextPred g x p (nextDigit g x p) at hnext
  rcases hnext with hnext | ⟨_, hnone⟩
  · exact hnext
  · exact False.elim (hnone (hasPrefix_extend g x h))

private noncomputable def chosenPrefix {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) : (n : ℕ) → Fin n → ℕ
  | 0 => Fin.elim0
  | n + 1 => Fin.snoc (chosenPrefix g x n) (nextDigit g x (chosenPrefix g x n))

private theorem chosenPrefix_hasPrefix {X Y : Type*} (g : (ℕ → ℕ) → X × Y)
    (x : X) (hx : x ∈ Prod.fst '' Set.range g) (n : ℕ) :
    HasPrefix g x (chosenPrefix g x n) := by
  induction n with
  | zero =>
      obtain ⟨a, ⟨σ, rfl⟩, ha⟩ := hx
      refine ⟨σ, ?_, ?_⟩
      · exact ha
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      exact nextDigit_hasPrefix g x ih

private def umSpace (X : Type*) [MeasurableSpace X] : MeasurableSpace X where
  MeasurableSet' := LQGMetric.UMeasurableSet
  measurableSet_empty := LQGMetric.UMeasurableSet.empty
  measurableSet_compl := fun _ h => h.compl
  measurableSet_iUnion := fun _ h => LQGMetric.UMeasurableSet.iUnion h

private theorem nextDigit_measurable {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [mX : MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (g : (ℕ → ℕ) → X × Y) (hg : Continuous g) {n : ℕ} (p : Fin n → ℕ) :
    @Measurable X ℕ (umSpace X) inferInstance (fun x => nextDigit g x p) := by
  classical
  have hP0 : ∀ k : ℕ, LQGMetric.UMeasurableSet
      {x : X | HasPrefix g x (Fin.snoc p k)} := fun k => hasPrefix_um g hg _
  letI : MeasurableSpace X := umSpace X
  have hP : ∀ k : ℕ, MeasurableSet {x : X | HasPrefix g x (Fin.snoc p k)} := hP0
  have hExist : MeasurableSet {x : X | ∃ k : ℕ, HasPrefix g x (Fin.snoc p k)} := by
    have h := MeasurableSet.iUnion hP
    convert h using 1
    ext x
    simp
  have hPred : ∀ k : ℕ, MeasurableSet {x : X | nextPred g x p k} := by
    intro k
    by_cases hk : k = 0
    · subst k
      have hn : MeasurableSet
          {x : X | ¬∃ j : ℕ, HasPrefix g x (Fin.snoc p j)} := hExist.compl
      have hu := (hP 0).union hn
      convert hu using 1
      ext x
      simp [nextPred]
    · simpa [nextPred, hk] using hP k
  have hm : Measurable (fun x : X => Nat.find (nextPred_exists g x p)) :=
    measurable_find (fun x => nextPred_exists g x p) hPred
  simpa only [nextDigit] using hm

private theorem measurable_countable_family {X D : Type*} [MeasurableSpace X]
    [MeasurableSpace D] [Countable D] [MeasurableSingletonClass D]
    (p : X → D) (hp : Measurable p) (F : D → X → ℕ)
    (hF : ∀ d, Measurable (F d)) :
    Measurable (fun x => F (p x) x) := by
  apply measurable_to_countable'
  intro k
  have h : MeasurableSet (⋃ d : D,
      (p ⁻¹' {d}) ∩ ((F d) ⁻¹' {k})) :=
    MeasurableSet.iUnion (fun d =>
      (hp (measurableSet_singleton d)).inter ((hF d) (measurableSet_singleton k)))
  convert h using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hx
    exact ⟨p x, rfl, hx⟩
  · rintro ⟨d, hd, hdx⟩
    simpa [hd] using hdx

private theorem chosenPrefix_measurable {X Y : Type*} [TopologicalSpace X]
    [PolishSpace X] [mX : MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : (ℕ → ℕ) → X × Y) (hg : Continuous g) (n : ℕ) :
    @Measurable X (Fin n → ℕ) (umSpace X) inferInstance
      (fun x => chosenPrefix g x n) := by
  have hFixed : ∀ (n : ℕ) (p : Fin n → ℕ),
      @Measurable X ℕ (umSpace X) inferInstance (fun x => nextDigit g x p) :=
    fun _ p => nextDigit_measurable g hg p
  letI : MeasurableSpace X := umSpace X
  induction n with
  | zero =>
      exact Measurable.of_eval (fun i => Fin.elim0 i)
  | succ n ih =>
      have hd : Measurable
          (fun x : X => nextDigit g x (chosenPrefix g x n)) :=
        measurable_countable_family (fun x => chosenPrefix g x n) ih
          (fun p x => nextDigit g x p) (hFixed n)
      apply Measurable.of_eval
      intro i
      cases i using Fin.lastCases with
      | last => simpa only [chosenPrefix, Fin.snoc_last] using hd
      | cast j =>
          simpa only [chosenPrefix, Fin.snoc_castSucc, Function.comp_def] using
            ((measurable_pi_apply j).comp ih)

private noncomputable def chosenBranch {X Y : Type*}
    (g : (ℕ → ℕ) → X × Y) (x : X) (i : ℕ) : ℕ :=
  chosenPrefix g x (i + 1) (Fin.last i)

private theorem chosenPrefix_eq_branch {X Y : Type*}
    (g : (ℕ → ℕ) → X × Y) (x : X) (n : ℕ) (i : Fin n) :
    chosenPrefix g x n i = chosenBranch g x i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.lastCases with
      | last => rfl
      | cast j =>
          simpa only [chosenPrefix, Fin.snoc_castSucc, Fin.val_castSucc]
            using ih j

private theorem chosenBranch_in_fiber {X Y : Type*} [TopologicalSpace X]
    [T2Space X] [TopologicalSpace Y]
    (g : (ℕ → ℕ) → X × Y) (hg : Continuous g)
    (x : X) (hx : x ∈ Prod.fst '' Set.range g) :
    (g (chosenBranch g x)).1 = x := by
  classical
  let w : ℕ → (ℕ → ℕ) := fun n =>
    Classical.choose (chosenPrefix_hasPrefix g x hx n)
  have hw (n : ℕ) : (g (w n)).1 = x ∧
      ∀ i : Fin n, w n i = chosenPrefix g x n i :=
    Classical.choose_spec (chosenPrefix_hasPrefix g x hx n)
  have hcoord (i : ℕ) :
      Tendsto (fun n => w n i) Filter.atTop (nhds (chosenBranch g x i)) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [Filter.eventually_ge_atTop (i + 1)] with n hn
    let j : Fin n := ⟨i, by omega⟩
    calc
      w n i = chosenPrefix g x n j := (hw n).2 j
      _ = chosenBranch g x i := chosenPrefix_eq_branch g x n j
  have hconv : Tendsto w Filter.atTop (nhds (chosenBranch g x)) :=
    tendsto_pi_nhds.mpr hcoord
  have hcont : Continuous (fun σ : ℕ → ℕ => (g σ).1) :=
    continuous_fst.comp hg
  have hlim : Tendsto (fun n => (g (w n)).1) Filter.atTop
      (nhds ((g (chosenBranch g x)).1)) :=
    (hcont.tendsto (chosenBranch g x)).comp hconv
  have hconst : (fun n => (g (w n)).1) = fun _ : ℕ => x := by
    funext n
    exact (hw n).1
  rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem chosenBranch_measurable {X Y : Type*} [TopologicalSpace X]
    [PolishSpace X] [mX : MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (g : (ℕ → ℕ) → X × Y) (hg : Continuous g) :
    @Measurable X (ℕ → ℕ) (umSpace X) inferInstance (chosenBranch g) := by
  have hp0 : ∀ i : ℕ,
      @Measurable X (Fin (i + 1) → ℕ) (umSpace X) inferInstance
        (fun x => chosenPrefix g x (i + 1)) :=
    fun i => chosenPrefix_measurable g hg (i + 1)
  letI : MeasurableSpace X := umSpace X
  apply Measurable.of_eval
  intro i
  have hp := hp0 i
  simpa only [chosenBranch, Function.comp_def] using
    ((measurable_pi_apply (Fin.last i)).comp hp)

/-- Jankov–von Neumann uniformization for an analytic relation in Polish spaces.
The nonemptiness of `Y` is needed to define the selector outside the projection. -/
theorem analytic_uniformization {X Y : Type*} [TopologicalSpace X]
    [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Nonempty Y] {A : Set (X × Y)} (hA : AnalyticSet A) :
    ∃ f : X → Y,
      (∀ x ∈ Prod.fst '' A, (x, f x) ∈ A) ∧
      (∀ s : Set Y, MeasurableSet s →
        LQGMetric.UMeasurableSet (f ⁻¹' s)) := by
  classical
  rw [AnalyticSet] at hA
  rcases hA with hEmpty | ⟨g, hg, hgA⟩
  · subst A
    letI : Inhabited Y := ⟨Classical.choice inferInstance⟩
    refine ⟨fun _ => default, ?_, ?_⟩
    · intro x hx
      simp at hx
    · intro s hs
      have hm : @Measurable X Y (umSpace X) inferInstance (fun _ => default) :=
        measurable_const
      exact hm hs
  · refine ⟨fun x => (g (chosenBranch g x)).2, ?_, ?_⟩
    · intro x hx
      rw [← hgA] at hx ⊢
      refine ⟨chosenBranch g x, ?_⟩
      exact Prod.ext (chosenBranch_in_fiber g hg x hx) rfl
    · intro s hs
      have hgm : Measurable (fun σ : ℕ → ℕ => (g σ).2) :=
        measurable_snd.comp hg.measurable
      have hbm := chosenBranch_measurable g hg
      have hm : @Measurable X Y (umSpace X) inferInstance
          (fun x => (g (chosenBranch g x)).2) := hgm.comp hbm
      exact hm hs

/-- A universally measurable selector composed with a measurable random input is measurable for
the probability completion. -/
theorem analytic_uniformization_probability {Ω X Y : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [Nonempty Y] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → X} (hZ : Measurable Z) {A : Set (X × Y)} (hA : AnalyticSet A) :
    ∃ W : Ω → Y, AEMeasurable W P ∧
      ∀ ω, Z ω ∈ Prod.fst '' A → (Z ω, W ω) ∈ A := by
  obtain ⟨f, hfA, hfUM⟩ := analytic_uniformization hA
  refine ⟨f ∘ Z, umap_comp_aemeasurable hfUM hZ P, ?_⟩
  intro ω hω
  exact hfA (Z ω) hω

/-- The endpoint component of a selected witness remains a.e. measurable. -/
theorem analytic_uniformization_probability_fst {Ω X Y₁ Y₂ : Type*}
    [MeasurableSpace Ω] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y₁] [PolishSpace Y₁] [MeasurableSpace Y₁] [BorelSpace Y₁]
    [TopologicalSpace Y₂] [PolishSpace Y₂] [MeasurableSpace Y₂] [BorelSpace Y₂]
    [Nonempty Y₁] [Nonempty Y₂] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → X} (hZ : Measurable Z) {A : Set (X × (Y₁ × Y₂))}
    (hA : AnalyticSet A) :
    ∃ W : Ω → Y₁, AEMeasurable W P ∧
      ∀ ω, Z ω ∈ Prod.fst '' A → ∃ y₂ : Y₂, (Z ω, (W ω, y₂)) ∈ A := by
  obtain ⟨V, hV, hVA⟩ := analytic_uniformization_probability P hZ hA
  refine ⟨Prod.fst ∘ V, measurable_fst.comp_aemeasurable hV, ?_⟩
  intro ω hω
  exact ⟨(V ω).2, hVA ω hω⟩

end SupercriticalConformalCovariance.Selection
