import InteractingSLE.Spec.Coupling.ResampleCore
import InteractingSLE.GFF.LocalSets.Basic

/-!
# Gaussian resampling: the finite chain of stages (Theorem 1.1, obligation 3)

Packet PROVE-T11-KER (Astra §1, pp. 5–6). A finite chain of stages `k = 0, 1, …, N` is given by increasing
σ-algebras `𝒜 k` (the stopped σ-algebras at the stage times), random regions `V (R k ω)` (indices `R k ω` in a finite
family, decreasing in `k`, the next one known at the current stage), and kernels `Q k T` (the protected kernels at the
stage times). Starting from a field kernel `η₀`, `exists_chain` produces one field kernel `η` whose restriction to the
stage region has, on the events of each stage σ-algebra, the joint law of the stage kernel, and whose joint law with
`𝒜 0` is that of `η₀`.

* `RectAgree 𝒜 P E κ₁ κ₂` : `P ⊗ κ₁` and `P ⊗ κ₂` agree on the rectangles `A × B`, `A ∈ 𝒜`, `A ⊆ E`;
* `exists_stage_on` : `exists_stage` on an event `E ∈ 𝒜`;
* `exists_chain` : the chain.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

open LQGMetric GFF

section RectAgree

variable {Ω X : Type*} [MeasurableSpace X]

/-- `P ⊗ κ₁` and `P ⊗ κ₂` agree on the rectangles `A × B` with `A ∈ 𝒜` and `A ⊆ E`. -/
def RectAgree (𝒜 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) (E : Set Ω)
    (κ₁ κ₂ : Kernel Ω X) : Prop :=
  ∀ A, MeasurableSet[𝒜] A → A ⊆ E → ∀ B, MeasurableSet B → (P ⊗ₘ κ₁) (A ×ˢ B) = (P ⊗ₘ κ₂) (A ×ˢ B)

theorem RectAgree.symm {𝒜 mΩ : MeasurableSpace Ω} {P : Measure Ω} {E : Set Ω} {κ₁ κ₂ : Kernel Ω X}
    (h : RectAgree 𝒜 P E κ₁ κ₂) : RectAgree 𝒜 P E κ₂ κ₁ :=
  fun A hA hAE B hB => (h A hA hAE B hB).symm

theorem RectAgree.trans {𝒜 mΩ : MeasurableSpace Ω} {P : Measure Ω} {E : Set Ω} {κ₁ κ₂ κ₃ : Kernel Ω X}
    (h₁ : RectAgree 𝒜 P E κ₁ κ₂) (h₂ : RectAgree 𝒜 P E κ₂ κ₃) : RectAgree 𝒜 P E κ₁ κ₃ :=
  fun A hA hAE B hB => (h₁ A hA hAE B hB).trans (h₂ A hA hAE B hB)

theorem RectAgree.mono {𝒜 𝒜' _mΩ : MeasurableSpace Ω} {P : Measure Ω} {E E' : Set Ω}
    {κ₁ κ₂ : Kernel Ω X} (h : RectAgree 𝒜 P E κ₁ κ₂) (h𝒜 : 𝒜' ≤ 𝒜) (hE : E' ⊆ E) :
    RectAgree 𝒜' P E' κ₁ κ₂ :=
  fun A hA hAE B hB => h A (h𝒜 A hA) (hAE.trans hE) B hB

theorem compProd_restrict_apply_prod {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {κ : Kernel Ω X}
    [IsMarkovKernel κ] {E A : Set Ω} (hE : MeasurableSet E) (hA : MeasurableSet A) {B : Set X}
    (hB : MeasurableSet B) : (P.restrict E ⊗ₘ κ) (A ×ˢ B) = (P ⊗ₘ κ) ((A ∩ E) ×ˢ B) := by
  rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod (hA.inter hE) hB,
    Measure.restrict_restrict hA]

/-- The joint law on a rectangle inside `E` only depends on the kernel on `E`. -/
theorem compProd_prod_congr {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {κ₁ κ₂ : Kernel Ω X}
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] {E A : Set Ω} (hA : MeasurableSet A) (hAE : A ⊆ E)
    (h : ∀ ω ∈ E, κ₁ ω = κ₂ ω) {B : Set X} (hB : MeasurableSet B) :
    (P ⊗ₘ κ₁) (A ×ˢ B) = (P ⊗ₘ κ₂) (A ×ˢ B) := by
  rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hA hB]
  exact setLIntegral_congr_fun hA fun ω hω => by rw [h ω (hAE hω)]

theorem compProd_map_apply_prod {Y : Type*} [MeasurableSpace Y] {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {κ : Kernel Ω X} [IsMarkovKernel κ] {f : X → Y} (hf : Measurable f) {A : Set Ω}
    (hA : MeasurableSet A) {B : Set Y} (hB : MeasurableSet B) :
    (P ⊗ₘ κ.map f) (A ×ˢ B) = (P ⊗ₘ κ) (A ×ˢ (f ⁻¹' B)) := by
  have : IsMarkovKernel (κ.map f) := Kernel.IsMarkovKernel.map κ hf
  rw [Measure.compProd_apply_prod hA hB, Measure.compProd_apply_prod hA (hf hB)]
  exact setLIntegral_congr_fun hA fun ω _ => by rw [Kernel.map_apply' _ hf _ hB]

/-- Agreement passes to images under a measurable map. -/
theorem RectAgree.map {Y : Type*} [MeasurableSpace Y] {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ)
    {P : Measure Ω} [IsFiniteMeasure P] {E : Set Ω} {κ₁ κ₂ : Kernel Ω X} [IsMarkovKernel κ₁]
    [IsMarkovKernel κ₂] (h : RectAgree 𝒜 P E κ₁ κ₂) {f : X → Y} (hf : Measurable f) :
    RectAgree 𝒜 P E (κ₁.map f) (κ₂.map f) := fun A hA hAE B hB => by
  rw [compProd_map_apply_prod hf (h𝒜 A hA) hB, compProd_map_apply_prod hf (h𝒜 A hA) hB]
  exact h A hA hAE _ (hf hB)

open Function in
/-- Agreement on every piece of a finite measurable partition gives agreement on the union. -/
theorem RectAgree.of_partition {ι : Type*} [Fintype ι] {𝒜 mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ)
    {P : Measure Ω} [IsFiniteMeasure P] {E : Set Ω} {κ₁ κ₂ : Kernel Ω X} [IsMarkovKernel κ₁]
    [IsMarkovKernel κ₂] {S : Ω → ι} (hS : ∀ i, MeasurableSet[𝒜] {ω | S ω = i})
    (h : ∀ i, RectAgree 𝒜 P (E ∩ {ω | S ω = i}) κ₁ κ₂) : RectAgree 𝒜 P E κ₁ κ₂ := by
  intro A hA hAE B hB
  have hA' : MeasurableSet A := h𝒜 A hA
  have hpiece : ∀ i, MeasurableSet (A ∩ {ω | S ω = i}) := fun i => hA'.inter (h𝒜 _ (hS i))
  have hdisj : Pairwise (Disjoint on fun i => A ∩ {ω | S ω = i}) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω hi hj => hij ?_
    exact hi.2.symm.trans hj.2
  have hU : A = ⋃ i, A ∩ {ω | S ω = i} := by
    ext ω; simp
  have key : ∀ κ : Kernel Ω X, (P ⊗ₘ κ) (A ×ˢ B) = ∑ i, (P ⊗ₘ κ) ((A ∩ {ω | S ω = i}) ×ˢ B) := by
    intro κ
    conv_lhs => rw [hU, Set.iUnion_prod_const]
    rw [measure_iUnion (fun i j hij => by
        exact Set.disjoint_prod.2 (Or.inl (hdisj hij)))
      (fun i => (hpiece i).prod hB), tsum_fintype]
  rw [key, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact h i _ (hA.inter (hS i)) (fun ω hω => ⟨hAE hω.1, hω.2⟩) B hB

end RectAgree

/-! ### One stage on an event -/

section StageOn

variable {Ω : Type*}

/-- `exists_stage` on an event `E ∈ 𝒜`. -/
theorem exists_stage_on {𝒜 𝒜' mΩ : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ 𝒜') (h𝒜' : 𝒜' ≤ mΩ)
    (P : Measure Ω) [IsFiniteMeasure P] {E : Set Ω} (hE : MeasurableSet[𝒜] E)
    (η : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsMarkovKernel η]
    (hη : Measurable[𝒜] fun ω => η ω) (V : TopologicalSpace.Opens ℂ) (Q Q' : Kernel Ω (DistOn V))
    [IsMarkovKernel Q] [IsMarkovKernel Q'] (hηQ : RectAgree 𝒜 P E (η.map (restrictDist V)) Q)
    (hQQ' : RectAgree 𝒜 P E Q' Q) :
    ∃ η' : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η' ∧
      Measurable[𝒜'] (fun ω => η' ω) ∧ RectAgree 𝒜 P E η' η ∧
      RectAgree 𝒜' P E (η'.map (restrictDist V)) Q' := by
  have h𝒜m : 𝒜 ≤ mΩ := h𝒜.trans h𝒜'
  have hEm : MeasurableSet E := h𝒜m E hE
  have hr : Measurable (restrictDist V (D := upperHalfPlaneOpens)) := measurable_restrictDist V
  have : IsMarkovKernel (η.map (restrictDist V)) := Kernel.IsMarkovKernel.map η hr
  obtain ⟨η', hη', hη'm, hc, hd⟩ := exists_stage h𝒜 h𝒜' (P.restrict E) η hη V Q Q'
    (fun A hA B hB => by
      rw [compProd_restrict_apply_prod hEm (h𝒜m A hA) hB,
        compProd_restrict_apply_prod hEm (h𝒜m A hA) hB]
      exact hηQ _ (hA.inter hE) inter_subset_right B hB)
    (fun A hA B hB => by
      rw [compProd_restrict_apply_prod hEm (h𝒜m A hA) hB,
        compProd_restrict_apply_prod hEm (h𝒜m A hA) hB]
      exact hQQ' _ (hA.inter hE) inter_subset_right B hB)
  have : IsMarkovKernel (η'.map (restrictDist V)) := Kernel.IsMarkovKernel.map η' hr
  refine ⟨η', hη', hη'm, fun A hA hAE B hB => ?_, fun A hA hAE B hB => ?_⟩
  · have h := hc A hA B hB
    rw [compProd_restrict_apply_prod hEm (h𝒜m A hA) hB,
      compProd_restrict_apply_prod hEm (h𝒜m A hA) hB, inter_eq_left.2 hAE] at h
    exact h
  · have h := hd A hA B hB
    rw [compProd_restrict_apply_prod hEm (h𝒜' A hA) hB,
      compProd_restrict_apply_prod hEm (h𝒜' A hA) hB, inter_eq_left.2 hAE] at h
    exact h

end StageOn

/-! ### The chain -/

section Chain

variable {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem RectAgree.of_empty {X : Type*} [MeasurableSpace X] {𝒜 mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {E : Set Ω} (hE : E = ∅) (κ₁ κ₂ : Kernel Ω X) : RectAgree 𝒜 P E κ₁ κ₂ := by
  intro A _ hAE B _
  have : A = ∅ := Set.subset_eq_empty hAE hE
  subst this
  simp

/-- **The chain of stages** (Astra pp. 5–6, without the resampling of `P_V h`). See the module docstring. -/
theorem exists_chain {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (V : Finset ι → TopologicalSpace.Opens ℂ) (hVH : ∀ T, V T ≤ upperHalfPlaneOpens)
    (hV : ∀ T T', T ⊆ T' → V T ≤ V T')
    (𝒜 : ℕ → MeasurableSpace Ω) (h𝒜 : Monotone 𝒜) (h𝒜m : ∀ k, 𝒜 k ≤ mΩ)
    (R : ℕ → Ω → Finset ι) (hR0 : ∀ T, MeasurableSet[𝒜 0] {ω | R 0 ω = T})
    (hR : ∀ k T, MeasurableSet[𝒜 k] {ω | R (k + 1) ω = T})
    (hRmono : ∀ k ω, R (k + 1) ω ⊆ R k ω)
    (Q : ℕ → (T : Finset ι) → Kernel Ω (DistOn (V T))) [hQ : ∀ k T, IsMarkovKernel (Q k T)]
    (η₀ : Kernel Ω (DistOn upperHalfPlaneOpens)) [IsMarkovKernel η₀]
    (hη₀ : Measurable[𝒜 0] fun ω => η₀ ω)
    (h0 : ∀ T, RectAgree (𝒜 0) P {ω | R 0 ω = T} (η₀.map (restrictDist (V T))) (Q 0 T))
    (hmart : ∀ k T, RectAgree (𝒜 k) P {ω | R (k + 1) ω = T} (Q (k + 1) T) (Q k T))
    (hcons : ∀ k T T', T ⊆ T' → RectAgree (𝒜 k) P ({ω | R k ω = T'} ∩ {ω | R (k + 1) ω = T})
      ((Q k T').map (restrictDist (V T))) (Q k T)) (N : ℕ) :
    ∃ η : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η ∧
      Measurable[𝒜 N] (fun ω => η ω) ∧ RectAgree (𝒜 0) P univ η η₀ ∧
      ∀ k ≤ N, ∀ T, RectAgree (𝒜 k) P {ω | R k ω = T} (η.map (restrictDist (V T))) (Q k T) := by
  have hr : ∀ T, Measurable (restrictDist (V T) (D := upperHalfPlaneOpens)) := fun T =>
    measurable_restrictDist (V T)
  have hRk : ∀ k T, MeasurableSet[𝒜 k] {ω | R k ω = T} := by
    intro k T
    cases k with
    | zero => exact hR0 T
    | succ k => exact h𝒜 (Nat.le_succ k) _ (hR k T)
  induction N with
  | zero =>
    refine ⟨η₀, inferInstance, hη₀, fun A _ _ B _ => rfl, fun k hk T => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.1 hk
    exact h0 T
  | succ N ih =>
    obtain ⟨η, hηM, hηm, hmarg, hinv⟩ := ih
    -- the restriction of `η` to the next region
    have hηQ : ∀ T, RectAgree (𝒜 N) P {ω | R (N + 1) ω = T}
        (η.map (restrictDist (V T))) (Q N T) := by
      intro T
      have : IsMarkovKernel (η.map (restrictDist (V T))) := Kernel.IsMarkovKernel.map η (hr T)
      refine RectAgree.of_partition (h𝒜m N) (S := R N) (hRk N) fun T' => ?_
      · by_cases hTT' : T ⊆ T'
        · have hm : (η.map (restrictDist (V T))) =
              (η.map (restrictDist (V T'))).map (restrictDist (V T) (D := V T')) := by
            rw [← Kernel.map_comp_right _ (hr T') (measurable_restrictDist (V T))]
            congr 1
            funext h
            exact (restrictDist_restrictDist (hV T T' hTT') (hVH T') h).symm
          have : IsMarkovKernel (η.map (restrictDist (V T'))) := Kernel.IsMarkovKernel.map η (hr T')
          rw [hm]
          refine (((hinv N le_rfl T').map (h𝒜m N) (measurable_restrictDist (V T))).mono le_rfl
            fun ω hω => hω.2).trans ((hcons N T T' hTT').mono le_rfl fun ω hω => ⟨hω.2, hω.1⟩)
        · refine RectAgree.of_empty ?_ _ _
          ext ω
          simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro h1 h2
          exact hTT' (h1 ▸ h2 ▸ hRmono N ω)
    -- one stage on each event `{R (N+1) = T}`
    have hstage : ∀ T, ∃ η' : Kernel Ω (DistOn upperHalfPlaneOpens), IsMarkovKernel η' ∧
        Measurable[𝒜 (N + 1)] (fun ω => η' ω) ∧ RectAgree (𝒜 N) P {ω | R (N + 1) ω = T} η' η ∧
        RectAgree (𝒜 (N + 1)) P {ω | R (N + 1) ω = T} (η'.map (restrictDist (V T))) (Q (N + 1) T) :=
      fun T => exists_stage_on (h𝒜 (Nat.le_succ N)) (h𝒜m (N + 1)) P (hR N T) η hηm (V T) (Q N T)
        (Q (N + 1) T) (hηQ T) (hmart N T)
    choose η' hη'M hη'm hc hd using hstage
    have hRm : ∀ T, MeasurableSet {ω | R (N + 1) ω = T} := fun T => h𝒜m N _ (hR N T)
    set η₁ := kernelGlue (R (N + 1)) hRm η' with hη₁
    have hη₁M : IsMarkovKernel η₁ := isMarkovKernel_kernelGlue _ _ _
    have hη₁m : Measurable[𝒜 (N + 1)] fun ω => η₁ ω :=
      measurable_glue (fun T => h𝒜 (Nat.le_succ N) _ (hR N T)) hη'm
    have hon : ∀ T, ∀ ω ∈ {ω | R (N + 1) ω = T}, η₁ ω = η' T ω := fun T ω hω => by
      rw [hη₁, kernelGlue_apply]
      rw [mem_ofPred_eq] at hω
      rw [hω]
    have key : RectAgree (𝒜 N) P univ η₁ η := by
      refine RectAgree.of_partition (h𝒜m N) (S := R (N + 1)) (hR N) fun T => ?_
      intro A hA hAE B hB
      rw [compProd_prod_congr (h𝒜m N A hA) (fun ω hω => (hAE hω).2) (hon T) hB]
      exact hc T A hA (fun ω hω => (hAE hω).2) B hB
    refine ⟨η₁, hη₁M, hη₁m, (key.mono (h𝒜 (Nat.zero_le N)) subset_rfl).trans hmarg,
      fun k hk T => ?_⟩
    have : IsMarkovKernel (η₁.map (restrictDist (V T))) := Kernel.IsMarkovKernel.map η₁ (hr T)
    have : IsMarkovKernel (η.map (restrictDist (V T))) := Kernel.IsMarkovKernel.map η (hr T)
    rcases Nat.lt_or_ge k (N + 1) with hkN | hkN
    · have hkN' : k ≤ N := Nat.lt_succ_iff.1 hkN
      exact ((key.map (h𝒜m N) (hr T)).mono (h𝒜 hkN') (subset_univ _)).trans (hinv k hkN' T)
    · obtain rfl : k = N + 1 := le_antisymm hk hkN
      intro A hA hAE B hB
      have : IsMarkovKernel ((η' T).map (restrictDist (V T))) :=
        Kernel.IsMarkovKernel.map (η' T) (hr T)
      have hcg : (P ⊗ₘ η₁.map (restrictDist (V T))) (A ×ˢ B) =
          (P ⊗ₘ (η' T).map (restrictDist (V T))) (A ×ˢ B) :=
        compProd_prod_congr (h𝒜m (N + 1) A hA) hAE (fun ω hω => by
          simp only [Kernel.map_apply _ (hr T), hon T ω hω]) hB
      rw [hcg]
      exact hd T A hA hAE B hB

end Chain

end Coupling

end InteractingSLE
