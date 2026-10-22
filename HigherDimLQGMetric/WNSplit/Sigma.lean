import HigherDimLFPP.Field.FiniteRange

/-!
# Noise σ-algebras of space-scale regions and their independence (packet S5a, D-WN′ (3))

Source: MA3 Details (a) **D-WN′** (`planning/audits/MA3-sections-5-6.md`), the σ-algebras
`𝒢(S, b) = σ(W(f) : f ∈ L², supp f ⊆ (0, b) × S)` and (3) (orthogonal kernels give independent
jointly Gaussian families); blueprint `prop:wn-split` (3).

* `wnsNoiseSpace S b`: the `f ∈ L²(ℝ × ℝ^d)` vanishing a.e. outside `(0, b) × S`;
* `wnsSigma0 W S b = σ(W(f) : f ∈ wnsNoiseSpace S b)`;
* `wnsComplete P m`: the sets of the ambient σ-algebra that are `P`-a.e. equal to a set of `m`
  (the completion of `m ≤` ambient by null sets of the ambient σ-algebra). Random variables that are
  a.e. equal to `m`-measurable ones are measurable for it (`measurable_wnsComplete_of_ae_eq`), and
  completion preserves mutual independence (`iIndep_wnsComplete`);
* `wnsSigma P W S b = wnsComplete P (wnsSigma0 W S b)`, the σ-algebra `𝒢(S, b)` of D-WN′;
* `iIndep_wnsSigma`: for pairwise disjoint `S i`, the `𝒢(S i, b)` are independent (the
  noise spaces are mutually orthogonal, and orthogonal white-noise families are independent,
  HigherDimLFPP's `IsWhiteNoise.iIndepFun_of_ae_eq`).

The completion by null sets is needed because the pairings of the fine field are only almost
surely equal to the white-noise integrals of their kernels.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- the σ-algebras below are used through `MeasurableSet[...]`, not as instances
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

variable {d : ℕ} {Ω : Type*}

/-! ## Completion by null sets

The sub-σ-algebra `m` is bound *before* the ambient σ-algebra `mΩ`, so that instance resolution
(for `P`, `MeasurableSet`, `=ᵐ[P]`) picks the ambient one; `m` is always passed explicitly. -/

/-- The sets of the ambient σ-algebra that are `P`-a.e. equal to a set of `m`. -/
def wnsComplete (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) :
    MeasurableSpace Ω where
  MeasurableSet' A := MeasurableSet A ∧ ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B
  measurableSet_empty := ⟨MeasurableSet.empty, ∅, @MeasurableSet.empty Ω m, EventuallyEqSet.rfl⟩
  measurableSet_compl A hA := by
    obtain ⟨hA1, B, hB, hAB⟩ := hA
    exact ⟨hA1.compl, Bᶜ, hB.compl, hAB.compl⟩
  measurableSet_iUnion f hf := by
    choose hf1 B hB hfB using hf
    exact ⟨MeasurableSet.iUnion hf1, ⋃ i, B i, MeasurableSet.iUnion hB,
      EventuallyEqSet.countable_iUnion hfB⟩

theorem measurableSet_wnsComplete_iff {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {A : Set Ω} :
    MeasurableSet[wnsComplete m P] A ↔ MeasurableSet A ∧ ∃ B, MeasurableSet[m] B ∧ A =ᵐ[P] B :=
  Iff.rfl

theorem wnsComplete_le (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} (P : Measure Ω) :
    wnsComplete m P ≤ mΩ :=
  fun _ hA => hA.1

theorem le_wnsComplete {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (hm : m ≤ mΩ) : m ≤ wnsComplete m P :=
  fun A hA => ⟨hm A hA, A, hA, EventuallyEqSet.rfl⟩

/-- A real random variable a.e. equal to an `m`-measurable one is `wnsComplete m P`-measurable. -/
theorem measurable_wnsComplete_of_ae_eq {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable[m] Y)
    (hXY : X =ᵐ[P] Y) : Measurable[wnsComplete m P] X := fun B hB =>
  ⟨hX hB, Y ⁻¹' B, hY hB, hXY.preimage B⟩

/-- **Completion preserves independence**. -/
theorem iIndep_wnsComplete {ι : Type*} {m : ι → MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (h : iIndep m P) : iIndep (fun i => wnsComplete (m i) P) P := by
  rw [iIndep_iff] at h ⊢
  intro s f hf
  choose! B hB hfB using fun i hi => (hf i hi).2
  have e1 : (⋂ i ∈ s, f i) =ᵐ[P] ⋂ i ∈ s, B i :=
    EventuallyEqSet.biInter s.finite_toSet fun i hi => hfB i hi
  rw [measure_congr e1, h s fun i hi => hB i hi]
  exact Finset.prod_congr rfl fun i hi => (measure_congr (hfB i hi)).symm

/-! ## Noise σ-algebras -/

variable [mΩ : MeasurableSpace Ω]

/-- The white-noise vectors supported (a.e.) in `(0, b) × S`. -/
def wnsNoiseSpace (S : Set (Rd d)) (b : ℝ) : Set (WN d) :=
  {f | ∀ᵐ p ∂(volume : Measure (ℝ × Rd d)), p ∉ Ioo 0 b ×ˢ S → (f : ℝ × Rd d → ℝ) p = 0}

/-- `σ(W(f) : f ∈ L², supp f ⊆ (0, b) × S)`. -/
def wnsSigma0 (W : WN d → Ω → ℝ) (S : Set (Rd d)) (b : ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (f : wnsNoiseSpace S b) => W f ω) MeasurableSpace.pi

/-- The noise σ-algebra `𝒢(S, b)` of D-WN′, completed by null sets. -/
def wnsSigma (P : Measure Ω) (W : WN d → Ω → ℝ) (S : Set (Rd d)) (b : ℝ) : MeasurableSpace Ω :=
  wnsComplete (wnsSigma0 W S b) P

omit mΩ in
theorem measurable_wnsSigma0 (W : WN d → Ω → ℝ) {S : Set (Rd d)} {b : ℝ} {f : WN d}
    (hf : f ∈ wnsNoiseSpace S b) : Measurable[wnsSigma0 W S b] (W f) := by
  have h : Measurable[wnsSigma0 W S b] (fun ω (g : wnsNoiseSpace S b) => W g ω) :=
    comap_measurable _
  exact (measurable_pi_apply (⟨f, hf⟩ : wnsNoiseSpace S b)).comp h

theorem wnsSigma0_le {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : HigherDimLFPP.IsWhiteNoise P W)
    (S : Set (Rd d)) (b : ℝ) : wnsSigma0 W S b ≤ mΩ :=
  (measurable_pi_iff.2 fun f : wnsNoiseSpace S b => hW.measurable f.1).comap_le

/-- A real random variable a.e. equal to `W(f)` with `f` supported in `(0, b) × S` is
`𝒢(S, b)`-measurable. -/
theorem measurable_wnsSigma_of_ae_eq {P : Measure Ω} {W : WN d → Ω → ℝ} {S : Set (Rd d)} {b : ℝ}
    {X : Ω → ℝ} (hX : Measurable X) {f : WN d} (hf : f ∈ wnsNoiseSpace S b)
    (hXf : X =ᵐ[P] W f) : Measurable[wnsSigma P W S b] X :=
  measurable_wnsComplete_of_ae_eq hX (measurable_wnsSigma0 W hf) hXf

/-- Vectors supported in `(0, b) × S` and `(0, b) × S'` are orthogonal if `S ∩ S' = ∅`. -/
theorem inner_eq_zero_of_mem_wnsNoiseSpace {S S' : Set (Rd d)} (hSS' : Disjoint S S') {b : ℝ}
    {f f' : WN d} (hf : f ∈ wnsNoiseSpace S b) (hf' : f' ∈ wnsNoiseSpace S' b) : ⟪f, f'⟫ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hf, hf'] with p hp hp'
  simp only [Pi.zero_apply]
  by_cases h : p ∈ Ioo 0 b ×ˢ S
  · have h' : p ∉ Ioo 0 b ×ˢ S' := fun h' =>
      Set.disjoint_left.1 hSS' (mem_prod.1 h).2 (mem_prod.1 h').2
    rw [hp' h', inner_zero_right]
  · rw [hp h, inner_zero_left]

/-- **Independence over disjoint regions** (D-WN′ (3)): for pairwise disjoint `S i`, the noise
σ-algebras `𝒢(S i, b)` are mutually independent. -/
theorem iIndep_wnsSigma {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : HigherDimLFPP.IsWhiteNoise P W)
    {ι : Type*} {S : ι → Set (Rd d)} (hS : Pairwise fun i j => Disjoint (S i) (S j)) (b : ℝ) :
    iIndep (fun i => wnsSigma P W (S i) b) P := by
  refine iIndep_wnsComplete ?_
  have h := hW.iIndepFun_of_ae_eq (fun i (f : wnsNoiseSpace (S i) b) => (f : WN d))
    (fun i j hij f f' => inner_eq_zero_of_mem_wnsNoiseSpace (hS hij) f.2 f'.2)
    (X := fun i (f : wnsNoiseSpace (S i) b) => W f) (fun _ _ => EventuallyEq.rfl)
  exact h.iIndep

end HigherDimLQGMetric
