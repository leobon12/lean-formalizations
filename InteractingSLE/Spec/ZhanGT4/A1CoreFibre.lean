/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CanonFiber
import InteractingSLE.Spec.Sec7.Lemma71DUsual

/-!
# A.1's rectangle core: conditional Girsanov through the joint density `M(s, τ)`

Packet PROVE-A1CORE. Source: Astra, *Follow-up 5* §1.3 (`source/external/AstraIG1/ig1_followup5.txt` L197–L222,
R73): "On each protected rectangle, that construction supplies a continuous joint density `M(s, t)` … with axis values
one and the two coordinate martingale identities. … If `τ` is bounded by the large-curve protection time, optional
sampling gives the density `M(s, τ)`. For bounded stopped-record tests, its identity is
`E_coupled[F G] = E_{P₁ ⊗ P₂}[M(s, τ) F G]`, `G ∈ 𝓕²_τ` (1.7), with `F` measurable from the protected small record
through `s`. Conditional Girsanov gives the image SDE."

The coupling lives on a product `X × Y` of the two curves' path spaces (curve `1` on `X`, curve `2` on `Y`), with
marginal laws `P₁`, `P₂`; the rectangle law is a density identity for `μ` against `P₁ ⊗ P₂` on the σ-algebra of
the two stopped records. This file proves, generically:

* **`lintegral_eq_of_rect`**: a density identity on the rectangles `A ×ˢ B` (`A ∈ 𝓐`, `B ∈ 𝓑`) extends to every
  `𝓐 ⊗ 𝓑`-measurable test function (Dynkin);
* **`rect_of_optional`**: (1.7) — the rectangle identity with the exit-time density `M(s, S₂)` and the optional
  sampling identity `∫_B M(s, S₂) dP₂ = ∫_B M(s, τ) dP₂` (`B ∈ 𝓕²_τ`) give the rectangle identity with `M(s, τ)`;
* **`isStoppedBM_of_density`**: conditional Girsanov, assembled — if for `P₂`-almost every frozen curve-`2` sample
  `y` the stopped Wald exponentials of the noise are martingales under the curve-`1` law tilted by the density
  `D(·, y)` (the frozen-hull rectangle law), then the noise is a Brownian motion stopped at the cap for the filtration
  `𝓔 ∨ 𝓖` under the coupling, `𝓔` the pulled-back curve-`2` σ-algebra (`𝓕²_τ`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Core

open A1Canon

/-! ### The stopped Wald exponential at time `0` and after the cap -/

section StopExp

variable {Ω : Type*}

theorem stopExp_zero {N : ℝ≥0 → Ω → ℝ} (hN0 : ∀ ω, N 0 ω = 0) (a : ℝ) (S : Ω → ℝ≥0) (ω : Ω) :
    stopExp a N S 0 ω = 1 := by
  simp [stopExp, hN0]

theorem stopExp_eq_of_le (a : ℝ) (N : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) {ω : Ω}
    (h : S ω ≤ s) : stopExp a N S t ω = stopExp a N S s ω := by
  simp only [stopExp, min_eq_right h, min_eq_right (h.trans hst)]

theorem stopExp_pos (a : ℝ) (N : ℝ≥0 → Ω → ℝ) (S : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : 0 < stopExp a N S t ω :=
  Real.exp_pos _

end StopExp

/-! ### Density identities on product σ-algebras -/

section Rect

variable {X Y : Type*} {𝓐 : MeasurableSpace X} {𝓑 𝓑' : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- **A density identity on rectangles extends to the product σ-algebra** (Dynkin): if
`μ (A ×ˢ B) = ∫_{A ×ˢ B} D d(P₁ ⊗ P₂)` for `A ∈ 𝓐`, `B ∈ 𝓑`, then `∫ f dμ = ∫ f D d(P₁ ⊗ P₂)` for every
`𝓐 ⊗ 𝓑`-measurable `f ≥ 0`. -/
theorem lintegral_eq_of_rect {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] (h𝓐 : 𝓐 ≤ mX)
    (h𝓑 : 𝓑 ≤ mY) {D : X × Y → ℝ≥0∞} (hD : Measurable D)
    (hrect : ∀ A B, MeasurableSet[𝓐] A → MeasurableSet[𝓑] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D z ∂(P₁.prod P₂))
    {f : X × Y → ℝ≥0∞} (hf : Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] f) :
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D z ∂(P₁.prod P₂) := by
  have hle : @Prod.instMeasurableSpace X Y 𝓐 𝓑 ≤ @Prod.instMeasurableSpace X Y mX mY :=
    sup_le_sup (MeasurableSpace.comap_mono h𝓐) (MeasurableSpace.comap_mono h𝓑)
  set ν : Measure (X × Y) := (P₁.prod P₂).withDensity D with hν
  have hν_rect : ∀ A B, MeasurableSet[𝓐] A → MeasurableSet[𝓑] B → μ (A ×ˢ B) = ν (A ×ˢ B) := by
    intro A B hA hB
    rw [hν, withDensity_apply _ ((h𝓐 A hA).prod (h𝓑 B hB)), hrect A B hA hB]
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    have h := hν_rect univ univ (@MeasurableSet.univ _ 𝓐) (@MeasurableSet.univ _ 𝓑)
    rw [univ_prod_univ] at h
    rw [← h]
    exact measure_lt_top μ univ
  -- the two trimmed measures agree on the generating rectangles
  have htrim : μ.trim hle = ν.trim hle := by
    have hgen := @generateFrom_prod X Y 𝓐 𝓑
    have := isFiniteMeasure_trim (μ := μ) hle
    refine ext_of_generate_finite (μ := μ.trim hle) (ν := ν.trim hle) _ hgen.symm
      (@isPiSystem_prod X Y 𝓐 𝓑) ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      rw [trim_measurableSet_eq hle (@MeasurableSet.prod _ _ 𝓐 𝓑 _ _ hA hB),
        trim_measurableSet_eq hle (@MeasurableSet.prod _ _ 𝓐 𝓑 _ _ hA hB)]
      exact hν_rect A B hA hB
    · rw [trim_measurableSet_eq hle (@MeasurableSet.univ _ (@Prod.instMeasurableSpace X Y 𝓐 𝓑)),
        trim_measurableSet_eq hle (@MeasurableSet.univ _ (@Prod.instMeasurableSpace X Y 𝓐 𝓑))]
      have h := hν_rect univ univ (@MeasurableSet.univ _ 𝓐) (@MeasurableSet.univ _ 𝓑)
      rwa [univ_prod_univ] at h
  rw [← lintegral_trim hle hf, htrim, lintegral_trim hle hf, hν,
    lintegral_withDensity_eq_lintegral_mul _ hD (hf.mono hle le_rfl)]
  refine lintegral_congr fun z => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

/-- **(1.7): optional sampling in the second coordinate.** A rectangle identity with the density `D₀` (`M(s, S₂)`) on
`𝓐 × 𝓑`, and the identity `∫_B D₀(x, ·) dP₂ = ∫_B D(x, ·) dP₂` for `P₁`-almost every `x` and every `B` of a smaller
σ-algebra `𝓑'` (`𝓕²_τ`, optional sampling of `t ↦ M(s, t)` at `τ`), give the rectangle identity with `D`
(`M(s, τ)`) on `𝓐 × 𝓑'`. -/
theorem rect_of_optional {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} (h𝓑' : 𝓑' ≤ 𝓑) (h𝓑 : 𝓑 ≤ mY) {D₀ D : X × Y → ℝ≥0∞} (hD₀ : Measurable D₀)
    (hD : Measurable D)
    (hrect : ∀ A B, MeasurableSet[𝓐] A → MeasurableSet[𝓑] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ z ∂(P₁.prod P₂))
    (hopt : ∀ᵐ x ∂P₁, ∀ B, MeasurableSet[𝓑'] B → ∫⁻ y in B, D₀ (x, y) ∂P₂ = ∫⁻ y in B, D (x, y) ∂P₂) :
    ∀ A B, MeasurableSet[𝓐] A → MeasurableSet[𝓑'] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D z ∂(P₁.prod P₂) := by
  intro A B hA hB
  have hBm : MeasurableSet[mY] B := h𝓑 B (h𝓑' B hB)
  rw [hrect A B hA (h𝓑' B hB), ← Measure.prod_restrict,
    lintegral_prod _ hD₀.aemeasurable, lintegral_prod _ hD.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hopt] with x hx
  exact hx B hB

end Rect

/-! ### Conditional Girsanov, assembled through the density -/

section Density

variable {X Y : Type*} {𝓐 : MeasurableSpace X} {𝓑 𝓔 : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- The pulled-back curve-`2` σ-algebra `snd⁻¹ 𝓔` is a sub-σ-algebra. -/
theorem comap_snd_le (h𝓔 : 𝓔 ≤ mY) :
    𝓔.comap Prod.snd ≤ (inferInstance : MeasurableSpace (X × Y)) :=
  (MeasurableSpace.comap_mono h𝓔).trans le_sup_right

omit mX mY in
/-- The section at `y` of `snd⁻¹ B ∩ C` is the section of `C` when `y ∈ B`, and empty otherwise. -/
theorem indicator_snd_inter {B : Set Y} {C : Set (X × Y)} (f : X × Y → ℝ≥0∞) (x : X) (y : Y) :
    (Prod.snd ⁻¹' B ∩ C).indicator f (x, y) = B.indicator (fun _ => (1 : ℝ≥0∞)) y * C.indicator f (x, y) := by
  by_cases hy : y ∈ B
  · simp only [Set.indicator_of_mem hy, one_mul]
    by_cases hC : (x, y) ∈ C
    · rw [Set.indicator_of_mem (show (x, y) ∈ Prod.snd ⁻¹' B ∩ C from ⟨hy, hC⟩), Set.indicator_of_mem hC]
    · rw [Set.indicator_of_notMem (fun h => hC h.2), Set.indicator_of_notMem hC]
  · simp only [Set.indicator_of_notMem hy, zero_mul]
    exact Set.indicator_of_notMem (fun h => hy h.1) _

/-- **Conditional Girsanov, assembled** (follow-up 5 §1.3, (1.7)): let the coupling `μ` of `X × Y` satisfy the density
identity `∫ f dμ = ∫ f D d(P₁ ⊗ P₂)` for `𝓐 ⊗ 𝓑`-measurable `f ≥ 0` (the rectangle law at the stop `τ`, `D = M(S₁, τ)`),
and let the noise `N` be continuous, `𝓖`-adapted, from `0`, with an `𝓖`-stopping time cap `S`. If its stopped Wald
exponentials are `𝓐 ⊗ 𝓑`-measurable, the sets `snd⁻¹ B ∩ A ∩ {s < S}` (`B ∈ 𝓔`, `A ∈ 𝓖_s`) are in `𝓐 ⊗ 𝓑`,
and for
`P₂`-almost every frozen curve-`2` sample `y` the stopped Wald exponentials have the martingale property under the
curve-`1` law tilted by `D(·, y)` (the frozen-hull rectangle law, "conditional Girsanov"), then `N` is a Brownian
motion stopped at `S` for `snd⁻¹ 𝓔 ∨ 𝓖` under `μ`. -/
theorem isStoppedBM_of_density {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] {D : X × Y → ℝ≥0∞} (hD : Measurable D)
    (hdens : ∀ f : X × Y → ℝ≥0∞, Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] f →
      ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D z ∂(P₁.prod P₂))
    (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) (h𝓔 : 𝓔 ≤ mY)
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    (hNc : ∀ z, Continuous (N · z)) (hN0 : ∀ z, N 0 z = 0) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime 𝓖 fun z => (S z : WithTop ℝ≥0))
    (hX : ∀ (a : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (stopExp a N S t))
    (hC : ∀ (s : ℝ≥0) (B : Set Y) (A : Set (X × Y)), MeasurableSet[𝓔] B → MeasurableSet[𝓖 s] A →
      MeasurableSet[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}))
    (hfib : ∀ᵐ y ∂P₂, ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₁ =
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₁) :
    IsStoppedBM μ (supFiltration (𝓔.comap Prod.snd) (comap_snd_le h𝓔) 𝓖) N S := by
  have h𝓡 : @Prod.instMeasurableSpace X Y 𝓐 𝓑 ≤ @Prod.instMeasurableSpace X Y mX mY :=
    sup_le_sup (MeasurableSpace.comap_mono h𝓐) (MeasurableSpace.comap_mono h𝓑)
  intro a
  set 𝓗 := supFiltration (𝓔.comap Prod.snd) (comap_snd_le h𝓔) 𝓖 with h𝓗
  have hadp : StronglyAdapted 𝓗 (stopExp a N S) := fun t =>
    ((stronglyAdapted_stopExp hNc hNa hS a) t).mono (le_supFiltration _ 𝓖 t)
  have hpos : ∀ t z, 0 ≤ stopExp a N S t z := fun t z => (stopExp_pos a N S t z).le
  have hmeas : ∀ t, Measurable (stopExp a N S t) := fun t => ((hadp t).measurable).mono (𝓗.le t) le_rfl
  have hSm : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {z | s < S z} := by
    intro s
    have h := hS s
    have e : {z | s < S z} = {z | (S z : WithTop ℝ≥0) ≤ s}ᶜ := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [e]
    exact h.compl
  -- the basic identity on `snd⁻¹ B ∩ A`, in lower integrals
  have key : ∀ s t : ℝ≥0, s ≤ t → ∀ (B : Set Y) (A : Set (X × Y)), MeasurableSet[𝓔] B → MeasurableSet[𝓖 s] A →
      ∫⁻ z in Prod.snd ⁻¹' B ∩ A, ENNReal.ofReal (stopExp a N S t z) ∂μ =
        ∫⁻ z in Prod.snd ⁻¹' B ∩ A, ENNReal.ofReal (stopExp a N S s z) ∂μ := by
    intro s t hst B A hB hA
    have hBm : MeasurableSet (Prod.snd ⁻¹' B : Set (X × Y)) := measurable_snd (h𝓔 B hB)
    have hAm : MeasurableSet A := 𝓖.le s A hA
    have hSm' : MeasurableSet {z | s < S z} := 𝓖.le s _ (hSm s)
    have hsplit : Prod.snd ⁻¹' B ∩ A =
        (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}) ∪ (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}ᶜ) :=
      (Set.inter_union_compl _ _).symm
    have hdisj : Disjoint (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}) (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}ᶜ) :=
      Disjoint.mono Set.inter_subset_right Set.inter_subset_right disjoint_compl_right
    rw [hsplit, lintegral_union ((hBm.inter hAm).inter hSm'.compl) hdisj,
      lintegral_union ((hBm.inter hAm).inter hSm'.compl) hdisj]
    congr 1
    · -- before the cap: the density identity and the fibres
      have hR := hC s B A hB hA
      rw [← lintegral_indicator (h𝓡 _ hR), ← lintegral_indicator (h𝓡 _ hR),
        hdens _ (((hX a t).ennreal_ofReal).indicator hR), hdens _ (((hX a s).ennreal_ofReal).indicator hR)]
      have hm : ∀ u, Measurable fun z => (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}).indicator
          (fun z => ENNReal.ofReal (stopExp a N S u z)) z * D z := fun u =>
        (((hmeas u).ennreal_ofReal).indicator (h𝓡 _ hR)).mul hD
      rw [lintegral_prod_symm _ (hm t).aemeasurable, lintegral_prod_symm _ (hm s).aemeasurable]
      refine lintegral_congr_ae ?_
      filter_upwards [hfib] with y hy
      have hA' : MeasurableSet[𝓖 s] (A ∩ {z | s < S z}) := hA.inter (hSm s)
      have e : ∀ u : ℝ≥0, ∀ x : X,
          (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}).indicator (fun z => ENNReal.ofReal (stopExp a N S u z)) (x, y) *
            D (x, y) = B.indicator (fun _ => (1 : ℝ≥0∞)) y *
              ((A ∩ {z | s < S z}).indicator (fun z => ENNReal.ofReal (stopExp a N S u z)) (x, y) * D (x, y)) := by
        intro u x
        rw [Set.inter_assoc, indicator_snd_inter, mul_assoc]
      simp_rw [e]
      rw [lintegral_const_mul' _ _ (by by_cases hy : y ∈ B <;> simp [hy]),
        lintegral_const_mul' _ _ (by by_cases hy : y ∈ B <;> simp [hy]), hy a s t hst _ hA']
    · -- after the cap: the stopped exponentials agree
      refine setLIntegral_congr_fun ((hBm.inter hAm).inter hSm'.compl) fun z hz => ?_
      have hz' : S z ≤ s := not_lt.1 hz.2
      rw [stopExp_eq_of_le a N S hst hz']
  -- integrability
  have hint : ∀ t, Integrable (stopExp a N S t) μ := by
    intro t
    refine ⟨(hmeas t).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hpos t))]
    have h := key 0 t (zero_le : (0 : ℝ≥0) ≤ t) univ univ (@MeasurableSet.univ _ 𝓔) (@MeasurableSet.univ _ (𝓖 0))
    simp only [Set.preimage_univ, Set.univ_inter, Measure.restrict_univ] at h
    rw [h]
    simp only [stopExp_zero hN0, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact measure_lt_top μ univ
  refine ⟨hadp, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓗.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun C hC _ => ?_) (hadp s).aestronglyMeasurable).symm
  set π : Set (Set (X × Y)) := {C | ∃ (B : Set Y) (A : Set (X × Y)), MeasurableSet[𝓔] B ∧
    MeasurableSet[𝓖 s] A ∧ C = Prod.snd ⁻¹' B ∩ A} with hπdef
  have hgen : 𝓗 s = MeasurableSpace.generateFrom π := by
    rw [h𝓗, supFiltration_apply]
    refine le_antisymm (sup_le (fun E hE => ?_) (fun A hA => ?_)) (MeasurableSpace.generateFrom_le ?_)
    · obtain ⟨B, hB, rfl⟩ := hE
      exact MeasurableSpace.measurableSet_generateFrom ⟨B, univ, hB, MeasurableSet.univ, (inter_univ _).symm⟩
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨univ, A, MeasurableSet.univ, hA, by rw [Set.preimage_univ, Set.univ_inter]⟩
    · rintro _ ⟨B, A, hB, hA, rfl⟩
      exact ((le_sup_left : 𝓔.comap Prod.snd ≤ 𝓔.comap Prod.snd ⊔ 𝓖 s) _ ⟨B, hB, rfl⟩).inter
        ((le_sup_right : 𝓖 s ≤ 𝓔.comap Prod.snd ⊔ 𝓖 s) _ hA)
  have hπ : IsPiSystem π := by
    rintro _ ⟨B, A, hB, hA, rfl⟩ _ ⟨B', A', hB', hA', rfl⟩ _
    exact ⟨B ∩ B', A ∩ A', hB.inter hB', hA.inter hA', by
      rw [Set.preimage_inter]; exact Set.inter_inter_inter_comm _ _ _ _⟩
  have huniv : univ ∈ π :=
    ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, by rw [Set.preimage_univ, Set.univ_inter]⟩
  refine (setIntegral_eq_of_isPiSystem (hint t) (hint s) (𝓗.le s) hgen hπ huniv ?_ hC).symm
  rintro _ ⟨B, A, hB, hA, rfl⟩
  have hBA : MeasurableSet (Prod.snd ⁻¹' B ∩ A : Set (X × Y)) :=
    (measurable_snd (h𝓔 B hB)).inter (𝓖.le s A hA)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hpos t)) (hmeas t).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hpos s)) (hmeas s).aestronglyMeasurable,
    key s t hst B A hB hA]

end Density

/-! ### Fibres over the first factor (the mirrored form) -/

section DensityFst

variable {X Y : Type*} {𝓐 𝓔 : MeasurableSpace X} {𝓑 : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- The pulled-back curve-`1` σ-algebra `fst⁻¹ 𝓔` is a sub-σ-algebra. -/
theorem comap_fst_le (h𝓔 : 𝓔 ≤ mX) :
    𝓔.comap Prod.fst ≤ (inferInstance : MeasurableSpace (X × Y)) :=
  (MeasurableSpace.comap_mono h𝓔).trans le_sup_left

omit mX mY in
theorem indicator_fst_inter {B : Set X} {C : Set (X × Y)} (f : X × Y → ℝ≥0∞) (x : X) (y : Y) :
    (Prod.fst ⁻¹' B ∩ C).indicator f (x, y) = B.indicator (fun _ => (1 : ℝ≥0∞)) x * C.indicator f (x, y) := by
  by_cases hx : x ∈ B
  · simp only [Set.indicator_of_mem hx, one_mul]
    by_cases hC : (x, y) ∈ C
    · rw [Set.indicator_of_mem (show (x, y) ∈ Prod.fst ⁻¹' B ∩ C from ⟨hx, hC⟩), Set.indicator_of_mem hC]
    · rw [Set.indicator_of_notMem (fun h => hC h.2), Set.indicator_of_notMem hC]
  · simp only [Set.indicator_of_notMem hx, zero_mul]
    exact Set.indicator_of_notMem (fun h => hx h.1) _

/-- **Conditional Girsanov, assembled, with the conditioning curve on the first factor**: the mirror of
`isStoppedBM_of_density` (fibres over `x ∈ X`, the image curve on `Y`). -/
theorem isStoppedBM_of_density_fst {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] {D : X × Y → ℝ≥0∞} (hD : Measurable D)
    (hdens : ∀ f : X × Y → ℝ≥0∞, Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] f →
      ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D z ∂(P₁.prod P₂))
    (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) (h𝓔 : 𝓔 ≤ mX)
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    (hNc : ∀ z, Continuous (N · z)) (hN0 : ∀ z, N 0 z = 0) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime 𝓖 fun z => (S z : WithTop ℝ≥0))
    (hX : ∀ (a : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (stopExp a N S t))
    (hC : ∀ (s : ℝ≥0) (B : Set X) (A : Set (X × Y)), MeasurableSet[𝓔] B → MeasurableSet[𝓖 s] A →
      MeasurableSet[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}))
    (hfib : ∀ᵐ x ∂P₁, ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₂ =
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₂) :
    IsStoppedBM μ (supFiltration (𝓔.comap Prod.fst) (comap_fst_le h𝓔) 𝓖) N S := by
  have h𝓡 : @Prod.instMeasurableSpace X Y 𝓐 𝓑 ≤ @Prod.instMeasurableSpace X Y mX mY :=
    sup_le_sup (MeasurableSpace.comap_mono h𝓐) (MeasurableSpace.comap_mono h𝓑)
  intro a
  set 𝓗 := supFiltration (𝓔.comap Prod.fst) (comap_fst_le h𝓔) 𝓖 with h𝓗
  have hadp : StronglyAdapted 𝓗 (stopExp a N S) := fun t =>
    ((stronglyAdapted_stopExp hNc hNa hS a) t).mono (le_supFiltration _ 𝓖 t)
  have hpos : ∀ t z, 0 ≤ stopExp a N S t z := fun t z => (stopExp_pos a N S t z).le
  have hmeas : ∀ t, Measurable (stopExp a N S t) := fun t => ((hadp t).measurable).mono (𝓗.le t) le_rfl
  have hSm : ∀ s : ℝ≥0, MeasurableSet[𝓖 s] {z | s < S z} := by
    intro s
    have h := hS s
    have e : {z | s < S z} = {z | (S z : WithTop ℝ≥0) ≤ s}ᶜ := by
      ext z; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, WithTop.coe_le_coe, not_le]
    rw [e]
    exact h.compl
  have key : ∀ s t : ℝ≥0, s ≤ t → ∀ (B : Set X) (A : Set (X × Y)), MeasurableSet[𝓔] B → MeasurableSet[𝓖 s] A →
      ∫⁻ z in Prod.fst ⁻¹' B ∩ A, ENNReal.ofReal (stopExp a N S t z) ∂μ =
        ∫⁻ z in Prod.fst ⁻¹' B ∩ A, ENNReal.ofReal (stopExp a N S s z) ∂μ := by
    intro s t hst B A hB hA
    have hBm : MeasurableSet (Prod.fst ⁻¹' B : Set (X × Y)) := measurable_fst (h𝓔 B hB)
    have hAm : MeasurableSet A := 𝓖.le s A hA
    have hSm' : MeasurableSet {z | s < S z} := 𝓖.le s _ (hSm s)
    have hsplit : Prod.fst ⁻¹' B ∩ A =
        (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}) ∪ (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}ᶜ) :=
      (Set.inter_union_compl _ _).symm
    have hdisj : Disjoint (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}) (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}ᶜ) :=
      Disjoint.mono Set.inter_subset_right Set.inter_subset_right disjoint_compl_right
    rw [hsplit, lintegral_union ((hBm.inter hAm).inter hSm'.compl) hdisj,
      lintegral_union ((hBm.inter hAm).inter hSm'.compl) hdisj]
    congr 1
    · have hR := hC s B A hB hA
      rw [← lintegral_indicator (h𝓡 _ hR), ← lintegral_indicator (h𝓡 _ hR),
        hdens _ (((hX a t).ennreal_ofReal).indicator hR), hdens _ (((hX a s).ennreal_ofReal).indicator hR)]
      have hm : ∀ u, Measurable fun z => (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}).indicator
          (fun z => ENNReal.ofReal (stopExp a N S u z)) z * D z := fun u =>
        (((hmeas u).ennreal_ofReal).indicator (h𝓡 _ hR)).mul hD
      rw [lintegral_prod _ (hm t).aemeasurable, lintegral_prod _ (hm s).aemeasurable]
      refine lintegral_congr_ae ?_
      filter_upwards [hfib] with x hx
      have hA' : MeasurableSet[𝓖 s] (A ∩ {z | s < S z}) := hA.inter (hSm s)
      have e : ∀ u : ℝ≥0, ∀ y : Y,
          (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}).indicator (fun z => ENNReal.ofReal (stopExp a N S u z)) (x, y) *
            D (x, y) = B.indicator (fun _ => (1 : ℝ≥0∞)) x *
              ((A ∩ {z | s < S z}).indicator (fun z => ENNReal.ofReal (stopExp a N S u z)) (x, y) * D (x, y)) := by
        intro u y
        rw [Set.inter_assoc, indicator_fst_inter, mul_assoc]
      simp_rw [e]
      rw [lintegral_const_mul' _ _ (by by_cases hx : x ∈ B <;> simp [hx]),
        lintegral_const_mul' _ _ (by by_cases hx : x ∈ B <;> simp [hx]), hx a s t hst _ hA']
    · refine setLIntegral_congr_fun ((hBm.inter hAm).inter hSm'.compl) fun z hz => ?_
      have hz' : S z ≤ s := not_lt.1 hz.2
      rw [stopExp_eq_of_le a N S hst hz']
  have hint : ∀ t, Integrable (stopExp a N S t) μ := by
    intro t
    refine ⟨(hmeas t).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hpos t))]
    have h := key 0 t (zero_le : (0 : ℝ≥0) ≤ t) univ univ (@MeasurableSet.univ _ 𝓔)
      (@MeasurableSet.univ _ (𝓖 0))
    simp only [Set.preimage_univ, Set.univ_inter, Measure.restrict_univ] at h
    rw [h]
    simp only [stopExp_zero hN0, ENNReal.ofReal_one, lintegral_const, one_mul]
    exact measure_lt_top μ univ
  refine ⟨hadp, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓗.le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun C hC _ => ?_) (hadp s).aestronglyMeasurable).symm
  set π : Set (Set (X × Y)) := {C | ∃ (B : Set X) (A : Set (X × Y)), MeasurableSet[𝓔] B ∧
    MeasurableSet[𝓖 s] A ∧ C = Prod.fst ⁻¹' B ∩ A} with hπdef
  have hgen : 𝓗 s = MeasurableSpace.generateFrom π := by
    rw [h𝓗, supFiltration_apply]
    refine le_antisymm (sup_le (fun E hE => ?_) (fun A hA => ?_)) (MeasurableSpace.generateFrom_le ?_)
    · obtain ⟨B, hB, rfl⟩ := hE
      exact MeasurableSpace.measurableSet_generateFrom ⟨B, univ, hB, MeasurableSet.univ, (inter_univ _).symm⟩
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨univ, A, MeasurableSet.univ, hA, by rw [Set.preimage_univ, Set.univ_inter]⟩
    · rintro _ ⟨B, A, hB, hA, rfl⟩
      exact ((le_sup_left : 𝓔.comap Prod.fst ≤ 𝓔.comap Prod.fst ⊔ 𝓖 s) _ ⟨B, hB, rfl⟩).inter
        ((le_sup_right : 𝓖 s ≤ 𝓔.comap Prod.fst ⊔ 𝓖 s) _ hA)
  have hπ : IsPiSystem π := by
    rintro _ ⟨B, A, hB, hA, rfl⟩ _ ⟨B', A', hB', hA', rfl⟩ _
    exact ⟨B ∩ B', A ∩ A', hB.inter hB', hA.inter hA', by
      rw [Set.preimage_inter]; exact Set.inter_inter_inter_comm _ _ _ _⟩
  have huniv : univ ∈ π :=
    ⟨univ, univ, MeasurableSet.univ, MeasurableSet.univ, by rw [Set.preimage_univ, Set.univ_inter]⟩
  refine (setIntegral_eq_of_isPiSystem (hint t) (hint s) (𝓗.le s) hgen hπ huniv ?_ hC).symm
  rintro _ ⟨B, A, hB, hA, rfl⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hpos t)) (hmeas t).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hpos s)) (hmeas s).aestronglyMeasurable,
    key s t hst B A hB hA]

end DensityFst

/-! ### Null augmentation and the fibre identity from a tilted stopped Brownian motion -/

section Fibre

/-- A stopped Brownian motion stays one for the null augmentation of its filtration. -/
theorem IsStoppedBM.nullAugmented {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓗 : Filtration ℝ≥0 mΩ} {N : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0} (h : IsStoppedBM P 𝓗 N S) :
    IsStoppedBM P (Ito.nullAugmented 𝓗 P) N S := fun a =>
  ⟨fun t => ((h a).1 t).mono (Ito.le_nullAugmented 𝓗 P t), fun i j hij =>
    (Sec7.Lemma71D.condExp_nullAugmented_ae_eq ((h a).integrable j) i).trans ((h a).2 i j hij)⟩

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The filtration of the sections at `y` (curve-`1` events of the frozen curve-`2` sample `y`). -/
def sectionFiltration (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))) (y : Y) :
    Filtration ℝ≥0 mX where
  seq t := (𝓖 t).comap fun x => (x, y)
  mono' _ _ hst := MeasurableSpace.comap_mono (𝓖.mono hst)
  le' t := (MeasurableSpace.comap_mono (𝓖.le t)).trans (measurable_prodMk_right (y := y)).comap_le

/-- The filtration of the sections at `x` (curve-`2` events of the frozen curve-`1` sample `x`). -/
def sectionFiltrationFst (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))) (x : X) :
    Filtration ℝ≥0 mY where
  seq t := (𝓖 t).comap fun y => (x, y)
  mono' _ _ hst := MeasurableSpace.comap_mono (𝓖.mono hst)
  le' t := (MeasurableSpace.comap_mono (𝓖.le t)).trans (measurable_prodMk_left (x := x)).comap_le

/-- Lower integrals of a nonnegative martingale over the sets of its filtration are constant in time. -/
theorem setLIntegral_ofReal_eq_of_martingale {Ω : Type*} [mΩ : MeasurableSpace Ω] {Q : Measure Ω}
    [IsFiniteMeasure Q] {𝓗 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : Martingale X 𝓗 Q)
    (hpos : ∀ t ω, 0 ≤ X t ω) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓗 s] A) :
    ∫⁻ ω in A, ENNReal.ofReal (X t ω) ∂Q = ∫⁻ ω in A, ENNReal.ofReal (X s ω) ∂Q := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hX.integrable t).integrableOn (ae_of_all _ (hpos t)),
    ← ofReal_integral_eq_lintegral_ofReal (hX.integrable s).integrableOn (ae_of_all _ (hpos s)),
    hX.setIntegral_eq hst hA]

/-- **The fibre identity from the frozen-hull rectangle law** (conditional Girsanov at a frozen curve-`2` sample `y`):
if, under the curve-`1` law tilted by `D(·, y)`, the noise at `y` is a Brownian motion stopped at the cap for the
section filtration, then the fibre identity of `isStoppedBM_of_density` holds at `y`. -/
theorem fib_of_isStoppedBM_withDensity {P₁ : Measure X} {D : X × Y → ℝ≥0∞} (hD : Measurable D) {y : Y}
    [IsFiniteMeasure (P₁.withDensity fun x => D (x, y))]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    (h : IsStoppedBM (P₁.withDensity fun x => D (x, y)) (sectionFiltration 𝓖 y) (fun t x => N t (x, y))
      fun x => S (x, y)) :
    ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₁ =
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₁ := by
  intro a s t hst A hA
  have hAy : MeasurableSet[sectionFiltration 𝓖 y s] ((fun x => (x, y)) ⁻¹' A) := ⟨A, hA, rfl⟩
  have hAym : MeasurableSet ((fun x => (x, y)) ⁻¹' A) := (sectionFiltration 𝓖 y).le s _ hAy
  have hDy : Measurable fun x => D (x, y) := hD.comp measurable_prodMk_right
  have e : ∀ u : ℝ≥0, ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S u z)) (x, y) * D (x, y) ∂P₁ =
      ∫⁻ x in (fun x => (x, y)) ⁻¹' A, ENNReal.ofReal (stopExp a (fun t x => N t (x, y)) (fun x => S (x, y)) u x)
        ∂(P₁.withDensity fun x => D (x, y)) := by
    intro u
    rw [← lintegral_indicator hAym, lintegral_withDensity_eq_lintegral_mul _ hDy
      ((Measurable.ennreal_ofReal (((h a).stronglyAdapted u).measurable.mono
        ((sectionFiltration 𝓖 y).le u) le_rfl)).indicator hAym)]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
    rfl
  rw [e t, e s]
  exact setLIntegral_ofReal_eq_of_martingale (h a) (fun t x => (stopExp_pos a _ _ t x).le) hst hAy

/-- The mirror of `fib_of_isStoppedBM_withDensity` (fibres over a frozen curve-`1` sample `x`). -/
theorem fib_of_isStoppedBM_withDensity_fst {P₂ : Measure Y} {D : X × Y → ℝ≥0∞} (hD : Measurable D) {x : X}
    [IsFiniteMeasure (P₂.withDensity fun y => D (x, y))]
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    (h : IsStoppedBM (P₂.withDensity fun y => D (x, y)) (sectionFiltrationFst 𝓖 x) (fun t y => N t (x, y))
      fun y => S (x, y)) :
    ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₂ =
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₂ := by
  intro a s t hst A hA
  have hAx : MeasurableSet[sectionFiltrationFst 𝓖 x s] ((fun y => (x, y)) ⁻¹' A) := ⟨A, hA, rfl⟩
  have hAxm : MeasurableSet ((fun y => (x, y)) ⁻¹' A) := (sectionFiltrationFst 𝓖 x).le s _ hAx
  have hDx : Measurable fun y => D (x, y) := hD.comp measurable_prodMk_left
  have e : ∀ u : ℝ≥0, ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S u z)) (x, y) * D (x, y) ∂P₂ =
      ∫⁻ y in (fun y => (x, y)) ⁻¹' A, ENNReal.ofReal (stopExp a (fun t y => N t (x, y)) (fun y => S (x, y)) u y)
        ∂(P₂.withDensity fun y => D (x, y)) := by
    intro u
    rw [← lintegral_indicator hAxm, lintegral_withDensity_eq_lintegral_mul _ hDx
      ((Measurable.ennreal_ofReal (((h a).stronglyAdapted u).measurable.mono
        ((sectionFiltrationFst 𝓖 x).le u) le_rfl)).indicator hAxm)]
    refine lintegral_congr fun y => ?_
    simp only [Pi.mul_apply]
    rw [mul_comm]
    rfl
  rw [e t, e s]
  exact setLIntegral_ofReal_eq_of_martingale (h a) (fun t y => (stopExp_pos a _ _ t y).le) hst hAx

end Fibre

end InteractingSLE.ZhanGT4.A1Core
