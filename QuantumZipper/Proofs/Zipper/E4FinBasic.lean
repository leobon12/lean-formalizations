import QuantumZipper.Proofs.Zipper.E4LimOpen

/-!
# E4-MC, generic tools: closure of `GoodEq` under the monotone-class operations

`handoff/E4.md`, item E4 (monotone class). `GoodEq` (identity of iterated lower integrals
together with the a.e.-measurability of both integrands, `E4LimMC`) is closed under
multiplication by constants, sums and monotone suprema (`goodEq_const_mul`, `goodEq_add`,
`goodEq_iSup`; the a.e.-measurability makes `lintegral_const_mul''`, `lintegral_add_left'`,
`lintegral_iSup'` applicable). Hence (`goodEq_induction`, via mathlib's
`Measurable.ennreal_induction`) it extends from indicators of measurable sets to all measurable
`ℝ≥0∞`-valued test functions. `indMeas_facts`: the pointwise Dynkin facts for integrands
`1_A · a · μ(C)` with `μ` a probability measure. `cylE`, `cylN`: finite-dimensional cylinder
generators (π-systems generating the product σ-algebras, `Fin.append`).

Standard measure theory: Dynkin's π-λ theorem and the monotone-class/"standard machine"
extension (Kallenberg, *Foundations of Modern Probability*, 2nd ed., Thm 1.1 and Lemma 1.11 /
Billingsley, *Probability and Measure*, Thm 3.2); own bookkeeping of the a.e.-measurability.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace E4Grid

section Closure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Ω → Measure ℝ} {S : Set ℝ}

theorem goodEq_const_mul (c : ℝ≥0∞) {F G : Ω → ℝ → ℝ≥0∞} (h : GoodEq P ν S F G) :
    GoodEq P ν S (fun ω x => c * F ω x) (fun ω x => c * G ω x) := by
  obtain ⟨he, hLo, hLi, hRo, hRi⟩ := h
  have hL : ∀ᵐ ω ∂P, ∫⁻ x in S, c * F ω x ∂ν ω = c * ∫⁻ x in S, F ω x ∂ν ω := by
    filter_upwards [hLi] with ω h
    exact lintegral_const_mul'' c h
  have hR : ∀ᵐ ω ∂P, ∫⁻ x in S, c * G ω x ∂ν ω = c * ∫⁻ x in S, G ω x ∂ν ω := by
    filter_upwards [hRi] with ω h
    exact lintegral_const_mul'' c h
  refine ⟨?_, (hLo.const_mul c).congr (hL.mono fun ω h => h.symm), ?_,
    (hRo.const_mul c).congr (hR.mono fun ω h => h.symm), ?_⟩
  · rw [lintegral_congr_ae hL, lintegral_congr_ae hR, lintegral_const_mul'' c hLo,
      lintegral_const_mul'' c hRo, he]
  · filter_upwards [hLi] with ω h
    exact h.const_mul c
  · filter_upwards [hRi] with ω h
    exact h.const_mul c

theorem goodEq_add {F₁ G₁ F₂ G₂ : Ω → ℝ → ℝ≥0∞} (h₁ : GoodEq P ν S F₁ G₁)
    (h₂ : GoodEq P ν S F₂ G₂) :
    GoodEq P ν S (fun ω x => F₁ ω x + F₂ ω x) (fun ω x => G₁ ω x + G₂ ω x) := by
  obtain ⟨he₁, hLo₁, hLi₁, hRo₁, hRi₁⟩ := h₁
  obtain ⟨he₂, hLo₂, hLi₂, hRo₂, hRi₂⟩ := h₂
  have hL : ∀ᵐ ω ∂P, ∫⁻ x in S, (F₁ ω x + F₂ ω x) ∂ν ω =
      ∫⁻ x in S, F₁ ω x ∂ν ω + ∫⁻ x in S, F₂ ω x ∂ν ω := by
    filter_upwards [hLi₁] with ω h
    exact lintegral_add_left' h _
  have hR : ∀ᵐ ω ∂P, ∫⁻ x in S, (G₁ ω x + G₂ ω x) ∂ν ω =
      ∫⁻ x in S, G₁ ω x ∂ν ω + ∫⁻ x in S, G₂ ω x ∂ν ω := by
    filter_upwards [hRi₁] with ω h
    exact lintegral_add_left' h _
  refine ⟨?_, (hLo₁.add hLo₂).congr (hL.mono fun ω h => h.symm), ?_,
    (hRo₁.add hRo₂).congr (hR.mono fun ω h => h.symm), ?_⟩
  · rw [lintegral_congr_ae hL, lintegral_congr_ae hR, lintegral_add_left' hLo₁,
      lintegral_add_left' hRo₁, he₁, he₂]
  · filter_upwards [hLi₁, hLi₂] with ω h h'
    exact h.add h'
  · filter_upwards [hRi₁, hRi₂] with ω h h'
    exact h.add h'

theorem goodEq_iSup {F G : ℕ → Ω → ℝ → ℝ≥0∞} (hFm : ∀ ω x, Monotone fun n => F n ω x)
    (hGm : ∀ ω x, Monotone fun n => G n ω x) (h : ∀ n, GoodEq P ν S (F n) (G n)) :
    GoodEq P ν S (fun ω x => ⨆ n, F n ω x) (fun ω x => ⨆ n, G n ω x) := by
  have hLi := ae_all_iff.2 fun n => (h n).2.2.1
  have hRi := ae_all_iff.2 fun n => (h n).2.2.2.2
  have hL : ∀ᵐ ω ∂P, ∫⁻ x in S, ⨆ n, F n ω x ∂ν ω = ⨆ n, ∫⁻ x in S, F n ω x ∂ν ω := by
    filter_upwards [hLi] with ω hm
    exact lintegral_iSup' hm (Eventually.of_forall fun x => hFm ω x)
  have hR : ∀ᵐ ω ∂P, ∫⁻ x in S, ⨆ n, G n ω x ∂ν ω = ⨆ n, ∫⁻ x in S, G n ω x ∂ν ω := by
    filter_upwards [hRi] with ω hm
    exact lintegral_iSup' hm (Eventually.of_forall fun x => hGm ω x)
  refine ⟨?_, (AEMeasurable.iSup fun n => (h n).2.1).congr (hL.mono fun ω h => h.symm), ?_,
    (AEMeasurable.iSup fun n => (h n).2.2.2.1).congr (hR.mono fun ω h => h.symm), ?_⟩
  · rw [lintegral_congr_ae hL, lintegral_congr_ae hR,
      lintegral_iSup' (fun n => (h n).2.1) (Eventually.of_forall fun ω a b hab =>
        lintegral_mono fun x => hFm ω x hab),
      lintegral_iSup' (fun n => (h n).2.2.2.1) (Eventually.of_forall fun ω a b hab =>
        lintegral_mono fun x => hGm ω x hab)]
    exact iSup_congr fun n => (h n).1
  · filter_upwards [hLi] with ω hm
    exact AEMeasurable.iSup hm
  · filter_upwards [hRi] with ω hm
    exact AEMeasurable.iSup hm

/-- **Standard machine for `GoodEq`.** If `F, G` are linear and monotone-continuous in the
test function `f` (pointwise in `(ω, x)`), `GoodEq` for all indicators of measurable sets gives
`GoodEq` for every measurable `f`. -/
theorem goodEq_induction {β : Type*} [MeasurableSpace β] (F G : (β → ℝ≥0∞) → Ω → ℝ → ℝ≥0∞)
    (hFc : ∀ (c : ℝ≥0∞) s, MeasurableSet s →
      F (s.indicator fun _ => c) = fun ω x => c * F (s.indicator 1) ω x)
    (hGc : ∀ (c : ℝ≥0∞) s, MeasurableSet s →
      G (s.indicator fun _ => c) = fun ω x => c * G (s.indicator 1) ω x)
    (hFa : ∀ f g, Measurable f → Measurable g → F (f + g) = fun ω x => F f ω x + F g ω x)
    (hGa : ∀ f g, Measurable f → Measurable g → G (f + g) = fun ω x => G f ω x + G g ω x)
    (hFs : ∀ f : ℕ → β → ℝ≥0∞, (∀ n, Measurable (f n)) → Monotone f →
      F (fun y => ⨆ n, f n y) = fun ω x => ⨆ n, F (f n) ω x)
    (hGs : ∀ f : ℕ → β → ℝ≥0∞, (∀ n, Measurable (f n)) → Monotone f →
      G (fun y => ⨆ n, f n y) = fun ω x => ⨆ n, G (f n) ω x)
    (hFmono : ∀ f g, Measurable f → Measurable g → f ≤ g → ∀ ω x, F f ω x ≤ F g ω x)
    (hGmono : ∀ f g, Measurable f → Measurable g → f ≤ g → ∀ ω x, G f ω x ≤ G g ω x)
    (hbasic : ∀ s, MeasurableSet s → GoodEq P ν S (F (s.indicator 1)) (G (s.indicator 1))) :
    ∀ f, Measurable f → GoodEq P ν S (F f) (G f) := fun f hf =>
  Measurable.ennreal_induction (motive := fun f => GoodEq P ν S (F f) (G f))
    (fun c s hs => by rw [hFc c s hs, hGc c s hs]; exact goodEq_const_mul c (hbasic s hs))
    (fun f g _ hf hg h₁ h₂ => by rw [hFa f g hf hg, hGa f g hf hg]; exact goodEq_add h₁ h₂)
    (fun f hf hmono h => by
      rw [hFs f hf hmono, hGs f hf hmono]
      exact goodEq_iSup (fun ω x a b hab => hFmono _ _ (hf a) (hf b) (hmono hab) ω x)
        (fun ω x a b hab => hGmono _ _ (hf a) (hf b) (hmono hab) ω x) h) hf

end Closure

/-- Pointwise Dynkin facts for `C ↦ 1_s(x) · a(x) · μ_x(C)`, `μ_x` probability measures. -/
theorem indMeas_facts {E : Type*} [MeasurableSpace E] (s : Set ℝ) (a : ℝ → ℝ≥0∞)
    (μ : ℝ → Measure E) [∀ x, IsProbabilityMeasure (μ x)] (x : ℝ) (ha : a x ≤ 1) :
    (s.indicator (fun x => a x * μ x ∅) x = 0) ∧
    (∀ C : Set E, s.indicator (fun x => a x * μ x C) x ≤
      s.indicator (fun x => a x * μ x univ) x) ∧
    (∀ C : Set E, MeasurableSet C → s.indicator (fun x => a x * μ x Cᶜ) x =
      s.indicator (fun x => a x * μ x univ) x - s.indicator (fun x => a x * μ x C) x) ∧
    (∀ f : ℕ → Set E, Pairwise (Function.onFun Disjoint f) → (∀ i, MeasurableSet (f i)) →
      s.indicator (fun x => a x * μ x (⋃ i, f i)) x =
        ∑' i, s.indicator (fun x => a x * μ x (f i)) x) ∧
    (∀ C : Set E, s.indicator (fun x => a x * μ x C) x ≤ 1) := by
  refine ⟨by simp, fun C => ?_, fun C hC => ?_, fun f hd hm => ?_, fun C => ?_⟩
  · by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      gcongr
      exact subset_univ C
    · simp [indicator_of_notMem hx]
  · by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      rw [prob_compl_eq_one_sub hC, measure_univ,
        ENNReal.mul_sub fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top ha]
    · simp [indicator_of_notMem hx]
  · by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      rw [measure_iUnion hd hm, ENNReal.tsum_mul_left]
    · simp [indicator_of_notMem hx]
  · by_cases hx : x ∈ s
    · simp only [indicator_of_mem hx]
      exact mul_le_one' ha prob_le_one
    · simp [indicator_of_notMem hx]

/-! ## Cylinder generators -/

/-- Configuration space of `Ψ`: `(x, (V, W⁰))`. -/
abbrev CfgE := ℝ × (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ)

/-- Finite-dimensional projection of a configuration. -/
def cylE {m : ℕ} (u : Fin m → ℝ≥0) (p : CfgE) : ℝ × (Fin m → ℝ) × (Fin m → ℝ) :=
  (p.1, fun j => p.2.1 (u j), fun j => p.2.2 (u j))

theorem measurable_cylE {m : ℕ} (u : Fin m → ℝ≥0) : Measurable (cylE u) :=
  measurable_fst.prodMk ((measurable_pi_iff.2 fun j =>
    (measurable_pi_apply (u j)).comp (measurable_fst.comp measurable_snd)).prodMk
    (measurable_pi_iff.2 fun j =>
      (measurable_pi_apply (u j)).comp (measurable_snd.comp measurable_snd)))

/-- Generators of the σ-algebra of `CfgE`: Borel finite-dimensional cylinders. -/
def genE : Set (Set CfgE) :=
  {D | ∃ (m : ℕ) (u : Fin m → ℝ≥0) (S : Set (ℝ × (Fin m → ℝ) × (Fin m → ℝ))),
    MeasurableSet S ∧ D = cylE u ⁻¹' S}

theorem isPiSystem_genE : IsPiSystem genE := by
  rintro _ ⟨m, u, S, hS, rfl⟩ _ ⟨m', u', S', hS', rfl⟩ _
  refine ⟨m + m', Fin.append u u',
    (fun q => (q.1, fun j => q.2.1 (Fin.castAdd m' j), fun j => q.2.2 (Fin.castAdd m' j))) ⁻¹' S ∩
    (fun q => (q.1, fun j => q.2.1 (Fin.natAdd m j), fun j => q.2.2 (Fin.natAdd m j))) ⁻¹' S',
    (measurable_fst.prodMk ((measurable_pi_iff.2 fun j =>
      (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_iff.2 fun j =>
        (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)))) hS |>.inter
    ((measurable_fst.prodMk ((measurable_pi_iff.2 fun j =>
      (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_pi_iff.2 fun j =>
        (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)))) hS'), ?_⟩
  ext p
  simp [cylE, Fin.append_left, Fin.append_right]

theorem generate_genE : (inferInstance : MeasurableSpace CfgE) =
    MeasurableSpace.generateFrom genE := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · refine sup_le (MeasurableSpace.comap_le_iff_le_map.2 fun A hA => ?_)
      (MeasurableSpace.comap_le_iff_le_map.2 (sup_le
        (MeasurableSpace.comap_le_iff_le_map.2 (iSup_le fun t =>
          MeasurableSpace.comap_le_iff_le_map.2 fun A hA => ?_))
        (MeasurableSpace.comap_le_iff_le_map.2 (iSup_le fun t =>
          MeasurableSpace.comap_le_iff_le_map.2 fun A hA => ?_))))
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨0, Fin.elim0, A ×ˢ univ, hA.prod MeasurableSet.univ, by ext p; simp [cylE]⟩
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨1, fun _ => t, {q | q.2.1 0 ∈ A}, measurable_snd.fst.eval hA, by ext p; simp [cylE]⟩
    · exact MeasurableSpace.measurableSet_generateFrom
        ⟨1, fun _ => t, {q | q.2.2 0 ∈ A}, measurable_snd.snd.eval hA, by ext p; simp [cylE]⟩
  · rintro _ ⟨m, u, S, hS, rfl⟩
    exact measurable_cylE u hS

/-- Finite-dimensional projection of a coordinate sequence. -/
def cylN {m : ℕ} (I : Fin m → ℕ) (c : ℕ → ℝ) : Fin m → ℝ := fun j => c (I j)

/-- Generators of the σ-algebra of `ℕ → ℝ`: open finite-dimensional cylinders. -/
def genN : Set (Set (ℕ → ℝ)) :=
  {C | ∃ (m : ℕ) (I : Fin m → ℕ) (O : Set (Fin m → ℝ)), IsOpen O ∧ C = cylN I ⁻¹' O}

theorem isPiSystem_genN : IsPiSystem genN := by
  rintro _ ⟨m, I, O, hO, rfl⟩ _ ⟨m', I', O', hO', rfl⟩ _
  refine ⟨m + m', Fin.append I I',
    (fun v j => v (Fin.castAdd m' j)) ⁻¹' O ∩ (fun v j => v (Fin.natAdd m j)) ⁻¹' O',
    (hO.preimage (continuous_pi fun j => continuous_apply _)).inter
      (hO'.preimage (continuous_pi fun j => continuous_apply _)), ?_⟩
  ext c
  simp [cylN, Fin.append_left, Fin.append_right]
  exact Iff.rfl

theorem generate_genN : (inferInstance : MeasurableSpace (ℕ → ℝ)) =
    MeasurableSpace.generateFrom genN := by
  refine le_antisymm (iSup_le fun n => MeasurableSpace.comap_le_iff_le_map.2 ?_)
    (MeasurableSpace.generateFrom_le ?_)
  · rw [BorelSpace.measurable_eq (α := ℝ)]
    refine MeasurableSpace.generateFrom_le fun s hs => ?_
    exact MeasurableSpace.measurableSet_generateFrom
      ⟨1, fun _ => n, {v | v 0 ∈ s}, (show IsOpen s from hs).preimage (continuous_apply 0), by ext c; simp [cylN]⟩
  · rintro _ ⟨m, I, O, hO, rfl⟩
    exact (measurable_pi_iff.2 fun j => measurable_pi_apply (I j)) hO.measurableSet

end E4Grid
end QuantumZipper
