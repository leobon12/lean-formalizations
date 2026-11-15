/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513Tree
import InteractingSLE.Spec.Exist.Uniq
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous versions from countably many measurable prefix evaluations

The measurable decoder uses Lusin--Souslin on continuous paths on `[0,1]`.
It preserves measurability for the field sigma algebra, without using an ambient
measurable null-set completion. Countably many endpoint agreements can then be
made exact simultaneously.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology

namespace InteractingSLE.Sec5.Prop513TreeExtract

abbrev UnitTime := Icc (0 : ℝ) 1

def ratTime (q : ℚ) : UnitTime := projIcc 0 1 (by norm_num) (q : ℝ)

theorem dense_ratTime : DenseRange ratTime :=
  (projIcc_surjective (by norm_num : (0 : ℝ) ≤ 1)).denseRange.comp
    Rat.denseRange_cast continuous_projIcc

def samples (f : C(UnitTime, ℂ)) : ℚ → ℂ := fun q => f (ratTime q)

theorem measurable_samples : Measurable samples :=
  measurable_pi_iff.2 fun q => ContinuousMap.measurable_eval (ratTime q)

theorem samples_injective : Function.Injective samples := by
  intro f g he
  apply ContinuousMap.coe_injective
  exact f.continuous.ext_on dense_ratTime g.continuous (by
    rintro _ ⟨q, rfl⟩
    exact congrFun he q)

theorem exists_decoder : ∃ R : (ℚ → ℂ) → C(UnitTime, ℂ), Measurable R ∧
    ∀ f, R (samples f) = f := by
  obtain ⟨R, hR, he⟩ := Exist.exists_measurable_leftInverse_of_injOn
    measurable_samples MeasurableSet.univ samples_injective.injOn
  exact ⟨R, hR, fun f => he f (mem_univ _)⟩

def decoder : (ℚ → ℂ) → C(UnitTime, ℂ) := exists_decoder.choose

theorem measurable_decoder : Measurable decoder := exists_decoder.choose_spec.1

theorem decoder_samples (f : C(UnitTime, ℂ)) : decoder (samples f) = f :=
  exists_decoder.choose_spec.2 f

/-- A coordinate-measurable path on a deterministic compact interval has a
coordinate-measurable, everywhere continuous version, whenever it is a.e.
continuous there. This works for an arbitrary sub-sigma-algebra `𝒢`. -/
theorem exists_continuous_prefix_version {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝒢 : MeasurableSpace Ω} {η : Ω → ℝ → ℂ}
    (hm : ∀ t, Measurable[𝒢] fun ω => η ω t) {T : ℝ} (hT : 0 < T)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (η ω) (Icc 0 T)) :
    ∃ ξ : Ω → ℝ → ℂ, (∀ t, Measurable[𝒢] fun ω => ξ ω t) ∧
      (∀ ω, Continuous (ξ ω)) ∧ ∀ᵐ ω ∂P, EqOn (ξ ω) (η ω) (Icc 0 T) := by
  let code : Ω → ℚ → ℂ := fun ω q => η ω (T * (ratTime q : ℝ))
  have hcode : Measurable[𝒢] code := measurable_pi_iff.2 fun q => hm _
  let ξ : Ω → ℝ → ℂ := fun ω t => decoder (code ω) (projIcc 0 1 (by norm_num) (t / T))
  refine ⟨ξ, fun t => ?_, fun ω => ?_, ?_⟩
  · exact (ContinuousMap.measurable_eval _).comp (measurable_decoder.comp hcode)
  · exact (decoder (code ω)).continuous.comp
      (continuous_projIcc.comp (continuous_id.div_const T))
  · filter_upwards [hc] with ω hω
    let f : C(UnitTime, ℂ) := ⟨fun s => η ω (T * (s : ℝ)),
      hω.comp_continuous (continuous_const.mul continuous_subtype_val)
        (fun s => ⟨mul_nonneg hT.le s.2.1, by nlinarith only [s.2.2, hT]⟩)⟩
    have he : code ω = samples f := rfl
    intro t ht
    change decoder (code ω) (projIcc 0 1 (by norm_num) (t / T)) = η ω t
    rw [he, decoder_samples]
    have ht' : t / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩
    change η ω (T * (projIcc 0 1 (by norm_num) (t / T) : ℝ)) = η ω t
    rw [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) ht']
    congr 1
    exact mul_div_cancel₀ _ hT.ne'

/-- Countably many continuous prefix versions can be chosen with exact common
node endpoints, while keeping measurability for the original sigma algebra. -/
theorem exists_tree_version {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝒢 : MeasurableSpace Ω} {η : ℕ → Ω → ℝ → ℂ}
    (hm : ∀ n t, Measurable[𝒢] fun ω => η n ω t)
    (τ : ℕ → ℝ) (d : ℕ → ℕ → ℕ) (hτ : ∀ n, 0 < τ n)
    (hmono : ∀ n m, τ n ≤ τ (d n m))
    (hc : ∀ᵐ ω ∂P, ∀ n, ContinuousOn (η n ω) (Icc 0 (τ n)))
    (hr : ∀ᵐ ω ∂P, ∀ n m, η (d n m) ω (τ n) = η n ω (τ n)) :
    ∃ ξ : ℕ → Ω → ℝ → ℂ, (∀ n t, Measurable[𝒢] fun ω => ξ n ω t) ∧
      (∀ n ω, Continuous (ξ n ω)) ∧
      (∀ n m ω, ξ (d n m) ω (τ n) = extremeAngleTreeNode ξ τ n ω) ∧
      ∀ᵐ ω ∂P, ∀ n, EqOn (ξ n ω) (η n ω) (Icc 0 (τ n)) := by
  classical
  have hex := fun n => @exists_continuous_prefix_version Ω mΩ P 𝒢 (η n)
    (hm n) (τ n) (hτ n) (hc.mono fun _ hω => hω n)
  choose ξ hξm hξc hξe using hex
  have he : ∀ᵐ ω ∂P, ∀ n, EqOn (ξ n ω) (η n ω) (Icc 0 (τ n)) :=
    ae_all_iff.2 hξe
  let G : Set Ω := {ω | ∀ n m, ξ (d n m) ω (τ n) = ξ n ω (τ n)}
  have hGm : MeasurableSet[𝒢] G := by
    simp only [G, ofPred_forall]
    exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun m =>
      measurableSet_eq_fun (hξm (d n m) (τ n)) (hξm n (τ n))
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [he, hr] with ω heω hrω n m
    rw [heω (d n m) ⟨(hτ n).le, hmono n m⟩, heω n ⟨(hτ n).le, le_rfl⟩]
    exact hrω n m
  refine ⟨fun n ω t => if ω ∈ G then ξ n ω t else 0,
    fun n t => Measurable.ite hGm (hξm n t) measurable_const, ?_, ?_, ?_⟩
  · intro n ω
    by_cases hω : ω ∈ G
    · simpa only [hω, ite_true] using hξc n ω
    · simpa only [hω, ite_false] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · intro n m ω
    change (if ω ∈ G then ξ (d n m) ω (τ n) else 0) =
      if ω ∈ G then ξ n ω (τ n) else 0
    by_cases hω : ω ∈ G
    · simp only [hω, ite_true]
      exact hω n m
    · simp only [hω, ite_false]
  · filter_upwards [hG, he] with ω hω heω n t ht
    simp only [hω, ite_true]
    exact heω n ht

end InteractingSLE.Sec5.Prop513TreeExtract
