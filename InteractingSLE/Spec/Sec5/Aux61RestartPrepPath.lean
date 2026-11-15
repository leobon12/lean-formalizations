import InteractingSLE.Spec.Sec5.Aux61RestartEvent
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Measurable simplicity and interiority of the retained own prefix

Packet PROVE-AUX61-R1. Compact-open path-space tests turn the geometric
prefix conditions into measurable events of the retained observations.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

/-- Injectivity of a continuous map on a compact metric domain is Borel.
Separated coincident pairs form a countable family of closed obstructions. -/
theorem measurableSet_injective_compact_path
    {X : Type*} [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] :
    MeasurableSet {f : C(X, ℂ) | Function.Injective f} := by
  have hclosed : ∀ n : ℕ, IsClosed {f : C(X, ℂ) | ∃ p : X × X,
      1 / ((n : ℝ) + 1) ≤ dist p.1 p.2 ∧ f p.1 = f p.2} := by
    intro n
    have h₁ : IsClosed {p : C(X, ℂ) × (X × X) |
        1 / ((n : ℝ) + 1) ≤ dist p.2.1 p.2.2} :=
      isClosed_le continuous_const (by fun_prop)
    have h₂ : IsClosed {p : C(X, ℂ) × (X × X) | p.1 p.2.1 = p.1 p.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hS := h₁.inter h₂
    have h := isClosedMap_fst_of_compactSpace _ hS
    convert h using 1
    ext f
    constructor
    · rintro ⟨p, hp⟩
      exact ⟨(f, p), hp, rfl⟩
    · rintro ⟨⟨_, p⟩, hp, rfl⟩
      exact ⟨p, hp⟩
  have heq : {f : C(X, ℂ) | Function.Injective f} = ⋂ n : ℕ,
      {f : C(X, ℂ) | ∃ p : X × X,
        1 / ((n : ℝ) + 1) ≤ dist p.1 p.2 ∧ f p.1 = f p.2}ᶜ := by
    ext f
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff]
    constructor
    · intro hf n ⟨⟨x, y⟩, hd, he⟩
      have hxy := hf he
      rw [hxy, dist_self] at hd
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact (not_le_of_gt hpos) hd
    · intro hf x y he
      by_contra hxy
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hxy)
      exact hf n ⟨(x, y), hn.le, he⟩
  rw [heq]
  exact MeasurableSet.iInter fun n => (hclosed n).measurableSet.compl

/-- Simplicity of a random compact own prefix is measurable from its prefix
evaluations. No future observations are required. -/
theorem measurableSet_injOn_prefix
    {Ω : Type*} [MeasurableSpace Ω] {η : Ω → ℝ → ℂ} {q : ℝ}
    (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 q))
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t) :
    MeasurableSet {ω | InjOn (η ω) (Icc (0 : ℝ) q)} := by
  let F : Ω → C(Icc (0 : ℝ) q, ℂ) := fun ω =>
    ⟨fun t => η ω t, (hc ω).domRestrict⟩
  have hFm : Measurable F := ContinuousMap.measurable_iff_eval.2 fun t => hm t t.2
  have h := measurableSet_injective_compact_path.preimage hFm
  convert h using 1
  ext ω
  change InjOn (η ω) (Icc (0 : ℝ) q) ↔ Function.Injective (F ω)
  constructor
  · intro hi x y hxy
    exact Subtype.ext (hi x.2 y.2 hxy)
  · intro hi x hx y hy hxy
    exact congrArg Subtype.val (@hi ⟨x, hx⟩ ⟨y, hy⟩ hxy)

/-- Interiority after the seed and through the retained time is measurable.
Each compact subinterval away from zero gives an open compact-open test. -/
theorem measurableSet_interior_prefix
    {Ω : Type*} [MeasurableSpace Ω] {η : Ω → ℝ → ℂ} {q : ℝ}
    (hc : ∀ ω, ContinuousOn (η ω) (Icc 0 q))
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t) :
    MeasurableSet {ω | MapsTo (η ω) (Ioc (0 : ℝ) q) H} := by
  let F : Ω → C(Icc (0 : ℝ) q, ℂ) := fun ω =>
    ⟨fun t => η ω t, (hc ω).domRestrict⟩
  have hFm : Measurable F := ContinuousMap.measurable_iff_eval.2 fun t => hm t t.2
  let K : ℕ → Set (Icc (0 : ℝ) q) := fun n => {t | 1 / ((n : ℝ) + 1) ≤ (t : ℝ)}
  have hK : ∀ n, IsCompact (K n) :=
    fun n => (isClosed_le continuous_const continuous_subtype_val).isCompact
  have heq : {ω | MapsTo (η ω) (Ioc (0 : ℝ) q) H} =
      ⋂ n : ℕ, F ⁻¹' {f : C(Icc (0 : ℝ) q, ℂ) | MapsTo f (K n) H} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_preimage]
    constructor
    · intro h n t ht
      exact h ⟨lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)) ht, t.2.2⟩
    · intro h t ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht.1
      exact h n (show (⟨t, ht.1.le, ht.2⟩ : Icc (0 : ℝ) q) ∈ K n from hn.le)
  rw [heq]
  exact MeasurableSet.iInter fun n =>
    (ContinuousMap.isOpen_setOfPred_mapsTo (hK n) QuantumZipper.isOpen_H).measurableSet.preimage hFm

end InteractingSLE.Sec5.Aux61Restart
