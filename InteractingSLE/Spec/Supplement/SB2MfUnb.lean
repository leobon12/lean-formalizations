/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MfFill

/-!
# Unbounded lower-union components survive filling (deterministic)

Packet PROVE-SB2-LCMEAN, round 3. The union-mean engine asks every component of `lowerUnion A = A ∪ {Im ≤ 0}` to be
unbounded, for the retained and the explored set. For a stage set `S` this is landed
(`WalkSide.not_isBounded_lowerUnion_stageSet`); the stage-chart pull-back works with the FILLED versions
(`Mf.fillVer`). Here:

* `isPreconnected_lowerHalf`, `not_isBounded_lowerHalf`: the closed lower half-plane `L`;
* `frontier_connectedComponentIn_subset_of_isOpen`: the frontier of a component of an open set lies outside the set;
* **`isPreconnected_lowerUnion_of_bounded`**: for bounded `S ⊆ ℍ` with unbounded lower-union components,
  `lowerUnion S` is preconnected (every component meets `L`);
* **`not_isBounded_lowerUnion_fillH_closure`**: then every component of `lowerUnion (fill (closure S))` is unbounded
  (the closure is attached, and each bounded pocket of `ℍ ∖ closure S` has its frontier in `closure S ∪ ℝ`);
* **`not_isBounded_lowerUnion_fillVer`**: the same for `fillVer B` (where `B` is unbounded, `fillVer B = B`).

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mf

open LocalSets

/-- The closed lower half-plane. -/
def lowerHalf : Set ℂ := {w : ℂ | w.im ≤ 0}

theorem isPreconnected_lowerHalf : IsPreconnected lowerHalf :=
  (convex_halfSpace_le Complex.imLm.isLinear (0 : ℝ)).isPreconnected

theorem not_isBounded_lowerHalf : ¬ Bornology.IsBounded lowerHalf := by
  intro hb
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  have hmem : (-(((|R| + 1 : ℝ) : ℂ) * Complex.I)) ∈ lowerHalf := by
    show (-(((|R| + 1 : ℝ) : ℂ) * Complex.I)).im ≤ 0
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    linarith [abs_nonneg R]
  have h1 := hR hmem
  rw [mem_closedBall, dist_zero_right, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |R| + 1)] at h1
  linarith [le_abs_self R]

theorem lowerUnion_eq (S : Set ℂ) : lowerUnion S = S ∪ lowerHalf := rfl

theorem isClosed_lowerHalf : IsClosed lowerHalf := isClosed_le Complex.continuous_im continuous_const

/-- The frontier of a component of an open set lies outside the set. -/
theorem frontier_connectedComponentIn_subset_of_isOpen {O : Set ℂ} (hO : IsOpen O) (z : ℂ) :
    frontier (connectedComponentIn O z) ⊆ closure O \ O := by
  intro y hy
  have hQo : IsOpen (connectedComponentIn O z) := hO.connectedComponentIn
  refine ⟨closure_mono (connectedComponentIn_subset O z) hy.1, fun hyO => ?_⟩
  have hyQ : y ∉ connectedComponentIn O z := by
    rw [hQo.frontier_eq] at hy
    exact hy.2
  have hVo : IsOpen (connectedComponentIn O y) := hO.connectedComponentIn
  obtain ⟨q, hqV, hqQ⟩ := mem_closure_iff.1 hy.1 _ hVo (mem_connectedComponentIn hyO)
  have e1 : connectedComponentIn O z = connectedComponentIn O q := connectedComponentIn_eq hqQ
  have e2 : connectedComponentIn O y = connectedComponentIn O q := connectedComponentIn_eq hqV
  exact hyQ (by rw [e1, ← e2]; exact mem_connectedComponentIn hyO)

/-- **A bounded set in `ℍ` whose lower union has unbounded components has a preconnected lower union.** -/
theorem isPreconnected_lowerUnion_of_bounded {S : Set ℂ} (hSb : Bornology.IsBounded S)
    (hS : ∀ z ∈ lowerUnion S, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion S) z)) :
    IsPreconnected (lowerUnion S) := by
  set p₀ : ℂ := -Complex.I with hp₀
  have hp₀L : p₀ ∈ lowerHalf := by show (-Complex.I).im ≤ 0; simp
  have hLsub : lowerHalf ⊆ lowerUnion S := subset_union_right
  have hL : lowerHalf ⊆ connectedComponentIn (lowerUnion S) p₀ :=
    isPreconnected_lowerHalf.subset_connectedComponentIn hp₀L hLsub
  have heq : connectedComponentIn (lowerUnion S) p₀ = lowerUnion S := by
    refine Subset.antisymm (connectedComponentIn_subset _ _) fun s hs => ?_
    have hunb := hS s hs
    obtain ⟨q, hqC, hqS⟩ : ∃ q ∈ connectedComponentIn (lowerUnion S) s, q ∉ S := by
      by_contra hn
      push Not at hn
      exact hunb (hSb.subset hn)
    have hqL : q ∈ lowerHalf := (connectedComponentIn_subset _ _ hqC).resolve_left hqS
    have e1 : connectedComponentIn (lowerUnion S) s = connectedComponentIn (lowerUnion S) q :=
      connectedComponentIn_eq hqC
    have hLq : lowerHalf ⊆ connectedComponentIn (lowerUnion S) q :=
      isPreconnected_lowerHalf.subset_connectedComponentIn hqL hLsub
    have e2 : connectedComponentIn (lowerUnion S) q = connectedComponentIn (lowerUnion S) p₀ :=
      connectedComponentIn_eq (hLq hp₀L)
    rw [← e2, ← e1]
    exact mem_connectedComponentIn hs
  rw [← heq]
  exact isPreconnected_connectedComponentIn

/-- **Filling keeps the lower-union components unbounded.** -/
theorem not_isBounded_lowerUnion_fillH_closure {S : Set ℂ} (hSH : S ⊆ H) (hSb : Bornology.IsBounded S)
    (hS : ∀ z ∈ lowerUnion S, ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion S) z)) :
    ∀ z ∈ lowerUnion (fillH (closure S)),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fillH (closure S))) z) := by
  set T := lowerUnion (fillH (closure S)) with hT
  set K := closure S ∪ lowerHalf with hK
  have hKpre : IsPreconnected K := by
    have h1 := (isPreconnected_lowerUnion_of_bounded hSb hS).closure
    rwa [lowerUnion_eq, closure_union, isClosed_lowerHalf.closure_eq] at h1
  have hKT : K ⊆ T := by
    rintro z (hz | hz)
    · by_cases hzH : z ∈ H
      · exact Or.inl ⟨hzH, Or.inl (by rwa [closure_closure])⟩
      · have hz0 : z ∈ Hbar := by
          rw [← closure_H]; exact closure_mono hSH hz
        exact Or.inr (show z.im ≤ 0 from le_of_not_gt hzH)
    · exact Or.inr hz
  set p₀ : ℂ := -Complex.I with hp₀
  have hp₀K : p₀ ∈ K := Or.inr (show (-Complex.I).im ≤ 0 by simp)
  have hKC : K ⊆ connectedComponentIn T p₀ := hKpre.subset_connectedComponentIn hp₀K hKT
  have hall : ∀ z ∈ T, z ∈ connectedComponentIn T p₀ := by
    intro z hz
    by_cases hzK : z ∈ K
    · exact hKC hzK
    · -- a point of a bounded pocket
      have hzF : z ∈ fillH (closure S) := hz.resolve_right fun h => hzK (Or.inr h)
      obtain ⟨hzH, hzc⟩ := hzF
      rw [closure_closure] at hzc
      have hzcS : z ∉ closure S := fun h => hzK (Or.inl h)
      have hQb : Bornology.IsBounded (connectedComponentIn (H \ closure S) z) := hzc.resolve_left hzcS
      set Q := connectedComponentIn (H \ closure S) z with hQ
      have hO : IsOpen (H \ closure S) := QuantumZipper.isOpen_H.sdiff isClosed_closure
      have hzQ : z ∈ Q := mem_connectedComponentIn ⟨hzH, hzcS⟩
      have hQT : Q ⊆ T := by
        intro y hy
        have hyO := connectedComponentIn_subset _ _ hy
        refine Or.inl ⟨hyO.1, Or.inr ?_⟩
        rw [closure_closure, ← connectedComponentIn_eq hy]
        exact hQb
      have hfr : frontier Q ⊆ K := by
        intro y hy
        obtain ⟨hyc, hyO⟩ := frontier_connectedComponentIn_subset_of_isOpen hO z hy
        have hyH : y ∈ Hbar := by
          rw [← closure_H]; exact closure_mono sdiff_subset hyc
        by_cases hyH' : y ∈ H
        · exact Or.inl (by_contra fun h => hyO ⟨hyH', h⟩)
        · exact Or.inr (show y.im ≤ 0 from le_of_not_gt hyH')
      have hclT : closure Q ⊆ T := by
        intro y hy
        rw [closure_eq_self_union_frontier] at hy
        rcases hy with hy | hy
        · exact hQT hy
        · exact hKT (hfr hy)
      have hfne : (frontier Q).Nonempty := by
        rw [nonempty_frontier_iff]
        refine ⟨⟨z, hzQ⟩, fun h => not_isBounded_lowerHalf (hQb.subset ?_)⟩
        rw [h]
        exact subset_univ _
      obtain ⟨y, hy⟩ := hfne
      have hpre : IsPreconnected (closure Q ∪ K) :=
        IsPreconnected.union y (frontier_subset_closure hy) (hfr hy) isPreconnected_connectedComponentIn.closure
          hKpre
      have hsub : closure Q ∪ K ⊆ connectedComponentIn T p₀ :=
        hpre.subset_connectedComponentIn (Or.inr hp₀K) (union_subset hclT hKT)
      exact hsub (Or.inl (subset_closure hzQ))
  intro z hz hb
  have e : connectedComponentIn T z = connectedComponentIn T p₀ := (connectedComponentIn_eq (hall z hz)).symm
  have hLC : lowerHalf ⊆ connectedComponentIn T z := by
    rw [e]; exact fun w hw => hKC (Or.inr hw)
  exact not_isBounded_lowerHalf (hb.subset hLC)

/-- **The filled version keeps the lower-union components unbounded.** -/
theorem not_isBounded_lowerUnion_fillVer {Ω : Type*} {B : Ω → Set ℂ} (hB : ∀ ω, B ω ⊆ H) (ω : Ω)
    (hS : ∀ z ∈ lowerUnion (B ω), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (B ω)) z)) :
    ∀ z ∈ lowerUnion (fillVer B ω), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fillVer B ω)) z) := by
  by_cases hb : Bornology.IsBounded (B ω)
  · rw [fillVer_of_bounded hb]
    exact not_isBounded_lowerUnion_fillH_closure (hB ω) hb hS
  · rw [fillVer_of_not_bounded hb]
    exact hS

end InteractingSLE.Theorem14.SB.Mf
