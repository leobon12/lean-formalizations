import HigherDimLQGMetric.Config.Continuous
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Bound data for continuous configuration coordinates

The compact exhaustion of each annulus supplies the sets `Lₘ`. A bound datum
records finite upper bounds, a common upper modulus, and a positive lower
modulus on every `Lₘ × Lₘ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology
open HigherDimLFPP (Rd)

/-- Upper and lower control for real metric coordinates on a compact exhaustion. -/
structure ConfigBoundDatum (X : Type*) [MetricSpace X] where
  upper : ℕ → ℝ
  upper_nonneg : ∀ m, 0 ≤ upper m
  modulus : ℕ → ℝ → ℝ
  modulus_nonneg : ∀ m η, 0 ≤ modulus m η
  modulus_mono : ∀ m, Monotone (modulus m)
  modulus_small : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ η : ℝ, 0 < η ∧ modulus m η < ε
  lower : ℕ → ℝ → ℝ
  lower_zero : ∀ m, lower m 0 = 0
  lower_pos : ∀ m : ℕ, ∀ η : ℝ, 0 < η → 0 < lower m η
  lower_mono : ∀ m, Monotone (lower m)

/-- The compact exhaustion of the outer annulus. -/
def configOuterExhaust (d : ℕ) : CompactExhaustion (configOuter d) :=
  CompactExhaustion.choice _

/-- The compact exhaustion of the inner annulus. -/
def configInnerExhaust (d : ℕ) : CompactExhaustion (configInner d) :=
  CompactExhaustion.choice _

/-- The three MA1 bounds on one coordinate. The product metric in the upper
modulus is equivalent to the paper's two separate endpoint bounds. -/
def configBoundOne {X : Type*} [MetricSpace X] (K : CompactExhaustion X)
    (β : ConfigBoundDatum X) : Set C(X × X, ℝ) :=
  {f | (∀ m (p : X × X), p.1 ∈ K m → p.2 ∈ K m →
        β.lower m (dist p.1 p.2) ≤ f p ∧ f p ≤ β.upper m) ∧
      (∀ m (p q : X × X), p.1 ∈ K m → p.2 ∈ K m →
        q.1 ∈ K m → q.2 ∈ K m → ∀ η : ℝ, 0 ≤ η → dist p q ≤ η →
          dist (f p) (f q) ≤ β.modulus m η)}

theorem configBoundOne_isClosed {X : Type*} [MetricSpace X]
    (K : CompactExhaustion X) (β : ConfigBoundDatum X) :
    IsClosed (configBoundOne K β) := by
  have hlow : IsClosed {f : C(X × X, ℝ) | ∀ m (p : X × X),
      p.1 ∈ K m → p.2 ∈ K m → β.lower m (dist p.1 p.2) ≤ f p} := by
    have h : IsClosed (⋂ m, ⋂ p : X × X, ⋂ (_ : p.1 ∈ K m),
        ⋂ (_ : p.2 ∈ K m), {f : C(X × X, ℝ) |
          β.lower m (dist p.1 p.2) ≤ f p}) :=
      isClosed_iInter fun m => isClosed_iInter fun p =>
        isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_le continuous_const (continuous_eval_const p)
    convert h using 1
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  have hupp : IsClosed {f : C(X × X, ℝ) | ∀ m (p : X × X),
      p.1 ∈ K m → p.2 ∈ K m → f p ≤ β.upper m} := by
    have h : IsClosed (⋂ m, ⋂ p : X × X, ⋂ (_ : p.1 ∈ K m),
        ⋂ (_ : p.2 ∈ K m), {f : C(X × X, ℝ) | f p ≤ β.upper m}) :=
      isClosed_iInter fun m => isClosed_iInter fun p =>
        isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_le (continuous_eval_const p) continuous_const
    convert h using 1
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  have hmod : IsClosed {f : C(X × X, ℝ) | ∀ m (p q : X × X),
      p.1 ∈ K m → p.2 ∈ K m → q.1 ∈ K m → q.2 ∈ K m →
      ∀ η : ℝ, 0 ≤ η → dist p q ≤ η →
        dist (f p) (f q) ≤ β.modulus m η} := by
    have h : IsClosed (⋂ m, ⋂ p : X × X, ⋂ q : X × X,
        ⋂ (_ : p.1 ∈ K m), ⋂ (_ : p.2 ∈ K m),
        ⋂ (_ : q.1 ∈ K m), ⋂ (_ : q.2 ∈ K m),
        ⋂ η : ℝ, ⋂ (_ : 0 ≤ η), ⋂ (_ : dist p q ≤ η),
        {f : C(X × X, ℝ) | dist (f p) (f q) ≤ β.modulus m η}) := by
      exact isClosed_iInter fun m => isClosed_iInter fun p => isClosed_iInter fun q =>
        isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun _ => isClosed_iInter fun _ =>
        isClosed_iInter fun η => isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_le ((continuous_eval_const p).dist (continuous_eval_const q))
            continuous_const
    convert h using 1
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  have heq : configBoundOne K β =
      {f : C(X × X, ℝ) | ∀ m (p : X × X), p.1 ∈ K m → p.2 ∈ K m →
        β.lower m (dist p.1 p.2) ≤ f p} ∩
      {f : C(X × X, ℝ) | ∀ m (p : X × X), p.1 ∈ K m → p.2 ∈ K m →
        f p ≤ β.upper m} ∩
      {f : C(X × X, ℝ) | ∀ m (p q : X × X),
        p.1 ∈ K m → p.2 ∈ K m → q.1 ∈ K m → q.2 ∈ K m →
        ∀ η : ℝ, 0 ≤ η → dist p q ≤ η →
          dist (f p) (f q) ≤ β.modulus m η} := by
    ext f
    simp only [configBoundOne, Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact ⟨fun h => ⟨⟨fun m p h1 h2 => (h.1 m p h1 h2).1,
      fun m p h1 h2 => (h.1 m p h1 h2).2⟩, h.2⟩,
      fun h => ⟨fun m p h1 h2 => ⟨h.1.1 m p h1 h2, h.1.2 m p h1 h2⟩, h.2⟩⟩
  rw [heq]
  exact (hlow.inter hupp).inter hmod

theorem configBoundOne_equicontinuous {X : Type*} [MetricSpace X]
    (K : CompactExhaustion X) (β : ConfigBoundDatum X) :
    Equicontinuous ((↑) : configBoundOne K β → X × X → ℝ) := by
  intro p
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  obtain ⟨m₁, hm₁⟩ := K.exists_mem_nhds p.1
  obtain ⟨m₂, hm₂⟩ := K.exists_mem_nhds p.2
  let m := max m₁ m₂
  have h₁ : K m ∈ 𝓝 p.1 := Filter.mem_of_superset hm₁ (K.subset (le_max_left _ _))
  have h₂ : K m ∈ 𝓝 p.2 := Filter.mem_of_superset hm₂ (K.subset (le_max_right _ _))
  have hprod : K m ×ˢ K m ∈ 𝓝 p := prod_mem_nhds h₁ h₂
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hprod
  obtain ⟨η, hη, hω⟩ := β.modulus_small m ε hε
  have hp : p ∈ K m ×ˢ K m := mem_of_mem_nhds hprod
  let t := min δ η
  have ht : 0 < t := lt_min hδ hη
  filter_upwards [Metric.ball_mem_nhds p ht] with q hq f
  have hq' : q ∈ K m ×ˢ K m := hball (Metric.ball_subset_ball (min_le_left δ η) hq)
  have hp' : p.1 ∈ K m ∧ p.2 ∈ K m := hp
  have hq'' : q.1 ∈ K m ∧ q.2 ∈ K m := hq'
  have hsmall : dist p q ≤ η := by
    rw [dist_comm]
    exact (Metric.mem_ball.mp hq).le.trans (min_le_right δ η)
  exact (f.2.2 m p q hp'.1 hp'.2 hq''.1 hq''.2 η hη.le hsmall).trans_lt hω

theorem configBoundOne_pointwise_bounded {X : Type*} [MetricSpace X]
    (K : CompactExhaustion X) (β : ConfigBoundDatum X) (p : X × X) :
    ∃ m : ℕ, ∀ f ∈ configBoundOne K β, f p ∈ Set.Icc 0 (β.upper m) := by
  obtain ⟨m₁, hm₁⟩ := K.exists_mem p.1
  obtain ⟨m₂, hm₂⟩ := K.exists_mem p.2
  let m := max m₁ m₂
  have hp₁ : p.1 ∈ K m := K.subset (le_max_left _ _) hm₁
  have hp₂ : p.2 ∈ K m := K.subset (le_max_right _ _) hm₂
  refine ⟨m, fun f hf => ?_⟩
  have h := hf.1 m p hp₁ hp₂
  have hnonneg : 0 ≤ β.lower m (dist p.1 p.2) := by
    calc
      0 = β.lower m 0 := (β.lower_zero m).symm
      _ ≤ β.lower m (dist p.1 p.2) := β.lower_mono m dist_nonneg
  exact ⟨hnonneg.trans h.1, h.2⟩

/-- Arzelà–Ascoli in the compact-open topology on `C(X × X, ℝ)`. -/
theorem configBoundOne_isCompact {X : Type*} [MetricSpace X]
    (K : CompactExhaustion X) (β : ConfigBoundDatum X) :
    IsCompact (configBoundOne K β) := by
  let S : Set C(X × X, ℝ) := configBoundOne K β
  have hEq : Equicontinuous ((↑) : S → X × X → ℝ) :=
    configBoundOne_equicontinuous K β
  have hEmb : IsClosedEmbedding
      (UniformOnFun.ofFun {L : Set (X × X) | IsCompact L} ∘
        (fun g : C(X × X, ℝ) => (g : X × X → ℝ))) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    change IsClosed (Set.range (ContinuousMap.toUniformOnFunIsCompact :
      C(X × X, ℝ) → UniformOnFun (X × X) ℝ {L | IsCompact L}))
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOfPred_continuous CompactlyCoherentSpace.isCoherentWith
  have hc : IsCompact (closure S) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖_compact := fun L hL => hL) hEmb
    · intro L _
      exact hEq.equicontinuousOn L
    · intro L _ p _
      obtain ⟨m, hm⟩ := configBoundOne_pointwise_bounded K β p
      refine ⟨Set.Icc 0 (β.upper m), isCompact_Icc, ?_⟩
      intro f hf
      exact hm f hf
  simpa only [S, (configBoundOne_isClosed K β).closure_eq] using hc

/-- The lower bound in `B(β)` gives the exact uniform inverse modulus used
by MA1 Lemmas 2.2′ and 2.3′. -/
theorem configBoundOne_uniformLower {X : Type*} [MetricSpace X]
    (K : CompactExhaustion X) (β : ConfigBoundDatum X)
    (F : ℕ → C(X × X, ℝ)) (hF : ∀ n, F n ∈ configBoundOne K β)
    (L : Set X) (hL : IsCompact L) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
      F n (u, v) < δ → dist u v < ε := by
  obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hL
  refine ⟨β.lower m ε, β.lower_pos m ε hε, ?_⟩
  intro n u hu v hv hsmall
  by_contra hlarge
  have hdist : ε ≤ dist u v := le_of_not_gt hlarge
  have hbound := (hF n).1 m (u, v) (hm hu) (hm hv)
  have hle := (β.lower_mono m hdist).trans hbound.1
  exact (not_lt_of_ge hle) hsmall

/-- A datum for both domains; the same bounds apply to the two metrics on each domain. -/
structure ConfigBounds (d : ℕ) where
  outer : ConfigBoundDatum (configOuter d)
  inner : ConfigBoundDatum (configInner d)

/-- `B(β)`, the closed family of configurations obeying all bounds. -/
def configBoundSet {d : ℕ} (β : ConfigBounds d) : Set (ConfigC d) :=
  {c | c.1 ∈ configBoundOne (configOuterExhaust d) β.outer ∧
       c.2.1 ∈ configBoundOne (configOuterExhaust d) β.outer ∧
       c.2.2.1 ∈ configBoundOne (configInnerExhaust d) β.inner ∧
       c.2.2.2 ∈ configBoundOne (configInnerExhaust d) β.inner}

theorem configBoundSet_isCompact {d : ℕ} (β : ConfigBounds d) :
    IsCompact (configBoundSet β) := by
  let O := configBoundOne (configOuterExhaust d) β.outer
  let I := configBoundOne (configInnerExhaust d) β.inner
  have hO : IsCompact O := configBoundOne_isCompact _ _
  have hI : IsCompact I := configBoundOne_isCompact _ _
  change IsCompact (O ×ˢ (O ×ˢ (I ×ˢ I)))
  exact hO.prod (hO.prod (hI.prod hI))

theorem configBoundSet_isClosed {d : ℕ} (β : ConfigBounds d) :
    IsClosed (configBoundSet β) := (configBoundSet_isCompact β).isClosed

end HigherDimLQGMetric
