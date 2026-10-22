import HigherDimLQGMetric.Sec6.Prop62Basic
import HigherDimLQGMetric.Coord.LemmaCC
import HigherDimLQGMetric.Coord.RecoveryFull

/-!
# [S] Proposition 6.2: witness paths in the compact configuration family

Packet S6b. Source: MA3 Details (a) **D-6.2** (*Construction*: the set `𝒢`, "`𝒢` is compact (closed
conditions; witness fibers compact by the common inverse modulus of `𝒞`, lengths lower
semicontinuous, …)"), blueprint Part A §6 (`prop:62`, steps (5)–(6)), source l. 1066–1077.

* `s6bWitness q B A a₁ c₂`: a path `P : [0,1] → B` in the outer configuration annulus with
  `D̃^U`-speed `≤ A`, endpoint distance `D^U(P 0, P 1) ≥ a₁` and `len(P; D̃^U) ≤ c₂ D^U(P 0, P 1)`.
  (The speed bound is put on the `D̃` coordinate, whose length is the one that must be lower
  semicontinuous; MA3 writes it for `D^U`, which is equivalent up to the factor `C_*`.)
* `s6b_isClosed_witness`: `{q ∈ C(β) | s6bWitness q B A a₁ c₂}` is closed (M2a's Lemma CC).
* `s6b_witness_of_path`: a finite-length path in `B` gives a witness (M2a's constant-speed
  reparametrization).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology BoundedContinuousFunction unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ### Lengths from speed bounds -/

/-- A speed bound `δ(P u, P v) ≤ L (v - u)` bounds the length by `L (b - a)`. -/
theorem s6b_curveLengthWith_le_of_speed {X : Type*} {δ : X → X → ℝ≥0∞} {P : ℝ → X}
    {a b L : ℝ} (hL : 0 ≤ L)
    (h : ∀ u v, a ≤ u → u ≤ v → v ≤ b → δ (P u) (P v) ≤ ENNReal.ofReal (L * (v - u))) :
    curveLengthWith δ P a b ≤ ENNReal.ofReal (L * (b - a)) := by
  unfold curveLengthWith
  refine partitionSup_le fun p => ?_
  calc p.sum (fun u v => δ (P u) (P v))
      ≤ ∑ i ∈ Finset.range p.n, ENNReal.ofReal (L * (p.t (i + 1) - p.t i)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
        exact h _ _ h1 h2 h3
    _ = ENNReal.ofReal (∑ i ∈ Finset.range p.n, L * (p.t (i + 1) - p.t i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i hi
        obtain ⟨-, h2, -⟩ := p.step (Finset.mem_range.1 hi)
        exact mul_nonneg hL (sub_nonneg.2 h2)
    _ = ENNReal.ofReal (L * (b - a)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => p.t i), p.last, p.zero]

/-! ### Coordinate convergence -/

theorem s6b_tendstoUniformlyOn_fst {ι : Type*} {l : Filter ι} {F : ι → ConfigC d}
    {q : ConfigC d} (h : Tendsto F l (𝓝 q)) {K : Set (configOuter d × configOuter d)}
    (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => ⇑(F n).1) ⇑q.1 l K := by
  have h1 : Tendsto (fun n => (F n).1) l (𝓝 q.1) := (continuous_fst.tendsto q).comp h
  have h2 := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h1
  exact (tendstoLocallyUniformly_iff_forall_isCompact.1 h2) K hK

theorem s6b_tendstoUniformlyOn_snd {ι : Type*} {l : Filter ι} {F : ι → ConfigC d}
    {q : ConfigC d} (h : Tendsto F l (𝓝 q)) {K : Set (configOuter d × configOuter d)}
    (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => ⇑(F n).2.1) ⇑q.2.1 l K := by
  have h1 : Tendsto (fun n => (F n).2.1) l (𝓝 q.2.1) :=
    ((continuous_fst.comp continuous_snd).tendsto q).comp h
  have h2 := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h1
  exact (tendstoLocallyUniformly_iff_forall_isCompact.1 h2) K hK

/-! ### Witness paths -/

/-- A **witness path** in `B` for the configuration `q`: `D̃^U`-speed `≤ A`, endpoint `D^U`-distance
`≥ a₁` and `D̃^U`-length `≤ c₂ ×` endpoint `D^U`-distance. -/
def s6bWitness (q : ConfigC d) (B : Set (Rd d)) (A a₁ c₂ : ℝ) : Prop :=
  ∃ P : I →ᵇ configOuter d, (∀ t, (P t : Rd d) ∈ B) ∧
    (∀ s t : I, q.2.1 (P s, P t) ≤ A * dist s t) ∧ a₁ ≤ q.1 (P 0, P 1) ∧
    curveLengthWith (fun u v => ENNReal.ofReal (q.2.1 (u, v))) (Set.IccExtend zero_le_one P) 0 1 ≤
      ENNReal.ofReal (c₂ * q.1 (P 0, P 1))

/-- The witness condition defines a closed subset of the compact family. -/
theorem s6b_isClosed_witness (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d) {B : Set (Rd d)}
    (hB : IsCompact B) (hBU : B ⊆ configOuter d) (A a₁ c₂ : ℝ) :
    IsClosed {q : ConfigC d | q ∈ configCompactFamily hd c C β ∧ s6bWitness q B A a₁ c₂} := by
  set L : Set (configOuter d) := Subtype.val ⁻¹' B with hL_def
  have hL : IsCompact L := trap_isCompact_preimage_val hB hBU
  have hLL : IsCompact (L ×ˢ L) := hL.prod hL
  refine isClosed_of_closure_subset fun q hq => ?_
  obtain ⟨F, hFS, hFq⟩ := mem_closure_iff_seq_limit.1 hq
  have hqC : q ∈ configCompactFamily hd c C β :=
    isClosed_closure.mem_of_tendsto hFq (Eventually.of_forall fun n => (hFS n).1)
  refine ⟨hqC, ?_⟩
  choose P hPB hPspeed hPsep hPlen using fun n => (hFS n).2
  have hBd : ∀ n, F n ∈ configBoundSet β := fun n =>
    configCompactFamily_subset_bound hd c C β (hFS n).1
  -- Lemma CC for the `D̃` coordinate
  obtain ⟨Q, hQL, φ, hφ, hQconv, hQspeed, hQlen, -⟩ :=
    lemmaCC (X := configOuter d) zero_le_one hL (fun n => ⇑(F n).2.1) ⇑q.2.1
      (fun n => ((F n).2.1.continuous).continuousOn) (s6b_tendstoUniformlyOn_snd hFq hLL)
      A P (fun n t => hPB n t)
      (fun ε hε => by
        obtain ⟨δ, hδ, H⟩ := configBoundOne_uniformLower (configOuterExhaust d) β.outer
          (fun n => (F n).2.1) (fun n => (hBd n).2.1) L hL ε hε
        exact ⟨δ, hδ, fun n x hx y hy h => H n x hx y hy h⟩)
      hPspeed
  refine ⟨Q, fun t => hQL t, hQspeed, ?_, ?_⟩ <;>
    -- the endpoint distances converge along the subsequence
    have hFφ : Tendsto (fun n => F (φ n)) atTop (𝓝 q) := hFq.comp hφ.tendsto_atTop <;>
    have hend : Tendsto (fun n => (F (φ n)).1 (P (φ n) 0, P (φ n) 1)) atTop
        (𝓝 (q.1 (Q 0, Q 1))) := by
      refine (s6b_tendstoUniformlyOn_fst hFφ hLL).tendsto_comp
        (q.1.continuous.continuousWithinAt) ?_
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ⟨hPB _ _, hPB _ _⟩⟩
      exact (hQconv.tendsto_at 0).prodMk_nhds (hQconv.tendsto_at 1)
  · exact ge_of_tendsto hend (Eventually.of_forall fun n => hPsep (φ n))
  · have hlim : Tendsto (fun n => ENNReal.ofReal (c₂ * (F (φ n)).1 (P (φ n) 0, P (φ n) 1)))
        atTop (𝓝 (ENNReal.ofReal (c₂ * q.1 (Q 0, Q 1)))) :=
      ENNReal.tendsto_ofReal (hend.const_mul c₂)
    calc curveLengthWith (fun u v => ENNReal.ofReal (q.2.1 (u, v)))
          (Set.IccExtend zero_le_one Q) 0 1
        ≤ liminf (fun n => curveLengthWith (fun x y => ENNReal.ofReal ((F (φ n)).2.1 (x, y)))
            (Set.IccExtend zero_le_one (P (φ n))) 0 1) atTop :=
          hQlen le_rfl zero_le_one le_rfl
      _ ≤ liminf (fun n => ENNReal.ofReal (c₂ * (F (φ n)).1 (P (φ n) 0, P (φ n) 1))) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => hPlen (φ n))
      _ = ENNReal.ofReal (c₂ * q.1 (Q 0, Q 1)) := hlim.liminf_eq

/-- A finite-length path in `B` with the ratio bound gives a witness (constant `D̃`-speed
reparametrization). -/
theorem s6b_witness_of_path {q : ConfigC d} (hq2 : IsCoordinate q.2.1) {B : Set (Rd d)}
    {u : I →ᵇ configOuter d} (huB : ∀ t, (u t : Rd d) ∈ B) {A a₁ c₂ : ℝ} (hA : 0 ≤ A)
    (hlenA : curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (Set.IccExtend zero_le_one u) 0 1 ≤ ENNReal.ofReal A)
    (hsep : a₁ ≤ q.1 (u 0, u 1))
    (hrat : curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (Set.IccExtend zero_le_one u) 0 1 ≤ ENNReal.ofReal (c₂ * q.1 (u 0, u 1))) :
    s6bWitness q B A a₁ c₂ := by
  have hfin : curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (Set.IccExtend zero_le_one u) 0 1 ≠ ∞ := (hlenA.trans_lt ENNReal.ofReal_lt_top).ne
  obtain ⟨R, hRB, hR0, hR1, hRspeed, -⟩ :=
    coordinate_reparam_bounded q.2.1 hq2 (fun _ => (1 : ℝ)) (K := Subtype.val ⁻¹' B) u huB hfin
  set L := (curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
    (Set.IccExtend zero_le_one u) 0 1).toReal with hL_def
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hLA : L ≤ A :=
    ((ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2 hlenA).trans_eq
      (ENNReal.toReal_ofReal hA)
  have hLeq : ENNReal.ofReal L = curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (Set.IccExtend zero_le_one u) 0 1 := ENNReal.ofReal_toReal hfin
  -- the reparametrized path has length at most `L`
  have hRlen : curveLengthWith (fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (Set.IccExtend zero_le_one R) 0 1 ≤ ENNReal.ofReal L := by
    have h := s6b_curveLengthWith_le_of_speed (δ := fun x y => ENNReal.ofReal (q.2.1 (x, y)))
      (P := Set.IccExtend zero_le_one R) (a := 0) (b := 1) hL0 (fun s t hs hst ht => by
        rw [Set.IccExtend_of_mem _ _ ⟨hs, hst.trans ht⟩, Set.IccExtend_of_mem _ _ ⟨hs.trans hst, ht⟩]
        refine ENNReal.ofReal_le_ofReal ((hRspeed _ _).trans_eq ?_)
        rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (by simpa using hst)]
        ring)
    simpa using h
  refine ⟨R, hRB, fun s t => (hRspeed s t).trans ?_, by rw [hR0, hR1]; exact hsep, ?_⟩
  · exact mul_le_mul_of_nonneg_right hLA dist_nonneg
  · rw [hR0, hR1]
    exact hRlen.trans (hLeq.le.trans hrat)

end HigherDimLQGMetric
