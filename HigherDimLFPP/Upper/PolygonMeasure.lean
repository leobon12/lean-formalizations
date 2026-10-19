import HigherDimLFPP.Upper.GoodNode
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Growth and coupling of good polygons: HA3 D4 (a), (b)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.1, Lemma 4.2 ("Both `ν_{Q_u}` and `ν_{I_u}`
satisfy (3.4) at scale `R_u` with a universal constant, and they have a displacement coupling of
size at most `C R_u √a_u`"), in the explicit form of HA3 D4 (a), (b)
(`planning/audits/HA3-section-4.md`): for `Q ∈ G_K(x, y)` and `a = log(len Q/|y - x|)`,

* (a) `ν_Q(B̄(w,t)) ≤ min(1, 3t/|y - x|)` and `ν_{[x,y]}(B̄(w,t)) ≤ min(1, 2t/|y - x|)`;
* (b) `ν_{[x,y]}` and `ν_Q` have a displacement coupling of size `2 |y - x| √a` (for `a₀ ≤ 1`).

2D source: `LQGDimension/LFPP/RecordVarianceAux1.lean` (`map_affine_restrict`, `segMeas_lin`,
`toMeasure_wc_lin`, `proj`, `segMeas_ball_le_proj`, `forward_growth`),
`LQGDimension/LFPP/RecordVarianceAux2.lean` (`vert_close`, `coupled_poly`) and
`LQGDimension/LFPP/ConstrainedCovMeas.lean` (`segMeas`, `pairSeg`, `coupled_wc`), with `ℂ`
replaced by `Rd d` (inner products instead of `Complex.normSq`, `Finset` sums of measures instead
of list sums).

The measures `segMeasure` and the growth and coupling predicates `GrowthBound`, `CoupledWithin`
have exactly the bodies recommended by HA2 (`planning/audits/HA2-section-3.md`, Lean block), so
that Lemma 3.1 (interface (I4)) applies to them directly; `polyMeasure` is the normalized
arclength of a polygon given by its vertex list (the list form of HA2's `polyMeasure`).

The last section records (4.5) for the node variables of `CutTree`:
`Σ_v p_{uv} H_v = ⟨φ, ν_{Q_u}⟩` (`integral_polyMeasure_childPoly`), hence
`G_u = ⟨φ, ν_{I_u} - ν_{Q_u}⟩` at good nodes (`G_eq_of_good`) and `G_u = ⟨φ, ν_{I_u} - ν_{I_v}⟩`
for an attained adverse child `v` at bad nodes (`G_eq_of_bad`); these identify the tree
variables with the record variables of Lemma 4.3 / HA3 D6.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

/-! ## Segment and polygon measures -/

section Defs

variable {d : ℕ}

/-- Uniform probability measure on the segment `[a, b]` (HA2's `segMeasure`). -/
def segMeasure (a b : Rd d) : Measure (Rd d) :=
  (volume.restrict (Icc (0 : ℝ) 1)).map fun s => a + s • (b - a)

/-- Normalized arclength `ν_Q` of the polygon `Q` with vertex list `z`. -/
def polyMeasure (z : List (Rd d)) : Measure (Rd d) :=
  ((edges z).map fun e => ENNReal.ofReal (‖e.2 - e.1‖ / polyLen z) • segMeasure e.1 e.2).sum

/-- Linear growth bound (3.4) at scale `R` with constant `B` (HA2's `GrowthBound`). -/
def GrowthBound (μ : Measure (Rd d)) (B R : ℝ) : Prop :=
  ∀ z : Rd d, ∀ t > 0, μ.real (Metric.closedBall z t) ≤ B * min 1 (t / R)

/-- Displacement coupling of size `u` (HA2's `CoupledWithin`). -/
def CoupledWithin (μ ν : Measure (Rd d)) (u : ℝ) : Prop :=
  ∃ cpl : Measure (Rd d × Rd d), cpl.map Prod.fst = μ ∧ cpl.map Prod.snd = ν ∧
    ∀ᵐ q ∂cpl, ‖q.1 - q.2‖ ≤ u

/-- The point with parameter `s` on the line through `a` and `b`. -/
def lin (a b : Rd d) (s : ℝ) : Rd d := a + s • (b - a)

/-- Weights `W i` on the edges `[V i, V (i+1)]`, `i < m`, as a measure. -/
def segSum (m : ℕ) (W : ℕ → ℝ) (V : ℕ → Rd d) : Measure (Rd d) :=
  ∑ i ∈ Finset.range m, ENNReal.ofReal (W i) • segMeasure (V i) (V (i + 1))

end Defs

/-! ## Elementary measure theory -/

section Basic

variable {d : ℕ}

theorem measurable_lin (a b : Rd d) : Measurable (lin a b) :=
  (continuous_const.add (continuous_id.smul continuous_const)).measurable

theorem segMeasure_eq (a b : Rd d) : segMeasure a b = (volume.restrict (Icc (0 : ℝ) 1)).map (lin a b) :=
  rfl

theorem segMeasure_univ (a b : Rd d) : segMeasure a b univ = 1 := by
  rw [segMeasure_eq, Measure.map_apply (measurable_lin a b) MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc]
  simp

instance (a b : Rd d) : IsProbabilityMeasure (segMeasure a b) :=
  ⟨segMeasure_univ a b⟩

theorem polyMeasure_range_map (V : ℕ → Rd d) (m : ℕ) :
    polyMeasure ((List.range (m + 1)).map V) =
      segSum m (fun i => ‖V (i + 1) - V i‖ / plen V m) V := by
  rw [polyMeasure, edges_range_map, polyLen_range_map, List.map_map, sum_map_range_eq]
  rfl

theorem segSum_univ {m : ℕ} {W : ℕ → ℝ} (V : ℕ → Rd d) (hW : ∀ i < m, 0 ≤ W i) :
    segSum m W V univ = ENNReal.ofReal (∑ i ∈ Finset.range m, W i) := by
  rw [segSum, Measure.finsetSum_apply, ENNReal.ofReal_sum_of_nonneg
    (fun i hi => hW i (Finset.mem_range.1 hi))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, segMeasure_univ, smul_eq_mul, mul_one]

theorem map_finsetSum_range {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (m : ℕ) (μ : ℕ → Measure α) :
    (∑ i ∈ Finset.range m, μ i).map f = ∑ i ∈ Finset.range m, (μ i).map f := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, Measure.map_add _ _ hf, ih, Finset.sum_range_succ]

theorem ae_finsetSum {α : Type*} [MeasurableSpace α] (m : ℕ) (μ : ℕ → Measure α)
    {p : α → Prop} (h : ∀ i < m, ∀ᵐ x ∂μ i, p x) :
    ∀ᵐ x ∂(∑ i ∈ Finset.range m, μ i), p x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ae_add_measure_iff]
    exact ⟨ih fun i hi => h i (by omega), h m (by omega)⟩

/-! ### Lebesgue measure on adjacent intervals -/

theorem restrict_Icc_add {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    volume.restrict (Icc a b) + volume.restrict (Icc b c) = volume.restrict (Icc a c) := by
  have h := Measure.restrict_union_add_inter (μ := (volume : Measure ℝ)) (Icc a b)
    (measurableSet_Icc (a := b) (b := c))
  rw [Set.Icc_union_Icc_eq_Icc hab hbc, Set.Icc_inter_Icc_eq_singleton hab hbc,
    Measure.restrict_eq_zero.2 Real.volume_singleton, add_zero] at h
  exact h.symm

theorem le_of_chain (P : ℕ → ℝ) {m : ℕ} (hP : ∀ i < m, P i ≤ P (i + 1)) : P 0 ≤ P m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih => exact (ih fun i hi => hP i (by omega)).trans (hP m (by omega))

theorem sum_restrict_Icc (P : ℕ → ℝ) {m : ℕ} (hP : ∀ i < m, P i ≤ P (i + 1)) :
    ∑ i ∈ Finset.range m, volume.restrict (Icc (P i) (P (i + 1))) =
      volume.restrict (Icc (P 0) (P m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih fun i hi => hP i (by omega),
      restrict_Icc_add (le_of_chain P fun i hi => hP i (by omega)) (hP m (by omega))]

/-- Affine image of the uniform measure on `[0,1]`. -/
theorem map_affine_restrict (a : ℝ) {h : ℝ} (hh : 0 < h) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun s : ℝ => a + s * h) =
      ENNReal.ofReal h⁻¹ • volume.restrict (Icc a (a + h)) := by
  have hf : Measurable (fun s : ℝ => a + s * h) := by fun_prop
  ext B hB
  rw [Measure.map_apply hf hB, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB,
    Measure.restrict_apply (hf hB)]
  have e : (fun s : ℝ => a + s * h) ⁻¹' B ∩ Icc 0 1 =
      (· * h) ⁻¹' ((fun x => a + x) ⁻¹' (B ∩ Icc a (a + h))) := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, ?_⟩
      · by_contra hs; push Not at hs; nlinarith
      · by_contra hs; push Not at hs; nlinarith
  rw [e, Real.volume_preimage_mul_right hh.ne', measure_preimage_add,
    abs_of_pos (inv_pos.2 hh)]

end Basic

/-! ## Growth of forward polygons (D4 (a)) -/

section Growth

variable {d : ℕ}

/-- Projection onto the direction of `v`, relative to `x`. -/
def proj (x v p : Rd d) : ℝ := ⟪p - x, v⟫ / ‖v‖

theorem proj_sub (x v p q : Rd d) : proj x v p - proj x v q = ⟪p - q, v⟫ / ‖v‖ := by
  unfold proj
  rw [← sub_div, ← inner_sub_left, sub_sub_sub_cancel_right]

theorem abs_proj_sub_le (x : Rd d) {v : Rd d} (hv : v ≠ 0) (p q : Rd d) :
    |proj x v p - proj x v q| ≤ ‖p - q‖ := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
  rw [proj_sub, abs_div, abs_of_pos hv', div_le_iff₀ hv']
  exact abs_real_inner_le_norm _ _

theorem proj_lin (x v a b : Rd d) (s : ℝ) :
    proj x v (lin a b s) = proj x v a + s * (proj x v b - proj x v a) := by
  unfold proj lin
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  ring

theorem segMeasure_closedBall_le_proj (x : Rd d) {v : Rd d} (hv : v ≠ 0) (a b w : Rd d) (t : ℝ)
    (hD : 0 < proj x v b - proj x v a) :
    segMeasure a b (Metric.closedBall w t) ≤
      ENNReal.ofReal (proj x v b - proj x v a)⁻¹ *
        volume.restrict (Icc (proj x v a) (proj x v b)) (Icc (proj x v w - t) (proj x v w + t)) := by
  set D := proj x v b - proj x v a with hDdef
  have haff : Measurable fun s : ℝ => proj x v a + s * D := by fun_prop
  have h1 : segMeasure a b (Metric.closedBall w t) ≤
      (volume.restrict (Icc (0 : ℝ) 1)).map (fun s : ℝ => proj x v a + s * D)
        (Icc (proj x v w - t) (proj x v w + t)) := by
    rw [segMeasure_eq, Measure.map_apply (measurable_lin a b) Metric.isClosed_closedBall.measurableSet,
      Measure.map_apply haff measurableSet_Icc]
    refine measure_mono fun s hs => ?_
    simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm] at hs ⊢
    have h := le_trans (abs_proj_sub_le x hv (lin a b s) w) hs
    rw [proj_lin, ← hDdef] at h
    rw [mem_Icc]
    constructor <;> linarith [(abs_le.1 h).1, (abs_le.1 h).2]
  refine h1.trans (le_of_eq ?_)
  rw [map_affine_restrict _ hD, Measure.smul_apply, smul_eq_mul,
    show proj x v a + D = proj x v b by rw [hDdef]; ring]

/-- **Forward-edge growth bound.**  If every edge advances along the direction `v` by at least
`W i / κ`, the combination has mass at most `2 κ t` on closed balls of radius `t`, whatever the
number of edges. -/
theorem forward_growth {m : ℕ} {W : ℕ → ℝ} {V : ℕ → Rd d} (x : Rd d) {v : Rd d} (hv : v ≠ 0)
    {κ : ℝ} (hκ : 0 ≤ κ) (hW0 : ∀ i < m, 0 ≤ W i)
    (hD : ∀ i < m, 0 < proj x v (V (i + 1)) - proj x v (V i))
    (hWD : ∀ i < m, W i ≤ κ * (proj x v (V (i + 1)) - proj x v (V i)))
    (w : Rd d) (t : ℝ) :
    segSum m W V (Metric.closedBall w t) ≤ ENNReal.ofReal (2 * κ * t) := by
  rw [segSum, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  set I := Icc (proj x v w - t) (proj x v w + t) with hI
  set P : ℕ → ℝ := fun i => proj x v (V i) with hP
  have hmono : ∀ i < m, P i ≤ P (i + 1) := fun i hi => by
    show proj x v (V i) ≤ proj x v (V (i + 1)); linarith [hD i hi]
  calc ∑ i ∈ Finset.range m,
        ENNReal.ofReal (W i) * segMeasure (V i) (V (i + 1)) (Metric.closedBall w t)
      ≤ ∑ i ∈ Finset.range m,
          ENNReal.ofReal κ * volume.restrict (Icc (P i) (P (i + 1))) I := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have hDi := hD i hi'
        calc ENNReal.ofReal (W i) * segMeasure (V i) (V (i + 1)) (Metric.closedBall w t)
            ≤ ENNReal.ofReal (W i) * (ENNReal.ofReal (proj x v (V (i + 1)) - proj x v (V i))⁻¹ *
                volume.restrict (Icc (P i) (P (i + 1))) I) := by
              gcongr
              exact segMeasure_closedBall_le_proj x hv (V i) (V (i + 1)) w t hDi
          _ = ENNReal.ofReal (W i * (proj x v (V (i + 1)) - proj x v (V i))⁻¹) *
                volume.restrict (Icc (P i) (P (i + 1))) I := by
              rw [← mul_assoc, ENNReal.ofReal_mul (hW0 i hi')]
          _ ≤ ENNReal.ofReal κ * volume.restrict (Icc (P i) (P (i + 1))) I := by
              gcongr
              rw [← div_eq_mul_inv, div_le_iff₀ hDi]
              exact hWD i hi'
    _ = ENNReal.ofReal κ * volume.restrict (Icc (P 0) (P m)) I := by
        rw [← Finset.mul_sum, ← Measure.finsetSum_apply, sum_restrict_Icc P hmono]
    _ ≤ ENNReal.ofReal κ * volume I := by
        gcongr
        exact Measure.restrict_le_self
    _ = ENNReal.ofReal (2 * κ * t) := by
        rw [hI, Real.volume_Icc, ← ENNReal.ofReal_mul hκ]; ring_nf

/-- `min 1 (c t / R)` form of a growth bound from a mass bound `c t / R` and total mass `≤ 1`. -/
theorem real_le_min_of_le {μ : Measure (Rd d)} [IsProbabilityMeasure μ] {s : Set (Rd d)}
    {b : ℝ} (hb : 0 ≤ b) (h : μ s ≤ ENNReal.ofReal b) : μ.real s ≤ min 1 b := by
  refine le_min ?_ ?_
  · rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  · rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hb h

/-- **Growth of a chord** (HA3 D4 (a), chord part): `ν_{[x,y]}(B̄(w,t)) ≤ min(1, 2t/|y - x|)`. -/
theorem segMeasure_growth {x y : Rd d} (hxy : x ≠ y) (w : Rd d) {t : ℝ} (ht : 0 < t) :
    (segMeasure x y).real (Metric.closedBall w t) ≤ min 1 (2 * t / ‖y - x‖) := by
  have hv : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hR : 0 < ‖y - x‖ := norm_pos_iff.2 hv
  have hproj : proj x (y - x) y - proj x (y - x) x = ‖y - x‖ := by
    rw [proj_sub, real_inner_self_eq_norm_sq]; field_simp
  refine real_le_min_of_le (by positivity) ?_
  refine (segMeasure_closedBall_le_proj x hv x y w t (by rw [hproj]; exact hR)).trans ?_
  rw [hproj]
  calc ENNReal.ofReal ‖y - x‖⁻¹ * volume.restrict (Icc (proj x (y - x) x) (proj x (y - x) y))
        (Icc (proj x (y - x) w - t) (proj x (y - x) w + t))
      ≤ ENNReal.ofReal ‖y - x‖⁻¹ * volume (Icc (proj x (y - x) w - t) (proj x (y - x) w + t)) := by
        gcongr
        exact Measure.restrict_le_self
    _ = ENNReal.ofReal (2 * t / ‖y - x‖) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (inv_nonneg.2 hR.le)]
        congr 1
        field_simp
        ring

/-- **Growth of a good polygon** (HA3 D4 (a), polygon part): for `z ∈ G_K(x, y)` and `x ≠ y`,
`ν_Q(B̄(w,t)) ≤ min(1, 3t/|y - x|)`.  (Only the forward condition is used: the projection on
the chord direction advances by at least `cos(1/10) ≥ 2/3` per unit of arclength.) -/
theorem goodFamily_growth {K : ℕ} {a₀ : ℝ} {x y : Rd d} {z : List (Rd d)}
    (hz : z ∈ goodFamily K a₀ x y) (hxy : x ≠ y) (w : Rd d) {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (polyMeasure z) ∧
      (polyMeasure z).real (Metric.closedBall w t) ≤ min 1 (3 * t / ‖y - x‖) := by
  have hlast := goodFamily_lastEdge hz hxy
  obtain ⟨V, hzV, hV0, hVK, hreg, hfwd, -⟩ := goodFamily_vertex hz
  have hv : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hR : 0 < ‖y - x‖ := norm_pos_iff.2 hv
  have hK : 1 ≤ K := by
    by_contra h
    have hK0 : K = 0 := by omega
    rw [hK0] at hVK
    exact hxy (hV0.symm.trans hVK)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  subst hzV
  -- every edge is nondegenerate
  have hℓpos : ∀ i < K, 0 < ‖V (i + 1) - V i‖ := by
    intro i hi
    by_cases hi' : i + 1 < K
    · rw [hreg i hi']; positivity
    · have hiK : i = K - 1 := by omega
      have := hlast (V (K - 1), V K) (by rw [getLast?_edges hK]; rfl)
      rw [hiK, Nat.sub_add_cancel hK]
      exact lt_of_lt_of_le (by positivity) this
  have hchord : V K - V 0 = y - x := by rw [hV0, hVK]
  have hS : 0 < plen V K := hR.trans_le (by rw [← hchord]; exact norm_sub_le_plen V K)
  have hRS : ‖y - x‖ ≤ plen V K := by rw [← hchord]; exact norm_sub_le_plen V K
  rw [polyMeasure_range_map]
  have hW0 : ∀ i < K, 0 ≤ ‖V (i + 1) - V i‖ / plen V K := fun i _ => by positivity
  have hprob : IsProbabilityMeasure (segSum K (fun i => ‖V (i + 1) - V i‖ / plen V K) V) := by
    constructor
    rw [segSum_univ V hW0, ← Finset.sum_div]
    change ENNReal.ofReal (plen V K / plen V K) = 1
    rw [div_self hS.ne', ENNReal.ofReal_one]
  refine ⟨hprob, real_le_min_of_le (by positivity) ?_⟩
  have hcos := two_thirds_le_cos_tenth
  -- projections advance by at least `cos(1/10) ℓ_i`
  have hadv : ∀ i < K, Real.cos (1 / 10) * ‖V (i + 1) - V i‖ ≤
      proj x (y - x) (V (i + 1)) - proj x (y - x) (V i) := by
    intro i hi
    rw [proj_sub, le_div_iff₀ hR]
    exact hfwd i hi
  refine (forward_growth (V := V) x hv (κ := 1 / (Real.cos (1 / 10) * plen V K))
    (by positivity) hW0 (fun i hi => ?_) (fun i hi => ?_) w t).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · exact lt_of_lt_of_le (mul_pos (by linarith) (hℓpos i hi)) (hadv i hi)
  · rw [div_le_iff₀ hS]
    have h1 := hadv i hi
    have e : 1 / (Real.cos (1 / 10) * plen V K) *
        (proj x (y - x) (V (i + 1)) - proj x (y - x) (V i)) * plen V K =
        (proj x (y - x) (V (i + 1)) - proj x (y - x) (V i)) / Real.cos (1 / 10) := by
      field_simp
    rw [e, le_div_iff₀ (by linarith)]
    linarith
  · -- `2 t / (cos(1/10) S) ≤ 3 t / R`
    have hcS : 0 < Real.cos (1 / 10) * plen V K := mul_pos (by linarith) hS
    rw [show 2 * (1 / (Real.cos (1 / 10) * plen V K)) * t =
      2 * t / (Real.cos (1 / 10) * plen V K) by ring, div_le_div_iff₀ hcS hR]
    have h1 : 2 * ‖y - x‖ ≤ 3 * (Real.cos (1 / 10) * plen V K) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 ht.le]

/-- **HA3 D4 (a)** in the `GrowthBound` form of (3.4): growth constant `3` at scale `|y - x|`. -/
theorem goodFamily_growthBound {K : ℕ} {a₀ : ℝ} {x y : Rd d} {z : List (Rd d)}
    (hz : z ∈ goodFamily K a₀ x y) (hxy : x ≠ y) :
    GrowthBound (polyMeasure z) 3 ‖y - x‖ := by
  intro w t ht
  refine (goodFamily_growth hz hxy w ht).2.trans ?_
  have hR : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  rcases le_total (t / ‖y - x‖) 1 with h | h
  · rw [min_eq_right h, mul_div_assoc]
    exact min_le_right _ _
  · rw [min_eq_left h]
    linarith [min_le_left (1 : ℝ) (3 * t / ‖y - x‖)]

/-- **HA3 D4 (a)**, chord part, in the `GrowthBound` form: growth constant `2` at scale
`|y - x|`. -/
theorem segMeasure_growthBound {x y : Rd d} (hxy : x ≠ y) :
    GrowthBound (segMeasure x y) 2 ‖y - x‖ := by
  intro w t ht
  refine (segMeasure_growth hxy w ht).trans ?_
  rcases le_total (t / ‖y - x‖) 1 with h | h
  · rw [min_eq_right h, mul_div_assoc]
    exact min_le_right _ _
  · rw [min_eq_left h]
    linarith [min_le_left (1 : ℝ) (2 * t / ‖y - x‖)]

end Growth

/-! ## Couplings (D4 (b)) -/

section Coupling

variable {d : ℕ}

/-- Splitting a chord: for parameters `0 = τ 0 ≤ τ 1 ≤ … ≤ τ m = 1`, the uniform measure on
`[a, b]` is the sum of the uniform measures on the pieces `[lin τ_i, lin τ_{i+1}]` with weights
`τ_{i+1} - τ_i`. -/
theorem segMeasure_lin (a b : Rd d) {σ τ : ℝ} (hστ : σ ≤ τ) :
    ENNReal.ofReal (τ - σ) • segMeasure (lin a b σ) (lin a b τ) =
      (volume.restrict (Icc σ τ)).map (lin a b) := by
  rcases eq_or_lt_of_le hστ with h | h
  · subst h
    simp
  · have haff : Measurable (fun s : ℝ => σ + s * (τ - σ)) := by fun_prop
    have e : (fun s : ℝ => lin a b σ + s • (lin a b τ - lin a b σ)) =
        lin a b ∘ (fun s : ℝ => σ + s * (τ - σ)) := by
      funext s
      simp only [lin, Function.comp]
      module
    have hpos : 0 < τ - σ := sub_pos.2 h
    rw [segMeasure, e, ← Measure.map_map (measurable_lin a b) haff,
      map_affine_restrict σ hpos, Measure.map_smul _ (measurable_lin a b).aemeasurable,
      smul_smul, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one,
      one_smul, add_sub_cancel]

theorem segMeasure_split (a b : Rd d) (τ : ℕ → ℝ) {m : ℕ} (hτ : ∀ i < m, τ i ≤ τ (i + 1))
    (h0 : τ 0 = 0) (hm : τ m = 1) :
    segMeasure a b = segSum m (fun i => τ (i + 1) - τ i) (fun i => lin a b (τ i)) := by
  rw [segSum]
  have h1 : ∀ i ∈ Finset.range m, ENNReal.ofReal (τ (i + 1) - τ i) •
      segMeasure (lin a b (τ i)) (lin a b (τ (i + 1))) =
      (volume.restrict (Icc (τ i) (τ (i + 1)))).map (lin a b) := fun i hi =>
    segMeasure_lin a b (hτ i (Finset.mem_range.1 hi))
  rw [Finset.sum_congr rfl h1, ← map_finsetSum_range (measurable_lin a b),
    sum_restrict_Icc τ hτ, h0, hm]
  rfl

/-- The pair of points with parameter `s` on `[a,b]` and `[a',b']`. -/
def pairSeg (a b a' b' : Rd d) (s : ℝ) : Rd d × Rd d := (lin a b s, lin a' b' s)

theorem measurable_pairSeg (a b a' b' : Rd d) : Measurable (pairSeg a b a' b') :=
  (measurable_lin a b).prodMk (measurable_lin a' b')

theorem norm_lin_sub_le {a b a' b' : Rd d} {u s : ℝ} (ha : ‖a - a'‖ ≤ u) (hb : ‖b - b'‖ ≤ u)
    (hs : s ∈ Icc (0 : ℝ) 1) : ‖lin a b s - lin a' b' s‖ ≤ u := by
  have e : lin a b s - lin a' b' s = (1 - s) • (a - a') + s • (b - b') := by
    simp only [lin, smul_sub, sub_smul, one_smul]; abel
  have h1 : 0 ≤ 1 - s := by linarith [hs.2]
  rw [e]
  calc _ ≤ ‖(1 - s) • (a - a')‖ + ‖s • (b - b')‖ := norm_add_le _ _
    _ = (1 - s) * ‖a - a'‖ + s * ‖b - b'‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1,
          abs_of_nonneg hs.1]
    _ ≤ (1 - s) * u + s * u := by gcongr; exact hs.1
    _ = u := by ring

/-- **Edgewise coupling** of two combinations with the same weights. -/
theorem coupled_segSum {m : ℕ} {W : ℕ → ℝ} {V V' : ℕ → Rd d} {u : ℝ}
    (hV : ∀ i ≤ m, ‖V i - V' i‖ ≤ u) :
    CoupledWithin (segSum m W V) (segSum m W V') u := by
  refine ⟨∑ i ∈ Finset.range m, ENNReal.ofReal (W i) •
    (volume.restrict (Icc (0 : ℝ) 1)).map (pairSeg (V i) (V (i + 1)) (V' i) (V' (i + 1))),
    ?_, ?_, ?_⟩
  · rw [map_finsetSum_range measurable_fst, segSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_map measurable_fst (measurable_pairSeg _ _ _ _)]
    rfl
  · rw [map_finsetSum_range measurable_snd, segSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.map_smul _ measurable_snd.aemeasurable,
      Measure.map_map measurable_snd (measurable_pairSeg _ _ _ _)]
    rfl
  · refine ae_finsetSum m _ fun i hi => ?_
    refine Measure.ae_smul_measure ?_ _
    rw [ae_map_iff (measurable_pairSeg _ _ _ _).aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact norm_lin_sub_le (hV i hi.le) (hV (i + 1) hi) hs

/-- If `|d| ≤ τ S` and `|d - v| ≤ (1 - τ) S`, then `d` is within `√(S² - |v|²)/2` of `τ v`
(2D `RecVar.vert_close`, with inner products). -/
theorem vert_close (dv v : Rd d) {τ S : ℝ} (h1 : ‖dv‖ ≤ τ * S) (h2 : ‖dv - v‖ ≤ (1 - τ) * S)
    (hS : ‖v‖ ≤ S) : ‖dv - τ • v‖ ^ 2 ≤ (S ^ 2 - ‖v‖ ^ 2) / 4 := by
  have hS0 : 0 ≤ S := (norm_nonneg _).trans hS
  have hX : 0 ≤ S ^ 2 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  rcases eq_or_lt_of_le hS0 with hS0' | hSpos
  · subst hS0'
    have hd : dv = 0 := norm_le_zero_iff.1 (by simpa using h1)
    have hv : v = 0 := norm_le_zero_iff.1 hS
    subst hd; subst hv; simp
  · have h0τ : 0 ≤ τ := by
      by_contra h; push Not at h; nlinarith [norm_nonneg dv]
    have h1τ : 0 ≤ 1 - τ := by
      by_contra h; push Not at h; nlinarith [norm_nonneg (dv - v)]
    have hid : ‖dv - τ • v‖ ^ 2 =
        (1 - τ) * ‖dv‖ ^ 2 + τ * ‖dv - v‖ ^ 2 - τ * (1 - τ) * ‖v‖ ^ 2 := by
      rw [norm_sub_sq_real dv (τ • v), norm_sub_sq_real dv v, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    have e1 : ‖dv‖ ^ 2 ≤ (τ * S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have e2 : ‖dv - v‖ ^ 2 ≤ ((1 - τ) * S) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have e3 : (1 - τ) * ‖dv‖ ^ 2 + τ * ‖dv - v‖ ^ 2 ≤
        (1 - τ) * (τ * S) ^ 2 + τ * ((1 - τ) * S) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left e1 h1τ) (mul_le_mul_of_nonneg_left e2 h0τ)
    rw [hid]
    nlinarith [mul_nonneg (sq_nonneg (τ - 1 / 2)) hX]

theorem plen_succ (V : ℕ → Rd d) (i : ℕ) : plen V (i + 1) = plen V i + ‖V (i + 1) - V i‖ :=
  Finset.sum_range_succ _ _

theorem norm_sub_le_plen_sub (V : ℕ → Rd d) {i m : ℕ} (hi : i ≤ m) :
    ‖V m - V i‖ ≤ plen V m - plen V i := by
  have e : V m - V i = ∑ j ∈ Finset.Ico i m, (V (j + 1) - V j) := by
    rw [Finset.sum_Ico_eq_sub _ hi, Finset.sum_range_sub, Finset.sum_range_sub]; abel
  rw [e, plen, plen, ← Finset.sum_Ico_eq_sub _ hi]
  exact norm_sum_le _ _

/-- **Coupling of a polygon with its chord** through normalized arclength (2D
`RecVar.coupled_poly`): vertex `i` of `V 0, …, V m` is coupled with the chord point of parameter
`plen V i / plen V m`, within `u` whenever `(S² - R²)/4 ≤ u²`. -/
theorem coupled_poly (V : ℕ → Rd d) {m : ℕ} (hS : 0 < plen V m) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : (plen V m ^ 2 - ‖V m - V 0‖ ^ 2) / 4 ≤ u ^ 2) :
    CoupledWithin (segMeasure (V 0) (V m)) (segSum m (fun i => ‖V (i + 1) - V i‖ / plen V m) V)
      u := by
  set S := plen V m with hSdef
  set τ : ℕ → ℝ := fun i => plen V i / S with hτdef
  have hτmono : ∀ i < m, τ i ≤ τ (i + 1) := fun i _ =>
    div_le_div_of_nonneg_right (by rw [plen_succ]; linarith [norm_nonneg (V (i + 1) - V i)])
      hS.le
  have hW : (fun i => τ (i + 1) - τ i) = fun i => ‖V (i + 1) - V i‖ / S := by
    funext i
    simp only [hτdef, plen_succ]
    ring
  have h0 : τ 0 = 0 := by simp [hτdef, plen]
  have h1 : τ m = 1 := div_self hS.ne'
  rw [segMeasure_split (V 0) (V m) τ hτmono h0 h1, hW]
  refine coupled_segSum fun i hi => ?_
  have hρS : ‖V m - V 0‖ ≤ S := by rw [hSdef, ← Finset.sum_range_sub V m]; exact norm_sum_le _ _
  have hτS : τ i * S = plen V i := div_mul_cancel₀ _ hS.ne'
  have hc := vert_close (V i - V 0) (V m - V 0) (τ := τ i) (S := S)
    (by
      rw [hτS, ← Finset.sum_range_sub V i]
      exact norm_sum_le _ _)
    (by
      rw [sub_mul, one_mul, hτS, show V i - V 0 - (V m - V 0) = -(V m - V i) by abel, norm_neg]
      exact norm_sub_le_plen_sub V hi)
    hρS
  have e : ‖lin (V 0) (V m) (τ i) - V i‖ = ‖V i - V 0 - τ i • (V m - V 0)‖ := by
    rw [← norm_neg]; congr 1; simp only [lin]; abel
  rw [e]
  have hsq : ‖V i - V 0 - τ i • (V m - V 0)‖ ^ 2 ≤ u ^ 2 := hc.trans hu
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hu0 two_ne_zero).1 hsq

/-- A good polygon `z ∈ G_K(x, y)` with `x ≠ y` has a probability normalized arclength. -/
theorem goodFamily_isProbabilityMeasure {K : ℕ} {a₀ : ℝ} {x y : Rd d} {z : List (Rd d)}
    (hz : z ∈ goodFamily K a₀ x y) (hxy : x ≠ y) : IsProbabilityMeasure (polyMeasure z) :=
  (goodFamily_growth hz hxy x one_pos).1

/-- **HA3 D4 (b)**: for `z ∈ G_K(x, y)` with threshold `a₀ ≤ 1` and `x ≠ y`, the chord measure
`ν_{[x,y]}` and the normalized arclength `ν_z` have a displacement coupling of size
`2 |y - x| √a`, `a = log(len z/|y - x|)` (normalized-arclength coupling). -/
theorem goodFamily_coupled {K : ℕ} {a₀ : ℝ} {x y : Rd d} {z : List (Rd d)}
    (hz : z ∈ goodFamily K a₀ x y) (hxy : x ≠ y) (ha₀ : a₀ ≤ 1) :
    CoupledWithin (segMeasure x y) (polyMeasure z)
      (2 * ‖y - x‖ * Real.sqrt (Real.log (polyLen z / ‖y - x‖))) := by
  obtain ⟨V, hzV, hV0, hVK, -, -, hpoly⟩ := goodFamily_vertex hz
  have hR : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have hchord : V K - V 0 = y - x := by rw [hV0, hVK]
  have hRS : ‖y - x‖ ≤ plen V K := by rw [← hchord]; exact norm_sub_le_plen V K
  have hS : 0 < plen V K := hR.trans_le hRS
  subst hzV
  rw [polyLen_range_map, polyMeasure_range_map]
  change CoupledWithin (segMeasure x y) _ (2 * ‖y - x‖ * Real.sqrt (Real.log (plen V K / ‖y - x‖)))
  -- the log excess `a ∈ [0, 1]`
  obtain ⟨a, ha⟩ : ∃ a, a = Real.log (plen V K / ‖y - x‖) := ⟨_, rfl⟩
  rw [← ha]
  have hSR : plen V K / ‖y - x‖ = Real.exp a := by rw [ha, Real.exp_log (div_pos hS hR)]
  have ha0 : 0 ≤ a := by rw [ha]; exact Real.log_nonneg ((one_le_div hR).2 hRS)
  have ha1 : a ≤ 1 := by
    have h1 : plen V K / ‖y - x‖ ≤ Real.exp a₀ := by rw [div_le_iff₀ hR]; exact hpoly
    rw [hSR] at h1
    linarith [Real.exp_le_exp.1 h1]
  have hSe : plen V K = Real.exp a * ‖y - x‖ := by rw [← hSR, div_mul_cancel₀ _ hR.ne']
  -- `e^{2a} - 1 ≤ 8 a`
  have he := exp_sub_one_le_two_mul ha0 ha1
  have he2 : Real.exp a ^ 2 - 1 ≤ 8 * a := by nlinarith [Real.exp_pos a]
  rw [← hV0, ← hVK]
  refine coupled_poly V hS (by positivity) ?_
  rw [hchord, hSe, mul_pow, mul_pow, mul_pow, Real.sq_sqrt ha0]
  nlinarith [sq_nonneg ‖y - x‖]

end Coupling

/-! ## The node variables as pairings with segment and polygon measures ((4.5)) -/

section NodeVariables

variable {d : ℕ}

theorem integrable_segMeasure {φ : Rd d → ℝ} (hφ : Continuous φ) (a b : Rd d) :
    Integrable φ (segMeasure a b) := by
  rw [segMeasure_eq, integrable_map_measure hφ.aestronglyMeasurable
    (measurable_lin a b).aemeasurable]
  exact (hφ.comp (continuous_const.add (continuous_id.smul continuous_const))).integrableOn_Icc

/-- `⟨φ, ν_{[a,b]}⟩ = segAvg φ a b`. -/
theorem integral_segMeasure {φ : Rd d → ℝ} (hφ : Continuous φ) (a b : Rd d) :
    ∫ z, φ z ∂(segMeasure a b) = segAvg φ a b := by
  rw [segMeasure_eq, integral_map (measurable_lin a b).aemeasurable hφ.aestronglyMeasurable,
    segAvg, intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rfl

theorem integral_segSum {φ : Rd d → ℝ} (hφ : Continuous φ) {m : ℕ} {W : ℕ → ℝ}
    (hW : ∀ i < m, 0 ≤ W i) (V : ℕ → Rd d) :
    ∫ z, φ z ∂(segSum m W V) = ∑ i ∈ Finset.range m, W i * segAvg φ (V i) (V (i + 1)) := by
  rw [segSum, integral_finsetSum_measure fun i _ =>
    (integrable_segMeasure hφ _ _).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_smul_measure, integral_segMeasure hφ,
    ENNReal.toReal_ofReal (hW i (Finset.mem_range.1 hi)), smul_eq_mul]

variable {T : CutTree} {γ : ℝ → Rd d} {K : ℕ} {ε ρ₀ : ℝ}

open TreeJensen

/-- `H_u = ⟨φ, ν_{I_u}⟩` as an integral against the chord measure. -/
theorem H_eq_integral (T : CutTree) (γ : ℝ → Rd d) {φ : Rd d → ℝ} (hφ : Continuous φ)
    (u : List ℕ) : T.H γ φ u = ∫ z, φ z ∂(segMeasure (T.x γ u) (T.y γ u)) :=
  (integral_segMeasure hφ _ _).symm

/-- **(4.5)**: `Σ_v p_{uv} H_v = ⟨φ, ν_{Q_u}⟩` for an internal node `u`. -/
theorem integral_polyMeasure_childPoly (hT : T.WF γ K ε ρ₀) {φ : Rd d → ℝ} (hφ : Continuous φ)
    {u : List ℕ} (hu : u ∈ T.nodes) :
    ∫ z, φ z ∂(polyMeasure (T.childPoly γ u)) =
      ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i]) := by
  rw [childPoly_eq, polyMeasure_range_map, integral_segSum hφ (fun i _ => by
    have := Finset.sum_nonneg (s := Finset.range (T.nch u))
      (fun j _ => norm_nonneg (γ (ctime T u (j + 1)) - γ (ctime T u j)))
    exact div_nonneg (norm_nonneg _) this)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [ctime_edge_norm hT hu hi', plen_ctime hT hu, CutTree.H, CutTree.x, CutTree.y,
    t₀_child hi', t₁_child hT hu hi']

/-- At a good node (`a_u ≤ a₀`), `G_u = -Δ_u = ⟨φ, ν_{I_u} - ν_{Q_u}⟩` ((4.5) and (4.9)). -/
theorem G_eq_of_good (hT : T.WF γ K ε ρ₀) {φ : Rd d → ℝ} (hφ : Continuous φ) {a₀ : ℝ}
    {u : List ℕ} (hu : u ∈ T.nodes) (hA : T.A γ u ≤ a₀) :
    T.G γ a₀ φ u = ∫ z, φ z ∂(segMeasure (T.x γ u) (T.y γ u)) -
      ∫ z, φ z ∂(polyMeasure (T.childPoly γ u)) := by
  rw [CutTree.G, ite_eq_left hA, integral_polyMeasure_childPoly hT hφ hu, H_eq_integral T γ hφ]

/-- At a bad node (`a_u > a₀`), `G_u = H_u - H_v` for some child `v` (the adverse child of §4.3),
i.e. `G_u = ⟨φ, ν_{I_u} - ν_{I_v}⟩`. -/
theorem G_eq_of_bad {φ : Rd d → ℝ} (hφ : Continuous φ) {a₀ : ℝ} {u : List ℕ}
    (hn : 0 < T.nch u) (hA : ¬ T.A γ u ≤ a₀) :
    ∃ i < T.nch u, T.G γ a₀ φ u =
      ∫ z, φ z ∂(segMeasure (T.x γ u) (T.y γ u)) -
        ∫ z, φ z ∂(segMeasure (T.x γ (u ++ [i])) (T.y γ (u ++ [i]))) := by
  have : Nonempty (Fin (T.nch u)) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite
    (f := fun i : Fin (T.nch u) => T.H γ φ u - T.H γ φ (u ++ [(i : ℕ)]))
  refine ⟨i, i.2, ?_⟩
  rw [CutTree.G, ite_eq_right hA, ← hi, H_eq_integral T γ hφ, H_eq_integral T γ hφ]

end NodeVariables

end HigherDimLFPP.Upper
