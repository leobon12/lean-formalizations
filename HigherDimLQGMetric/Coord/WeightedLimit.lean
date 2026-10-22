import HigherDimLQGMetric.Coord.CurveLimit
import HigherDimLQGMetric.Coord.Compactness
import HigherDimLQGMetric.Metric.WeightedLength
import Mathlib.Topology.Order.Compact

/-!
# Weighted lower semicontinuity for varying coordinate distances

The weighted part of MA1 Lemma CC is reduced to convergence of the infimum of the
weight on each fixed time interval and lower semicontinuity of ordinary length.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

/-- The minimum of a continuous real function on a compact parameter space varies
continuously under uniform convergence. -/
private theorem tendsto_iInf_boundedContinuousFunction
    {T ι : Type*} [TopologicalSpace T] [CompactSpace T]
    {l : Filter ι} {F : ι → T →ᵇ ℝ} {f : T →ᵇ ℝ}
    (h : Tendsto F l (𝓝 f)) :
    Tendsto (fun i => ⨅ t : T, F i t) l (𝓝 (⨅ t : T, f t)) := by
  have hc : Continuous (fun g : T →ᵇ ℝ => ⨅ t : T, g t) := by
    have hEval : Continuous (fun p : (T →ᵇ ℝ) × T => p.1 p.2) :=
      ContinuousEval.continuous_eval
    have hmin := (isCompact_univ (X := T)).continuous_sInf
      (f := fun g : T →ᵇ ℝ => fun t : T => g t) hEval
    change Continuous (fun g : T →ᵇ ℝ => sInf (range fun t : T => g t))
    simpa only [Set.image_univ] using hmin
  exact (hc.tendsto f).comp h

/-- Restricting uniformly convergent continuous functions to a closed subinterval preserves
convergence of their minima. -/
private theorem tendsto_iInf_subinterval
    {a b c d : ℝ} (hac : a ≤ c) (_hcd : c ≤ d) (hdb : d ≤ b)
    {ι : Type*} {l : Filter ι} {F : ι → Icc a b →ᵇ ℝ} {f : Icc a b →ᵇ ℝ}
    (hF : Tendsto F l (𝓝 f)) :
    Tendsto (fun i => ⨅ t : Icc c d,
        F i (⟨t.val, hac.trans t.property.1, t.property.2.trans hdb⟩ : Icc a b)) l
      (𝓝 (⨅ t : Icc c d,
        f (⟨t.val, hac.trans t.property.1, t.property.2.trans hdb⟩ : Icc a b))) := by
  let e : Icc c d → Icc a b := fun t =>
    ⟨t.val, hac.trans t.property.1, t.property.2.trans hdb⟩
  have he : Continuous e := by
    exact Continuous.subtype_mk continuous_subtype_val _
  let v : ι → Icc c d →ᵇ ℝ := fun i =>
    mkOfCompact ((F i).toContinuousMap.comp ⟨e, he⟩)
  let g : Icc c d →ᵇ ℝ := mkOfCompact (f.toContinuousMap.comp ⟨e, he⟩)
  have hvg : Tendsto v l (𝓝 g) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    exact (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hF).comp e
  exact tendsto_iInf_boundedContinuousFunction hvg

/-- The `infAlong` factor in each weighted partition piece converges for uniformly
converging curves in a compact common image. -/
theorem coordinate_infAlong_tendsto
    {X : Type*} [MetricSpace X] {L : Set X} (hL : IsCompact L)
    (w : X → ℝ) (hw : ContinuousOn w L)
    {a b : ℝ} (hab : a ≤ b)
    (u : ℕ → Icc a b →ᵇ X) (f : Icc a b →ᵇ X)
    (φ : ℕ → ℕ) (huL : ∀ n t, u n t ∈ L) (hfL : ∀ t, f t ∈ L)
    (hlim : TendstoUniformly (fun n t => u (φ n) t) f atTop)
    {c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    Tendsto (fun n => infAlong w (Set.IccExtend hab (u (φ n))) c d) atTop
      (𝓝 (infAlong w (Set.IccExtend hab f) c d)) := by
  have hcont (n : ℕ) : Continuous (fun t : Icc a b => w (u (φ n) t)) :=
    hw.comp_continuous (u (φ n)).continuous (fun t => huL (φ n) t)
  have hcont₀ : Continuous (fun t : Icc a b => w (f t)) :=
    hw.comp_continuous f.continuous hfL
  let V : ℕ → Icc a b →ᵇ ℝ := fun n => mkOfCompact
    ⟨fun t => w (u (φ n) t), hcont n⟩
  let V₀ : Icc a b →ᵇ ℝ := mkOfCompact ⟨fun t => w (f t), hcont₀⟩
  have hV : Tendsto V atTop (𝓝 V₀) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    exact coordinate_weight_tendstoUniformly hL w hw u f φ huL hfL hlim
  have hmin := tendsto_iInf_subinterval hac hcd hdb hV
  have hrepr (g : Icc a b →ᵇ X) :
      infAlong w (Set.IccExtend hab g) c d =
        ENNReal.ofReal (⨅ t : Icc c d,
          w (g (⟨t.val, hac.trans t.property.1, t.property.2.trans hdb⟩ : Icc a b))) := by
    rw [← ofReal_iInf_eq_infAlong hcd]
    congr 1
    apply iInf_congr
    intro t
    rw [Set.IccExtend_of_mem (h := hab) _
      (⟨hac.trans t.property.1, t.property.2.trans hdb⟩ : t.val ∈ Icc a b)]
  rw [hrepr]
  simp_rw [hrepr]
  exact ENNReal.tendsto_ofReal hmin

variable {X : Type*} {ι : Type*} {l : Filter ι}
  {δ : X → X → ℝ≥0∞} {δi : ι → X → X → ℝ≥0∞}
  {P : ℝ → X} {Pi : ι → ℝ → X} {w : X → ℝ} {a b : ℝ}

private theorem ennreal_le_liminf_add (F G : ι → ℝ≥0∞) :
    liminf F l + liminf G l ≤ liminf (fun i => F i + G i) l := by
  let S : Set ℝ≥0∞ := {a | ∀ᶠ i in l, a ≤ F i}
  let T : Set ℝ≥0∞ := {a | ∀ᶠ i in l, a ≤ G i}
  have hS : S.Nonempty := ⟨0, Eventually.of_forall fun i => bot_le⟩
  have hT : T.Nonempty := ⟨0, Eventually.of_forall fun i => bot_le⟩
  change sSup S + sSup T ≤ liminf (fun i => F i + G i) l
  rw [ENNReal.sSup_add hS]
  refine iSup_le fun x => iSup_le fun hx => ?_
  rw [ENNReal.add_sSup hT]
  refine iSup_le fun y => iSup_le fun hy => ?_
  exact Filter.le_liminf_of_le (by isBoundedDefault)
    ((hx.and hy).mono fun i hi => add_le_add hi.1 hi.2)

variable [l.NeBot]

/-- Finite sums preserve the lower liminf inequality in `ENNReal`. -/
private theorem finset_sum_le_liminf {α : Type*} (s : Finset α)
    (F : α → ι → ℝ≥0∞) (G : α → ℝ≥0∞)
    (h : ∀ j ∈ s, G j ≤ liminf (F j) l) :
    (∑ j ∈ s, G j) ≤ liminf (fun i => ∑ j ∈ s, F j i) l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      calc
        G j + ∑ k ∈ s, G k ≤ liminf (F j) l +
            liminf (fun i => ∑ k ∈ s, F k i) l := by
          exact add_le_add (h j (Finset.mem_insert_self _ _))
            (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))
        _ ≤ liminf (fun i => F j i + ∑ k ∈ s, F k i) l :=
          ennreal_le_liminf_add _ _

/-- Lower semicontinuity of weighted length from its fixed-partition terms. -/
theorem weightedLengthWith_le_liminf_of_piecewise
    (hweight : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      Tendsto (fun i => infAlong w (Pi i) s t) l (𝓝 (infAlong w P s t)))
    (hlength : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b →
      curveLengthWith δ P s t ≤
        liminf (fun i => curveLengthWith (δi i) (Pi i) s t) l) :
    weightedLengthWith δ w P a b ≤
      liminf (fun i => weightedLengthWith (δi i) w (Pi i) a b) l := by
  unfold weightedLengthWith
  refine partitionSup_le fun p => ?_
  have hsum : p.sum (fun s t => infAlong w P s t * curveLengthWith δ P s t) ≤
      liminf (fun i => p.sum (fun s t =>
        infAlong w (Pi i) s t * curveLengthWith (δi i) (Pi i) s t)) l := by
    unfold IccPartition.sum
    apply finset_sum_le_liminf
    intro j hj
    have hstep := p.step (Finset.mem_range.mp hj)
    calc
      infAlong w P (p.t j) (p.t (j + 1)) *
          curveLengthWith δ P (p.t j) (p.t (j + 1)) ≤
          liminf (fun i => infAlong w (Pi i) (p.t j) (p.t (j + 1))) l *
          liminf (fun i => curveLengthWith (δi i) (Pi i) (p.t j) (p.t (j + 1))) l := by
        rw [(hweight _ _ hstep.1 hstep.2.1 hstep.2.2).liminf_eq]
        exact mul_le_mul' le_rfl (hlength _ _ hstep.1 hstep.2.1 hstep.2.2)
      _ ≤ liminf (fun i => infAlong w (Pi i) (p.t j) (p.t (j + 1)) *
          curveLengthWith (δi i) (Pi i) (p.t j) (p.t (j + 1))) l := ENNReal.le_liminf_mul
  calc
    p.sum (fun s t => infAlong w P s t * curveLengthWith δ P s t) ≤ _ := hsum
    _ ≤ liminf (fun i => partitionSup (fun s t =>
        infAlong w (Pi i) s t * curveLengthWith (δi i) (Pi i) s t) a b) l :=
      Filter.liminf_le_liminf (Eventually.of_forall fun i => le_partitionSup p)

/-- Weighted lower semicontinuity in MA1 Lemma CC, on every subinterval of the
parameter interval. -/
theorem coordinate_weightedLength_le_liminf
    {Y : Type*} [MetricSpace Y] {L : Set Y} (hL : IsCompact L)
    {ρ : Y × Y → ℝ} {ρi : ℕ → Y × Y → ℝ}
    {a b : ℝ} (hab : a ≤ b) (hρ : ContinuousOn ρ (L ×ˢ L))
    (hρi : TendstoUniformlyOn ρi ρ atTop (L ×ˢ L))
    (u : ℕ → Icc a b →ᵇ Y) (f : Icc a b →ᵇ Y)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (huL : ∀ n t, u n t ∈ L) (hfL : ∀ t, f t ∈ L)
    (hlim : TendstoUniformly (fun n t => u (φ n) t) f atTop)
    (w : Y → ℝ) (hw : ContinuousOn w L)
    {c d : ℝ} (hac : a ≤ c) (_hcd : c ≤ d) (hdb : d ≤ b) :
    weightedLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) w
        (Set.IccExtend hab f) c d ≤
      liminf (fun n => weightedLengthWith
        (fun x y => ENNReal.ofReal (ρi (φ n) (x, y))) w
        (Set.IccExtend hab (u (φ n))) c d) atTop := by
  apply weightedLengthWith_le_liminf_of_piecewise
  · intro s t hcs hst htd
    exact coordinate_infAlong_tendsto hL w hw hab u f φ huL hfL hlim
      (hac.trans hcs) hst (htd.trans hdb)
  · intro s t hcs hst htd
    exact coordinate_curveLength_le_liminf hab hρ hρi u f φ hφ huL hfL hlim
      (hac.trans hcs) hst (htd.trans hdb)

end HigherDimLQGMetric
