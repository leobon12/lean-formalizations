import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Order.SuccPred.IntervalSucc

/-!
# Riemann–Stieltjes sums of a force-point gap (deterministic layer of Theorem 2.4)

Packet PROVE-SEC2-MART. Specification, proof of Theorem 2.4 (`source/spec/p001-048.md`,
anchor `thm-2.4-proof`, L834–L854): a geometric force-point image `V` is continuous and monotone,
and away from the collision set `Z = {V = W}` it solves the Loewner equation `dV = 2/(V − W) dt`;
the collision set is Lebesgue-null (Lemma 2.5). The identification of the quadratic variation of the
driver uses the Stieltjes identity

  `∫_a^b (V − W) dV = 2 (b − a)`,

which this file proves in the form needed by the discrete martingale argument: Riemann–Stieltjes
sums along partitions of small mesh converge.

## Main results

* `sum_abs_sub_eq_of_monotoneOn_or_antitoneOn`: the variation of a monotone path along a partition
  telescopes to `|v b − v a|`;
* `exists_delta_abs_sum_gap_mul_sub_sub_le`: for `v, w` continuous on `[a, b]`, `v` monotone, with
  `v' = 2/(v − w)` at every interior point where `v ≠ w` and a Lebesgue-null collision set,
  `|∑ₖ (v(pₖ) − w(pₖ)) (v(pₖ₊₁) − v(pₖ)) − 2 (b − a)| ≤ ε` for every partition `p` of `[a, b]`
  of mesh `< δ(ε)`;
* `exists_delta_abs_sub_lt`: uniform continuity along partitions (increments `< η` for small mesh),
  which makes the sums `∑ Δf Δg` vanish for `g` monotone.

## Proof

Split the cells of the partition. On a cell `[α, β]` without collision, `v` is `C¹` with
`v' = 2/e`, `e = v − w`, of constant sign, so `e(α) Δv − 2 Δp = ∫ 2 (e(α) − e(u))/e(u) du` is at
most `osc · |Δv|`. A cell that meets the collision set has `|e(α)| ≤ osc` and lies in the closed
`δ`-thickening of the compact collision set, whose measure tends to `0` with `δ`
(`tendsto_measure_cthickening_of_isCompact`). Summing, the error is at most
`osc · |v b − v a| + 2 |cthickening δ Z|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace InteractingSLE

namespace MartChar

/-! ### Partitions and the variation of a monotone path -/

section Partition

variable {a b : ℝ} {n : ℕ} {p : ℕ → ℝ}

lemma mem_Icc_of_partition (hp : Monotone p) (h0 : p 0 = a) (hn : p n = b) {k : ℕ} (hk : k ≤ n) :
    p k ∈ Icc a b :=
  ⟨h0 ▸ hp (Nat.zero_le k), hn ▸ hp hk⟩

lemma le_of_partition (hp : Monotone p) (h0 : p 0 = a) (hn : p n = b) : a ≤ b :=
  h0 ▸ hn ▸ hp (Nat.zero_le n)

lemma Icc_cell_subset (hp : Monotone p) (h0 : p 0 = a) (hn : p n = b) {k : ℕ} (hk : k < n) :
    Icc (p k) (p (k + 1)) ⊆ Icc a b :=
  Icc_subset_Icc (mem_Icc_of_partition hp h0 hn hk.le).1 (mem_Icc_of_partition hp h0 hn hk).2

lemma sum_sub_partition (hn' : p n = b) (h0 : p 0 = a) :
    ∑ k ∈ Finset.range n, (p (k + 1) - p k) = b - a := by
  rw [Finset.sum_range_sub p, hn', h0]

/-- The variation of a monotone path along a partition telescopes. -/
lemma sum_abs_sub_eq_of_monotoneOn {v : ℝ → ℝ} (hv : MonotoneOn v (Icc a b)) (hp : Monotone p)
    (h0 : p 0 = a) (hn : p n = b) :
    ∑ k ∈ Finset.range n, |v (p (k + 1)) - v (p k)| = |v b - v a| := by
  have hab := le_of_partition hp h0 hn
  have hnn : ∀ k ∈ Finset.range n, 0 ≤ v (p (k + 1)) - v (p k) := fun k hk => by
    have hk' := Finset.mem_range.1 hk
    exact sub_nonneg.2 (hv (mem_Icc_of_partition hp h0 hn hk'.le)
      (mem_Icc_of_partition hp h0 hn hk') (hp (Nat.le_succ k)))
  rw [Finset.sum_congr rfl fun k hk => abs_of_nonneg (hnn k hk),
    Finset.sum_range_sub (fun k => v (p k)), h0, hn,
    abs_of_nonneg (sub_nonneg.2 (hv ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab))]

lemma sum_abs_sub_eq_of_monotoneOn_or_antitoneOn {v : ℝ → ℝ}
    (hv : MonotoneOn v (Icc a b) ∨ AntitoneOn v (Icc a b)) (hp : Monotone p) (h0 : p 0 = a)
    (hn : p n = b) :
    ∑ k ∈ Finset.range n, |v (p (k + 1)) - v (p k)| = |v b - v a| := by
  rcases hv with hv | hv
  · exact sum_abs_sub_eq_of_monotoneOn hv hp h0 hn
  · have h := sum_abs_sub_eq_of_monotoneOn (v := fun x => -v x) hv.neg hp h0 hn
    simpa only [neg_sub_neg, abs_sub_comm] using h

/-- Uniform continuity along partitions: the increments of a continuous path along a partition of
small mesh are uniformly small. -/
lemma exists_delta_abs_sub_lt {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |x - y| < δ → |f x - f y| < η := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.1 hu η hη
  exact ⟨δ, hδ, fun x hx y hy hxy => h x hx y hy hxy⟩

/-- `∑ₖ Δf Δg` is at most `η ∑ₖ |Δg|` when every increment of `f` is at most `η`. -/
lemma abs_sum_mul_le {f g : ℕ → ℝ} {η : ℝ} (hf : ∀ k < n, |f k| ≤ η) :
    |∑ k ∈ Finset.range n, f k * g k| ≤ η * ∑ k ∈ Finset.range n, |g k| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hf k (Finset.mem_range.1 hk)) (abs_nonneg _)

end Partition

/-! ### One cell -/

section Cell

variable {v w : ℝ → ℝ} {α β η : ℝ}

/-- A continuous function without zeros on `[α, β]` has the sign of its value at `α`. -/
lemma pos_of_pos_of_ne_zero {e : ℝ → ℝ} (he : ContinuousOn e (Icc α β))
    (hne : ∀ u ∈ Icc α β, e u ≠ 0) (hα : 0 < e α) : ∀ u ∈ Icc α β, 0 < e u := by
  intro u hu
  by_contra hneg
  have hlt : e u < 0 := lt_of_le_of_ne (not_lt.1 hneg) (hne u hu)
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hu.1 (he.mono (Icc_subset_Icc le_rfl hu.2))
    ⟨hlt.le, hα.le⟩
  exact hne c ⟨hc.1, hc.2.trans hu.2⟩ hc0

/-- **A collision-free cell.** If `v` solves `v' = 2/(v − w)` on `(α, β)` and `v ≠ w` on
`[α, β]`, then `|(v α − w α) Δv − 2 (β − α)| ≤ η |Δv|`, where `η` bounds the oscillation of
`v − w` against its value at `α`. -/
lemma abs_gap_mul_sub_sub_le_of_ne (hαβ : α ≤ β) (hv : ContinuousOn v (Icc α β))
    (hw : ContinuousOn w (Icc α β)) (hne : ∀ u ∈ Icc α β, v u ≠ w u)
    (hderiv : ∀ u ∈ Ioo α β, HasDerivAt v (2 / (v u - w u)) u)
    (hosc : ∀ u ∈ Icc α β, |(v α - w α) - (v u - w u)| ≤ η) :
    |(v α - w α) * (v β - v α) - 2 * (β - α)| ≤ η * |v β - v α| := by
  set e : ℝ → ℝ := fun u => v u - w u with he_def
  have he : ContinuousOn e (Icc α β) := hv.sub hw
  have he0 : ∀ u ∈ Icc α β, e u ≠ 0 := fun u hu => sub_ne_zero.2 (hne u hu)
  have hcont2 : ContinuousOn (fun u => 2 / e u) (Icc α β) :=
    continuousOn_const.div he he0
  have hint2 : IntervalIntegrable (fun u => 2 / e u) volume α β :=
    (hcont2.mono (by rw [uIcc_of_le hαβ])).intervalIntegrable
  have hftc : ∫ u in α..β, 2 / e u = v β - v α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hαβ hv hderiv hint2
  -- the integrand of the error
  set g : ℝ → ℝ := fun u => 2 * (e α - e u) / e u with hg_def
  have hgcont : ContinuousOn g (Icc α β) :=
    (continuousOn_const.mul (continuousOn_const.sub he)).div he he0
  have hgint : IntervalIntegrable g volume α β :=
    (hgcont.mono (by rw [uIcc_of_le hαβ])).intervalIntegrable
  have herr : e α * (v β - v α) - 2 * (β - α) = ∫ u in α..β, g u := by
    have hg_eq : ∀ u ∈ uIcc α β, g u = e α * (2 / e u) - 2 := by
      intro u hu
      rw [uIcc_of_le hαβ] at hu
      have := he0 u hu
      simp only [hg_def]
      field_simp
    rw [intervalIntegral.integral_congr hg_eq, intervalIntegral.integral_sub
      (hint2.const_mul (e α)) intervalIntegrable_const, intervalIntegral.integral_const_mul,
      hftc, intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- `|g| ≤ η |2/e|` and `∫ |2/e| = |Δv|`
  have hnn : 0 ≤ ∫ u in α..β, |2 / e u| :=
    intervalIntegral.integral_nonneg hαβ fun u _ => abs_nonneg _
  have habs2 : ∫ u in α..β, |2 / e u| = |v β - v α| := by
    rcases lt_or_gt_of_ne (he0 α ⟨le_rfl, hαβ⟩) with hneg | hpos
    · have hneg' : ∀ u ∈ Icc α β, e u < 0 := by
        have h := pos_of_pos_of_ne_zero (e := fun u => -e u) he.neg
          (fun u hu => neg_ne_zero.2 (he0 u hu)) (neg_pos.2 hneg)
        exact fun u hu => neg_pos.1 (h u hu)
      have hcongr : ∀ u ∈ uIcc α β, |2 / e u| = -(2 / e u) := by
        intro u hu
        rw [uIcc_of_le hαβ] at hu
        exact abs_of_neg (div_neg_of_pos_of_neg two_pos (hneg' u hu))
      have h1 : ∫ u in α..β, |2 / e u| = -(v β - v α) := by
        rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_neg, hftc]
      rw [h1, abs_of_nonpos (by linarith)]
    · have hpos' := pos_of_pos_of_ne_zero he he0 hpos
      have hcongr : ∀ u ∈ uIcc α β, |2 / e u| = 2 / e u := by
        intro u hu
        rw [uIcc_of_le hαβ] at hu
        exact abs_of_pos (div_pos two_pos (hpos' u hu))
      have h1 : ∫ u in α..β, |2 / e u| = v β - v α := by
        rw [intervalIntegral.integral_congr hcongr, hftc]
      rw [h1, abs_of_nonneg (by linarith)]
  have hmono : ∫ u in α..β, |g u| ≤ ∫ u in α..β, η * |2 / e u| := by
    refine intervalIntegral.integral_mono_on hαβ hgint.abs (hint2.abs.const_mul η) fun u hu => ?_
    have hgu : g u = (e α - e u) * (2 / e u) := by
      simp only [hg_def]
      ring
    rw [hgu, abs_mul]
    exact mul_le_mul_of_nonneg_right (hosc u hu) (abs_nonneg _)
  calc |(v α - w α) * (v β - v α) - 2 * (β - α)| = |∫ u in α..β, g u| := by rw [← herr]
    _ ≤ ∫ u in α..β, |g u| := intervalIntegral.abs_integral_le_integral_abs hαβ
    _ ≤ ∫ u in α..β, η * |2 / e u| := hmono
    _ = η * |v β - v α| := by rw [intervalIntegral.integral_const_mul, habs2]

end Cell

/-! ### The Riemann–Stieltjes limit -/

section Limit

variable {v w : ℝ → ℝ} {a b : ℝ}

/-- **Riemann–Stieltjes sums of the gap.** Let `v, w` be continuous on `[a, b]`, `v` monotone, with
`v' = 2/(v − w)` at every interior point where `v ≠ w`, and suppose the collision set
`{u ∈ [a, b] : v u = w u}` is Lebesgue-null. Then the sums
`∑ₖ (v(pₖ) − w(pₖ)) (v(pₖ₊₁) − v(pₖ))` along partitions `p` of `[a, b]` converge to
`2 (b − a)` as the mesh tends to `0` (Specification, proof of Theorem 2.4: `∫ (V − W) dV = 2 dt`). -/
theorem exists_delta_abs_sum_gap_mul_sub_sub_le (hv : ContinuousOn v (Icc a b))
    (hw : ContinuousOn w (Icc a b)) (hmono : MonotoneOn v (Icc a b) ∨ AntitoneOn v (Icc a b))
    (hderiv : ∀ u ∈ Ioo a b, v u ≠ w u → HasDerivAt v (2 / (v u - w u)) u)
    (hnull : volume {u ∈ Icc a b | v u = w u} = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (p : ℕ → ℝ), Monotone p → p 0 = a → p n = b →
      (∀ k < n, p (k + 1) - p k < δ) →
      |(∑ k ∈ Finset.range n, (v (p k) - w (p k)) * (v (p (k + 1)) - v (p k))) - 2 * (b - a)|
        ≤ ε := by
  classical
  set Z : Set ℝ := {u ∈ Icc a b | v u = w u} with hZ_def
  have hZc : IsCompact Z := by
    have hcl : IsClosed (Icc a b ∩ (fun u => v u - w u) ⁻¹' {0}) :=
      (hv.sub hw).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hZeq : Z = Icc a b ∩ (fun u => v u - w u) ⁻¹' {0} := by
      ext u
      simp only [hZ_def, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, sub_eq_zero]
    rw [hZeq]
    exact isCompact_Icc.of_isClosed_subset hcl inter_subset_left
  -- a thickening of small measure
  have hlim := tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure ℝ)) hZc
  rw [hnull] at hlim
  have hε4 : (0 : ENNReal) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨r, hr, hrZ⟩ : ∃ r > 0, volume (cthickening r Z) < ENNReal.ofReal (ε / 4) := by
    have hev := (tendsto_order.1 hlim).2 _ hε4
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨r / 2, half_pos hr, hball ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    exact half_lt_self hr
  -- uniform continuity of the gap
  set V : ℝ := |v b - v a|
  set η : ℝ := ε / (2 * (V + 1)) with hη_def
  have hV : 0 ≤ V := abs_nonneg _
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ₁, hδ₁, hosc⟩ := exists_delta_abs_sub_lt (hv.sub hw) hη
  refine ⟨min δ₁ r, lt_min hδ₁ hr, fun n p hp h0 hn hmesh => ?_⟩
  have hab := le_of_partition hp h0 hn
  -- per-cell data
  set bad : ℕ → Prop := fun k => ∃ c ∈ Icc (p k) (p (k + 1)), v c = w c with hbad_def
  have hcell : ∀ k < n, |(v (p k) - w (p k)) * (v (p (k + 1)) - v (p k)) - 2 * (p (k + 1) - p k)|
      ≤ η * |v (p (k + 1)) - v (p k)| + (if bad k then 2 * (p (k + 1) - p k) else 0) := by
    intro k hk
    have hsub := Icc_cell_subset hp h0 hn hk
    have hαβ : p k ≤ p (k + 1) := hp (Nat.le_succ k)
    have hosc' : ∀ u ∈ Icc (p k) (p (k + 1)), |(v (p k) - w (p k)) - (v u - w u)| ≤ η := by
      intro u hu
      refine (hosc (p k) (hsub ⟨le_rfl, hαβ⟩) u (hsub hu) ?_).le
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hu.1)]
      exact lt_of_le_of_lt (sub_le_sub_right hu.2 _) ((hmesh k hk).trans_le (min_le_left _ _))
    by_cases hb : bad k
    · obtain ⟨c, hc, hvc⟩ := hb
      rw [ite_eq_left ⟨c, hc, hvc⟩]
      have he : |v (p k) - w (p k)| ≤ η := by
        have := hosc' c hc
        rwa [hvc, sub_self, sub_zero] at this
      have hdp : 0 ≤ p (k + 1) - p k := sub_nonneg.2 hαβ
      calc |(v (p k) - w (p k)) * (v (p (k + 1)) - v (p k)) - 2 * (p (k + 1) - p k)|
          ≤ |(v (p k) - w (p k)) * (v (p (k + 1)) - v (p k))| + |2 * (p (k + 1) - p k)| :=
            abs_sub _ _
        _ = |v (p k) - w (p k)| * |v (p (k + 1)) - v (p k)| + 2 * (p (k + 1) - p k) := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (p (k + 1) - p k))]
        _ ≤ η * |v (p (k + 1)) - v (p k)| + 2 * (p (k + 1) - p k) := by
            gcongr
    · rw [ite_eq_right hb, add_zero]
      have hne : ∀ u ∈ Icc (p k) (p (k + 1)), v u ≠ w u := fun u hu hvu => hb ⟨u, hu, hvu⟩
      refine abs_gap_mul_sub_sub_le_of_ne hαβ (hv.mono hsub) (hw.mono hsub) hne
        (fun u hu => hderiv u ?_ (hne u (Ioo_subset_Icc_self hu))) hosc'
      exact ⟨(hsub ⟨le_rfl, hαβ⟩).1.trans_lt hu.1, hu.2.trans_le (hsub ⟨hαβ, le_rfl⟩).2⟩
  -- the bad cells have small total length
  set S := (Finset.range n).filter bad with hS_def
  have hbadsum : ∑ k ∈ S, (p (k + 1) - p k) < ε / 4 := by
    have hnn : ∀ k ∈ S, 0 ≤ p (k + 1) - p k := fun k _ => sub_nonneg.2 (hp (Nat.le_succ k))
    have hdisj : PairwiseDisjoint (↑S) fun k => Ico (p k) (p (k + 1)) := by
      intro i _ j _ hij
      exact hp.pairwise_disjoint_on_Ico_succ hij
    have hsubset : (⋃ k ∈ S, Ico (p k) (p (k + 1))) ⊆ cthickening r Z := by
      intro u hu
      simp only [mem_iUnion] at hu
      obtain ⟨k, hk, hu⟩ := hu
      obtain ⟨hkn, c, hc, hvc⟩ := Finset.mem_filter.1 hk
      have hkn' := Finset.mem_range.1 hkn
      have hcZ : c ∈ Z := ⟨Icc_cell_subset hp h0 hn hkn' hc, hvc⟩
      refine Metric.mem_cthickening_of_dist_le u c r Z hcZ ?_
      rw [Real.dist_eq]
      have h1 : |u - c| ≤ p (k + 1) - p k := by
        rw [abs_le]
        constructor <;> linarith [hu.1, hu.2, hc.1, hc.2]
      exact h1.trans ((hmesh k hkn').le.trans (min_le_right _ _))
    have hmeas : ENNReal.ofReal (∑ k ∈ S, (p (k + 1) - p k)) < ENNReal.ofReal (ε / 4) := by
      rw [ENNReal.ofReal_sum_of_nonneg hnn]
      calc ∑ k ∈ S, ENNReal.ofReal (p (k + 1) - p k)
          = ∑ k ∈ S, volume (Ico (p k) (p (k + 1))) := by
            simp only [Real.volume_Ico]
        _ = volume (⋃ k ∈ S, Ico (p k) (p (k + 1))) :=
            (measure_biUnion_finset hdisj fun k _ => measurableSet_Ico).symm
        _ ≤ volume (cthickening r Z) := measure_mono hsubset
        _ < ENNReal.ofReal (ε / 4) := hrZ
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hmeas
  -- summation
  have hvar := sum_abs_sub_eq_of_monotoneOn_or_antitoneOn hmono hp h0 hn
  have hsplit : (∑ k ∈ Finset.range n, (v (p k) - w (p k)) * (v (p (k + 1)) - v (p k)))
      - 2 * (b - a) = ∑ k ∈ Finset.range n,
        ((v (p k) - w (p k)) * (v (p (k + 1)) - v (p k)) - 2 * (p (k + 1) - p k)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_sub_partition hn h0]
  have hsum : ∑ k ∈ Finset.range n, (η * |v (p (k + 1)) - v (p k)|
      + (if bad k then 2 * (p (k + 1) - p k) else 0)) = η * V + 2 * ∑ k ∈ S, (p (k + 1) - p k) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hvar, hS_def, Finset.sum_filter, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> ring
  have hηV : η * V ≤ ε / 2 := by
    rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) two_pos]
    nlinarith
  rw [hsplit]
  calc |∑ k ∈ Finset.range n,
        ((v (p k) - w (p k)) * (v (p (k + 1)) - v (p k)) - 2 * (p (k + 1) - p k))|
      ≤ ∑ k ∈ Finset.range n,
        |(v (p k) - w (p k)) * (v (p (k + 1)) - v (p k)) - 2 * (p (k + 1) - p k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (η * |v (p (k + 1)) - v (p k)|
        + (if bad k then 2 * (p (k + 1) - p k) else 0)) :=
        Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.1 hk)
    _ = η * V + 2 * ∑ k ∈ S, (p (k + 1) - p k) := hsum
    _ ≤ ε := by linarith

end Limit

end MartChar

end InteractingSLE
