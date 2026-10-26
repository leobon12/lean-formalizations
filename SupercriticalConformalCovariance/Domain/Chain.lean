import HigherDimLQGMetric.Metric.Reparam

/-!
# Chain rule for weighted lengths in an extended pseudometric space

For a pseudo-extended-metric space `X`, an open `S ⊆ X`, continuous
weights `w₁ ≥ 0`, `w₂ > 0` on `S`, and a continuous curve `P` in `S`:

  `∫_P w₂ ds_{(w₁·D)_S} = ∫_P w₁ w₂ ds_D`   (`weightedLengthWith_weylDistOn_eq`),

i.e. Weyl scaling composes: `e^{ξ g} · (e^{ξ f} · D)_S = (e^{ξ (f + g)} · D)_S`
(`weylDistOnWith_weylDistOn_eq`). The sealed `HigherDimLQGMetric.weightedLength_weyl_chain` is the
`ContMetric` (Euclidean `ℝ^d`) version; this one is metric-free, proved by fine uniform partitions
(uniform continuity of `w₂` along the curve) on top of the length identity
`HigherDimLQGMetric.curveLengthWith_weylDistOn` ([S] Lemma 2.1(c)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open HigherDimLQGMetric
open LQGMetric.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-- Additivity of the weighted length along a monotone chain. -/
theorem sum_weightedLength_eq (w : X → ℝ) (P : ℝ → X) {u : ℕ → ℝ} (hu : Monotone u) (N : ℕ) :
    ∑ k ∈ Finset.range N, weightedLength w P (u k) (u (k + 1)) = weightedLength w P (u 0) (u N) := by
  induction N with
  | zero => simp [weightedLength_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, weightedLength_add (hu (Nat.zero_le N)) (hu (Nat.le_succ N))]

/-- `K · inf_{[s,t]} w = inf_{[s,t]} (k w)` for `K = ofReal k`, `k > 0`. -/
theorem ofReal_mul_infAlong {k : ℝ} (hk : 0 < k) (w : X → ℝ) (P : ℝ → X) (s t : ℝ) :
    ENNReal.ofReal k * infAlong w P s t = infAlong (fun x => k * w x) P s t := by
  have h0 : ENNReal.ofReal k ≠ 0 := (ENNReal.ofReal_pos.2 hk).ne'
  unfold infAlong
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun r => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine iInf_congr fun _ => ?_
  rw [← ENNReal.ofReal_mul hk.le]

/-- Lower half: `inf w₂ · ∫ w₁ ds ≤ ∫ w₁ w₂ ds` on `[u, v]`. -/
theorem infAlong_mul_weightedLength_le {w₁ w₂ : X → ℝ} {P : ℝ → X} {u v : ℝ}
    (hw₁ : ∀ r ∈ Icc u v, 0 ≤ w₁ (P r)) :
    infAlong w₂ P u v * weightedLength w₁ P u v ≤
      weightedLength (fun x => w₁ x * w₂ x) P u v := by
  unfold weightedLength
  rw [← partitionSup_const_mul]
  refine partitionSup_mono fun s t hs hst ht => ?_
  rw [← mul_assoc]
  refine mul_le_mul' (le_infAlong fun r hr => ?_) le_rfl
  have hr' : r ∈ Icc u v := ⟨hs.trans hr.1, hr.2.trans ht⟩
  calc infAlong w₂ P u v * infAlong w₁ P s t
      ≤ ENNReal.ofReal (w₂ (P r)) * ENNReal.ofReal (w₁ (P r)) :=
        mul_le_mul' (infAlong_le hr') (infAlong_le hr)
    _ = ENNReal.ofReal (w₁ (P r) * w₂ (P r)) := by
        rw [mul_comm, ENNReal.ofReal_mul (hw₁ r hr')]

/-- Upper half: if `w₂ ≤ k` along `[u, v]` (`k > 0`), then `∫ w₁ w₂ ds ≤ k ∫ w₁ ds`. -/
theorem weightedLength_mul_le {w₁ w₂ : X → ℝ} {P : ℝ → X} {u v k : ℝ} (hk : 0 < k)
    (hw₁ : ∀ r ∈ Icc u v, 0 ≤ w₁ (P r)) (hw₂ : ∀ r ∈ Icc u v, w₂ (P r) ≤ k) :
    weightedLength (fun x => w₁ x * w₂ x) P u v ≤ ENNReal.ofReal k * weightedLength w₁ P u v := by
  unfold weightedLength
  rw [← partitionSup_const_mul]
  refine partitionSup_mono fun s t hs hst ht => ?_
  rw [← mul_assoc, ofReal_mul_infAlong hk]
  refine mul_le_mul' (infAlong_mono_weight fun r hr => ?_) le_rfl
  have hr' : r ∈ Icc u v := ⟨hs.trans hr.1, hr.2.trans ht⟩
  rw [mul_comm k]
  exact mul_le_mul_of_nonneg_left (hw₂ r hr') (hw₁ r hr')

/-- **Chain rule.** `∫_P w₂ ds_{(w₁·D)_S} = ∫_P w₁ w₂ ds_D` for a continuous curve `P` in the open
set `S`, `w₁ ≥ 0` and `w₂ > 0` continuous on `S`. -/
theorem weightedLengthWith_weylDistOn_eq {S : Set X} {w₁ w₂ : X → ℝ} (hS : IsOpen S)
    (hw₁ : ContinuousOn w₁ S) (hw₁0 : ∀ x ∈ S, 0 ≤ w₁ x)
    (hw₂ : ContinuousOn w₂ S) (hw₂p : ∀ x ∈ S, 0 < w₂ x)
    {P : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hPS : MapsTo P (Icc a b) S) :
    weightedLengthWith (weylDistOn w₁ S) w₂ P a b = weightedLength (fun x => w₁ x * w₂ x) P a b := by
  set g : ℝ → ℝ → ℝ≥0∞ := fun u v => infAlong w₂ P u v * weightedLength w₁ P u v with hg
  have h0 : weightedLengthWith (weylDistOn w₁ S) w₂ P a b = partitionSup g a b := by
    unfold weightedLengthWith
    refine partitionSup_congr fun u v hu huv hv => ?_
    rw [curveLengthWith_weylDistOn hS hw₁ (hP.mono (Icc_subset_Icc hu hv))
      (hPS.mono_left (Icc_subset_Icc hu hv))]
  have hw₁P : ∀ r ∈ Icc a b, 0 ≤ w₁ (P r) := fun r hr => hw₁0 _ (hPS hr)
  rw [h0]
  apply le_antisymm
  · -- `≤`
    refine partitionSup_le fun p => ?_
    calc p.sum g ≤ ∑ i ∈ Finset.range p.n,
          weightedLength (fun x => w₁ x * w₂ x) P (p.t i) (p.t (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨h1, -, h3⟩ := p.step (Finset.mem_range.1 hi)
          exact infAlong_mul_weightedLength_le fun r hr =>
            hw₁P r ⟨h1.trans hr.1, hr.2.trans h3⟩
      _ ≤ weightedLength (fun x => w₁ x * w₂ x) P a b := p.sum_partitionSup_le _
  · -- `≥`, by fine uniform partitions
    by_cases hA : partitionSup g a b = ⊤
    · rw [hA]; exact le_top
    obtain ⟨m, M, hm, hmM⟩ := exists_bounds_along hw₂ hw₂p hab hP hPS
    have huc : UniformContinuousOn (fun t => w₂ (P t)) (Icc a b) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (hw₂.comp hP hPS)
    rw [Metric.uniformContinuousOn_iff] at huc
    have key : ∀ n : ℕ, weightedLength (fun x => w₁ x * w₂ x) P a b ≤
        ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * partitionSup g a b := by
      intro n
      set ε : ℝ := m / ((n : ℝ) + 1) with hε
      have hε0 : 0 < ε := by positivity
      obtain ⟨δ, hδ, hδuc⟩ := huc ε hε0
      obtain ⟨N, hN, hNδ⟩ := exists_uniform_fine hab hδ
      set p := IccPartition.uniform hab N hN with hp
      have hmono : Monotone p.t := fun i j hij => by
        show a + (i : ℝ) * ((b - a) / N) ≤ a + (j : ℝ) * ((b - a) / N)
        have : 0 ≤ (b - a) / N := div_nonneg (sub_nonneg.2 hab) (Nat.cast_nonneg N)
        gcongr
      have hsum := sum_weightedLength_eq (fun x => w₁ x * w₂ x) P hmono N
      rw [show p.t 0 = a from p.zero, show p.t N = b from p.last] at hsum
      rw [← hsum]
      set c : ℝ := 1 + 1 / ((n : ℝ) + 1) with hc
      have hc0 : 0 < c := by positivity
      calc ∑ k ∈ Finset.range N, weightedLength (fun x => w₁ x * w₂ x) P (p.t k) (p.t (k + 1))
          ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal c * g (p.t k) (p.t (k + 1)) := by
            refine Finset.sum_le_sum fun k hk => ?_
            obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hk)
            have hsub : Icc (p.t k) (p.t (k + 1)) ⊆ Icc a b := Icc_subset_Icc h1 h3
            -- the oscillation of `w₂` on the piece is at most `ε ≤ w₂ / (n + 1)`
            have hosc : ∀ r ∈ Icc (p.t k) (p.t (k + 1)), ∀ s ∈ Icc (p.t k) (p.t (k + 1)),
                w₂ (P r) ≤ c * w₂ (P s) := by
              intro r hr s hs
              have hrs : dist r s < δ := by
                rw [Real.dist_eq]
                have hstep : p.t (k + 1) - p.t k = (b - a) / N :=
                  IccPartition.uniform_step hab N hN k
                have : |r - s| ≤ p.t (k + 1) - p.t k := by
                  rw [abs_le]; constructor <;> linarith [hr.1, hr.2, hs.1, hs.2]
                linarith
              have h := hδuc r (hsub hr) s (hsub hs) hrs
              rw [Real.dist_eq] at h
              have hms : m ≤ w₂ (P s) := (hmM s (hsub hs)).1
              have hle : ε ≤ w₂ (P s) / ((n : ℝ) + 1) := by
                rw [hε]; exact div_le_div_of_nonneg_right hms (by positivity)
              have : w₂ (P r) ≤ w₂ (P s) + ε := by linarith [(abs_lt.1 h).2]
              calc w₂ (P r) ≤ w₂ (P s) + w₂ (P s) / ((n : ℝ) + 1) := by linarith
                _ = c * w₂ (P s) := by rw [hc]; ring
            -- the piece bound
            set i₂ := infAlong w₂ P (p.t k) (p.t (k + 1)) with hi₂
            have hi₂t : i₂ ≠ ⊤ := infAlong_ne_top h2
            have hi₂0 : ENNReal.ofReal m ≤ i₂ := ofReal_le_infAlong fun s hs => (hmM s (hsub hs)).1
            have hi₂p : 0 < i₂.toReal := ENNReal.toReal_pos
              ((ENNReal.ofReal_pos.2 hm).trans_le hi₂0).ne' hi₂t
            have hbound : ∀ r ∈ Icc (p.t k) (p.t (k + 1)), w₂ (P r) ≤ c * i₂.toReal := by
              intro r hr
              have hle : ENNReal.ofReal (w₂ (P r)) ≤ ENNReal.ofReal c * i₂ := by
                rw [hi₂, ofReal_mul_infAlong hc0]
                exact le_infAlong fun s hs =>
                  ENNReal.ofReal_le_ofReal (hosc r hr s hs)
              rw [← ENNReal.ofReal_toReal hi₂t, ← ENNReal.ofReal_mul hc0.le] at hle
              exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle
            calc weightedLength (fun x => w₁ x * w₂ x) P (p.t k) (p.t (k + 1))
                ≤ ENNReal.ofReal (c * i₂.toReal) * weightedLength w₁ P (p.t k) (p.t (k + 1)) :=
                  weightedLength_mul_le (by positivity)
                    (fun r hr => hw₁P r (hsub hr)) hbound
              _ = ENNReal.ofReal c * g (p.t k) (p.t (k + 1)) := by
                  rw [ENNReal.ofReal_mul hc0.le, ENNReal.ofReal_toReal hi₂t, mul_assoc]
        _ = ENNReal.ofReal c * p.sum g := by rw [IccPartition.sum, Finset.mul_sum]; rfl
        _ ≤ ENNReal.ofReal c * partitionSup g a b := mul_le_mul' le_rfl (le_partitionSup p)
    -- let `n → ∞`
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * partitionSup g a b)
        atTop (𝓝 (partitionSup g a b)) := by
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1))) atTop (𝓝 1) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at this
        simpa using ENNReal.tendsto_ofReal this
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hA)
    exact ge_of_tendsto' hlim key

/-- **Composition of Weyl scalings** on an open set: `(w₂ · (w₁·D)_S)_S = ((w₁ w₂)·D)_S`. -/
theorem weylDistOnWith_weylDistOn_eq {S : Set X} {w₁ w₂ : X → ℝ} (hS : IsOpen S)
    (hw₁ : ContinuousOn w₁ S) (hw₁0 : ∀ x ∈ S, 0 ≤ w₁ x)
    (hw₂ : ContinuousOn w₂ S) (hw₂p : ∀ x ∈ S, 0 < w₂ x) (x y : X) :
    weylDistOnWith (weylDistOn w₁ S) w₂ S x y = weylDistOn (fun z => w₁ z * w₂ z) S x y := by
  unfold weylDistOnWith weylDistOn
  refine iInf_congr fun P => iInf_congr fun hc => iInf_congr fun _ => iInf_congr fun _ =>
    iInf_congr fun hPS => ?_
  exact weightedLengthWith_weylDistOn_eq hS hw₁ hw₁0 hw₂ hw₂p zero_le_one hc hPS

end SupercriticalConformalCovariance.Domain
