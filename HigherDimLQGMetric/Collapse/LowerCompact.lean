import HigherDimLQGMetric.Collapse.NearMin

/-! # Compact lower bound for curves collapsing into a closed set -/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Uniform length and tube bounds force every limiting pair of endpoints to be connected
inside the collapse set by a curve of no greater length. -/
theorem collapse_compact_lower_bound {X : Type*} [MetricSpace X]
    {Y K : Set X} (hY : IsCompact Y) (hK : IsClosed K) (hKne : K.Nonempty)
    {P : ℕ → ℝ → X} {u v : X} {C : ℝ} (hC : 0 ≤ C)
    (hPc : ∀ n, ContinuousOn (P n) (Icc 0 1))
    (hPY : ∀ n, MapsTo (P n) (Icc 0 1) Y)
    (hlen : ∀ n, curveLength (P n) 0 1 ≤ ENNReal.ofReal C)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, Metric.infDist (P n t) K < ε)
    (hu : Tendsto (fun n => P n 0) atTop (𝓝 u))
    (hv : Tendsto (fun n => P n 1) atTop (𝓝 v)) :
    internalEDist K u v ≤ ENNReal.ofReal C := by
  classical
  let F : ℕ → Icc (0 : ℝ) 1 →ᵇ X := fun n =>
    (collapse_exists_lipschitz_path hC (hPc n) rfl rfl (hPY n) (hlen n)).choose
  have hF : ∀ n, F n 0 = P n 0 ∧ F n 1 = P n 1 ∧
      (∀ t, F n t ∈ Y) ∧
      (∀ t, ∃ s ∈ Icc (0 : ℝ) 1, F n t = P n s) ∧
      curveLength (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) (F n)) 0 1 =
        curveLength (P n) 0 1 ∧
      (∀ s t, dist (F n s) (F n t) ≤ C * dist s t) :=
    fun n => (collapse_exists_lipschitz_path hC (hPc n) rfl rfl (hPY n) (hlen n)).choose_spec
  obtain ⟨Q, hQY, φ, hφ, hlim, hlenlim⟩ :=
    collapse_curve_subseq hY zero_le_one C F (fun n t => (hF n).2.2.1 t)
      (fun n s t => (hF n).2.2.2.2.2 s t)
  have hQK : ∀ t, Q t ∈ K := by
    intro t
    have htlim : Tendsto (fun n => F (φ n) t) atTop (𝓝 (Q t)) := hlim.tendsto_at t
    have hdistlim : Tendsto (fun n => Metric.infDist (F (φ n) t) K) atTop
        (𝓝 (Metric.infDist (Q t) K)) :=
      (Metric.continuous_infDist_pt K).continuousAt.tendsto.comp htlim
    have hzero : Metric.infDist (Q t) K = 0 := by
      by_contra hne
      have hpos : 0 < Metric.infDist (Q t) K :=
        lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne)
      have heps : 0 < Metric.infDist (Q t) K / 2 := by positivity
      have hnearφ : ∀ᶠ n in atTop,
          Metric.infDist (F (φ n) t) K < Metric.infDist (Q t) K / 2 := by
        filter_upwards [hφ.tendsto_atTop.eventually (hnear _ heps)] with n hn
        obtain ⟨s, hs, hFs⟩ := (hF (φ n)).2.2.2.1 t
        rw [hFs]
        exact hn s hs
      have hbad : Metric.infDist (Q t) K ≤ Metric.infDist (Q t) K / 2 :=
        le_of_tendsto hdistlim (hnearφ.mono fun _ h => h.le)
      linarith
    exact (hK.mem_iff_infDist_zero hKne).2 hzero
  have hQ0 : Q (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) = u := by
    apply tendsto_nhds_unique (hlim.tendsto_at _)
    convert hu.comp hφ.tendsto_atTop using 1
    ext n
    exact (hF (φ n)).1
  have hQ1 : Q (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1) = v := by
    apply tendsto_nhds_unique (hlim.tendsto_at _)
    convert hv.comp hφ.tendsto_atTop using 1
    ext n
    exact (hF (φ n)).2.1
  have hlenQ : curveLength (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 0 1 ≤
      ENNReal.ofReal C := by
    calc
      curveLength (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 0 1
          ≤ liminf (fun n => curveLength
              (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) (F (φ n))) 0 1) atTop := hlenlim
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal C) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall fun n => by
          rw [(hF (φ n)).2.2.2.2.1]
          exact hlen (φ n))
      _ = ENNReal.ofReal C := by simp
  have hQcont : ContinuousOn (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q)
      (Icc 0 1) := (continuous_IccExtend_iff.mpr Q.continuous).continuousOn
  have hQmaps : MapsTo (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q)
      (Icc 0 1) K := by
    intro t ht
    rw [Set.IccExtend_of_mem _ Q ht]
    exact hQK ⟨t, ht⟩
  have hQend0 : (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 0 = u := by
    rw [Set.IccExtend_of_mem _ Q (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
    exact hQ0
  have hQend1 : (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 1 = v := by
    rw [Set.IccExtend_of_mem _ Q (by norm_num : (1 : ℝ) ∈ Icc 0 1)]
    exact hQ1
  calc
    internalEDist K u v = internalEDist K
        ((Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 0)
        ((Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 1) := by
          rw [hQend0, hQend1]
    _ ≤ curveLength (Set.IccExtend (by norm_num : (0 : ℝ) ≤ 1) Q) 0 1 :=
      internalEDist_le_curveLength zero_le_one hQcont hQmaps
    _ ≤ ENNReal.ofReal C := hlenQ

/-- The compact lower bound for weighted curves: a cost of order `λ C` and a tube of
width `η`, both vanishing, force an intrinsic curve of length at most `C`. -/
theorem collapse_weighted_lower_bound {X : Type*} [MetricSpace X]
    {Y K : Set X} (hY : IsCompact Y) (hK : IsClosed K) (hKne : K.Nonempty)
    {P : ℕ → ℝ → X} {u v : X} {C : ℝ} (hC : 0 ≤ C)
    {lam eta : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlam : Tendsto lam atTop (𝓝 0)) (heta : Tendsto eta atTop (𝓝 0))
    {a₀ : ℝ} (ha₀ : 0 < a₀) {w : ℕ → X → ℝ}
    (hwlow : ∀ n z, lam n ≤ w n z)
    (hwoff : ∀ n z, eta n ≤ Metric.infDist z K → a₀ ≤ w n z)
    (hPc : ∀ n, ContinuousOn (P n) (Icc 0 1))
    (hPY : ∀ n, MapsTo (P n) (Icc 0 1) Y)
    (hstart : ∀ n, Metric.infDist (P n 0) K ≤ eta n)
    (hcost : ∀ n, weightedLength (w n) (P n) 0 1 ≤ ENNReal.ofReal (lam n * C))
    (hu : Tendsto (fun n => P n 0) atTop (𝓝 u))
    (hv : Tendsto (fun n => P n 1) atTop (𝓝 v)) :
    internalEDist K u v ≤ ENNReal.ofReal C := by
  have hlen : ∀ n, curveLength (P n) 0 1 ≤ ENNReal.ofReal C := by
    intro n
    have hfac : ENNReal.ofReal (lam n) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (hlam0 n))
    have hmul : ENNReal.ofReal (lam n) * curveLength (P n) 0 1 ≤
        ENNReal.ofReal (lam n) * ENNReal.ofReal C := by
      calc
        ENNReal.ofReal (lam n) * curveLength (P n) 0 1
            ≤ weightedLength (w n) (P n) 0 1 :=
          ofReal_mul_curveLength_le_weightedLength zero_le_one
            (fun t _ => hwlow n (P n t))
        _ ≤ ENNReal.ofReal (lam n * C) := hcost n
        _ = ENNReal.ofReal (lam n) * ENNReal.ofReal C :=
          ENNReal.ofReal_mul (hlam0 n).le
    exact (ENNReal.mul_le_mul_iff_right hfac ENNReal.ofReal_ne_top).1 hmul
  have htend : Tendsto (fun n => eta n + lam n * C / a₀) atTop (𝓝 0) := by
    convert heta.add ((hlam.mul_const C).div_const a₀) using 1
    simp
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ∈ Icc (0 : ℝ) 1, Metric.infDist (P n t) K < ε := by
    intro ε hε
    filter_upwards [htend.eventually (eventually_lt_nhds hε)] with n hn t ht
    have hb := infDist_le_eta_add_cost_div (hPc n) ha₀
      (mul_nonneg (hlam0 n).le hC) (hstart n) (hwoff n) (hcost n) t ht
    exact hb.trans_lt hn
  exact collapse_compact_lower_bound hY hK hKne hC hPc hPY hlen hnear hu hv

/-- No normalized weighted distance can stay below a strict intrinsic lower bound.
The proof extracts bad indices, selects strict competitors, and applies compactness. -/
theorem collapse_eventually_lower {X : Type*} [MetricSpace X]
    {Y K : Set X} (hY : IsCompact Y) (hK : IsClosed K) (hKne : K.Nonempty)
    {lam eta : ℕ → ℝ} (hlam0 : ∀ n, 0 < lam n)
    (hlam : Tendsto lam atTop (𝓝 0)) (heta : Tendsto eta atTop (𝓝 0))
    {a₀ : ℝ} (ha₀ : 0 < a₀) {w : ℕ → X → ℝ}
    (hwlow : ∀ n z, lam n ≤ w n z)
    (hwoff : ∀ n z, eta n ≤ Metric.infDist z K → a₀ ≤ w n z)
    {x y : ℕ → X} {u v : X}
    (hstart : ∀ n, Metric.infDist (x n) K ≤ eta n)
    (hu : Tendsto x atTop (𝓝 u)) (hv : Tendsto y atTop (𝓝 v))
    {C B : ℝ} (hC : 0 ≤ C) (hCB : C < B)
    (hBd : ENNReal.ofReal B < internalEDist K u v) :
    ∀ᶠ n in atTop, ENNReal.ofReal C ≤
      (ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n) := by
  classical
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop,
      (ENNReal.ofReal (lam n))⁻¹ * weylDistOn (w n) Y (x n) (y n) <
        ENNReal.ofReal C := by
    simpa only [not_le] using (Filter.not_eventually.mp hnot)
  obtain ⟨ns, hns, hbad⟩ := Filter.exists_seq_forall_of_frequently hfreq
  have hB : 0 ≤ B := le_trans hC hCB.le
  have hW : ∀ n, weylDistOn (w (ns n)) Y (x (ns n)) (y (ns n)) <
      ENNReal.ofReal (lam (ns n) * B) := by
    intro n
    have hfac : ENNReal.ofReal (lam (ns n)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (hlam0 (ns n)))
    have hstrict : ENNReal.ofReal C < ENNReal.ofReal B :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC).2 hCB
    calc
      weylDistOn (w (ns n)) Y (x (ns n)) (y (ns n))
          = ENNReal.ofReal (lam (ns n)) *
              ((ENNReal.ofReal (lam (ns n)))⁻¹ *
                weylDistOn (w (ns n)) Y (x (ns n)) (y (ns n))) :=
            (ENNReal.mul_inv_cancel_left hfac ENNReal.ofReal_ne_top).symm
      _ < ENNReal.ofReal (lam (ns n)) * ENNReal.ofReal C :=
        (ENNReal.mul_lt_mul_iff_right hfac ENNReal.ofReal_ne_top).2 (hbad n)
      _ < ENNReal.ofReal (lam (ns n)) * ENNReal.ofReal B :=
        (ENNReal.mul_lt_mul_iff_right hfac ENNReal.ofReal_ne_top).2 hstrict
      _ = ENNReal.ofReal (lam (ns n) * B) :=
        (ENNReal.ofReal_mul (hlam0 (ns n)).le).symm
  let P : ℕ → ℝ → X := fun n => (exists_weighted_competitor (hW n)).choose
  have hP : ∀ n, ContinuousOn (P n) (Icc 0 1) ∧ P n 0 = x (ns n) ∧
      P n 1 = y (ns n) ∧ MapsTo (P n) (Icc 0 1) Y ∧
      weightedLength (w (ns n)) (P n) 0 1 < ENNReal.ofReal (lam (ns n) * B) :=
    fun n => (exists_weighted_competitor (hW n)).choose_spec
  have hlow := collapse_weighted_lower_bound hY hK hKne hB
    (fun n => hlam0 (ns n)) (hlam.comp hns) (heta.comp hns) ha₀
    (fun n z => hwlow (ns n) z) (fun n z hz => hwoff (ns n) z hz)
    (fun n => (hP n).1) (fun n => (hP n).2.2.2.1)
    (fun n => by rw [(hP n).2.1]; exact hstart (ns n))
    (fun n => (hP n).2.2.2.2.le)
    (by
      have heq : (fun n => P n 0) = x ∘ ns := funext fun n => (hP n).2.1
      rw [heq]
      exact hu.comp hns)
    (by
      have heq : (fun n => P n 1) = y ∘ ns := funext fun n => (hP n).2.2.1
      rw [heq]
      exact hv.comp hns)
  exact (not_lt_of_ge hlow) hBd

end HigherDimLQGMetric
