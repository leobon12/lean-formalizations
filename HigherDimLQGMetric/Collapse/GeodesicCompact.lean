import HigherDimLQGMetric.Collapse.Speed

/-! # Compact convergence of normalized paths to an intrinsic geodesic -/

set_option autoImplicit false

open Set Filter Topology BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Compactness part of Lemma 3.1′(b).  The speed and tube estimates are separated
from this topological extraction so they can be supplied by the weighted path laws. -/
theorem collapse_geodesic_subseq {X : Type*} [MetricSpace X]
    {Y K : Set X} (hY : IsCompact Y) (hK : IsCompact K) (hKne : K.Nonempty)
    {P : ℕ → ℝ → X} {L : ℕ → ℝ} {x y : ℕ → X} {u v : X} {T ℓ : ℝ}
    (hT : 0 ≤ T) (hL0 : ∀ n, 0 ≤ L n) (hLT : ∀ n, L n ≤ T)
    (hL : Tendsto L atTop (𝓝 ℓ))
    (hPc : ∀ n, ContinuousOn (P n) (Icc 0 T))
    (hPY : ∀ n, MapsTo (P n) (Icc 0 T) Y)
    (hspeed : ∀ n, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      dist (P n s) (P n t) ≤ dist s t)
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ t ∈ Icc (0 : ℝ) T, Metric.infDist (P n t) K < ε)
    (hP0 : ∀ n, P n 0 = x n) (hPL : ∀ n, P n (L n) = y n)
    (hconst : ∀ n t, L n ≤ t → t ≤ T → P n t = P n (L n))
    (hx : Tendsto x atTop (𝓝 u)) (hy : Tendsto y atTop (𝓝 v))
    (hend : internalEDist K u v = ENNReal.ofReal ℓ) :
    ∃ Q : Icc (0 : ℝ) T →ᵇ X, (∀ t, Q t ∈ K) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoUniformly (fun n (t : Icc (0 : ℝ) T) => P (φ n) t) Q atTop ∧
        (Set.IccExtend hT Q) 0 = u ∧
        (∃ hℓ : ℓ ∈ Icc (0 : ℝ) T, Q ⟨ℓ, hℓ⟩ = v ∧
          (∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
            internalEDist K ((Set.IccExtend hT Q) s)
              ((Set.IccExtend hT Q) t) = ENNReal.ofReal (t - s)) ∧
          ∀ t : Icc (0 : ℝ) T, ℓ ≤ t → Q t = v) := by
  classical
  let F : ℕ → Icc (0 : ℝ) T →ᵇ X := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t => P n t, (hPc n).domRestrict⟩
  have hF : ∀ n (t : Icc (0 : ℝ) T), F n t = P n t := fun _ _ => rfl
  obtain ⟨Q, hQY, φ, hφ, hlim, _⟩ :=
    collapse_curve_subseq hY hT 1 F
      (fun n t => by rw [hF]; exact hPY n t.2)
      (fun n s t => by simpa only [hF, one_mul, Subtype.dist_eq] using hspeed n s s.2 t t.2)
  have hlim' : TendstoUniformly (fun n (t : Icc (0 : ℝ) T) => P (φ n) t) Q atTop := by
    simpa only [hF] using hlim
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
        rw [hF]
        exact hn t t.2
      have hbad : Metric.infDist (Q t) K ≤ Metric.infDist (Q t) K / 2 :=
        le_of_tendsto hdistlim (hnearφ.mono fun _ h => h.le)
      linarith
    exact (hK.isClosed.mem_iff_infDist_zero hKne).2 hzero
  have hℓ0 : 0 ≤ ℓ := ge_of_tendsto hL (Eventually.of_forall hL0)
  have hℓT : ℓ ≤ T := le_of_tendsto hL (Eventually.of_forall hLT)
  have hℓmem : ℓ ∈ Icc (0 : ℝ) T := ⟨hℓ0, hℓT⟩
  have hQ0 : Q ⟨0, ⟨le_rfl, hT⟩⟩ = u := by
    apply tendsto_nhds_unique (hlim.tendsto_at _)
    have heq : (fun n => F (φ n) ⟨0, ⟨le_rfl, hT⟩⟩) = x ∘ φ := by
      funext n
      simp only [hF, hP0, Function.comp_def]
    rw [heq]
    exact hx.comp hφ.tendsto_atTop
  have hQℓ : Q ⟨ℓ, hℓmem⟩ = v := by
    have hLφ : Tendsto (fun n => (⟨L (φ n), ⟨hL0 _, hLT _⟩⟩ : Icc (0 : ℝ) T))
        atTop (𝓝 (⟨ℓ, hℓmem⟩ : Icc (0 : ℝ) T)) :=
      tendsto_subtype_rng.mpr (hL.comp hφ.tendsto_atTop)
    have hcomp := hlim.tendsto_comp Q.continuous.continuousAt hLφ
    have heq : (fun n => F (φ n) (⟨L (φ n), ⟨hL0 _, hLT _⟩⟩ : Icc (0 : ℝ) T)) =
        y ∘ φ := by
      funext n
      simp only [hF, hPL, Function.comp_def]
    rw [heq] at hcomp
    exact tendsto_nhds_unique hcomp (hy.comp hφ.tendsto_atTop)
  have hQspeed : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      dist ((Set.IccExtend hT Q) s) ((Set.IccExtend hT Q) t) ≤ dist s t := by
    intro s hs t ht
    have hdistlim : Tendsto (fun n => dist (F (φ n) ⟨s, hs⟩) (F (φ n) ⟨t, ht⟩))
        atTop (𝓝 (dist (Q ⟨s, hs⟩) (Q ⟨t, ht⟩))) :=
      (continuous_dist.tendsto _).comp
        ((hlim.tendsto_at ⟨s, hs⟩).prodMk_nhds (hlim.tendsto_at ⟨t, ht⟩))
    have hbound : dist (Q ⟨s, hs⟩) (Q ⟨t, ht⟩) ≤ dist s t :=
      le_of_tendsto hdistlim (Eventually.of_forall fun n => by
        simpa only [hF] using hspeed (φ n) s hs t ht)
    simpa only [Set.IccExtend_of_mem hT Q hs, Set.IccExtend_of_mem hT Q ht] using hbound
  have hQcont : ContinuousOn (Set.IccExtend hT Q) (Icc 0 T) :=
    (continuous_IccExtend_iff.mpr Q.continuous).continuousOn
  have hQmaps : MapsTo (Set.IccExtend hT Q) (Icc 0 T) K := by
    intro t ht
    rw [Set.IccExtend_of_mem hT Q ht]
    exact hQK ⟨t, ht⟩
  have hQend0 : (Set.IccExtend hT Q) 0 = u := by
    rw [Set.IccExtend_of_mem hT Q ⟨le_rfl, hT⟩]
    exact hQ0
  have hQendℓ : (Set.IccExtend hT Q) ℓ = v := by
    rw [Set.IccExtend_of_mem hT Q hℓmem]
    exact hQℓ
  have hgeo := intrinsic_unit_speed_of_endpoint_distance hQcont hQmaps hQspeed
    hℓ0 hℓT hQend0 hQendℓ hend
  have htail : ∀ t : Icc (0 : ℝ) T, ℓ ≤ t → Q t = v := by
    intro t ht
    by_cases heq : (t : ℝ) = ℓ
    · subst heq
      exact hQℓ
    have hlt : ℓ < (t : ℝ) := lt_of_le_of_ne ht (Ne.symm heq)
    have hltφ : ∀ᶠ n in atTop, L (φ n) < t :=
      (hL.comp hφ.tendsto_atTop).eventually (eventually_lt_nhds hlt)
    have htend : Tendsto (fun n => F (φ n) t) atTop (𝓝 (Q t)) := hlim.tendsto_at t
    have htend' : Tendsto (fun n => F (φ n) t) atTop (𝓝 v) := by
      apply (hy.comp hφ.tendsto_atTop).congr'
      filter_upwards [hltφ] with n hn
      simp only [hF, hconst (φ n) t hn.le t.2.2, hPL, Function.comp_def]
    exact tendsto_nhds_unique htend htend'
  refine ⟨Q, hQK, φ, hφ, hlim', hQend0, ⟨hℓmem, hQℓ, ?_, htail⟩⟩
  intro s hs t ht hst
  exact hgeo s hs t ht hst

end HigherDimLQGMetric
