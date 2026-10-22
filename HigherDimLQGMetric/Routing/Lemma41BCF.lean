import HigherDimLQGMetric.Routing.Lemma41Cut
import HigherDimLQGMetric.Collapse.Lemma32

/-! Adapter from ordered arc traversal to the shortcut lemma's geodesic interface. -/

set_option autoImplicit false

noncomputable section

open Set Topology BoundedContinuousFunction

namespace HigherDimLQGMetric

theorem lemma41_bcf_intrinsic_geodesic_injOn {X : Type*} [MetricSpace X]
    (K : Set X) {T ℓ : ℝ} (hT : 0 ≤ T)
    (Q : Icc (0 : ℝ) T →ᵇ X)
    (hQK : ∀ u ∈ Icc (0 : ℝ) ℓ, Set.IccExtend hT Q u ∈ K)
    (hunit : ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ, s ≤ t →
      LQGMetric.MetricGeometry.internalEDist K
        (Set.IccExtend hT Q s) (Set.IccExtend hT Q t) = ENNReal.ofReal (t - s)) :
    InjOn (Set.IccExtend hT Q) (Icc 0 ℓ) := by
  let F : ℝ → X := Set.IccExtend hT Q
  have hfull : ∀ s ∈ Icc (0 : ℝ) ℓ, ∀ t ∈ Icc (0 : ℝ) ℓ,
      LQGMetric.MetricGeometry.internalEDist K (F s) (F t) = ENNReal.ofReal |t - s| := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      exact hunit s hs t ht hst
    · rw [LQGMetric.MetricGeometry.internalEDist_comm, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hts)]
      exact hunit t ht s hs hts
  exact intrinsic_geodesic_injOn hQK hfull

theorem lemma41_bcf_path_range {X : Type*} [MetricSpace X]
    {T ℓ : ℝ} (hT : 0 ≤ T) (hℓ0 : 0 ≤ ℓ)
    (Q : Icc (0 : ℝ) T →ᵇ X) :
    ∃ P : Path (Set.IccExtend hT Q 0) (Set.IccExtend hT Q ℓ),
      Set.range P = (Set.IccExtend hT Q) '' Icc 0 ℓ := by
  let F : ℝ → X := Set.IccExtend hT Q
  let φ : ℝ → ℝ := fun r => ℓ * r
  have hφc : Continuous φ := continuous_const.mul continuous_id
  have hFc : Continuous F := continuous_IccExtend_iff.mpr Q.continuous
  let P : Path (F 0) (F ℓ) :=
    { toFun := fun r => F (φ r)
      continuous_toFun := hFc.comp (hφc.comp continuous_subtype_val)
      source' := by simp [φ]
      target' := by simp [φ] }
  have hφm : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_left hab hℓ0
  have himg : φ '' Icc (0 : ℝ) 1 = Icc 0 ℓ := by
    have h := hφc.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) hφm
    simpa [φ] using h
  refine ⟨P, ?_⟩
  ext z
  constructor
  · rintro ⟨r, rfl⟩
    change F (φ r) ∈ F '' Icc 0 ℓ
    exact ⟨φ r, (himg ▸ ⟨r, r.property, rfl⟩), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨r, hr, hru⟩ := himg.symm ▸ hu
    exact ⟨⟨r, hr⟩, by change F (φ r) = F u; rw [hru]⟩

theorem lemma41_traversesMarkedArc_of_range {X : Type*} [MetricSpace X]
    {T ℓ : ℝ} (hT : 0 ≤ T) (hℓT : ℓ ≤ T)
    (Q : Icc (0 : ℝ) T →ᵇ X)
    (hQi : InjOn (Set.IccExtend hT Q) (Icc 0 ℓ))
    (σ : ℝ → X) (hσc : ContinuousOn σ (Icc 0 1))
    (hσi : InjOn σ (Icc 0 1))
    (hσrange : σ '' Icc (0 : ℝ) 1 ⊆
      (Set.IccExtend hT Q) '' Icc 0 ℓ) :
    TraversesMarkedArc hℓT Q σ ∨
      TraversesMarkedArc hℓT Q (fun r => σ (1 - r)) := by
  let F : ℝ → X := Set.IccExtend hT Q
  have hFc : ContinuousOn F (Icc 0 ℓ) :=
    (continuous_IccExtend_iff.mpr Q.continuous).continuousOn
  have htrav := lemma41_arc_range_forces_traversal F hFc hQi σ hσc hσi hσrange
  rcases htrav with hforward | hreverse
  · left
    rcases hforward with ⟨s, t, hs, hst, ht, hsQ, htQ, hmid⟩
    refine ⟨s, t, hs, hst, ht, ?_, ?_, ?_⟩
    · simpa only [F, Set.IccExtend_of_mem hT Q ⟨hs, hst.trans (ht.trans hℓT)⟩] using hsQ
    · simpa only [F, Set.IccExtend_of_mem hT Q ⟨hs.trans hst, ht.trans hℓT⟩] using htQ
    · intro r hr
      obtain ⟨q, hq, hqQ⟩ := hmid r hr
      refine ⟨q, hq.1, hq.2, ⟨hs.trans hq.1, hq.2.trans (ht.trans hℓT)⟩, ?_⟩
      simpa only [F, Set.IccExtend_of_mem hT Q ⟨hs.trans hq.1, hq.2.trans (ht.trans hℓT)⟩]
        using hqQ
  · right
    rcases hreverse with ⟨s, t, hs, hst, ht, hsQ, htQ, hmid⟩
    refine ⟨s, t, hs, hst, ht, ?_, ?_, ?_⟩
    · simpa only [F, Set.IccExtend_of_mem hT Q ⟨hs, hst.trans (ht.trans hℓT)⟩] using hsQ
    · simpa only [F, Set.IccExtend_of_mem hT Q ⟨hs.trans hst, ht.trans hℓT⟩] using htQ
    · intro r hr
      obtain ⟨q, hq, hqQ⟩ := hmid r hr
      refine ⟨q, hq.1, hq.2, ⟨hs.trans hq.1, hq.2.trans (ht.trans hℓT)⟩, ?_⟩
      simpa only [F, Set.IccExtend_of_mem hT Q ⟨hs.trans hq.1, hq.2.trans (ht.trans hℓT)⟩]
        using hqQ

/-- Abstract forcing result in exactly the two-orientation interface of `lemma32_shortcut`. -/
theorem lemma41_forcing_of_components {X V E : Type*}
    [MetricSpace X] [Fintype V] [DecidableEq V] [Fintype E]
    (K : Set X) (C Star : V → Set X)
    (left right : E → V) (σ : E → ℝ → X)
    (hne : ∀ e, left e ≠ right e)
    (hCcompact : ∀ v, IsCompact (C v))
    (hCC : ∀ v w, v ≠ w → Disjoint (C v) (C w))
    (hσc : ∀ e, ContinuousOn (σ e) (Icc 0 1))
    (hσi : ∀ e, InjOn (σ e) (Icc 0 1))
    (hσC : ∀ e v u, u ∈ Icc (0 : ℝ) 1 → σ e u ∈ C v →
      (u = 0 ∧ v = left e) ∨ (u = 1 ∧ v = right e))
    (hσσ : ∀ e f, e ≠ f →
      Disjoint (σ e '' Icc (0 : ℝ) 1) (σ f '' Icc (0 : ℝ) 1))
    (hCStar : ∀ v, C v ⊆ Star v)
    (hσStar : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆ Star (left e) ∩ Star (right e))
    (hK : K = (⋃ v, C v) ∪ (⋃ e, σ e '' Icc (0 : ℝ) 1))
    {b : ℝ} (hb : 0 < b)
    (hdiam : ∀ v, ∀ a ∈ Star v, ∀ c ∈ Star v, dist a c < b / 8)
    {T ℓ : ℝ} (hT : 0 ≤ T) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ T)
    (Q : Icc (0 : ℝ) T →ᵇ X)
    (hQK : ∀ u ∈ Icc (0 : ℝ) ℓ, Set.IccExtend hT Q u ∈ K)
    (hQi : InjOn (Set.IccExtend hT Q) (Icc 0 ℓ))
    (hsep : b / 4 ≤ dist (Set.IccExtend hT Q 0) (Set.IccExtend hT Q ℓ)) :
    ∃ e, TraversesMarkedArc hℓT Q (σ e) ∨
      TraversesMarkedArc hℓT Q (fun r => σ e (1 - r)) := by
  obtain ⟨P, hPrange⟩ := lemma41_bcf_path_range hT hℓ0 Q
  have hPK : Set.range P ⊆ (⋃ v, C v) ∪ (⋃ e, σ e '' Icc (0 : ℝ) 1) := by
    rw [hPrange, ← hK]
    rintro z ⟨u, hu, rfl⟩
    exact hQK u hu
  obtain ⟨e, he⟩ := lemma41_distant_path_contains_marked P C Star left right σ
    hne hCcompact hCC hσc hσi hσC hσσ hCStar hσStar hPK hb hdiam hsep
  refine ⟨e, ?_⟩
  apply lemma41_traversesMarkedArc_of_range hT hℓT Q hQi (σ e) (hσc e)
    (hσi e)
  simpa only [hPrange] using he

end HigherDimLQGMetric
