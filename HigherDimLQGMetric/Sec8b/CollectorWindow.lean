import HigherDimLQGMetric.Sec8b.GeodBridge
import HigherDimLQGMetric.Sec8b.PruningGeometry
import HigherDimLQGMetric.Sec8.ExcursionEquiv

/-! First and last collector visits for the one-site undo step. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Topology Metric unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- A compact closed hitting-time set has first and last visits. This is the
dimension-independent version of `LQGMetric.LM.t17_first_last_hit`. -/
theorem s7b_first_last_hit {P : ℝ → Rd d} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) {K : Set (Rd d)}
    (hK : IsClosed K) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) (hPt₀ : P t₀ ∈ K) :
    ∃ s u : ℝ, a ≤ s ∧ s ≤ u ∧ u ≤ b ∧ P s ∈ K ∧ P u ∈ K ∧
      ∀ t ∈ Icc a b, P t ∈ K → s ≤ t ∧ t ≤ u := by
  have hT : IsClosed (Icc a b ∩ P ⁻¹' K) :=
    hP.preimage_isClosed_of_isClosed isClosed_Icc hK
  have hc : IsCompact (Icc a b ∩ P ⁻¹' K) :=
    isCompact_Icc.of_isClosed_subset hT inter_subset_left
  have hn : (Icc a b ∩ P ⁻¹' K).Nonempty := ⟨t₀, ht₀, hPt₀⟩
  obtain ⟨hs1, hs2⟩ := hc.sInf_mem hn
  obtain ⟨hu1, hu2⟩ := hc.sSup_mem hn
  refine ⟨_, _, hs1.1, csInf_le_csSup hn hc.bddBelow hc.bddAbove,
    hu1.2, hs2, hu2, fun t ht hPt => ?_⟩
  exact ⟨csInf_le hc.bddBelow ⟨ht, hPt⟩,
    le_csSup hc.bddAbove ⟨ht, hPt⟩⟩

/-- The first and last closed-collector times exclude the open collector on
both outside pieces. -/
theorem s7b_first_last_avoids_open {P : ℝ → Rd d} {a b σ₁ σ₂ : ℝ}
    {V : Set (Rd d)}
    (hbound : a ≤ σ₁ ∧ σ₁ ≤ σ₂ ∧ σ₂ ≤ b)
    (hfirstlast : ∀ t ∈ Icc a b, P t ∈ closure V → σ₁ ≤ t ∧ t ≤ σ₂) :
    (∀ t ∈ Icc a σ₁, P t ∉ V ∨ t = σ₁) ∧
    (∀ t ∈ Icc σ₂ b, P t ∉ V ∨ t = σ₂) := by
  constructor
  · intro t ht
    by_cases h : t = σ₁
    · exact Or.inr h
    · left
      intro hVt
      have hts := (hfirstlast t ⟨ht.1, (ht.2.trans hbound.2.1).trans hbound.2.2⟩
        (subset_closure hVt)).1
      exact h (le_antisymm ht.2 hts)
  · intro t ht
    by_cases h : t = σ₂
    · exact Or.inr h
    · left
      intro hVt
      have hts := (hfirstlast t ⟨(hbound.1.trans hbound.2.1).trans ht.1,
        ht.2⟩ (subset_closure hVt)).2
      exact h (le_antisymm hts ht.1)

/-- The first and last closed-collector hits themselves cannot lie in the
open collector when the endpoints start outside it. -/
theorem s7b_first_last_avoid_open_closed {P : ℝ → Rd d} {a b σ₁ σ₂ : ℝ}
    {V : Set (Rd d)} (hP : ContinuousOn P (Icc a b)) (hV : IsOpen V)
    (hbound : a ≤ σ₁ ∧ σ₁ ≤ σ₂ ∧ σ₂ ≤ b)
    (ha : P a ∉ V) (hb : P b ∉ V)
    (hfirstlast : ∀ t ∈ Icc a b, P t ∈ closure V → σ₁ ≤ t ∧ t ≤ σ₂) :
    (∀ t ∈ Icc a σ₁, P t ∉ V) ∧
    (∀ t ∈ Icc σ₂ b, P t ∉ V) := by
  have hclosed : IsClosed (Icc a b ∩ P ⁻¹' Vᶜ) :=
    hP.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl
  have hσ₁ : P σ₁ ∉ V := by
    by_cases heq : a = σ₁
    · simpa only [← heq] using ha
    · have hlt : a < σ₁ := lt_of_le_of_ne hbound.1 heq
      have hsub : Ico a σ₁ ⊆ Icc a b ∩ P ⁻¹' Vᶜ := by
        intro t ht
        have ht01 : t ∈ Icc a b :=
          ⟨ht.1, (ht.2.le.trans hbound.2.1).trans hbound.2.2⟩
        refine ⟨ht01, ?_⟩
        intro htV
        exact (not_le_of_gt ht.2) (hfirstlast t ht01 (subset_closure htV)).1
      have hcl : σ₁ ∈ closure (Ico a σ₁) := by
        rw [closure_Ico heq]
        exact ⟨hbound.1, le_rfl⟩
      exact (closure_minimal hsub hclosed hcl).2
  have hσ₂ : P σ₂ ∉ V := by
    by_cases heq : σ₂ = b
    · simpa only [heq] using hb
    · have hlt : σ₂ < b := lt_of_le_of_ne hbound.2.2 heq
      have hsub : Ioc σ₂ b ⊆ Icc a b ∩ P ⁻¹' Vᶜ := by
        intro t ht
        have ht01 : t ∈ Icc a b :=
          ⟨(hbound.1.trans hbound.2.1).trans ht.1.le, ht.2⟩
        refine ⟨ht01, ?_⟩
        intro htV
        exact (not_le_of_gt ht.1) (hfirstlast t ht01 (subset_closure htV)).2
      have hcl : σ₂ ∈ closure (Ioc σ₂ b) := by
        rw [closure_Ioc heq]
        exact ⟨le_rfl, hbound.2.2⟩
      exact (closure_minimal hsub hclosed hcl).2
  obtain ⟨hleft, hright⟩ := s7b_first_last_avoids_open hbound hfirstlast
  constructor
  · intro t ht
    rcases hleft t ht with hv | heq
    · exact hv
    · simpa only [heq] using hσ₁
  · intro t ht
    rcases hright t ht with hv | heq
    · exact hv
    · simpa only [heq] using hσ₂

/-- The first clause of (T4) confines the entire interval between two
closed-collector visits to the radius-four ball. -/
theorem s7b_T4_window_in_ball {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {s r : ℝ} {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (Metric.ball q.1 (4 * r))
        (Metric.ball q'.1 (4 * r))))
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D Dt E : ContMetric d)
    (htrap : TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
      D Dt s r site.1 site.2)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (P : ℝ → Rd d) (hP : IsGeod E P)
    {σ₁ σ₂ : ℝ} (h0 : 0 ≤ σ₁) (_h12 : σ₁ ≤ σ₂) (h2 : σ₂ ≤ 1)
    (hσ₁ : P σ₁ ∈ closure (sec8Collector T.V r site.1))
    (hσ₂ : P σ₂ ∈ closure (sec8Collector T.V r site.1)) :
    ∀ τ ∈ Icc σ₁ σ₂, P τ ∈ Metric.ball site.1 (4 * r) := by
  have hT4 := htrap.2.2.2 Z hsite hJ hdisj E hE P hP
  intro τ hτ
  exact hT4.1 σ₁ σ₂ τ h0 hτ.1 hτ.2 h2 hσ₁ hσ₂

/-- If all closed-collector visits lie in one ball component, failure of the
excursion event gives a short internal connection between the global first
and last visits. -/
theorem s7b_notExc_short (η : C(unitInterval, Rd d)) (D : ContMetric d)
    (V : Set (Rd d)) (z : Rd d) (r b : ℝ)
    (hout0 : η 0 ∉ ball z (4 * r)) (hout1 : η 1 ∉ ball z (4 * r))
    (hVball : closure V ⊆ ball z (4 * r))
    (hT4 : ∀ s t u : unitInterval, s ≤ t → t ≤ u →
      η s ∈ closure V → η u ∈ closure V → η t ∈ ball z (4 * r))
    (hvisit : ∃ t : unitInterval, η t ∈ V)
    (hnot : ¬ Exc η D V z r b) :
    ∃ σ₁ σ₂ : unitInterval,
      σ₁ ≤ σ₂ ∧ η σ₁ ∈ closure V ∧ η σ₂ ∈ closure V ∧
      (∀ t : unitInterval, η t ∈ closure V → σ₁ ≤ t ∧ t ≤ σ₂) ∧
      D.internal (ball z (4 * r)) (η σ₁) (η σ₂) < ENNReal.ofReal b := by
  have hbot : (0 : unitInterval) = ⊥ := by
    apply Subtype.ext
    rfl
  have htop : (1 : unitInterval) = ⊤ := by
    apply Subtype.ext
    rfl
  obtain ⟨τ, hτV⟩ := hvisit
  have hτF : η τ ∈ closure V := subset_closure hτV
  have hτball : η τ ∈ ball z (4 * r) := hVball hτF
  have h0τ : (0 : unitInterval) < τ := by
    apply lt_of_le_of_ne bot_le
    intro heq
    exact hout0 (by rw [hbot, heq]; exact hτball)
  have hτ1 : τ < (1 : unitInterval) := by
    apply lt_of_le_of_ne le_top
    intro heq
    exact hout1 (by rw [htop, ← heq]; exact hτball)
  let σ₁ := sec8FirstHit η (closure V) 0
  let σ₂ := sec8LastHit η (closure V) 1
  have hσ₁τ : σ₁ ≤ τ := sInf_le (show τ ∈ sec8FollowingHit η (closure V) 0 from
    Or.inr ⟨by simp only [mem_Ici, hbot]; exact bot_le, hτF⟩)
  have hτσ₂ : τ ≤ σ₂ := le_sSup (show τ ∈ sec8PriorHit η (closure V) 1 from
    Or.inr ⟨by simp only [mem_Iic, htop]; exact le_top, hτF⟩)
  have hσ₁F : η σ₁ ∈ closure V := by
    have hm := sec8FirstHit_mem η (closure V) isClosed_closure 0
    rcases hm with hone | ⟨_, hF⟩
    · exact False.elim ((not_le_of_gt hτ1) (hone ▸ hσ₁τ))
    · exact hF
  have hσ₂F : η σ₂ ∈ closure V := by
    have hm := sec8LastHit_mem η (closure V) isClosed_closure 1
    rcases hm with hzero | ⟨_, hF⟩
    · exact False.elim ((not_le_of_gt h0τ) (hzero ▸ hτσ₂))
    · exact hF
  have hfirstlast : ∀ t : unitInterval, η t ∈ closure V → σ₁ ≤ t ∧ t ≤ σ₂ := by
    intro t ht
    exact ⟨sInf_le (Or.inr ⟨by simp only [mem_Ici, hbot]; exact bot_le, ht⟩),
      le_sSup (Or.inr ⟨by simp only [mem_Iic, htop]; exact le_top, ht⟩)⟩
  let α := sec8Alpha η z r τ
  let β := sec8Beta η z r τ
  have houtα : η α ∉ ball z (4 * r) := sec8_alpha_boundary η z r hout0 τ
  have houtβ : η β ∉ ball z (4 * r) := sec8_beta_boundary η z r hout1 τ
  have hαle : α ≤ τ := by
    have hm := sec8LastHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
    rcases hm with hzero | ⟨hτ, _⟩
    · rw [show α = 0 from hzero]
      exact bot_le
    · exact hτ
  have hβge : τ ≤ β := by
    have hm := sec8FirstHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
    rcases hm with hone | ⟨hτ, _⟩
    · rw [show β = 1 from hone]
      exact le_top
    · exact hτ
  have hατ : α < τ := lt_of_le_of_ne hαle (fun heq => houtα (heq ▸ hτball))
  have hτβ : τ < β := lt_of_le_of_ne hβge (fun heq => houtβ (heq ▸ hτball))
  have hinside : ∀ t ∈ Ioo α β, η t ∈ ball z (4 * r) := by
    intro t ht
    rcases lt_trichotomy t τ with hlt | heq | hgt
    · exact sec8_in_ball_after_alpha η z r τ t ⟨ht.1, hlt⟩
    · simpa only [heq] using hτball
    · exact sec8_in_ball_before_beta η z r τ t ⟨hgt, ht.2⟩
  have hασ₁ : α < σ₁ := by
    have hα : α ≤ σ₁ := by
      by_contra hn
      have hσ₁α : σ₁ < α := lt_of_not_ge hn
      exact houtα (hT4 σ₁ α τ hσ₁α.le hαle hσ₁F hτF)
    exact lt_of_le_of_ne hα (fun heq => houtα (heq ▸ hVball hσ₁F))
  have hσ₂β : σ₂ < β := by
    have hβ : σ₂ ≤ β := by
      by_contra hn
      have hβσ₂ : β < σ₂ := lt_of_not_ge hn
      exact houtβ (hT4 τ β σ₂ hβge hβσ₂.le hτF hσ₂F)
    exact lt_of_le_of_ne hβ (fun heq => houtβ (heq ▸ hVball hσ₂F))
  let S : Set unitInterval := {t | t ∈ Ioo α β ∧ η t ∈ closure V}
  have hσ₁S : σ₁ ∈ S := ⟨⟨hασ₁, hσ₁τ.trans_lt hτβ⟩, hσ₁F⟩
  have hσ₂S : σ₂ ∈ S := ⟨⟨hατ.trans_le hτσ₂, hσ₂β⟩, hσ₂F⟩
  have hσ₁eq : sInf S = σ₁ := by
    apply le_antisymm (sInf_le hσ₁S)
    exact le_sInf (fun t ht => (hfirstlast t ht.2).1)
  have hσ₂eq : sSup S = σ₂ := by
    apply le_antisymm
    · exact sSup_le (fun t ht => (hfirstlast t ht.2).2)
    · exact le_sSup hσ₂S
  have hshort : D.internal (ball z (4 * r)) (η σ₁) (η σ₂) < ENNReal.ofReal b := by
    apply lt_of_not_ge
    intro hlong
    apply hnot
    refine ⟨α, β, hατ.trans hτβ, houtα, houtβ, hinside,
      ⟨τ, ⟨hατ, hτβ⟩, hτV⟩, ?_⟩
    simpa only [S, hσ₁eq, hσ₂eq] using hlong
  exact ⟨σ₁, σ₂, hσ₁τ.trans hτσ₂, hσ₁F, hσ₂F, hfirstlast, hshort⟩

/-- The actual (T4) trap and failure of (C4) supply the pruning undo bound for
one site of a discounted geodesic. -/
theorem s7b_undo_of_notExc {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D Dt E E' : ContMetric d)
    (htrap : TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
      D Dt s r site.1 site.2)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (hE' : IsWeylOf ξ (-F_Z T.f r (Z.erase site)) D E')
    (x y : Rd d) (η : C(unitInterval, Rd d))
    (hη : IsConstSpeedGeod E x y η)
    (houtx : x ∉ ball site.1 (4 * r))
    (houty : y ∉ ball site.1 (4 * r))
    (hvisit : ∃ t : unitInterval, η t ∈ sec8Collector T.V r site.1)
    (hnot : ¬ Exc η D (sec8Collector T.V r site.1) site.1 r (T.b * s)) :
    E'.1 (x, y) ≤ E.1 (x, y) + T.b * s := by
  let P := s7b_realPath η
  have hP : IsGeod E P := s7b_constSpeed_isGeod E x y η hη
  have hVball : closure (sec8Collector T.V r site.1) ⊆ ball site.1 (4 * r) :=
    (S6a.closure_collector_subset hr site.1 T.closureV).trans
      (S6a.ann_subset_ball hr site.1)
  have hT4real := (htrap.2.2.2 Z hsite hJ hdisj E hE P hP).1
  have hT4unit : ∀ u v w : unitInterval, u ≤ v → v ≤ w →
      η u ∈ closure (sec8Collector T.V r site.1) →
      η w ∈ closure (sec8Collector T.V r site.1) →
      η v ∈ ball site.1 (4 * r) := by
    intro u v w huv hvw hu hw
    have huvR : (u : ℝ) ≤ v := huv
    have hvwR : (v : ℝ) ≤ w := hvw
    have hres := hT4real (u : ℝ) (w : ℝ) (v : ℝ)
      u.property.1 huvR hvwR w.property.2
      (by simpa only [sec8Collector, P, s7b_realPath_coe] using hu)
      (by simpa only [sec8Collector, P, s7b_realPath_coe] using hw)
    simpa only [P, s7b_realPath_coe] using hres
  obtain ⟨σ₁, σ₂, h12, hσ₁, hσ₂, hfirstlast, hshort⟩ :=
    s7b_notExc_short η D (sec8Collector T.V r site.1) site.1 r
      (T.b * s) (by simpa only [hη.1] using houtx)
      (by simpa only [hη.2.1] using houty) hVball hT4unit hvisit hnot
  have hfirstlastR : ∀ t ∈ Icc (0 : ℝ) 1,
      P t ∈ closure (sec8Collector T.V r site.1) →
      (σ₁ : ℝ) ≤ t ∧ t ≤ (σ₂ : ℝ) := by
    intro t ht hmem
    let tI : unitInterval := ⟨t, ht⟩
    have htI : P t = η tI := by
      simpa only [tI] using s7b_realPath_coe η tI
    have h := hfirstlast tI (htI ▸ hmem)
    exact h
  have hopen : IsOpen (sec8Collector T.V r site.1) :=
    S6a.isOpen_collector hr.ne' site.1 T.openV
  have hbound : (0 : ℝ) ≤ (σ₁ : ℝ) ∧ (σ₁ : ℝ) ≤ (σ₂ : ℝ) ∧
      (σ₂ : ℝ) ≤ 1 := ⟨σ₁.property.1, h12, σ₂.property.2⟩
  have hP0 : P 0 = x := by simpa only [P, s7b_realPath_zero] using hη.1
  have hP1 : P 1 = y := by simpa only [P, s7b_realPath_one] using hη.2.1
  have havoid := s7b_first_last_avoid_open_closed hP.1 hopen hbound
    (by intro hx; exact houtx (hVball (subset_closure (hP0 ▸ hx))))
    (by intro hy; exact houty (hVball (subset_closure (hP1 ▸ hy))))
    hfirstlastR
  have hshort' : E'.internal (ball site.1 (4 * r))
      (P (σ₁ : ℝ)) (P (σ₂ : ℝ)) ≤ ENNReal.ofReal (T.b * s) := by
    dsimp only [P]
    rw [s7b_realPath_coe η σ₁, s7b_realPath_coe η σ₂,
      s7b_erase_internal_eq_on_ball T hr hJ hdisj hsite D E' hE']
    exact hshort.le
  have hb : 0 ≤ T.b * s := mul_nonneg T.constants.2.1.le hs.le
  exact s7b_erase_distance_le_of_window T hr hJ hsite D E E' hE hE'
    x y P hP hP0 hP1
    σ₁.property.1 h12 σ₂.property.2 hb havoid.1 havoid.2 hshort'

/-- Full bad-site undo rule, including the case where the selected geodesic
never visits that collector. -/
theorem s7b_undo_bad_site {ξ cs Cs : ℝ}
    {Dfun Dtfun : DistRd d → ContMetric d}
    (T : Sec8TrapData d ξ cs Cs Dfun Dtfun)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) {Z : Finset (Rd d × ℕ)}
    (hJ : ∀ q ∈ Z, q.2 < T.J)
    (hdisj : (Z : Set (Rd d × ℕ)).Pairwise
      (fun q q' => Disjoint (ball q.1 (4 * r)) (ball q'.1 (4 * r))))
    {site : Rd d × ℕ} (hsite : site ∈ Z)
    (D Dt E E' : ContMetric d)
    (htrap : TrapProps ξ T.V T.f T.J T.a T.b T.c T.g T.H T.c'
      D Dt s r site.1 site.2)
    (hE : IsWeylOf ξ (-F_Z T.f r Z) D E)
    (hE' : IsWeylOf ξ (-F_Z T.f r (Z.erase site)) D E')
    (x y : Rd d) (η : C(unitInterval, Rd d))
    (hη : IsConstSpeedGeod E x y η)
    (houtx : x ∉ ball site.1 (4 * r))
    (houty : y ∉ ball site.1 (4 * r))
    (hbad : ¬ Exc η D (sec8Collector T.V r site.1) site.1 r (T.b * s)) :
    E'.1 (x, y) ≤ E.1 (x, y) + T.b * s := by
  by_cases hvisit : ∃ t : unitInterval, η t ∈ sec8Collector T.V r site.1
  · exact s7b_undo_of_notExc T hs hr hJ hdisj hsite D Dt E E' htrap hE hE'
      x y η hη houtx houty hvisit hbad
  · let P := s7b_realPath η
    have hP : IsGeod E P := s7b_constSpeed_isGeod E x y η hη
    have havoid : ∀ t ∈ Icc (0 : ℝ) 1,
        P t ∉ sec8Collector T.V r site.1 := by
      intro t ht hmem
      let tI : unitInterval := ⟨t, ht⟩
      have htI : P t = η tI := by
        simpa only [tI] using s7b_realPath_coe η tI
      exact hvisit ⟨tI, htI ▸ hmem⟩
    have hle := s7b_erase_distance_le_no_visit T hr hJ hsite D E E' hE hE'
      x y P hP (by simpa only [P, s7b_realPath_zero] using hη.1)
      (by simpa only [P, s7b_realPath_one] using hη.2.1) havoid
    have hb : 0 ≤ T.b * s := mul_nonneg T.constants.2.1.le hs.le
    linarith only [hle, hb]

end HigherDimLQGMetric
