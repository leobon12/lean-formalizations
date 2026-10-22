import HigherDimLQGMetric.Sec8.ExcursionBorel

/-!
# Identification of the Borel excursion observable

For paths whose endpoints lie outside the trap ball, the first and last
boundary hits locate precisely one connected component of its inverse image.
The closed-collector hitting times then coincide with the infimum and
supremum in the source's excursion definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology Metric unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem sec8_alpha_le (η : C(unitInterval, Rd d)) (z : Rd d) (r : ℝ)
    (τ : unitInterval) : sec8Alpha η z r τ ≤ τ := by
  have hmem := sec8LastHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
  rcases hmem with hzero | ⟨hτ, _⟩
  · rw [sec8Alpha, hzero]
    exact bot_le
  · exact hτ

private theorem sec8_le_beta (η : C(unitInterval, Rd d)) (z : Rd d) (r : ℝ)
    (τ : unitInterval) : τ ≤ sec8Beta η z r τ := by
  have hmem := sec8FirstHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
  rcases hmem with hone | ⟨hτ, _⟩
  · rw [sec8Beta, hone]
    exact le_top
  · exact hτ

/-- Every time strictly between the last boundary hit and the cutoff remains
inside the ball. -/
theorem sec8_in_ball_after_alpha (η : C(unitInterval, Rd d)) (z : Rd d)
    (r : ℝ) (τ t : unitInterval)
    (ht : t ∈ Ioo (sec8Alpha η z r τ) τ) : η t ∈ ball z (4 * r) := by
  by_contra hout
  have hmem : t ∈ sec8PriorHit η (ball z (4 * r))ᶜ τ :=
    Or.inr ⟨ht.2.le, hout⟩
  exact (not_le_of_gt ht.1) (le_sSup hmem)

/-- Every time strictly between the cutoff and the next boundary hit remains
inside the ball. -/
theorem sec8_in_ball_before_beta (η : C(unitInterval, Rd d)) (z : Rd d)
    (r : ℝ) (τ t : unitInterval)
    (ht : t ∈ Ioo τ (sec8Beta η z r τ)) : η t ∈ ball z (4 * r) := by
  by_contra hout
  have hmem : t ∈ sec8FollowingHit η (ball z (4 * r))ᶜ τ :=
    Or.inr ⟨ht.1.le, hout⟩
  exact (not_le_of_gt ht.2) (sInf_le hmem)

/-- The boundary times actually lie outside the ball when path endpoints do. -/
theorem sec8_alpha_boundary (η : C(unitInterval, Rd d)) (z : Rd d)
    (r : ℝ) (h0 : η 0 ∉ ball z (4 * r)) (τ : unitInterval) :
    η (sec8Alpha η z r τ) ∉ ball z (4 * r) := by
  have hmem := sec8LastHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
  rcases hmem with hzero | ⟨_, hout⟩
  · rw [sec8Alpha, hzero]
    exact h0
  · exact hout

theorem sec8_beta_boundary (η : C(unitInterval, Rd d)) (z : Rd d)
    (r : ℝ) (h1 : η 1 ∉ ball z (4 * r)) (τ : unitInterval) :
    η (sec8Beta η z r τ) ∉ ball z (4 * r) := by
  have hmem := sec8FirstHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
  rcases hmem with hone | ⟨_, hout⟩
  · rw [sec8Beta, hone]
    exact h1
  · exact hout

/-- If `(α,β)` is a ball component and `τ` lies inside, the canonical last
boundary hit is exactly `α`. -/
theorem sec8Alpha_eq_of_component (η : C(unitInterval, Rd d)) (z : Rd d)
    (r : ℝ) {α β τ : unitInterval} (hατ : α < τ) (hτβ : τ < β)
    (houtα : η α ∉ ball z (4 * r))
    (hin : ∀ t ∈ Ioo α β, η t ∈ ball z (4 * r)) :
    sec8Alpha η z r τ = α := by
  have hαmem : α ∈ sec8PriorHit η (ball z (4 * r))ᶜ τ :=
    Or.inr ⟨hατ.le, houtα⟩
  apply le_antisymm
  · by_contra hnot
    have hlt : α < sec8Alpha η z r τ := lt_of_not_ge hnot
    have hτ : sec8Alpha η z r τ ≤ τ := sec8_alpha_le η z r τ
    have hball : η (sec8Alpha η z r τ) ∈ ball z (4 * r) :=
      hin _ ⟨hlt, hτ.trans_lt hτβ⟩
    have hmem := sec8LastHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
    rcases hmem with hzero | ⟨_, hout⟩
    · have : sec8Alpha η z r τ = 0 := hzero
      exact (not_le_of_gt hlt) (this ▸ bot_le)
    · exact hout hball
  · exact le_sSup hαmem

theorem sec8Beta_eq_of_component (η : C(unitInterval, Rd d)) (z : Rd d)
    (r : ℝ) {α β τ : unitInterval} (hατ : α < τ) (hτβ : τ < β)
    (houtβ : η β ∉ ball z (4 * r))
    (hin : ∀ t ∈ Ioo α β, η t ∈ ball z (4 * r)) :
    sec8Beta η z r τ = β := by
  have hβmem : β ∈ sec8FollowingHit η (ball z (4 * r))ᶜ τ :=
    Or.inr ⟨hτβ.le, houtβ⟩
  apply le_antisymm
  · exact sInf_le hβmem
  · by_contra hnot
    have hlt : sec8Beta η z r τ < β := lt_of_not_ge hnot
    have hτ : τ ≤ sec8Beta η z r τ := sec8_le_beta η z r τ
    have hball : η (sec8Beta η z r τ) ∈ ball z (4 * r) :=
      hin _ ⟨hατ.trans_le hτ, hlt⟩
    have hmem := sec8FirstHit_mem η (ball z (4 * r))ᶜ isOpen_ball.isClosed_compl τ
    rcases hmem with hone | ⟨_, hout⟩
    · have : sec8Beta η z r τ = 1 := hone
      exact (not_le_of_gt hlt) (this ▸ le_top)
    · exact hout hball

/-- The Borel closed-collector hitting times are the infimum and supremum
of all collector times in the given component. -/
theorem sec8_collector_times_eq (η : C(unitInterval, Rd d)) (V : Set (Rd d))
    (z : Rd d) (r : ℝ) {α β : unitInterval}
    (houtα : η α ∉ ball z (4 * r)) (houtβ : η β ∉ ball z (4 * r))
    (hVball : closure V ⊆ ball z (4 * r))
    (hvisit : ∃ t ∈ Ioo α β, η t ∈ V) :
    let S : Set unitInterval := {t | t ∈ Ioo α β ∧ η t ∈ closure V}
    α < sec8FirstHit η (closure V) α ∧
    sec8FirstHit η (closure V) α ≤ sec8LastHit η (closure V) β ∧
    sec8LastHit η (closure V) β < β ∧
    sec8FirstHit η (closure V) α = sInf S ∧
    sec8LastHit η (closure V) β = sSup S := by
  dsimp only
  obtain ⟨s, ⟨hαs, hsβ⟩, hsV⟩ := hvisit
  have hsF : η s ∈ closure V := subset_closure hsV
  let σ₁ := sec8FirstHit η (closure V) α
  let σ₂ := sec8LastHit η (closure V) β
  have hσ₁s : σ₁ ≤ s := sInf_le (show s ∈ sec8FollowingHit η (closure V) α from
    Or.inr ⟨hαs.le, hsF⟩)
  have hsσ₂ : s ≤ σ₂ := le_sSup (show s ∈ sec8PriorHit η (closure V) β from
    Or.inr ⟨hsβ.le, hsF⟩)
  have hσ₁F : η σ₁ ∈ closure V := by
    have hm := sec8FirstHit_mem η (closure V) isClosed_closure α
    rcases hm with hone | ⟨_, hF⟩
    · have hσ₁top : σ₁ = 1 := hone
      have : (1 : unitInterval) ≤ s := hσ₁top ▸ hσ₁s
      exact False.elim ((not_le_of_gt (hsβ.trans_le le_top)) this)
    · exact hF
  have hσ₂F : η σ₂ ∈ closure V := by
    have hm := sec8LastHit_mem η (closure V) isClosed_closure β
    rcases hm with hzero | ⟨_, hF⟩
    · have hσ₂zero : σ₂ = 0 := hzero
      have : s ≤ (0 : unitInterval) := hσ₂zero ▸ hsσ₂
      exact False.elim ((not_le_of_gt (bot_le.trans_lt hαs)) this)
    · exact hF
  have hασ₁ : α < σ₁ := by
    have hαle : α ≤ σ₁ := by
      have hm := sec8FirstHit_mem η (closure V) isClosed_closure α
      rcases hm with hone | ⟨hα, _⟩
      · rw [show σ₁ = 1 from hone]
        exact le_top
      · exact hα
    exact lt_of_le_of_ne hαle (by
      intro heq
      exact houtα (hVball (heq ▸ hσ₁F)))
  have hσ₂β : σ₂ < β := by
    have hle : σ₂ ≤ β := by
      have hm := sec8LastHit_mem η (closure V) isClosed_closure β
      rcases hm with hzero | ⟨hβ, _⟩
      · rw [show σ₂ = 0 from hzero]
        exact bot_le
      · exact hβ
    exact lt_of_le_of_ne hle (by
      intro heq
      exact houtβ (hVball (heq ▸ hσ₂F)))
  have hσ₁mem : σ₁ ∈ {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V} :=
    ⟨⟨hασ₁, hσ₁s.trans_lt hsβ⟩, hσ₁F⟩
  have hσ₂mem : σ₂ ∈ {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V} :=
    ⟨⟨hαs.trans_le hsσ₂, hσ₂β⟩, hσ₂F⟩
  have hσ₁least : ∀ t ∈ {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V}, σ₁ ≤ t := by
    intro t ht
    exact sInf_le (show t ∈ sec8FollowingHit η (closure V) α from
      Or.inr ⟨ht.1.1.le, ht.2⟩)
  have hσ₂greatest : ∀ t ∈ {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V}, t ≤ σ₂ := by
    intro t ht
    exact le_sSup (show t ∈ sec8PriorHit η (closure V) β from
      Or.inr ⟨ht.1.2.le, ht.2⟩)
  refine ⟨hασ₁, hσ₁s.trans hsσ₂, hσ₂β, ?_, ?_⟩
  · have hl : σ₁ ≤ sInf {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V} :=
      le_sInf hσ₁least
    have hr : sInf {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V} ≤ σ₁ :=
      sInf_le hσ₁mem
    exact le_antisymm hl hr
  · have hl : σ₂ ≤ sSup {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V} :=
      le_sSup hσ₂mem
    have hr : sSup {t : unitInterval | t ∈ Ioo α β ∧ η t ∈ closure V} ≤ σ₂ :=
      sSup_le hσ₂greatest
    exact le_antisymm hl hr

/-- On length metrics and paths with endpoints outside the trap ball, the
countable Borel test is exactly the source excursion predicate. -/
theorem ExcBorel_iff_Exc (η : C(unitInterval, Rd d)) (D : ContMetric d)
    (V : Set (Rd d)) (z : Rd d) (r ϑ : ℝ)
    (h0 : η 0 ∉ ball z (4 * r)) (h1 : η 1 ∉ ball z (4 * r))
    (hV : IsOpen V) (hVball : closure V ⊆ ball z (4 * r))
    (hD : D.IsLength) : ExcBorel η D V z r ϑ ↔ Exc η D V z r ϑ := by
  constructor
  · rintro ⟨n, m, hAt⟩
    let τ := TopologicalSpace.denseSeq unitInterval n
    let υ := TopologicalSpace.denseSeq unitInterval m
    let α := sec8Alpha η z r τ
    let β := sec8Beta η z r τ
    change η τ ∈ ball z (4 * r) ∧ α < τ ∧ τ < β ∧
      α < υ ∧ υ < β ∧ η υ ∈ V ∧
      α < sec8SigmaFirst η V z r τ ∧
      sec8SigmaFirst η V z r τ ≤ sec8SigmaLast η V z r τ ∧
      sec8SigmaLast η V z r τ < β ∧
      ENNReal.ofReal ϑ ≤ D.chainInf (ball z (4 * r))
        (η (sec8SigmaFirst η V z r τ))
        (η (sec8SigmaLast η V z r τ)) at hAt
    rcases hAt with ⟨hτball, hατ, hτβ, hαυ, hυβ, hυV,
      _, _, _, hchain⟩
    have hinside : ∀ t ∈ Ioo α β, η t ∈ ball z (4 * r) := by
      intro t ht
      rcases lt_trichotomy t τ with hlt | heq | hgt
      · exact sec8_in_ball_after_alpha η z r τ t ⟨ht.1, hlt⟩
      · simpa only [heq] using hτball
      · exact sec8_in_ball_before_beta η z r τ t ⟨hgt, ht.2⟩
    have houtα := sec8_alpha_boundary η z r h0 τ
    have houtβ := sec8_beta_boundary η z r h1 τ
    have hvisit : ∃ t ∈ Ioo α β, η t ∈ V := ⟨υ, ⟨hαυ, hυβ⟩, hυV⟩
    obtain ⟨_, _, _, hσ₁, hσ₂⟩ :=
      sec8_collector_times_eq η V z r houtα houtβ hVball hvisit
    refine ⟨α, β, hατ.trans hτβ, houtα, houtβ, hinside, hvisit, ?_⟩
    rw [← hσ₁, ← hσ₂, D.internal_eq_chainInf hD isOpen_ball]
    exact hchain
  · rintro ⟨α, β, hαβ, houtα, houtβ, hinside, hvisit, hthreshold⟩
    obtain ⟨s, hs, hsV⟩ := hvisit
    have hvisit' : ∃ t ∈ Ioo α β, η t ∈ V := ⟨s, hs, hsV⟩
    have hsball : η s ∈ ball z (4 * r) :=
      hVball (subset_closure hsV)
    have hUτ : IsOpen (Ioo α β ∩ η ⁻¹' ball z (4 * r)) :=
      isOpen_Ioo.inter (isOpen_ball.preimage η.continuous)
    obtain ⟨n, hn⟩ :=
      (TopologicalSpace.denseRange_denseSeq unitInterval).exists_mem_open
        hUτ ⟨s, hs, hsball⟩
    have hUυ : IsOpen (Ioo α β ∩ η ⁻¹' V) :=
      isOpen_Ioo.inter (hV.preimage η.continuous)
    obtain ⟨m, hm⟩ :=
      (TopologicalSpace.denseRange_denseSeq unitInterval).exists_mem_open
        hUυ ⟨s, hs, hsV⟩
    let τ := TopologicalSpace.denseSeq unitInterval n
    let υ := TopologicalSpace.denseSeq unitInterval m
    have hατ : α < τ := hn.1.1
    have hτβ : τ < β := hn.1.2
    have hαeq : sec8Alpha η z r τ = α :=
      sec8Alpha_eq_of_component η z r hατ hτβ houtα hinside
    have hβeq : sec8Beta η z r τ = β :=
      sec8Beta_eq_of_component η z r hατ hτβ houtβ hinside
    obtain ⟨hασ₁, hσ₁σ₂, hσ₂β, hσ₁, hσ₂⟩ :=
      sec8_collector_times_eq η V z r houtα houtβ hVball hvisit'
    refine ⟨n, m, ?_⟩
    change η τ ∈ ball z (4 * r) ∧
      sec8Alpha η z r τ < τ ∧ τ < sec8Beta η z r τ ∧
      sec8Alpha η z r τ < υ ∧ υ < sec8Beta η z r τ ∧ η υ ∈ V ∧
      sec8Alpha η z r τ < sec8SigmaFirst η V z r τ ∧
      sec8SigmaFirst η V z r τ ≤ sec8SigmaLast η V z r τ ∧
      sec8SigmaLast η V z r τ < sec8Beta η z r τ ∧
      ENNReal.ofReal ϑ ≤ D.chainInf (ball z (4 * r))
        (η (sec8SigmaFirst η V z r τ))
        (η (sec8SigmaLast η V z r τ))
    simp only [sec8SigmaFirst, sec8SigmaLast, hαeq, hβeq]
    refine ⟨hn.2, hατ, hτβ, hm.1.1, hm.1.2, hm.2,
      hασ₁, hσ₁σ₂, hσ₂β, ?_⟩
    rw [hσ₁, hσ₂, ← D.internal_eq_chainInf hD isOpen_ball]
    exact hthreshold
end HigherDimLQGMetric
