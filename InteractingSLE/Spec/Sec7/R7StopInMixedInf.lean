/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7StopInMixed
import InteractingSLE.Spec.Sec7.R7StopInEraseInf

/-!
# Lemma R.3 and Consequence R.4 for an outer pocket opening at the flow seed

Packet PROVE-R7-STOPIN. Supplement §5.1, §5.3–§5.4 (`source/spec/p433-480.md` L930–L996, pp. 471–474), for the change
pocket `cfPocket R L r` whose lower corner is the common seed of the walls (`rightLo R L r = 0`): in the counterflow
chart `m(z) = −1/z` its junction is the original target `∞`, its sides are `cfArcRInf`, `cfArcLInf` from
`y₀ = cfArcRInf 0` to `∞`, and `σ = ∞` ("allowing the terminal original-target time for `σ`"). This is the shape of the
selected pocket when the two walls meet only at their seed (for instance two outer arms whose angles differ by more
than the critical angle).

* `midArcInf M τ_M`: the clipped certified frontier from `y₀` to `∞` (`exists_midArcInf`: continuous, injective,
  proper, reverse visited, every point visited, containing every point of `C̄ ∩ m(M)` in `ℍ`);
* `cfArcRInf_mem_of_outer`, `cfArcLInf_mem_of_outer`: an outer side lies in the forbidden side or on the clipped
  frontier;
* **`isErasurePocketInf_rightOuter`**, **`…_leftOuter`**, **`…_outerOuter`**: the erasure facts at infinity
  (`IsErasurePocketInf`), with (JP1) and the absence of a final gap proved from the walls' reverse visit order, the
  avoidance of the exterior sides, Aux. 37 along one barrier (`BarrierAttachConstInf`) and §5.4's equal gap endpoints
  (`PocketGapEqInf`).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology Function
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R7StopIn

open WangWu Lemma71I PocketCoord PocketJordan Sec6

/-! ### The inputs at infinity -/

/-- **Aux. lemma 37 along one barrier at infinity**: the last-visit attachment of the barrier `B` (parametrized from
`y₀` towards `∞`) does not move on an interval `[a, b]`, `a ≥ τ`, avoiding `C`. -/
def BarrierAttachConstInf (η : ℝ → ℂ) (C : Set ℂ) (B : ℝ → ℂ) (τ : ℝ) : Prop :=
  ∀ a b : ℝ, τ ≤ a → a ≤ b → (∀ t ∈ Icc a b, η t ∉ C) →
    lastVisit (fun t => η '' Icc 0 t) B b = lastVisit (fun t => η '' Icc 0 t) B a

/-- **§5.4, "Closed gaps have identical endpoints"**, for a pocket opening at the flow seed (`σ = ∞`). -/
def PocketGapEqInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) : Prop :=
  ∀ a b : ℝ, τ ≤ a → a < b → (∀ t ∈ Icc a b, η t ∉ C) →
    b ∈ closure {t | a < t ∧ η t ∈ C} → (a = τ ∨ a ∈ closure {t | τ < t ∧ η t ∈ C}) → η a = η b

/-! ### The clipped frontier at infinity -/

section Mid

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- **The clipped certified frontier from `y₀` to `∞`** in the counterflow chart: `v ↦ m(M̃(τ_M/(1 + v)))`. -/
def midArcInf (M : ℝ≥0 → ℂ) (τM : ℝ) (v : ℝ) : ℂ := cfPt (toDisc (realPath M) (τM / (1 + v)))

/-- A reverse-visited wall read from a disc time `u > 0` towards its seed is in reverse first-visit order at
infinity. -/
theorem rev_inf_of_wall {X : ℝ≥0 → ℂ} (hX : IsSimpleProper X) {η : ℝ → ℂ} (hη0 : η 0 = 0)
    (hrev : IsWallReverseVisit X η) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    IsReverseVisitOrderInf (fun v => cfPt (toDisc (realPath X) (u / (1 + v)))) fun t => η '' Icc 0 t := by
  have hd : ∀ v ∈ Ici (0 : ℝ), u / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv =>
    ⟨(div_one_add_mem hu hv).1, (div_one_add_mem hu hv).2.trans hu1⟩
  intro t v₁ hv₁ v₂ hv₂ h12 hvis
  have h1 : (0 : ℝ) < 1 + v₁ := by linarith [mem_Ici.1 hv₁]
  exact wall_rev hX hη0 hrev (hd v₂ hv₂) (hd v₁ hv₁) (div_le_div_of_nonneg_left hu.le h1 (by linarith)) hvis

/-- **The clipped frontier at infinity as a barrier** (Lemma R.3 for a pocket opening at the flow seed). -/
theorem exists_midArcInf (h : IsChangeConfigInc R L r) (hM : IsSimpleProper M)
    (hO : WangWu.IsOrderedArcs (realPath R) (realPath M) (realPath L)) (hcR : NoCommonArc M R)
    (hcL : NoCommonArc M L) {η : ℝ → ℂ} (hη0 : η 0 = 0) (hrevM : IsWallReverseVisit M η) :
    ∃ τM : ℝ, ContinuousOn (midArcInf M τM) (Ici 0) ∧ InjOn (midArcInf M τM) (Ici 0) ∧
      Tendsto (fun v => ‖midArcInf M τM v‖) atTop atTop ∧
      (IsReverseVisitOrderInf (midArcInf M τM) fun t => η '' Icc 0 t) ∧ midArcInf M τM 0 = cfArcRInf R L r 0 ∧
      (∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ midArcInf M τM '' Ici 0) ∧
      (IsWallVisited M η → ∀ v ∈ Ici (0 : ℝ), ∃ t, midArcInf M τM v ∈ η '' Icc 0 t) := by
  obtain ⟨σM, τM, h0σ, hστ, hτ1, -, hτb, -, hout⟩ := exists_midTimes h hO hcR hcL
  have hτ0 : 0 < τM := h0σ.trans_lt hστ
  have hαM := hM.isProperArc.isDiscCrosscut_toDisc
  obtain ⟨hc, hi, ht, himg, -⟩ := crosscut_arcInf_props hαM hτ0 hτ1
  have hd : ∀ v ∈ Ici (0 : ℝ), τM / (1 + v) ∈ Ioc (0 : ℝ) 1 := fun v hv =>
    ⟨(div_one_add_mem hτ0 hv).1, (div_one_add_mem hτ0 hv).2.trans hτ1⟩
  refine ⟨τM, hc, hi, ht, rev_inf_of_wall hM hη0 hrevM hτ0 hτ1, ?_, fun z hzc hzH hzM => ?_,
    fun hvis v hv => wall_visited hη0 hM hvis (hd v hv)⟩
  · simp only [midArcInf, add_zero, div_one]
    rw [hτb, IsChangeConfigInc.cfArcRInf_zero]
  · obtain ⟨t', ht'⟩ := hzM
    have hMH : M t' ∈ H := by rw [ht']; exact negInv_mem_H hzH
    have ht'0 : (0 : ℝ) < t' := by
      refine lt_of_le_of_ne t'.coe_nonneg fun h0 => ?_
      have : t' = 0 := by exact_mod_cast h0.symm
      rw [this, hM.2.2.1] at hMH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hMH)
    have hz : z = negInv (M t') := by rw [ht', negInv_negInv]
    have hcl := neg_cayley_mem_closure h.changePocket_subset_H hzc
    rw [hz, cayley_negInv (H_subset_Hbar' hMH) (WangWu.ne_zero_of_mem_H hMH), neg_neg,
      ← toDisc_realPath_discTime] at hcl
    have hmem := hout _ (discTime_mem_Icc t') hcl
    have hpos : 0 < discTime (t' : ℝ) := div_pos ht'0 (by linarith)
    have himg' : midArcInf M τM '' Ici 0 = cfPt '' (toDisc (realPath M) '' Ioc 0 τM) := himg
    rw [himg']
    refine ⟨_, ⟨_, ⟨hpos, hmem.2⟩, rfl⟩, ?_⟩
    rw [toDisc_realPath_discTime, cfPt_cayley (H_subset_Hbar' hMH) (WangWu.ne_zero_of_mem_H hMH), hz]

/-- **An outer right side at infinity**: every point of `cfArcRInf` is in `m(E)` or on the barrier `B`. -/
theorem cfArcRInf_mem_of_outer (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {E : Set ℂ}
    (houter : range R ⊆ E ∪ range M) {B : ℝ → ℂ} (hB0 : B 0 = cfArcRInf R L r 0)
    (hBmem : ∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ B '' Ici 0) {v : ℝ}
    (hv : v ∈ Ici (0 : ℝ)) : cfArcRInf R L r v ∈ negInv '' E ∪ B '' Ici 0 := by
  have hC := h.isCfPocketInf h0
  obtain ⟨-, hvv, huv, -⟩ := h.changeCorner_props
  have hu0 : 0 < rightHi R L r := h0 ▸ huv
  have hzcl : cfArcRInf R L r v ∈ closure (cfPocket R L r) :=
    frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inl ⟨v, hv, rfl⟩)
  rcases eq_or_lt_of_le (mem_Ici.1 hv) with hv0 | hv0
  · exact Or.inr ⟨0, self_mem_Ici, by rw [hB0, hv0]⟩
  · have hd : rightHi R L r / (1 + v) ∈ Ioo (0 : ℝ) 1 :=
      ⟨(div_one_add_mem hu0 hv).1, (div_one_add_lt hu0 hv0).trans_le hvv.2⟩
    obtain ⟨e, hpos⟩ := cfPt_toDisc_of_mem h.right hd
    have hz : cfArcRInf R L r v = negInv (R (arcTime (rightHi R L r / (1 + v))).toNNReal) := e
    rcases houter ⟨_, rfl⟩ with hE | hMr
    · exact Or.inl ⟨_, hE, hz.symm⟩
    · have hRH := h.right.2.2.2.1 _ hpos
      refine Or.inr (hBmem _ hzcl ?_ ?_)
      · rw [hz]; exact negInv_mem_H hRH
      · rw [hz, negInv_negInv]; exact hMr

/-- **An outer left side at infinity**: every point of `cfArcLInf` is in `m(E)` or on the barrier `B`. -/
theorem cfArcLInf_mem_of_outer (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {E : Set ℂ}
    (houter : range L ⊆ E ∪ range M) {B : ℝ → ℂ} (hB0 : B 0 = cfArcRInf R L r 0)
    (hBmem : ∀ z ∈ closure (cfPocket R L r), z ∈ H → negInv z ∈ range M → z ∈ B '' Ici 0) {v : ℝ}
    (hv : v ∈ Ici (0 : ℝ)) : cfArcLInf R L r v ∈ negInv '' E ∪ B '' Ici 0 := by
  have hC := h.isCfPocketInf h0
  obtain ⟨-, -, -, -, hbb, hab, -⟩ := h.changeCorner_props
  have ha0 := h.leftLo_eq_zero_of_rightLo_eq_zero h0
  have hb0 : 0 < leftHi R L r := ha0 ▸ hab
  have hzcl : cfArcLInf R L r v ∈ closure (cfPocket R L r) :=
    frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inr ⟨v, hv, rfl⟩)
  rcases eq_or_lt_of_le (mem_Ici.1 hv) with hv0 | hv0
  · exact Or.inr ⟨0, self_mem_Ici, by rw [hB0, ← hv0, hC.seed]⟩
  · have hd : leftHi R L r / (1 + v) ∈ Ioo (0 : ℝ) 1 :=
      ⟨(div_one_add_mem hb0 hv).1, (div_one_add_lt hb0 hv0).trans_le hbb.2⟩
    obtain ⟨e, hpos⟩ := cfPt_toDisc_of_mem h.left hd
    have hz : cfArcLInf R L r v = negInv (L (arcTime (leftHi R L r / (1 + v))).toNNReal) := e
    rcases houter ⟨_, rfl⟩ with hE | hMr
    · exact Or.inl ⟨_, hE, hz.symm⟩
    · have hLH := h.left.2.2.2.1 _ hpos
      refine Or.inr (hBmem _ hzcl ?_ ?_)
      · rw [hz]; exact negInv_mem_H hLH
      · rw [hz, negInv_negInv]; exact hMr

end Mid

/-! ### Assembly at infinity -/

section Assemble

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- A visited point of a barrier at infinity forces its start `y₀` to be visited. -/
theorem y_mem_of_barrierInf {B : ℝ → ℂ} (hrev : IsReverseVisitOrderInf B fun t => η '' Icc 0 t) {y₀ : ℂ}
    (hB0 : B 0 = y₀) {v s : ℝ} (hv : v ∈ Ici (0 : ℝ)) (h : B v ∈ η '' Icc 0 s) : y₀ ∈ η '' Icc 0 s :=
  hB0 ▸ hrev s 0 self_mem_Ici v hv (mem_Ici.1 hv) h

/-- The erasure facts at infinity from the pocket topology, two reverse-visited barriers covering the visited
frontier, the first visit of `y₀`, Aux. 37 along the first barrier and §5.4's gap equality. -/
theorem isErasurePocketInf_of_barriers (hη : IsLoewnerTrace W η) (h : IsChangeConfigInc R L r)
    (h0 : rightLo R L r = 0) {F : Set ℂ} {B₁ B₂ : ℝ → ℂ}
    (hB₁t : Tendsto (fun v => ‖B₁ v‖) atTop atTop)
    (hrev₁ : IsReverseVisitOrderInf B₁ fun t => η '' Icc 0 t) (hrev₂ : IsReverseVisitOrderInf B₂ fun t => η '' Icc 0 t)
    (h₁0 : B₁ 0 = cfArcRInf R L r 0) (h₂0 : B₂ 0 = cfArcRInf R L r 0)
    (hvis₁ : ∀ v ∈ Ici (0 : ℝ), ∃ t, B₁ v ∈ η '' Icc 0 t)
    (hfr : frontier (cfPocket R L r) ⊆ F ∪ (B₁ '' Ici 0 ∪ B₂ '' Ici 0)) (havoid : ∀ t, 0 ≤ t → η t ∉ F)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) B₁ (firstHit η (cfArcRInf R L r 0)))
    (hgap : PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0))) :
    IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0)) := by
  have hC := h.isCfPocketInf h0
  obtain ⟨hτ0, hτ, hτf⟩ := firstHit_spec hη.2.1 (h₁0 ▸ hvis₁ 0 self_mem_Ici)
  have hfrv : ∀ s, 0 ≤ s → η s ∈ frontier (cfPocket R L r) → cfArcRInf R L r 0 ∈ η '' Icc 0 s := by
    intro s hs hsf
    have hvs : η s ∈ η '' Icc 0 s := ⟨s, ⟨hs, le_rfl⟩, rfl⟩
    rcases hfr hsf with hF | ⟨v, hv, he⟩ | ⟨v, hv, he⟩
    · exact absurd hF (havoid s hs)
    · exact y_mem_of_barrierInf hrev₁ h₁0 hv (he ▸ hvs)
    · exact y_mem_of_barrierInf hrev₂ h₂0 hv (he ▸ hvs)
  exact ⟨hη.2.1, hC.isOpen, hτ0, fun t ht htC => lt_of_frontier_visit hη hC.isOpen hC.subset_H hτf hfrv ht htC,
    hτ, noFinalInf_of_attach hη.2.1 hC.isOpen hB₁t h₁0 hvis₁ hAC hτ0 hτ, hgap⟩

/-- **The erasure facts at infinity of a mixed pocket with an outer right arm** (the contained left side
`cfArcLInf` and the clipped `β_R` as barriers). -/
theorem isErasurePocketInf_rightOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : WangWu.IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η) (hrevM : IsWallReverseVisit M η)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r) (firstHit η (cfArcRInf R L r 0)))
    (hgap : PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0))) :
    IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0)) := by
  have hC := h.isCfPocketInf h0
  have hη0 : η 0 = 0 := hη.1
  obtain ⟨-, -, -, -, hbb, hab, -⟩ := h.changeCorner_props
  have hb0 : 0 < leftHi R L r := h.leftLo_eq_zero_of_rightLo_eq_zero h0 ▸ hab
  obtain ⟨τM, -, -, -, hBrev, hB0, hBmem, -⟩ := exists_midArcInf h hM hO hcR hcL hη0 hrevM
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' rightSideOf (range M) ∪ (cfArcLInf R L r '' Ici 0 ∪ midArcInf M τM '' Ici 0) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · rcases cfArcRInf_mem_of_outer h h0 houter hB0 hBmem hv with h' | h'
      exacts [Or.inl h', Or.inr (Or.inr h')]
    · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
  have hvisL' : ∀ v ∈ Ici (0 : ℝ), ∃ t, cfArcLInf R L r v ∈ η '' Icc 0 t := fun v hv =>
    wall_visited hη0 h.left hvisL ⟨(div_one_add_mem hb0 hv).1, (div_one_add_mem hb0 hv).2.trans hbb.2⟩
  exact isErasurePocketInf_of_barriers hη h h0 hC.tendsto₂ (rev_inf_of_wall h.left hη0 hrevL hb0 hbb.2) hBrev
    hC.seed hB0 hvisL' hfr (fun t ht => notMem_image_negInv (havoid t ht)) hAC hgap

/-- **The erasure facts at infinity of a mixed pocket with an outer left arm** (the contained right side
`cfArcRInf` and the clipped `β_L` as barriers). -/
theorem isErasurePocketInf_leftOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : WangWu.IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η) (hrevM : IsWallReverseVisit M η)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcRInf R L r) (firstHit η (cfArcRInf R L r 0)))
    (hgap : PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0))) :
    IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0)) := by
  have hC := h.isCfPocketInf h0
  have hη0 : η 0 = 0 := hη.1
  obtain ⟨-, hvv, huv, -⟩ := h.changeCorner_props
  have hu0 : 0 < rightHi R L r := h0 ▸ huv
  obtain ⟨τM, -, -, -, hBrev, hB0, hBmem, -⟩ := exists_midArcInf h hM hO hcR hcL hη0 hrevM
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' leftSideOf (range M) ∪ (cfArcRInf R L r '' Ici 0 ∪ midArcInf M τM '' Ici 0) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
    · rcases cfArcLInf_mem_of_outer h h0 houter hB0 hBmem hv with h' | h'
      exacts [Or.inl h', Or.inr (Or.inr h')]
  have hvisR' : ∀ v ∈ Ici (0 : ℝ), ∃ t, cfArcRInf R L r v ∈ η '' Icc 0 t := fun v hv =>
    wall_visited hη0 h.right hvisR ⟨(div_one_add_mem hu0 hv).1, (div_one_add_mem hu0 hv).2.trans hvv.2⟩
  exact isErasurePocketInf_of_barriers hη h h0 hC.tendsto₁ (rev_inf_of_wall h.right hη0 hrevR hu0 hvv.2) hBrev
    rfl hB0 hvisR' hfr (fun t ht => notMem_image_negInv (havoid t ht)) hAC hgap

/-- **The erasure facts at infinity of a pocket with two outer arms** (the two clipped certified frontiers as
barriers; Aux. 37 — Aux. 43 for an extremal arm — along the clipped `β_R`). -/
theorem isErasurePocketInf_outerOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {M₁ M₂ : ℝ≥0 → ℂ}
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : WangWu.IsOrderedArcs (realPath R) (realPath M₁) (realPath L))
    (hO₂ : WangWu.IsOrderedArcs (realPath R) (realPath M₂) (realPath L)) (hc₁R : NoCommonArc M₁ R)
    (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R) (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁) (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (hAC : ∀ τ₁ : ℝ, midArcInf M₁ τ₁ 0 = cfArcRInf R L r 0 →
      BarrierAttachConstInf η (cfPocket R L r) (midArcInf M₁ τ₁) (firstHit η (cfArcRInf R L r 0)))
    (hgap : PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0))) :
    IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) (firstHit η (cfArcRInf R L r 0)) := by
  have hC := h.isCfPocketInf h0
  have hη0 : η 0 = 0 := hη.1
  obtain ⟨τ₁, -, -, hB₁t, hB₁rev, hB₁0, hB₁mem, hB₁vis⟩ := exists_midArcInf h hM₁ hO₁ hc₁R hc₁L hη0 hrev₁
  obtain ⟨τ₂, -, -, -, hB₂rev, hB₂0, hB₂mem, -⟩ := exists_midArcInf h hM₂ hO₂ hc₂R hc₂L hη0 hrev₂
  have hfr : frontier (cfPocket R L r) ⊆ (negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂)) ∪
      (midArcInf M₁ τ₁ '' Ici 0 ∪ midArcInf M₂ τ₂ '' Ici 0) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · rcases cfArcRInf_mem_of_outer h h0 houterR hB₁0 hB₁mem hv with h' | h'
      exacts [Or.inl (Or.inl h'), Or.inr (Or.inl h')]
    · rcases cfArcLInf_mem_of_outer h h0 houterL hB₂0 hB₂mem hv with h' | h'
      exacts [Or.inl (Or.inr h'), Or.inr (Or.inr h')]
  have havoid' : ∀ t, 0 ≤ t → η t ∉ negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂) :=
    fun t ht hm => by
      rcases hm with hm | hm
      · exact notMem_image_negInv (fun h' => havoid t ht (Or.inl h')) hm
      · exact notMem_image_negInv (fun h' => havoid t ht (Or.inr h')) hm
  exact isErasurePocketInf_of_barriers hη h h0 hB₁t hB₁rev hB₂rev hB₁0 hB₂0 (hB₁vis hvis₁) hfr havoid'
    (hAC τ₁ hB₁0) hgap

end Assemble

end InteractingSLE.Sec7.R7StopIn
