/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.HOuterWire
import InteractingSLE.Spec.Sec7.R7SurviveChange
import InteractingSLE.Spec.Sec7.R7SurviveLoewner
import InteractingSLE.Spec.Sec7.R7StopInMixedInf
import InteractingSLE.Spec.Sec7.R7GapEqGeoGap
import InteractingSLE.Spec.Sec7.R7GateBridgeChange
import InteractingSLE.Spec.Sec7.OuterInCollarInf

/-!
# Theorem R.7's outer pockets: the pocket geometry `OuterGeom(Inf)` of one realization

Packet PROVE-R7-OUTERIN. `HOuter.R7OuterInputs.geom/geomInf` ask, per realization of a mixed or outer change pocket,
for the erasure facts of §5.4 (`R7StopIn.IsErasurePocket(Inf)`) and the relative Loewner conclusion of Aux. lemma 41
(`R7StopIn.RelLoewner`) in every Jordan coordinate (`HOuter.OuterGeom`, `HOuter.OuterGeomInf`). Here they are assembled
from the landed geometric results, case by case:

* **bounded mixed pockets** (one outer arm; `outerGeom_leftOuter`, `outerGeom_rightOuter`): from PROVE-R7-STOPIN's
  erasure assembly (`isErasurePocket_{left,right}Outer`), PROVE-R7-GAPEQ's physical gap equality
  (`R7Survive.pocketGapEq_{left,right}Outer`) and relative driver (`R7Survive.relLoewner_{left,right}Outer`). The only
  input beyond the walls' and the counterflow's pathwise configuration is Aux. lemma 37 along the contained side
  (`R7StopIn.BarrierAttachConst`, the germ comparison);
* **bounded pockets with two outer arms** (`outerGeom_outerOuter`): §5.4's gap equality is proved
  (`pocketGapEq_outerOuter`: exterior collars at every noncorner frontier point, PROVE-R7-GAPEQ's
  `R7GapEqGeo.pocketGapEq_outerOuter`); STOPIN's erasure assembly then needs Aux. 37 along the clipped `β_R`, and the
  relative driver is Aux. 41's conclusion;
* **pockets opening at the flow seed** (`outerGeomInf_{left,right}Outer`, `outerGeomInf_outerOuter`): STOPIN's
  assemblies at infinity from Aux. 37 along the contained (clipped) side, §5.4's gap equality at infinity (proved for
  two outer arms: `pocketGapEqInf_outerOuter`, `OuterInCollarInf`) and Aux. 41.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.OuterIn

open Sec6 WangWu Lemma71I PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen R7StopIn HOuter

section Bounded

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The pocket geometry of a bounded mixed pocket with an outer left arm** (`α_L ⊂ E_L ∪ β_L`, `M = β_L` between the
walls): the erasure facts and the relative driver from the pathwise configuration and Aux. lemma 37 along the
contained right side. -/
theorem outerGeom_leftOuter (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hηH : ∀ t, 0 < t → η t ∈ H)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η)
    (hrevM : IsWallReverseVisit M η) (hvisM : IsWallVisited M η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    OuterGeom R L r η := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hgap := R7Survive.pocketGapEq_leftOuter h h0 hM hO hcR hcL houter hη hW hW0 hηH hrevR hvisR hrevM h42 hAC
    havoid
  exact ⟨isErasurePocket_leftOuter h hb hM hO hcR hcL houter hη hW hW0 havoid hrevR hrevM hvisM h42 hAC hgap,
    fun ψ hψ => R7Survive.relLoewner_leftOuter h h0 hM hO hcR hcL houter hη hW hW0 hηH
      (PocketStopMarked.isJordanCoord_of_cf hψ) havoid hrevR hvisR hrevM hvisM h42 hAC⟩

/-- **The pocket geometry of a bounded mixed pocket with an outer right arm** (`α_R ⊂ E_R ∪ β_R`, `M = β_R` between
the walls): the erasure facts and the relative driver from the pathwise configuration and Aux. lemma 37 along the
contained left side. -/
theorem outerGeom_rightOuter (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hηH : ∀ t, 0 < t → η t ∈ H)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η)
    (hrevM : IsWallReverseVisit M η) (hvisM : IsWallVisited M η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))) :
    OuterGeom R L r η := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hgap := R7Survive.pocketGapEq_rightOuter h h0 hM hO hcR hcL houter hη hW hW0 hηH hrevL hvisL hrevM h42 hAC
    havoid
  exact ⟨isErasurePocket_rightOuter h hb hM hO hcR hcL houter hη hW hW0 havoid hrevL hrevM hvisM h42 hAC hgap,
    fun ψ hψ => R7Survive.relLoewner_rightOuter h h0 hM hO hcR hcL houter hη hW hW0 hηH
      (PocketStopMarked.isJordanCoord_of_cf hψ) havoid hrevL hvisL hrevM hvisM h42 hAC⟩

/-- **The relative Loewner conclusion of a bounded change pocket in every Jordan coordinate** (Aux. lemma 41's
conclusion, the second conjunct of `OuterGeom`). -/
def OuterRelLoewner (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, IsCfJordan R L r ψ →
    RelLoewner (fun v => ψ (erasedPath η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0)) v))
      (pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0)))

/-- **Aux. lemma 37 along the clipped `β_R`** of a bounded pocket with two outer arms (every clipping of `M₁` from
`m(x₀)` to `m(y₀)`), in the form of `isErasurePocket_outerOuter`. -/
def OuterOuterAttach (R L M₁ : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) : Prop :=
  ∀ σ₁ τ₁ : ℝ, midArc M₁ σ₁ τ₁ 0 = cfArcR R L r 0 → midArc M₁ σ₁ τ₁ 1 = cfArcR R L r 1 →
    BarrierAttachConst η (cfPocket R L r) (midArc M₁ σ₁ τ₁) (firstHit η (cfArcR R L r 1))
      (firstHit η (cfArcR R L r 0))

/-- **§5.4's gap equality of a bounded pocket with two outer arms** (`M₁ = β_R`, `M₂ = β_L` between the walls): every
noncorner frontier point has an exterior collar (both arms are outer), so PROVE-R7-GAPEQ's
`R7GapEqGeo.pocketGapEq_outerOuter` applies; the corner visits come from the clipped `β_R`. -/
theorem pocketGapEq_outerOuter (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) {M₁ M₂ : ℝ≥0 → ℂ}
    (hM₁ : IsSimpleProper M₁)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hη : IsLoewnerTrace W η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    PocketGapEq η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  obtain ⟨σ₁, τ₁, -, -, -, hB0, hB1, -, hBvis⟩ := exists_midArc h hb hM₁ hO₁ hc₁R hc₁L hη.1 hrev₁
  obtain ⟨hτ0, hτ, -⟩ := firstHit_spec hη.2.1 (hB1 ▸ hBvis hvis₁ 1 ⟨zero_le_one, le_rfl⟩)
  obtain ⟨-, -, hσf⟩ := firstHit_spec hη.2.1 (hB0 ▸ hBvis hvis₁ 0 ⟨le_rfl, zero_le_one⟩)
  refine R7GapEqGeo.pocketGapEq_outerOuter h h0 (R7FaceSelect.changePocket_subset_left_of_order h hO₁)
    (R7FaceSelect.changePocket_subset_right_of_order h hO₂) hη.2.1
    (F := negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂))
    ((R7FaceSelect.right_exterior_subset hO₁).trans subset_union_left)
    ((R7FaceSelect.left_exterior_subset hO₂).trans subset_union_right) Subset.rfl
    (R7GateBridge.no_interval_frontier hC hη.2.1 h42) (fun t ht hm => ?_) hτ0 hτ hσf
  rcases hm with hm | hm
  · exact notMem_image_negInv (fun hz => havoid t ht (Or.inl hz)) hm
  · exact notMem_image_negInv (fun hz => havoid t ht (Or.inr hz)) hm

/-- **The pocket geometry of a bounded pocket with two outer arms** (`M₁ = β_R`, `M₂ = β_L` between the walls): the
erasure facts from the pathwise configuration, Aux. lemma 37 along the clipped `β_R` and the gap equality
(`pocketGapEq_outerOuter`); the relative driver is Aux. lemma 41's conclusion. -/
theorem outerGeom_outerOuter (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r) {M₁ M₂ : ℝ≥0 → ℂ}
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R) (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁) (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : OuterOuterAttach R L M₁ r η) (hloc : OuterRelLoewner R L r η) :
    OuterGeom R L r η :=
  ⟨isErasurePocket_outerOuter h hb hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL hη hW hW0 havoid hrev₁ hrev₂
    hvis₁ h42 hAC (pocketGapEq_outerOuter h hb hM₁ hO₁ hO₂ hc₁R hc₁L hη havoid hrev₁ hvis₁ h42), hloc⟩

end Bounded

section Infinite

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The relative Loewner conclusion of a pocket opening at the flow seed in every Jordan coordinate at infinity**
(Aux. lemma 41 at infinity, the second conjunct of `OuterGeomInf`). -/
def OuterRelLoewnerInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) : Prop :=
  ∀ ψ : ℂ → ℂ, IsCfJordanInf R L r ψ →
    RelLoewner (fun v => ψ (erasedPathInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) v))
      (clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))

/-- **The pocket geometry at infinity of a mixed pocket with an outer left arm**: STOPIN's erasure at infinity from
the configuration, Aux. lemma 37 along the contained right side and §5.4's gap equality; Aux. lemma 41 at infinity. -/
theorem outerGeomInf_leftOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η) (hrevM : IsWallReverseVisit M η)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcRInf R L r) (firstHit η (cfArcRInf R L r 0)))
    (hgap : PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))
    (hloc : OuterRelLoewnerInf R L r η) :
    OuterGeomInf R L r η :=
  ⟨isErasurePocketInf_leftOuter h h0 hM hO hcR hcL houter hη havoid hrevR hvisR hrevM hAC hgap, hloc⟩

/-- **The pocket geometry at infinity of a mixed pocket with an outer right arm** (contained left side). -/
theorem outerGeomInf_rightOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M) (Lemma71I.realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L) (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    (hη : IsLoewnerTrace W η) (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
    (hrevL : IsWallReverseVisit L η) (hvisL : IsWallVisited L η) (hrevM : IsWallReverseVisit M η)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r) (firstHit η (cfArcRInf R L r 0)))
    (hgap : PocketGapEqInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))
    (hloc : OuterRelLoewnerInf R L r η) :
    OuterGeomInf R L r η :=
  ⟨isErasurePocketInf_rightOuter h h0 hM hO hcR hcL houter hη havoid hrevL hvisL hrevM hAC hgap, hloc⟩

/-- **Aux. lemma 37 along the clipped `β_R` at infinity** (every clipping of `M₁` from `m(y₀)`), in the form of
`isErasurePocketInf_outerOuter`. -/
def OuterOuterAttachInf (R L M₁ : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) : Prop :=
  ∀ τ₁ : ℝ, midArcInf M₁ τ₁ 0 = cfArcRInf R L r 0 →
    BarrierAttachConstInf η (cfPocket R L r) (midArcInf M₁ τ₁) (firstHit η (cfArcRInf R L r 0))

/-- **The pocket geometry at infinity of a pocket with two outer arms** (clipped `β_R` as the attachment barrier):
§5.4's gap equality at infinity is proved (`pocketGapEqInf_outerOuter`: exterior collars along both proper arms). -/
theorem outerGeomInf_outerOuter (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0) {M₁ M₂ : ℝ≥0 → ℂ}
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R) (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁) (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : OuterOuterAttachInf R L M₁ r η) (hloc : OuterRelLoewnerInf R L r η) :
    OuterGeomInf R L r η :=
  ⟨isErasurePocketInf_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL hη havoid hrev₁ hrev₂ hvis₁
    hAC (pocketGapEqInf_outerOuter h h0 hM₁ hO₁ hO₂ hc₁R hc₁L hη havoid hrev₁ hvis₁ h42), hloc⟩

end Infinite

end InteractingSLE.Sec7.OuterIn
