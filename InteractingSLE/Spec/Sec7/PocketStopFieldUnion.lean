/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopFieldChart

/-!
# The marked union law at `T(q)`: from Aux. lemma 35's `Γ ∪ R_T` to Aux. lemma 124's `B ∪ R_T`

Packet PROVE-STRIPSYS35 (PROVE-STRIPSYS33 §5.1). Specification §7.4, Aux. lemma 124 (`source/spec/p385-432.md`
L171–L196, pp. 393–394: "Assume the marked optional union law for `A ∪ R_t` … Then `B ∪ R_T` has the corresponding full
marked local-set law") and Aux. lemmas 35–36 (`source/spec/p145-192.md` L908–L940: "the marked stopping-time local-set
law, retaining these curve labels").

PROVE-STRIPSYS33's named input `PocketStop.PocketStopUnionLaw` is the marked union law of Aux. lemma 124's set
`B ∪ R_{T(q)}` (`B = ℍ ∖ C` the exterior of the pocket `C`, `R_{T(q)}` the counterflow hull at the ambient stop). The
union produced by Lemma 6.2 is Aux. lemma 35's `A_T = Γ ∪ R_T` (`Γ` the walls in the counterflow chart). Here the first
follows from the second:

* **`disjoint_extHullSet_iff`** (deterministic): for an open pocket `C ⊆ ℍ` with `Γ ∩ C = ∅` and `∂C ∩ ℍ ⊆ Γ`, and an
  open `U ⊆ ℍ`, the set `B ∪ F` avoids `U` iff `Γ ∪ F` avoids `U` and the points of a fixed dense sequence lying in
  `U` lie in `C` (every component of `U` is open, hence contains such a point, and a connected set meeting `C` and
  avoiding `∂C ∩ ℍ ⊆ Γ` stays in `C`);
* **`pocketStopUnionLaw_of_wallsLaw`**: hence the history-marked locality and the hitting measurability pass from any
  random set equal to `Γ ∪ F` on the live event (`PocketStopWallsLaw`) to `B ∪ F` — the pocket events of the dense
  points are walls' events, absorbed into the marks;
* **`pocketStopUnionLaw_cfPocket`**: the same for the strip system's change pocket with
  `Γ = m(range R ∪ range L)` (Aux. lemma 35's walls), every pocket hypothesis from the change configuration.

Ruling R48: nothing here uses Theorem 1.2/1.3 or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopField

open QuantumZipper (H)
open LQGMetric (DistOn)
open PocketTraversal PocketAdapt Lemma71C LocalSets WholeField PocketCoupling PocketUnionPt PocketStop

/-! ### The avoidance events of `B ∪ F` and of `Γ ∪ F` -/

section Det

/-- **The avoidance identity** (deterministic): for an open `C ⊆ ℍ` whose frontier in `ℍ` lies on `Γ` and which `Γ`
does not meet in `ℍ`, an open `U ⊆ ℍ` avoids `ℍ ∩ (Cᶜ ∪ F)` iff it avoids `ℍ ∩ (Γ ∪ F)` and every point of the dense
sequence `e` lying in `U` lies in `C`. -/
theorem disjoint_extHullSet_iff {C Γ F U : Set ℂ} (hCo : IsOpen C) (hΓC : Disjoint (H ∩ Γ) C) (hfr : frontier C ∩ H ⊆ Γ)
    (hUo : IsOpen U) (hUH : U ⊆ H) {e : ℕ → ℂ} (he : DenseRange e) :
    Disjoint (extHullSet C F) U ↔ Disjoint (H ∩ (Γ ∪ F)) U ∧ ∀ n, e n ∈ U → e n ∈ C := by
  constructor
  · intro hd
    have hUC : ∀ z ∈ U, z ∈ C ∧ z ∉ F := fun z hz => by
      have hz' : z ∉ extHullSet C F := fun h => Set.disjoint_left.1 hd h hz
      simp only [extHullSet, mem_inter_iff, mem_union, mem_compl_iff, not_and, not_or, not_not] at hz'
      exact hz' (hUH hz)
    refine ⟨Set.disjoint_left.2 fun z hz hzU => ?_, fun n hn => (hUC _ hn).1⟩
    rcases hz.2 with hΓ | hF
    · exact Set.disjoint_left.1 hΓC ⟨hz.1, hΓ⟩ (hUC z hzU).1
    · exact (hUC z hzU).2 hF
  · rintro ⟨hd, hpt⟩
    refine Set.disjoint_left.2 fun z hz hzU => ?_
    rcases hz.2 with hzC | hF
    · set V := connectedComponentIn U z with hV
      have hVo : IsOpen V := hUo.connectedComponentIn
      have hzV : z ∈ V := mem_connectedComponentIn hzU
      obtain ⟨n, hn⟩ := he.exists_mem_open hVo ⟨z, hzV⟩
      have hnU : e n ∈ U := connectedComponentIn_subset U z hn
      have hsub : V ⊆ C := isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hCo
        ⟨e n, hn, hpt n hnU⟩ fun w ⟨hwcl, hwV⟩ => by
          by_contra hwC
          have hwU : w ∈ U := connectedComponentIn_subset U z hwV
          have hwfr : w ∈ frontier C := ⟨hwcl, by rw [hCo.interior_eq]; exact hwC⟩
          exact Set.disjoint_left.1 hd ⟨hUH hwU, Or.inl (hfr ⟨hwfr, hUH hwU⟩)⟩ hwU
      exact hzC (hsub hzV)
    · exact Set.disjoint_left.1 hd ⟨hz.1, Or.inr hF⟩ hzU

end Det

/-! ### The union law of `B ∪ R_{T(q)}` from the union law of `Γ ∪ R_{T(q)}` -/

section Walls

variable {Ω : Type*}

/-- **The marked union law of `Γ ∪ R_{T(q)}` at the ambient stop** (Aux. lemma 35's marked stopping-time local-set law
of the walls `Γ` together with the counterflow hull `F` at `T(q)`, with the relative history as marks): some
hitting-measurable random set, history-marked avoidance-local for `𝓦 ∨ σ(A ∩ prefix events up to q)`, equals
`ℍ ∩ (Γ ∪ F)` on the live event `A ∩ {q < ζ}`. -/
def PocketStopWallsLaw (𝓦 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (Γ F : Ω → Set ℂ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (q : ℝ≥0) : Prop :=
  ∃ E : Ω → Set ℂ, Measurable[mΩ, hittingSigma] E ∧ IsHistoryAvoidanceLocal (locPrefixSigma 𝓦 A γ q) E h₀ P ∧
    ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → E ω = H ∩ (Γ ω ∪ F ω)

variable {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The walls' event that the points of the dense sequence lying in `U` lie in the pocket. -/
def ptEvent (A : Set Ω) (C : Ω → Set ℂ) (e : ℕ → ℂ) (U : Set ℂ) : Set Ω :=
  {ω | ∀ n, e n ∈ U → ω ∈ A ∧ e n ∈ C ω}

omit mΩ in
theorem measurableSet_ptEvent {A : Set Ω} {C : Ω → Set ℂ} (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (e : ℕ → ℂ) (U : Set ℂ) : MeasurableSet[𝓦] (ptEvent A C e U) := by
  have e1 : ptEvent A C e U = ⋂ n, {ω | e n ∈ U → ω ∈ A ∧ e n ∈ C ω} := by
    ext ω
    simp only [ptEvent, mem_ofPred_eq, mem_iInter]
  rw [e1]
  refine MeasurableSet.iInter fun n => ?_
  by_cases hn : e n ∈ U
  · simp only [hn, true_imp_iff]
    exact hCm (e n)
  · simp only [hn, false_imp_iff, ofPred_true]
    exact MeasurableSet.univ

/-- **The marked union law of `B ∪ R_{T(q)}` from that of `Γ ∪ R_{T(q)}`** (Aux. lemma 124 from Aux. lemma 35): if on
`A` the pocket `C ⊆ ℍ` is open, does not meet the walls `Γ` in `ℍ`, has its frontier in `ℍ` on `Γ`, and its membership
events at fixed points are walls' events, then `PocketStopWallsLaw` implies `PocketStopUnionLaw`. -/
theorem pocketStopUnionLaw_of_wallsLaw {A : Set Ω} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} (h𝓦 : 𝓦 ≤ mΩ)
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ) {C Γ F : Ω → Set ℂ}
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω}) (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω) {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : PocketStopWallsLaw 𝓦 P A γ Γ F h₀ q) : PocketStopUnionLaw 𝓦 P A γ C F h₀ q := by
  classical
  obtain ⟨E', hE'm, hE'loc, hE'eq⟩ := hW
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set Lv : Set Ω := {ω | ω ∈ A ∧ (q : ℝ≥0∞) < capLife (γ ω)} with hLv
  have hLvH : MeasurableSet[locPrefixSigma 𝓦 A γ q] Lv := measurableSet_live (𝓦 := 𝓦) A γ q
  have hW𝓗 : 𝓦 ≤ locPrefixSigma 𝓦 A γ q := le_sup_left
  -- the key identity on the live event, for open `U ⊆ ℍ`
  have key : ∀ U : Set ℂ, IsOpen U → U ⊆ H → ∀ ω ∈ Lv,
      (Disjoint (liveExt A γ C F q ω) U ↔ Disjoint (E' ω) U ∧ ω ∈ ptEvent A C e U) := by
    intro U hUo hUH ω hω
    rw [liveExt_of_live hω, hE'eq ω hω.1 hω.2,
      disjoint_extHullSet_iff (hCo ω hω.1) (hΓC ω hω.1) (hfr ω hω.1) hUo hUH he]
    exact and_congr_right fun _ => ⟨fun h n hn => ⟨hω.1, h n hn⟩, fun h n hn => (h n hn).2⟩
  -- off the live event `liveExt = ℍ` meets every nonempty `U ⊆ ℍ`
  have off : ∀ U : Set ℂ, U.Nonempty → U ⊆ H → ∀ ω ∉ Lv, ¬ Disjoint (liveExt A γ C F q ω) U := by
    intro U hU hUH ω hω hd
    rw [liveExt_of_not_live hω] at hd
    obtain ⟨z, hz⟩ := hU
    exact Set.disjoint_left.1 hd (hUH hz) hz
  refine ⟨liveExt A γ C F q, ?_, ?_, fun ω hω hq => liveExt_of_live ⟨hω, hq⟩⟩
  · -- hitting measurability
    refine @measurable_generateFrom Ω (Set ℂ) mΩ _ _ ?_
    rintro _ ⟨U, hUo, hUH, rfl⟩
    rcases U.eq_empty_or_nonempty with hU | hU
    · have e0 : liveExt A γ C F q ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} = ∅ := by
        ext ω
        simp only [hU, inter_empty, Set.not_nonempty_empty, ofPred_false, preimage_empty, mem_empty_iff_false]
      rw [e0]
      exact MeasurableSet.empty
    · have e1 : liveExt A γ C F q ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
          Lvᶜ ∪ (Lv ∩ ((E' ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty}) ∪ (ptEvent A C e U)ᶜ)) := by
        ext ω
        simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_compl_iff, mem_inter_iff]
        rw [← Set.not_disjoint_iff_nonempty_inter, ← Set.not_disjoint_iff_nonempty_inter]
        by_cases hω : ω ∈ Lv
        · rw [key U hUo hUH ω hω]
          tauto
        · exact ⟨fun _ => Or.inl hω, fun _ => off U hU hUH ω hω⟩
      rw [e1]
      have hLm : MeasurableSet[mΩ] Lv := hpre _ hLvH
      exact hLm.compl.union (hLm.inter ((hE'm (MeasurableSpace.measurableSet_generateFrom ⟨U, hUo, hUH, rfl⟩)).union
        (h𝓦 _ (measurableSet_ptEvent hCm e U)).compl))
  · -- the history-marked locality
    intro U G hUH hG hd F₀ hF₀
    rcases (U : Set ℂ).eq_empty_or_nonempty with hU | hU
    · obtain ⟨g, hg, hge⟩ := hE'loc U G hUH hG hd F₀ hF₀
      refine ⟨g, hg, ?_⟩
      have e0 : {ω | Disjoint (liveExt A γ C F q ω) U} ∩ F₀ = {ω | Disjoint (E' ω) U} ∩ F₀ := by
        simp only [hU, disjoint_empty, ofPred_true]
      rw [e0]
      exact hge
    · have hF₁ : MeasurableSet[locPrefixSigma 𝓦 A γ q] (F₀ ∩ Lv ∩ ptEvent A C e U) :=
        (hF₀.inter hLvH).inter (hW𝓗 _ (measurableSet_ptEvent hCm e U))
      obtain ⟨g, hg, hge⟩ := hE'loc U G hUH hG hd _ hF₁
      refine ⟨g, hg, ?_⟩
      have e1 : {ω | Disjoint (liveExt A γ C F q ω) U} ∩ F₀ =
          {ω | Disjoint (E' ω) U} ∩ (F₀ ∩ Lv ∩ ptEvent A C e U) := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq]
        by_cases hω : ω ∈ Lv
        · rw [key U U.isOpen hUH ω hω]
          tauto
        · exact ⟨fun h => absurd h.1 (off U hU hUH ω hω), fun h => absurd h.2.1.2 hω⟩
      rw [e1]
      exact hge

end Walls

/-! ### The change pocket of the strip system -/

section Pocket

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

open WangWu (negInv)
open PocketCoord PocketJordan PocketMarks WangWu Lemma71I

/-- **The walls bound the change pocket** (both pocket shapes): the inverted walls do not meet the pocket in `ℍ`, and
the pocket's frontier in `ℍ` lies on them. -/
theorem cfPocket_walls_props {R L : ℝ≥0 → ℂ} {r : ℝ≥0} (h : IsChangeConfigInc R L r) :
    Disjoint (H ∩ negInv '' (range R ∪ range L)) (cfPocket R L r) ∧
      frontier (cfPocket R L r) ∩ H ⊆ negInv '' (range R ∪ range L) := by
  have hfr : frontier (cfPocket R L r) ⊆
      (range fun s => cfPt (toDisc (realPath R) s)) ∪ range fun s => cfPt (toDisc (realPath L) s) := by
    rcases h.changeCorner_props.1.1.lt_or_eq with hpos | h0
    · exact frontier_cfPocket_subset h (zero_notMem_closure_of_rightLo_pos h hpos)
    · exact frontier_cfPocket_subset_inf h h0.symm
  obtain ⟨h1, -, h3⟩ := wallsHullSet_props h hfr ∅
  refine ⟨Set.disjoint_left.2 fun z hz hzC => ?_, fun z hz => ?_⟩
  · have := h3 ⟨⟨hz.1, Or.inl hz.2⟩, hzC⟩
    exact this
  · rcases (h1 hz).2 with hΓ | hF
    · exact hΓ
    · exact hF.elim

/-- **The marked union law of `B ∪ R_{T(q)}` for the change pocket** from that of `m(walls) ∪ R_{T(q)}` (Aux. lemma 124
from Aux. lemma 35): on a walls-measurable event `A ⊆ G` of change configurations. -/
theorem pocketStopUnionLaw_cfPocket {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} (h𝓦 : 𝓦 ≤ mΩ)
    (hRm : ∀ t, Measurable[𝓦] fun ω => R ω t) (hLm : ∀ t, Measurable[𝓦] fun ω => L ω t) {G : Set Ω}
    (hGm : MeasurableSet[𝓦] G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) {A : Set Ω}
    (hA : MeasurableSet[𝓦] A) (hAG : A ⊆ G) {γ : Ω → ℝ → ℂ} {q : ℝ≥0} (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ)
    {F : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : PocketStopWallsLaw 𝓦 P A γ (fun ω => negInv '' (range (R ω) ∪ range (L ω))) F h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ (fun ω => cfPocket (R ω) (L ω) r) F h₀ q :=
  pocketStopUnionLaw_of_wallsLaw h𝓦 hpre (measurableSet_mem_cfPocket_of_subset hRm hLm hGm hG hA hAG)
    (fun ω hω => isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H)
    (fun ω hω => (cfPocket_walls_props (hG ω (hAG hω))).1) (fun ω hω => (cfPocket_walls_props (hG ω (hAG hω))).2)
    hW

end Pocket

end InteractingSLE.Sec7.PocketStopField
