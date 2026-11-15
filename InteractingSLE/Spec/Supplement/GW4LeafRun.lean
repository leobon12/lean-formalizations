/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafChain
import InteractingSLE.Spec.Supplement.GW1WalkChainRun

/-!
# GW1's run induction with first-visit data (deterministic)

Packet PROVE-T14-GW4REG. `GW1WalkChain.walkChainRepresentation_of_pieceSimpleAt` builds the proper parametrization of
a boundary walk by induction over its run (`ArcHistory` for live states). This file repeats that induction with
`VHist` in place of `ArcHistory`, for one counterflow trace `γ`, given at each step the first-visit data of the new
arc:

* `PieceVisitOK γ c W S old` at each launch: the physical piece `f ∘ α` (for every boundary extension `f` of the
  launch chart and every generating trace `α`) is first visited in strict reverse order along itself after its seed,
  and each of its points after the seed strictly before every point of the old set (GW1, p. 619: "It lies in
  `η[0, T_{w_j}]` in reverse first-visit order", item 3);
* `ConnVisitOK γ q g S` at each real connector `g` from `q`: reverse order along it, and every point after `q`
  first visited strictly before `q`.

The conclusion (**`exists_reverseVisits_of_run`**): the completed walk has a proper parametrization from its root
with strict reverse first visits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW1X GW1Bookkeep GW1WalkChain Exist Exist.Staged Exist.StagedLaw

/-! ### The first-visit data of one step -/

/-- **First-visit data of a launched piece**: for every boundary extension `f` of the chart `c` and every generating
trace `α` of the piece's driver up to its stop `S`, the physical piece `f ∘ α` is first visited by `γ` in strict
reverse order along `(0, S]`, and each of its points after the seed strictly before every point of `old`. -/
def PieceVisitOK (γ : ℝ≥0 → ℂ) (c : Chart) (W : ℝ≥0 → ℝ) (S : ℝ≥0∞) (old : Set ℂ) : Prop :=
  ∀ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ), (∀ p ∈ QuantumZipper.Hbar, Tendsto c.2.1 (𝓝[QuantumZipper.H] p) (𝓝 (f p))) →
    IsGeneratingTrace W S α →
    (∀ t t' : ℝ≥0, 0 < t → t < t' → (t' : ℝ≥0∞) ≤ S →
      GB11.firstVisit γ (f (α t')) < GB11.firstVisit γ (f (α t))) ∧
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → ∀ p ∈ old, GB11.firstVisit γ (f (α t)) < GB11.firstVisit γ p

/-- **First-visit data of a real connector** `g` from `q` on `[0, S]`: strict reverse order along it, and every point
after `q` first visited strictly before `q`. -/
def ConnVisitOK (γ : ℝ≥0 → ℂ) (q : ℝ) (g : ℝ≥0 → ℂ) (S : ℝ≥0∞) : Prop :=
  (∀ t t' : ℝ≥0, 0 < t → t < t' → (t' : ℝ≥0∞) ≤ S → GB11.firstVisit γ (g t') < GB11.firstVisit γ (g t)) ∧
    ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) ≤ S → GB11.firstVisit γ (g t) < GB11.firstVisit γ (q : ℂ)

/-! ### The arcs of a piece, with their parametrization exposed -/

/-- `GW1Bookkeep.exists_isArc_of_pieceSimpleAt` with the arc exposed as `rescale (f ∘ α) T`. -/
theorem exists_rescale_of_pieceSimpleAt {c : Chart} {W : ℝ≥0 → ℝ} {T : ℝ≥0} {old : Set ℂ}
    {q₀ q₁ : ℝ} (hT : 0 < T) (h : PieceSimpleAt c W (T : ℝ≥0∞) old q₀ q₁) :
    ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ),
      (∀ p ∈ QuantumZipper.Hbar, Tendsto c.2.1 (𝓝[QuantumZipper.H] p) (𝓝 (f p))) ∧
      IsGeneratingTrace W (T : ℝ≥0∞) α ∧ IsArc (rescale (f ∘ α) T) ∧
      rescale (f ∘ α) T '' Iic 1 = c.tipSet
        (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) (T : ℝ≥0∞)).toNNReal) (T : ℝ≥0∞) ∧
      (∀ s ∈ Iic (1 : ℝ≥0), rescale (f ∘ α) T s ∈ QuantumZipper.Hbar) ∧
      rescale (f ∘ α) T 0 = (q₀ : ℂ) ∧ rescale (f ∘ α) T 1 = (q₁ : ℂ) ∧
      rescale (f ∘ α) T '' Iic 1 ∩ old = {rescale (f ∘ α) T 0} := by
  obtain ⟨f, α, C, hf, hC, hmaps, hW0, hWc, hgen, htrans, hinj, hStart, hEnd, havoid⟩ := h
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (T : ℝ≥0∞)} = Iic T := by
    ext t
    simp only [mem_ofPred_eq, mem_Iic, ENNReal.coe_le_coe]
  have hinj' : Set.InjOn (f ∘ α) (Iic T) := by
    intro s hs t ht hst
    exact hinj (hset ▸ hs) (hset ▸ ht) hst
  obtain ⟨hArc, hImage, h0, h1⟩ := exists_isArc_tipSet hf hT hgen hWc hW0 hinj'
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (T : ℝ≥0∞) → α t ∈ QuantumZipper.Hbar := by
    intro t ht
    exact Sec7.IsGeneratingTrace.mem_Hbar hgen
      (hWc.mono fun t hs => Set.mem_ofPred_eq.mpr (le_of_lt hs)) hW0 ht
  have hγH : ∀ s ∈ Iic (1 : ℝ≥0), rescale (f ∘ α) T s ∈ QuantumZipper.Hbar := by
    intro s hs
    have ht : min s 1 * T ∈ Iic T :=
      Set.mem_Iic.2 (mul_le_of_le_one_left (zero_le (a := T)) (min_le_right s 1))
    change f (α (min s 1 * T)) ∈ QuantumZipper.Hbar
    exact hmaps _ (hαH _ (ENNReal.coe_le_coe.2 ht))
  refine ⟨f, α, hf, hgen, hArc, hImage, hγH, h0.trans hStart, ?_, ?_⟩
  · have hEnd' : f (α T) = (q₁ : ℂ) := by simpa using hEnd (by simp)
    exact h1.trans hEnd'
  · rw [hImage, havoid, h0]

/-- `GW1Bookkeep.exists_isProperCurve_of_pieceSimpleAt` with the curve exposed as `f ∘ α`. -/
theorem exists_proper_of_pieceSimpleAt {c : Chart} {W : ℝ≥0 → ℝ} {old : Set ℂ}
    {q₀ q₁ : ℝ} (h : PieceSimpleAt c W ⊤ old q₀ q₁) :
    ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ),
      (∀ p ∈ QuantumZipper.Hbar, Tendsto c.2.1 (𝓝[QuantumZipper.H] p) (𝓝 (f p))) ∧
      IsGeneratingTrace W ⊤ α ∧ Supp9B.IsProperCurve (fun t => f (α t)) ∧ f (α 0) = (q₀ : ℂ) ∧
      range (fun t => f (α t)) = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) ⊤).toNNReal) ⊤ ∧
      c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) ⊤).toNNReal) ⊤ ∩ old = {f (α 0)} := by
  obtain ⟨f, α, C, hf, hC, hmaps, hW0, hWc, hgen, htrans, hinj, hStart, -, havoid⟩ := h
  have htime : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞)} = univ := by
    ext t
    simp
  have hαc : Continuous α := continuousOn_univ.1 (htime ▸ hgen.2.1)
  have hαH : ∀ t : ℝ≥0, α t ∈ QuantumZipper.Hbar := fun t =>
    Sec7.IsGeneratingTrace.mem_Hbar hgen
      (hWc.mono fun t hs => Set.mem_ofPred_eq.mpr (le_of_lt hs)) hW0 le_top
  have hfcont : ContinuousOn f QuantumZipper.Hbar := GW1P.continuousOn_of_tendsto hf
  let g : ℝ≥0 → ℂ := fun t => f (α t)
  have hgc : Continuous g := continuousOn_univ.1
    (hfcont.comp hαc.continuousOn fun t _ => hαH t)
  have hginj : Function.Injective g := by
    intro s t hst
    exact hinj (htime.symm ▸ Set.mem_univ s) (htime.symm ▸ Set.mem_univ t) hst
  have hgH : ∀ t, g t ∈ QuantumZipper.Hbar := fun t => hmaps _ (hαH t)
  have hgtr : Tendsto (fun t : ℝ≥0 => ‖g t‖) atTop atTop := by
    apply tendsto_atTop.2
    intro R
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((htrans rfl).eventually_ge_atTop (R + C))
    filter_upwards [eventually_atTop.2 ⟨T, fun t ht => hT t ht⟩] with t ht
    have hlarge : R + C ≤ ‖α t‖ := ht
    have hdist : ‖α t‖ - ‖g t‖ ≤ C := by
      calc
        ‖α t‖ - ‖g t‖ ≤ ‖α t - g t‖ := norm_sub_norm_le _ _
        _ = ‖f (α t) - α t‖ := by simp [g, norm_sub_rev]
        _ ≤ C := hC _ (hαH t)
    change R ≤ ‖g t‖
    linarith
  have htip : c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) ⊤).toNNReal) ⊤ =
      f '' (α '' univ) := by
    calc
      _ = f '' (α '' {t | (t : ℝ≥0∞) ≤ (⊤ : ℝ≥0∞)}) :=
        CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hWc hW0 fun t _ => hf _ (hαH t)
      _ = f '' (α '' univ) := by rw [htime]
  refine ⟨f, α, hf, hgen, ⟨hgc, hginj, hgH, hgtr⟩, hStart, ?_, havoid⟩
  rw [htip]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨α t, ⟨t, Set.mem_univ _, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨t, -, rfl⟩, rfl⟩
    exact ⟨t, rfl⟩

/-- The rescaled piece inherits the strict reverse order and the newness. -/
theorem arcOrd_rescale {γ : ℝ≥0 → ℂ} {g : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T)
    (hord : ∀ t t' : ℝ≥0, 0 < t → t < t' → t' ≤ T → GB11.firstVisit γ (g t') < GB11.firstVisit γ (g t)) :
    ArcOrd γ (rescale g T) := by
  intro s s' hs hss hs'
  have hs1 : s ≤ 1 := hss.le.trans hs'
  simp only [rescale, min_eq_left hs1, min_eq_left hs']
  exact hord _ _ (mul_pos hs hT) (mul_lt_mul_of_pos_right hss hT) (mul_le_of_le_one_left (zero_le (a := T)) hs')

theorem new_rescale {γ : ℝ≥0 → ℂ} {g : ℝ≥0 → ℂ} {T : ℝ≥0} (hT : 0 < T) {A : Set ℂ}
    (hnew : ∀ t : ℝ≥0, 0 < t → t ≤ T → ∀ p ∈ A, GB11.firstVisit γ (g t) < GB11.firstVisit γ p) :
    ∀ t : ℝ≥0, 0 < t → t ≤ 1 → ∀ p ∈ A, GB11.firstVisit γ (rescale g T t) < GB11.firstVisit γ p := by
  intro t ht ht1 p hp
  simp only [rescale, min_eq_left ht1]
  exact hnew _ (mul_pos ht hT) (mul_le_of_le_one_left (zero_le (a := T)) ht1) p hp


/-! ### The run induction -/

/-- A live state has a chronological history with first-visit data; a completed state has a proper parametrization
from the root with strict reverse first visits. -/
def StateRV (γ : ℝ≥0 → ℂ) (root : ℝ) (s : ExplState) : Prop :=
  (stStatus s = stDone ∧ ∃ g : ℝ≥0 → ℂ, Supp9B.IsProperCurve g ∧ g 0 = (root : ℂ) ∧
      range g = statePhysicalSet root s ∧ ReverseVisits γ g) ∨
    (stStatus s ≠ stDone ∧ VHist γ (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))

theorem stateRV_init (γ : ℝ≥0 → ℂ) (root : ℝ) : StateRV γ root (ExplState.init root) := by
  refine Or.inr ⟨?_, ?_⟩
  · intro heq
    cases heq
  · convert VHist.root (γ := γ) (x := (root : ℂ)) using 1 <;>
    simp only [statePhysicalSet, ExplState.init, List.not_mem_nil, iUnion_of_empty, iUnion_empty,
      union_empty, stPt]

theorem stateRV_launch {γ : ℝ≥0 → ℂ} {root : ℝ} {s : ExplState}
    (h : VHist γ (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))
    (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (hP : PieceSimpleAt (stChart s) D.1 D.2 (statePhysicalSet root s) (stPt s)
      (stPt (ExplState.launch s k D θ ⊤)))
    (hV : PieceVisitOK γ (stChart s) D.1 D.2 (statePhysicalSet root s)) :
    StateRV γ root (ExplState.launch s k D θ ⊤) := by
  have hset := statePhysicalSet_launch root s k D θ ⊤
  simp only [min_top_left] at hset
  by_cases htop : D.2 = ⊤
  · obtain ⟨f, α, hf, hα, hρ, hρ0, hρset, hρold⟩ := exists_proper_of_pieceSimpleAt (htop ▸ hP)
    obtain ⟨hord, hnew⟩ := hV f α hf (htop ▸ hα)
    have hmeet : ∀ t, f (α t) ∈ statePhysicalSet root s → t = 0 := by
      intro t ht
      have hm : f (α t) ∈ ({f (α 0)} : Set ℂ) := by
        rw [← hρold, ← hρset]
        exact ⟨⟨t, rfl⟩, ht⟩
      exact hρ.2.1 (mem_singleton_iff.1 hm)
    obtain ⟨g, hg, hg0, hgR, hgV⟩ := h.exists_reverseVisits hρ hρ0 hmeet
      (fun t t' ht htt => hord t t' ht htt (by rw [htop]; exact le_top))
      (fun t ht p hp => hnew t ht (by rw [htop]; exact le_top) p hp)
    refine Or.inl ⟨(launch_eq_of_top s k D θ ⊤ (by simp only [htop, min_self])).2.2.2.2.1, g, hg, hg0, ?_, hgV⟩
    rw [hgR]
    simpa only [htop, hρset] using hset.symm
  · have hnot : stStatus (ExplState.launch s k D θ ⊤) ≠ stDone := by
      obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
      simp only [ExplState.launch, min_top_left, htop, ↓reduceIte, not_top_lt]
      split_ifs <;> try (intro heq; cases heq)
      all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> intro heq <;> cases heq)
    refine Or.inr ⟨hnot, ?_⟩
    by_cases hzero : D.2 = 0
    · obtain ⟨hZ, hq⟩ := tipSet_zero_of_pieceSimpleAt (hzero ▸ hP)
      rw [hzero, hZ] at hset
      have hsingle : statePhysicalSet root s ∪ {(stPt s : ℂ)} = statePhysicalSet root s :=
        union_eq_left.2 (singleton_subset_iff.2 h.endpoint_mem)
      rw [hset, hsingle, hq]
      exact h
    · let T := D.2.toNNReal
      have hT : (T : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal htop
      have hTpos : 0 < T := by
        apply pos_iff_ne_zero.2
        intro h0
        apply hzero
        rw [← hT, h0, ENNReal.coe_zero]
      obtain ⟨f, α, hf, hα, hArc, hImage, hH, h0, h1, hmeet⟩ :=
        exists_rescale_of_pieceSimpleAt hTpos (hT.symm ▸ hP)
      obtain ⟨hord, hnew⟩ := hV f α hf (hT ▸ hα)
      have hHist := h.append (rescale (f ∘ α) T) hArc (fun t ht => hH t ht) h0
        (by
          intro t ht hmem
          apply hArc.2 ht (mem_Iic.2 zero_le)
          have hm : rescale (f ∘ α) T t ∈ ({rescale (f ∘ α) T 0} : Set ℂ) := by
            rw [← hmeet]; exact ⟨⟨t, ht, rfl⟩, hmem⟩
          exact mem_singleton_iff.1 hm)
        (arcOrd_rescale hTpos fun t t' ht htt ht' =>
          hord t t' ht htt (by rw [← hT]; exact ENNReal.coe_le_coe.2 ht'))
        (new_rescale hTpos fun t ht htT p hp =>
          hnew t ht (by rw [← hT]; exact ENNReal.coe_le_coe.2 htT) p hp)
      rw [hImage, hT, h1] at hHist
      rw [hset]
      exact hHist

theorem stateRV_moveAlong {γ : ℝ≥0 → ℂ} {root : ℝ} {s : ExplState}
    (h : VHist γ (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))
    (right : Bool) (x : ℝ) (mark : Bool)
    (hdir : if right then stPt s < x else x < stPt s)
    (hclear : ConnectorClearance root s (((↑) : ℝ → ℂ) ''
      (if right then Icc (stPt s) x else Icc x (stPt s))))
    (hV : ConnVisitOK γ (stPt s) (realArc (stPt s) x) 1) :
    StateRV γ root (ExplState.moveAlong s right x mark) := by
  have hne : stPt s ≠ x := by
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hdir
    · exact hdir.ne'
    · exact hdir.ne
  have himage : realArc (stPt s) x '' Iic 1 = ((↑) : ℝ → ℂ) ''
      (if right then Icc (stPt s) x else Icc x (stPt s)) := by
    rw [image_realArc]
    cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at hdir ⊢
    · rw [min_eq_right hdir.le, max_eq_left hdir.le]
    · rw [min_eq_left hdir.le, max_eq_right hdir.le]
  have hArc := isArc_realArc hne
  have hHist := h.append (realArc (stPt s) x) hArc
    (fun t _ => realArc_upper _ _ t) (realArc_zero _ _) (by
      intro t ht hmem
      apply hArc.2 ht (mem_Iic.2 (by norm_num))
      rw [realArc_zero]
      apply hclear _ _ hmem
      rw [← himage]
      exact ⟨t, ht, rfl⟩)
    (fun t t' ht htt ht' => hV.1 t t' ht htt (by exact_mod_cast ht'))
    (fun t ht ht1 p hp => lt_of_lt_of_le (hV.2 t ht (by exact_mod_cast ht1)) (h.endpoint_min p hp))
  rw [himage, realArc_one] at hHist
  refine Or.inr ⟨?_, ?_⟩
  · obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
    intro heq
    cases heq
  · rw [statePhysicalSet_moveAlong]
    simpa only [GW1W.stPt_moveAlong] using hHist

theorem stateRV_moveToEnd {γ : ℝ≥0 → ℂ} {root : ℝ} {s : ExplState}
    (h : VHist γ (root : ℂ) (statePhysicalSet root s) (stPt s : ℂ))
    (right : Bool) (hclear : ConnectorClearance root s (range (realRay right (stPt s))))
    (hV : ConnVisitOK γ (stPt s) (realRay right (stPt s)) ⊤) :
    StateRV γ root (ExplState.moveToEnd s right) := by
  have hmeet : ∀ t, realRay right (stPt s) t ∈ statePhysicalSet root s → t = 0 := by
    intro t ht
    apply (isProperCurve_realRay right (stPt s)).2.1
    rw [realRay_zero]
    exact hclear _ ⟨t, rfl⟩ ht
  obtain ⟨g, hg, hg0, hgR, hgV⟩ := h.exists_reverseVisits (isProperCurve_realRay right (stPt s))
    (realRay_zero _ _) hmeet (fun t t' ht htt => hV.1 t t' ht htt le_top)
    (fun t ht p hp => lt_of_lt_of_le (hV.2 t ht le_top) (h.endpoint_min p hp))
  refine Or.inl ⟨?_, g, hg, hg0, ?_, hgV⟩
  · obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
    rfl
  · rw [hgR, statePhysicalSet_moveToEnd]


section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {right : Bool}
  {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- First-visit data of the real connectors of one run, at its boundary-continuation instructions. -/
def WalkConnVisit (γ : ℝ≥0 → ℂ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (right : Bool) : Prop :=
  ∀ k, k < spec.2.2.length → k % 2 = 1 → let s := ExplState.run κ b jumps spec D k
    (∀ r x, (if r then stPt s < x else x < stPt s) →
      ExplState.contStep κ b jumps s none right = ExplState.moveAlong s r x true →
      ConnVisitOK γ (stPt s) (realArc (stPt s) x) 1) ∧
    (∀ r, ExplState.contStep κ b jumps s none right = ExplState.moveToEnd s r →
      ConnVisitOK γ (stPt s) (realRay r (stPt s)) ⊤)

/-- **GW1's walk with strict reverse first visits** (deterministic run induction): the hypotheses of
`GW1WalkChain.walkChainRepresentation_of_pieceSimpleAt`, together with the first-visit data of every launched piece
and every real connector, give a proper parametrization of the completed walk from `0` along which `γ` first visits
the points in strict reverse order. -/
theorem exists_reverseVisits_of_run (γ : ℝ≥0 → ℂ)
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1))))
    (hPV : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (k + 1)).2.2.2.1 k = some (c, θ') →
      PieceVisitOK γ c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)))
    (hC : WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps)
      (boundaryWalkSpec b jumps θ right) D)
    (hCV : WalkConnVisit (κ := κ) (b := b) (jumps := jumps) γ (boundaryWalkSpec b jumps θ right) D right)
    (hDone : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length) = stDone) :
    ∃ g : ℝ≥0 → ℂ, Supp9B.IsProperCurve g ∧ g 0 = 0 ∧
      range g = statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
        (boundaryWalkSpec b jumps θ right).2.2.length) ∧ ReverseVisits γ g := by
  let spec := boundaryWalkSpec b jumps θ right
  have hI : ∀ n, StateRV γ 0
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
    intro n
    induction n with
    | zero => exact stateRV_init γ 0
    | succ n ih =>
      by_cases hdone : stStatus
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) = stDone
      · have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
            ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
          rw [run_succ]
          cases hk : spec.2.2[n]? with
          | none => rfl
          | some a =>
            change ExplState.step κ b jumps false D
              (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (a, n) =
                ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n
            rcases a with ⟨a, t⟩ | r | ⟨v, r⟩
            · exact isTerminal_flowStep (Or.inl hdone) n (D n) a t
            · exact contStep_of_done hdone none r
            · exact contStep_of_done hdone (some v) r
        rw [heq]
        exact ih
      · have hHist : VHist γ (0 : ℂ)
            (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n))
            (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) : ℂ) := by
          rcases ih with ⟨hd, _⟩ | ⟨_, hh⟩
          · exact False.elim (hdone hd)
          · exact hh
        cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
            (n + 1)).2.2.2.1 n with
        | some p =>
          obtain ⟨c, θ'⟩ := p
          have hn : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
              (n + 1)).2.2.2.1 n ≠ none := by
            rw [hl]
            exact Option.some_ne_none _
          have heq := GW1W.launch_walk hn
          have hpiece := hP n c θ' hl hHist.endpoint_mem
          have hpv := hPV n c θ' hl
          obtain ⟨hev, hlen⟩ := GW1W.even_of_launches_walk hn
          have htime : instrTime spec n = ⊤ := by
            simp only [spec, instrTime, GW1Conn.getElem?_boundaryWalkSpec, hlen, hev, ↓reduceIte]
          obtain ⟨_, _, hc⟩ := eq_launch_of_launches spec D hl
          rw [htime, min_top_left, hc, heq] at hpiece
          rw [htime, min_top_left, hc] at hpv
          rw [heq]
          exact stateRV_launch hHist n (D n) θ hpiece hpv
        | none =>
          by_cases hlen : n < spec.2.2.length
          · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
            · have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
              have hnl := hl
              rw [heq] at hnl
              rw [heq, GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl]
              exact ih
            · have heq := GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen hodd
              rcases contStep_none_cases (κ := κ) b jumps
                (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) right
                with hs | hs | ⟨r, x, hd, hs⟩ | ⟨r, hs⟩
              · rw [heq, hs]
                exact ih
              · rw [heq, hs]
                refine Or.inr ⟨?_, hHist⟩
                intro hf
                cases hf
              · rw [heq, hs]
                exact stateRV_moveAlong hHist r x true hd ((hC n).1 r x (heq.trans hs))
                  ((hCV n hlen hodd).1 r x hd hs)
              · rw [heq, hs]
                exact stateRV_moveToEnd hHist r ((hC n).2 r (heq.trans hs)) ((hCV n hlen hodd).2 r hs)
          · have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
            ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n := by
              rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_right hlen]
            rw [heq]
            exact ih
  rcases hI spec.2.2.length with ⟨_, g, hg, hg0, hgR, hgV⟩ | ⟨hn, _⟩
  · exact ⟨g, hg, by simpa using hg0, hgR, hgV⟩
  · exact False.elim (hn hDone)

end Run

end GW4Leaf

end Theorem14

end InteractingSLE
