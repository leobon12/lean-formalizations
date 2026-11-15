/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12RemPassiveEvol
import InteractingSLE.Spec.Supplement.G12RemFar

/-!
# A passive zero-weight mark at a real point: the extended evolution

Packet PROVE-G12B. Proof of Corollary W0a (supplement §9, p. 528): "retain it as a passive zero-weight mark; this
does not change the driving law or the displayed cumulative weight." For an integrated `SLE_κ(ρ)` evolution of an
ordered force word and a point `y > 0` that is not a right mark but has a right mark `x_k < y` below it:

* `isSLEPathUpTo_insertNth`: inserting a force coordinate from `y`, ordered with the other right marks, at a
  position `p` of the right marks (`Fin.insertNth`), with weight `0`, gives a local integrated path of the extended
  word (the zero weight changes neither the driving equation nor the continuation threshold);
* `isIntegratedSLEEvolution_insertPassive`: **the extended evolution** — the same filtered probability space, driver,
  Brownian motion and lifetime, with the passive mark `passMark y ζ W (V^k)` inserted after the last mark `x_k < y`
  (`Sec4.isIntegratedSLEEvolution_iff_compEmb`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G12

/-! ### Inserting into an ordered tuple -/

theorem monotone_insertNth {n : ℕ} {f : Fin n → ℝ} (hf : Monotone f) (p : Fin (n + 1)) {x : ℝ}
    (hb : ∀ j : Fin n, j.castSucc < p → f j ≤ x) (ha : ∀ j : Fin n, p ≤ j.castSucc → x ≤ f j) :
    Monotone (Fin.insertNth p x f) := by
  intro i i' hii'
  rcases Fin.eq_self_or_eq_succAbove p i with hi | ⟨j, hj⟩ <;>
    rcases Fin.eq_self_or_eq_succAbove p i' with hi' | ⟨j', hj'⟩
  · rw [hi, hi']
  · rw [hi, hj'] at hii' ⊢
    rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact ha j' ((Fin.lt_succAbove_iff_le_castSucc _ _).1 (lt_of_le_of_ne hii' (Fin.succAbove_ne _ _).symm))
  · rw [hj, hi'] at hii' ⊢
    rw [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    exact hb j ((Fin.succAbove_lt_iff_castSucc_lt _ _).1 (lt_of_le_of_ne hii' (Fin.succAbove_ne _ _)))
  · rw [hj, hj'] at hii' ⊢
    rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    exact hf (Fin.succAbove_le_succAbove_iff.1 hii')

/-- A sum over the inserted tuple, when the inserted term vanishes. -/
theorem sum_insertNth_of_eq_zero {n : ℕ} (p : Fin (n + 1)) (g : Fin (n + 1) → ℝ) (hg : g p = 0) :
    ∑ i, g i = ∑ j, g (p.succAbove j) := by
  rw [Fin.sum_univ_succAbove g p, hg, zero_add]

/-! ### The extended path -/

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Inserting a zero-weight force coordinate into an integrated path.** -/
theorem isSLEPathUpTo_insertNth (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (p : Fin (nR + 1))
    {y : ℝ} {v : ℝ≥0 → ℝ} (hv : ForceCoord w ζ y v)
    (hbelow : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j : Fin nR, j.castSucc < p → vR j t ≤ v t)
    (habove : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ j : Fin nR, p ≤ j.castSucc → v t ≤ vR j t) :
    Sec2.IsSLEPathUpTo a xL (Fin.insertNth p y xR) ρL (Fin.insertNth p 0 ρR) w vL (Fin.insertNth p v vR) b ζ := by
  have hU := hp.isSLEPathUpTo le_rfl
  refine
    { w_zero := hU.w_zero
      vL_zero := hU.vL_zero
      vR_zero := fun i => ?_
      continuousOn_w := hU.continuousOn_w
      continuousOn_vL := hU.continuousOn_vL
      continuousOn_vR := fun i => ?_
      antitone_vL := hU.antitone_vL
      vL_le_w := hU.vL_le_w
      w_le_vR := fun {t} ht i => ?_
      monotone_vR := fun {t} ht => ?_
      integrable_gapL := hU.integrable_gapL
      integrable_gapR := fun {t} ht i => ?_
      w_eq := fun {t} ht => ?_
      vL_eq := hU.vL_eq
      vR_eq := fun {t} ht i => ?_
      volume_collisionL := hU.volume_collisionL
      volume_collisionR := fun i => ?_
      not_threshold := fun {t} ht => ?_ }
  · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hv.zero
    · simp only [Fin.insertNth_apply_succAbove]; exact hU.vR_zero j
  · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hv.cont
    · simp only [Fin.insertNth_apply_succAbove]; exact hU.continuousOn_vR j
  · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hv.le ht
    · simp only [Fin.insertNth_apply_succAbove]; exact hU.w_le_vR ht j
  · have e : (fun i => Fin.insertNth (α := fun _ => ℝ≥0 → ℝ) p v vR i t) = Fin.insertNth p (v t) (fun j => vR j t) := by
      funext i
      rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩ <;> simp
    rw [e]
    exact monotone_insertNth (hU.monotone_vR ht) p (hbelow t ht) (habove t ht)
  · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]
      refine ((hv.int ht).const_mul (-(1 / 2))).congr fun s _ => ?_
      simp only [two_div_sub_eq]
      ring
    · simp only [Fin.insertNth_apply_succAbove]; exact hU.integrable_gapR ht j
  · rw [hU.w_eq ht]
    congr 1
    rw [sum_insertNth_of_eq_zero p _ (by simp)]
    simp only [Fin.insertNth_apply_succAbove]
  · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hv.eq ht
    · simp only [Fin.insertNth_apply_succAbove]; exact hU.vR_eq ht j
  · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hv.null
    · simp only [Fin.insertNth_apply_succAbove]; exact hU.volume_collisionR j
  · have hsum : (∑ i ∈ Finset.univ.filter (fun i => Fin.insertNth (α := fun _ => ℝ≥0 → ℝ) p v vR i t = w t),
        Fin.insertNth (α := fun _ => ℝ) p 0 ρR i) =
        ∑ j ∈ Finset.univ.filter (fun j => vR j t = w t), ρR j := by
      rw [Finset.sum_filter, Finset.sum_filter, sum_insertNth_of_eq_zero p _ (by simp)]
      simp only [Fin.insertNth_apply_succAbove]
    have h := hU.not_threshold ht
    unfold ForceWord.ThresholdCondition at h ⊢
    rw [hsum]
    exact h

/-! ### The extended evolution -/

section Evolution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **The passive mark along one path** is a force coordinate from `y`, above `V^k` and below every right mark
from `x_j ≥ y`. -/
theorem forceCoord_passMark {y : ℝ} (hy : 0 < y) {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
      (fun t => B t ω) (ζ ω)) (hord : IsOrderedForceWord xL xR) {k : Fin nR} (hk : xR k < y) :
    ForceCoord (fun t => W t ω) (ζ ω) y (fun t => passMark y ζ W (VR k) t ω) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → VR k t ω ≤ passMark y ζ W (VR k) t ω) ∧
      ∀ j : Fin nR, y ≤ xR j → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → passMark y ζ W (VR k) t ω ≤ VR j t ω := by
  have hF := hp.isForcePath
  have hH := passHyp_of_continuousOn (ζ := ζ) hy hF.w_zero hF.continuousOn_w
  obtain ⟨hc, hb, ha⟩ := hH.forceCoord_passMarkPath (forceCoord_of_isForcePath hF k) hk.le
  have heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → passMark y ζ W (VR k) t ω =
      passMarkPath (fun s => W s ω) (ζ ω) (fun n t => passCut y ζ W n t ω) (fun s => VR k s ω) t :=
    fun t ht => passMark_eq_path hy hF.w_zero hF.continuousOn_w ht
  refine ⟨hc.congr (passMark_zero ω) heq, fun t ht => by rw [heq t ht]; exact hb t ht,
    fun j hj t ht => ?_⟩
  have hkj : k ≤ j := by
    by_contra hjk; rw [not_le] at hjk; linarith [hord.2.2.1 hjk.le]
  rw [heq t ht]
  exact ha (forceCoord_of_isForcePath hF j) hj (fun s hs => hF.monotone_vR hs hkj) t ht

/-- **The extended evolution with a passive mark.** For a point `y > 0` with `x_k` the last right mark below `y`
(`y` may or may not be a mark), inserting the passive mark `passMark y ζ W V^k` with weight `0` right after `x_k`
gives an integrated `SLE_κ(ρ)` evolution of the extended word, with the same driver, Brownian motion and lifetime. -/
theorem isIntegratedSLEEvolution_insertPassive (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hord : IsOrderedForceWord xL xR) {y : ℝ} (hy : 0 < y) {k : Fin nR} (hk : xR k < y)
    (hky : ∀ j, xR j < y → j ≤ k) :
    IsIntegratedSLEEvolution κ xL (Fin.insertNth k.succ y xR) ρL (Fin.insertNth k.succ 0 ρR) P 𝓕 W VL
      (Fin.insertNth (α := fun _ => ℝ≥0 → Ω → ℝ) k.succ (passMark y ζ W (VR k)) VR) B ζ := by
  set p : Fin (nR + 1) := k.succ with hpdef
  have hL : ∀ i, i ∉ Set.range (RelEmbedding.refl (α := Fin nL) (· ≤ ·)) → ρL i = 0 :=
    fun i hi => absurd ⟨i, rfl⟩ hi
  have hR : ∀ i, i ∉ Set.range (Fin.succAboveOrderEmb p) → Fin.insertNth (α := fun _ => ℝ) p 0 ρR i = 0 := by
    intro i hi
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp
    · exact absurd ⟨j, rfl⟩ hi
  refine (isIntegratedSLEEvolution_iff_compEmb (RelEmbedding.refl _) (Fin.succAboveOrderEmb p) hL hR).2
    ⟨?_, hE.2.2.1, fun i => ?_, ?_⟩
  · simp only [RelEmbedding.refl_apply, Fin.succAboveOrderEmb_apply, Fin.insertNth_apply_succAbove]
    exact hE
  · rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact adaptedBefore_passMark hE.2.1 (hE.2.2.2.1 k)
    · simp only [Fin.insertNth_apply_succAbove]; exact hE.2.2.2.1 j
  · filter_upwards [hE.2.2.2.2] with ω hp
    have e : (fun i t => Fin.insertNth (α := fun _ => ℝ≥0 → Ω → ℝ) p (passMark y ζ W (VR k)) VR i t ω) =
        Fin.insertNth (α := fun _ => ℝ≥0 → ℝ) p (fun t => passMark y ζ W (VR k) t ω) (fun j t => VR j t ω) := by
      funext i t
      rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩ <;> simp
    rw [e]
    obtain ⟨hc, hb, ha⟩ := forceCoord_passMark hy hp hord hk
    refine isSLEPathUpTo_insertNth hp p hc (fun t ht j hj => ?_) (fun t ht j hj => ?_)
    · have hjk : j ≤ k := by
        rw [hpdef, Fin.castSucc_lt_succ_iff] at hj; exact hj
      exact (hp.isForcePath.monotone_vR ht hjk).trans (hb t ht)
    · have hkj : k < j := by
        rw [hpdef] at hj
        by_contra hjk; rw [not_lt] at hjk
        exact absurd hj (not_le.2 (Fin.castSucc_lt_succ_iff.2 hjk))
      have hyj : y ≤ xR j := by
        by_contra hlt; rw [not_le] at hlt
        exact absurd (hky j hlt) (not_le.2 hkj)
      exact ha j hyj t ht

/-- **Lemma G12 at a passive right point.** For an integrated `SLE_κ(ρ)` evolution of an ordered force word
(`κ > 0`) and a generating trace `η`, a point `y > 0` that is not a right mark, with some right mark below it and
cumulative weight `S = Σ_{x_k < y} ρ_k > −2` (and `S > κ/2 − 4`): almost surely `η` does not visit `y` on `[0, ζ]`. -/
theorem ae_trace_ne_right_of_passive [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : 0 < y)
    (hny : ∀ j, xR j ≠ y) (hex : ∃ j, xR j < y)
    (hS' : -2 < ∑ k ∈ Finset.univ.filter (fun k => xR k < y), ρR k)
    (hS : κ / 2 - 4 < ∑ k ∈ Finset.univ.filter (fun k => xR k < y), ρR k) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  obtain ⟨j₁, hj₁⟩ := hex
  have hne : (Finset.univ.filter (fun j => xR j < y)).Nonempty := ⟨j₁, Finset.mem_filter.2 ⟨mem_univ _, hj₁⟩⟩
  set k := (Finset.univ.filter (fun j => xR j < y)).max' hne with hkdef
  have hk : xR k < y := (Finset.mem_filter.1 (Finset.max'_mem _ hne)).2
  have hky : ∀ j, xR j < y → j ≤ k := fun j hj =>
    Finset.le_max' _ j (Finset.mem_filter.2 ⟨mem_univ _, hj⟩)
  set p : Fin (nR + 1) := k.succ with hpdef
  have hE' := isIntegratedSLEEvolution_insertPassive hE hord hy hk hky
  have hb : ∀ j : Fin nR, j.castSucc < p → xR j ≤ y := fun j hj => by
    rw [hpdef, Fin.castSucc_lt_succ_iff] at hj
    exact (hord.2.2.1 hj).trans hk.le
  have ha : ∀ j : Fin nR, p ≤ j.castSucc → y ≤ xR j := fun j hj => by
    have hkj : k < j := by
      rw [hpdef] at hj
      by_contra hjk; rw [not_lt] at hjk
      exact absurd hj (not_le.2 (Fin.castSucc_lt_succ_iff.2 hjk))
    by_contra hlt; rw [not_le] at hlt
    exact absurd (hky j hlt) (not_le.2 hkj)
  have hmono := monotone_insertNth hord.2.2.1 p hb ha
  have hord' : IsOrderedForceWord xL (Fin.insertNth (α := fun _ => ℝ) p y xR) := by
    refine ⟨hord.1, hord.2.1, hmono, fun i => ?_⟩
    rcases Fin.eq_self_or_eq_succAbove p i with rfl | ⟨j, rfl⟩
    · simp only [Fin.insertNth_apply_same]; exact hy.le
    · simp only [Fin.insertNth_apply_succAbove]; exact hord.2.2.2 j
  have hyp : Fin.insertNth (α := fun _ => ℝ) p y xR p = y := Fin.insertNth_apply_same _ _ _
  have hx : Fin.insertNth (α := fun _ => ℝ) p y xR 0 < Fin.insertNth (α := fun _ => ℝ) p y xR p := by
    rw [hyp]
    refine lt_of_le_of_lt (hmono (Fin.zero_le (p.succAbove k))) ?_
    rw [Fin.insertNth_apply_succAbove]; exact hk
  have hsum : ∀ (q : ℝ → Prop) [DecidablePred q], ¬ q y →
      ∑ i ∈ Finset.univ.filter (fun i => q (Fin.insertNth (α := fun _ => ℝ) p y xR i)),
          Fin.insertNth (α := fun _ => ℝ) p 0 ρR i =
        ∑ j ∈ Finset.univ.filter (fun j => q (xR j)), ρR j := by
    intro q _ hq
    rw [Finset.sum_filter, Finset.sum_filter, sum_insertNth_of_eq_zero p _ (by simp)]
    simp only [Fin.insertNth_apply_succAbove]
  have h1 := hsum (fun x => x < y) (lt_irrefl y)
  have h2 : ∑ j ∈ Finset.univ.filter (fun j => xR j ≤ y), ρR j =
      ∑ j ∈ Finset.univ.filter (fun j => xR j < y), ρR j :=
    Finset.sum_congr (Finset.filter_congr fun j _ => ⟨fun h => lt_of_le_of_ne h (hny j), le_of_lt⟩) fun _ _ => rfl
  have h3 : ∑ i ∈ Finset.univ.filter (fun i => Fin.insertNth (α := fun _ => ℝ) p y xR i ≤ y),
      Fin.insertNth (α := fun _ => ℝ) p 0 ρR i =
      ∑ j ∈ Finset.univ.filter (fun j => xR j ≤ y), ρR j := by
    rw [Finset.sum_filter, Finset.sum_filter, sum_insertNth_of_eq_zero p _ (by simp)]
    simp only [Fin.insertNth_apply_succAbove]
  have h := ae_trace_ne_right_of_near (i₀ := 0) (j₀ := p) hκ hord' hE' hη (fun k => Fin.zero_le k) hx
    (by rw [hyp, h1]; exact hS') (by rw [hyp, h3, h2]; exact hS)
  rw [hyp] at h
  exact h

/-- **Lemma G12 at a passive left point**, the reflection of `ae_trace_ne_right_of_passive`: a point `y < 0` that is
not a left mark, with some left mark above it and `S = Σ_{y < x_{k,L}} ρ_{k,L} > −2` (and `> κ/2 − 4`), is almost
surely never visited. -/
theorem ae_trace_ne_left_of_passive [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : y < 0)
    (hny : ∀ j, xL j ≠ y) (hex : ∃ j, y < xL j)
    (hS' : -2 < ∑ k ∈ Finset.univ.filter (fun k => y < xL k), ρL k)
    (hS : κ / 2 - 4 < ∑ k ∈ Finset.univ.filter (fun k => y < xL k), ρL k) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  have hE' := hE.reflect
  have hη' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => (-W) t ω) (ζ ω) (fun t => LP.reflectC (η ω t)) := by
    filter_upwards [hη] with ω h
    exact LP.isGeneratingTrace_reflect h
  obtain ⟨j₁, hj₁⟩ := hex
  have hfilt : Finset.univ.filter (fun k => (-xL) k < -y) = Finset.univ.filter (fun k => y < xL k) :=
    Finset.filter_congr fun k _ => by simp
  have h := ae_trace_ne_right_of_passive (y := -y) hκ (isOrderedForceWord_reflect hord) hE' hη' (by linarith)
    (fun j hj => hny j (by simpa using hj)) ⟨j₁, by simpa using hj₁⟩ (by rw [hfilt]; exact hS')
    (by rw [hfilt]; exact hS)
  filter_upwards [h] with ω hω t ht heq
  apply hω t ht
  rw [heq]
  simp [LP.reflectC]

end Evolution

end G12

end Supp7

end InteractingSLE
