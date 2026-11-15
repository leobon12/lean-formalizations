/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LuLift
import InteractingSLE.Spec.Supplement.SB4RTrWalk2

/-!
# SB2(2)'s physical sets: the relative walk is the range of the lift curve

Packet PROVE-SB2-LIFTSET (target 2, assembly). The lockstep induction with history (`SB2LuAcc`) from the starting
stage (`SB2LuStart`), read through the lift image (`SB2LuLift`), gives the conclusion of
`SB2LowerRelWalkRangeStatement` at one sample: the relative walk's physical set is `range γ` for the lift curve `γ`
of the actual tail.

* `start_arc_phys`, `start_piece_phys`: the physical parts of the two runs at the starting stage (on a connector:
  `{0}` with the `ι`-image of the connector right of `R`; on a piece: `{0}` with the relative first piece);
* **`range_eq_physSet_of_accCorr`**: from the correspondence with history at the end of the run (pieces paired by
  the lift relation), the actual walk done there, and the start parts corresponding;
* **`range_eq_physSet_start_arc`**, **`range_eq_physSet_start_piece`**: end to end, from the starting-stage data,
  the per-step data (`StepOK`, and at every launch the lift relation of the two new pieces) and the lift curve.

The remaining hypotheses on the actual walk and the lift curve are deterministic: `β₀` is injective with range the
actual physical set and visits `R` at `t_L`; its head `β₀ '' [0, t_L]` has real points `≤ R`
(`head_real_le_of_s2`: Lemma S2's `β₀ '' [0, t_R] ⊆ K_A`, `head_real_le_of_subset_hullK`) and contains the actual
prefix before the start (`hP₀`, the order of the actual stages along `β₀`; `subset_head_of_split` reduces it to the
later part being preconnected, unbounded and meeting the prefix only at its seed); its tail has real points `≥ R`
(`htail`); the lift curve reads the untouched ray through `ι` (`lift_eq_of_rayChartInj`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ}

/-! ### The starting states -/

/-- **The connector of a rightward move contains `R`** when the move starts at `pt ≤ R` and every restart mark lies
beyond `R`. -/
theorem exists_arc_mem_of_move {b : ℝ → ℝ} {J : Finset ℝ} {s t : ExplState} {R : ℝ}
    (ht : t = if hC : (restartSet κ b J s).Nonempty then
      ExplState.moveAlong s true ((restartSet κ b J s).min' hC) true else ExplState.moveToEnd s true)
    (hpt : stPt s ≤ R) (hgap : ∀ x ∈ restartSet κ b J s, R < x) :
    ∃ a : Set ℝ, R ∈ a ∧ t.2.1 = s.2.1 ++ [a] := by
  split_ifs at ht with hC
  · exact ⟨Icc (stPt s) ((restartSet κ b J s).min' hC), ⟨hpt, (hgap _ (Finset.min'_mem _ hC)).le⟩,
      by rw [ht, moveAlong_arcs_true]⟩
  · exact ⟨_, mem_Ici.2 hpt, by rw [ht, moveToEnd_arcs_true]⟩

/-- **A zero-lifetime piece launched from the root `0`** has the physical point `0` only. -/
theorem tipSet_newPc_init_zero {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver d) (h0 : d.2 = 0) :
    (newPc (ExplState.init 0) d).1.tipSet (newPc (ExplState.init 0) d).2.1 (newPc (ExplState.init 0) d).2.2 =
      {0} := by
  have hW : (fun r : ℝ≥0 => d.1 (min (r : ℝ≥0∞) (min ⊤ d.2)).toNNReal) = fun _ => 0 := by
    funext r
    rw [h0, min_eq_right le_top, min_eq_right zero_le, ENNReal.toNNReal_zero]
    exact hreg.2.1
  have e : newPc (ExplState.init 0) d = (Chart.id.recenter 0, fun _ => 0, 0) := by
    unfold newPc
    rw [hW, h0, min_eq_right le_top]
    rfl
  rw [e]
  simpa using Lf.tipSet_zero_piece 0

/-- The physical part of the initial state at the root `0`. -/
theorem statePhysicalSet_init : statePhysicalSet 0 (ExplState.init 0) = {0} := by
  simp [statePhysicalSet, ExplState.init]


variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ}

/-- **The starting stage on an actual connector, with the physical parts**: `stCorr_start_arc`, the connector `a`
contains `R`, the actual physical part grows by `a`, and the relative one is `{0}` with `ι '' (a ∩ Ici R)`. -/
theorem start_arc_phys (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hn : n < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hodd : n % 2 = 1)
    (hmove : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) none true =
      if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)).Nonempty then
        ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) true
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) true)
    (hθ : stAngle (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) = θ)
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ≤ R)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n), R < x)
    (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ)
    (hreg : IsRegularDriver (D₂ 0)) (h0 : (D₂ 0).2 = 0) :
    ∃ a : Set ℝ, R ∈ a ∧
      StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) ∧
      statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)) =
        statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ∪ ((↑) : ℝ → ℂ) '' a ∧
      statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) =
        {0} ∪ ((↑) : ℝ → ℂ) '' (ι '' (a ∩ Ici R)) := by
  obtain ⟨hc, a, ha₁, ha₂⟩ := stCorr_start_arc h hn hodd hmove hθ hpt hrec hgap hlow hreg h0
  obtain ⟨a', hRa', ha'⟩ := exists_arc_mem_of_move hmove hpt hgap
  have hrun₁ : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) =
      ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) none true :=
    run_succ_walk_cont hn hodd
  have haa : a = a' := by
    rw [hrun₁] at ha₁
    have := ha₁.symm.trans ha'
    simpa using this
  subst haa
  refine ⟨a, hRa', hc, ?_, ?_⟩
  · rw [statePhysicalSet_append (t := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (Y := [])
      (by rw [hrun₁, contStep_pieces, List.append_nil]) ha₁]
    simp
  · have hp₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2).1 =
        (ExplState.init 0).1 ++ [newPc (ExplState.init 0) (D₂ 0)] := by
      rw [run_succ_walk_cont (by have := one_lt_length_boundaryWalkSpec b₂ J₂ θ true; omega) (by norm_num),
        contStep_pieces, run_one_walk, launch_pieces]
      rfl
    have ha₂' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2).2.1 =
        (ExplState.init 0).2.1 ++ [ι '' (a ∩ Ici R)] := by
      rw [ha₂]
      rfl
    rw [statePhysicalSet_append hp₂ ha₂', statePhysicalSet_init]
    simp only [List.mem_singleton, iUnion_iUnion_eq_left, tipSet_newPc_init_zero hreg h0, union_self]

/-- **The starting stage on an actual piece, the physical parts**: after the two launches the actual physical part
grows by the actual piece, and the relative one is `{0}` with the relative first piece. -/
theorem start_piece_phys {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ}
    (hlaunch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1) =
      ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) n (D₁ n) θ ⊤) :
    statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n + 1)) =
        statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) ∪
          (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n)).1.tipSet
            (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n)).2.1
            (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n)).2.2 ∧
      statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) =
        {0} ∪ (newPc (ExplState.init 0) (D₂ 0)).1.tipSet (newPc (ExplState.init 0) (D₂ 0)).2.1
          (newPc (ExplState.init 0) (D₂ 0)).2.2 := by
  constructor
  · rw [statePhysicalSet_append (t := ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n)
      (Y := [newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n) (D₁ n)]) (Z := [])
      (by rw [hlaunch, launch_pieces]; rfl) (by rw [hlaunch, launch_arcs, List.append_nil])]
    simp
  · rw [statePhysicalSet_append (t := ExplState.init 0) (Y := [newPc (ExplState.init 0) (D₂ 0)]) (Z := [])
      (by rw [run_one_walk, launch_pieces]; rfl)
      (by rw [run_one_walk, launch_arcs]; rfl), statePhysicalSet_init]
    simp


/-! ### The range identity after the lockstep run -/

variable {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **The head of `β₀` has real points `≤ realMax A`** when it lies in `K_A` (Lemma S2: `β₀ '' [0, t_R] ⊆ K_A`). -/
theorem head_real_le_of_subset_hullK {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} {A : Set ℂ} (hK : β₀ '' Icc 0 tL ⊆ hullK A) :
    ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ realMax A := by
  intro t ht x hx
  have hmem : (x : ℂ) ∈ hullK A := hx ▸ hK ⟨t, ⟨zero_le, ht⟩, rfl⟩
  rcases hmem with hf | ⟨y, hy, hyx⟩
  · have : (0 : ℝ) < (x : ℂ).im := hf.1
    simp at this
  · rw [← Complex.ofReal_injective hyx]
    exact hy.2


/-- **The head hypothesis from Lemma S2 reflected** (`s2HullRight`): if `A = p '' [0, 1]` lies on the closed left of
the proper curve `β₀` from `0`, which visits `realMax A` at `t_L`, the head `β₀ '' [0, t_L]` has real points
`≤ realMax A`. -/
theorem head_real_le_of_s2 {p : ℝ → ℂ} {β₀ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ : Supp9B.IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedLeftSide β₀) (hβL : β₀ tL = realMax (p '' Icc 0 1)) :
    ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ realMax (p '' Icc 0 1) := by
  obtain ⟨-, tR, htR, -, hK, -⟩ := s2HullRight hp hp0 hpH hβ hβ0 hA
  have e : tR = tL := hβ.2.1 (htR.trans hβL.symm)
  subst e
  exact head_real_le_of_subset_hullK hK

/-- **The prefix before a split lies on the head** (deterministic topology, for `hP₀`): if the physical set of a proper
curve `β₀` contains a preconnected unbounded part `T` through `β₀ t_y`, and `P` meets `T` at most in `β₀ t_y`, then `P`
lies on `β₀ '' [0, t_y]`. -/
theorem subset_head_of_split {β₀ : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β₀) {P T : Set ℂ} {ty : ℝ≥0}
    (hP : P ⊆ range β₀) (hT : T ⊆ range β₀) (hTc : IsPreconnected T) (hTu : ¬ Bornology.IsBounded T)
    (hy : β₀ ty ∈ T) (hPT : P ∩ T ⊆ {β₀ ty}) : P ⊆ β₀ '' Iic ty := by
  have he := isClosedEmbedding_of_isProperCurve hβ
  have hI : IsPreconnected (β₀ ⁻¹' T) := by
    rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hT]
    exact hTc
  have hunb : ∀ M : ℝ≥0, ∃ t ∈ β₀ ⁻¹' T, M ≤ t := by
    intro M
    by_contra hcon
    push Not at hcon
    apply hTu
    have hsub : T ⊆ β₀ '' Iic M := by
      intro z hz
      obtain ⟨t, rfl⟩ := hT hz
      exact ⟨t, (hcon t hz).le, rfl⟩
    have hc : IsCompact (Iic M) := by rw [← Icc_bot]; exact isCompact_Icc
    exact ((hc.image hβ.1).isBounded).subset hsub
  rintro z hz
  obtain ⟨t, rfl⟩ := hP hz
  refine ⟨t, ?_, rfl⟩
  by_contra hlt
  have hlt : ty < t := lt_of_not_ge hlt
  obtain ⟨t', ht', htt'⟩ := hunb t
  have htI : t ∈ β₀ ⁻¹' T := hI.Icc_subset hy ht' ⟨hlt.le, htt'⟩
  have heq : β₀ t = β₀ ty := hPT ⟨hz, htI⟩
  exact hlt.ne' (hβ.2.1 heq)

/-- **The relative physical set is the range of the lift curve** (deterministic): the correspondence with history
holds at actual stage `N + o` and relative stage `N`, with pieces paired by the lift relation, the actual walk is
done there, `β₀` is an injective parametrization of the actual walk visiting `R` at `t_L`, and the start parts
correspond (`hQ`, given that the actual start part lies on `β₀`). -/
theorem range_eq_physSet_of_accCorr (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {N o : ℕ}
    {t₁ t₂ : ExplState} (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hc : AccCorr ι R (LiftRel β₀ tL γ) t₁ t₂ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ N))
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hQ : statePhysicalSet 0 t₁ ⊆ range β₀ → liftImage β₀ tL γ (statePhysicalSet 0 t₁) = statePhysicalSet 0 t₂) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  obtain ⟨X, Y₁, Y₂, hY, hP₁, hP₂⟩ := physSet_eq_of_accCorr hN₁ hN₂ hc hd
  have hsub : ∀ a ∈ X, ((↑) : ℝ → ℂ) '' a ⊆ range β₀ := fun a ha => by
    rw [hβr, hP₁]
    exact subset_union_of_subset_right (subset_biUnion_of_mem (u := fun a => ((↑) : ℝ → ℂ) '' a) ha) _
  have hQ' := hQ (by rw [hβr, hP₁]; exact subset_union_left.trans subset_union_left)
  refine range_eq_of_decomp hβr hP₁ hP₂ hY hQ' fun a ha => ?_
  exact liftImage_ofReal hβ hβL hγ0 h.map_base hhead htail hray fun x hx _ => hsub a ha ⟨x, hx, rfl⟩

/-- **SB2(2)'s physical sets, starting on an actual connector** (deterministic, one sample). The actual walk moves
right at its connector instruction `o + 1` (`o` even) from `pt ≤ R` across `R` (no restart mark in `(pt, R]`, low
outward height at `R`); the relative first piece has zero lifetime. From relative stage `2` (actual stage `o + 2`)
to `N` the lockstep data hold (`StepOK`, and at each launch the relative piece is the lift of the actual one), and
the actual walk is done at `N + o`. If `β₀` is an injective parametrization of the actual walk visiting `R` at
`t_L`, whose head has real points `≤ R` and tail real points `≥ R`, the actual prefix before the connector lies on
the head, and the lift curve `γ` reads the untouched ray through `ι`, then the relative walk's physical set is
`range γ`. -/
theorem range_eq_physSet_start_arc (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}
    (ho : o % 2 = 0) (hn : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hmove : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) none
        true =
      if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true
          ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true)
    (hθ : stAngle (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) = θ)
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R)
    (hgap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)), R < x)
    (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ) (hreg : IsRegularDriver (D₂ 0)) (h0 : (D₂ 0).2 = 0)
    (h2N : 2 ≤ N) (hlen : ∀ i, 2 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hstep : ∀ i, 2 ≤ i → i < N →
      StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι R (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ⊆
      β₀ '' Iic tL) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  obtain ⟨a, hRa, hc, hS₁, hS₂⟩ := start_arc_phys h hn (by omega) hmove hθ hpt hrec hgap hlow hreg h0
  have e : 2 + o = o + 1 + 1 := by omega
  have h₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 2) := by rw [e]; exact hc
  have hacc := accCorr_run_of_steps (L := LiftRel β₀ tL γ) h le_rfl o 2 N ho hlen h₀ hstep N h2N le_rfl
  refine range_eq_physSet_of_accCorr h hN₁ hN₂ hacc hd hβr hβ hβL hγ0 hhead htail hray fun hsub => ?_
  rw [e] at hsub ⊢
  rw [hS₁, hS₂]
  rw [hS₁] at hsub
  exact liftImage_start_arc hβ hβL hγ0 h.map_base hhead htail hray hP₀ hRa
    fun x hx _ => hsub (Or.inr ⟨x, hx, rfl⟩)


/-- **SB2(2)'s physical sets, starting on an actual piece** (deterministic, one sample). The actual flow instruction
`o` (even) launches the piece through `R` from a state with point and record `≤ R`; the relative walk launches its
first piece from the root, with the launch observables of `StepOK` and the lift relation (the relative first piece
is the lift of the actual one), and `R` is a physical point of the actual piece. From relative stage `1` (actual
stage `o + 1`) to `N` the lockstep data hold and the actual walk is done at `N + o`. With `β₀`, `γ` as in
`range_eq_physSet_start_arc` (the actual prefix before the piece on the head), the relative walk's physical set is
`range γ`. -/
theorem range_eq_physSet_start_piece (h : RayCorr b₁ J₁ b₂ J₂ R ι) {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}
    (ho : o % 2 = 0)
    (hlaunch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) =
      ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) o (D₁ o) θ ⊤)
    (htip : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≠ .inr (.inl ()))
    (hpt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hrec : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R)
    (hT : (D₂ 0).2 = ⊤ ↔ (D₁ o).2 = ⊤) (h0 : (D₂ 0).2 = 0 ↔ (D₁ o).2 = 0)
    (hR : (∃ x : ℝ, 0 < x ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ↔
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x)
    (hL₁ : ¬ ∃ x : ℝ, x < stRecL (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ∧
      lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x)
    (hL₂ : ¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x)
    (hrec' : (D₁ o).2 ≠ ⊤ → lRecR (ExplState.init 0) ⊤ (D₂ 0) =
      ι (max (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊤ (D₁ o)) R))
    (hlift₀ : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o))
      (newPc (ExplState.init 0) (D₂ 0)))
    (hRmem : (R : ℂ) ∈ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).1.tipSet
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.1
      (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.2)
    (h1N : 1 ≤ N) (hlen : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hstep : ∀ i, 1 ≤ i → i < N →
      StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι R (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
          (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (hN₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hβ : Function.Injective β₀) (hβL : β₀ tL = R) (hγ0 : γ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x)
    (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hP₀ : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  have hc := stCorr_start_piece (b₂ := b₂) (J₂ := J₂) (D₂ := D₂) h hlaunch htip hpt hrec hT h0 hR hL₁ hL₂ hrec'
  obtain ⟨hS₁, hS₂⟩ := start_piece_phys (b₂ := b₂) (J₂ := J₂) (D₂ := D₂) hlaunch
  have e : 1 + o = o + 1 := by omega
  have h₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (1 + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ 1) := by rw [e]; exact hc
  have hacc := accCorr_run_of_steps (L := LiftRel β₀ tL γ) h le_rfl o 1 N ho hlen h₀ hstep N h1N le_rfl
  refine range_eq_physSet_of_accCorr h hN₁ hN₂ hacc hd hβr hβ hβL hγ0 hhead htail hray fun _ => ?_
  rw [e, hS₁, hS₂]
  exact liftImage_start_piece hβ hγ0 hP₀ hlift₀ (by rw [hβL]; exact Or.inr hRmem)

end InteractingSLE.Theorem14.SB.Lk
