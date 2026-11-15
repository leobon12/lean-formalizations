/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInClockPath
import InteractingSLE.Spec.Supplement.BR6Proof

/-!
# BR4a's infinite relative capacity (`BR4aClockStatement`) from Theorem 1.3

Packet PROVE-T14-BR4A3. Supplement p. 609–610, Corollary BR4 ("The transformed actual prefix before the first hit of
`z` has the complete canonical driving law of this admissible word in its own filtration […] If its relative capacity
had a finite limit, the admissible integrated law and nonexplosion would bound the relative driver and hulls through
that limit. But continuity of the original prefix at its hit of `z` makes its image under `ψ` approach infinity. This
contradiction gives infinite relative capacity") and Corollary BR4a ("makes the relative lifetime infinite as in BR4:
a finite lifetime would bound all driver coordinates and, by the Loewner rectangle bound, the hull, contradicting the
transformed trace's limit at infinity").

The route is that of BR6's sufficiency proof (`BR6Proof`, `BR6ProofSeed`):
1. insert the visited point `z > 0` as a passive right mark and amalgamate coincident marks
   (`Supp7.G12.isIntegratedSLEEvolution_insertPassive`, `IsIntegratedSLEEvolution.amalgamate`);
2. LP9's retargeted local process at `z` (`Zhan.Retarget.exists_retarget_evolution_of_seed_stop`) agrees before its
   horizon with a full integrated evolution `G` of the transformed word on the same space
   (`Sec7.SeedStop.exists_isIntegratedSLEEvolution_of_stop`), whose lifetime is at least that horizon;
3. Theorem 1.3 gives `G` a generating trace through its lifetime, so the deterministic core
   (`BR4aIn.newHorizon_eq_top_of_code`) forces the new horizon of the first visit to be infinite.
No admissibility of the transformed word is needed: a trace through a finite threshold also closes the chain.
For `v > 0` the evolution is reflected (`IsIntegratedSLEEvolution.reflect`).

* `lt_of_pullData`, `le_sepTime_of_lt`, `not_thresholdCondition_seed`;
* `ae_newHorizon_eq_top_dist` (distinct word, retargeted index), `ae_newHorizon_eq_top_idx` (any target index
  `≥ 1`), **`ae_newHorizon_eq_top_ord`** (ordered word, any `z > 0` beyond a right mark);
* **`br4aClockStatement_of_theorem13`**: `Exist.Theorem13Statement.{u} → BR4aClockStatement.{u}` (R48: Theorem 1.3 is
  a permitted root of Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.BR4aIn

open Zhan Zhan.Retarget MartChar.RealFlow Sec7 Sec7.RandRestart Sec2 Sec2.Assembly Sec2.Assembly2 Sec7.Band
  BR3Ref BR4aChain

/-! ### Separation before the visit -/

/-- Before the end of Zhan's pull-back data the target is strictly right of the driver. -/
theorem lt_of_pullData {w vk : ℝ≥0 → ℝ} {xk : ℝ} {T₀ : ℝ≥0∞} (hd : PullData w vk xk T₀) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) < T₀) : w s < vk s := by
  have h := (hd.sep (s : ℝ) s.coe_nonneg (by simpa using hs)).pos s ⟨s.coe_nonneg, le_rfl⟩
  simp only [gap, Real.toNNReal_coe] at h
  linarith

/-- The separation time is at least every time before which the target stays right of the driver. -/
theorem le_sepTime_of_lt {w vk : ℝ≥0 → ℝ} {T₀ ζ : ℝ≥0∞} (hTζ : T₀ ≤ ζ)
    (h : ∀ s : ℝ≥0, (s : ℝ≥0∞) < T₀ → w s < vk s) : T₀ ≤ sepTime w vk ζ := by
  unfold sepTime
  refine le_min hTζ (le_iInf₂ fun s hs => ?_)
  by_contra hlt
  push Not at hlt
  exact absurd hs.2 (not_le.2 (h s hlt))

/-- An integrated evolution whose lifetime is infinite with positive probability has an admissible seed. -/
theorem not_thresholdCondition_seed {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  obtain ⟨ω, hζω, hp⟩ := (hζ.and hE.ae_isIntegratedSLEPath).exists
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -, -⟩ := hp
  have h := hnt 0 (by rw [hζω]; exact ENNReal.coe_lt_top)
  have eL : (fun i => VL i 0 ω) = xL := funext hvL0
  have eR : (fun i => VR i 0 ω) = xR := funext hvR0
  rwa [hw0, eL, eR] at h

/-! ### The new horizon of the first visit is infinite -/

section Dist

variable {κ : ℝ} {nL j m : ℕ}

/-- **Infinite new horizon, distinct word.** For a distinct word with target `x_k` (Lean index `j ≥ 1` of a right
list of length `j + 1 + m`) and an integrated evolution with infinite lifetime: almost surely, at every time `T₀` at
which a complete generating trace of the driver is at `x_k`, with `x_k` outside the earlier closed hulls, Zhan's new
horizon `sup_{S < T₀} C(S)` of the target change to `x_k` is infinite. -/
theorem ae_newHorizon_eq_top_dist (h13 : Exist.Theorem13Statement.{u}) (hκ : 0 < κ) {xL : Fin nL → ℝ}
    {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} (hD : LP.IsDistinctForceWord xL xR)
    (hj : 1 ≤ j) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ T₀ : ℝ≥0,
      (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧ γ T₀ = LP.retargetPos xR) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ →
        (LP.retargetPos xR : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal ω) t)) →
      newHorizon (LP.retargetPos xR) (fun t => W t ω)
        (fun t => rightImg (fun s : ℝ => W s.toNNReal ω) (LP.retargetPos xR) t) T₀ = ⊤ := by
  have hD' := LP.isDistinctForceWord_retarget hD hj
  have hF := hD'.1
  have hxk : 0 < LP.retargetPos xR := LP.retargetPos_pos hD.2.2 hD.1.2.2.2 hj
  have hseed := not_thresholdCondition_seed hE hζ
  -- the retargeted local evolution, its first positive announcing time, and the full evolution `G`
  obtain ⟨𝓘, β, τ, -, hτ, hloc, S, hSst, hSae⟩ := exists_retarget_evolution_of_seed_stop hκ hD hj hE hseed
  have hTst : IsStoppingTime (usualAugmentation 𝓘 (P.prod P))
      fun p : Ω × Ω => (firstPos (fun n (q : Ω × Ω) => S n q.1) p : WithTop ℝ≥0) :=
    fun t => Ito.le_usualAugmentation 𝓘 (P.prod P) t _ (isStoppingTime_firstPos hSst t)
  have hT0 : ∀ p : Ω × Ω, 0 < firstPos (fun n (q : Ω × Ω) => S n q.1) p := fun p => firstPos_pos _ p
  have hTτ : ∀ᵐ p ∂(P.prod P), (firstPos (fun n (q : Ω × Ω) => S n q.1) p : ℝ≥0∞) < τ p.1 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hSae] with p hp
    exact firstPos_lt (S := fun n (q : Ω × Ω) => S n q.1) (τ := fun q => τ q.1) hp.1 hp.2
  have hgood : ∀ᵐ p ∂(P.prod P), GoodWord (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR)
      (contWord (fun u p => newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u)
        (firstPos (fun n (q : Ω × Ω) => S n q.1)) p) := by
    filter_upwards [hloc.ae_path, hTτ] with p hp hpτ
    exact goodWord_of_isSLEPathUpTo hp hF (hT0 p) hpτ
  obtain ⟨𝓖, Wg, VLg, VRg, Bg, ζg, hG, hagG⟩ :=
    SeedStop.exists_isIntegratedSLEEvolution_of_stop hκ hloc hTst hT0 hTτ hgood
  have h13G := h13 hκ hF hG
  have hq := Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)
  refine Sec7.ae_of_ae_prod_fst (P := P) (Φ := fun ω => ∀ T₀ : ℝ≥0,
      (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧ γ T₀ = LP.retargetPos xR) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ →
        (LP.retargetPos xR : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal ω) t)) →
      newHorizon (LP.retargetPos xR) (fun t => W t ω)
        (fun t => rightImg (fun s : ℝ => W s.toNNReal ω) (LP.retargetPos xR) t) T₀ = ⊤) ?_
  filter_upwards [hagG, h13G, hq.ae hτ, hq.ae hE.ae_isIntegratedSLEPath, hq.ae hζ] with p hag h13p hτp hp hζp
  intro T₀ ⟨γ, hγ, hγT⟩ hsep
  set w : ℝ≥0 → ℝ := fun t => W t p.1 with hwdef
  set xk := LP.retargetPos xR with hxkdef
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p.1 := fun t => by rw [hζp]; exact ENNReal.coe_lt_top
  have hw : Continuous w := continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => hlt t)
  have hw0 : w 0 = 0 := hp.1
  -- the target process is the flow of `x_k`
  have hvk : (fun t => VR (LP.retargetIdx j m) t p.1) = fun t : ℝ≥0 => rightImg (fun s : ℝ => w s.toNNReal) xk t :=
    funext fun t => WangWu.vR_eq_rightImg hp hw (hlt t) _
  have hd : PullData w (fun t => rightImg (fun s : ℝ => w s.toNNReal) xk t) xk T₀ :=
    pullData_of_notMem hw hw0 hxk hsep
  -- the new horizon of the first visit is below the local horizon, hence below the lifetime of `G`
  have hTsep : (T₀ : ℝ≥0∞) ≤ sepTime w (fun t => VR (LP.retargetIdx j m) t p.1) (ζ p.1) := by
    rw [hvk]
    exact le_sepTime_of_lt (by rw [hζp]; exact le_top) fun s hs => lt_of_pullData hd hs
  have hNτ : newHorizon xk w (fun t => rightImg (fun s : ℝ => w s.toNNReal) xk t) T₀ ≤ τ p.1 := by
    rw [hτp, ← hvk]
    exact Sec5.TwoMark.Trace12.newHorizon_mono hTsep
  obtain ⟨-, ηg, hηg, -⟩ := h13p
  refine newHorizon_eq_top_of_code hw hw0 hxk hγ hγT hsep hηg (hNτ.trans hag.1) fun t ht => ?_
  have h := (hag.2 t (lt_of_lt_of_le ht hNτ)).1
  rw [← h]
  show newDrv xk w (fun t => VR (LP.retargetIdx j m) t p.1) t = _
  rw [hvk]

end Dist

/-- **Infinite new horizon, any target index** `J ≥ 1` of a distinct word. -/
theorem ae_newHorizon_eq_top_idx (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hD : LP.IsDistinctForceWord xL xR)
    (J : Fin nR) (hJ : 1 ≤ (J : ℕ)) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ T₀ : ℝ≥0,
      (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧ γ T₀ = xR J) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → (xR J : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal ω) t)) →
      newHorizon (xR J) (fun t => W t ω) (fun t => rightImg (fun s : ℝ => W s.toNNReal ω) (xR J) t) T₀ = ⊤ := by
  obtain ⟨j, hjJ⟩ : ∃ j : ℕ, (J : ℕ) = j := ⟨_, rfl⟩
  obtain ⟨m, rfl⟩ : ∃ m, nR = j + 1 + m := ⟨nR - (j + 1), by have := J.isLt; omega⟩
  have hJe : J = LP.retargetIdx j m := Fin.ext (by simp [LP.retargetIdx, hjJ])
  subst hJe
  exact ae_newHorizon_eq_top_dist h13 hκ hD (by omega) hE hζ

/-- **Infinite new horizon, ordered word.** For an ordered word with a right mark strictly before `z > 0` and an
integrated evolution with infinite lifetime: almost surely, at every time `T₀` at which a complete generating trace is
at `z`, with `z` outside the earlier closed hulls, Zhan's new horizon of the target change to `z` is infinite. (Insert
`z` as a passive right mark and amalgamate coincident marks, as in BR6's sufficiency proof.) -/
theorem ae_newHorizon_eq_top_ord (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : IsOrderedForceWord xL xR) (hzR : ∃ i, xR i < z) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, ∀ T₀ : ℝ≥0,
      (∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧ γ T₀ = z) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → (z : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal ω) t)) →
      newHorizon z (fun t => W t ω) (fun t => rightImg (fun s : ℝ => W s.toNNReal ω) z t) T₀ = ⊤ := by
  obtain ⟨hxLa, hxL0, hxRm, hxR0⟩ := hF
  -- the last right mark below `z`
  set A := univ.filter (fun i => xR i < z) with hA
  have hAne : A.Nonempty := by
    obtain ⟨i, hi⟩ := hzR
    exact ⟨i, by simp [hA, hi]⟩
  set kk := A.max' hAne with hkk
  have hkz : xR kk < z := (mem_filter.1 (A.max'_mem hAne)).2
  have hky : ∀ j, xR j < z → j ≤ kk := fun j hj => A.le_max' j (by simp [hA, hj])
  -- insert `z` as a passive right mark
  have hE1 := Supp7.G12.isIntegratedSLEEvolution_insertPassive hE ⟨hxLa, hxL0, hxRm, hxR0⟩ hz hkz hky
  set xR' := Fin.insertNth (α := fun _ => ℝ) kk.succ z xR with hxR'
  have hb : ∀ j : Fin nR, j.castSucc < kk.succ → xR j ≤ z := fun j hj =>
    (hxRm (Fin.castSucc_lt_succ_iff.1 hj)).trans hkz.le
  have ha : ∀ j : Fin nR, kk.succ ≤ j.castSucc → z ≤ xR j := fun j hj => by
    by_contra h
    rw [not_le] at h
    have h' := hky j h
    rw [Fin.le_def] at hj h'
    simp only [Fin.val_succ, Fin.val_castSucc] at hj
    omega
  have hxR'm : Monotone xR' := Supp7.G12.monotone_insertNth hxRm kk.succ hb ha
  have hxR'0 : ∀ i, 0 ≤ xR' i := by
    intro i
    rcases Fin.eq_self_or_eq_succAbove kk.succ i with rfl | ⟨j, rfl⟩
    · simp only [hxR', Fin.insertNth_apply_same]; exact hz.le
    · simp only [hxR', Fin.insertNth_apply_succAbove]; exact hxR0 j
  have hF' : IsOrderedForceWord xL xR' := ⟨hxLa, hxL0, hxR'm, hxR'0⟩
  -- amalgamate
  have hEa := hE1.amalgamate hF'
  have hDa := LP.isDistinctForceWord_amalgamate hF'
  set J := LP.amCls xR' kk.succ with hJ
  have hJpos : LP.amPos xR' J = z := by
    rw [hJ, LP.amPos_amCls]; simp only [hxR', Fin.insertNth_apply_same]
  have hval : ∀ j : Fin nR, xR' (kk.succ.succAbove j) = xR j := fun j => by
    simp only [hxR', Fin.insertNth_apply_succAbove]
  have hJ1 : 1 ≤ (J : ℕ) := by
    have hlt : LP.amCls xR' (kk.succ.succAbove kk) < J := by
      rw [hJ, amCls_lt_amCls_iff, hval]
      simpa [hxR'] using hkz
    rw [Fin.lt_def] at hlt
    omega
  have hmain := ae_newHorizon_eq_top_idx h13 hκ hDa J hJ1 hEa hζ
  rw [hJpos] at hmain
  exact hmain

/-! ### Corollary BR4a's clock -/

/-- **BR4a's relative capacity is infinite** (`BR4aClockStatement`, supplement p. 610), from Theorem 1.3. The
counterflow's integrated evolution (the flow-line word of `b'` at angle `0`, parameter `16/κ > 4`) has infinite
lifetime; for `v < 0` the pole `−1/v = |v|⁻¹` is right of the seed `0⁺`, for `v > 0` the reflected evolution has its
pole `|v|⁻¹` right of the reflected seed. `ae_newHorizon_eq_top_ord` makes the new horizon of the first visit infinite,
and `clock_unbounded_of_oriented` turns it into an unbounded clock `clock v` before the first visit. -/
theorem br4aClockStatement_of_theorem13 (h13 : Exist.Theorem13Statement.{u}) : BR4aClockStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hζ' v hv0 hvis b' J' h' hb' htr' 𝓕 VL VR B hC
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hF := Theorem15.isOrderedForceWord_flowLine b' J' 0
  have hE := hC.1
  have hgood : ∀ᵐ ω ∂P, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ := by
    filter_upwards [h13 hκ' hF hE, hE.ae_isIntegratedSLEPath, hζ'] with ω hω hp hζω
    obtain ⟨-, η, hη, -⟩ := hω
    rw [hζω] at hη
    have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ' ω := fun t => by rw [hζω]; exact ENNReal.coe_lt_top
    exact ⟨continuousOn_univ.1 (hp.isForcePath.continuousOn_w.mono fun t _ => hlt t), hp.1, η, hη⟩
  have hN : ∀ᵐ ω ∂P, ∀ T₀ : ℝ≥0,
      (∃ γo : ℝ≥0 → ℂ, IsGeneratingTrace (oDrv v fun t => W' t ω) ⊤ γo ∧ γo T₀ = scl v) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ →
        (scl v : ℂ) ∉ closure (fwdHull (fun s : ℝ => oDrv v (fun t => W' t ω) s.toNNReal) t)) →
      newHorizon (scl v) (oDrv v fun t => W' t ω) (tgt v fun t => W' t ω) T₀ = ⊤ := by
    rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · have h1 := ae_newHorizon_eq_top_ord h13 hκ' (scl_pos hv0) hF ⟨⟨0, Nat.succ_pos _⟩, ?_⟩ hE hζ'
      · filter_upwards [h1] with ω hω T₀ hγ hsep
        unfold tgt
        rw [oDrv_of_neg hneg] at hγ hsep ⊢
        exact hω T₀ hγ hsep
      · show (0 : ℝ) < scl v
        exact scl_pos hv0
    · have h1 := ae_newHorizon_eq_top_ord h13 hκ' (scl_pos hv0) (Supp7.G12.isOrderedForceWord_reflect hF)
        ⟨⟨0, Nat.succ_pos _⟩, ?_⟩ (IsIntegratedSLEEvolution.reflect hE) hζ'
      · filter_upwards [h1] with ω hω T₀ hγ hsep
        have e : oDrv v (fun t => W' t ω) = fun t => (-W') t ω := by rw [oDrv_of_pos hpos]; rfl
        unfold tgt
        rw [e] at hγ hsep ⊢
        exact hω T₀ hγ hsep
      · show -(0 : ℝ) < scl v
        rw [neg_zero]
        exact scl_pos hv0
  filter_upwards [hN, hgood, hvis] with ω hNω hgω hvisω
  obtain ⟨hc, h0, γ, hγ⟩ := hgω
  exact fun M => clock_unbounded_of_oriented hc h0 hγ hv0 hvisω hNω M

end InteractingSLE.Theorem14.BR4aIn
