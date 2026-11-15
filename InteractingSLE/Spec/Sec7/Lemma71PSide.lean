/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PCorner

/-!
# Lemma 7.1's (CS), geometric half: the middle curve's integer along each side of the slit

Packet PROVE-LEMMA71P. Pathwise, at a capacity time `t` (`IsTSetting`: the pocket data `IsPocketSeg`, the inherited
branch, and a continuous driver `W` with trace `η` for the mapped segment up to `t`). With `ψ_t` the chart of the
active component (`tChart`), `D` its domain, `U = capInv γ' t` and `T = κ U` the curve time of the capacity stop:

* `IsTSetting.mem_of_mem_dom`, `notMem_prefix_of_mem_dom`: `D` lies in the pocket, off the stopped middle prefix
  `γ([0, T])`;
* `notMem_prefix_of_alive`: the landing point of an alive real chart point is off `γ([0, T])`;
* **`IsTSetting.subset_H_diff_fillH`** (escape): `D` lies in the unbounded domain of every closed `Γ ⊆ β ∪ γ([0, T])`
  (it touches the right wall at an alive point, beyond which the right side of `α` runs to `∞`);
* `IsTSetting.exists_land_mid'`: landing at the middle chart points before `T`;
* **`IsTSetting.wallInt_local`**, **`IsTSetting.wallInt_of_mem`**: the integer of `Im (log g^γ_T′ − log ψ_t′)` along
  the middle curve exists, is locally constant, hence constant on each side `(L_t − W_t, 0)`, `(0, R_t − W_t)`;
* **`IsTSetting.exists_wallInt_tip`**: the tip corner — the two sides have the same integer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71K (IsMarkedPocket wallPt segPt)
open Lemma71N (IsPocketFrame IsPocketBranch)
open Lemma71O (land WallInt)
open Lemma71C (IsSegCurve capLife capInv segDriver)
open MartChar.RealFlow

/-- **The pathwise setting at capacity time `t`**: the pocket data, the inherited branch `n`, and a continuous driver
`W` (`W 0 = 0`) agreeing with the canonical driver of the mapped segment on `[0, t]` with a Loewner trace `η` equal to
the capacity trace `γ' ∘ capInv` on `[0, t]` (`exists_loewnerTrace`). -/
structure IsTSetting (β α γ : ℝ≥0 → ℂ) (C : Set ℂ) (c : Chart) (Ψ : ℂ → ℂ) (a b : ℝ) (γ' : ℝ → ℂ) (κ : ℝ → ℝ)
    (n : ℤ) (W : ℝ → ℝ) (η : ℝ → ℂ) (t : ℝ≥0) : Prop where
  seg : IsPocketSeg β α γ C c Ψ a b γ' κ
  branch : IsPocketBranch β α c n
  ht : (t : ℝ≥0∞) < capLife γ'
  hW : Continuous W
  hW0 : W 0 = 0
  hWe : EqOn W (Ito.rpath fun s => segDriver γ' s) (Icc 0 t)
  hη : IsLoewnerTrace W η
  hηe : ∀ s : ℝ, 0 ≤ s → s ≤ t → η s = γ' (capInv γ' s)

namespace IsTSetting

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ} {n : ℤ}
  {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ≥0}

theorem ht0 (_ : IsTSetting β α γ C c Ψ a b γ' κ n W η t) : (0 : ℝ) ≤ t := t.coe_nonneg

theorem hc' (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) : (tChart c n W t).IsConformal :=
  (Lemma71E.isConformal_shiftLift hS.seg.frame.hc n).loewner hS.hW hS.hW0 t.coe_nonneg

theorem hB (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) : HasBdryLimits (fwdMapInv W t) :=
  hS.hη.hasBdryLimits hS.hW hS.hW0 t.coe_nonneg

/-- The curve time of the capacity stop. -/
def capT (_ : IsTSetting β α γ C c Ψ a b γ' κ n W η t) : ℝ≥0 := (κ (capInv γ' t)).toNNReal

theorem capT_eq (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) :
    ((hS.capT : ℝ≥0) : ℝ) = κ (capInv γ' t) :=
  Real.coe_toNNReal _ (hS.seg.κ_nonneg (Lemma71C.capInv_nonneg γ' t))

/-- The hull of the mapped prefix. -/
theorem fwdHull_eq (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) :
    fwdHull W t = fillH (γ' '' Icc 0 (capInv γ' t)) := by
  rw [hS.hη.2.2 t t.coe_nonneg]
  congr 1
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [hS.hηe s hs.1 hs.2]
    refine ⟨capInv γ' s, ⟨Lemma71C.capInv_nonneg γ' s, ?_⟩, rfl⟩
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h]
    · have ht' := hS.ht
      rw [← ENNReal.ofReal_coe_nnreal] at ht'
      exact (capInv_lt_capInv hS.seg.seg hs.1 h ht').le
  · rintro ⟨v, hv, rfl⟩
    have hd := PocketTraversal.isDrivenCurve_of_isSegCurve hS.seg.seg
    have ht' : ENNReal.ofReal (t : ℝ) < capLife γ' := by rw [ENNReal.ofReal_coe_nnreal]; exact hS.ht
    obtain ⟨hU0, hU1⟩ := hd.capInv_spec t.coe_nonneg ht'
    have hc0 := hd.capClock_nonneg hv.1
    have hcle : Lemma71C.capClock γ' v ≤ t := by
      rw [← hU1]; exact hd.strictMonoOn_capClock.monotoneOn hv.1 hU0 hv.2
    refine ⟨Lemma71C.capClock γ' v, ⟨hc0, hcle⟩, ?_⟩
    rw [hS.hηe _ hc0 hcle, hd.capInv_eq hv.1]

/-- **A point of the active component** lies in the pocket and its chart value is off the hull `K_t`. -/
theorem mem_of_mem_dom (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {z : ℂ}
    (hz : z ∈ ((tChart c n W t).dom : Set ℂ)) : z ∈ C ∧ c.1 z ∈ H \ fwdHull W t := by
  rw [hS.hc'.coe_dom] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hF := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hS.hW hS.hW0 t.coe_nonneg hy
  refine ⟨?_, ?_⟩
  · rw [← hS.seg.frame.hdom]; exact hS.seg.frame.hc.inv_mem_dom hF.1
  · show c.1 (c.2.1 (fwdMapInv W t y)) ∈ H \ fwdHull W t
    rw [hS.seg.frame.hc.2.2 _ hF.1]; exact hF

theorem inv_mem_dom (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {y : ℂ} (hy : y ∈ H) :
    (tChart c n W t).2.1 y ∈ ((tChart c n W t).dom : Set ℂ) :=
  hS.hc'.inv_mem_dom hy

/-- **The active component misses the stopped middle prefix** `γ([0, T])`. -/
theorem notMem_prefix_of_mem_dom (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {z : ℂ}
    (hz : z ∈ ((tChart c n W t).dom : Set ℂ)) : z ∉ γ '' Icc 0 hS.capT := by
  rintro ⟨s, hs, rfl⟩
  obtain ⟨hzC, hzK⟩ := hS.mem_of_mem_dom hz
  have hF := hS.seg.frame
  have hcK : cayley (γ s) ∈ closure (cayley '' C) \ {wallPt α b} :=
    ⟨subset_closure ⟨γ s, hzC, rfl⟩, fun h => hF.closePt_notMem (by
      rw [← Set.mem_singleton_iff.1 h]; exact ⟨γ s, hzC, rfl⟩)⟩
  have hsle : (s : ℝ) ≤ κ (capInv γ' t) := by rw [← hS.capT_eq]; exact_mod_cast hs.2
  have hmem := hS.seg.mem_image_of_le hcK (Lemma71C.capInv_nonneg γ' t) hsle
  rw [← hF.hΨe _ hzC] at hmem
  apply hzK.2
  rw [hS.fwdHull_eq]
  exact ⟨hzK.1, Or.inl (subset_closure hmem)⟩

/-- **An alive real chart point is off the mapped prefix** (`Lemma71N.ofReal_notMem_image_of_isForwardSol`). -/
theorem ofReal_notMem_seg (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {ξ : ℝ} (hξ0 : ξ ≠ 0) {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W (ξ : ℂ) t u) : (ξ : ℂ) ∉ γ' '' Icc 0 (capInv γ' t) :=
  Lemma71N.ofReal_notMem_image_of_isForwardSol hS.hW t.coe_nonneg hS.seg.seg.1 hS.seg.seg.2.2.1 hS.seg.seg.2.2.2.1
    hS.seg.seg.2.2.2.2.2 hS.fwdHull_eq hξ0 hu

/-- **The landing point of an alive real chart point is off the stopped middle prefix.** -/
theorem notMem_prefix_of_alive (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {ξ : ℝ} (hξ0 : ξ ≠ 0)
    {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W (ξ : ℂ) t u) : land c ξ ∉ γ '' Icc 0 hS.capT := by
  have hF := hS.seg.frame
  have hξH : ((ξ : ℝ) : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨z, hzK, hΨz, -⟩ := Lemma71O.PocketFrame.exists_tendsto hF hξH
  have hland : land c ξ = cayleyInv z := Lemma71O.PocketFrame.land_eq hF hξH hzK hΨz
  rintro ⟨s, hs, hse⟩
  have hz1 : z ≠ 1 := fun h => hF.one_notMem (h ▸ hzK)
  have hcz : cayley (γ s) = z := by rw [hse, hland, QuantumZipper.CA.cayley_cayleyInv hz1]
  have hsle : (s : ℝ) ≤ κ (capInv γ' t) := by rw [← hS.capT_eq]; exact_mod_cast hs.2
  have hmem := hS.seg.mem_image_of_le (by rw [hcz]; exact hzK) (Lemma71C.capInv_nonneg γ' t) hsle
  rw [hcz, hΨz] at hmem
  exact hS.ofReal_notMem_seg hξ0 hu hmem

/-- **Escape** (supplement §2.3: "The pocket `C` lies in `D_p`"): the active component lies in the unbounded domain
of every closed `Γ ⊆ range β ∪ γ([0, T])`: it touches the right wall at the landing point of an alive real chart point
right of `R_t − W_t`, which is off `Γ` and adherent to the right side of `α`, an unbounded connected set off `Γ`. -/
theorem subset_H_diff_fillH (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Γ : Set ℂ} (hΓc : IsClosed Γ)
    (hΓ : Γ ⊆ range β ∪ γ '' Icc 0 hS.capT) : ((tChart c n W t).dom : Set ℂ) ⊆ H \ fillH Γ := by
  have hF := hS.seg.frame
  have ht0 := hS.ht0
  -- an alive real chart point right of the slit
  obtain ⟨y, hy0, hya, hyx⟩ := Lemma71N.exists_alive_cflow_eq hS.hW ht0 (x := rightImg W 0 t - W t + 1)
    (by linarith)
  have hu := WangWu.isForwardSol_of_alive hS.hW hya
  have hFx : extendFrom H (fwdMapInv W t) (cflow W y t) = (y : ℂ) :=
    SideHeight.extendFrom_eq_of_isForwardSol' hS.hB hS.hW hS.hW0 ht0 (mem_Hbar_of_im_eq_zero (by simp)) hu
  obtain ⟨s, hs0, hsβ, hls⟩ := Lemma71O.PocketFrame.land_ofReal_pos hF hy0
  have hland := tendsto_tChart_inv (t := t) hF hS.hη hS.hW hS.hW0 n
    (mem_Hbar_of_im_eq_zero (z := ((cflow W y t : ℝ) : ℂ)) (by simp))
  rw [hFx, hls] at hland
  have hNe := Lemma71O.nhdsWithin_H_ofReal_neBot (cflow W y t)
  have hw₀D : α s ∈ closure ((tChart c n W t).dom : Set ℂ) :=
    mem_closure_of_tendsto hland (eventually_nhdsWithin_of_forall fun y hy => hS.inv_mem_dom hy)
  have hw₀γ : α s ∉ γ '' Icc 0 hS.capT := by
    rw [← hls]; exact hS.notMem_prefix_of_alive hy0.ne' hu
  have hRdisj := Lemma71I.disjoint_rightSideOf_of_subset_closedLeftSide hF.hα.isProperCurve hF.hα.2.2.1 hF.hord
  have hDpc : IsPreconnected ((tChart c n W t).dom : Set ℂ) := by
    rw [hS.hc'.coe_dom]; exact convex_H.isPreconnected.image _ hS.hc'.1.continuousOn
  refine Lemma71O.subset_H_diff_fillH_of_escape hΓc hDpc ?_ ?_ ?_ (Lemma613.not_isBounded_rightSideOf hF.hα)
    (w₀ := α s) ?_ hw₀D (Lemma613.mem_closure_rightSideOf hF.hα s)
  · intro z hz
    obtain ⟨hzC, -⟩ := hS.mem_of_mem_dom hz
    refine ⟨hF.subset_H hzC, fun hzΓ => ?_⟩
    rcases hΓ hzΓ with h | h
    · exact (hF.subset_sides hzC).2.1.2 h
    · exact hS.notMem_prefix_of_mem_dom hz h
  · have h := hF.hα.isProperArc.isPreconnected_rightSideOf
    rwa [Lemma71I.arcRange_realPath] at h
  · intro z hz
    refine ⟨hz.1.1, fun hzΓ => ?_⟩
    rcases hΓ hzΓ with h | ⟨u, -, rfl⟩
    · exact Set.disjoint_left.1 hRdisj h hz
    · exact Set.disjoint_left.1 hS.seg.hγα ⟨u, rfl⟩ hz
  · refine ⟨hF.hα.2.2.2.1 s hs0, fun h => ?_⟩
    rcases hΓ h with h' | h'
    · exact hsβ h'
    · exact hw₀γ h'

end IsTSetting

/-! ### The middle chart points -/

/-- The image `L_t − W_t` of `0⁻`. -/
def midL (W : ℝ → ℝ) (t : ℝ) : ℝ := -rightImg (fun s => -W s) 0 t - W t

/-- The image `R_t − W_t` of `0⁺`. -/
def midR (W : ℝ → ℝ) (t : ℝ) : ℝ := rightImg W 0 t - W t

theorem midL_nonpos {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) : midL W t ≤ 0 := by
  have : -W t ≤ rightImg (fun s => -W s) 0 t := le_rightImg (w := fun s => -W s) hW.neg 0 ht
  unfold midL
  linarith

theorem midR_nonneg {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ midR W t := by
  have := le_rightImg (w := W) hW 0 ht
  unfold midR
  linarith

/-- A function `ℝ≥0 → ℝ` with a generating trace on `[0, ∞)`, read on `ℝ`, is continuous with value `0` at `0`. -/
theorem rdriver_spec {Wγ : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (htr : IsGeneratingTrace Wγ ⊤ γ) :
    Continuous (fun r : ℝ => Wγ r.toNNReal) ∧ (fun r : ℝ => Wγ r.toNNReal) 0 = 0 := by
  refine ⟨(Lemma71O.continuous_of_isGeneratingTrace_top htr).comp continuous_real_toNNReal, ?_⟩
  simp only [Real.toNNReal_zero]
  exact SideHeight.w_zero_of_isGeneratingTrace htr (by simp)

namespace IsTSetting

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ} {n : ℤ}
  {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ≥0}

/-- **CS-a in the setting**: at a middle chart point `x ≠ 0` the inverse of `ψ_t` lands at `γ(σ)` with `σ` strictly
before the capacity stop `T`; `F̄_t(x)` is the mapped segment point. -/
theorem exists_land (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {x : ℝ} (hxL : midL W t < x)
    (hxR : x < midR W t) (hx0 : x ≠ 0) :
    ∃ σ : ℝ≥0, σ < hS.capT ∧ Tendsto (tChart c n W t).2.1 (𝓝[H] (x : ℂ)) (𝓝 (γ σ)) ∧
      ∃ u : ℝ, 0 ≤ u ∧ u < capInv γ' t ∧ extendFrom H (fwdMapInv W t) x = γ' u ∧ σ = (κ u).toNNReal := by
  obtain ⟨u, hu0, hut, hue, hT⟩ := exists_land_mid hS.seg hS.ht hS.hη hS.hW hS.hW0 hS.hηe n hxL hxR hx0
  refine ⟨(κ u).toNNReal, ?_, hT, u, hu0, hut, hue, rfl⟩
  have hlt : κ u < κ (capInv γ' t) := hS.seg.hκ hu0 (Lemma71C.capInv_nonneg γ' t) hut
  exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg (hS.seg.κ_nonneg hu0)).2 hlt

/-- The active component lies off the hull of the stopped middle prefix at every time `q ≤ T`. -/
theorem subset_H_diff_fwdHull (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wγ : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace Wγ ⊤ γ) {q : ℝ≥0} (hq : q ≤ hS.capT) :
    ((tChart c n W t).dom : Set ℂ) ⊆ H \ fwdHull (fun r : ℝ => Wγ r.toNNReal) q := by
  rw [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htr (WithTop.coe_lt_top q)]
  exact hS.subset_H_diff_fillH (isCompact_Icc.image hS.seg.hγ.1).isClosed fun z hz =>
    Or.inr (image_mono (Icc_subset_Icc_right hq) hz)

theorem subset_H_diff_fillH_prefix (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {q : ℝ≥0}
    (hq : q ≤ hS.capT) : ((tChart c n W t).dom : Set ℂ) ⊆ H \ fillH (γ '' Icc 0 q) :=
  hS.subset_H_diff_fillH (isCompact_Icc.image hS.seg.hγ.1).isClosed fun _ hz =>
    Or.inr (image_mono (Icc_subset_Icc_right hq) hz)

/-- **The local integer along the middle curve**: at a middle chart point `x ≠ 0`, one integer `m` with
`Im (log g^γ_T′ − L_t) ∘ ψ_t⁻¹ → 2πm` at all real points near `x` (`Lemma71O.exists_int_wall`: the transition
`g^γ_T ∘ ψ_t⁻¹` has real limits there since the landing points lie on `γ([0, T])`). -/
theorem wallInt_local (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wγ : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace Wγ ⊤ γ) {Lt : ℂ → ℂ}
    (hLt : IsDerivLog (tChart c n W t).1 Lt (tChart c n W t).dom) {x : ℝ} (hxL : midL W t < x)
    (hxR : x < midR W t) (hx0 : x ≠ 0) :
    ∃ m : ℤ, ∃ ε > 0, ∀ z : ℝ, |z - x| < ε → WallInt (tChart c n W t) Lt Wγ hS.capT z m := by
  obtain ⟨hWc, hW0⟩ := rdriver_spec htr
  set r := min (min (x - midL W t) (midR W t - x)) |x| with hr
  have hr0 : 0 < r := lt_min (lt_min (by linarith) (by linarith)) (abs_pos.2 hx0)
  obtain ⟨m, ε, hε, -, hint⟩ := Lemma71O.exists_int_wall (isLoewnerTrace_of_isGeneratingTrace htr) hWc hW0
    hS.capT.2 hS.hc' rfl hLt (hS.subset_H_diff_fwdHull htr le_rfl) hr0 fun z hz hz0 => by
      have hzx : z = ((z.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
      have hd : |z.re - x| < r := by
        rw [hzx, mem_ball, Lemma71O.dist_ofReal_ofReal, Real.dist_eq] at hz; exact hz
      have h1 := lt_of_lt_of_le hd (min_le_left _ _)
      have h2 := lt_of_lt_of_le hd (min_le_right _ _)
      rw [abs_lt] at h1
      obtain ⟨σ, hσ, hT, -⟩ := hS.exists_land (x := z.re)
        (by linarith [min_le_left (x - midL W t) (midR W t - x), h1.1])
        (by linarith [min_le_right (x - midL W t) (midR W t - x), h1.2])
        (fun h => by rw [h, zero_sub, abs_neg] at h2; exact lt_irrefl _ h2)
      refine ⟨γ σ, Lemma71O.notMem_H_diff_fwdHull htr hσ.le, ?_⟩
      rw [hzx]; exact hT
  refine ⟨m, ε, hε, fun z hz => hint (z : ℂ) ?_ (by simp)⟩
  rw [mem_ball, Lemma71O.dist_ofReal_ofReal, Real.dist_eq]
  exact hz

/-- **The integer is constant along each side of the slit** (`Lemma71O.eq_of_isPreconnected_of_local`). -/
theorem wallInt_of_mem (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wγ : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace Wγ ⊤ γ) {Lt : ℂ → ℂ}
    (hLt : IsDerivLog (tChart c n W t).1 Lt (tChart c n W t).dom) {I : Set ℝ} (hI : IsPreconnected I)
    (hIm : ∀ z ∈ I, midL W t < z ∧ z < midR W t ∧ z ≠ 0) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) {m : ℤ}
    (hm : WallInt (tChart c n W t) Lt Wγ hS.capT x m) : WallInt (tChart c n W t) Lt Wγ hS.capT y m :=
  Lemma71O.eq_of_isPreconnected_of_local (P := fun z m => WallInt (tChart c n W t) Lt Wγ hS.capT z m) hI
    (fun _ _ _ _ h h' => Lemma71O.WallInt.unique h h')
    (fun z hz => by
      obtain ⟨m', ε, hε, h⟩ := hS.wallInt_local htr hLt (hIm z hz).1 (hIm z hz).2.1 (hIm z hz).2.2
      exact ⟨m', ε, hε, fun w _ hw => h w hw⟩) hx hy hm

/-- **The tip corner** (supplement §2.3, "the two retained sides share one real interval"): when both sides of the
slit are nonempty, one integer near the tip on both sides (`Lemma71O.exists_int_corner` for `g^γ_T`: the tip lands on
`γ(T)`, the nearby real points on `γ([0, T))`). -/
theorem exists_wallInt_tip (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wγ : ℝ≥0 → ℝ}
    (htr : IsGeneratingTrace Wγ ⊤ γ) {Lt : ℂ → ℂ}
    (hLt : IsDerivLog (tChart c n W t).1 Lt (tChart c n W t).dom) (hL0 : midL W t < 0) (hR0 : 0 < midR W t) :
    ∃ m : ℤ, ∃ ε > 0, ε ≤ -midL W t ∧ ε ≤ midR W t ∧
      ∀ z : ℝ, |z| < ε → WallInt (tChart c n W t) Lt Wγ hS.capT z m := by
  obtain ⟨hWc, hW0⟩ := rdriver_spec htr
  set Wr : ℝ → ℝ := fun r : ℝ => Wγ r.toNNReal with hWr
  set q : ℝ := (hS.capT : ℝ) with hq
  have hq0 : 0 ≤ q := hS.capT.2
  have hCt := hS.subset_H_diff_fwdHull htr le_rfl
  -- the landing at the tip and a bound
  have hland0 := tendsto_tChart_inv (t := t) hS.seg.frame hS.hη hS.hW hS.hW0 n
    (mem_Hbar_of_im_eq_zero (z := (0 : ℂ)) (by simp))
  set p₀ := land c (extendFrom H (fwdMapInv W t) 0) with hp₀
  obtain ⟨δ, hδ, hδp⟩ := Metric.tendsto_nhdsWithin_nhds.1 hland0 1 one_pos
  obtain ⟨M, hM⟩ := (isMapOut_fwdMap hWc hW0 hq0).exists_norm_sub_le (isHPHull_fwdHull hWc hq0)
  set r := min δ (min (-midL W t) (midR W t)) with hr
  have hr0 : 0 < r := lt_min hδ (lt_min (by linarith) hR0)
  have hbd : ∀ y ∈ ball (0 : ℂ) r ∩ H, ‖fwdMap Wr q ((tChart c n W t).2.1 y)‖ ≤ ‖p₀‖ + 1 + M + |Wr q| := by
    rintro y ⟨hyb, hy⟩
    have h1 := hδp hy (lt_of_lt_of_le (mem_ball.1 hyb) (min_le_left _ _))
    have hz := hCt (hS.inv_mem_dom hy)
    have h2 := hM _ hz
    have h3 : ‖(tChart c n W t).2.1 y‖ ≤ ‖p₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' ((tChart c n W t).2.1 y) p₀
      rw [← dist_eq_norm] at this
      linarith
    have h4 := norm_le_norm_add_norm_sub' (fwdMap Wr q ((tChart c n W t).2.1 y) + Wr q) ((tChart c n W t).2.1 y)
    have h5 : ‖fwdMap Wr q ((tChart c n W t).2.1 y)‖ ≤
        ‖fwdMap Wr q ((tChart c n W t).2.1 y) + Wr q‖ + |Wr q| := by
      have := norm_sub_le (fwdMap Wr q ((tChart c n W t).2.1 y) + Wr q) ((Wr q : ℝ) : ℂ)
      rw [add_sub_cancel_right, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    linarith
  have hlim : ∀ z ∈ ball (0 : ℂ) r, z.im = 0 → z ≠ 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun y => fwdMap Wr q ((tChart c n W t).2.1 y)) (𝓝[H] z) (𝓝 v) := by
    intro z hz hz0 hzne
    have hzx : z = ((z.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
    have hzr : |z.re| < r := by
      rw [hzx, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at hz; exact hz
    have h2 := lt_of_lt_of_le hzr (min_le_right _ _)
    rw [abs_lt] at h2
    obtain ⟨σ, hσ, hT, -⟩ := hS.exists_land (x := z.re)
      (by linarith [min_le_left (-midL W t) (midR W t), h2.1])
      (by linarith [min_le_right (-midL W t) (midR W t), h2.2])
      (fun h => hzne (by rw [hzx, h, ofReal_zero]))
    rw [hzx] at hT ⊢
    exact Lemma71O.exists_real_tendsto_wall htr (Lemma71O.continuous_of_isGeneratingTrace_top htr)
      (SideHeight.w_zero_of_isGeneratingTrace htr (by simp)) hS.hc' hCt (mem_Hbar_of_im_eq_zero (by simp)) hσ.le hT
  obtain ⟨m, ε, hε, hεr, hcorner⟩ := Lemma71O.exists_int_corner hS.hc' rfl hLt
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWc hq0) hCt (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWc hq0)
    (QuantumZipper.FwdHolo.injOn_fwdMap hWc hq0) (fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hWc hq0 hz)
    (isDerivLog_fwdMap hWc hq0) hr0 hbd hlim
  refine ⟨m, ε, hε, (hεr.trans (min_le_right _ _)).trans (min_le_left _ _),
    (hεr.trans (min_le_right _ _)).trans (min_le_right _ _), fun z hz => hcorner (z : ℂ) ?_ (by simp)⟩
  rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  exact hz

end IsTSetting

end InteractingSLE.Sec7.Lemma71P
