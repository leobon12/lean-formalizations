/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ChamberArcs
import InteractingSLE.Foundations.Loewner.YuanShift
import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc

/-!
# The two sides of a simple Loewner trace under the mapping-out function

Packet PROVE-WW-B6. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), the boundary
values of a seed line's mean (proof of Proposition 4.19: "On a compact subarc of `β`, compare with a sufficiently long
finite prefix … Local-set boundary compatibility therefore gives the boundary value `+λ` from `R`"; proof of Lemma 4.10:
"The Loewner prime-end map identifies `(L_t, W_t)` and `(W_t, R_t)` as the two hull-frontier intervals"; proof of
Lemma 4.15: "On each new slit side … (PA) has the required value `−λ` or `+λ`"). This is the obstruction 1 of
`planning/handoffs/PROVE-WW-B5.md` (the prime-end boundary correspondence of `g_t` at the two sides of a simple slit).

Setting: `W` a continuous driver with `W 0 = 0`, `η` a continuous Loewner trace of `W` (`IsLoewnerTrace`) which is a
simple proper arc of `ℍ` from `0` to `∞` (`IsProperArc`), `t > 0`, `f_t = fwdMap W t` the centred mapping-out function
`g_t − W_t` of the hull `K_t = η(0, t]`, and `F̄_t = extendFrom ℍ (fwdMapInv W t)` the continuous extension of its
inverse to `ℍ̄`.

* `IsProperArc.leftSideOf_eq_image`, `isPreconnected_leftSideOf`: the left side of a proper arc is the Cayley preimage
  of the upper side of its crosscut, hence connected; `exists_ball_inter_H_subset_leftSideOf`: near a negative real
  point, `ℍ` lies on the left side; `notMem_closure_leftSideOf_of_pos`: no positive real point is adherent to it (and
  the mirror statements for the right side).
* `futureArc W t = loewnerTip (shiftDrive W t)`: the **mapped future** `u ↦ g_t(η(t + u)) − W_t`
  (`extendFrom_futureArc`: `F̄_t(β(u)) = η(t + u)`, PROVE-GEO-YUAN's [Yua22] Corollary 1.3 machinery), and
  `isProperArc_futureArc`: it is again a simple proper arc from `0`.
* `fwdMap_mem_leftSideOf_futureArc`: **`f_t` maps the left side of `η` into the left side of the mapped future** (the
  left side is connected, its image avoids the mapped future, and points near `−R`, `R` large, are mapped near the
  negative real axis); mirror for the right side.
* `exists_neg_of_mapClusterPt_leftSideOf`: every cluster point of `f_t(z)` as `z → η(s)` (`0 < s < t`) from the left
  side of `η` is a **negative real** `x` with `F̄_t(x) = η(s)` (mirror: positive).
* **`tendsto_comp_fwdMap_leftSideOf`**: hence a function `c` with the limit `ℓ` at every such real point (from `ℍ`) has
  `c(f_t(z)) → ℓ` as `z → η(s)` from the left side of `η` (mirror: right side).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.WangWu

/-! ### The two sides of a proper arc -/

/-- A real point is adherent to every half-disc of `ℍ` around it. -/
theorem ofReal_mem_closure_ball_inter_H (x : ℝ) {r : ℝ} (hr : 0 < r) :
    (x : ℂ) ∈ closure (ball (x : ℂ) r ∩ H) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hm : 0 < min ε r / 2 := by positivity
  have hnorm : ‖((min ε r / 2 : ℝ) : ℂ) * I‖ = min ε r / 2 := by
    rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
  refine ⟨x + ((min ε r / 2 : ℝ) : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq, add_sub_cancel_left, hnorm]
    linarith [min_le_right ε r]
  · show 0 < (((x : ℂ) + ((min ε r / 2 : ℝ) : ℂ) * I)).im
    simpa using hm
  · rw [dist_eq, sub_add_cancel_left, norm_neg, hnorm]
    linarith [min_le_left ε r]

namespace IsProperArc

variable {γ : ℝ → ℂ}

/-- **The left side of a proper arc is the Cayley preimage of the upper side of its crosscut.** -/
theorem leftSideOf_eq_image (hγ : IsProperArc γ) :
    leftSideOf (arcRange γ) = cayleyInv '' crossSide (toDisc γ) 1 := by
  ext z
  constructor
  · intro hz
    have hzH : z ∈ H := hz.1.1
    exact ⟨cayley z, (hγ.mem_leftSideOf_iff hzH).1 hz,
      cayleyInv_cayley_of_mem_Hbar (le_of_lt (show (0 : ℝ) < z.im from hzH))⟩
  · rintro ⟨w, hw, rfl⟩
    have hwb : w ∈ ball (0 : ℂ) 1 := (hγ.isDiscCrosscut_toDisc.crossSide_subset (Or.inl rfl) hw).1
    refine (hγ.mem_leftSideOf_iff (QuantumZipper.CA.cayleyInv_mem_H hwb)).2 ?_
    rwa [cayley_cayleyInv_of_mem_ball hwb]

/-- **The right side of a proper arc is the Cayley preimage of the lower side of its crosscut.** -/
theorem rightSideOf_eq_image (hγ : IsProperArc γ) :
    rightSideOf (arcRange γ) = cayleyInv '' crossSide (toDisc γ) (-1) := by
  ext z
  constructor
  · intro hz
    have hzH : z ∈ H := hz.1.1
    exact ⟨cayley z, (hγ.mem_rightSideOf_iff hzH).1 hz,
      cayleyInv_cayley_of_mem_Hbar (le_of_lt (show (0 : ℝ) < z.im from hzH))⟩
  · rintro ⟨w, hw, rfl⟩
    have hwb : w ∈ ball (0 : ℂ) 1 := (hγ.isDiscCrosscut_toDisc.crossSide_subset (Or.inr rfl) hw).1
    refine (hγ.mem_rightSideOf_iff (QuantumZipper.CA.cayleyInv_mem_H hwb)).2 ?_
    rwa [cayley_cayleyInv_of_mem_ball hwb]

theorem continuousOn_cayleyInv_ball : ContinuousOn cayleyInv (ball (0 : ℂ) 1) := fun _ hw =>
  (continuousAt_cayleyInv (ne_one_of_mem_ball hw)).continuousWithinAt

/-- The left side of a proper arc is connected. -/
theorem isPreconnected_leftSideOf (hγ : IsProperArc γ) : IsPreconnected (leftSideOf (arcRange γ)) := by
  rw [hγ.leftSideOf_eq_image]
  exact (hγ.isDiscCrosscut_toDisc.isPreconnected_crossSide (Or.inl rfl)).image _
    (continuousOn_cayleyInv_ball.mono fun w hw =>
      (hγ.isDiscCrosscut_toDisc.crossSide_subset (Or.inl rfl) hw).1)

/-- The right side of a proper arc is connected. -/
theorem isPreconnected_rightSideOf (hγ : IsProperArc γ) : IsPreconnected (rightSideOf (arcRange γ)) := by
  rw [hγ.rightSideOf_eq_image]
  exact (hγ.isDiscCrosscut_toDisc.isPreconnected_crossSide (Or.inr rfl)).image _
    (continuousOn_cayleyInv_ball.mono fun w hw =>
      (hγ.isDiscCrosscut_toDisc.crossSide_subset (Or.inr rfl) hw).1)

/-- A real point off the arc has a half-disc neighbourhood in `ℍ` off the arc, contained in one component. -/
theorem exists_ball_inter_H_subset_component (hγ : IsProperArc γ) {x : ℝ} (hx : x ≠ 0) :
    ∃ r > 0, ∀ z ∈ ball (x : ℂ) r ∩ H, z ∈ H \ arcRange γ ∧
      ball (x : ℂ) r ∩ H ⊆ connectedComponentIn (H \ arcRange γ) z := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 hγ.isClosed_arcRange.isOpen_compl x
    (hγ.ofReal_notMem_arcRange hx)
  have hdisj : ball (x : ℂ) r ∩ H ⊆ H \ arcRange γ := fun z hz => ⟨hz.2, hsub hz.1⟩
  refine ⟨r, hr, fun z hz => ⟨hdisj hz, ?_⟩⟩
  exact ((convex_ball _ _).inter (convex_H)).isPreconnected.subset_connectedComponentIn hz hdisj

/-- **Near a negative real point, `ℍ` lies on the left side of a proper arc.** -/
theorem exists_ball_inter_H_subset_leftSideOf (hγ : IsProperArc γ) {x : ℝ} (hx : x < 0) :
    ∃ r > 0, ball (x : ℂ) r ∩ H ⊆ leftSideOf (arcRange γ) := by
  obtain ⟨r, hr, h⟩ := hγ.exists_ball_inter_H_subset_component hx.ne
  exact ⟨r, hr, fun z hz => ⟨(h z hz).1, x, hx, hγ.ofReal_notMem_arcRange hx.ne,
    closure_mono (h z hz).2 (ofReal_mem_closure_ball_inter_H x hr)⟩⟩

/-- **Near a positive real point, `ℍ` lies on the right side of a proper arc.** -/
theorem exists_ball_inter_H_subset_rightSideOf (hγ : IsProperArc γ) {x : ℝ} (hx : 0 < x) :
    ∃ r > 0, ball (x : ℂ) r ∩ H ⊆ rightSideOf (arcRange γ) := by
  obtain ⟨r, hr, h⟩ := hγ.exists_ball_inter_H_subset_component hx.ne'
  exact ⟨r, hr, fun z hz => ⟨(h z hz).1, x, hx, hγ.ofReal_notMem_arcRange hx.ne',
    closure_mono (h z hz).2 (ofReal_mem_closure_ball_inter_H x hr)⟩⟩

/-- **No positive real point is adherent to the left side of a proper arc.** -/
theorem notMem_closure_leftSideOf_of_pos (hγ : IsProperArc γ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ∉ closure (leftSideOf (arcRange γ)) := by
  obtain ⟨r, hr, h⟩ := hγ.exists_ball_inter_H_subset_rightSideOf hx
  intro hcl
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.1 hcl r hr
  have hzH : z ∈ H := hz.1.1
  have hzr : z ∈ rightSideOf (arcRange γ) := h ⟨by rw [mem_ball, dist_comm]; exact hzx, hzH⟩
  exact Set.disjoint_left.1 hγ.disjoint_leftSideOf_rightSideOf hz hzr

/-- **No negative real point is adherent to the right side of a proper arc.** -/
theorem notMem_closure_rightSideOf_of_neg (hγ : IsProperArc γ) {x : ℝ} (hx : x < 0) :
    (x : ℂ) ∉ closure (rightSideOf (arcRange γ)) := by
  obtain ⟨r, hr, h⟩ := hγ.exists_ball_inter_H_subset_leftSideOf hx
  intro hcl
  obtain ⟨z, hz, hzx⟩ := Metric.mem_closure_iff.1 hcl r hr
  have hzH : z ∈ H := hz.1.1
  have hzl : z ∈ leftSideOf (arcRange γ) := h ⟨by rw [mem_ball, dist_comm]; exact hzx, hzH⟩
  exact Set.disjoint_left.1 hγ.disjoint_leftSideOf_rightSideOf hzl hz

end IsProperArc

/-! ### The inverse map and its boundary extension -/

section Inverse

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- The continuous extension `F̄_t` of the inverse map stays at bounded distance from the identity on `ℍ̄`. -/
theorem exists_norm_extendFrom_sub_le (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) : ∃ C : ℝ, (∀ w ∈ H, ‖fwdMapInv W t w - w‖ ≤ C) ∧
      ∀ ξ ∈ Hbar, ‖extendFrom H (fwdMapInv W t) ξ - ξ‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ht
  refine ⟨C, hC, fun ξ hξ => ?_⟩
  have hlim := (hη.hasBdryLimits hW hW0 ht).tendsto hξ
  have : (𝓝[H] ξ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hξ)
  have h2 : Tendsto (fun w => ‖fwdMapInv W t w - w‖) (𝓝[H] ξ)
      (𝓝 ‖extendFrom H (fwdMapInv W t) ξ - ξ‖) :=
    (hlim.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
  exact le_of_tendsto h2 (eventually_nhdsWithin_of_forall fun w hw => hC w hw)

/-- `F̄_t = F_t` on `ℍ`. -/
theorem extendFrom_fwdMapInv_eq (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {w : ℂ} (hw : w ∈ H) :
    extendFrom H (fwdMapInv W t) w = fwdMapInv W t w :=
  extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ht) hw

/-- `F̄_t ∘ f_t = id` off the hull. -/
theorem extendFrom_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ fwdHull W t) : extendFrom H (fwdMapInv W t) (fwdMap W t z) = z := by
  rw [extendFrom_fwdMapInv_eq hW hW0 ht (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz),
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hz]

/-- **The cluster lemma.** Along an ultrafilter converging to `p` inside a set `S` off the hull, `f_t` converges to a
point `y ∈ ℍ̄` with `F̄_t(y) = p`. -/
theorem exists_tendsto_fwdMap_ultrafilter (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) {S : Set ℂ} (hS : S ⊆ H \ fwdHull W t) {p : ℂ} (U : Ultrafilter ℂ)
    (hU : (U : Filter ℂ) ≤ 𝓝[S] p) :
    ∃ y ∈ Hbar, Tendsto (fwdMap W t) U (𝓝 y) ∧ extendFrom H (fwdMapInv W t) y = p := by
  obtain ⟨C, hC, hCbar⟩ := exists_norm_extendFrom_sub_le hη hW hW0 ht
  have hUS : ∀ᶠ w in (U : Filter ℂ), w ∈ S := hU self_mem_nhdsWithin
  have hUp : Tendsto id (U : Filter ℂ) (𝓝 p) := hU.trans nhdsWithin_le_nhds
  have hUb : ∀ᶠ w in (U : Filter ℂ), w ∈ ball p 1 := hUp (ball_mem_nhds p one_pos)
  have hgH : ∀ᶠ w in (U : Filter ℂ), fwdMap W t w ∈ H :=
    hUS.mono fun w hw => QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht (hS hw)
  have hgK : ∀ᶠ w in (U : Filter ℂ), fwdMap W t w ∈ closedBall (0 : ℂ) (‖p‖ + 1 + C) := by
    filter_upwards [hUS, hUb] with w hw hwb
    have e := QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht (hS hw)
    have h1 := hC _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht (hS hw))
    rw [e] at h1
    rw [mem_closedBall, dist_zero_right]
    have h2 : ‖w‖ ≤ ‖p‖ + 1 := by
      have := norm_le_norm_add_norm_sub' w p
      rw [mem_ball, dist_eq] at hwb
      linarith
    calc ‖fwdMap W t w‖ ≤ ‖w‖ + ‖fwdMap W t w - w‖ := norm_le_norm_add_norm_sub' _ _
      _ = ‖w‖ + ‖w - fwdMap W t w‖ := by rw [norm_sub_rev]
      _ ≤ ‖p‖ + 1 + C := by linarith
  obtain ⟨y, -, hy⟩ := (isCompact_closedBall (0 : ℂ) (‖p‖ + 1 + C)).ultrafilter_le_nhds
    (U.map (fwdMap W t)) (by rw [Ultrafilter.coe_map, le_principal_iff]; exact hgK)
  have hy' : Tendsto (fwdMap W t) U (𝓝 y) := by rw [Ultrafilter.coe_map] at hy; exact hy
  have hyH : y ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hy' hgH
  refine ⟨y, hyH, hy', ?_⟩
  have hF : Tendsto (extendFrom H (fwdMapInv W t)) (𝓝[Hbar] y) (𝓝 (extendFrom H (fwdMapInv W t) y)) :=
    (hη.hasBdryLimits hW hW0 ht).continuousOn y hyH
  have hy'' : Tendsto (fwdMap W t) U (𝓝[Hbar] y) :=
    tendsto_nhdsWithin_iff.2 ⟨hy', hgH.mono fun w hw => le_of_lt (show (0 : ℝ) < (fwdMap W t w).im from hw)⟩
  have h1 := hF.comp hy''
  have h2 : Tendsto (fun w => extendFrom H (fwdMapInv W t) (fwdMap W t w)) U (𝓝 p) :=
    hUp.congr' (hUS.mono fun w hw => (extendFrom_fwdMap hW hW0 ht (hS hw)).symm)
  exact tendsto_nhds_unique h1 h2

end Inverse

/-! ### The mapped future of a simple trace -/

section Future

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- **The hull of a simple trace** is its initial piece without the real start. -/
theorem fwdHull_eq_image_Ioc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (ht : 0 ≤ t) :
    fwdHull W t = η '' Ioc 0 t := by
  rw [hη.2.2 t ht]
  exact YuanCharacterisation.fillH_image_eq ht (hγ.cont.mono Icc_subset_Ici_self)
    (hγ.inj.mono Icc_subset_Ici_self) (by rw [hγ.zero, zero_im]) fun u hu => hγ.mem_H u hu.1

theorem fwdHull_subset_arcRange (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (ht : 0 ≤ t) :
    fwdHull W t ⊆ arcRange η := by
  rw [fwdHull_eq_image_Ioc hη hγ ht]
  exact image_mono fun u hu => le_of_lt hu.1

/-- Later points of a simple trace are off the hull. -/
theorem mem_H_diff_fwdHull (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (ht : 0 ≤ t) {u : ℝ}
    (hu : t < u) : η u ∈ H \ fwdHull W t := by
  refine ⟨hγ.mem_H u (ht.trans_lt hu), ?_⟩
  rw [fwdHull_eq_image_Ioc hη hγ ht]
  rintro ⟨u', hu', e⟩
  have := hγ.inj (mem_Ici.2 hu'.1.le) (mem_Ici.2 (ht.trans hu.le)) e
  linarith [hu'.2]

/-- The mapped future `u ↦ g_t(η(t + u)) − W_t` (the tip of the shifted chain, [Yua22] Corollary 1.3). -/
def futureArc (W : ℝ → ℝ) (t : ℝ) : ℝ → ℂ := loewnerTip (QuantumZipper.RS.shiftDrive W t)

theorem extendFrom_futureArc (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    {u : ℝ} (hu : 0 ≤ u) :
    futureArc W t u ∈ Hbar ∧ extendFrom H (fwdMapInv W t) (futureArc W t u) = η (t + u) :=
  ⟨(hη.extendFrom_shift_tip hW hW0 ht hu).1, (hη.extendFrom_shift_tip hW hW0 ht hu).2.1⟩

theorem futureArc_mem_H (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) {u : ℝ} (hu : 0 < u) : futureArc W t u ∈ H := by
  obtain ⟨h1, h2⟩ := extendFrom_futureArc hη hW hW0 ht hu.le
  by_contra hH
  have him : (futureArc W t u).im = 0 :=
    le_antisymm (not_lt.1 hH) h1
  exact hη.extendFrom_not_mem hW hW0 ht him (h2 ▸ mem_H_diff_fwdHull hη hγ ht (by linarith))

theorem futureArc_zero (hW : Continuous W) : futureArc W t 0 = 0 := by
  have hW' : Continuous (QuantumZipper.RS.shiftDrive W t) := QuantumZipper.RS.continuous_shiftDrive hW t
  have hW0' : QuantumZipper.RS.shiftDrive W t 0 = 0 := by simp [QuantumZipper.RS.shiftDrive]
  have h0 : (0 : ℂ) ∈ closure H := by rw [closure_H]; exact zero_mem_Hbar
  refine extendFrom_eq h0 ?_
  have : Tendsto (fun w : ℂ => w) (𝓝[H] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  exact this.congr' (eventually_nhdsWithin_of_forall fun w hw => (fwdMapInv_zero_time hW' hW0' hw).symm)

/-- **The mapped future of a simple proper trace is a simple proper arc from `0`.** -/
theorem isProperArc_futureArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) : IsProperArc (futureArc W t) := by
  have hFinj : ∀ {u u' : ℝ}, 0 ≤ u → 0 ≤ u' → futureArc W t u = futureArc W t u' → u = u' := by
    intro u u' hu hu' e
    have h := congrArg (extendFrom H (fwdMapInv W t)) e
    rw [(extendFrom_futureArc hη hW hW0 ht hu).2, (extendFrom_futureArc hη hW hW0 ht hu').2] at h
    have := hγ.inj (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) h
    linarith
  obtain ⟨C, -, hC⟩ := exists_norm_extendFrom_sub_le hη hW hW0 ht
  refine ⟨fun u hu => ?_, fun u hu u' hu' e => hFinj hu hu' e, futureArc_zero hW,
    fun u hu => futureArc_mem_H hη hγ hW hW0 ht hu, ?_⟩
  · rcases eq_or_lt_of_le (mem_Ici.1 hu) with h0 | hpos
    · subst h0
      exact hη.continuousWithinAt_shift_Ici hW hW0 ht le_rfl
    · refine hη.continuousWithinAt_shift_of_subsingleton hW hW0 ht hpos.le ?_
      rintro ξ ⟨hξ, hξe⟩ ξ' ⟨hξ', hξe'⟩
      have hmem := mem_H_diff_fwdHull hη hγ ht (show t < t + u by linarith)
      have hξH : ξ ∈ H := by
        by_contra hH
        exact hη.extendFrom_not_mem hW hW0 ht (le_antisymm (not_lt.1 hH) hξ) (hξe ▸ hmem)
      have hξH' : ξ' ∈ H := by
        by_contra hH
        exact hη.extendFrom_not_mem hW hW0 ht (le_antisymm (not_lt.1 hH) hξ') (hξe' ▸ hmem)
      rw [extendFrom_fwdMapInv_eq hW hW0 ht hξH] at hξe
      rw [extendFrom_fwdMapInv_eq hW hW0 ht hξH'] at hξe'
      exact (isConformalBijection_fwdMapInv hW hW0 ht).2.injOn hξH hξH' (hξe.trans hξe'.symm)
  · have h1 : Tendsto (fun u => ‖η (t + u)‖) atTop atTop :=
      hγ.tendsto.comp (tendsto_atTop_add_const_left _ t tendsto_id)
    refine tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right _ (-C) h1)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    obtain ⟨hm, he⟩ := extendFrom_futureArc hη hW hW0 ht hu
    have := hC _ hm
    rw [he] at this
    have h2 := norm_le_norm_add_norm_sub' (η (t + u)) (futureArc W t u)
    have h3 : ‖η (t + u) - futureArc W t u‖ ≤ C := this
    linarith

theorem arcRange_futureArc_notMem_ofReal (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) {x : ℝ} (hx : x ≠ 0) : (x : ℂ) ∉ arcRange (futureArc W t) :=
  (isProperArc_futureArc hη hγ hW hW0 ht).ofReal_notMem_arcRange hx

end Future

/-! ### The sides under the mapping-out function -/

section Sides

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- `f_t` maps the complement of the trace into the complement of the mapped future. -/
theorem fwdMap_notMem_arcRange_futureArc (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull W t) (hzA : z ∉ arcRange η) :
    fwdMap W t z ∉ arcRange (futureArc W t) := by
  rintro ⟨u, hu, e⟩
  have h := (extendFrom_futureArc hη hW hW0 ht hu).2
  rw [e, extendFrom_fwdMap hW hW0 ht hz] at h
  exact hzA ⟨t + u, mem_Ici.2 (by linarith [mem_Ici.1 hu]), h.symm⟩

/-- **`f_t` maps the left side of a simple trace into the left side of its mapped future.** -/
theorem fwdMap_mem_leftSideOf_futureArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ leftSideOf (arcRange η)) :
    fwdMap W t z ∈ leftSideOf (arcRange (futureArc W t)) := by
  set S := leftSideOf (arcRange η)
  have hSK : S ⊆ H \ fwdHull W t := fun w hw =>
    ⟨hw.1.1, fun hK => hw.1.2 (fwdHull_subset_arcRange hη hγ ht hK)⟩
  have hcont : ContinuousOn (fwdMap W t) S :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn.mono hSK
  have hsub : fwdMap W t '' S ⊆ H \ arcRange (futureArc W t) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht (hSK hw),
      fwdMap_notMem_arcRange_futureArc hη hW hW0 ht (hSK hw) hw.1.2⟩
  have hcomp : fwdMap W t '' S ⊆ connectedComponentIn (H \ arcRange (futureArc W t)) (fwdMap W t z) :=
    (hγ.isPreconnected_leftSideOf.image _ hcont).subset_connectedComponentIn
      (mem_image_of_mem _ hz) hsub
  refine ⟨hsub (mem_image_of_mem _ hz), ?_⟩
  -- a negative real point adherent to the image, near `−(C + 1)`
  obtain ⟨C, -, hC⟩ := exists_norm_extendFrom_sub_le hη hW hW0 ht
  set x₀ : ℝ := -(|C| + 1)
  have hx₀ : x₀ < 0 := by simp only [x₀]; linarith [abs_nonneg C]
  obtain ⟨r, hr, hrS⟩ := hγ.exists_ball_inter_H_subset_leftSideOf hx₀
  have hcl : (x₀ : ℂ) ∈ closure (ball (x₀ : ℂ) r ∩ H) := ofReal_mem_closure_ball_inter_H x₀ hr
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  set U := Ultrafilter.of (𝓝[ball (x₀ : ℂ) r ∩ H] (x₀ : ℂ))
  obtain ⟨y, hyH, hy, hFy⟩ := exists_tendsto_fwdMap_ultrafilter hη hW hW0 ht (hrS.trans hSK) U
    (Ultrafilter.of_le _)
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have := (isConformalBijection_fwdMapInv hW hW0 ht).2.mapsTo (show y ∈ H from hpos)
    rw [← extendFrom_fwdMapInv_eq hW hW0 ht hpos, hFy] at this
    exact lt_irrefl _ (show (0 : ℝ) < ((x₀ : ℝ) : ℂ).im from this.1)
  have hyre : y.re < 0 := by
    have h1 := hC y hyH
    rw [hFy] at h1
    have h2 : |((x₀ : ℂ) - y).re| ≤ ‖(x₀ : ℂ) - y‖ := Complex.abs_re_le_norm _
    rw [sub_re, ofReal_re] at h2
    have := (abs_le.1 (h2.trans h1)).1
    simp only [x₀] at this
    linarith [le_abs_self C]
  have hyeq : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyim])
  refine ⟨y.re, hyre, arcRange_futureArc_notMem_ofReal hη hγ hW hW0 ht hyre.ne, ?_⟩
  rw [← hyeq]
  refine closure_mono hcomp (mem_closure_of_tendsto hy ?_)
  have hU : ∀ᶠ w in (U : Filter ℂ), w ∈ ball (x₀ : ℂ) r ∩ H := Ultrafilter.of_le _ self_mem_nhdsWithin
  exact hU.mono fun w hw => mem_image_of_mem _ (hrS hw)

/-- **`f_t` maps the right side of a simple trace into the right side of its mapped future.** -/
theorem fwdMap_mem_rightSideOf_futureArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ rightSideOf (arcRange η)) :
    fwdMap W t z ∈ rightSideOf (arcRange (futureArc W t)) := by
  set S := rightSideOf (arcRange η)
  have hSK : S ⊆ H \ fwdHull W t := fun w hw =>
    ⟨hw.1.1, fun hK => hw.1.2 (fwdHull_subset_arcRange hη hγ ht hK)⟩
  have hcont : ContinuousOn (fwdMap W t) S :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn.mono hSK
  have hsub : fwdMap W t '' S ⊆ H \ arcRange (futureArc W t) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht (hSK hw),
      fwdMap_notMem_arcRange_futureArc hη hW hW0 ht (hSK hw) hw.1.2⟩
  have hcomp : fwdMap W t '' S ⊆ connectedComponentIn (H \ arcRange (futureArc W t)) (fwdMap W t z) :=
    (hγ.isPreconnected_rightSideOf.image _ hcont).subset_connectedComponentIn
      (mem_image_of_mem _ hz) hsub
  refine ⟨hsub (mem_image_of_mem _ hz), ?_⟩
  -- a positive real point adherent to the image, near `C + 1`
  obtain ⟨C, -, hC⟩ := exists_norm_extendFrom_sub_le hη hW hW0 ht
  set x₀ : ℝ := |C| + 1
  have hx₀ : 0 < x₀ := by simp only [x₀]; linarith [abs_nonneg C]
  obtain ⟨r, hr, hrS⟩ := hγ.exists_ball_inter_H_subset_rightSideOf hx₀
  have hcl : (x₀ : ℂ) ∈ closure (ball (x₀ : ℂ) r ∩ H) := ofReal_mem_closure_ball_inter_H x₀ hr
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  set U := Ultrafilter.of (𝓝[ball (x₀ : ℂ) r ∩ H] (x₀ : ℂ))
  obtain ⟨y, hyH, hy, hFy⟩ := exists_tendsto_fwdMap_ultrafilter hη hW hW0 ht (hrS.trans hSK) U
    (Ultrafilter.of_le _)
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have := (isConformalBijection_fwdMapInv hW hW0 ht).2.mapsTo (show y ∈ H from hpos)
    rw [← extendFrom_fwdMapInv_eq hW hW0 ht hpos, hFy] at this
    exact lt_irrefl _ (show (0 : ℝ) < ((x₀ : ℝ) : ℂ).im from this.1)
  have hyre : 0 < y.re := by
    have h1 := hC y hyH
    rw [hFy] at h1
    have h2 : |((x₀ : ℂ) - y).re| ≤ ‖(x₀ : ℂ) - y‖ := Complex.abs_re_le_norm _
    rw [sub_re, ofReal_re] at h2
    have := (abs_le.1 (h2.trans h1)).2
    simp only [x₀] at this
    linarith [le_abs_self C]
  have hyeq : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyim])
  refine ⟨y.re, hyre, arcRange_futureArc_notMem_ofReal hη hγ hW hW0 ht hyre.ne', ?_⟩
  rw [← hyeq]
  refine closure_mono hcomp (mem_closure_of_tendsto hy ?_)
  have hU : ∀ᶠ w in (U : Filter ℂ), w ∈ ball (x₀ : ℂ) r ∩ H := Ultrafilter.of_le _ self_mem_nhdsWithin
  exact hU.mono fun w hw => mem_image_of_mem _ (hrS hw)

end Sides

/-! ### Boundary values at the two sides of the slit -/

section Values

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ}

/-- `F̄_t(0) = η(t)`: the driving point is the tip. -/
theorem extendFrom_zero (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) :
    extendFrom H (fwdMapInv W t) 0 = η t :=
  extendFrom_eq (by rw [closure_H]; exact zero_mem_Hbar) (hη.tendsto_fwdMapInv_tip hW hW0 ht)

/-- The common part of the two side statements: along an ultrafilter converging to `η(s)` (`0 < s < t`) inside a set
`S` off the hull, `f_t` converges to a nonzero real point `x` with `F̄_t(x) = η(s)`, from `ℍ`. -/
theorem exists_real_tendsto_fwdMap (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {s : ℝ} (hs : 0 < s) (hst : s < t) {S : Set ℂ} (hS : S ⊆ H \ fwdHull W t)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[S] (η s)) :
    ∃ x : ℝ, x ≠ 0 ∧ extendFrom H (fwdMapInv W t) x = η s ∧ Tendsto (fwdMap W t) U (𝓝[H] (x : ℂ)) ∧
      (x : ℂ) ∈ closure (fwdMap W t '' S) := by
  have ht : 0 ≤ t := (hs.trans hst).le
  obtain ⟨y, hyH, hy, hFy⟩ := exists_tendsto_fwdMap_ultrafilter hη hW hW0 ht hS U hU
  have hsK : η s ∈ fwdHull W t := by
    rw [fwdHull_eq_image_Ioc hη hγ ht]
    exact ⟨s, ⟨hs, hst.le⟩, rfl⟩
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hyH
    have := (isConformalBijection_fwdMapInv hW hW0 ht).2.mapsTo (show y ∈ H from hpos)
    rw [← extendFrom_fwdMapInv_eq hW hW0 ht hpos, hFy] at this
    exact this.2 hsK
  have hyeq : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyim])
  have hUS : ∀ᶠ w in (U : Filter ℂ), w ∈ S := hU self_mem_nhdsWithin
  refine ⟨y.re, fun h0 => ?_, hyeq ▸ hFy, ?_, ?_⟩
  · have hy0 : y = 0 := by rw [hyeq, h0, ofReal_zero]
    rw [hy0, extendFrom_zero hη hW hW0 ht] at hFy
    have := hγ.inj (mem_Ici.2 ht) (mem_Ici.2 hs.le) hFy
    linarith
  · rw [← hyeq]
    exact tendsto_nhdsWithin_iff.2 ⟨hy, hUS.mono fun w hw =>
      QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht (hS hw)⟩
  · rw [← hyeq]
    exact mem_closure_of_tendsto hy (hUS.mono fun w hw => mem_image_of_mem _ hw)

/-- **The left side of the slit.** Let `η` be a simple proper trace of `W` and `0 < s < t`. If `c` tends to `ℓ` (from
`ℍ`) at every negative real point `x` with `F̄_t(x) = η(s)`, then `c(f_t(z)) → ℓ` as `z → η(s)` from the left side of
`η`: the points approaching `η(s)` from the left of the complete trace are mapped by `g_t − W_t` to points approaching
the left hull-frontier interval `(L_t − W_t, 0)`. -/
theorem tendsto_comp_fwdMap_leftSideOf (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {s : ℝ} (hs : 0 < s) (hst : s < t) {c : ℂ → ℝ} {ℓ : ℝ}
    (hc : ∀ x : ℝ, x < 0 → extendFrom H (fwdMapInv W t) x = η s → Tendsto c (𝓝[H] (x : ℂ)) (𝓝 ℓ)) :
    Tendsto (fun z => c (fwdMap W t z)) (𝓝[leftSideOf (arcRange η)] (η s)) (𝓝 ℓ) := by
  have ht : 0 ≤ t := (hs.trans hst).le
  have hSK : leftSideOf (arcRange η) ⊆ H \ fwdHull W t := fun w hw =>
    ⟨hw.1.1, fun hK => hw.1.2 (fwdHull_subset_arcRange hη hγ ht hK)⟩
  rw [Filter.tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨x, hx0, hFx, hlim, hcl⟩ := exists_real_tendsto_fwdMap hη hγ hW hW0 hs hst hSK U hU
  have hxneg : x < 0 := by
    refine lt_of_le_of_ne (not_lt.1 fun hpos => ?_) hx0
    refine (isProperArc_futureArc hη hγ hW hW0 ht).notMem_closure_leftSideOf_of_pos hpos ?_
    have hsub : fwdMap W t '' leftSideOf (arcRange η) ⊆ leftSideOf (arcRange (futureArc W t)) :=
      image_subset_iff.2 fun w hw => fwdMap_mem_leftSideOf_futureArc hη hγ hW hW0 ht hw
    exact closure_mono hsub hcl
  exact (hc x hxneg hFx).comp hlim

/-- **The right side of the slit** (mirror of `tendsto_comp_fwdMap_leftSideOf`): points approaching `η(s)` from the
right of the complete trace are mapped by `g_t − W_t` to points approaching the right hull-frontier interval. -/
theorem tendsto_comp_fwdMap_rightSideOf (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {s : ℝ} (hs : 0 < s) (hst : s < t) {c : ℂ → ℝ} {ℓ : ℝ}
    (hc : ∀ x : ℝ, 0 < x → extendFrom H (fwdMapInv W t) x = η s → Tendsto c (𝓝[H] (x : ℂ)) (𝓝 ℓ)) :
    Tendsto (fun z => c (fwdMap W t z)) (𝓝[rightSideOf (arcRange η)] (η s)) (𝓝 ℓ) := by
  have ht : 0 ≤ t := (hs.trans hst).le
  have hSK : rightSideOf (arcRange η) ⊆ H \ fwdHull W t := fun w hw =>
    ⟨hw.1.1, fun hK => hw.1.2 (fwdHull_subset_arcRange hη hγ ht hK)⟩
  rw [Filter.tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨x, hx0, hFx, hlim, hcl⟩ := exists_real_tendsto_fwdMap hη hγ hW hW0 hs hst hSK U hU
  have hxpos : 0 < x := by
    refine lt_of_le_of_ne (not_lt.1 fun hneg => ?_) hx0.symm
    refine (isProperArc_futureArc hη hγ hW hW0 ht).notMem_closure_rightSideOf_of_neg hneg ?_
    have hsub : fwdMap W t '' rightSideOf (arcRange η) ⊆ rightSideOf (arcRange (futureArc W t)) :=
      image_subset_iff.2 fun w hw => fwdMap_mem_rightSideOf_futureArc hη hγ hW hW0 ht hw
    exact closure_mono hsub hcl
  exact (hc x hxpos hFx).comp hlim

end Values

end InteractingSLE.WangWu
