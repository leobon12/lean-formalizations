import InteractingSLE.Spec.Sec2.MartingaleFinalGeom
import InteractingSLE.Spec.Sec2.TerminalPath
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.WangWu.Prop418Side
import InteractingSLE.WangWu.CouplingMean
import InteractingSLE.WangWu.MeanIdentLine

/-!
# Wang–Wu at `κ = 4`: the force coordinates are the geometric images; side values on a simple slit

Packet PROVE-WW-B7. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), Definition 1.4
("values `−λ` and `+λ` on the left and right sides of the new trace whenever that trace has been established") and the
specification's "geometric force endpoints" (`source/spec/p001-048.md` L936–L966).

* **Force coordinates are geometric images** (`vR_eq_rightImg`, `vL_eq_neg_rightImg`). For every integrated path
  (frozen `IsIntegratedSLEPath`) with a continuous driver, each force coordinate is the geometric image
  `rightImg` of its force point (`inf {g_t(y) : y > x alive}`; for the left side by reflection). The specification
  proves this by "once `R` and a right force coordinate `V` agree, they remain equal" (L962–L966); the proof here is a
  first-crossing comparison (`le_of_forall_sub_le_sub`) in both directions: `V ≤ g(y)` for every alive `y > x` (the
  Loewner vector field `2/(· − w)` is decreasing above the driver), and `R ≤ V` on every interval where `R > V`,
  where `R` solves the Loewner equation with a positive gap (`rightImg_eq_add_integral`) and `V` solves it off its
  null collision set.
* **The force images lie off the slit interval** (`lt_of_extendFrom_mem_H_left`, `…_right`): if a real point `x < 0`
  is mapped by the boundary extension `F̄_t` of the inverse Loewner map into `ℍ`, then `x` lies strictly to the right of
  every centred left force image. (The real points left of the leftmost image are images of alive real points,
  `extendFrom_eq_of_isForwardSol`, and `F̄_t` is continuous on `ℍ̄`.)
* **Side values of the conditional mean on a simple slit** (`tendsto_meanAt_leftSideOf`, `…_rightSideOf`): for a
  simple proper Loewner trace `η` of the driver and `0 < s < t < ζ`, the mean `η_t` of Definition 1.4 tends to `−λ`
  (resp. `+λ`) at `η(s)` from the left (resp. right) side of the complete trace (B6's slit-side correspondence
  `tendsto_comp_fwdMap_leftSideOf` + the boundary values of Lemma 3.1).
-/

set_option autoImplicit false

universe u

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

open MartChar.RealFlow

/-! ### A first-crossing comparison -/

/-- **First-crossing comparison.** Let `u, v` be continuous on `[0, T]` with `u 0 ≤ v 0`. If on every interval
`[a, b] ⊆ (0, T]` on which `u > v` the increment of `u` is at most that of `v`, then `u ≤ v` on `[0, T]`. -/
theorem le_of_forall_sub_le_sub {u v : ℝ → ℝ} {T : ℝ} (hu : ContinuousOn u (Icc 0 T))
    (hv : ContinuousOn v (Icc 0 T)) (h0 : u 0 ≤ v 0)
    (hstep : ∀ a b, 0 < a → a ≤ b → b ≤ T → (∀ s ∈ Icc a b, v s < u s) → u b - u a ≤ v b - v a)
    {t : ℝ} (ht : t ∈ Icc 0 T) : u t ≤ v t := by
  by_contra hlt
  push Not at hlt
  set g : ℝ → ℝ := fun s => u s - v s with hg
  have hgc : ContinuousOn g (Icc 0 t) := (hu.sub hv).mono (Icc_subset_Icc_right ht.2)
  set A := {s ∈ Icc 0 t | g s ≤ 0} with hA
  have hAc : IsClosed A := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, ht.1⟩, by simp only [hg]; linarith⟩
  have hAb : BddAbove A := ⟨t, fun s hs => hs.1.2⟩
  set t₀ := sSup A with ht₀
  have ht₀A : t₀ ∈ A := hAc.csSup_mem ⟨0, hA0⟩ hAb
  have hgt : 0 < g t := by simp only [hg]; linarith
  have ht₀t : t₀ < t := by
    refine lt_of_le_of_ne ht₀A.1.2 fun h => ?_
    have := ht₀A.2
    rw [h] at this
    linarith
  have hpos : ∀ s ∈ Ioc t₀ t, 0 < g s := fun s hs => by
    by_contra hle
    push Not at hle
    have : s ≤ t₀ := le_csSup hAb ⟨⟨ht₀A.1.1.trans hs.1.le, hs.2⟩, hle⟩
    linarith [hs.1]
  have hle : ∀ a ∈ Ioc t₀ t, g t ≤ g a := fun a ha => by
    have := hstep a t (ht₀A.1.1.trans_lt ha.1) ha.2 ht.2 fun s hs => by
      have := hpos s ⟨ha.1.trans_le hs.1, hs.2⟩
      simp only [hg] at this
      linarith
    simp only [hg]
    linarith
  have hlim : Tendsto g (𝓝[Ioc t₀ t] t₀) (𝓝 (g t₀)) :=
    (hgc t₀ ht₀A.1).mono_left (nhdsWithin_mono _ fun s hs => ⟨ht₀A.1.1.trans hs.1.le, hs.2⟩)
  have : (𝓝[Ioc t₀ t] t₀).NeBot := left_nhdsWithin_Ioc_neBot ht₀t
  have h1 : g t ≤ g t₀ := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle)
  linarith [ht₀A.2]

/-! ### Force coordinates are geometric images -/

section Geometric

variable {w v : ℝ → ℝ} {x T : ℝ}

/-- The increment of a solution of the integrated force equation. -/
theorem sub_eq_integral_of_forceEq (hint : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 T)
    (heq : ∀ s ∈ Icc 0 T, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r - w r)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hbT : b ≤ T) : v b - v a = ∫ r in a..b, 2 / (v r - w r) := by
  have hT : 0 ≤ T := ha.trans (hab.trans hbT)
  have hia : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 a := by
    refine hint.mono_set ?_
    rw [uIcc_of_le ha, uIcc_of_le hT]
    exact Icc_subset_Icc_right (hab.trans hbT)
  have hib : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 b := by
    refine hint.mono_set ?_
    rw [uIcc_of_le (ha.trans hab), uIcc_of_le hT]
    exact Icc_subset_Icc_right hbT
  rw [heq b ⟨ha.trans hab, hbT⟩, heq a ⟨ha, hab.trans hbT⟩,
    ← intervalIntegral.integral_interval_sub_left hib hia]
  ring

/-- **The geometric image is below the force coordinate.** -/
theorem rightImg_le_of_forceEq (hw : Continuous w) (hw0 : w 0 = 0) (hx : 0 ≤ x)
    (hvc : ContinuousOn v (Icc 0 T)) (hwv : ∀ s ∈ Icc 0 T, w s ≤ v s)
    (hint : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 T)
    (heq : ∀ s ∈ Icc 0 T, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r - w r))
    (hnull : volume {s | s ∈ Icc 0 T ∧ w s = v s} = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    rightImg w x t ≤ v t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hRc : ContinuousOn (rightImg w x) (Icc 0 T) := (continuousOn_rightImg hw x).mono fun s hs => hs.1
  have hv0 : v 0 = x := by rw [heq 0 ⟨le_rfl, hT⟩, intervalIntegral.integral_same, add_zero]
  refine le_of_forall_sub_le_sub hRc hvc (by rw [rightImg_zero hw hw0 hx, hv0]) ?_ ht
  intro a b ha hab hbT hlt
  -- a positive gap of `R` on `[a, b]`
  have hgc : ContinuousOn (fun s => rightImg w x s - w s) (Icc a b) :=
    (hRc.mono (Icc_subset_Icc ha.le hbT)).sub hw.continuousOn
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hab) hgc
  have hgap0 : 0 < rightImg w x s₀ - w s₀ := by
    have := hlt s₀ hs₀
    have := hwv s₀ ⟨ha.le.trans hs₀.1, hs₀.2.trans hbT⟩
    linarith
  have hgap : ∀ u ∈ Icc a b, (rightImg w x s₀ - w s₀) / 2 < rightImg w x u - w u := fun u hu => by
    have := hmin hu
    simp only [mem_ofPred_eq] at this
    linarith
  have hR := rightImg_eq_add_integral hw ha hab (by linarith) hgap ⟨hab, le_rfl⟩
  rw [hR, sub_eq_integral_of_forceEq hint heq ha.le hab hbT, add_sub_cancel_left]
  -- compare the integrands off the collision set
  have hRi : IntervalIntegrable (fun s => 2 / (rightImg w x s - w s)) volume a b := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hab]
    exact continuousOn_const.div hgc fun u hu => by have := hgap u hu; linarith
  have hvi : IntervalIntegrable (fun s => 2 / (v s - w s)) volume a b :=
    hint.mono_set (by rw [uIcc_of_le hab, uIcc_of_le hT]; exact Icc_subset_Icc ha.le hbT)
  refine intervalIntegral.integral_mono_ae_restrict hab hRi hvi ?_
  have hn : ∀ᵐ s ∂volume, s ∉ {s | s ∈ Icc 0 T ∧ w s = v s} := measure_eq_zero_iff_ae_notMem.1 hnull
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  filter_upwards [hn] with s hs hsab
  have hsT : s ∈ Icc 0 T := ⟨ha.le.trans hsab.1, hsab.2.trans hbT⟩
  have hne : w s ≠ v s := fun h => hs ⟨hsT, h⟩
  have hpos : 0 < v s - w s := sub_pos.2 (lt_of_le_of_ne (hwv s hsT) hne)
  have hlt' := hlt s hsab
  exact div_le_div_of_nonneg_left zero_le_two hpos (by linarith)

/-- **The force coordinate is below every alive image** `g_t(y)`, `y > x`. -/
theorem le_gImg_of_forceEq (hw : Continuous w) (hvc : ContinuousOn v (Icc 0 T))
    (hint : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 T)
    (heq : ∀ s ∈ Icc 0 T, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r - w r)) {y t : ℝ} (hxy : x < y)
    (ht : t ∈ Icc 0 T) (hy : Alive w y t) : v t ≤ gImg w y t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hv0 : v 0 = x := by rw [heq 0 ⟨le_rfl, hT⟩, intervalIntegral.integral_same, add_zero]
  have hgc : ContinuousOn (gImg w y) (Icc 0 t) :=
    hw.continuousOn.add (hy.isPosSol hw).1
  have heq' : ∀ s ∈ Icc 0 t, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r - w r) :=
    fun s hs => heq s ⟨hs.1, hs.2.trans ht.2⟩
  have hint' : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 t :=
    hint.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2)
  refine le_of_forall_sub_le_sub (hvc.mono (Icc_subset_Icc_right ht.2)) hgc ?_ ?_ ⟨ht.1, le_rfl⟩
  · rw [hv0, gImg_zero hw (hy.mono ht.1)]
    exact hxy.le
  intro a b ha hab hbt hlt
  rw [sub_eq_integral_of_forceEq hint' heq' ha.le hab hbt, hy.gImg_eq hw ⟨ha.le.trans hab, hbt⟩,
    hy.gImg_eq hw ⟨ha.le, hab.trans hbt⟩, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left]
  · refine intervalIntegral.integral_mono_on hab ?_ ?_ fun s hs => ?_
    · exact hint'.mono_set (by rw [uIcc_of_le hab, uIcc_of_le ht.1]; exact Icc_subset_Icc ha.le hbt)
    · exact ((hy.continuousOn_inv hw).mono (Icc_subset_Icc ha.le hbt)).intervalIntegrable_of_Icc hab
    · have hst : s ∈ Icc 0 t := ⟨ha.le.trans hs.1, hs.2.trans hbt⟩
      have hc := hy.cflow_pos hw hst
      have hl := hlt s hs
      have hg : gImg w y s = w s + cflow w y s := rfl
      exact div_le_div_of_nonneg_left zero_le_two hc (by linarith)
  · exact ((hy.continuousOn_inv hw).mono (Icc_subset_Icc_right hbt)).intervalIntegrable_of_Icc
      (ha.le.trans hab)
  · exact ((hy.continuousOn_inv hw).mono (Icc_subset_Icc_right (hab.trans hbt))).intervalIntegrable_of_Icc
      ha.le

/-- **Force coordinates are geometric images** (deterministic form): a continuous solution `v ≥ w` of the integrated
force equation from `x ≥ 0`, with integrable reciprocal gap and null collision set, is the geometric image
`rightImg w x` on `[0, T]`. -/
theorem eq_rightImg_of_forceEq (hw : Continuous w) (hw0 : w 0 = 0) (hx : 0 ≤ x)
    (hvc : ContinuousOn v (Icc 0 T)) (hwv : ∀ s ∈ Icc 0 T, w s ≤ v s)
    (hint : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 T)
    (heq : ∀ s ∈ Icc 0 T, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r - w r))
    (hnull : volume {s | s ∈ Icc 0 T ∧ w s = v s} = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    v t = rightImg w x t :=
  le_antisymm (le_csInf (imgSet_nonempty hw x ht.1) fun _ ⟨_y, hxy, hy, hg⟩ =>
    hg ▸ le_gImg_of_forceEq hw hvc hint heq hxy ht hy)
    (rightImg_le_of_forceEq hw hw0 hx hvc hwv hint heq hnull ht)

end Geometric

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The right force coordinates of an integrated path are the geometric images** (specification L936–L966): for a
continuous driver, `v^{i,R}_t = inf {g_t(y) : y > x^{i,R} alive at t}` for every `t < ζ`. -/
theorem vR_eq_rightImg (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hw : Continuous w)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) : vR i t = rightImg (Ito.rpath w) (xR i) t := by
  obtain ⟨hw0, -, hvR0, -, -, hvRc, -, -, hwvR, -, -, hgapR, -, -, hvReq, -, hnullR, -, -, -⟩ := hp
  have hrw : Continuous (Ito.rpath w) := hw.comp continuous_real_toNNReal
  have hζ0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ := lt_of_le_of_lt (by simp) ht
  have hx : 0 ≤ xR i := by
    have := hwvR 0 hζ0 i
    rwa [hw0, hvR0] at this
  have hlt : ∀ s ∈ Icc (0 : ℝ) t, (s.toNNReal : ℝ≥0∞) < ζ := fun s hs =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) ht
  have e : (fun s : ℝ => 2 / (vR i s.toNNReal - Ito.rpath w s)) =
      fun s => (-2) * (w s.toNNReal - vR i s.toNNReal)⁻¹ := by
    funext s
    rw [Ito.rpath, div_eq_mul_inv, ← neg_sub, inv_neg]
    ring
  have hnull : volume {s | s ∈ Icc (0 : ℝ) t ∧ Ito.rpath w s = vR i s.toNNReal} = 0 :=
    measure_mono_null (fun s (hs : s ∈ Icc (0 : ℝ) t ∧ Ito.rpath w s = vR i s.toNNReal) =>
      (⟨hs.1.1, hlt s hs.1, hs.2⟩ : 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR i s.toNNReal))
      (hnullR i)
  have key := eq_rightImg_of_forceEq (v := fun s : ℝ => vR i s.toNNReal) (T := t) hrw
    (by simp [Ito.rpath, hw0]) hx
    ((hvRc i).comp continuous_real_toNNReal.continuousOn fun s hs => hlt s hs)
    (fun s hs => hwvR _ (hlt s hs) i) (by rw [e]; exact (hgapR t ht i).const_mul (-2))
    (fun s hs => by
      have := hvReq s.toNNReal (hlt s hs) i
      rwa [Real.coe_toNNReal _ hs.1] at this)
    hnull ⟨t.coe_nonneg, le_rfl⟩
  simpa using key

/-- **The left force coordinates are the geometric images** (by reflection):
`v^{i,L}_t = −inf {g^{−w}_t(y) : y > −x^{i,L} alive}`. -/
theorem vL_eq_neg_rightImg (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hw : Continuous w)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) :
    vL i t = -rightImg (fun s => -Ito.rpath w s) (-xL i) t := by
  have h := vR_eq_rightImg hp.reflect hw.neg ht i
  have e : Ito.rpath (-w) = fun s => -Ito.rpath w s := rfl
  rw [e] at h
  simp only [Pi.neg_apply] at h
  linarith

end Path

/-! ### Real starting points of the Loewner flow -/

section RealStart

variable {W : ℝ → ℝ}

/-- An alive real point `y` (right side) gives a solution of QuantumZipper's centred flow from `y`. -/
theorem isForwardSol_of_alive (hW : Continuous W) {y t : ℝ} (hy : Alive W y t) :
    QuantumZipper.IsForwardSol W (y : ℂ) t (fun s => (cflow W y s : ℂ)) := by
  obtain ⟨hc, hX⟩ := hy.isPosSol hW
  refine ⟨Complex.continuous_ofReal.comp_continuousOn hc, fun s hs => ⟨?_, ?_⟩⟩
  · exact Complex.ofReal_ne_zero.2 (hX s hs).1.ne'
  · have e : (fun r : ℝ => (2 : ℂ) / (cflow W y r : ℂ)) = fun r => ((2 / cflow W y r : ℝ) : ℂ) := by
      funext r; push_cast; rfl
    show (cflow W y s : ℂ) = _
    rw [e, intervalIntegral.integral_ofReal, (hX s hs).2]
    push_cast
    ring

/-- A left real point `−y`, with `y` alive for the reflected driver `−W`, gives a solution of the centred flow from
`−y`. -/
theorem isForwardSol_neg_of_alive (hW : Continuous W) {y t : ℝ} (hy : Alive (fun s => -W s) y t) :
    QuantumZipper.IsForwardSol W (-(y : ℂ)) t (fun s => -(cflow (fun s => -W s) y s : ℂ)) := by
  obtain ⟨hc, hX⟩ := Alive.isPosSol (w := fun s => -W s) hW.neg hy
  refine ⟨(Complex.continuous_ofReal.comp_continuousOn hc).neg, fun s hs => ⟨?_, ?_⟩⟩
  · exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 (hX s hs).1.ne')
  · have e : (fun r : ℝ => (2 : ℂ) / -(cflow (fun s => -W s) y r : ℂ)) =
        fun r => ((-(2 / cflow (fun s => -W s) y r) : ℝ) : ℂ) := by
      funext r; push_cast; rw [div_neg]
    show -(cflow (fun s => -W s) y s : ℂ) = _
    rw [e, intervalIntegral.integral_ofReal, intervalIntegral.integral_neg, (hX s hs).2]
    push_cast
    ring

end RealStart

/-! ### The force images lie off the slit interval -/

section Slit

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The boundary extension at a starting point of the flow**: if `u` solves the centred flow from `p ∈ ℍ̄` on
`[0, t]`, then `F̄_t(u_t) = p`. -/
theorem extendFrom_eq_of_isForwardSol (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {p : ℂ} (hp : p ∈ Hbar) {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W p t u) :
    extendFrom H (fwdMapInv W t) (u t) = p := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol ht hu
  set E := Real.exp (2 / δ ^ 2 * t) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hev : ∀ᶠ z in 𝓝[H] p, z ∈ H \ fwdHull W t := by
    have hball : ∀ᶠ z in 𝓝[H] p, z ∈ Metric.ball p (δ / E) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds p (by positivity))
    filter_upwards [hball, self_mem_nhdsWithin] with z hz hzH
    refine ⟨hzH, not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzH ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc ‖z - p‖ * E < δ / E * E := mul_lt_mul_of_pos_right hz hE0
      _ = δ := div_mul_cancel₀ δ hE0.ne'
  have hlim : Tendsto (fwdMap W t) (𝓝[H] p) (𝓝 (u t)) := tendsto_fwdMap_of_isForwardSol hW ht hu
  have hNe : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (closure_H ▸ hp)
  have hmaps : ∀ᶠ z in 𝓝[H] p, fwdMap W t z ∈ H :=
    hev.mono fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz
  have hutH : u t ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hlim hmaps
  have hlim' : Tendsto (fwdMap W t) (𝓝[H] p) (𝓝[Hbar] (u t)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, hmaps.mono fun z hz => le_of_lt (show (0 : ℝ) < (fwdMap W t z).im from hz)⟩
  have hF : Tendsto (extendFrom H (fwdMapInv W t)) (𝓝[Hbar] (u t))
      (𝓝 (extendFrom H (fwdMapInv W t) (u t))) :=
    (hη.hasBdryLimits hW hW0 ht).continuousOn (u t) hutH
  have h2 : Tendsto (fun z => extendFrom H (fwdMapInv W t) (fwdMap W t z)) (𝓝[H] p) (𝓝 p) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
      (hev.mono fun z hz => (extendFrom_fwdMap hW hW0 ht hz).symm)
  exact tendsto_nhds_unique (hF.comp hlim') h2

/-- If real points `x_n → x` are mapped by `F̄_t` to real points, so is `x`. -/
theorem im_extendFrom_eq_zero_of_tendsto (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {x : ℝ} {xn : ℕ → ℝ} (hxn : Tendsto xn atTop (𝓝 x))
    (him : ∀ n, (extendFrom H (fwdMapInv W t) (xn n)).im = 0) :
    (extendFrom H (fwdMapInv W t) x).im = 0 := by
  have hxH : ((x : ℂ)) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have hF : Tendsto (extendFrom H (fwdMapInv W t)) (𝓝[Hbar] (x : ℂ))
      (𝓝 (extendFrom H (fwdMapInv W t) x)) :=
    (hη.hasBdryLimits hW hW0 ht).continuousOn _ hxH
  have hc : Tendsto (fun n => ((xn n : ℝ) : ℂ)) atTop (𝓝[Hbar] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto x).comp hxn,
      Eventually.of_forall fun n => show (0 : ℝ) ≤ ((xn n : ℝ) : ℂ).im by simp⟩
  have h := (Complex.continuous_im.tendsto _).comp (hF.comp hc)
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr fun n => (him n).symm)

/-- **Left real points mapped into `ℍ` lie right of the leftmost geometric image**: if `F̄_t(x) ∈ ℍ` for a real
`x`, then `x > L_t − W_t`, where `L_t = −inf {g^{−W}_t(y) : y > 0 alive}` is the image of `0⁻`. (Real points
`x ≤ L_t − W_t` are limits of images of alive real points, which `F̄_t` maps back to the real line.) -/
theorem neg_rightImg_sub_lt_of_extendFrom_mem_H (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hFx : extendFrom H (fwdMapInv W t) x ∈ H) :
    -rightImg (fun s => -W s) 0 t - W t < x := by
  by_contra hle
  push Not at hle
  have hM : rightImg (fun s => -W s) 0 t ≤ -x - W t := by linarith
  have hseq : ∀ n : ℕ, ∃ y, 0 < y ∧ Alive (fun s => -W s) y t ∧ -x - W t < gImg (fun s => -W s) y t ∧
      gImg (fun s => -W s) y t < -x - W t + 1 / ((n : ℝ) + 1) :=
    fun n => exists_alive_gImg_mem hW.neg ht (by positivity) hM
  choose y hy0 hya hyM hyM' using hseq
  set xn : ℕ → ℝ := fun n => -(gImg (fun s => -W s) (y n) t + W t) with hxn
  have hcf : ∀ n, cflow (fun s => -W s) (y n) t = gImg (fun s => -W s) (y n) t + W t := fun n => by
    simp only [gImg]
    ring
  have him : ∀ n, (extendFrom H (fwdMapInv W t) (xn n)).im = 0 := fun n => by
    have h := extendFrom_eq_of_isForwardSol hη hW hW0 ht
      (show (0 : ℝ) ≤ (-(y n : ℂ)).im by simp) (isForwardSol_neg_of_alive hW (hya n))
    have e : -(cflow (fun s => -W s) (y n) t : ℂ) = ((xn n : ℝ) : ℂ) := by
      rw [hcf n, hxn]
      push_cast
      ring
    rw [e] at h
    rw [h]
    simp
  have hlim : Tendsto xn atTop (𝓝 x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n : ℕ => x - 1 / ((n : ℝ) + 1))
      (h := fun _ => x) ?_ tendsto_const_nhds (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hyM' n
      simp only [hxn]
      linarith
    · have := hyM n
      simp only [hxn]
      linarith
  have := im_extendFrom_eq_zero_of_tendsto hη hW hW0 ht hlim him
  have hpos : (0 : ℝ) < (extendFrom H (fwdMapInv W t) x).im := hFx
  linarith

/-- **Right real points mapped into `ℍ` lie left of the rightmost geometric image**: if `F̄_t(x) ∈ ℍ` for a real
`x`, then `x < R_t − W_t`, `R_t = inf {g_t(y) : y > 0 alive}` (the image of `0⁺`). -/
theorem lt_rightImg_sub_of_extendFrom_mem_H (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {x : ℝ} (hFx : extendFrom H (fwdMapInv W t) x ∈ H) :
    x < rightImg W 0 t - W t := by
  by_contra hle
  push Not at hle
  have hM : rightImg W 0 t ≤ x + W t := by linarith
  have hseq : ∀ n : ℕ, ∃ y, 0 < y ∧ Alive W y t ∧ x + W t < gImg W y t ∧
      gImg W y t < x + W t + 1 / ((n : ℝ) + 1) :=
    fun n => exists_alive_gImg_mem hW ht (by positivity) hM
  choose y hy0 hya hyM hyM' using hseq
  set xn : ℕ → ℝ := fun n => gImg W (y n) t - W t with hxn
  have him : ∀ n, (extendFrom H (fwdMapInv W t) (xn n)).im = 0 := fun n => by
    have h := extendFrom_eq_of_isForwardSol hη hW hW0 ht
      (show (0 : ℝ) ≤ ((y n : ℂ)).im by simp) (isForwardSol_of_alive hW (hya n))
    have e : (cflow W (y n) t : ℂ) = ((xn n : ℝ) : ℂ) := by
      rw [hxn]
      simp only [gImg]
      push_cast
      ring
    rw [e] at h
    rw [h]
    simp
  have hlim : Tendsto xn atTop (𝓝 x) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => x)
      (h := fun n : ℕ => x + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_ (fun n => ?_) (fun n => ?_)
    · simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · have := hyM n
      simp only [hxn]
      linarith
    · have := hyM' n
      simp only [hxn]
      linarith
  have := im_extendFrom_eq_zero_of_tendsto hη hW hW0 ht hlim him
  have hpos : (0 : ℝ) < (extendFrom H (fwdMapInv W t) x).im := hFx
  linarith

end Slit

/-! ### Side values of the conditional mean on a simple slit -/

section SideValues

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ → ℂ}

theorem continuous_rpath (hw : Continuous w) : Continuous (Ito.rpath w) := hw.comp continuous_real_toNNReal

theorem rpath_zero (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) : Ito.rpath w 0 = 0 := by
  simp [Ito.rpath, hp.1]

/-- **The centred left force images lie strictly left of the slit interval**: every real `x` that `F̄_t` maps into `ℍ`
satisfies `v^{i,L}_t − w_t < x`. -/
theorem vL_sub_lt_of_extendFrom_mem_H (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hw : Continuous w) (hη : IsLoewnerTrace (Ito.rpath w) η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {x : ℝ}
    (hFx : extendFrom H (fwdMapInv (Ito.rpath w) t) x ∈ H) (i : Fin nL) : vL i t - w t < x := by
  have hk := neg_rightImg_sub_lt_of_extendFrom_mem_H hη (continuous_rpath hw) (rpath_zero hp) t.coe_nonneg hFx
  have hxL : xL i ≤ 0 := by
    obtain ⟨hw0, hvL0, -, -, -, -, -, hvLw, -⟩ := id hp
    have := hvLw 0 (lt_of_le_of_lt (by simp) ht) i
    rwa [hvL0, hw0] at this
  have hmono : rightImg (fun s => -Ito.rpath w s) 0 t ≤ rightImg (fun s => -Ito.rpath w s) (-xL i) t :=
    rightImg_mono_index (continuous_rpath hw).neg t.coe_nonneg (neg_nonneg.2 hxL)
  rw [vL_eq_neg_rightImg hp hw ht i]
  have : Ito.rpath w t = w t := Ito.rpath_coe w t
  linarith

/-- **The centred right force images lie strictly right of the slit interval.** -/
theorem lt_vR_sub_of_extendFrom_mem_H (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hw : Continuous w) (hη : IsLoewnerTrace (Ito.rpath w) η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {x : ℝ}
    (hFx : extendFrom H (fwdMapInv (Ito.rpath w) t) x ∈ H) (i : Fin nR) : x < vR i t - w t := by
  have hk := lt_rightImg_sub_of_extendFrom_mem_H hη (continuous_rpath hw) (rpath_zero hp) t.coe_nonneg hFx
  have hxR : 0 ≤ xR i := by
    obtain ⟨hw0, -, hvR0, -, -, -, -, -, hwvR, -⟩ := id hp
    have := hwvR 0 (lt_of_le_of_lt (by simp) ht) i
    rwa [hvR0, hw0] at this
  have hmono := rightImg_mono_index (continuous_rpath hw) t.coe_nonneg hxR
  rw [vR_eq_rightImg hp hw ht i]
  have : Ito.rpath w t = w t := Ito.rpath_coe w t
  linarith

/-- **Left-side value `−λ` of the mean on a simple slit** (Definition 1.4, "values `−λ` and `+λ` on the left and
right sides of the new trace"): for a simple proper Loewner trace `η` of the driver and `0 < s < t < ζ`,
`η_t(z) → −λ` as `z → η(s)` from the left side of the complete trace. -/
theorem tendsto_meanAt_leftSideOf (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) (hw : Continuous w)
    (hη : IsLoewnerTrace (Ito.rpath w) η) (hγ : IsProperArc η) {s : ℝ} {t : ℝ≥0} (hs : 0 < s)
    (hst : s < t) (ht : (t : ℝ≥0∞) < ζ) :
    Tendsto (meanAt ρL ρR w vL vR t) (𝓝[leftSideOf (arcRange η)] (η s)) (𝓝 (-wwLambda)) := by
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -⟩ := id hp
  have hvL : ∀ i, vL i t - w t ≤ 0 := fun i => sub_nonpos.2 (hvLw t ht i)
  have hvR : ∀ i, 0 ≤ vR i t - w t := fun i => sub_nonneg.2 (hwvR t ht i)
  refine tendsto_comp_fwdMap_leftSideOf hη hγ (continuous_rpath hw) (rpath_zero hp) hs hst
    (c := condMean ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t)) fun x hx hFx => ?_
  have hFxH : extendFrom H (fwdMapInv (Ito.rpath w) t) x ∈ H := hFx ▸ hγ.mem_H s hs
  have hlt : ∀ i, vL i t - w t < x := vL_sub_lt_of_extendFrom_mem_H hp hw hη ht hFxH
  have hxS : x ∉ forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hx.ne h0
    · exact (hlt i).ne hi
    · linarith [hvR i]
  have h := tendsto_condMean_left (ρL := ρL) (ρR := ρR) hvL hvR hx hxS
  rwa [Finset.filter_false_of_mem fun i _ => not_lt.2 (hlt i).le, Finset.sum_empty, add_zero,
    mul_one] at h

/-- **Right-side value `+λ` of the mean on a simple slit.** -/
theorem tendsto_meanAt_rightSideOf (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) (hw : Continuous w)
    (hη : IsLoewnerTrace (Ito.rpath w) η) (hγ : IsProperArc η) {s : ℝ} {t : ℝ≥0} (hs : 0 < s)
    (hst : s < t) (ht : (t : ℝ≥0∞) < ζ) :
    Tendsto (meanAt ρL ρR w vL vR t) (𝓝[rightSideOf (arcRange η)] (η s)) (𝓝 wwLambda) := by
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -⟩ := id hp
  have hvL : ∀ i, vL i t - w t ≤ 0 := fun i => sub_nonpos.2 (hvLw t ht i)
  have hvR : ∀ i, 0 ≤ vR i t - w t := fun i => sub_nonneg.2 (hwvR t ht i)
  refine tendsto_comp_fwdMap_rightSideOf hη hγ (continuous_rpath hw) (rpath_zero hp) hs hst
    (c := condMean ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t)) fun x hx hFx => ?_
  have hFxH : extendFrom H (fwdMapInv (Ito.rpath w) t) x ∈ H := hFx ▸ hγ.mem_H s hs
  have hlt : ∀ i, x < vR i t - w t := lt_vR_sub_of_extendFrom_mem_H hp hw hη ht hFxH
  have hxS : x ∉ forceJumpSet (fun i => vL i t - w t) (fun i => vR i t - w t) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hx.ne' h0
    · linarith [hvL i]
    · exact (hlt i).ne' hi
  have h := tendsto_condMean_right (ρL := ρL) (ρR := ρR) hvL hvR hx.le hxS
  rwa [Finset.filter_false_of_mem fun i _ => not_le.2 (hlt i), Finset.sum_empty, add_zero,
    mul_one] at h

/-- `η_t = condMean ∘ f_t` is harmonic off the hull. -/
theorem harmonicOnNhd_meanAt (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) (hw : Continuous w)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    InnerProductSpace.HarmonicOnNhd (meanAt ρL ρR w vL vR t) (H \ fwdHull (Ito.rpath w) t) := by
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -⟩ := id hp
  have hc := (isBoundedHarmonicExtension_condMean ρL ρR (vL := fun i => vL i t - w t)
    (vR := fun i => vR i t - w t) (fun i => sub_nonpos.2 (hvLw t ht i))
    (fun i => sub_nonneg.2 (hwvR t ht i))).1
  have hO := QuantumZipper.FwdHolo.isOpen_compl_fwdHull (continuous_rpath hw) t.coe_nonneg
  have hd := QuantumZipper.FwdHolo.differentiableOn_fwdMap (continuous_rpath hw) t.coe_nonneg
  intro z hz
  exact QuantumZipper.FieldLawler.fl_harmonicAt_comp (hd.analyticAt (hO.mem_nhds hz))
    (hc _ (QuantumZipper.FwdHolo.mapsTo_fwdMap (continuous_rpath hw) t.coe_nonneg hz))

/-- For a simple proper trace, the complement of the prefix `η([0, t])` in `ℍ` is the complement of the hull. -/
theorem H_diff_arcPrefix_eq (hη : IsLoewnerTrace (Ito.rpath w) η) (hγ : IsProperArc η) (t : ℝ≥0) :
    H \ arcPrefix η t = H \ fwdHull (Ito.rpath w) t := by
  rw [fwdHull_eq_image_Ioc hη hγ t.coe_nonneg]
  ext z
  refine ⟨fun hz => ⟨hz.1, fun h => hz.2 (image_mono Ioc_subset_Icc_self h)⟩, fun hz => ⟨hz.1, ?_⟩⟩
  rintro ⟨s, hs, rfl⟩
  rcases hs.1.eq_or_lt with h0 | hpos
  · have h1 := hz.1
    rw [← h0, hγ.zero] at h1
    exact (lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h1))
  · exact hz.2 ⟨s, ⟨hpos, hs.2⟩, rfl⟩

/-- **The per-sample prefix input of `ae_hasLeftSideLimit_of_prefix` / `ae_hasRightSideLimit_of_prefix`.** If a
distribution `g` (the local-set mean of the prefix `η([0, t])`) is represented off the prefix by the mean `η_t` of
Definition 1.4, then it has a harmonic representative off the prefix with value `−λ` from the left and `+λ` from the
right of the complete trace at every `η(s)`, `0 < s < t`. -/
theorem exists_rep_tendsto_sides_prefix (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ)
    (hw : Continuous w) (hη : IsLoewnerTrace (Ito.rpath w) η) (hγ : IsProperArc η) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) {g : LQGMetric.DistOn upperHalfPlaneOpens}
    (hg : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix η t →
      g φ = ∫ z, meanAt ρL ρR w vL vR t z * φ z) :
    ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix η t) ∧
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix η t → g φ = ∫ z, v z * φ z) ∧
      (∀ s : ℝ, 0 < s → s < t →
        Tendsto v (𝓝[leftSideOf (arcRange η)] (η s)) (𝓝 (-wwLambda))) ∧
      ∀ s : ℝ, 0 < s → s < t → Tendsto v (𝓝[rightSideOf (arcRange η)] (η s)) (𝓝 wwLambda) := by
  refine ⟨meanAt ρL ρR w vL vR t, ?_, hg, fun s hs hst => tendsto_meanAt_leftSideOf hp hw hη hγ hs hst ht,
    fun s hs hst => tendsto_meanAt_rightSideOf hp hw hη hγ hs hst ht⟩
  rw [H_diff_arcPrefix_eq hη hγ t]
  exact harmonicOnNhd_meanAt hp hw ht

/-- Off the hull the frozen mean is the mean `η_t`. -/
theorem frozenMean_eq_meanAt {t : ℝ≥0} {z : ℂ} (hz : z ∈ H \ fwdHull (Ito.rpath w) t) :
    frozenMean ρL ρR w vL vR t z = meanAt ρL ρR w vL vR t z := by
  have hlt : (t : ℝ≥0∞) < QuantumZipper.swallowTime (Ito.rpath w) z := by
    by_contra hle
    push Not at hle
    refine hz.2 ⟨hz.1, ?_⟩
    rwa [ENNReal.ofReal_coe_nnreal]
  rw [frozenMean, ite_eq_left hlt]

end SideValues

/-! ### Side values of a complete seed line from mean-represented prefixes -/

section Probabilistic

open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF AEDeterminedSigma)
open InteractingSLE.LocalSets (IsLocalSetMean)

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The per-sample prefix representative with a harmonic offset `m₀` (the field `h` seen by a coupling `F = h + m₀`):
`η_t − m₀` has the side values `−λ − m₀` and `λ − m₀` on the slit. -/
theorem exists_rep_tendsto_sides_prefix_sub {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ₀ : ℝ≥0∞} {η : ℝ → ℂ}
    (hp : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ₀) (hw : Continuous w)
    (hη : IsLoewnerTrace (Ito.rpath w) η) (hγ : IsProperArc η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ₀)
    {m₀ : ℂ → ℝ} (hm₀ : InnerProductSpace.HarmonicOnNhd m₀ H) {g : DistOn upperHalfPlaneOpens}
    (hg : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix η t →
      g φ = ∫ z, (meanAt ρL ρR w vL vR t z - m₀ z) * φ z) :
    ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix η t) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix η t → g φ = ∫ z, v z * φ z) ∧
      (∀ s : ℝ, 0 < s → s < t →
        Tendsto v (𝓝[leftSideOf (arcRange η)] (η s)) (𝓝 (-wwLambda - m₀ (η s)))) ∧
      ∀ s : ℝ, 0 < s → s < t →
        Tendsto v (𝓝[rightSideOf (arcRange η)] (η s)) (𝓝 (wwLambda - m₀ (η s))) := by
  have hm₀c : ∀ s : ℝ, 0 < s → Tendsto m₀ (𝓝 (η s)) (𝓝 (m₀ (η s))) := fun s hs =>
    (hm₀ _ (hγ.mem_H s hs)).1.continuousAt
  refine ⟨fun z => meanAt ρL ρR w vL vR t z - m₀ z, ?_, hg, fun s hs hst => ?_, fun s hs hst => ?_⟩
  · rw [H_diff_arcPrefix_eq hη hγ t]
    exact (harmonicOnNhd_meanAt hp hw ht).sub fun z hz => hm₀ z hz.1
  · exact (tendsto_meanAt_leftSideOf hp hw hη hγ hs hst ht).sub ((hm₀c s hs).mono_left nhdsWithin_le_nhds)
  · exact (tendsto_meanAt_rightSideOf hp hw hη hγ hs hst ht).sub ((hm₀c s hs).mono_left nhdsWithin_le_nhds)

/-- **Left- and right-side values of a complete seed line from mean-represented prefixes.** Let `γ` be a random simple
proper arc which is almost surely the Loewner trace of the driver of an integrated `SLE₄(ρ)` path with infinite
lifetime, and whose range and prefixes `γ([0, n + 1])` are field-determined local sets of the zero-boundary GFF `h`.
If almost surely every prefix mean is represented off the prefix by `η_{n+1} − m₀` (the mean of Definition 1.4 minus a
harmonic offset `m₀`, e.g. the bounded harmonic extension of the boundary data of the coupled field `F = h + m₀`),
then the complete mean has the side values `−λ − m₀` on the left and `λ − m₀` on the right of `γ`
(`HasLeftSideLimit`, `HasRightSideLimit`: the inputs of Lemma 4.21 and Proposition 4.20). The representation `hrep`
is the stopped-prefix locality with mean `frozenMean` (PROVE-WW-B5/B6 obstruction 1(b)). -/
theorem ae_hasSideLimits_of_prefix_meanAt (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {γ : Ω → ℝ → ℂ}
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath 4 xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun i t => VR i t ω) (fun t => B t ω) (ζ ω))
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (hWc : ∀ᵐ ω ∂P, Continuous fun t => W t ω)
    (htr : ∀ᵐ ω ∂P, IsLoewnerTrace (Ito.rpath fun t => W t ω) (γ ω))
    (harc : ∀ᵐ ω ∂P, IsProperArc (γ ω))
    (hm : Measurable[mΩ, hittingSigma] fun ω => arcRange (γ ω))
    (hdet : AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P)
    (hloc : IsLocalSet (fun ω => arcRange (γ ω)) h P)
    (hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (γ ω) (n + 1))
    (hploc : ∀ n : ℕ, IsLocalSet (fun ω => arcPrefix (γ ω) (n + 1)) h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean (fun ω => arcRange (γ ω)) h P g)
    {gp : ℕ → Ω → DistOn upperHalfPlaneOpens}
    (hgp : ∀ n : ℕ, IsLocalSetMean (fun ω => arcPrefix (γ ω) (n + 1)) h P (gp n))
    {m₀ : ℂ → ℝ} (hm₀ : InnerProductSpace.HarmonicOnNhd m₀ H)
    (hrep : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ H \ arcPrefix (γ ω) (n + 1) →
        gp n ω φ = ∫ z, (meanAt ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun i t => VR i t ω)
          ((n : ℝ≥0) + 1) z - m₀ z) * φ z) :
    (∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (γ ω) fun z => -wwLambda - m₀ z) ∧
      ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (γ ω) fun z => wwLambda - m₀ z := by
  have hpre : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ arcPrefix (γ ω) (n + 1)) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ arcPrefix (γ ω) (n + 1) →
        gp n ω φ = ∫ z, v z * φ z) ∧
      (∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[leftSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (-wwLambda - m₀ (γ ω s)))) ∧
      ∀ s : ℝ, 0 < s → s < (n : ℝ) + 1 →
        Tendsto v (𝓝[rightSideOf (arcRange (γ ω))] (γ ω s)) (𝓝 (wwLambda - m₀ (γ ω s))) := by
    filter_upwards [hpath, hζ, hWc, htr, harc, hrep] with ω hp hz hw hη hγ hr n
    have ht : (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hz]; exact ENNReal.coe_lt_top
    have hcast : (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
    have h1 := exists_rep_tendsto_sides_prefix_sub hp hw hη hγ ht hm₀ (g := gp n ω)
      (fun φ hφ => by rw [hcast] at *; exact hr n φ hφ)
    rw [hcast] at h1
    exact h1
  refine ⟨ae_hasLeftSideLimit_of_prefix hh harc hm hdet hloc hpm hploc hg hgp ?_,
    ae_hasRightSideLimit_of_prefix hh harc hm hdet hloc hpm hploc hg hgp ?_⟩
  · filter_upwards [hpre] with ω hω n
    obtain ⟨v, h1, h2, h3, -⟩ := hω n
    exact ⟨v, h1, h2, h3⟩
  · filter_upwards [hpre] with ω hω n
    obtain ⟨v, h1, h2, -, h4⟩ := hω n
    exact ⟨v, h1, h2, h4⟩

end Probabilistic

end WangWu

end InteractingSLE
