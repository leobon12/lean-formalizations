/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux57
import InteractingSLE.Spec.Supplement.R1RefFreshTip
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.WangWu.Prop418Side
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.YuanCorollary13Finite
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# The chart of a simple trace stopped before its lifetime

Packet PROVE-LEMMA76B (the chart facts behind Aux. lemmas 69–70, specification pp. 273–275). For a simple frozen
generating trace `η` (`IsGeneratingTrace w T η`, `w` continuous before `T`, `w 0 = 0`) and a stop `0 < q < T`, the
centred mapping-out function `f = f_q` of `K = fill η([0, q])` and the continuous extension `Φ = F̄_q` of its inverse
to `ℍ̄` satisfy the facts collected in `IsChart`: `f` is a bijection `ℍ \ K → ℍ` at bounded distance from the identity
with inverse `Φ`, every approach to a point of `ℍ̄` along an ultrafilter has a limit of `f` that `Φ` maps back to the
point, `Φ(0)` is the tip, the tip has the single preimage `0` when it is interior (fresh-tip uniqueness, Lemma 1.1 of
the singleton-tip elimination note, `IsLoewnerTrace.eq_zero_of_extendFrom_eq_of_isCutTime`), real boundary values in
`ℍ` are trace points, and at a free real point `x` the chart has a real value `c` with `Φ` mapping `(c − δ, c)` to
real points left of `x` (the Schwarz reflection of Aux. lemma 57, increasing on the real line).

The frozen trace is continued to a global Loewner trace after a time in `(q, T)` (`IsGeneratingTrace.isLoewnerTraceLT`,
`IsLoewnerTraceLT.isLoewnerTrace_ext`), whose maps at time `q` are those of `w`.

## Main results

* `ReverseArc.exists_global_model`: the global continuation;
* `ReverseArc.IsChart`, **`ReverseArc.isChart`**: the chart facts.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE

namespace Sec7

namespace ReverseArc

/-! ### The global continuation -/

/-- **A frozen generating trace before `T`, continued**: a continuous driver `W` with `W 0 = 0` and a global Loewner
trace `γ` of `W` agreeing with the frozen data on `[0, T']`, for some `T' > q`. -/
theorem exists_global_model {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < T) :
    ∃ (W : ℝ → ℝ) (γ : ℝ → ℂ) (T' : ℝ), (q : ℝ) < T' ∧ Continuous W ∧ W 0 = 0 ∧ IsLoewnerTrace W γ ∧
      (∀ r ∈ Icc (0 : ℝ) T', W r = w r.toNNReal) ∧ ∀ r ∈ Icc (0 : ℝ) T', γ r = η r.toNNReal := by
  obtain ⟨t₂, hqt₂, ht₂T⟩ := exists_real_btwn_of_lt hq
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  set T' : ℝ := ((q : ℝ) + t₂) / 2 with hT'def
  have hqT' : (q : ℝ) < T' := by rw [hT'def]; linarith
  have hT't₂ : T' < t₂ := by rw [hT'def]; linarith
  have hT'0 : 0 ≤ T' := (NNReal.coe_nonneg q).trans hqT'.le
  have hW₀c : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hw ht₂T
  have hW₀0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂, hw0]
  have hL := (hη.isLoewnerTraceLT ht₂T).isLoewnerTrace_ext hW₀c hW₀0 hT'0 hT't₂
  refine ⟨YuanCorollary13.extDrive (frozenDrive w t₂) T', YuanCorollary13.extTrace (frozenDrive w t₂)
    (fun s : ℝ => η s.toNNReal) T', T', hqT', YuanCorollary13.continuous_extDrive hW₀c,
    YuanCorollary13.extDrive_zero hW₀0 hT'0, hL, fun r hr => ?_, fun r hr => ?_⟩
  · rw [YuanCorollary13.extDrive_eq hr.2, frozenDrive_eq ⟨hr.1, hr.2.trans hT't₂.le⟩]
  · rw [YuanCorollary13.extTrace_eq hr.2]

/-! ### Planar helpers -/

/-- A point of the filling of a closed set that is adherent to the unbounded domain lies on the set. -/
theorem mem_of_mem_fillH_of_mem_closure {S : Set ℂ} (hS : IsClosed S) {z : ℂ} (hz : z ∈ fillH S)
    (hc : z ∈ closure (H \ fillH S)) : z ∈ S := by
  obtain ⟨hzH, hz'⟩ := hz
  rw [hS.closure_eq] at hz'
  rcases hz' with h | h
  · exact h
  by_contra hzS
  have hO : IsOpen (H \ S) := QuantumZipper.isOpen_H.sdiff hS
  have hCo : IsOpen (connectedComponentIn (H \ S) z) := hO.connectedComponentIn
  have hzC : z ∈ connectedComponentIn (H \ S) z := mem_connectedComponentIn ⟨hzH, hzS⟩
  obtain ⟨w, hwC, hw⟩ := mem_closure_iff.1 hc _ hCo hzC
  apply hw.2
  refine ⟨hw.1, Or.inr ?_⟩
  rw [hS.closure_eq, ← connectedComponentIn_eq hwC]
  exact h

/-! ### The chart -/

/-- **The chart facts** of a simple trace `η` from `0` stopped at `q`, for the centred map `f` and the continuous
extension `Φ` of its inverse. -/
structure IsChart (η : ℝ≥0 → ℂ) (q : ℝ≥0) (f Φ : ℂ → ℂ) : Prop where
  maps : MapsTo f (H \ fillH (η '' Icc 0 q)) H
  injOn : InjOn f (H \ fillH (η '' Icc 0 q))
  cont : ContinuousOn f (H \ fillH (η '' Icc 0 q))
  bdd : ∃ C : ℝ, ∀ z ∈ H \ fillH (η '' Icc 0 q), ‖f z - z‖ ≤ C
  inv_cont : ContinuousOn Φ Hbar
  inv_mem : MapsTo Φ H (H \ fillH (η '' Icc 0 q))
  f_inv : ∀ w ∈ H, f (Φ w) = w
  inv_f : ∀ z ∈ H \ fillH (η '' Icc 0 q), Φ (f z) = z
  cluster : ∀ (U : Ultrafilter ℂ) (p : ℂ), (U : Filter ℂ) ≤ 𝓝[H \ fillH (η '' Icc 0 q)] p →
    ∃ y ∈ Hbar, Tendsto f U (𝓝 y) ∧ Φ y = p
  tip : Φ 0 = η q
  tip_fibre : η q ∈ H → ∀ y : ℝ, Φ y = η q → y = 0
  bdry : ∀ y : ℝ, Φ y ∈ H → Φ y ∈ η '' Icc 0 q
  free_real : ∀ x : ℝ, HalfPlaneSep.IsFreeAt (η '' Icc 0 q) x → ∃ c : ℝ,
    Tendsto f (𝓝[H] (x : ℂ)) (𝓝 (c : ℂ)) ∧ Φ c = x ∧ ∃ δ > 0, ∀ y ∈ Ioo (c - δ) c, ∃ x' : ℝ, x' < x ∧ Φ y = x'

/-- **Free real points in the chart.** If `g = f + κ` maps out the hull `K` and `Φ` is a continuous extension to `ℍ̄`
of the inverse of `f`, then at a real point `x` whose half-ball avoids `K` the chart has a real value `c`, `Φ(c) = x`,
and `Φ` maps `(c − δ, c)` to real points left of `x` (the Schwarz reflection of `g` at `x` is increasing on `ℝ`). -/
theorem free_real_of_isMapOut {K : Set ℂ} (hK : IsHPHull K) {f Φ : ℂ → ℂ} {κ : ℝ}
    (hg : IsMapOut K fun z => f z + κ) (hΦc : ContinuousOn Φ Hbar) (hinv : ∀ z ∈ H \ K, Φ (f z) = z)
    {x : ℝ} {ε : ℝ} (hε : 0 < ε) (hfree : ball (x : ℂ) ε ∩ H ⊆ H \ K) :
    ∃ c : ℝ, Tendsto f (𝓝[H] (x : ℂ)) (𝓝 (c : ℂ)) ∧ Φ c = x ∧
      ∃ δ > 0, ∀ y ∈ Ioo (c - δ) c, ∃ x' : ℝ, x' < x ∧ Φ y = x' := by
  set g : ℂ → ℂ := fun z => f z + κ with hgdef
  have hd : Disjoint (ball (x : ℂ) ε) K := Set.disjoint_left.2 fun z hzb hzK =>
    (hfree ⟨hzb, hK.1 hzK⟩).2 hzK
  obtain ⟨G, hG⟩ := exists_isBdryReflection hK hg hε hd
  set r := ε / 2 with hr
  have hr0 : 0 < r := hG.pos
  have hGc : ContinuousOn G (ball (x : ℂ) r) := hG.diff.continuousOn
  -- the real values of the reflection
  set h : ℝ → ℝ := fun t => (G t).re - κ with hh
  have hGreal : ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → G t = (((G t).re : ℝ) : ℂ) := fun t ht =>
    Complex.ext (by simp) (by simp [hG.real_of_im _ ht (by simp)])
  -- at every real point of the ball: the limit of `f` and the inverse
  have hlim : ∀ t : ℝ, (t : ℂ) ∈ ball (x : ℂ) r → Tendsto f (𝓝[H] (t : ℂ)) (𝓝 (h t : ℂ)) ∧ Φ (h t) = t := by
    intro t ht
    have hball : ball (x : ℂ) r ∈ 𝓝 (t : ℂ) := isOpen_ball.mem_nhds ht
    have hGt : Tendsto G (𝓝[H] (t : ℂ)) (𝓝 (G t)) :=
      ((hGc _ ht).continuousAt hball).tendsto.mono_left nhdsWithin_le_nhds
    have heq : f =ᶠ[𝓝[H] (t : ℂ)] fun z => G z - κ := by
      filter_upwards [inter_mem_nhdsWithin H hball] with z hz
      rw [hG.eqOn ⟨hz.2, hz.1⟩]
      simp [hgdef]
    have hft : Tendsto f (𝓝[H] (t : ℂ)) (𝓝 (h t : ℂ)) := by
      refine (Tendsto.congr' heq.symm ?_)
      have := hGt.sub_const (κ : ℂ)
      convert this using 2
      rw [hh, hGreal t ht]
      push_cast
      simp
    refine ⟨hft, ?_⟩
    have hneb : (𝓝[H] (t : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    have hsub : ∀ z ∈ ball (x : ℂ) r ∩ H, z ∈ H \ K := fun z hz =>
      hfree ⟨ball_subset_ball (by rw [hr]; linarith) hz.1, hz.2⟩
    have hfH : Tendsto f (𝓝[H] (t : ℂ)) (𝓝[Hbar] (h t : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hft, ?_⟩
      filter_upwards [inter_mem_nhdsWithin H hball] with z hz
      have h1 := hg.1.2.mapsTo (hsub z ⟨hz.2, hz.1⟩)
      have h2 : (0 : ℝ) < (f z + κ).im := h1
      show 0 ≤ (f z).im
      simp only [add_im, ofReal_im, add_zero] at h2
      exact h2.le
    have hΦt : Tendsto (fun z => Φ (f z)) (𝓝[H] (t : ℂ)) (𝓝 (Φ (h t))) :=
      ((hΦc _ (by show (0 : ℝ) ≤ ((h t : ℝ) : ℂ).im; simp)).tendsto).comp hfH
    have hid : Tendsto (fun z => Φ (f z)) (𝓝[H] (t : ℂ)) (𝓝 (t : ℂ)) := by
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [inter_mem_nhdsWithin H hball] with z hz
      exact (hinv z (hsub z ⟨hz.2, hz.1⟩)).symm
    exact tendsto_nhds_unique hΦt hid
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr0
  refine ⟨h x, (hlim x hxB).1, (hlim x hxB).2, ?_⟩
  -- the reflection is increasing on the real diameter
  set a : ℝ := x - r / 2 with ha
  set b : ℝ := x + r / 2 with hb
  have hIcc : ∀ t ∈ Icc a b, (t : ℂ) ∈ ball (x : ℂ) r := by
    intro t ht
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hhc : ContinuousOn h (Icc a b) := by
    refine ((continuous_re.comp_continuousOn (hGc.comp continuous_ofReal.continuousOn
      fun t ht => hIcc t ht)).sub continuousOn_const)
  have hhi : InjOn h (Icc a b) := by
    intro t ht t' ht' htt'
    have h1 : G t = G t' := by
      rw [hGreal t (hIcc t ht), hGreal t' (hIcc t' ht')]
      have : (G t).re = (G t').re := by simpa [hh] using htt'
      rw [this]
    exact_mod_cast hG.injOn hg (hIcc t ht) (hIcc t' ht') h1
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hmono : StrictMonoOn h (Icc a b) := by
    rcases hhc.strictMonoOn_of_injOn_Icc' hab hhi with hm | hanti
    · exact hm
    exfalso
    obtain ⟨hdim, hdre⟩ := hG.deriv_im_eq_zero_and_re_pos hg
    have hGd : HasDerivAt G (deriv G x) (x : ℂ) :=
      (hG.diff.differentiableAt (isOpen_ball.mem_nhds hxB)).hasDerivAt
    have hd : HasDerivAt h (deriv G x).re x := by
      have h2 := hGd.real_of_complex.sub_const κ
      simpa [hh] using h2
    have hslope := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
      (nhdsWithin_mono _ (fun t (ht : t ∈ Ioi x) => ne_of_gt ht))
    have hneg : ∀ᶠ t in 𝓝[>] x, slope h x t < 0 := by
      have hxb : x < b := by rw [hb]; linarith
      filter_upwards [Ioo_mem_nhdsGT hxb] with t ht
      have hxI : x ∈ Icc a b := ⟨by rw [ha]; linarith, hxb.le⟩
      have htI : t ∈ Icc a b := ⟨by rw [ha]; linarith [ht.1], ht.2.le⟩
      have := hanti hxI htI ht.1
      rw [slope_def_field]
      exact div_neg_of_neg_of_pos (by linarith) (by linarith [ht.1])
    have := le_of_tendsto hslope (hneg.mono fun t ht => ht.le)
    linarith
  have hax : a < x := by rw [ha]; linarith
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hxI : x ∈ Icc a b := ⟨hax.le, by rw [hb]; linarith⟩
  refine ⟨h x - h a, sub_pos.2 (hmono haI hxI hax), fun y hy => ?_⟩
  have hy' : y ∈ Icc (h a) (h x) := ⟨by linarith [hy.1], hy.2.le⟩
  obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hax.le (hhc.mono (Icc_subset_Icc_right hxI.2)) hy'
  have htx : t ≠ x := fun h' => by
    rw [h'] at hty
    exact lt_irrefl (h x) (calc h x = y := hty
      _ < h x := hy.2)
  refine ⟨t, lt_of_le_of_ne ht.2 htx, ?_⟩
  rw [← hty]
  exact (hlim t (hIcc t ⟨ht.1, ht.2.trans hxI.2⟩)).2

/-- **The chart facts for a simple frozen generating trace** stopped at `0 < q < T`. -/
theorem isChart {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ T})
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < T) (hq0 : 0 < q) :
    IsChart η q (fwdMap (fun r : ℝ => w r.toNNReal) q) (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q)) := by
  obtain ⟨W, γ, T', hqT', hWc, hW0, hγ, hWeq, hγeq⟩ := exists_global_model hη hw hw0 hq
  have hq0' : (0 : ℝ) ≤ q := NNReal.coe_nonneg q
  have hf : fwdMap (fun r : ℝ => w r.toNNReal) q = fwdMap W q := funext fun z =>
    fwdMap_eq_of_eqOn hq0' fun r hr => (hWeq r ⟨hr.1, hr.2.trans hqT'.le⟩).symm
  have hΦ : fwdMapInv (fun r : ℝ => w r.toNNReal) q = fwdMapInv W q :=
    fwdMapInv_eq_of_eqOn hq0' hqT' fun r hr => (hWeq r hr).symm
  have himg : γ '' Icc 0 (q : ℝ) = η '' Icc 0 q := by
    rw [image_congr (fun r hr => hγeq r ⟨hr.1, hr.2.trans hqT'.le⟩), image_toNNReal_Icc η hq0',
      Real.toNNReal_coe]
  have hK : fwdHull W q = fillH (η '' Icc 0 q) := by rw [hγ.2.2 q hq0', himg]
  have hγq : γ q = η q := by rw [hγeq q ⟨hq0', hqT'.le⟩, Real.toNNReal_coe]
  have hηc : IsCompact (η '' Icc 0 q) := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hq.le)
  rw [hf, hΦ]
  have hKh : IsHPHull (fwdHull W q) := isHPHull_fwdHull hWc hq0'
  have hgm := isMapOut_fwdMap hWc hW0 hq0'
  have hΦc : ContinuousOn (extendFrom H (fwdMapInv W q)) Hbar := (hγ.hasBdryLimits hWc hW0 hq0').continuousOn
  have hinvf : ∀ z ∈ H \ fwdHull W q, extendFrom H (fwdMapInv W q) (fwdMap W q z) = z := fun z hz => by
    rw [ZhanGT4.extendFrom_eq_fwdMapInv hWc hW0 hq0' (QuantumZipper.FwdHolo.mapsTo_fwdMap hWc hq0' hz)]
    exact QuantumZipper.RS.fwdMapInv_fwdMap hWc hW0 hq0' hz
  refine ⟨?_, ?_, ?_, ?_, hΦc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hK]; exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWc hq0'
  · rw [← hK]; exact QuantumZipper.FwdHolo.injOn_fwdMap hWc hq0'
  · rw [← hK]; exact (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWc hq0').continuousOn
  · rw [← hK]
    obtain ⟨M, hM⟩ := hgm.exists_norm_sub_le hKh
    refine ⟨M + |W q|, fun z hz => ?_⟩
    have h1 := hM z hz
    have h2 : fwdMap W q z - z = (fwdMap W q z + (W q : ℂ) - z) - (W q : ℂ) := by ring
    rw [h2]
    refine (norm_sub_le _ _).trans (add_le_add h1 ?_)
    rw [norm_real, Real.norm_eq_abs]
  · intro w hw
    rw [← hK, ZhanGT4.extendFrom_eq_fwdMapInv hWc hW0 hq0' hw]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWc hW0 hq0' hw
  · intro w hw
    rw [ZhanGT4.extendFrom_eq_fwdMapInv hWc hW0 hq0' hw]
    exact QuantumZipper.RS.fwdMap_fwdMapInv hWc hW0 hq0' hw
  · rw [← hK]; exact hinvf
  · intro U p hU
    rw [← hK] at hU
    exact WangWu.exists_tendsto_fwdMap_ultrafilter hγ hWc hW0 hq0' subset_rfl U hU
  · have := ZhanGT4.extendFrom_zero_eq hγ hWc hW0 hq0'
    rw [hγq] at this
    exact this
  · intro hqH y hy
    have hcut : YuanSimpleApprox.IsCutTime γ q := by
      refine ⟨hγq ▸ hqH, ?_⟩
      rintro ⟨t, ht, hte⟩
      rw [hγeq t ⟨ht.1, ht.2.le.trans hqT'.le⟩, hγq] at hte
      have h1 := hinj (show ((t.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T from
          (ENNReal.coe_le_coe.2 (Real.toNNReal_le_toNNReal ht.2.le)).trans
            (by rw [Real.toNNReal_coe]; exact hq.le)) (show (q : ℝ≥0∞) ≤ T from hq.le) hte
      have h2 : t = q := by
        have := congrArg (fun r : ℝ≥0 => (r : ℝ)) h1
        simpa [Real.coe_toNNReal _ ht.1] using this
      exact absurd h2 (ne_of_lt ht.2)
    exact hγ.eq_zero_of_extendFrom_eq_of_isCutTime hWc hW0 hq0 hcut (hy.trans hγq.symm)
  · intro y hy
    obtain ⟨h1, h2⟩ := ZhanGT4.extendFrom_mem_fwdHull hγ hWc hW0 hq0' hy
    rw [hK] at h1 h2
    exact mem_of_mem_fillH_of_mem_closure hηc.isClosed h1 h2
  · intro x hx
    obtain ⟨ε, hε, hsub⟩ := hx
    rw [← hK] at hsub
    exact free_real_of_isMapOut hKh hgm hΦc hinvf hε hsub

end ReverseArc

end Sec7

end InteractingSLE
