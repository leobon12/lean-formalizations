/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftSide

/-!
# Lemma S2, the one-sided lift

Packet PROVE-T14-SB5. **`s2LiftStatement : S2LiftStatement`** (supplement pp. 577–579, `source/spec/p577-624.md`
L19–L49: "The post-`t_L` arc has a continuous injective proper lift in `closure ℍ` under `g_A`, starting from the left
original-real base prime end `g_A(L⁻)` and ending at infinity. It uses the unique prime end selected by its free left
collar at every old-range contact"), deterministic.

Construction. Let `β''(s) = β(t_L + s)` (`postCurve`), `Y` its open left side, `e` the boundary values of the left entry
chart `c` on `(−∞, L)`, and `F = liftFn c e`: `c.fwd` on `ℍ`, `e ∘ re` below the axis. On `Y`, `F` is continuous: the
upper part of `Y` lies in `D_A` (`postCurve_leftSide_free`), the rest is left of `L` (`re_lt_of_mem_leftSide`), where
`c.fwd` has the continuous boundary values `e`. The lift is `γ(s) = lim F` at `β''(s)` along `Y` (`extendFrom`):

* the limit exists (`exists_tendsto_of_cluster`): `F` is bounded near `β''(s)` (`IsLeftEntryChart.exists_norm_fwd_le`:
  "`g_A` fixes infinity"), its cluster values lie in the finite fiber `g⁻¹{β''(s)}` (since `g ∘ F` is the identity on
  the upper part and `re` below), and `Y` is locally connected at `β''(s)` (`leftSide_locallyConnected`, Schoenflies)
  — "two distinct fiber points would separate those germs";
* `γ` is continuous (`continuousOn_extendFrom`), `g ∘ γ = β''`, `γ(0) = 0` (along the lower-left quadrant at `L`,
  `F = e(L − η) → 0`: "the chosen prime end is exactly `g_A(L⁻)`"), injective since `β''` is, and proper since `g` is
  bounded on compact sets.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B (IsProperCurve leftSide rightSide closedRightSide lowerLeft lowerRight)
open InteractingSLE.HalfPlaneSep (IsFreeAt)

namespace InteractingSLE

namespace Theorem14

namespace SB

/-! ### The lift function -/

section LiftFn

/-- The chart read from the left side: `c.fwd` on `ℍ`, the boundary values `e ∘ re` on and below the axis. -/
def liftFn (c : Chart) (e : ℝ → ℝ) (w : ℂ) : ℂ := if 0 < w.im then c.1 w else ((e w.re : ℝ) : ℂ)

variable {A : Set ℂ} {L : ℝ} {c : Chart} {e : ℝ → ℝ}

theorem liftFn_of_pos {w : ℂ} (hw : 0 < w.im) : liftFn c e w = c.1 w := by
  simp only [liftFn, hw, ↓reduceIte]

theorem liftFn_of_nonpos {w : ℂ} (hw : w.im ≤ 0) : liftFn c e w = ((e w.re : ℝ) : ℂ) := by
  simp only [liftFn, not_lt.2 hw, ↓reduceIte]

theorem H_union_im_nonpos : H ∪ {v : ℂ | v.im ≤ 0} = univ := by
  ext v
  exact ⟨fun _ => mem_univ _, fun _ => (lt_or_ge 0 v.im).imp id id⟩

/-- **The lift function is continuous** on `D_A` and left of `L` on and below the axis. -/
theorem continuousAt_liftFn (hD : IsDomainChart (H \ fillH A) c)
    (he : ∀ x < L, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) {w : ℂ}
    (hw : w ∈ H \ fillH A ∨ (w.im ≤ 0 ∧ w.re < L)) : ContinuousAt (liftFn c e) w := by
  rcases hw with hw | ⟨him, hre⟩
  · have hc : ContinuousAt c.1 w :=
      hD.differentiableOn_fwd.continuousOn.continuousAt (hD.isOpen.mem_nhds hw)
    refine hc.congr ?_
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hw.1] with v hv
    exact (liftFn_of_pos hv).symm
  have hb : Tendsto (fun v : ℂ => ((e v.re : ℝ) : ℂ)) (𝓝 w) (𝓝 (e w.re : ℂ)) :=
    (tendsto_boundaryValue he hre).comp (continuous_re.tendsto w)
  rcases lt_or_eq_of_le him with him | him
  · rw [ContinuousAt, liftFn_of_nonpos him.le]
    refine hb.congr' ?_
    filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds him] with v hv
    exact (liftFn_of_nonpos (le_of_lt hv)).symm
  · have hwx : w = ((w.re : ℝ) : ℂ) := Complex.ext rfl (by simp [him])
    have h1 : Tendsto (liftFn c e) (𝓝[H] w) (𝓝 (e w.re : ℂ)) := by
      have := he w.re hre
      rw [← hwx] at this
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact (liftFn_of_pos hv).symm
    have h2 : Tendsto (liftFn c e) (𝓝[{v : ℂ | v.im ≤ 0}] w) (𝓝 (e w.re : ℂ)) :=
      (hb.mono_left nhdsWithin_le_nhds).congr'
        (eventually_nhdsWithin_of_forall fun v hv => (liftFn_of_nonpos hv).symm)
    rw [ContinuousAt, liftFn_of_nonpos him.le, ← nhdsWithin_univ, ← H_union_im_nonpos, nhdsWithin_union]
    exact h1.sup h2

end LiftFn

/-! ### Cluster values in the fiber -/

section ClusterVal

/-- A cluster value of `F` along a filter living on a closed set `S`, where `g` is continuous on `S` and `g ∘ F → z`,
lies in `g⁻¹{z} ∩ S`. -/
theorem mem_fiber_of_mapClusterPt {F g : ℂ → ℂ} {S : Set ℂ} (hS : IsClosed S) (hg : ContinuousOn g S)
    {l : Filter ℂ} (hFS : ∀ᶠ w in l, F w ∈ S) {z y : ℂ} (hgF : Tendsto (g ∘ F) l (𝓝 z))
    (hy : MapClusterPt y l F) : y ∈ g ⁻¹' {z} ∩ S := by
  have hmem : S ∈ map F l := hFS
  have hyS : y ∈ S := hS.closure_eq ▸ ClusterPt.mem_closure_of_mem hy _ hmem
  refine ⟨?_, hyS⟩
  have hne : (𝓝 y ⊓ map F l).NeBot := hy
  have hle : 𝓝 y ⊓ map F l ≤ 𝓝[S] y := le_inf inf_le_left (inf_le_right.trans (le_principal_iff.2 hmem))
  have h1 : Tendsto g (𝓝 y ⊓ map F l) (𝓝 (g y)) := (hg y hyS).tendsto.mono_left hle
  have h2 : Tendsto g (𝓝 y ⊓ map F l) (𝓝 z) := (tendsto_map'_iff.2 hgF).mono_left inf_le_right
  exact tendsto_nhds_unique h1 h2

/-- The vertical projection of the lower half-plane onto `ℝ`, the identity on `ℍ`. -/
def projUp (w : ℂ) : ℂ := if 0 < w.im then w else ((w.re : ℝ) : ℂ)

theorem dist_projUp_le {z : ℂ} (hz : 0 ≤ z.im) (w : ℂ) : dist (projUp w) z ≤ 2 * dist w z := by
  unfold projUp
  split_ifs with h
  · linarith [dist_nonneg (x := w) (y := z)]
  · rw [not_lt] at h
    have h1 : dist ((w.re : ℝ) : ℂ) w = |w.im| := by
      rw [dist_eq_norm, show ((w.re : ℝ) : ℂ) - w = ((-w.im : ℝ) : ℂ) * I by
        apply Complex.ext <;> simp, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_neg]
    have h2 : |w.im| ≤ dist w z := by
      rw [abs_of_nonpos h, dist_comm, dist_eq_norm]
      have := abs_im_le_norm (z - w)
      rw [sub_im] at this
      linarith [le_abs_self (z.im - w.im)]
    linarith [dist_triangle ((w.re : ℝ) : ℂ) w z]

theorem tendsto_projUp {z : ℂ} (hz : 0 ≤ z.im) : Tendsto projUp (𝓝 z) (𝓝 z) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun w => dist_nonneg) (fun w => dist_projUp_le hz w) ?_
  simpa using (((tendsto_id (x := 𝓝 z)).dist (tendsto_const_nhds (x := z))).const_mul (2 : ℝ))

end ClusterVal

/-! ### Lemma S2, the one-sided lift -/

section Main

/-- **Lemma S2, the one-sided lift** (supplement pp. 577–579). -/
theorem s2LiftStatement : S2LiftStatement := by
  intro p β hp hp0 _ hβ hβ0 hA c g hc hgc hgi hgf tL htL
  set A := p '' Icc 0 1 with hAdef
  set L := realMin A with hLdef
  obtain ⟨-, -, hLR, -, -⟩ := realBase_facts hp hp0
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hAconn : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) := by
    have h0A : (0 : ℂ) ∈ A := ⟨0, left_mem_Icc.2 zero_le_one, hp0⟩
    exact IsPreconnected.union 0 h0A (show (0 : ℂ) ∈ {z : ℂ | z.im ≤ 0} by simp)
      (isPreconnected_Icc.image p hp)
      (convex_halfSpace_le (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected
  obtain ⟨C₁, C₂, hC₁, hCb⟩ := hc.exists_norm_fwd_le hAc.isBounded hAconn
  obtain ⟨e, he, he0⟩ := hc.2.1
  have hD := hc.1
  have hfree : ∀ x < L, IsFreeAt A (x : ℂ) := fun x hx => isFreeAt_of_lt hAc (fun y hy => (hLR y hy).1) hx
  set β'' := postCurve β tL with hβ''
  have hβ''p : IsProperCurve β'' := isProperCurve_postCurve hβ
  have hβ''0 : β'' 0 = (L : ℂ) := by rw [hβ'', postCurve_zero, htL]
  have h0'' : (β'' 0).im = 0 := by rw [hβ''0]; simp
  have hre'' : (β'' 0).re = L := by rw [hβ''0]; simp
  set Y := leftSide β'' with hY
  set F := liftFn c e with hF
  have hYsplit : ∀ w ∈ Y, w ∈ H \ fillH A ∨ (w.im ≤ 0 ∧ w.re < L) := fun w hw => by
    by_cases him : 0 < w.im
    · exact Or.inl (postCurve_leftSide_free hp hp0 hβ hβ0 hA htL hw him)
    · rw [not_lt] at him
      exact Or.inr ⟨him, by have := re_lt_of_mem_leftSide hβ''p h0'' hw him; rwa [hre''] at this⟩
  have hFc : ContinuousOn F Y := fun w hw => (continuousAt_liftFn hD he (hYsplit w hw)).continuousWithinAt
  have hFS : ∀ w ∈ Y, F w ∈ {v : ℂ | 0 ≤ v.im} := fun w hw => by
    rcases hYsplit w hw with hwD | ⟨him, -⟩
    · rw [hF, liftFn_of_pos hwD.1]
      exact le_of_lt (show (0 : ℝ) < (c.1 w).im from hD.fwd_mem hwD)
    · rw [hF, liftFn_of_nonpos him]
      simp
  have hgF : ∀ w ∈ Y, g (F w) = projUp w := fun w hw => by
    rcases hYsplit w hw with hwD | ⟨him, hre⟩
    · have h : (0 : ℝ) < w.im := hwD.1
      rw [hF, liftFn_of_pos h, hgi (hD.fwd_mem hwD), hD.inv_fwd hwD]
      simp only [projUp, h, ↓reduceIte]
    · rw [hF, liftFn_of_nonpos him, eq_of_boundaryValue hD hgc hgi (he _ hre) (hfree _ hre)]
      simp only [projUp, not_lt.2 him, ↓reduceIte]
  have hgFlim : ∀ z : ℂ, 0 ≤ z.im → Tendsto (g ∘ F) (𝓝[Y] z) (𝓝 z) := fun z hz =>
    ((tendsto_projUp hz).mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (hgF w hw).symm)
  -- bounds
  have heb : ∀ x < L, |e x| ≤ C₁ * (|x| + 1) + C₂ := by
    intro x hx
    have hne : (𝓝[H] (x : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (mem_closure_H_of_im_nonneg (by simp))
    have hlim := (continuous_norm.tendsto _).comp (he x hx)
    have : ‖((e x : ℝ) : ℂ)‖ ≤ C₁ * (|x| + 1) + C₂ := by
      refine le_of_tendsto hlim ?_
      filter_upwards [eventually_mem_of_isFreeAt (hfree x hx),
        inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) one_pos)] with w hw hwb
      have hwn : ‖w‖ ≤ |x| + 1 := by
        have h1 : dist w (x : ℂ) < 1 := hwb.2
        have h2 := norm_sub_norm_le w (x : ℂ)
        rw [← dist_eq_norm, norm_real, Real.norm_eq_abs] at h2
        linarith
      have := hCb w hw
      simp only [Function.comp_apply]
      nlinarith [hC₁]
    simpa [Real.norm_eq_abs] using this
  have hFb : ∀ w ∈ Y, ‖F w‖ ≤ C₁ * (‖w‖ + 1) + C₂ := by
    intro w hw
    rcases hYsplit w hw with hwD | ⟨him, hre⟩
    · rw [hF, liftFn_of_pos hwD.1]
      have := hCb w hwD
      nlinarith [hC₁]
    · rw [hF, liftFn_of_nonpos him, norm_real, Real.norm_eq_abs]
      have h1 := heb _ hre
      have h2 := abs_re_le_norm w
      nlinarith [hC₁]
  have hcl : ∀ s : ℝ≥0, β'' s ∈ closure Y := fun s =>
    Supp9B.seedRayClosure_subset_closure_leftSide hβ''p h0'' (Or.inl ⟨s, rfl⟩)
  have hlim : ∀ s : ℝ≥0, ∃ y, Tendsto F (𝓝[Y] (β'' s)) (𝓝 y) := by
    intro s
    have hz : β'' s ∈ seedRayClosure β'' := Or.inl ⟨s, rfl⟩
    refine exists_tendsto_of_cluster (hgf (β'' s)) (hcl s) hFc one_pos (M := C₁ * (‖β'' s‖ + 2) + C₂)
      (fun w hw => ?_) (fun y hy => mem_fiber_of_mapClusterPt (isClosed_le continuous_const continuous_im) hgc
        (eventually_nhdsWithin_of_forall hFS) (hgFlim _ (hβ''p.2.2.1 s)) hy)
      (fun ε hε => leftSide_locallyConnected hβ''p h0'' hz hε)
    have hwn : ‖w‖ ≤ ‖β'' s‖ + 1 := by
      have h1 : dist w (β'' s) < 1 := hw.2
      have h2 := norm_sub_norm_le w (β'' s)
      rw [← dist_eq_norm] at h2
      linarith
    have := hFb w hw.1
    nlinarith [hC₁]
  set Gx := extendFrom Y F with hGx
  have hT : ∀ s, Tendsto F (𝓝[Y] (β'' s)) (𝓝 (Gx (β'' s))) := fun s => tendsto_extendFrom (hlim s)
  have hfib : ∀ s, Gx (β'' s) ∈ g ⁻¹' {β'' s} ∩ {w : ℂ | 0 ≤ w.im} := fun s => by
    have hne : (𝓝[Y] (β'' s)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hcl s)
    exact mem_fiber_of_mapClusterPt (isClosed_le continuous_const continuous_im) hgc
      (eventually_nhdsWithin_of_forall hFS) (hgFlim _ (hβ''p.2.2.1 s)) (hT s).mapClusterPt
  have hgG : ∀ s, g (Gx (β'' s)) = β'' s := fun s => (hfib s).1
  have hGc : ContinuousOn Gx (range β'') :=
    continuousOn_extendFrom (fun _ ⟨s, hs⟩ => hs ▸ hcl s) (fun _ ⟨s, hs⟩ => hs ▸ hlim s)
  refine ⟨fun s => Gx (β'' s), ⟨hGc.comp_continuous hβ''p.1 (fun s => ⟨s, rfl⟩), fun s s' h => ?_,
    fun s => (hfib s).2, ?_⟩, ?_, fun s => hgG s⟩
  · refine hβ''p.2.1 ?_
    rw [← hgG s, ← hgG s']
    exact congrArg g h
  · refine tendsto_atTop.2 fun R => ?_
    have hK : IsCompact (closedBall (0 : ℂ) R ∩ {w : ℂ | 0 ≤ w.im}) :=
      (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_im)
    obtain ⟨M, hM⟩ := (hK.image_of_continuousOn (hgc.mono inter_subset_right)).isBounded.exists_norm_le
    filter_upwards [hβ''p.2.2.2.eventually (eventually_gt_atTop M)] with s hs
    by_contra hlt
    rw [not_le] at hlt
    have hmem : Gx (β'' s) ∈ closedBall (0 : ℂ) R ∩ {w : ℂ | 0 ≤ w.im} :=
      ⟨mem_closedBall_zero_iff.2 hlt.le, (hfib s).2⟩
    have := hM _ (mem_image_of_mem g hmem)
    rw [hgG s] at this
    linarith
  · -- the lower-left approach to `L` selects `g_A(L⁻)`
    have hw : Tendsto (fun η : ℝ => ((L - η : ℝ) : ℂ) - (η : ℂ) * I) (𝓝[>] 0) (𝓝[Y] (β'' 0)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · rw [hβ''0]
        have : Tendsto (fun η : ℝ => ((L - η : ℝ) : ℂ) - (η : ℂ) * I) (𝓝 0)
            (𝓝 (((L - 0 : ℝ) : ℂ) - ((0 : ℝ) : ℂ) * I)) := (Continuous.tendsto (by fun_prop) 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with η hη
        have hη' : (0 : ℝ) < η := hη
        refine Supp9B.lowerLeft_subset_leftSide hβ''p.2.2.1 h0'' ⟨?_, ?_⟩
        · simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero, hre'']
          linarith
        · simp only [sub_im, ofReal_im, mul_im, I_re, mul_zero, ofReal_re, I_im, mul_one, zero_sub]
          linarith
    have hval : Tendsto (fun η : ℝ => F (((L - η : ℝ) : ℂ) - (η : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun η : ℝ => L - η) (𝓝[>] 0) (𝓝[<] L) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun η : ℝ => L - η) (𝓝 0) (𝓝 (L - 0)) := (continuous_const.sub continuous_id).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with η hη
          have hη' : (0 : ℝ) < η := hη
          show L - η < L
          linarith
      have h2 := (continuous_ofReal.tendsto 0).comp (he0.comp h1)
      rw [ofReal_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with η hη
      have hη' : (0 : ℝ) < η := hη
      rw [hF, liftFn_of_nonpos (by simp; linarith)]
      simp
    exact tendsto_nhds_unique ((hT 0).comp hw) hval

end Main

end SB

end Theorem14

end InteractingSLE
