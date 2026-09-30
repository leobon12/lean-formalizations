import QuantumZipper.Proofs.Zipper.SWCoreB7cMov
import QuantumZipper.Proofs.Zipper.SWCoreB7cFibre
import QuantumZipper.Proofs.Zipper.SWCoreB7cInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7c (5): the fixed-path anchored convergence on one time box

Decision D70, fixed-path side of AC-fam. For a **fixed** continuous driver `W`, an anchor
`0 < q ≤ T`, a window `[u,v]` live at `q` and `s₀ ∈ [q,T]`, there is `ε > 0` such that for every
free field `Y`, almost surely, for every continuous `f` supported in `[u₂,v₂] ⊂ (u,v)`, the
transported test integrals

  `∫ awTest (F_s) u v f d(bdryApprox γ (coordChange (𝔥₀ + Y) ψ_s Q) k)`,
  `F_s = realRevMap (vrev W T) (T − s)`, `ψ_s = flowFam W q ![s, W s] = revMapExt (vrev W s) (s − q)`,

converge uniformly in `s ∈ [q,T]`, `|s − s₀| ≤ ε` (`flow_box_conv`). Ingredients: the flow box
(`flow_local_class_sep`), the weighted transport with parameter-dependent test functions
(`ae_transport_family_h0rev_mov`), joint continuity of the moving test functions
(`continuousOn_awTest`, `continuousOn_realRevMap_joint`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open B2 RegUnif

/-- A uniform modulus in the parameter from joint continuity and a common compact support. -/
theorem unif_mod_of_continuousOn {S : Set ℝ} (hS : IsCompact S) {G : ℝ → ℝ → ℝ}
    (hG : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (S ×ˢ univ)) {α β : ℝ}
    (hGz : ∀ s ∈ S, ∀ x ∉ Icc α β, G s x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S, |s - s'| ≤ δ →
      ∀ x, |G s x - G s' x| ≤ ε := by
  intro ε hε
  have hUC := (hS.prod (isCompact_Icc (a := α) (b := β))).uniformContinuousOn_of_continuous
    (hG.mono (prod_mono subset_rfl (subset_univ _)))
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
  refine ⟨δ / 2, by linarith, fun s hs s' hs' hss' x => ?_⟩
  by_cases hx : x ∈ Icc α β
  · have hd : dist (s, x) (s', x) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg _)]
      linarith
    have := hδc (s, x) ⟨hs, hx⟩ (s', x) ⟨hs', hx⟩ hd
    rw [Real.dist_eq] at this
    exact this.le
  · rw [hGz s hs x hx, hGz s' hs' x hx, sub_zero, abs_zero]; exact hε.le

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
/-- **Fixed-path anchored convergence on one time box.** -/
theorem flow_box_conv {W : ℝ → ℝ} (hW : Continuous W) {T q : ℝ} (hq0 : 0 < q) (hqT : q ≤ T)
    {u v u' v' u₂ v₂ : ℝ} (huu' : u < u') (hu'v' : u' < v') (hv'v : v' < v)
    (hu₂ : u' < u₂) (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v')
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc q T) (κ : ℝ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Y : Ω → FieldSample, IsFreeGFFModConstH Y P →
      ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ, Continuous f → tsupport f ⊆ Icc u₂ v₂ →
        ∃ Λ : ℝ → ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ s ∈ Icc q T, |s - s₀| ≤ ε →
          |∫ x, awTest (realRevMap (vrev W T) (T - s)) u v f x ∂bdryApprox γ
              (coordChange (ofFun (h0rev κ) + Y ω) (flowFam W q ![s, W s]) (Qc γ)) k -
            Λ s| ≤ η := by
  obtain ⟨a, b, ρ, M, ε, L, c, hab, hρ, hε, hL, hc, hcl, hwin, hlip, hsep⟩ :=
    flow_local_class_sep hW hq0 hqT huu' hu'v' hv'v hLive hs₀
  -- shrink the time range so that `(s, W s)` stays in the box
  obtain ⟨δW, hδW, hδWc⟩ := Metric.continuous_iff.1 hW s₀ ε hε
  set ε' : ℝ := min ε (δW / 2) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by linarith)
  refine ⟨ε', hε'0, fun Y hY => ?_⟩
  -- the box
  set lo : Fin 2 → ℝ := ![max q (s₀ - ε), W s₀ - ε] with hlo
  set hi : Fin 2 → ℝ := ![min T (s₀ + ε), W s₀ + ε] with hhi
  set K : Set (Fin 2 → ℝ) := Icc lo hi with hK
  have hmemK : ∀ p : Fin 2 → ℝ, p ∈ K ↔ (p 0 ∈ Icc q T ∧ |p 0 - s₀| ≤ ε) ∧
      |p 1 - W s₀| ≤ ε := by
    intro p
    simp only [hK, mem_Icc, Pi.le_def, Fin.forall_fin_two, hlo, hhi, Matrix.cons_val_zero,
      Matrix.cons_val_one, max_le_iff, le_min_iff, abs_le]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩
      exact ⟨⟨⟨h1, h4⟩, by linarith, by linarith⟩, by linarith, by linarith⟩
    · rintro ⟨⟨⟨h1, h4⟩, h2, h5⟩, h3, h6⟩
      exact ⟨⟨⟨h1, by linarith⟩, by linarith⟩, ⟨h4, by linarith⟩, by linarith⟩
  have hs₀K : (![s₀, W s₀] : Fin 2 → ℝ) ∈ K := by
    rw [hmemK]; simp [hs₀, hε.le]
  have hlohi : lo ≤ hi := hs₀K.1.trans hs₀K.2
  have hΨ : ∀ p ∈ K, flowFam W q p ∈ BdryClass a b ρ M 1 := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hmemK p).1 hp
    rw [fin2_eta p]; exact hcl _ h1 h2 _ h3
  have hlip2 : ∀ p ∈ K, ∀ p' ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b),
      ‖flowFam W q p z - flowFam W q p' z‖ ≤ (2 * L) * ‖p - p'‖ := by
    intro p hp p' hp' z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hmemK p).1 hp
    obtain ⟨⟨h1', h2'⟩, h3'⟩ := (hmemK p').1 hp'
    have k := hlip _ h1 h2 _ h3 _ h1' h2' _ h3' z hz
    rw [← fin2_eta p, ← fin2_eta p'] at k
    refine k.trans ?_
    have e0 := abs_coord_le_norm p p' 0
    have e1 := abs_coord_le_norm p p' 1
    nlinarith
  have hsep' : ∀ p ∈ K, ∀ z ∈ thickening (ρ : ℝ) (segC a b), c ≤ ‖flowFam W q p z‖ := by
    intro p hp z hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := (hmemK p).1 hp
    rw [fin2_eta p]; exact hsep _ h1 h2 _ h3 z hz
  have hmain := ae_transport_family_h0rev_mov (P := P) κ hY hγ hγ2 (flowFam W q) K hab hρ
    (by norm_num : (0 : ℝ) < ((1 : ℚ) : ℝ)) (by positivity : (0 : ℝ) ≤ 2 * L)
    (by simpa using hΨ) hlip2 (lipschitzWith_boxClamp lo hi) (boxClamp_mem hlohi)
    (fun p hp => boxClamp_of_mem hp) (by positivity : (0 : ℝ) ≤ ‖lo‖ + ‖hi‖)
    (fun p hp => norm_le_of_mem_box hp) isCompact_Icc hc hsep'
  -- the carrier and the moving test functions
  set V := vrev W T with hVdef
  have hV : Continuous V := continuous_vrev hW T
  set S : Set ℝ := Icc (max q (s₀ - ε)) (min T (s₀ + ε)) with hS
  have hSmem : ∀ s ∈ S, s ∈ Icc q T ∧ |s - s₀| ≤ ε := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    rw [max_le_iff] at h1; rw [le_min_iff] at h2
    exact ⟨⟨h1.1, h2.1⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  have hSmem' : ∀ s ∈ Icc q T, |s - s₀| ≤ ε → s ∈ S := by
    intro s hs hss
    obtain ⟨h1, h2⟩ := abs_le.1 hss
    exact ⟨max_le hs.1 (by linarith), le_min hs.2 (by linarith)⟩
  have hσ : ∀ s ∈ S, T - s ∈ Icc (0 : ℝ) (T - q) := fun s hs =>
    ⟨by linarith [(hSmem s hs).1.2], by linarith [(hSmem s hs).1.1]⟩
  set F : ℝ → ℝ → ℝ := fun s y => realRevMap V (T - s) y with hF
  have hFc : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ Icc u v) := by
    have hj := continuousOn_realRevMap_joint hV (by linarith : (0 : ℝ) ≤ T - q) hLive
    refine hj.comp (f := fun p : ℝ × ℝ => (T - p.1, p.2))
      ((continuous_const.sub continuous_fst).prodMk continuous_snd).continuousOn ?_
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    exact ⟨hσ s hs, hy⟩
  have hFm : ∀ s ∈ S, StrictMonoOn (F s) (Icc u v) := fun s hs =>
    b7bf_strictMonoOn hV hLive (hσ s hs)
  have hScpt : IsCompact S := isCompact_Icc
  have hSne : S.Nonempty := ⟨s₀, hSmem' s₀ hs₀ (by rw [sub_self, abs_zero]; exact hε.le)⟩
  -- uniform margins inside `(a,b)`
  have hFsc : ∀ y ∈ Icc u v, ContinuousOn (fun s => F s y) S := fun y hy =>
    hFc.comp (f := fun s : ℝ => (s, y)) (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, hy⟩)
  have hu₂I : u₂ ∈ Icc u v := ⟨by linarith, by linarith⟩
  have hv₂I : v₂ ∈ Icc u v := ⟨by linarith, by linarith⟩
  have hu'I : u' ∈ Icc u v := ⟨huu'.le, by linarith⟩
  have hv'I : v' ∈ Icc u v := ⟨by linarith, hv'v.le⟩
  obtain ⟨s1, hs1, hmin⟩ := hScpt.exists_isMinOn hSne (hFsc u₂ hu₂I)
  obtain ⟨s2, hs2, hmax⟩ := hScpt.exists_isMaxOn hSne (hFsc v₂ hv₂I)
  set α := F s1 u₂ with hα
  set β := F s2 v₂ with hβ
  have hαa : (a : ℝ) < α := by
    have h1 := (hwin s1 (hSmem s1 hs1).1 (hSmem s1 hs1).2 u' ⟨le_rfl, hu'v'.le⟩).1
    have h2 := hFm s1 hs1 hu'I hu₂I hu₂
    exact lt_trans h1 h2
  have hβb : β < (b : ℝ) := by
    have h1 := (hwin s2 (hSmem s2 hs2).1 (hSmem s2 hs2).2 v' ⟨hu'v'.le, le_rfl⟩).2
    have h2 := hFm s2 hs2 hv₂I hv'I hv₂
    exact lt_trans h2 h1
  have hT0 : Icc α β ⊆ Ioo (a : ℝ) b := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  filter_upwards [hmain] with ω hω f hf hfs
  set G : ℝ → ℝ → ℝ := fun s x => awTest (F s) u v f x with hG
  have hGc : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (S ×ˢ univ) :=
    continuousOn_awTest (lt_trans huu' hu₂) hu₂v₂ (lt_trans hv₂ hv'v) hFc hFm hf hfs
  have hGz : ∀ s ∈ S, ∀ x ∉ Icc α β, G s x = 0 := by
    intro s hs x hx
    refine awTest_eq_zero_of_not_mem (hFm s hs) hfs (by linarith) (by linarith) ?_
    by_contra h
    push_neg at h
    exact hx ⟨le_trans (hmin hs) h.1, le_trans h.2 (hmax hs)⟩
  -- the parameter family of test functions
  set fam : (Fin 2 → ℝ) → ℝ → ℝ := fun p => G (max (max q (s₀ - ε)) (min (min T (s₀ + ε)) (p 0)))
    with hfam
  have hclS : ∀ p : Fin 2 → ℝ, max (max q (s₀ - ε)) (min (min T (s₀ + ε)) (p 0)) ∈ S :=
    fun p => ⟨le_max_left _ _, max_le (hSne.mono subset_rfl |>.elim fun s hs =>
      le_trans hs.1 hs.2) (min_le_left _ _)⟩
  have hclK : ∀ p ∈ K, max (max q (s₀ - ε)) (min (min T (s₀ + ε)) (p 0)) = p 0 := by
    intro p hp
    have h := hSmem' (p 0) ((hmemK p).1 hp).1.1 ((hmemK p).1 hp).1.2
    rw [min_eq_right h.2, max_eq_right h.1]
  have hsl : ∀ s ∈ S, Continuous (G s) := fun s hs =>
    continuousOn_univ.1 (hGc.comp (f := fun y : ℝ => (s, y))
      (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨hs, mem_univ _⟩))
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, ∀ s ∈ S, ∀ x, |G s x| ≤ Cf := by
    obtain ⟨C, hC⟩ := (hScpt.prod (isCompact_Icc (a := α) (b := β))).exists_bound_of_continuousOn
      (hGc.mono (prod_mono subset_rfl (subset_univ _)))
    refine ⟨max C 0, fun s hs x => ?_⟩
    by_cases hx : x ∈ Icc α β
    · have := hC (s, x) ⟨hs, hx⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · rw [hGz s hs x hx, abs_zero]; exact le_max_right _ _
  obtain hmodG := unif_mod_of_continuousOn hScpt hGc hGz
  have key := hω fam (Icc α β) isCompact_Icc hT0 (fun p hp => hsl _ (hclS p))
    (fun p hp => closure_minimal (fun x hx => by
      by_contra h; exact hx (hGz _ (hclS p) x h)) isClosed_Icc)
    Cf (fun p hp x => hCf _ (hclS p) x)
    (fun ε₁ hε₁ => by
      obtain ⟨δ, hδ, hδc⟩ := hmodG ε₁ hε₁
      refine ⟨δ, hδ, fun p hp p' hp' hpp' x => ?_⟩
      simp only [hfam]
      rw [hclK p hp, hclK p' hp']
      exact hδc _ (hSmem' _ ((hmemK p).1 hp).1.1 ((hmemK p).1 hp).1.2) _
        (hSmem' _ ((hmemK p').1 hp').1.1 ((hmemK p').1 hp').1.2)
        ((abs_coord_le_norm p p' 0).trans hpp') x)
  refine ⟨fun s => ∫ u in Icc (flowFam W q ![s, W s] (a : ℝ)).re
      (flowFam W q ![s, W s] (b : ℝ)).re,
      fam ![s, W s] (Function.invFunOn (fun t : ℝ => (flowFam W q ![s, W s] t).re)
        (Icc (a : ℝ) b) u) * Real.exp (γ / 2 * h0rev κ u) ∂qBoundaryMeasure γ (Y ω),
    fun η hη => ?_⟩
  filter_upwards [key η hη] with k hk s hs hss
  have hsK : (![s, W s] : Fin 2 → ℝ) ∈ K := by
    rw [hmemK]
    refine ⟨⟨by simpa using hs, by simpa using hss.trans (min_le_left _ _)⟩, ?_⟩
    have hd : dist s s₀ < δW := by
      rw [Real.dist_eq]; exact lt_of_le_of_lt (hss.trans (min_le_right _ _)) (by linarith)
    have := hδWc s hd
    rw [Real.dist_eq] at this
    simpa using this.le
  have e : fam ![s, W s] = awTest (realRevMap (vrev W T) (T - s)) u v f := by
    simp only [hfam, hG, hF, hVdef]
    rw [hclK _ hsK]
    simp
  have := hk _ hsK
  rw [e] at this ⊢
  exact this

set_option maxHeartbeats 1000000 in
/-- **Fixed-path anchored convergence on the whole time interval `[q,T]`** (finite cover by the
time boxes of `flow_box_conv`). -/
theorem flow_fixed_conv {W : ℝ → ℝ} (hW : Continuous W) {T q : ℝ} (hq0 : 0 < q) (hqT : q ≤ T)
    {u v u' v' u₂ v₂ : ℝ} (huu' : u < u') (hu'v' : u' < v') (hv'v : v' < v)
    (hu₂ : u' < u₂) (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v')
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x)
    (κ : ℝ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (Y : Ω → FieldSample)
    (hY : IsFreeGFFModConstH Y P) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ, Continuous f → tsupport f ⊆ Icc u₂ v₂ →
      UniformCauchySeqOn (fun k s => ∫ x, awTest (realRevMap (vrev W T) (T - s)) u v f x
        ∂bdryApprox γ (coordChange (ofFun (h0rev κ) + Y ω) (flowFam W q ![s, W s]) (Qc γ)) k)
        atTop (Icc q T) := by
  classical
  have hbox : ∀ s₀ ∈ Icc q T, ∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ, Continuous f →
      tsupport f ⊆ Icc u₂ v₂ → ∃ Λ : ℝ → ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
        ∀ s ∈ Icc q T, |s - s₀| ≤ ε →
          |∫ x, awTest (realRevMap (vrev W T) (T - s)) u v f x ∂bdryApprox γ
              (coordChange (ofFun (h0rev κ) + Y ω) (flowFam W q ![s, W s]) (Qc γ)) k -
            Λ s| ≤ η := fun s₀ hs₀ => by
    obtain ⟨ε, hε, h⟩ := flow_box_conv (P := P) hW hq0 hqT huu' hu'v' hv'v hu₂ hu₂v₂ hv₂ hLive
      hs₀ κ hγ hγ2
    exact ⟨ε, hε, h Y hY⟩
  choose! εf hεf hae using hbox
  obtain ⟨t, htS, hcov⟩ := (isCompact_Icc (a := q) (b := T)).elim_nhds_subcover
    (fun s₀ => ball s₀ (εf s₀)) (fun s₀ hs₀ => ball_mem_nhds _ (hεf s₀ hs₀))
  have hall : ∀ᵐ ω ∂P, ∀ s₀ ∈ t, ∀ f : ℝ → ℝ, Continuous f →
      tsupport f ⊆ Icc u₂ v₂ → ∃ Λ : ℝ → ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
        ∀ s ∈ Icc q T, |s - s₀| ≤ εf s₀ →
          |∫ x, awTest (realRevMap (vrev W T) (T - s)) u v f x ∂bdryApprox γ
              (coordChange (ofFun (h0rev κ) + Y ω) (flowFam W q ![s, W s]) (Qc γ)) k -
            Λ s| ≤ η :=
    (ae_ball_iff t.countable_toSet).2 fun s₀ hs₀ => hae s₀ (htS s₀ hs₀)
  filter_upwards [hall] with ω hω f hf hfs
  choose Λ hΛ using fun (s₀ : t) => hω s₀.1 s₀.2 f hf hfs
  -- the box of each point
  have hpick : ∀ s ∈ Icc q T, ∃ s₀ : t, |s - s₀.1| < εf s₀.1 := by
    intro s hs
    obtain ⟨s₀, hs₀t, hss⟩ := mem_iUnion₂.1 (hcov hs)
    exact ⟨⟨s₀, hs₀t⟩, by rw [← Real.dist_eq]; exact mem_ball.1 hss⟩
  choose j hj using hpick
  refine TendstoUniformlyOn.uniformCauchySeqOn
    (f := fun s => if hs : s ∈ Icc q T then Λ (j s hs) s else 0) ?_
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hfin : ∀ᶠ k in atTop, ∀ s₀ : t, ∀ s ∈ Icc q T, |s - s₀.1| ≤ εf s₀.1 →
      |∫ x, awTest (realRevMap (vrev W T) (T - s)) u v f x ∂bdryApprox γ
          (coordChange (ofFun (h0rev κ) + Y ω) (flowFam W q ![s, W s]) (Qc γ)) k -
        Λ s₀ s| ≤ η / 2 :=
    eventually_all.2 fun s₀ => hΛ s₀ (η / 2) (by positivity)
  filter_upwards [hfin] with k hk s hs
  simp only [dif_pos hs]
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (hk (j s hs) s hs (hj s hs).le) (by linarith)

end SWCore
end QuantumZipper
