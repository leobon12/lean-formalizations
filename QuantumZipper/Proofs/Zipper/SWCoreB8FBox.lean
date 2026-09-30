import QuantumZipper.Proofs.Zipper.SWCoreB7cBox
import QuantumZipper.Proofs.Zipper.SWCoreB8Class

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (1): the three-parameter flow box `(s, w, c)` (offset form of `flow_box_conv`)

Decision D70 (fixed-path side) with the dilation as one more family parameter (D64, SWC-B8
plan (a)). For a **fixed** continuous driver `W`, an anchor `0 < q ≤ T`, a window `[u,v]` live at
`q`, `s₀ ∈ [q,T]` and an offset `d₀ ∈ [1,2]`, there is `ε > 0` such that for every free field `Y`,
almost surely, for every continuous `f` supported in `[u₂,v₂] ⊂ (u,v)`, the dilated transported
test integrals

  `∫ awTest (F_s) u v f (c ·) d(bdryApprox γ (coordChange (𝔥₀ + Y) (ψ_s ∘ (c ·)) Q) k)`

converge uniformly in `(s, c)`, `|s − s₀| ≤ ε`, `|c − d₀| ≤ ε` (`flow_box_conv3`).

The maps `z ↦ ψ_s(c z)` of the box lie in one boundary class (`dil_mem_class`, on a sub-window
`[a', b']` with `c [a', b'] ⊂ (a, b)` for `c` near `d₀`) and are Lipschitz in `(s, w, c)`
(`flow_local_class_sep` + `dil_lipschitz_loc`); the test functions `x ↦ awTest (F_s) u v f (c x)`
are jointly continuous with a common compact support. Then the weighted family transport
`ae_transport_family_h0rev_mov` with `n = 3` applies, exactly as in `flow_box_conv`.

Sources: Sheffield–Wang arXiv:1605.06171 Thm 1.4 (continuous radii) and Thm 4.3 (all maps at
once), through the D64 family cores. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open B2 RegUnif

/-- `unif_mod_of_continuousOn` for a compact parameter set in a pseudometric space. -/
theorem unif_mod_of_continuousOn_metric {E : Type*} [PseudoMetricSpace E] {S : Set E}
    (hS : IsCompact S) {G : E → ℝ → ℝ}
    (hG : ContinuousOn (fun p : E × ℝ => G p.1 p.2) (S ×ˢ univ)) {α β : ℝ}
    (hGz : ∀ s ∈ S, ∀ x ∉ Icc α β, G s x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ S, ∀ s' ∈ S, dist s s' ≤ δ →
      ∀ x, |G s x - G s' x| ≤ ε := by
  intro ε hε
  have hUC := (hS.prod (isCompact_Icc (a := α) (b := β))).uniformContinuousOn_of_continuous
    (hG.mono (prod_mono subset_rfl (subset_univ _)))
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
  refine ⟨δ / 2, by linarith, fun s hs s' hs' hss' x => ?_⟩
  by_cases hx : x ∈ Icc α β
  · have hd : dist (s, x) (s', x) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      linarith
    have := hδc (s, x) ⟨hs, hx⟩ (s', x) ⟨hs', hx⟩ hd
    rw [Real.dist_eq] at this
    exact this.le
  · rw [hGz s hs x hx, hGz s' hs' x hx, sub_zero, abs_zero]; exact hε.le

/-- `dil_lipschitz` on a sub-window `[c₁, c₂] ⊂ [1,2]` of dilations. -/
theorem dil_lipschitz_loc {a b ρ M m : ℝ} {ψ : ℂ → ℂ} (hψ : ψ ∈ BdryClass a b ρ M m)
    (hρ : 0 < ρ) {α β ρ' c₁ c₂ : ℝ} (hρ'ρ : 4 * ρ' ≤ ρ) (h1 : 1 ≤ c₁) (h2 : c₂ ≤ 2)
    (hin : ∀ c ∈ Icc c₁ c₂, ∀ t ∈ Icc α β, c * t ∈ Icc a b)
    {c c' : ℝ} (hc : c ∈ Icc c₁ c₂) (hc' : c' ∈ Icc c₁ c₂) {z : ℂ}
    (hz : z ∈ thickening ρ' (segC α β)) :
    ‖ψ ((c : ℂ) * z) - ψ ((c' : ℂ) * z)‖ ≤ 4 * M / ρ * ‖z‖ * |c - c'| := by
  set S : Set ℂ := segment ℝ ((c' : ℂ) * z) ((c : ℂ) * z) with hS
  have hSsub : S ⊆ thickening (ρ / 2) (segC a b) := by
    intro w hw
    obtain ⟨θ, η, hθ, hη, hθη, rfl⟩ := hw
    have hcθ : θ * c' + η * c ∈ Icc c₁ c₂ := by
      constructor <;> nlinarith [hc.1, hc.2, hc'.1, hc'.2]
    have hcθ' : θ * c' + η * c ∈ Icc (1 : ℝ) 2 := ⟨h1.trans hcθ.1, hcθ.2.trans h2⟩
    have := dil_mem_thick hcθ' (hin _ hcθ) hz
    have e : θ • ((c' : ℂ) * z) + η • ((c : ℂ) * z) = ((θ * c' + η * c : ℝ) : ℂ) * z := by
      simp only [Complex.real_smul]; push_cast; ring
    rw [e]
    exact thickening_mono (by linarith) _ this
  have hdS : ∀ w ∈ S, DifferentiableAt ℂ ψ w := fun w hw =>
    hψ.1.differentiableAt (isOpen_thickening.mem_nhds
      (thickening_mono (by linarith) _ (hSsub hw)))
  have hb : ∀ w ∈ S, ‖deriv ψ w‖ ≤ 4 * M / ρ := fun w hw =>
    norm_deriv_le_of_class hψ hρ (hSsub hw)
  have key := (convex_segment _ _).norm_image_sub_le_of_norm_deriv_le hdS hb
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have e2 : ‖(c : ℂ) * z - (c' : ℂ) * z‖ = ‖z‖ * |c - c'| := by
    rw [← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, mul_comm]
  rw [e2] at key
  calc _ ≤ 4 * M / ρ * (‖z‖ * |c - c'|) := key
    _ = _ := by ring

theorem norm_le_of_mem_thick_segC {α β ρ : ℝ} {z : ℂ} (hz : z ∈ thickening ρ (segC α β)) :
    ‖z‖ ≤ |α| + |β| + ρ := by
  obtain ⟨_, ⟨t, ht, rfl⟩, hzt⟩ := mem_thickening_iff.1 hz
  have h1 : ‖(t : ℂ)‖ ≤ |α| + |β| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2, abs_nonneg α, abs_nonneg β, neg_abs_le α, le_abs_self β]
  have h2 := norm_sub_norm_le z (t : ℂ)
  rw [dist_eq_norm] at hzt
  linarith

theorem mem_box3 {p l h : Fin 3 → ℝ} : p ∈ Icc l h ↔
    (l 0 ≤ p 0 ∧ p 0 ≤ h 0) ∧ (l 1 ≤ p 1 ∧ p 1 ≤ h 1) ∧ (l 2 ≤ p 2 ∧ p 2 ≤ h 2) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1 0, h2 0⟩, ⟨h1 1, h2 1⟩, ⟨h1 2, h2 2⟩⟩
  · rintro ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩⟩
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
    exacts [a0, a1, a2, b0, b1, b2]

theorem abs_coord_le_norm' {n : ℕ} (p p' : Fin n → ℝ) (i : Fin n) : |p i - p' i| ≤ ‖p - p'‖ := by
  have := norm_le_pi_norm (p - p') i
  rwa [Real.norm_eq_abs, Pi.sub_apply] at this

/-- **The dilations in the map and in the test function cancel in the limit**: the explicit limit
of the family transport for `ψ ∘ (c ·)` and `G (c ·)` is that for `ψ` and `G`, when `G` vanishes
off `[α, β] ⊂ (c a', c b')`. -/
theorem dil_limit_eq {ψ : ℂ → ℂ} {a b ρ M m : ℝ} (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ)
    {a' b' c α β : ℝ} (hab' : a' ≤ b')
    (hin : ∀ t ∈ Icc a' b', c * t ∈ Icc a b) (hα : c * a' < α) (hβ : β < c * b')
    {G : ℝ → ℝ} (hG : ∀ x ∉ Icc α β, G x = 0) (w : ℝ → ℝ) (ν : Measure ℝ) :
    ∫ u in Icc (ψ ((c : ℂ) * (a' : ℂ))).re (ψ ((c : ℂ) * (b' : ℂ))).re,
        G (c * Function.invFunOn (fun t : ℝ => (ψ ((c : ℂ) * (t : ℂ))).re) (Icc a' b') u) *
          w u ∂ν =
      ∫ u in Icc (ψ (a : ℂ)).re (ψ (b : ℂ)).re,
        G (Function.invFunOn (fun t : ℝ => (ψ (t : ℂ)).re) (Icc a b) u) * w u ∂ν := by
  set φ : ℝ → ℝ := fun t => (ψ (t : ℂ)).re with hφ
  have hca : c * a' ∈ Icc a b := hin a' ⟨le_rfl, hab'⟩
  have hcb : c * b' ∈ Icc a b := hin b' ⟨hab', le_rfl⟩
  have hab : a ≤ b := hca.1.trans hca.2
  have hφc : ContinuousOn φ (Icc a b) := by
    have h1 : ContinuousOn ψ (thickening ρ (segC a b)) := hψ.1.continuousOn
    refine Complex.continuous_re.comp_continuousOn
      (h1.comp Complex.continuous_ofReal.continuousOn ?_)
    intro t ht
    exact self_subset_thickening hρ _ ⟨t, ht, rfl⟩
  have hφm : StrictMonoOn φ (Icc a b) := hψ.2.2.2.1
  have e1 : ∀ t : ℝ, (c : ℂ) * (t : ℂ) = ((c * t : ℝ) : ℂ) := fun t => by push_cast; ring
  have hfun : (fun t : ℝ => (ψ ((c : ℂ) * (t : ℂ))).re) = fun t => φ (c * t) :=
    funext fun t => by rw [e1]
  rw [hfun, e1, e1]
  have hsub : Icc (φ (c * a')) (φ (c * b')) ⊆ Icc (φ a) (φ b) :=
    Icc_subset_Icc (hφm.monotoneOn ⟨le_rfl, hab⟩ hca hca.1)
      (hφm.monotoneOn hcb ⟨hab, le_rfl⟩ hcb.2)
  have hinv : ∀ u ∈ Icc (φ a) (φ b), Function.invFunOn φ (Icc a b) u ∈ Icc a b ∧
      φ (Function.invFunOn φ (Icc a b) u) = u := by
    intro u hu
    have hex : ∃ y ∈ Icc a b, φ y = u := intermediate_value_Icc hab hφc hu
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hdiff : ∀ u ∈ Icc (φ a) (φ b) \ Icc (φ (c * a')) (φ (c * b')),
      G (Function.invFunOn φ (Icc a b) u) * w u = 0 := by
    intro u hu
    obtain ⟨hy, hyu⟩ := hinv u hu.1
    have hn : Function.invFunOn φ (Icc a b) u ∉ Icc α β := by
      intro hyab
      apply hu.2
      rw [← hyu]
      exact ⟨hφm.monotoneOn hca hy (by linarith [hyab.1]),
        hφm.monotoneOn hy hcb (by linarith [hyab.2])⟩
    rw [hG _ hn, zero_mul]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub hdiff]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  have hcc : ContinuousOn (fun t => φ (c * t)) (Icc a' b') :=
    hφc.comp (continuous_const.mul continuous_id).continuousOn fun t ht => hin t ht
  have hex : ∃ y ∈ Icc a' b', φ (c * y) = u := intermediate_value_Icc hab' hcc hu
  have hy'm := Function.invFunOn_mem hex
  have hy'e : φ (c * Function.invFunOn (fun t => φ (c * t)) (Icc a' b') u) = u :=
    Function.invFunOn_eq hex
  obtain ⟨hy, hyu⟩ := hinv u (hsub hu)
  have heq : c * Function.invFunOn (fun t => φ (c * t)) (Icc a' b') u =
      Function.invFunOn φ (Icc a b) u :=
    hφm.injOn (hin _ hy'm) hy (by rw [hy'e, hyu])
  rw [heq]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 2000000 in
/-- **Fixed-path anchored convergence on one `(s, c)` box, offset form.** -/
theorem flow_box_conv3 {W : ℝ → ℝ} (hW : Continuous W) {T q : ℝ} (hq0 : 0 < q) (hqT : q ≤ T)
    {u v u' v' u₂ v₂ : ℝ} (huu' : u < u') (hu'v' : u' < v') (hv'v : v' < v)
    (hu₂ : u' < u₂) (hu₂v₂ : u₂ ≤ v₂) (hv₂ : v₂ < v')
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal (T - q) < realHitTime (vrev W T) x) {s₀ d₀ : ℝ}
    (hs₀ : s₀ ∈ Icc q T) (hd₀ : d₀ ∈ Icc (1 : ℝ) 2) (κ : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Y : Ω → FieldSample, IsFreeGFFModConstH Y P →
      ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ, Continuous f → tsupport f ⊆ Icc u₂ v₂ →
        ∃ Λ : ℝ → ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ s ∈ Icc q T, |s - s₀| ≤ ε →
          ∀ c ∈ Icc (1 : ℝ) 2, |c - d₀| ≤ ε →
          |∫ x, awTest (realRevMap (vrev W T) (T - s)) u v f (c * x) ∂bdryApprox γ
              (coordChange (ofFun (h0rev κ) + Y ω)
                (fun z => flowFam W q ![s, W s] ((c : ℂ) * z)) (Qc γ)) k -
            Λ s| ≤ η := by
  obtain ⟨a, b, ρ, M, ε, L, csep, hab, hρ, hε, hL, hcs, hcl, hwin, hlip, hsep⟩ :=
    flow_local_class_sep hW hq0 hqT huu' hu'v' hv'v hLive hs₀
  obtain ⟨δW, hδW, hδWc⟩ := Metric.continuous_iff.1 hW s₀ ε hε
  have hd0 : 0 < d₀ := by linarith [hd₀.1]
  -- the time window and the window flows (as in `flow_box_conv`)
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
  have hs₀S : s₀ ∈ S := hSmem' s₀ hs₀ (by rw [sub_self, abs_zero]; exact hε.le)
  have hSne : S.Nonempty := ⟨s₀, hs₀S⟩
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
  -- the dilated sub-window `[a', b']` and the offset window around `d₀`
  obtain ⟨a', ha'1, ha'2⟩ := exists_rat_btwn ((div_lt_div_iff_of_pos_right hd0).2 hαa)
  obtain ⟨b', hb'1, hb'2⟩ := exists_rat_btwn ((div_lt_div_iff_of_pos_right hd0).2 hβb)
  have ha'd : (a : ℝ) < a' * d₀ := (div_lt_iff₀ hd0).1 ha'1
  have ha'd' : (a' : ℝ) * d₀ < α := (lt_div_iff₀ hd0).1 ha'2
  have hb'd : β < (b' : ℝ) * d₀ := (div_lt_iff₀ hd0).1 hb'1
  have hb'd' : (b' : ℝ) * d₀ < b := (lt_div_iff₀ hd0).1 hb'2
  set a₁ : ℝ := (a' + α / d₀) / 2 with ha₁
  set b₁ : ℝ := (b' + β / d₀) / 2 with hb₁
  have ha'a₁ : (a' : ℝ) < a₁ := by rw [ha₁]; linarith
  have hb₁b' : b₁ < (b' : ℝ) := by rw [hb₁]; linarith
  have o1 : IsOpen {c : ℝ | (a : ℝ) < c * a'} :=
    isOpen_lt continuous_const (continuous_id.mul continuous_const)
  have o2 : IsOpen {c : ℝ | c * a₁ < α} :=
    isOpen_lt (continuous_id.mul continuous_const) continuous_const
  have o3 : IsOpen {c : ℝ | β < c * b₁} :=
    isOpen_lt continuous_const (continuous_id.mul continuous_const)
  have o4 : IsOpen {c : ℝ | c * b' < (b : ℝ)} :=
    isOpen_lt (continuous_id.mul continuous_const) continuous_const
  have hUo : IsOpen {c : ℝ | (a : ℝ) < c * a' ∧ c * a₁ < α ∧ β < c * b₁ ∧ c * b' < b} :=
    o1.inter (o2.inter (o3.inter o4))
  have hd₀U : d₀ ∈ {c : ℝ | (a : ℝ) < c * a' ∧ c * a₁ < α ∧ β < c * b₁ ∧ c * b' < b} := by
    have eα : d₀ * (α / d₀) = α := mul_div_cancel₀ α hd0.ne'
    have eβ : d₀ * (β / d₀) = β := mul_div_cancel₀ β hd0.ne'
    have e1 : d₀ * a₁ = (d₀ * a' + α) / 2 := by
      rw [ha₁, show d₀ * ((a' + α / d₀) / 2) = (d₀ * a' + d₀ * (α / d₀)) / 2 by ring, eα]
    have e2 : d₀ * b₁ = (d₀ * b' + β) / 2 := by
      rw [hb₁, show d₀ * ((b' + β / d₀) / 2) = (d₀ * b' + d₀ * (β / d₀)) / 2 by ring, eβ]
    refine ⟨by linarith, ?_, ?_, by linarith⟩
    · rw [e1]; linarith
    · rw [e2]; linarith
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.isOpen_iff.1 hUo d₀ hd₀U
  set δ : ℝ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set C : Set ℝ := Icc (max 1 (d₀ - δ)) (min 2 (d₀ + δ)) with hC
  have hCmem : ∀ c ∈ C, c ∈ Icc (1 : ℝ) 2 ∧ |c - d₀| ≤ δ := by
    intro c hc
    obtain ⟨h1, h2⟩ := hc
    rw [max_le_iff] at h1; rw [le_min_iff] at h2
    exact ⟨⟨h1.1, h2.1⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩
  have hCmem' : ∀ c ∈ Icc (1 : ℝ) 2, |c - d₀| ≤ δ → c ∈ C := by
    intro c hc hcc
    obtain ⟨h1, h2⟩ := abs_le.1 hcc
    exact ⟨max_le hc.1 (by linarith), le_min hc.2 (by linarith)⟩
  have hCU : ∀ c ∈ C, (a : ℝ) < c * a' ∧ c * a₁ < α ∧ β < c * b₁ ∧ c * b' < b := by
    intro c hc
    refine hball ?_
    rw [mem_ball, Real.dist_eq]
    linarith [(hCmem c hc).2]
  have hCpos : ∀ c ∈ C, 0 < c := fun c hc => by linarith [(hCmem c hc).1.1]
  have hinC : ∀ c ∈ C, ∀ t ∈ Icc (a' : ℝ) b', c * t ∈ Icc (a : ℝ) b := by
    intro c hc t ht
    obtain ⟨h1, -, -, h4⟩ := hCU c hc
    have hc0 := hCpos c hc
    exact ⟨by linarith [mul_le_mul_of_nonneg_left ht.1 hc0.le],
      by linarith [mul_le_mul_of_nonneg_left ht.2 hc0.le]⟩
  have hd₀C : d₀ ∈ C := hCmem' d₀ hd₀ (by rw [sub_self, abs_zero]; exact hδ.le)
  have hCcpt : IsCompact C := isCompact_Icc
  -- the box in `(s, w, c)`
  set lo : Fin 3 → ℝ := ![max q (s₀ - ε), W s₀ - ε, max 1 (d₀ - δ)] with hlo
  set hi : Fin 3 → ℝ := ![min T (s₀ + ε), W s₀ + ε, min 2 (d₀ + δ)] with hhi
  set K : Set (Fin 3 → ℝ) := Icc lo hi with hK
  have hmemK : ∀ p : Fin 3 → ℝ, p ∈ K ↔ p 0 ∈ S ∧ |p 1 - W s₀| ≤ ε ∧ p 2 ∈ C := by
    intro p
    rw [hK, mem_box3, abs_le]
    simp only [hlo, hhi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hS, hC, mem_Icc]
    constructor
    · rintro ⟨h0, ⟨h1, h1'⟩, h2⟩; exact ⟨h0, ⟨by linarith, by linarith⟩, h2⟩
    · rintro ⟨h0, ⟨h1, h1'⟩, h2⟩; exact ⟨h0, ⟨by linarith, by linarith⟩, h2⟩
  have hp₀K : (![s₀, W s₀, d₀] : Fin 3 → ℝ) ∈ K := by
    rw [hmemK]
    exact ⟨hs₀S, by simp [hε.le], hd₀C⟩
  have hlohi : lo ≤ hi := hp₀K.1.trans hp₀K.2
  set ρ' : ℚ := ρ / 4 with hρ'def
  have hρ'e : ((ρ' : ℚ) : ℝ) = (ρ : ℝ) / 4 := by rw [hρ'def]; push_cast; ring
  have hρ'0 : (0 : ℝ) < ρ' := by rw [hρ'e]; positivity
  set Ψ : (Fin 3 → ℝ) → ℂ → ℂ := fun p z => flowFam W q ![p 0, p 1] (((p 2 : ℝ) : ℂ) * z)
    with hΨdef
  have hthick : ∀ c ∈ C, ∀ z ∈ thickening ((ρ' : ℚ) : ℝ) (segC a' b'),
      (c : ℂ) * z ∈ thickening (ρ : ℝ) (segC a b) := fun c hc z hz =>
    thickening_mono (by rw [hρ'e]; linarith) _ (dil_mem_thick (hCmem c hc).1 (hinC c hc) hz)
  have hΨ : ∀ p ∈ K, Ψ p ∈ BdryClass (a' : ℝ) b' ((ρ' : ℚ) : ℝ) M ((1 : ℚ) : ℝ) := by
    intro p hp
    obtain ⟨h0, h1, h2⟩ := (hmemK p).1 hp
    rw [Rat.cast_one]
    exact dil_mem_class (hcl _ (hSmem _ h0).1 (hSmem _ h0).2 _ h1) hρ'0
      (by rw [hρ'e]; linarith) (hCmem _ h2).1 (hinC _ h2) zero_le_one
  set R₁ : ℝ := |(a' : ℝ)| + |(b' : ℝ)| + ((ρ' : ℚ) : ℝ) with hR₁
  set L3 : ℝ := 2 * L + |4 * (M : ℝ) / ρ| * R₁ with hL3
  have hR₁0 : 0 ≤ R₁ := by positivity
  have hL30 : 0 ≤ L3 := by positivity
  have hlip3 : ∀ p ∈ K, ∀ p' ∈ K, ∀ z ∈ thickening ((ρ' : ℚ) : ℝ) (segC a' b'),
      ‖Ψ p z - Ψ p' z‖ ≤ L3 * ‖p - p'‖ := by
    intro p hp p' hp' z hz
    obtain ⟨h0, h1, h2⟩ := (hmemK p).1 hp
    obtain ⟨h0', h1', h2'⟩ := (hmemK p').1 hp'
    have k1 := hlip _ (hSmem _ h0).1 (hSmem _ h0).2 _ h1 _ (hSmem _ h0').1 (hSmem _ h0').2 _ h1'
      _ (hthick _ h2 z hz)
    have k2 := dil_lipschitz_loc (hcl _ (hSmem _ h0').1 (hSmem _ h0').2 _ h1') hρ
      (ρ' := ((ρ' : ℚ) : ℝ)) (by rw [hρ'e]; linarith) (le_max_left _ _) (min_le_left _ _)
      hinC h2 h2' hz
    have hz' : ‖z‖ ≤ R₁ := norm_le_of_mem_thick_segC hz
    have e0 := abs_coord_le_norm' p p' 0
    have e1 := abs_coord_le_norm' p p' 1
    have e2 := abs_coord_le_norm' p p' 2
    have k3 : 4 * (M : ℝ) / ρ * ‖z‖ * |p 2 - p' 2| ≤ |4 * (M : ℝ) / ρ| * R₁ * ‖p - p'‖ := by
      calc 4 * (M : ℝ) / ρ * ‖z‖ * |p 2 - p' 2| ≤ |4 * (M : ℝ) / ρ| * ‖z‖ * |p 2 - p' 2| := by
            gcongr; exact le_abs_self _
        _ ≤ |4 * (M : ℝ) / ρ| * R₁ * ‖p - p'‖ := by gcongr
    have tri : ‖Ψ p z - Ψ p' z‖ ≤ ‖flowFam W q ![p 0, p 1] ((p 2 : ℂ) * z) -
          flowFam W q ![p' 0, p' 1] ((p 2 : ℂ) * z)‖ +
        ‖flowFam W q ![p' 0, p' 1] ((p 2 : ℂ) * z) -
          flowFam W q ![p' 0, p' 1] ((p' 2 : ℂ) * z)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have k1' : L * (|p 0 - p' 0| + |p 1 - p' 1|) ≤ 2 * L * ‖p - p'‖ := by
      nlinarith [mul_le_mul_of_nonneg_left e0 hL, mul_le_mul_of_nonneg_left e1 hL]
    have eL : L3 * ‖p - p'‖ = 2 * L * ‖p - p'‖ + |4 * (M : ℝ) / ρ| * R₁ * ‖p - p'‖ := by
      rw [hL3]; ring
    linarith
  have hsep3 : ∀ p ∈ K, ∀ z ∈ thickening ((ρ' : ℚ) : ℝ) (segC a' b'), csep ≤ ‖Ψ p z‖ := by
    intro p hp z hz
    obtain ⟨h0, h1, h2⟩ := (hmemK p).1 hp
    exact hsep _ (hSmem _ h0).1 (hSmem _ h0).2 _ h1 _ (hthick _ h2 z hz)
  have hab' : (a' : ℝ) < b' := by
    have hαβ : α ≤ β :=
      (hmin hs2).trans ((hFm s2 hs2).monotoneOn hu₂I hv₂I hu₂v₂)
    have : α / d₀ ≤ β / d₀ := div_le_div_of_nonneg_right hαβ hd0.le
    linarith
  refine ⟨min (min ε (δW / 2)) δ, lt_min (lt_min hε (by linarith)) hδ, fun Y hY => ?_⟩
  have hmain := ae_transport_family_h0rev_mov (P := P) κ hY hγ hγ2 Ψ K hab' hρ'0
    (by norm_num : (0 : ℝ) < ((1 : ℚ) : ℝ)) hL30 hΨ hlip3 (lipschitzWith_boxClamp lo hi)
    (boxClamp_mem hlohi) (fun p hp => boxClamp_of_mem hp) (by positivity : (0 : ℝ) ≤ ‖lo‖ + ‖hi‖)
    (fun p hp => norm_le_of_mem_box hp) isCompact_Icc hcs hsep3
  filter_upwards [hmain] with ω hω f hf hfs
  set G : ℝ → ℝ → ℝ := fun s x => awTest (F s) u v f x with hG
  have hGc : ContinuousOn (fun p : ℝ × ℝ => G p.1 p.2) (S ×ˢ univ) :=
    continuousOn_awTest (lt_trans huu' hu₂) hu₂v₂ (lt_trans hv₂ hv'v) hFc hFm hf hfs
  have hGz : ∀ s ∈ S, ∀ x ∉ Icc α β, G s x = 0 := by
    intro s hs x hx
    refine awTest_eq_zero_of_not_mem (hFm s hs) hfs (by linarith) (by linarith) ?_
    by_contra h
    push Not at h
    exact hx ⟨le_trans (hmin hs) h.1, le_trans h.2 (hmax hs)⟩
  have hsl : ∀ s ∈ S, Continuous (G s) := fun s hs =>
    continuousOn_univ.1 (hGc.comp (f := fun y : ℝ => (s, y))
      (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨hs, mem_univ _⟩))
  obtain ⟨Cf, hCf⟩ : ∃ Cf : ℝ, ∀ s ∈ S, ∀ x, |G s x| ≤ Cf := by
    obtain ⟨C0, hC0⟩ := (hScpt.prod (isCompact_Icc (a := α) (b := β))).exists_bound_of_continuousOn
      (hGc.mono (prod_mono subset_rfl (subset_univ _)))
    refine ⟨max C0 0, fun s hs x => ?_⟩
    by_cases hx : x ∈ Icc α β
    · have := hC0 (s, x) ⟨hs, hx⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · rw [hGz s hs x hx, abs_zero]; exact le_max_right _ _
  set G' : ℝ × ℝ → ℝ → ℝ := fun sc x => G sc.1 (sc.2 * x) with hG'
  have hG'c : ContinuousOn (fun p : (ℝ × ℝ) × ℝ => G' p.1 p.2) ((S ×ˢ C) ×ˢ univ) :=
    hGc.comp (f := fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.1.2 * p.2))
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).mul continuous_snd)).continuousOn
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  have hG'z : ∀ sc ∈ S ×ˢ C, ∀ x ∉ Icc a₁ b₁, G' sc x = 0 := by
    intro sc hsc x hx
    refine hGz sc.1 hsc.1 _ ?_
    obtain ⟨-, h2, h3, -⟩ := hCU sc.2 hsc.2
    have hc0 := hCpos sc.2 hsc.2
    intro hm
    apply hx
    constructor
    · by_contra h
      push Not at h
      linarith [mul_lt_mul_of_pos_left h hc0, hm.1]
    · by_contra h
      push Not at h
      linarith [mul_lt_mul_of_pos_left h hc0, hm.2]
  have hmod := unif_mod_of_continuousOn_metric (hScpt.prod hCcpt) hG'c hG'z
  set fam : (Fin 3 → ℝ) → ℝ → ℝ := fun p => G' (boxClamp lo hi p 0, boxClamp lo hi p 2)
    with hfam
  have hclm : ∀ p, (boxClamp lo hi p 0, boxClamp lo hi p 2) ∈ S ×ˢ C := fun p => by
    have h := (hmemK _).1 (boxClamp_mem hlohi p)
    exact ⟨h.1, h.2.2⟩
  have hfamK : ∀ p ∈ K, fam p = G' (p 0, p 2) := fun p hp => by
    simp only [hfam, boxClamp_of_mem hp]
  have hG'cont : ∀ sc ∈ S ×ˢ C, Continuous (G' sc) := fun sc hsc =>
    (hsl _ hsc.1).comp (continuous_const.mul continuous_id)
  have hT0 : Icc a₁ b₁ ⊆ Ioo (a' : ℝ) b' := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have key := hω fam (Icc a₁ b₁) isCompact_Icc hT0 (fun p _ => hG'cont _ (hclm p))
    (fun p _ => closure_minimal (fun x hx => by
      by_contra h; exact hx (hG'z _ (hclm p) x h)) isClosed_Icc)
    Cf (fun p _ x => hCf _ (hclm p).1 _)
    (fun ε₁ hε₁ => by
      obtain ⟨δ₁, hδ₁, hδc⟩ := hmod ε₁ hε₁
      refine ⟨δ₁, hδ₁, fun p hp p' hp' hpp' x => ?_⟩
      rw [hfamK p hp, hfamK p' hp']
      have h1 := (hmemK p).1 hp
      have h2 := (hmemK p').1 hp'
      refine hδc _ ⟨h1.1, h1.2.2⟩ _ ⟨h2.1, h2.2.2⟩ ?_ x
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      exact max_le ((abs_coord_le_norm' p p' 0).trans hpp')
        ((abs_coord_le_norm' p p' 2).trans hpp'))
  refine ⟨fun s => ∫ u in Icc (flowFam W q ![s, W s] ((a : ℝ) : ℂ)).re
      (flowFam W q ![s, W s] ((b : ℝ) : ℂ)).re,
      G s (Function.invFunOn (fun t : ℝ => (flowFam W q ![s, W s] (t : ℂ)).re)
        (Icc (a : ℝ) b) u) * Real.exp (γ / 2 * h0rev κ u) ∂qBoundaryMeasure γ (Y ω),
    fun η hη => ?_⟩
  filter_upwards [key η hη] with k hk s hs hss c hc hcc
  have hpK : (![s, W s, c] : Fin 3 → ℝ) ∈ K := by
    rw [hmemK]
    refine ⟨hSmem' s hs (hss.trans ((min_le_left _ _).trans (min_le_left _ _))), ?_,
      hCmem' c hc (hcc.trans (min_le_right _ _))⟩
    have hd : dist s s₀ < δW := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (hss.trans ((min_le_left _ _).trans (min_le_right _ _)))
        (by linarith)
    have := hδWc s hd
    rw [Real.dist_eq] at this
    simpa using this.le
  obtain ⟨hsS, hWs, hcC⟩ := (hmemK _).1 hpK
  have e : fam ![s, W s, c] = fun x => awTest (realRevMap (vrev W T) (T - s)) u v f (c * x) := by
    rw [hfamK _ hpK]; rfl
  have hlim : (∫ u in Icc (Ψ ![s, W s, c] ((a' : ℝ) : ℂ)).re (Ψ ![s, W s, c] ((b' : ℝ) : ℂ)).re,
      fam ![s, W s, c] (Function.invFunOn (fun t : ℝ => (Ψ ![s, W s, c] (t : ℂ)).re)
        (Icc (a' : ℝ) b') u) * Real.exp (γ / 2 * h0rev κ u) ∂qBoundaryMeasure γ (Y ω)) =
      ∫ u in Icc (flowFam W q ![s, W s] ((a : ℝ) : ℂ)).re
        (flowFam W q ![s, W s] ((b : ℝ) : ℂ)).re,
        G s (Function.invFunOn (fun t : ℝ => (flowFam W q ![s, W s] (t : ℂ)).re)
          (Icc (a : ℝ) b) u) * Real.exp (γ / 2 * h0rev κ u) ∂qBoundaryMeasure γ (Y ω) := by
    rw [hfamK _ hpK]
    obtain ⟨-, h2, h3, -⟩ := hCU c hcC
    have hc0 := hCpos c hcC
    exact dil_limit_eq (ψ := flowFam W q ![s, W s]) (G := G s)
      (hcl s (hSmem s hsS).1 (hSmem s hsS).2 (W s) (by simpa using hWs)) hρ hab'.le (hinC c hcC)
      (by linarith [mul_lt_mul_of_pos_left ha'a₁ hc0])
      (by linarith [mul_lt_mul_of_pos_left hb₁b' hc0]) (hGz s hsS)
      (fun u => Real.exp (γ / 2 * h0rev κ u)) _
  have := hk _ hpK
  rw [hlim, e] at this
  exact this

end SWCore
end QuantumZipper
