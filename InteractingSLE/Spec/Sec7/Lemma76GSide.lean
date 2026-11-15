/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GZone
import InteractingSLE.Spec.Sec7.SideHeightBox

/-!
# The sides of the two prefixes in the retained chart

Packet PROVE-LEMMA76G (proof of Lemma 7.6, pp. 268–269: the two sides `∓λ − θ₂χ` of the second prefix around the
second tip `0`, and the two sides `∓λ − θ₁χ` of the first prefix around the first tip `w₁`). In the setting of
`Lemma76GZone`, let `f` be the physical single-path chart of the first prefix at its stop `a` (`f(α(a)) = 0`, the
right side of `α` at positive values). Then:

* at every real chart point `w > R₂` the composite `f ∘ ψ` has a real limit `F(w)` (`exists_real_tendsto_comp`, the
  cluster-set lemma of `YuanFiber`), and `F` is strictly increasing on `(R₂, ∞)` (`Lemma76GMono`, Schwarz reflection
  and the open mapping theorem);
* `F(w₁) = 0` (`bdryVal_tip₁`: along `f⁻¹(iδ) → α(a)` inside the domain, the chart tends to `w₁`);

hence a chart point `w ∈ (L₁, R₁)` sees the right side of `α` (`F(w) > 0`) iff `w > w₁`. Mirror statements for the
second prefix on `(−∞, L₁)` with `F(0) = 0`. Finally every open subinterval of a prefix's chart interval contains a
chart point mapped into `ℍ` (`exists_mem_H_of_forall_mem`), which is how the slit bound of the single-path heights is
transported to real points of the prefix.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv)

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open HalfPlaneSep Restart Supp7 SideHeightBox

/-- The physical single-path chart of a path from `x` at the stop `q`, for the driver `W`. -/
def physF (W : ℝ≥0 → ℝ) (q : ℝ≥0) (x : ℝ) : ℂ → ℂ := fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - x)

open scoped Classical in
/-- The boundary value of `f ∘ ψ` at a real point (the limit within `ℍ`, `0` if none). -/
def bdryVal (f ψ : ℂ → ℂ) (w : ℝ) : ℝ :=
  if h : ∃ y : ℝ, Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((y : ℝ) : ℂ)) then h.choose else 0

theorem tendsto_bdryVal {f ψ : ℂ → ℂ} {w : ℝ}
    (h : ∃ y : ℝ, Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((y : ℝ) : ℂ))) :
    Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((bdryVal f ψ w : ℝ) : ℂ)) := by
  classical
  have e : bdryVal f ψ w = h.choose := by simp only [bdryVal, h, ↓reduceDIte]
  rw [e]; exact h.choose_spec

theorem bdryVal_eq {f ψ : ℂ → ℂ} {w y : ℝ}
    (h : Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((y : ℝ) : ℂ))) : bdryVal f ψ w = y := by
  have := neBot_nhdsWithin_H w
  exact ofReal_injective (tendsto_nhds_unique (tendsto_bdryVal ⟨y, h⟩) h)

/-! ### The physical chart -/

section Phys

variable {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x : ℝ} {W : ℝ≥0 → ℝ} {q : ℝ≥0}

theorem isOpen_U (hp : IsPathGood α ζ x) (hq : (q : ℝ≥0∞) ≤ ζ) : IsOpen (H \ fillH (α '' Icc 0 q)) :=
  isOpen_H_diff_fillH (Sec7.IsPathGood.isCompact_image hp hq).isBounded

theorem differentiableOn_physF (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hq : (q : ℝ≥0∞) < ζ) :
    DifferentiableOn ℂ (physF W q x) (H \ fillH (α '' Icc 0 q)) := by
  obtain ⟨κ, -, hmap, -⟩ := ReverseArc.exists_physChart hg hWc hW0 hq
  have h := hmap.1.1
  have : physF W q x = fun z => (fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) + κ) - κ := by
    funext z; simp [physF]
  rw [this]
  exact h.sub_const _

theorem physF_disp (hp : IsPathGood α ζ x) (hg : IsGeneratingTrace W ζ (fun t => α t - x))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ}) (hW0 : W 0 = 0) (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) :
    ∃ C : ℝ, ∀ z ∈ H \ fillH (α '' Icc 0 q), ‖physF W q x z - z‖ ≤ C := by
  have hinj' : InjOn (fun t => α t - x) {t | (t : ℝ≥0∞) ≤ ζ} := fun s hs t ht hst =>
    hp.1 hs ht (sub_left_injective hst)
  obtain ⟨C, hC⟩ := (ReverseArc.isChart hg hWc hW0 hinj' hq hq0).bdd
  refine ⟨C + |x|, fun z hz => ?_⟩
  have hz' := (ReverseArc.mem_H_diff_fillH_phys_iff (α := α) x q z).1 hz
  have h1 := hC _ hz'
  have h2 : physF W q x z - z = (fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) - (z - x)) - (x : ℂ) := by
    simp only [physF]; ring
  rw [h2]
  calc ‖(fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) - (z - x)) - (x : ℂ)‖
      ≤ ‖fwdMap (fun r : ℝ => W r.toNNReal) q (z - x) - (z - x)‖ + ‖(x : ℂ)‖ := norm_sub_le _ _
    _ ≤ C + |x| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith

end Phys

/-! ### Real limits of the composite -/

section Comp

variable {α : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ ψ : ℂ → ℂ}

/-- **The composite has a real limit** at a real point whose chart image is off the single-path domain. -/
theorem exists_real_tendsto_comp (hch : IsPhysChart α q f Φ) (hψc : ContinuousOn ψ Hbar)
    (hψU : MapsTo ψ H (H \ fillH (α '' Icc 0 q))) {M : ℝ} (hM : ∀ z ∈ H, ‖f (ψ z) - z‖ ≤ M) {w : ℝ}
    (hw : ψ w ∉ H \ fillH (α '' Icc 0 q)) :
    ∃ y : ℝ, Φ y = ψ w ∧ Tendsto (fun z => f (ψ z)) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((y : ℝ) : ℂ)) := by
  have hinj : InjOn Φ H := fun z hz z' hz' h => by rw [← hch.f_inv z hz, ← hch.f_inv z' hz', h]
  have hR : ∀ z : ℂ, z.im = 0 → Φ z ∉ Φ '' H := by
    rintro z hz0 ⟨v, hv, hvz⟩
    have hU := hch.inv_mem hv
    rw [hvz] at hU
    have hze : z = ((z.re : ℝ) : ℂ) := (Restart.ofReal_re_eq hz0).symm
    rw [hze] at hU
    have hα := hch.bdry z.re hU.1
    exact hU.2 (mem_fillH_of_mem_closure hU.1 (subset_closure hα))
  have hGc : ContinuousOn (fun z => f (ψ z)) H :=
    hch.cont.comp (hψc.mono H_subset_Hbar) hψU
  have hGH : MapsTo (fun z => f (ψ z)) H Hbar := fun z hz => H_subset_Hbar (hch.maps (hψU hz))
  have hGR : ∀ᶠ z in 𝓝[H] ((w : ℝ) : ℂ), ‖f (ψ z)‖ ≤ ‖((w : ℝ) : ℂ)‖ + 1 + M := by
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds ((w : ℝ) : ℂ) one_pos), self_mem_nhdsWithin]
      with z hz hzH
    have h1 := hM z hzH
    have h2 : ‖z‖ ≤ ‖((w : ℝ) : ℂ)‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z ((w : ℝ) : ℂ)
      have h3 : ‖z - ((w : ℝ) : ℂ)‖ < 1 := by rw [← dist_eq_norm]; exact hz.2
      linarith
    calc ‖f (ψ z)‖ = ‖(f (ψ z) - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖f (ψ z) - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖((w : ℝ) : ℂ)‖ + 1 + M := by linarith
  have hFG : Tendsto (fun z => Φ (f (ψ z))) (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 (ψ w)) := by
    have h1 : Tendsto ψ (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 (ψ w)) :=
      ((hψc _ (ofReal_mem_Hbar w)).tendsto).mono_left (nhdsWithin_mono _ H_subset_Hbar)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (hch.inv_f _ (hψU hz)).symm
  obtain ⟨ξ, hξ, hΦξ, hlim⟩ := exists_tendsto_of_tendsto_comp hch.diff hch.inv_cont hinj hR (ofReal_mem_Hbar w)
    hGc hGH hGR hFG
  have hξ0 : ξ.im = 0 := by
    by_contra hne
    have hξH : ξ ∈ H := lt_of_le_of_ne hξ (Ne.symm hne)
    exact hw (hΦξ ▸ hch.inv_mem hξH)
  refine ⟨ξ.re, ?_, ?_⟩
  · rw [Restart.ofReal_re_eq hξ0]; exact hΦξ
  · rw [Restart.ofReal_re_eq hξ0]; exact hlim

end Comp

/-! ### Non-real chart points inside a prefix's chart interval -/

/-- **An open chart interval mapped into a prefix contains a chart point mapped into `ℍ`** (a prefix contains no
real segment, and `ψ` is not constant on a real interval). -/
theorem exists_mem_H_of_forall_mem {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {x₀ : ℝ} {c : ℝ≥0} (hp : IsPathGood γ ζ x₀)
    (hc : (c : ℝ≥0∞) ≤ ζ) {ψ : ℂ → ℂ} (hψc : ContinuousOn ψ Hbar) (hψd : DifferentiableOn ℂ ψ H)
    (hψi : InjOn ψ H) (hψim : ∀ w ∈ Hbar, 0 ≤ (ψ w).im) {u v : ℝ} (huv : u < v)
    (hall : ∀ t ∈ Ioo u v, ψ t ∈ γ '' Icc 0 c) : ∃ t ∈ Ioo u v, ψ t ∈ H := by
  by_contra hno
  push Not at hno
  have hreal : ∀ t ∈ Ioo u v, (ψ t).im = 0 := fun t ht =>
    le_antisymm (not_lt.1 (hno t ht)) (hψim _ (ofReal_mem_Hbar t))
  have hgc : ContinuousOn (fun t : ℝ => (ψ t).re) (Ioo u v) :=
    Complex.continuous_re.comp_continuousOn (hψc.comp_continuous continuous_ofReal ofReal_mem_Hbar).continuousOn
  have hpc : IsPreconnected ((fun t : ℝ => (ψ t).re) '' Ioo u v) := isPreconnected_Ioo.image _ hgc
  by_cases hconst : ∀ t ∈ Ioo u v, ∀ t' ∈ Ioo u v, (ψ t).re = (ψ t').re
  · obtain ⟨m₀, hm₀⟩ : (Ioo u v).Nonempty := nonempty_Ioo.2 huv
    obtain ⟨m, hm, hne⟩ := exists_ne_of_injOn hψd hψc hψi huv (ψ m₀)
    apply hne
    rw [← Restart.ofReal_re_eq (hreal m hm), ← Restart.ofReal_re_eq (hreal m₀ hm₀), hconst m hm m₀ hm₀]
  · push Not at hconst
    obtain ⟨t, ht, t', ht', hne⟩ := hconst
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · refine not_forall_Icc_mem_image hp hc hlt fun y hy => ?_
      obtain ⟨s, hs, hsy⟩ := hpc.Icc_subset ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩ hy
      rw [← hsy, Restart.ofReal_re_eq (hreal s hs)]
      exact hall s hs
    · refine not_forall_Icc_mem_image hp hc hlt fun y hy => ?_
      obtain ⟨s, hs, hsy⟩ := hpc.Icc_subset ⟨t', ht', rfl⟩ ⟨t, ht, rfl⟩ hy
      rw [← hsy, Restart.ofReal_re_eq (hreal s hs)]
      exact hall s hs

/-! ### The two side functions of the retained chart -/

namespace IsSetting

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}
  (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift)
include hs

theorem ψi : InjOn ψ H := hs.bij.injOn

theorem ψU₁ : MapsTo ψ H (H \ fillH (α '' Icc 0 a)) := fun _ hz => IsSetting.fill₁_subset (hs.bij.mapsTo hz)

theorem ψU₂ : MapsTo ψ H (H \ fillH (β '' Icc 0 b)) := fun _ hz => IsSetting.fill₂_subset (hs.bij.mapsTo hz)

theorem comp_disp {f : ℂ → ℂ} {U : Set ℂ} (hψU : MapsTo ψ H U) {C : ℝ} (hC : ∀ z ∈ U, ‖f z - z‖ ≤ C) :
    ∃ M : ℝ, ∀ z ∈ H, ‖f (ψ z) - z‖ ≤ M := by
  obtain ⟨M, hM⟩ := hs.disp
  refine ⟨C + M, fun z hz => ?_⟩
  calc ‖f (ψ z) - z‖ = ‖(f (ψ z) - ψ z) + (ψ z - z)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖f (ψ z) - ψ z‖ + ‖ψ z - z‖ := norm_add_le _ _
    _ ≤ C + M := add_le_add (hC _ (hψU hz)) (hM z (H_subset_Hbar hz))

theorem ψφ {d : ℂ} (hd : d ∈ activeDomain α a β b) : ψ (φ d) = d := by
  rw [hs.D_eq] at hd
  obtain ⟨v, hv, rfl⟩ := hs.bij.surjOn hd
  rw [hs.hC.fwd_inv v hv]

theorem notMem_U₁ {w : ℝ} (hw : (zoneData φ α a β b).R₂ < w) : ψ w ∉ H \ fillH (α '' Icc 0 a) := by
  rcases hs.inv_cases w with hα | hβ | hu
  · intro h
    exact h.2 (mem_fillH_of_mem_closure h.1 (subset_closure hα))
  · exact absurd (hs.le_R₂_of_mem₂ hβ) (not_le.2 hw)
  · intro h
    exact (ne_of_gt (show (0 : ℝ) < (ψ w).im from h.1)) hu.1

theorem notMem_U₂ {w : ℝ} (hw : w < (zoneData φ α a β b).L₁) : ψ w ∉ H \ fillH (β '' Icc 0 b) := by
  rcases hs.inv_cases w with hα | hβ | hu
  · exact absurd (hs.L₁_le_of_mem₁ hα) (not_le.2 hw)
  · intro h
    exact h.2 (mem_fillH_of_mem_closure h.1 (subset_closure hβ))
  · intro h
    exact (ne_of_gt (show (0 : ℝ) < (ψ w).im from h.1)) hu.1

/-- **The side function of the first prefix**: the boundary values of `f_a ∘ ψ` (`f_a` the physical chart of the
first prefix at its stop) exist on `(R₂, ∞)`, are strictly increasing there and vanish at the first tip `w₁`. -/
theorem side₁ (ha0 : 0 < a) {W : ℝ≥0 → ℝ} (hg : IsGeneratingTrace W ζ₁ (fun t => α t - x₁))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₁}) (hW0 : W 0 = 0) :
    (∀ w : ℝ, (zoneData φ α a β b).R₂ < w → Tendsto (fun z => physF W a x₁ (ψ z)) (𝓝[H] ((w : ℝ) : ℂ))
      (𝓝 ((bdryVal (physF W a x₁) ψ w : ℝ) : ℂ))) ∧
    StrictMonoOn (bdryVal (physF W a x₁) ψ) (Ioi (zoneData φ α a β b).R₂) ∧
    bdryVal (physF W a x₁) ψ (zoneData φ α a β b).M₁ = 0 := by
  have hch : IsPhysChart α a (physF W a x₁)
      (fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) a) w + x₁) :=
    isPhysChart hg hWc hW0 hs.hp₁.1 hs.hpair.1 ha0
  obtain ⟨C, hC⟩ := physF_disp hs.hp₁ hg hWc hW0 hs.hpair.1 ha0
  obtain ⟨M, hM⟩ := hs.comp_disp hs.ψU₁ hC
  have hlim : ∀ w : ℝ, (zoneData φ α a β b).R₂ < w → Tendsto (fun z => physF W a x₁ (ψ z))
      (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((bdryVal (physF W a x₁) ψ w : ℝ) : ℂ)) := fun w hw => by
    obtain ⟨y, -, hy⟩ := exists_real_tendsto_comp hch hs.ψc hs.ψU₁ hM (hs.notMem_U₁ hw)
    exact tendsto_bdryVal ⟨y, hy⟩
  have hmono := strictMonoOn_Ioi_of_tendsto_comp hs.ψc hs.ψd hs.ψU₁ (isOpen_U hs.hp₁ hs.ha)
    (differentiableOn_physF hg hWc hW0 hs.hpair.1) hch.maps hs.ψi hch.injOn (fun w hw => hlim w hw) hM
  refine ⟨hlim, hmono, ?_⟩
  -- the first tip
  have hz := hs.zoneData_good
  have hw₁ : (zoneData φ α a β b).R₂ < (zoneData φ α a β b).M₁ := hs.R₂_lt_L₁.trans_le hz.L₁_le
  have hαa : α a ∈ α '' Icc 0 a := ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩
  have hfree : IsFreeAt (β '' Icc 0 b) (α a) := by
    rcases isFreeAt_or_isTrappedAt hs.isCompact₂.isClosed (fun h => Set.disjoint_left.1 hs.disj hαa h) with h | h
    · exact h
    · exact (Lemma76E.false_of_isTrappedAt_fst hs.hp₁ hs.hp₂ hs.hpair hs.isCompact₂.isClosed subset_union_right
        hs.disj hαa h).elim
  obtain ⟨ε, hε, hεfree⟩ := hfree
  set Φ : ℂ → ℂ := fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) a) w + x₁ with hΦ
  set e : ℕ → ℂ := fun n => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with he
  have heH : ∀ n, e n ∈ H := fun n => by
    show 0 < (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I).im
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    exact Nat.one_div_pos_of_nat
  have he0 : Tendsto e atTop (𝓝 0) := by
    have := ((continuous_ofReal.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).mul_const I
    simpa [he] using this
  have he0' : Tendsto e atTop (𝓝[Hbar] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨he0, Eventually.of_forall fun n => H_subset_Hbar (heH n)⟩
  have hvlim : Tendsto (fun n => Φ (e n)) atTop (𝓝 (α a)) := by
    have := ((hch.inv_cont 0 (by simp [Hbar])).tendsto).comp he0'
    rwa [hch.tip] at this
  have hvU : ∀ n, Φ (e n) ∈ H \ fillH (α '' Icc 0 a) := fun n => hch.inv_mem (heH n)
  have hvD : ∀ᶠ n in atTop, Φ (e n) ∈ activeDomain α a β b := by
    filter_upwards [hvlim (ball_mem_nhds _ hε)] with n hn
    rw [hs.D_eq]
    exact Sec7.mem_H_diff_fillH_union_of_disjoint hs.isCompact₁ hs.isCompact₂ hs.disj (hvU n)
      (hεfree ⟨hn, (hvU n).1⟩)
  have hvDf : Tendsto (fun n => Φ (e n)) atTop (𝓝[activeDomain α a β b] (α a)) :=
    tendsto_nhdsWithin_iff.2 ⟨hvlim, hvD⟩
  have hzlim := hs.chartPt_tip₁.1.comp hvDf
  have hact := hs.hC.isActiveChart hs.h0₂
  have hzH : ∀ᶠ n in atTop, φ (Φ (e n)) ∈ H := hvD.mono fun n hn => hact.1.mapsTo hn
  have hzlim' : Tendsto (fun n => φ (Φ (e n))) atTop (𝓝[H] ((zoneData φ α a β b).M₁ : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hzlim, hzH⟩
  have hG : ∀ᶠ n in atTop, physF W a x₁ (ψ (φ (Φ (e n)))) = e n := by
    filter_upwards [hvD] with n hn
    rw [hs.ψφ hn]
    exact hch.f_inv _ (heH n)
  have h1 := ((hlim _ hw₁).comp hzlim').congr' hG
  have := tendsto_nhds_unique h1 he0
  exact_mod_cast this

/-- **The side function of the second prefix**: the boundary values of `f_b ∘ ψ` exist on `(−∞, L₁)`, are strictly
increasing there and vanish at the second tip `0`. -/
theorem side₂ {W : ℝ≥0 → ℝ} (hg : IsGeneratingTrace W ζ₂ (fun t => β t - x₂))
    (hWc : ContinuousOn W {s | (s : ℝ≥0∞) < ζ₂}) (hW0 : W 0 = 0) :
    (∀ w : ℝ, w < (zoneData φ α a β b).L₁ → Tendsto (fun z => physF W b x₂ (ψ z)) (𝓝[H] ((w : ℝ) : ℂ))
      (𝓝 ((bdryVal (physF W b x₂) ψ w : ℝ) : ℂ))) ∧
    StrictMonoOn (bdryVal (physF W b x₂) ψ) (Iio (zoneData φ α a β b).L₁) ∧
    bdryVal (physF W b x₂) ψ 0 = 0 := by
  have hb0 : 0 < b := by
    refine pos_iff_ne_zero.2 fun h => ?_
    have h1 := hs.hpair.2.2.1
    rw [h] at h1
    exact (ne_of_gt (show (0 : ℝ) < (β 0).im from h1)) hs.h0₂
  have hch : IsPhysChart β b (physF W b x₂)
      (fun w => extendFrom H (fwdMapInv (fun r : ℝ => W r.toNNReal) b) w + x₂) :=
    isPhysChart hg hWc hW0 hs.hp₂.1 hs.hpair.2.1 hb0
  obtain ⟨C, hC⟩ := physF_disp hs.hp₂ hg hWc hW0 hs.hpair.2.1 hb0
  obtain ⟨M, hM⟩ := hs.comp_disp hs.ψU₂ hC
  have hlim : ∀ w : ℝ, w < (zoneData φ α a β b).L₁ → Tendsto (fun z => physF W b x₂ (ψ z))
      (𝓝[H] ((w : ℝ) : ℂ)) (𝓝 ((bdryVal (physF W b x₂) ψ w : ℝ) : ℂ)) := fun w hw => by
    obtain ⟨y, -, hy⟩ := exists_real_tendsto_comp hch hs.ψc hs.ψU₂ hM (hs.notMem_U₂ hw)
    exact tendsto_bdryVal ⟨y, hy⟩
  have hmono := strictMonoOn_Iio_of_tendsto_comp hs.ψc hs.ψd hs.ψU₂ (isOpen_U hs.hp₂ hs.hb)
    (differentiableOn_physF hg hWc hW0 hs.hpair.2.1) hch.maps hs.ψi hch.injOn (fun w hw => hlim w hw) hM
  refine ⟨hlim, hmono, ?_⟩
  have hz := hs.zoneData_good
  have h0L : (0 : ℝ) < (zoneData φ α a β b).L₁ := lt_of_le_of_lt hz.M₂_le hs.R₂_lt_L₁
  obtain ⟨y, hΦy, hy⟩ := exists_real_tendsto_comp hch hs.ψc hs.ψU₂ hM (hs.notMem_U₂ h0L)
  rw [ofReal_zero, hs.ψ0] at hΦy
  have hy0 := hch.tip_fibre hs.hpair.2.2.1 y hΦy
  rw [hy0] at hy
  exact bdryVal_eq hy

end IsSetting

end Lemma76G

end Sec7

end InteractingSLE
