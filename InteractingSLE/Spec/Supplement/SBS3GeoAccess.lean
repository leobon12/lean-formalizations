/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3GeoSecond
import InteractingSLE.Spec.Supplement.SB2FinCompP38

/-!
# Lemma S3: component access and the assembled second-path geometry

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification pp. 579–580). Deterministic. The component form of
Proposition 3.8 (`FinRel.ae_tendsto_sub_of_union_comp`, used by T14-S3's `ae_eq_chartWord_values_of_freeNear`)
needs the comparison approach to lie in the `B`-free components of `(ℍ ∖ A) ∩ B(p, r)` for both orders of the two
histories (T14-S3's open item 3, `hAccessOld` / `hAccessSecond`). Both follow from one clopen argument:

* `subset_image_halfDisc_of_isPreconnected`: a connected set meeting the image of an open upper half-disc and missing
  the image of its boundary stays in the image;
* `exists_le_nhdsWithin_freeNear`: if the real diameter maps into `S` and the upper semicircle misses `g(x)`, the
  approach `g_*(𝓝[ℍ] x)` is in the `T`-free components of `(ℍ ∖ S) ∩ B(g(x), r)` for small `r`;
* `exists_access_of_lifted_arc`: on a lifted common arc (real, increasing), the hypotheses hold for a shrunken collar;
* **`exists_s3_geometry_of_s2`**: on S2's lift, for every common arc ending at an interior tip of the second trace:
  side, joint domain and joint-domain limit of the approach; both component accesses for arbitrary `S, T` inside the
  joint fill; and the second chart's normalized map-out, its left limit `y + w(q)` (`y < 0`, `Φ_q(y)` the physical
  point) and its transition gap, in exactly the form of `S3.JointPhaseGaps`'s second chart.

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.S3.Geo

open Supp9B (IsProperCurve leftSide closedRightSide)
open Sec7.ReverseArc

/-- **A connected set meeting the image of a half-disc and missing the image of its boundary stays inside.**
Clopen argument: the image of the open half-disc is open, the image of the closed half-disc is compact. -/
theorem subset_image_halfDisc_of_isPreconnected {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) {x : ℂ}
    {ρ : ℝ} (hU : IsOpen (g '' (ball x ρ ∩ H))) {C : Set ℂ} (hC : IsPreconnected C)
    (hne : (C ∩ g '' (ball x ρ ∩ H)).Nonempty)
    (hmiss : ∀ w ∈ closedBall x ρ, 0 ≤ w.im → w ∉ ball x ρ ∩ H → g w ∉ C) :
    C ⊆ g '' (ball x ρ ∩ H) := by
  have hK : IsCompact (closedBall x ρ ∩ {z : ℂ | 0 ≤ z.im}) :=
    (isCompact_closedBall x ρ).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hgK : IsClosed (g '' (closedBall x ρ ∩ {z : ℂ | 0 ≤ z.im})) :=
    (hK.image_of_continuousOn (hgc.mono inter_subset_right)).isClosed
  refine hC.subset_left_of_subset_union hU hgK.isOpen_compl ?_ ?_ hne
  · rw [Set.disjoint_left]
    rintro _ ⟨w, hw, rfl⟩ hcon
    exact hcon ⟨w, ⟨ball_subset_closedBall hw.1, show (0 : ℝ) ≤ w.im from le_of_lt hw.2⟩, rfl⟩
  · intro z hz
    by_cases hzK : z ∈ g '' (closedBall x ρ ∩ {z : ℂ | 0 ≤ z.im})
    · obtain ⟨w, hw, rfl⟩ := hzK
      by_cases hwU : w ∈ ball x ρ ∩ H
      · exact Or.inl ⟨w, hwU, rfl⟩
      · exact absurd hz (hmiss w hw.1 hw.2 hwU)
    · exact Or.inr hzK

/-- **Component access at a lifted boundary point** (the deterministic core of T14-S3's `hAccessOld` /
`hAccessSecond`). Let `g` be continuous on `ℍ̄`, `x` real, and let the image `U` of the upper half-disc of radius `ρ`
at `x` be open and miss `S ∪ T`. If `g` sends the real diameter into `S` and no point of the closed upper semicircle
to `g(x)`, then for some `r > 0` the approach `g_*(𝓝[ℍ] x)` is in the `T`-free components of `(ℍ ∖ S) ∩ B(g(x), r)`:
every such component through a point of `U` stays in `U`. -/
theorem exists_le_nhdsWithin_freeNear {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) {x ρ : ℝ} (hρ : 0 < ρ)
    (hU : IsOpen (g '' (ball (x : ℂ) ρ ∩ H))) {S T : Set ℂ}
    (hUST : g '' (ball (x : ℂ) ρ ∩ H) ⊆ H \ (S ∪ T)) (hseg : ∀ y : ℝ, |y - x| ≤ ρ → g y ∈ S)
    (hsph : ∀ w : ℂ, dist w x = ρ → 0 ≤ w.im → g w ≠ g x) :
    ∃ r > 0, map g (𝓝[H] (x : ℂ)) ≤ 𝓝[FinRel.freeNear T S (g x) r] (g x) := by
  set Z := g '' (sphere (x : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im}) with hZ
  have hSc : IsCompact (sphere (x : ℂ) ρ ∩ {z : ℂ | 0 ≤ z.im}) :=
    (isCompact_sphere (x : ℂ) ρ).inter_right (isClosed_le continuous_const Complex.continuous_im)
  have hZc : IsClosed Z := (hSc.image_of_continuousOn (hgc.mono inter_subset_right)).isClosed
  have hxZ : g x ∉ Z := by
    rintro ⟨w, hw, hgw⟩
    exact hsph w (mem_sphere.1 hw.1) hw.2 hgw
  obtain ⟨r, hr, hrZ⟩ := Metric.isOpen_iff.1 hZc.isOpen_compl (g x) hxZ
  refine ⟨r, hr, ?_⟩
  have hfree : ∀ z ∈ g '' (ball (x : ℂ) ρ ∩ H) ∩ ball (g x) r, z ∈ FinRel.freeNear T S (g x) r := by
    rintro z ⟨hzU, hzr⟩
    have hzST := hUST hzU
    have hzD : z ∈ (H \ S) ∩ ball (g x) r := ⟨⟨hzST.1, fun h => hzST.2 (Or.inl h)⟩, hzr⟩
    refine ⟨hzD, ?_⟩
    have hsub : connectedComponentIn ((H \ S) ∩ ball (g x) r) z ⊆ g '' (ball (x : ℂ) ρ ∩ H) := by
      refine subset_image_halfDisc_of_isPreconnected hgc hU (isPreconnected_connectedComponentIn)
        ⟨z, mem_connectedComponentIn hzD, hzU⟩ fun w hw hw0 hwU hwC => ?_
      have hwC' := connectedComponentIn_subset _ _ hwC
      rcases hw0.lt_or_eq with hpos | hzero
      · have hwd : dist w x = ρ := le_antisymm (mem_closedBall.1 hw) (not_lt.1 fun h => hwU ⟨h, hpos⟩)
        exact hrZ hwC'.2 ⟨w, ⟨mem_sphere.2 hwd, hw0⟩, rfl⟩
      · have hwr : w = (w.re : ℂ) := Complex.ext rfl (by simp only [Complex.ofReal_im, ← hzero])
        have hre : |w.re - x| ≤ ρ := by
          have h1 : |(w - (x : ℂ)).re| ≤ ‖w - (x : ℂ)‖ := Complex.abs_re_le_norm _
          rw [Complex.sub_re, Complex.ofReal_re] at h1
          exact h1.trans (by rw [← dist_eq_norm]; exact mem_closedBall.1 hw)
        have hS := hseg w.re hre
        rw [← hwr] at hS
        exact hwC'.1.2 hS
    rw [Set.disjoint_left]
    intro u hu huT
    exact (hUST (hsub hu)).2 (Or.inr huT)
  have hlim : Tendsto g (𝓝[H] (x : ℂ)) (𝓝 (g x)) :=
    ((hgc (x : ℂ) (by simp)).tendsto).mono_left (nhdsWithin_mono _ fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz)
  refine le_inf hlim (le_principal_iff.2 ?_)
  rw [mem_map]
  filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ), self_mem_nhdsWithin,
    hlim (ball_mem_nhds (g x) hr)] with w hw hwH hwr
  exact hfree (g w) ⟨⟨w, ⟨hw.2, hwH⟩, rfl⟩, hwr⟩

/-- **Component access on S2's lifted common arc.** Let `g` be the inverse extension of a domain chart, `γ` a lift
of an injective curve `β` (`g ∘ γ = β(t_L + ·)`), real on `[a, b]` with strictly increasing coordinate on `(a, b)`,
whose arc `β(t_L + [a, b])` lies in `S`, and let a half-disc collar at `γ(t)` be mapped off a set `J ⊇ S ∪ T`. Then
for some `r > 0` the approach `g_*(𝓝[ℍ] γ(t))` lies in the `T`-free components of `(ℍ ∖ S) ∩ B(β(t_L + t), r)`.

Proof. Shrink the collar to a half-disc whose real diameter is covered by the lifted arc (intermediate values between
two lifted arc points on either side of `t`): its image is in `S`; its upper semicircle misses `β(t_L + t)` (inside
the old collar the image is off `J ∋ β(t_L + t)`; at the two real ends by injectivity of `β`). Apply
`exists_le_nhdsWithin_freeNear`. -/
theorem exists_access_of_lifted_arc {D S T J : Set ℂ} {c : Chart} {g : ℂ → ℂ} (hc : IsDomainChart D c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {β γ : ℝ≥0 → ℂ} (hβi : Function.Injective β)
    (hγc : Continuous γ) {tL a b t : ℝ≥0} (ht : t ∈ Ioo a b) (hreal : ∀ s ∈ Icc a b, (γ s).im = 0)
    (hmono : StrictMonoOn (fun s => (γ s).re) (Ioo a b)) (hlift : ∀ s, g (γ s) = β (tL + s))
    (harc : ∀ s ∈ Icc a b, β (tL + s) ∈ S) (hSJ : S ⊆ J) (hTJ : T ⊆ J) {ρ : ℝ} (hρ : 0 < ρ)
    (hcol : g '' (ball (γ t) ρ ∩ H) ⊆ H \ J) :
    ∃ r > 0, map g (𝓝[H] (γ t)) ≤ 𝓝[FinRel.freeNear T S (β (tL + t)) r] (β (tL + t)) := by
  obtain ⟨s₁, hs₁a, hs₁t⟩ := exists_between ht.1
  obtain ⟨s₂, hs₂t, hs₂b⟩ := exists_between ht.2
  have hs₁ : s₁ ∈ Ioo a b := ⟨hs₁a, hs₁t.trans ht.2⟩
  have hs₂ : s₂ ∈ Ioo a b := ⟨ht.1.trans hs₂t, hs₂b⟩
  set x : ℝ := (γ t).re with hx
  have hγt : γ t = (x : ℂ) := Complex.ext (by rw [Complex.ofReal_re])
    (by rw [Complex.ofReal_im]; exact hreal t (Ioo_subset_Icc_self ht))
  have h₁ : (γ s₁).re < x := hmono hs₁ ht hs₁t
  have h₂ : x < (γ s₂).re := hmono ht hs₂ hs₂t
  set m : ℝ := min (x - (γ s₁).re) ((γ s₂).re - x) with hm
  have hm0 : 0 < m := lt_min (sub_pos.2 h₁) (sub_pos.2 h₂)
  set ρ' : ℝ := min (ρ / 2) (m / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_min (by linarith) (by linarith)
  have hρ'ρ : ρ' < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρ'm : ρ' < m := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hm1 : m ≤ x - (γ s₁).re := min_le_left _ _
  have hm2 : m ≤ (γ s₂).re - x := min_le_right _ _
  have hivt : ∀ y : ℝ, |y - x| ≤ ρ' → ∃ s ∈ Icc s₁ s₂, γ s = (y : ℂ) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := abs_le.1 hy
    obtain ⟨s, hs, hsy⟩ := intermediate_value_Icc (hs₁t.trans hs₂t).le
      ((Complex.continuous_re.comp hγc).continuousOn) (show y ∈ Icc (γ s₁).re (γ s₂).re from
        ⟨by linarith, by linarith⟩)
    have hsab : s ∈ Icc a b := ⟨hs₁a.le.trans hs.1, hs.2.trans hs₂b.le⟩
    refine ⟨s, hs, Complex.ext ?_ ?_⟩
    · rw [Complex.ofReal_re]; exact hsy
    · rw [Complex.ofReal_im]; exact hreal s hsab
  have hU : IsOpen (g '' (ball (x : ℂ) ρ' ∩ H)) := by
    have heq : g '' (ball (x : ℂ) ρ' ∩ H) = D ∩ c.1 ⁻¹' (ball (x : ℂ) ρ' ∩ H) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [hgi hw.2]
        exact ⟨hc.inv_mem hw.2, by rw [mem_preimage, hc.fwd_inv hw.2]; exact hw⟩
      · rintro ⟨hzD, hz⟩
        exact ⟨c.1 z, hz, by rw [hgi hz.2, hc.inv_fwd hzD]⟩
    rw [heq]
    exact hc.differentiableOn_fwd.continuousOn.isOpen_inter_preimage hc.isOpen
      (isOpen_ball.inter QuantumZipper.isOpen_H)
  have hsub : ball (x : ℂ) ρ' ⊆ ball (γ t) ρ := by
    rw [hγt]; exact ball_subset_ball hρ'ρ.le
  have hcol' : g '' (ball (x : ℂ) ρ' ∩ H) ⊆ H \ (S ∪ T) := by
    rintro _ ⟨w, hw, rfl⟩
    have h := hcol ⟨w, ⟨hsub hw.1, hw.2⟩, rfl⟩
    exact ⟨h.1, fun h' => h.2 (h'.elim (fun h'' => hSJ h'') (fun h'' => hTJ h''))⟩
  have hseg : ∀ y : ℝ, |y - x| ≤ ρ' → g y ∈ S := by
    intro y hy
    obtain ⟨s, hs, hsy⟩ := hivt y hy
    rw [← hsy, hlift]
    exact harc s ⟨hs₁a.le.trans hs.1, hs.2.trans hs₂b.le⟩
  have hgx : g (x : ℂ) = β (tL + t) := by rw [← hγt]; exact hlift t
  have hsph : ∀ w : ℂ, dist w x = ρ' → 0 ≤ w.im → g w ≠ g x := by
    intro w hw hw0 he
    rw [hgx] at he
    rcases hw0.lt_or_eq with hpos | hzero
    · have hwb : w ∈ ball (γ t) ρ := by
        rw [hγt, mem_ball, hw]; exact hρ'ρ
      have h := hcol ⟨w, ⟨hwb, hpos⟩, rfl⟩
      rw [he] at h
      exact h.2 (hSJ (harc t (Ioo_subset_Icc_self ht)))
    · have hwr : w = (w.re : ℂ) := Complex.ext (by rw [Complex.ofReal_re])
        (by rw [Complex.ofReal_im]; exact hzero.symm)
      have hd : dist w x = |w.re - x| := by
        rw [hwr, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          Complex.ofReal_re]
      obtain ⟨s, -, hsy⟩ := hivt w.re (by rw [← hd, hw])
      rw [hwr, ← hsy, hlift] at he
      have hst : s = t := add_left_cancel (hβi he)
      rw [hst, hγt] at hsy
      have hxw : x = w.re := Complex.ofReal_injective hsy
      rw [hd, ← hxw, sub_self, abs_zero] at hw
      exact hρ'0.ne hw
  obtain ⟨r, hr, hle⟩ := exists_le_nhdsWithin_freeNear hgc hρ'0 hU hcol' hseg hsph
  rw [hgx] at hle
  exact ⟨r, hr, by rw [hγt]; exact hle⟩

/-- **The S3 geometry on S2's lift** (Lemma S3, p. 580, all deterministic inputs of `S3.JointPhaseGaps` and of the
component form of Proposition 3.8). On the lift `γ` of S2 (`exists_positive_left_joint_collar_of_s2`), for every
common arc `β'(t_L + [a, b]) ⊆ A` whose end `q = t_L + b` is an interior tip of the second trace `η` (agreeing with
the witness `β'` up to `q`), and every `t ∈ (a, b)`, the approach `F = g_*(𝓝[ℍ] γ(t))`:

* is nontrivial, on the left of `β'`, in the joint domain `ℍ ∖ fill(A ∪ η[0, q])`, and tends to `η(t_L + t)`
  within it (`joint_domain` of `ProtectedWordComparison`);
* lies in the `T`-free components of `(ℍ ∖ S) ∩ B(η(t_L + t), r)` for some `r > 0`, for **any** `S ⊇` the common
  arc and `S, T ⊆ fill(A ∪ η[0, q])` (both access conditions `hAccessOld`, `hAccessSecond` of T14-S3);
* has, for the normalized mapping-out map `g₂ = f_q + w(q)` of `fill(η[0, q])`, the limit `y + w(q)` from `ℍ` with
  `y < 0` and `Φ_q(y) = η(t_L + t)` (the exposed **left** side of the second path), and a ball about `y + w(q)` misses
  `g₂(fill(A ∪ η[0, q]) ∖ fill(η[0, q]))` (the second transition gap). -/
theorem exists_s3_geometry_of_s2 {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    {β' : ℝ≥0 → ℂ} (hβ' : IsProperCurve β') (hβ'0 : β' 0 = 0) (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    {c : Chart} {g : ℂ → ℂ} (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite)
    {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ}) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
      β' tL = realMin (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧ (∀ s, g (γ s) = β' (tL + s)) ∧
      ∀ a b t : ℝ≥0, t ∈ Ioo a b → β' '' Icc (tL + a) (tL + b) ⊆ p '' Icc 0 1 →
        ((tL + b : ℝ≥0) : ℝ≥0∞) < ζ → η (tL + b) ∈ H → (∀ s ≤ tL + b, β' s = η s) →
        0 < (γ t).re ∧ (𝓝[H] (γ t)).NeBot ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (leftSide β' ∩ (H \ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b)))) ∧
        Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[H \ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b))] (η (tL + t)) ∧
        (∀ S T : Set ℂ, β' '' Icc (tL + a) (tL + b) ⊆ S →
          S ⊆ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b)) → T ⊆ fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b)) →
          ∃ r > 0, Filter.map g (𝓝[H] (γ t)) ≤ 𝓝[FinRel.freeNear T S (η (tL + t)) r] (η (tL + t))) ∧
        IsMapOut (fillH (η '' Icc 0 (tL + b)))
          (fun z => fwdMap (fun r : ℝ => w r.toNNReal) (tL + b) z + w (tL + b)) ∧
        ∃ y : ℝ, y < 0 ∧ extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) (tL + b)) y = η (tL + t) ∧
          Tendsto (fun z => fwdMap (fun r : ℝ => w r.toNNReal) (tL + b) z + w (tL + b))
            (Filter.map g (𝓝[H] (γ t))) (𝓝[H] ((y + w (tL + b) : ℝ) : ℂ)) ∧
          ∃ r > 0, Disjoint (ball ((y + w (tL + b) : ℝ) : ℂ) r)
            ((fun z => fwdMap (fun r : ℝ => w r.toNNReal) (tL + b) z + w (tL + b)) ''
              (fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b)) \ fillH (η '' Icc 0 (tL + b)))) := by
  obtain ⟨tL, γ, htL, hγp, hγ0, hlift, hall⟩ :=
    exists_second_geometry_of_s2 hp hp0 hpH hβ' hβ'0 hA hc hgc hgi hgf hη hw hw0 hinj
  refine ⟨tL, γ, htL, hγp, hγ0, hlift, fun a b t ht harc hqζ hqH hag => ?_⟩
  obtain ⟨hpos, hne, hFL, hgt, y, hy0, hfFH, hΦy, r, hr, hgap⟩ := hall a b t ht harc hqζ hqH hag
  set q : ℝ≥0 := tL + b with hqdef
  set A : Set ℂ := p '' Icc 0 1 with hAdef
  set J : Set ℂ := fillH (A ∪ η '' Icc 0 q) with hJdef
  set f := fwdMap (fun r : ℝ => w r.toNNReal) q with hfdef
  have hab : a < b := ht.1.trans ht.2
  have hq0 : 0 < q := lt_of_lt_of_le (lt_of_le_of_lt zero_le hab) le_add_self
  obtain ⟨-, -, -, hmo, -, -⟩ := secondChart_facts hη hw hw0 hinj hqζ hq0
  have hD := hc.1
  have harc' : ∀ s ∈ Icc a b, g (γ s) ∈ A := fun s hs => by
    rw [hlift s]; exact harc ⟨tL + s, ⟨add_le_add le_rfl hs.1, add_le_add le_rfl hs.2⟩, rfl⟩
  have hreal : ∀ s ∈ Icc a b, (γ s).im = 0 := fun s hs =>
    im_eq_zero_of_landing_mem hD hgi (hγp.2.2.1 s) (harc' s hs)
  have hmono : StrictMonoOn (fun s => (γ s).re) (Ioo a b) :=
    strictMonoOn_re_of_lifted_common_arc hp hp0 hc hgc hgi hγp hγ0
      (by rintro _ ⟨s, hs, rfl⟩; exact harc' s ⟨hs.1.le, hs.2.le⟩)
  have hFJ : Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (H \ J) := hFL.trans (principal_mono.2 inter_subset_right)
  have hcolJ : ∃ ρ > 0, g '' (ball (γ t) ρ ∩ H) ⊆ H \ J := by
    have hmem : g ⁻¹' (H \ J) ∈ 𝓝[H] (γ t) := mem_map.1 (hFJ (mem_principal_self _))
    obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hmem
    exact ⟨ρ, hρ, by rintro _ ⟨u, hu, rfl⟩; exact hsub hu⟩
  have htq : tL + t ≤ q := add_le_add le_rfl ht.2.le
  have htrans : Tendsto (fun v : ℂ => v + ((w q : ℝ) : ℂ)) (𝓝[H] (y : ℂ)) (𝓝[H] ((y + w q : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc' : Continuous fun v : ℂ => v + ((w q : ℝ) : ℂ) := continuous_id.add continuous_const
      have h := (hc'.tendsto (y : ℂ)).mono_left (nhdsWithin_le_nhds (s := H))
      rwa [← Complex.ofReal_add] at h
    · filter_upwards [self_mem_nhdsWithin] with v hv
      show (0 : ℝ) < (v + ((w q : ℝ) : ℂ)).im
      rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hv
  refine ⟨hpos, hne, hFL, le_inf hgt hFJ, fun S T hS hSJ hTJ => ?_, hmo, y, hy0, hΦy,
    htrans.comp hfFH, r, hr, ?_⟩
  · obtain ⟨ρ, hρ, hcol⟩ := hcolJ
    obtain ⟨r', hr', hle⟩ := exists_access_of_lifted_arc hD hgc hgi hβ'.2.1 hγp.1 ht hreal hmono hlift
      (fun s hs => hS ⟨tL + s, ⟨add_le_add le_rfl hs.1, add_le_add le_rfl hs.2⟩, rfl⟩) hSJ hTJ hρ hcol
    rw [hag (tL + t) htq] at hle
    exact ⟨r', hr', hle⟩
  · rw [Set.disjoint_left]
    rintro _ hu ⟨z, hz, rfl⟩
    refine Set.disjoint_left.1 hgap ?_ ⟨z, hz, rfl⟩
    rw [mem_ball, Complex.dist_eq] at hu ⊢
    have he : ∀ v : ℂ, v + ((w q : ℝ) : ℂ) - ((y + w q : ℝ) : ℂ) = v - (y : ℂ) := fun v => by
      rw [Complex.ofReal_add]; ring
    simp only [he] at hu
    exact hu

end InteractingSLE.Theorem14.SB.S3.Geo
