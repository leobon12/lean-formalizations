/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior
import InteractingSLE.Spec.Sec7.ContinuityProb2Join

/-!
# A.3.2: the crosscut property as countably many conditions on boundary values

Packet PROVE-ZHAN-A35. Source: Astra, *Follow-up proofs and dependency audit*, §A.3 (`ig1_followup_proofs.txt`
L648–L655, ruling R38): at the first swallowing time `σ`, `∂(ℍ \ K_σ) ∩ ℍ` "is a simple crosscut with finite real
endpoints on opposite sides of zero". To transfer this through the mixture identity (G3) it must be a measurable
property of the strip path; here it is reduced, deterministically, to countably many conditions on the boundary values
`F(v)` of the inverse map `f_σ` at **rational** real points `v`.

* `BdryCode F`: (1) `F` separates disjoint rational intervals by a positive distance, (2) the set `O = {Im F > 0}`
  contains every rational interval whose ends lie in it, with a positive lower bound, (3) the real values of `F`
  left of `O` are `≤ −1 − 1/(k+1)`, right of `O` are `≥ 1/(k+1)`, (4) `O` contains a rational point.
* `IsBdryExt W σ F`: `F` extends `f_σ` continuously to `ℍ̄` and sends no real point into `ℍ \ K_σ`.
* `frontier_eq_range`: then `∂(ℍ \ K_σ) = F(ℝ)`.
* **`bdryCode_of_crosscut`** (crosscut ⇒ code): if `∂(ℍ \ K_σ) ∩ ℍ = γ((0, 1))` for a simple crosscut with
  `γ 0 < −1` and `γ 1 > 0`, the code holds.
* **`exists_crosscut_of_bdryCode`** (code ⇒ crosscut): conversely the code gives such a crosscut, `γ = F` on `[c, d]`,
  `(c, d) = O`.
* `isBdryExt_of_crosscut`: a crosscut boundary gives the extension (`K_σ` is the filling of the crosscut; Torhorst for
  path complements, `Sec7.exists_extension_of_fwdHull_eq`).

All arguments are elementary topology on top of the boundary-injectivity theorem `injective_of_frontier_eq_crosscut`
(PROVE-ZHAN-GT4-A2) and the Jordan separation `IsCrosscutDomain.exists_inside`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A35

open QuantumZipper

/-- **The boundary code** of a function `F : ℝ → ℂ` (the boundary values of `f_σ` on the real line), read at rational
points only. -/
def BdryCode (F : ℝ → ℂ) : Prop :=
  (∀ a₁ b₁ a₂ b₂ : ℚ, b₁ < a₂ → ∃ k : ℕ, ∀ x y : ℚ, a₁ ≤ x → x ≤ b₁ → a₂ ≤ y → y ≤ b₂ →
      1 / ((k : ℝ) + 1) ≤ ‖F x - F y‖) ∧
  (∀ v₁ v₃ : ℚ, 0 < (F v₁).im → 0 < (F v₃).im → ∃ k : ℕ, ∀ v : ℚ, v₁ ≤ v → v ≤ v₃ →
      1 / ((k : ℝ) + 1) ≤ (F v).im) ∧
  (∃ k : ℕ, ∀ v w : ℚ, 0 < (F w).im → (F v).im = 0 →
      (v < w → (F v).re ≤ -1 - 1 / ((k : ℝ) + 1)) ∧ (w < v → 1 / ((k : ℝ) + 1) ≤ (F v).re)) ∧
  (∃ w : ℚ, 0 < (F w).im)

/-- The boundary code is a measurable condition on a family of functions measurable at every rational point. -/
theorem measurableSet_bdryCode {α : Type*} [MeasurableSpace α] {G : α → ℝ → ℂ}
    (hG : ∀ q : ℚ, Measurable fun a => G a q) : MeasurableSet {a | BdryCode (G a)} := by
  have hre : ∀ q : ℚ, Measurable fun a => (G a q).re := fun q => Complex.measurable_re.comp (hG q)
  have him : ∀ q : ℚ, Measurable fun a => (G a q).im := fun q => Complex.measurable_im.comp (hG q)
  refine measurableSet_setOfPred.2 (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_)))
  · refine Measurable.forall fun a₁ => Measurable.forall fun b₁ => Measurable.forall fun a₂ =>
      Measurable.forall fun b₂ => measurable_const.imp (Measurable.exists fun k => Measurable.forall fun x =>
        Measurable.forall fun y => measurable_const.imp (measurable_const.imp (measurable_const.imp
          (measurable_const.imp ?_))))
    exact measurableSet_setOfPred.1 (measurableSet_le measurable_const ((hG x).sub (hG y)).norm)
  · refine Measurable.forall fun v₁ => Measurable.forall fun v₃ =>
      (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (him v₁))).imp
        ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const (him v₃))).imp
          (Measurable.exists fun k => Measurable.forall fun v => measurable_const.imp
            (measurable_const.imp ?_)))
    exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (him v))
  · refine Measurable.exists fun k => Measurable.forall fun v => Measurable.forall fun w =>
      (measurableSet_setOfPred.1 (measurableSet_lt measurable_const (him w))).imp
        ((measurableSet_setOfPred.1 (measurableSet_eq_fun (him v) measurable_const)).imp
          (Measurable.and (measurable_const.imp ?_) (measurable_const.imp ?_)))
    · exact measurableSet_setOfPred.1 (measurableSet_le (hre v) measurable_const)
    · exact measurableSet_setOfPred.1 (measurableSet_le measurable_const (hre v))
  · exact Measurable.exists fun w => measurableSet_setOfPred.1 (measurableSet_lt measurable_const (him w))

/-! ### Rational approximation -/

/-- A closed property holding at the rational points of `(a, b)` holds on `[a, b]`. -/
theorem forall_Icc_of_forall_rat {p : ℝ → Prop} (hp : IsClosed {x | p x}) {a b : ℝ} (hab : a < b)
    (h : ∀ q : ℚ, a < q → (q : ℝ) < b → p q) {x : ℝ} (hx : x ∈ Icc a b) : p x := by
  have hsub : Ioo a b ⊆ closure ((fun q : ℚ => (q : ℝ)) '' {q : ℚ | a < q ∧ (q : ℝ) < b}) := by
    intro y hy
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max a (y - δ) < min b (y + δ) from
      max_lt (lt_min hab (by linarith [hy.1])) (lt_min (by linarith [hy.2]) (by linarith)))
    refine ⟨q, hball ?_, q, ⟨(le_max_left _ _).trans_lt hq1, hq2.trans_le (min_le_left _ _)⟩, rfl⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right a (y - δ), min_le_right b (y + δ)]
  have hcl : closure (Ioo a b) ⊆ {x | p x} := by
    refine (closure_mono hsub).trans ?_
    rw [closure_closure]
    exact closure_minimal (by rintro _ ⟨q, hq, rfl⟩; exact h q hq.1 hq.2) hp
  rw [closure_Ioo hab.ne] at hcl
  exact hcl hx

theorem exists_rat_mem_of_isOpen {O : Set ℝ} (hO : IsOpen O) (hne : O.Nonempty) : ∃ q : ℚ, (q : ℝ) ∈ O := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x hx
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - ε < x + ε by linarith)
  refine ⟨q, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### Boundary extensions of the inverse map -/

/-- **`F` is a boundary extension of `f_σ`**: continuous on `ℍ̄`, equal to `f_σ` on `ℍ`, and no real point is sent
into `ℍ \ K_σ`. -/
structure IsBdryExt (W : ℝ → ℝ) (σ : ℝ) (F : ℂ → ℂ) : Prop where
  eqOn : EqOn F (fwdMapInv W σ) H
  contOn : ContinuousOn F Hbar
  not_mem : ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W σ

section Ext

variable {W : ℝ → ℝ} {σ : ℝ} {F : ℂ → ℂ}

theorem ofReal_mem_Hbar (v : ℝ) : (v : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (v : ℂ).im by simp

theorem IsBdryExt.continuous_real (hF : IsBdryExt W σ F) : Continuous fun v : ℝ => F v :=
  hF.contOn.comp_continuous continuous_ofReal ofReal_mem_Hbar

theorem IsBdryExt.tendsto_real (hF : IsBdryExt W σ F) (v : ℝ) : Tendsto F (𝓝[H] (v : ℂ)) (𝓝 (F v)) :=
  (hF.contOn _ (ofReal_mem_Hbar v)).tendsto.mono_left (nhdsWithin_mono _ H_subset_Hbar)

theorem IsBdryExt.mem_closure (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 ≤ σ) (hF : IsBdryExt W σ F)
    (v : ℝ) : F v ∈ closure (H \ fwdHull W σ) := by
  have hne : (𝓝[H] (v : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  refine mem_closure_of_tendsto (hF.tendsto_real v) ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [hF.eqOn hz]
  exact RS.fwdMapInv_mem_compl_fwdHull hW hW0 hσ hz

theorem IsBdryExt.mem_frontier (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 ≤ σ) (hF : IsBdryExt W σ F)
    (v : ℝ) : F v ∈ frontier (H \ fwdHull W σ) := by
  rw [(FwdHolo.isOpen_compl_fwdHull hW hσ).frontier_eq]
  exact ⟨hF.mem_closure hW hW0 hσ v, hF.not_mem v (by simp)⟩

theorem IsBdryExt.mem_Hbar (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 ≤ σ) (hF : IsBdryExt W σ F)
    (v : ℝ) : F v ∈ Hbar := by
  have h := closure_mono (show H \ fwdHull W σ ⊆ H from sdiff_subset) (hF.mem_closure hW hW0 hσ v)
  rwa [closure_H] at h

theorem IsBdryExt.im_nonneg (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 ≤ σ) (hF : IsBdryExt W σ F)
    (v : ℝ) : 0 ≤ (F v).im := hF.mem_Hbar hW hW0 hσ v

theorem IsBdryExt.exists_norm_sub_le (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 ≤ σ) (hF : IsBdryExt W σ F) :
    ∃ C, ∀ u ∈ Hbar, ‖F u - u‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hσ
  refine ⟨C, fun u hu => ?_⟩
  have hne : (𝓝[H] u).NeBot := by rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]; exact hu
  have ht : Tendsto (fun z => ‖F z - z‖) (𝓝[H] u) (𝓝 ‖F u - u‖) :=
    (((hF.contOn u hu).tendsto.mono_left (nhdsWithin_mono _ H_subset_Hbar)).sub
      (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  refine le_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [hF.eqOn hz]; exact hC z hz

/-- **The boundary of `ℍ \ K_σ` is the image of the real line** under a boundary extension. -/
theorem IsBdryExt.frontier_eq_range (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 ≤ σ) (hF : IsBdryExt W σ F) :
    frontier (H \ fwdHull W σ) = range fun v : ℝ => F v := by
  refine Subset.antisymm (fun z hz => ?_) (by rintro _ ⟨v, rfl⟩; exact hF.mem_frontier hW hW0 hσ v)
  set D := H \ fwdHull W σ with hD
  have hDo : IsOpen D := FwdHolo.isOpen_compl_fwdHull hW hσ
  rw [hDo.frontier_eq] at hz
  obtain ⟨y, hyD, hyz⟩ := mem_closure_iff_seq_limit.1 hz.1
  have hyim : ∀ n, ∃ w ∈ H, fwdMapInv W σ w = y n := fun n => by
    have := hyD n; rw [hD, ← RS.image_fwdMapInv_H hW hW0 hσ] at this; exact this
  choose w hwH hwy using hyim
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hσ
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto y hyz).exists_norm_le
  have hwb : ∀ n, w n ∈ closedBall (0 : ℂ) (R + C) := fun n => by
    rw [mem_closedBall, dist_zero_right]
    have h1 := hC (w n) (hwH n)
    rw [hwy n] at h1
    have h2 := hR (y n) ⟨n, rfl⟩
    have h3 := norm_sub_norm_le (w n) (y n)
    rw [norm_sub_rev] at h1
    linarith
  obtain ⟨w₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hwb
  have hw₀ : w₀ ∈ Hbar := isClosed_Hbar.mem_of_tendsto hlim (Eventually.of_forall fun n => H_subset_Hbar (hwH _))
  have hFw : Tendsto (fun n => F (w (φ n))) atTop (𝓝 (F w₀)) := (hF.contOn w₀ hw₀).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => H_subset_Hbar (hwH _)⟩)
  have hFy : Tendsto (fun n => F (w (φ n))) atTop (𝓝 z) := by
    refine (hyz.comp hφ.tendsto_atTop).congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hF.eqOn (hwH _), hwy]
  have hz' : F w₀ = z := tendsto_nhds_unique hFw hFy
  by_cases hw₀H : w₀ ∈ H
  · exact absurd (show z ∈ D by
      rw [← hz', hF.eqOn hw₀H]; exact RS.fwdMapInv_mem_compl_fwdHull hW hW0 hσ hw₀H) hz.2
  · have him : w₀.im = 0 := le_antisymm (not_lt.1 hw₀H) hw₀
    refine ⟨w₀.re, ?_⟩
    show F (w₀.re : ℂ) = z
    rw [← hz']
    congr 1
    exact Complex.ext (by simp) (by simp [him])

end Ext

/-! ### Crosscut ⇒ code -/

section Crosscut

variable {W : ℝ → ℝ} {σ : ℝ} {F : ℂ → ℂ}

/-- Real points strictly between the ends of the crosscut are not boundary points of the crosscut domain. -/
theorem not_mem_frontier_of_mem_Ioo {D : Set ℂ} {γ : ℝ → ℂ} (hD : IsCrosscutDomain D γ) {x : ℝ}
    (hx : x ∈ Ioo (γ 0).re (γ 1).re) : (x : ℂ) ∉ frontier D := by
  obtain ⟨V, hVo, -, hVH, hVD, -, hfrV, -⟩ := hD.exists_inside
  obtain ⟨r, hr, hball⟩ := hD.exists_ball_inter_H_subset_inside hVo hVH hfrV hx
  intro hfr
  have hcl : (x : ℂ) ∈ closure D := frontier_subset_closure hfr
  rw [mem_closure_iff_nhds] at hcl
  obtain ⟨z, hzb, hzD⟩ := hcl (ball (x : ℂ) r) (ball_mem_nhds _ hr)
  exact Set.disjoint_left.1 hVD (hball ⟨hzb, hD.subset_H hzD⟩) hzD

/-- A continuous `g : ℝ → ℂ` with `|Re g v − v|` bounded is a closed map. -/
theorem isClosedMap_of_abs_re_sub_le {g : ℝ → ℂ} (hgc : Continuous g) {C : ℝ}
    (hgC : ∀ v : ℝ, |(g v).re - v| ≤ C) : IsClosedMap g := by
  intro S hS
  refine isClosed_iff_clusterPt.2 fun z hz => ?_
  have hz' : z ∈ closure (g '' S) := mem_closure_iff_clusterPt.2 hz
  obtain ⟨y, hyS, hyz⟩ := mem_closure_iff_seq_limit.1 hz'
  choose s hsS hsy using hyS
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto y hyz).exists_norm_le
  have hsb : ∀ n, s n ∈ closedBall (0 : ℝ) (R + C) := fun n => by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    have h2 : ‖g (s n)‖ ≤ R := by rw [hsy n]; exact hR (y n) ⟨n, rfl⟩
    have h3 := abs_le.1 ((Complex.abs_re_le_norm (g (s n))).trans h2)
    have h1 := abs_le.1 (hgC (s n))
    rw [abs_le]; constructor <;> linarith
  obtain ⟨s₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hsb
  have hs₀ : s₀ ∈ S := hS.mem_of_tendsto hlim (Eventually.of_forall fun n => hsS _)
  have h1 : Tendsto (fun n => g (s (φ n))) atTop (𝓝 (g s₀)) := (hgc.tendsto s₀).comp hlim
  have h2 : Tendsto (fun n => g (s (φ n))) atTop (𝓝 z) :=
    (hyz.comp hφ.tendsto_atTop).congr fun n => by simp only [Function.comp_apply, hsy]
  exact ⟨s₀, hs₀, tendsto_nhds_unique h1 h2⟩

/-- **Crosscut ⇒ code.** If `∂(ℍ \ K_σ) ∩ ℍ` is the open part of a simple crosscut `γ` with `γ 0 < −1` and
`γ 1 > 0`, the boundary values of a boundary extension satisfy the boundary code. -/
theorem bdryCode_of_crosscut (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 < σ) (hF : IsBdryExt W σ F)
    {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (h0 : (γ 0).re < -1) (h1 : 0 < (γ 1).re)
    (hfr : frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1) : BdryCode fun v : ℝ => F v := by
  set g : ℝ → ℂ := fun v => F v with hg
  have hlt : (γ 0).re < (γ 1).re := by linarith
  have hD := isCrosscutDomain_of_frontier hW hW0 hσ hγ hlt hfr
  have hgc : Continuous g := hF.continuous_real
  have hinj : Function.Injective g :=
    injective_of_frontier_eq_crosscut hW hW0 hσ hF.eqOn hF.contOn hF.not_mem hγ hlt hfr
  have hrange := hF.frontier_eq_range hW hW0 hσ.le
  obtain ⟨C, hC⟩ := hF.exists_norm_sub_le hW hW0 hσ.le
  have hgC : ∀ v : ℝ, |(g v).re - v| ≤ C := fun v => by
    have := hC v (ofReal_mem_Hbar v)
    have h' := Complex.abs_re_le_norm (F v - v)
    simp only [sub_re, ofReal_re] at h'
    exact h'.trans this
  have himg : ∀ v, 0 ≤ (g v).im := hF.im_nonneg hW hW0 hσ.le
  -- `O = {v | g v ∈ ℍ}`
  set O : Set ℝ := {v | 0 < (g v).im} with hO
  have hOo : IsOpen O := isOpen_lt continuous_const (Complex.continuous_im.comp hgc)
  have hgO : g '' O = γ '' Ioo 0 1 := by
    rw [← hfr, hrange]
    ext z; constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, rfl⟩, hv⟩
    · rintro ⟨⟨v, rfl⟩, hv⟩; exact ⟨v, hv, rfl⟩
  have hOpc : IsPreconnected O := by
    have hind : Topology.IsInducing g :=
      (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hgc hinj
        (isClosedMap_of_abs_re_sub_le hgc hgC)).toIsInducing
    rw [← hind.isPreconnected_image, hgO]
    exact isPreconnected_Ioo.image _ (hγ.1.mono Ioo_subset_Icc_self)
  have hOc : OrdConnected O := hOpc.ordConnected
  -- the real values off `O` avoid `(γ 0, γ 1)`
  have hoff : ∀ v, v ∉ O → (g v).im = 0 ∧ ((g v).re ≤ (γ 0).re ∨ (γ 1).re ≤ (g v).re) := by
    intro v hv
    have him : (g v).im = 0 := le_antisymm (not_lt.1 hv) (himg v)
    refine ⟨him, ?_⟩
    by_contra hcon
    push Not at hcon
    have hmem : g v ∈ frontier (H \ fwdHull W σ) := by rw [hrange]; exact ⟨v, rfl⟩
    have heq : g v = ((g v).re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [heq] at hmem
    exact not_mem_frontier_of_mem_Ioo hD ⟨hcon.1, hcon.2⟩ hmem
  -- left of `O`: values `≤ γ 0`; right of `O`: values `≥ γ 1`
  have hleft : ∀ v w, w ∈ O → v ∉ O → v < w → (g v).re ≤ (γ 0).re := by
    intro v w hw hv hvw
    rcases (hoff v hv).2 with h | h
    · exact h
    exfalso
    set u := min v ((γ 0).re - C - 1) with hu
    have huv : u ≤ v := min_le_left _ _
    have hgu : (g u).re < (γ 0).re := by
      have := (abs_le.1 (hgC u)).2
      have : u ≤ (γ 0).re - C - 1 := min_le_right _ _
      linarith
    obtain ⟨u', hu', hval⟩ := intermediate_value_Icc huv
      ((Complex.continuous_re.comp hgc).continuousOn)
      (show ((γ 0).re + (γ 1).re) / 2 ∈ Icc (g u).re (g v).re from ⟨by linarith, by linarith⟩)
    have hu'O : u' ∉ O := fun hu'O => hv (hOc.out hu'O hw ⟨hu'.2, hvw.le⟩)
    rcases (hoff u' hu'O).2 with h' | h'
    · simp only [Function.comp_apply] at hval; linarith
    · simp only [Function.comp_apply] at hval; linarith
  have hright : ∀ v w, w ∈ O → v ∉ O → w < v → (γ 1).re ≤ (g v).re := by
    intro v w hw hv hwv
    rcases (hoff v hv).2 with h | h
    swap
    · exact h
    exfalso
    set u := max v ((γ 1).re + C + 1) with hu
    have hvu : v ≤ u := le_max_left _ _
    have hgu : (γ 1).re < (g u).re := by
      have := (abs_le.1 (hgC u)).1
      have : (γ 1).re + C + 1 ≤ u := le_max_right _ _
      linarith
    obtain ⟨u', hu', hval⟩ := intermediate_value_Icc hvu
      ((Complex.continuous_re.comp hgc).continuousOn)
      (show ((γ 0).re + (γ 1).re) / 2 ∈ Icc (g v).re (g u).re from ⟨by linarith, by linarith⟩)
    have hu'O : u' ∉ O := fun hu'O => hv (hOc.out hw hu'O ⟨hwv.le, hu'.1⟩)
    rcases (hoff u' hu'O).2 with h' | h'
    · simp only [Function.comp_apply] at hval; linarith
    · simp only [Function.comp_apply] at hval; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (1) separation of disjoint rational intervals
    intro a₁ b₁ a₂ b₂ hb
    by_cases hne : (a₁ : ℝ) ≤ b₁ ∧ (a₂ : ℝ) ≤ b₂
    · have hK : IsCompact (Icc (a₁ : ℝ) b₁ ×ˢ Icc (a₂ : ℝ) b₂) := isCompact_Icc.prod isCompact_Icc
      have hKne : (Icc (a₁ : ℝ) b₁ ×ˢ Icc (a₂ : ℝ) b₂).Nonempty :=
        ⟨((a₁ : ℝ), (a₂ : ℝ)), ⟨le_rfl, hne.1⟩, ⟨le_rfl, hne.2⟩⟩
      have hcont : ContinuousOn (fun p : ℝ × ℝ => ‖g p.1 - g p.2‖) (Icc (a₁ : ℝ) b₁ ×ˢ Icc (a₂ : ℝ) b₂) :=
        ((hgc.comp continuous_fst).sub (hgc.comp continuous_snd)).norm.continuousOn
      obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hKne hcont
      have hpos : 0 < ‖g p.1 - g p.2‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        intro heq
        have := hinj heq
        have h1 := hp.1.2; have h2 := hp.2.1
        have hb' : (b₁ : ℝ) < a₂ := by exact_mod_cast hb
        linarith [this ▸ h1]
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
      refine ⟨k, fun x y hx1 hx2 hy1 hy2 => ?_⟩
      have := hmin (show ((x : ℝ), (y : ℝ)) ∈ Icc (a₁ : ℝ) b₁ ×ˢ Icc (a₂ : ℝ) b₂ from
        ⟨⟨(by exact_mod_cast hx1 : (a₁ : ℝ) ≤ x), (by exact_mod_cast hx2 : (x : ℝ) ≤ b₁)⟩,
          ⟨(by exact_mod_cast hy1 : (a₂ : ℝ) ≤ y), (by exact_mod_cast hy2 : (y : ℝ) ≤ b₂)⟩⟩)
      exact hk.le.trans this
    · refine ⟨0, fun x y hx1 hx2 hy1 hy2 => absurd ⟨?_, ?_⟩ hne⟩
      · exact_mod_cast hx1.trans hx2
      · exact_mod_cast hy1.trans hy2
  · -- (2) the open set `O` is an interval
    intro v₁ v₃ hv₁ hv₃
    by_cases hle : (v₁ : ℝ) ≤ v₃
    · have hsub : Icc (v₁ : ℝ) v₃ ⊆ O := hOc.out hv₁ hv₃
      obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hle)
        ((Complex.continuous_im.comp hgc).continuousOn)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < (g p).im from hsub hp)
      refine ⟨k, fun v h1 h2 => hk.le.trans (hmin ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩)⟩
    · refine ⟨0, fun v h1 h2 => absurd ?_ hle⟩
      exact_mod_cast h1.trans h2
  · -- (3) the real values on both sides
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < min (-1 - (γ 0).re) (γ 1).re from
      lt_min (by linarith) h1)
    refine ⟨k, fun v w hw hv => ⟨fun hvw => ?_, fun hwv => ?_⟩⟩
    · have hvO : (v : ℝ) ∉ O := fun h => by
        have : (0 : ℝ) < (g v).im := h
        simp only [hg] at this; linarith
      have := hleft v w hw hvO (by exact_mod_cast hvw)
      simp only [hg] at this
      linarith [min_le_left (-1 - (γ 0).re) (γ 1).re]
    · have hvO : (v : ℝ) ∉ O := fun h => by
        have : (0 : ℝ) < (g v).im := h
        simp only [hg] at this; linarith
      have := hright v w hw hvO (by exact_mod_cast hwv)
      simp only [hg] at this
      linarith [min_le_right (-1 - (γ 0).re) (γ 1).re]
  · -- (4) `O` contains a rational point
    have hne : O.Nonempty := by
      have h : (γ '' Ioo 0 1).Nonempty := (nonempty_Ioo.2 one_pos).image γ
      rw [← hgO] at h
      obtain ⟨_, ⟨v, hv, -⟩⟩ := h
      exact ⟨v, hv⟩
    exact exists_rat_mem_of_isOpen hOo hne

end Crosscut

/-! ### Code ⇒ crosscut -/

section Code

variable {W : ℝ → ℝ} {σ : ℝ} {F : ℂ → ℂ}

/-- **Code ⇒ crosscut.** If the boundary values of a boundary extension of `f_σ` satisfy the boundary code, then
`∂(ℍ \ K_σ) ∩ ℍ` is the open part of a simple crosscut `γ` with `γ 0 < −1` and `γ 1 > 0` (`γ = F` on the closure
`[c, d]` of `{v | F v ∈ ℍ}`). -/
theorem exists_crosscut_of_bdryCode (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 < σ) (hF : IsBdryExt W σ F)
    (hc : BdryCode fun v : ℝ => F v) :
    ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re < -1 ∧ 0 < (γ 1).re ∧
      frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1 := by
  obtain ⟨hc1, hc2, ⟨k, hk⟩, ⟨w₀, hw₀⟩⟩ := hc
  set g : ℝ → ℂ := fun v => F v with hg
  have hgc : Continuous g := hF.continuous_real
  have himg : ∀ v, 0 ≤ (g v).im := hF.im_nonneg hW hW0 hσ.le
  have hrange := hF.frontier_eq_range hW hW0 hσ.le
  obtain ⟨C, hC⟩ := hF.exists_norm_sub_le hW hW0 hσ.le
  -- injectivity from (1)
  have hinj : Function.Injective g := by
    intro x y hxy
    by_contra hne
    wlog hlt : x < y generalizing x y
    · exact this hxy.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    obtain ⟨b₁, hb₁1, hb₁2⟩ := exists_rat_btwn hlt
    obtain ⟨a₂, ha₂1, ha₂2⟩ := exists_rat_btwn hb₁2
    obtain ⟨a₁, ha₁⟩ := exists_rat_lt x
    obtain ⟨b₂, hb₂⟩ := exists_rat_gt y
    obtain ⟨m, hm⟩ := hc1 a₁ b₁ a₂ b₂ (by exact_mod_cast ha₂1)
    have hstep : ∀ y' : ℚ, (a₂ : ℝ) < y' → (y' : ℝ) < b₂ → 1 / ((m : ℝ) + 1) ≤ ‖g x - g y'‖ := by
      intro y' h1 h2
      exact forall_Icc_of_forall_rat (p := fun x' => 1 / ((m : ℝ) + 1) ≤ ‖g x' - g y'‖)
        (isClosed_le continuous_const ((hgc.sub continuous_const).norm)) (show (a₁ : ℝ) < b₁ by linarith)
        (fun q h1' h2' => hm q y' (by exact_mod_cast h1'.le) (by exact_mod_cast h2'.le)
          (by exact_mod_cast h1.le) (by exact_mod_cast h2.le)) ⟨ha₁.le, hb₁1.le⟩
    have h := forall_Icc_of_forall_rat (p := fun y' => 1 / ((m : ℝ) + 1) ≤ ‖g x - g y'‖)
      (isClosed_le continuous_const ((continuous_const.sub hgc).norm)) (show (a₂ : ℝ) < b₂ by linarith)
      hstep ⟨ha₂2.le, hb₂.le⟩
    rw [hxy, sub_self, norm_zero] at h
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  -- the set `O = {g ∈ ℍ}`
  set O : Set ℝ := {v | 0 < (g v).im} with hO
  have hOo : IsOpen O := isOpen_lt continuous_const (Complex.continuous_im.comp hgc)
  have hOc : ∀ v₁ v₂ v₃, v₁ ∈ O → v₃ ∈ O → v₁ < v₂ → v₂ < v₃ → v₂ ∈ O := by
    intro v₁ v₂ v₃ h₁ h₃ h12 h23
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.isOpen_iff.1 hOo v₁ h₁
    obtain ⟨ε₃, hε₃, hb₃⟩ := Metric.isOpen_iff.1 hOo v₃ h₃
    obtain ⟨q₁, hq₁1, hq₁2⟩ := exists_rat_btwn (show v₁ - ε₁ < v₁ by linarith)
    obtain ⟨q₃, hq₃1, hq₃2⟩ := exists_rat_btwn (show v₃ < v₃ + ε₃ by linarith)
    have hq₁O : (q₁ : ℝ) ∈ O := hb₁ (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hq₃O : (q₃ : ℝ) ∈ O := hb₃ (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
    obtain ⟨m, hm⟩ := hc2 q₁ q₃ hq₁O hq₃O
    have h := forall_Icc_of_forall_rat (p := fun v => 1 / ((m : ℝ) + 1) ≤ (g v).im)
      (isClosed_le continuous_const (Complex.continuous_im.comp hgc)) (show (q₁ : ℝ) < q₃ by linarith)
      (fun q h1 h2 => hm q (by exact_mod_cast h1.le) (by exact_mod_cast h2.le))
      (show v₂ ∈ Icc (q₁ : ℝ) q₃ from ⟨by linarith, by linarith⟩)
    show 0 < (g v₂).im
    have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  -- `O` is bounded
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hW σ).exists_norm_le
  have hObd : ∀ v ∈ O, |v| ≤ R + C := by
    intro v hv
    have hmem : g v ∈ fwdHull W σ := by
      have hfr : g v ∈ frontier (H \ fwdHull W σ) := hF.mem_frontier hW hW0 hσ.le v
      rw [(FwdHolo.isOpen_compl_fwdHull hW hσ.le).frontier_eq] at hfr
      by_contra hK'
      exact hfr.2 ⟨hv, hK'⟩
    have h1 := hR _ hmem
    have h2 := hC v (ofReal_mem_Hbar v)
    have h3 : ‖((v : ℝ) : ℂ)‖ ≤ ‖g v‖ + ‖g v - v‖ := by
      calc ‖((v : ℝ) : ℂ)‖ = ‖g v - (g v - v)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖g v‖ + ‖g v - v‖ := norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h3
    simp only [hg] at h1 h3
    linarith
  have hOne : O.Nonempty := ⟨w₀, hw₀⟩
  have hbb : BddBelow O := ⟨-(R + C), fun v hv => by linarith [(abs_le.1 (hObd v hv)).1]⟩
  have hba : BddAbove O := ⟨R + C, fun v hv => by linarith [(abs_le.1 (hObd v hv)).2]⟩
  set c := sInf O with hcdef
  set d := sSup O with hddef
  have hOeq : O = Ioo c d := by
    ext v; constructor
    · intro hv
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOo v hv
      have h1 : v - ε / 2 ∈ O := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
      have h2 : v + ε / 2 ∈ O := hball (by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
      exact ⟨lt_of_le_of_lt (csInf_le hbb h1) (by linarith), lt_of_lt_of_le (by linarith) (le_csSup hba h2)⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨v₁, hv₁O, hv₁⟩ := exists_lt_of_csInf_lt hOne h1
      obtain ⟨v₃, hv₃O, hv₃⟩ := exists_lt_of_lt_csSup hOne h2
      exact hOc v₁ v v₃ hv₁O hv₃O hv₁ hv₃
  have hw₀' : (w₀ : ℝ) ∈ Ioo c d := hOeq ▸ hw₀
  have hcd : c < d := hw₀'.1.trans hw₀'.2
  have hcO : c ∉ O := by rw [hOeq]; exact fun h => lt_irrefl _ h.1
  have hdO : d ∉ O := by rw [hOeq]; exact fun h => lt_irrefl _ h.2
  have hoff : ∀ v, v ∉ O → (g v).im = 0 := fun v hv => le_antisymm (not_lt.1 hv) (himg v)
  -- the crosscut
  set γ : ℝ → ℂ := fun s => g (c + s * (d - c)) with hγdef
  have hdc : 0 < d - c := sub_pos.2 hcd
  have hγ0 : γ 0 = g c := by simp [hγdef]
  have hγ1 : γ 1 = g d := by simp [hγdef]
  have himage : γ '' Ioo 0 1 = g '' O := by
    rw [hOeq]
    ext z; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨c + s * (d - c), ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(v - c) / (d - c), ⟨div_pos (by linarith [hv.1]) hdc, (div_lt_one hdc).2 (by linarith [hv.2])⟩, ?_⟩
      simp only [hγdef]
      congr 1
      field_simp
      ring
  have hcross : IsRealCrosscut γ := by
    refine ⟨(hgc.comp (continuous_const.add (continuous_id.mul continuous_const))).continuousOn, ?_, ?_, ?_, ?_⟩
    · intro s _ t _ hst
      have := hinj hst
      have h' : s * (d - c) = t * (d - c) := by linarith
      exact mul_right_cancel₀ hdc.ne' h'
    · rw [himage]; rintro _ ⟨v, hv, rfl⟩; exact hv
    · rw [hγ0]; exact hoff c hcO
    · rw [hγ1]; exact hoff d hdO
  refine ⟨γ, hcross, ?_, ?_, ?_⟩
  · -- the left end is `≤ −1 − 1/(k+1)`
    rw [hγ0]
    have h := forall_Icc_of_forall_rat (p := fun v => (g v).re ≤ -1 - 1 / ((k : ℝ) + 1))
      (isClosed_le (Complex.continuous_re.comp hgc) continuous_const) (show c - 1 < c by linarith)
      (fun q h1 h2 => by
        have hqO : (q : ℝ) ∉ O := by rw [hOeq]; exact fun h => lt_asymm h.1 h2
        exact (hk q w₀ hw₀ (hoff q hqO)).1 (by exact_mod_cast h2.trans hw₀'.1))
      (show c ∈ Icc (c - 1) c from ⟨by linarith, le_rfl⟩)
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  · rw [hγ1]
    have h := forall_Icc_of_forall_rat (p := fun v => 1 / ((k : ℝ) + 1) ≤ (g v).re)
      (isClosed_le continuous_const (Complex.continuous_re.comp hgc)) (show d < d + 1 by linarith)
      (fun q h1 h2 => by
        have hqO : (q : ℝ) ∉ O := by rw [hOeq]; exact fun h => lt_asymm h.2 h1
        exact (hk q w₀ hw₀ (hoff q hqO)).2 (by exact_mod_cast hw₀'.2.trans h1))
      (show d ∈ Icc d (d + 1) from ⟨le_rfl, by linarith⟩)
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  · rw [hrange, himage]
    ext z; constructor
    · rintro ⟨⟨v, rfl⟩, hv⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, rfl⟩, hv⟩

end Code

/-! ### A crosscut boundary gives a boundary extension -/

section Fill

variable {W : ℝ → ℝ} {σ : ℝ}

/-- **The hull at a crosscut time is the filling of the crosscut.** -/
theorem fwdHull_eq_fillH_of_crosscut (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 < σ) {γ : ℝ → ℂ}
    (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re)
    (hfr : frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1) : fwdHull W σ = fillH (γ '' Icc 0 1) := by
  have hD := isCrosscutDomain_of_frontier hW hW0 hσ hγ hlt hfr
  obtain ⟨V, hVo, -, hVH, hVD, hHD, hfrV, -⟩ := hD.exists_inside
  set A := γ '' Icc 0 1 with hA
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hγ.1
  have hclA : closure A = A := hAc.isClosed.closure_eq
  set D := H \ fwdHull W σ with hDdef
  have hDo : IsOpen D := hD.isOpen
  have hAH : ∀ z ∈ A, z ∈ H → z ∈ γ '' Ioo 0 1 := by
    rintro _ ⟨s, hs, rfl⟩ hsH
    have hH : 0 < (γ s).im := hsH
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, rfl⟩
    · rintro rfl; rw [hγ.2.2.2.1] at hH; exact lt_irrefl 0 hH
    · rintro rfl; rw [hγ.2.2.2.2] at hH; exact lt_irrefl 0 hH
  have hDA : Disjoint D A := by
    refine Set.disjoint_left.2 fun z hzD hzA => ?_
    have hzfr : z ∈ frontier D ∩ H := by rw [hfr]; exact hAH z hzA hzD.1
    rw [hDo.frontier_eq] at hzfr
    exact hzfr.1.2 hzD
  have hKb : Bornology.IsBounded (fwdHull W σ) := isBounded_fwdHull hW σ
  ext z
  simp only [fillH, hclA, mem_ofPred_eq]
  constructor
  · intro hz
    refine ⟨hz.1, ?_⟩
    have hzHD : z ∈ H \ D := ⟨hz.1, fun h => h.2 hz⟩
    rcases hHD hzHD with hzV | hzγ
    · by_cases hzA : z ∈ A
      · exact Or.inl hzA
      right
      have hsub : connectedComponentIn (H \ A) z ⊆ V := by
        refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hVo isClosed_closure.isOpen_compl
          (Set.disjoint_left.2 fun x hx hx' => hx' (subset_closure hx)) (fun x hx => ?_)
          ⟨z, mem_connectedComponentIn ⟨hz.1, hzA⟩, hzV⟩
        by_cases hxV : x ∈ V
        · exact Or.inl hxV
        right
        intro hxcl
        have hxfr : x ∈ frontier V := ⟨hxcl, by rw [hVo.interior_eq]; exact hxV⟩
        rw [hfrV] at hxfr
        have hxs := connectedComponentIn_subset (H \ A) z hx
        rcases hxfr with hxA | ⟨t, -, hxt⟩
        · exact hxs.2 hxA
        · have : (0 : ℝ) < x.im := hxs.1
          rw [← hxt, crosscutSeg_im hγ] at this
          exact lt_irrefl 0 this
      have hVK : V ⊆ fwdHull W σ := fun x hx => by
        by_contra hxK
        exact Set.disjoint_left.1 hVD hx ⟨hVH hx, hxK⟩
      exact hKb.subset (hsub.trans hVK)
    · exact Or.inl (image_mono Ioo_subset_Icc_self hzγ)
  · rintro ⟨hzH, hzA | hzb⟩
    · by_contra hzK
      exact Set.disjoint_left.1 hDA ⟨hzH, hzK⟩ hzA
    · by_contra hzK
      have hzD : z ∈ D := ⟨hzH, hzK⟩
      have hsub : D ⊆ connectedComponentIn (H \ A) z :=
        hD.isPreconnected.subset_connectedComponentIn hzD
          (fun x hx => ⟨hD.subset_H hx, fun hxA => Set.disjoint_left.1 hDA hx hxA⟩)
      obtain ⟨R, hR⟩ := hD.far
      obtain ⟨M, hM⟩ := (hzb.subset hsub).exists_norm_le
      set T := max R M + 1 with hT
      have hTH : (T : ℂ) * I ∈ H := by
        show 0 < ((T : ℂ) * I).im
        simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        have := le_max_left R M; have := le_max_right R M
        linarith [norm_nonneg z, (norm_nonneg z).trans (hM z hzD)]
      have hTn : ‖(T : ℂ) * I‖ = T := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
        have := le_max_left R M; have := le_max_right R M
        linarith [norm_nonneg z, (norm_nonneg z).trans (hM z hzD)]
      have hmem := hR _ hTH (by rw [hTn]; linarith [le_max_left R M])
      have := hM _ hmem
      rw [hTn] at this
      linarith [le_max_right R M]

/-- **A crosscut boundary gives a boundary extension** of `f_σ` (Torhorst for the filled crosscut). -/
theorem exists_isBdryExt_of_crosscut (hW : Continuous W) (hW0 : W 0 = 0) (hσ : 0 < σ) {γ : ℝ → ℂ}
    (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re)
    (hfr : frontier (H \ fwdHull W σ) ∩ H = γ '' Ioo 0 1) : ∃ F : ℂ → ℂ, IsBdryExt W σ F := by
  have hK := fwdHull_eq_fillH_of_crosscut hW hW0 hσ hγ hlt hfr
  set γ' : ℝ → ℂ := fun s => γ (s / σ) with hγ'def
  have hγ' : ContinuousOn γ' (Icc 0 σ) :=
    hγ.1.comp (continuous_id.div_const σ).continuousOn
      (fun s hs => ⟨div_nonneg hs.1 hσ.le, (div_le_one hσ).2 hs.2⟩)
  have himg : γ' '' Icc 0 σ = γ '' Icc 0 1 := by
    ext z; constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s / σ, ⟨div_nonneg hs.1 hσ.le, (div_le_one hσ).2 hs.2⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s * σ, ⟨mul_nonneg hs.1 hσ.le, by nlinarith [hs.2]⟩, ?_⟩
      simp only [hγ'def, mul_div_cancel_right₀ _ hσ.ne']
  obtain ⟨F, h1, h2, h3⟩ := Sec7.exists_extension_of_fwdHull_eq hW hW0 hσ.le hγ' (by rw [himg]; exact hK)
  exact ⟨F, ⟨h1, h2, h3⟩⟩

end Fill

end InteractingSLE.ZhanGT4.A35
