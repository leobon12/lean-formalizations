/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkTchFibre
import InteractingSLE.Spec.Supplement.WalkWdTouch
import InteractingSLE.Spec.Supplement.WalkNormSide
import InteractingSLE.Spec.Supplement.GB7aCmpLoewner

/-!
# The transition into a prefix chart at landings on any piece point, and the side at a touch point

Packet PROVE-WALK-TOUCH. Let `c` be a conformal chart whose inverse lands at `x` on a point `q` of a recorded piece,
and suppose `c⁻¹` maps a half-disc at `x` into the domain of the prefix chart `prefixChart pc τ`, read through a global
Loewner model `(W, η)` of the piece's driver.

* **`exists_tendsto_transition`**: if the launch chart's forward map tends to the model point `η(s)` at `q` (`s < τ`;
  `WalkTch.PieceData.tendsto_fwd`, valid also at real touch points), the transition `T = (prefixChart pc τ).fwd ∘ c⁻¹`
  tends to a nonzero real `y` with `F̄_τ(y) = η(s)` (PROVE-WALK-WORDS2's cluster-set lemma
  `WalkWd.exists_tendsto_real_of_fibre_loewner`; `F̄_τ(T w) = pc.1.fwd(c⁻¹ w)`, `T` bounded by the bounded distortion of
  the launch chart and of the Loewner map).
* **`strictMonoOn_of_tendsto_real`**: a conformal map of a half-disc into `ℍ` with real limits along the diameter has a
  continuous strictly increasing boundary function (Schwarz reflection, `Sec7.Aux37Side.strictMonoOn_re`).
* **`not_isForwardSol_of_trace`**: a real trace point visited before `τ` is not alive at `τ`.
* **`neg_and_margin_of_later`** (left side) / **`pos_and_margin_of_later`** (right side): let `m` be the increasing
  boundary function of the transition near `x₀`, with values preimages of trace points before `τ`. If a point `x₁`
  right (left) of `x₀` lands on a later fresh point `η(s₁)` with `η([s₁, τ]) ⊆ ℍ`, then `m(x₀) < 0` (`> 0`), and the
  images of the alive real points of that sign keep a positive distance from `m(x₀)`. Proof: if `m(x₀) > 0`, the cut
  lemma at `s₁` on `[0, m(x₀)]` (`WalkNorm.exists_eq_of_cut`) gives a positive preimage of `η(s₁)` below
  `m(x₀) < m(x₁)`, against the fibre lemma at `η(s₁)`. For the margin: an alive image in `[m(x₀ − δ/2), m(x₁)]` would
  be a value of `m` (intermediate values), hence a trace point before `τ`; above `m(x₁) = y_l` the margin of
  `WalkNorm.exists_leftSide_of_cut` applies. This is the case `η(t₀) ∈ ℝ` that
  `WalkNorm.exists_isLeftSidePt_of_cut` does not cover.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.WalkTch

open WalkBdry WalkWords

/-! ### The transition limit -/

/-- **The transition into a prefix chart at a landing on a piece point** (see the module docstring). -/
theorem exists_tendsto_transition {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ} {V : ℝ≥0 → ℝ} {α : ℝ≥0 → ℂ}
    (d : PieceData pc A f V α) {W : ℝ → ℝ} {η : ℝ → ℂ} {T' : ℝ} {τ : ℝ≥0} (hτT : (τ : ℝ) < T')
    (hWc : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (hpcT : ContinuousOn (pieceDrv pc) (Icc 0 T')) (hag : EqOn (pieceDrv pc) W (Icc 0 T'))
    (hinj : InjOn η (Icc 0 (τ : ℝ))) {c : Chart} (hc : c.IsConformal) {x δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ w ∈ H ∩ ball (x : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom)
    {s : ℝ} (hs : 0 ≤ s) (hsτ : s < τ) {q : ℂ} (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 q))
    (hfwd : Tendsto pc.1.1 (𝓝[pc.1.2.1 '' H] q) (𝓝 (η s))) :
    ∃ y : ℝ, y ≠ 0 ∧ extendFrom H (fwdMapInv W τ) y = η s ∧
      Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) := by
  have hτ0 : (0 : ℝ) ≤ τ := τ.coe_nonneg
  obtain ⟨C, hC⟩ := d.bdd
  obtain ⟨C₁, hC₁⟩ := exists_norm_fwdMapInv_sub_le hWc hW0 hτ0
  have hcL : (pc.1.loewner W τ).IsConformal := d.conf.loewner hWc hW0 hτ0
  have hinv : ∀ z, (prefixChart pc τ).2.1 z = (pc.1.loewner W τ).2.1 z :=
    prefixChart_inv_eq_loewner hWc hpcT hag hτT
  have hfeq : ∀ z, (prefixChart pc τ).1 z = (pc.1.loewner W τ).1 z := prefixChart_fwd_eq_loewner hag hτT.le
  have hdomeq := prefixChart_dom_eq_loewner hWc hpcT hag hτT
  obtain ⟨δ₁, hδ₁, hδ₁b⟩ := Metric.tendsto_nhdsWithin_nhds.1 hland 1 one_pos
  set δ₀ : ℝ := min δ δ₁ with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min hδ hδ₁
  have hsub : H ∩ ball (x : ℂ) δ₀ ⊆ H ∩ ball (x : ℂ) δ := fun w hw => ⟨hw.1, ball_subset_ball (min_le_left _ _) hw.2⟩
  -- the transition read through the model
  have hkey : ∀ w ∈ H ∩ ball (x : ℂ) δ, ∃ v ∈ H, (prefixChart pc τ).1 (c.2.1 w) = v ∧
      fwdMapInv W τ v = pc.1.1 (c.2.1 w) ∧ c.2.1 w ∈ pc.1.2.1 '' H := by
    intro w hw
    have hm : c.2.1 w ∈ interior ((prefixChart pc τ).2.1 '' H) := hdom w hw
    obtain ⟨v, hv, hve⟩ := interior_subset hm
    rw [hinv] at hve
    have hFv : fwdMapInv W τ v ∈ H := QuantumZipper.RS.fwdMapInv_mem_H hWc hW0 hτ0 hv
    have hve' : pc.1.2.1 (fwdMapInv W τ v) = c.2.1 w := hve
    refine ⟨v, hv, ?_, ?_, ⟨_, hFv, hve'⟩⟩
    · rw [hfeq, ← hve, hcL.2.2 v hv]
    · rw [← hve', d.conf.2.2 _ hFv]
  set T : ℂ → ℂ := fun w => (prefixChart pc τ).1 (c.2.1 w) with hTdef
  have hTd : DifferentiableOn ℂ T (H ∩ ball (x : ℂ) δ) := by
    have hT' : T = fun w => (pc.1.loewner W τ).1 (c.2.1 w) := funext fun w => hfeq _
    rw [hT']
    refine hcL.differentiableOn_fwd.comp (hc.1.mono inter_subset_left) fun w hw => ?_
    have hw' : c.2.1 w ∈ ((prefixChart pc τ).dom : Set ℂ) := hdom w hw
    rw [hdomeq] at hw'
    exact hw'
  have hTH : MapsTo T (H ∩ ball (x : ℂ) δ₀) H := fun w hw => by
    obtain ⟨v, hv, he, -, -⟩ := hkey w (hsub hw)
    show (prefixChart pc τ).1 (c.2.1 w) ∈ H
    rw [he]; exact hv
  have hTb : ∀ w ∈ H ∩ ball (x : ℂ) δ₀, ‖T w‖ ≤ ‖q‖ + 1 + C + C₁ := by
    intro w hw
    obtain ⟨v, hv, he, hFv, u, hu, hue⟩ := hkey w (hsub hw)
    show ‖(prefixChart pc τ).1 (c.2.1 w)‖ ≤ _
    rw [he]
    have h1 := hC₁ v hv
    have h2 := norm_sub_norm_le v (fwdMapInv W τ v)
    rw [norm_sub_rev] at h2
    have hu' : pc.1.1 (c.2.1 w) = u := by rw [← hue, d.conf.2.2 u hu]
    have hfu : f u = c.2.1 w := by rw [← hue]; exact PieceData.eqOn_land d hu
    have h3 := hC u (QuantumZipper.H_subset_Hbar hu)
    have h4 := norm_sub_norm_le u (f u)
    rw [norm_sub_rev] at h4
    have hwb : dist (c.2.1 w) q < 1 := hδ₁b hw.1 (ball_subset_ball (min_le_right _ _) hw.2)
    rw [dist_eq_norm] at hwb
    have h5 := norm_sub_norm_le (c.2.1 w) q
    rw [hFv, hu'] at h1 h2
    rw [hfu] at h3 h4
    linarith
  have hFT : Tendsto (fun w => extendFrom H (fwdMapInv W τ) (T w)) (𝓝[H] (x : ℂ)) (𝓝 (η s)) := by
    have hcD : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝[pc.1.2.1 '' H] q) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hland, ?_⟩
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hδ)] with w hwH hwb
      obtain ⟨-, -, -, -, hD⟩ := hkey w ⟨hwH, hwb⟩
      exact hD
    refine (hfwd.comp hcD).congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hδ)] with w hwH hwb
    obtain ⟨v, hv, he, hFv, -⟩ := hkey w ⟨hwH, hwb⟩
    show pc.1.1 (c.2.1 w) = extendFrom H (fwdMapInv W τ) ((prefixChart pc τ).1 (c.2.1 w))
    rw [he, ZhanGT4.extendFrom_eq_fwdMapInv hWc hW0 hτ0 hv, hFv]
  exact WalkWd.exists_tendsto_real_of_fibre_loewner hη hWc hW0 hs hsτ hinj hδ₀
    (show (0 : ℝ) ≤ ((x : ℂ)).im by simp) (hTd.continuousOn.mono hsub) hTH hTb hFT

/-! ### The bundled boundary function of the transition -/

/-- **The transition on a set mapped into the prefix domain**: holomorphic, `ℍ`-valued, injective. -/
theorem transition_facts {pc : Piece} (hpc1 : pc.1.IsConformal) {W : ℝ → ℝ} {T' : ℝ} {τ : ℝ≥0}
    (hτT : (τ : ℝ) < T') (hWc : Continuous W) (hW0 : W 0 = 0) (hpcT : ContinuousOn (pieceDrv pc) (Icc 0 T'))
    (hag : EqOn (pieceDrv pc) W (Icc 0 T')) {c : Chart} (hc : c.IsConformal) {S : Set ℂ} (hSH : S ⊆ H)
    (hdom : ∀ w ∈ S, c.2.1 w ∈ (prefixChart pc τ).dom) :
    DifferentiableOn ℂ (fun w => (prefixChart pc τ).1 (c.2.1 w)) S ∧
      MapsTo (fun w => (prefixChart pc τ).1 (c.2.1 w)) S H ∧
      InjOn (fun w => (prefixChart pc τ).1 (c.2.1 w)) S := by
  have hcL : (pc.1.loewner W τ).IsConformal := hpc1.loewner hWc hW0 τ.coe_nonneg
  have hfeq : ∀ z, (prefixChart pc τ).1 z = (pc.1.loewner W τ).1 z := prefixChart_fwd_eq_loewner hag hτT.le
  have hdomeq := prefixChart_dom_eq_loewner hWc hpcT hag hτT
  have hmem : ∀ w ∈ S, c.2.1 w ∈ ((pc.1.loewner W τ).dom : Set ℂ) := fun w hw => by
    have hw' : c.2.1 w ∈ ((prefixChart pc τ).dom : Set ℂ) := hdom w hw
    rwa [hdomeq] at hw'
  refine ⟨(hcL.differentiableOn_fwd.comp (hc.1.mono hSH) hmem).congr fun w _ => hfeq _,
    fun w hw => by show (prefixChart pc τ).1 (c.2.1 w) ∈ H; rw [hfeq]; exact hcL.fwd_mem (hmem w hw),
    fun w₁ hw₁ w₂ hw₂ he => ?_⟩
  have he' : (pc.1.loewner W τ).1 (c.2.1 w₁) = (pc.1.loewner W τ).1 (c.2.1 w₂) := by
    rw [← hfeq, ← hfeq]; exact he
  have h1 := congrArg (pc.1.loewner W τ).2.1 he'
  rw [hcL.inv_fwd (hmem w₁ hw₁), hcL.inv_fwd (hmem w₂ hw₂)] at h1
  exact hc.injOn (hSH hw₁) (hSH hw₂) h1

/-! ### The boundary function of a half-disc map -/


/-- **A conformal map of a half-disc into `ℍ` with real limits on the diameter has a continuous strictly increasing
boundary function.** -/
theorem strictMonoOn_of_tendsto_real {T : ℂ → ℂ} {x₀ δ : ℝ} (hTd : DifferentiableOn ℂ T (H ∩ ball (x₀ : ℂ) δ))
    (hTH : MapsTo T (H ∩ ball (x₀ : ℂ) δ) H) (hTi : InjOn T (H ∩ ball (x₀ : ℂ) δ)) {m : ℝ → ℝ}
    (hm : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), Tendsto T (𝓝[H] (x : ℂ)) (𝓝 (m x : ℂ))) :
    StrictMonoOn m (Ioo (x₀ - δ) (x₀ + δ)) ∧ ContinuousOn m (Ioo (x₀ - δ) (x₀ + δ)) := by
  have hOpen : IsOpen (H ∩ ball (x₀ : ℂ) δ) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hTat : ∀ w ∈ H ∩ ball (x₀ : ℂ) δ, Tendsto T (𝓝[H] w) (𝓝 (T w)) := fun w hw =>
    ((hTd.continuousOn w hw).continuousAt (hOpen.mem_nhds hw)).tendsto.mono_left nhdsWithin_le_nhds
  have hreal_mem : ∀ z ∈ ball (x₀ : ℂ) δ, z.im = 0 → z = (z.re : ℂ) ∧ z.re ∈ Ioo (x₀ - δ) (x₀ + δ) := by
    intro z hz hz0
    have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    refine ⟨he, ?_⟩
    rw [he, mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt] at hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  set φ : ℂ → ℂ := extendFrom H T with hφdef
  have hφT : ∀ w ∈ H ∩ ball (x₀ : ℂ) δ, φ w = T w := fun w hw => extendFrom_eq (subset_closure hw.1) (hTat w hw)
  have hφm : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), φ x = (m x : ℂ) := fun x hx => by
    refine extendFrom_eq ?_ (hm x hx)
    rw [closure_H]; show (0 : ℝ) ≤ ((x : ℂ)).im; simp
  have hφc : ContinuousOn φ (Hbar ∩ ball (x₀ : ℂ) δ) := by
    refine continuousOn_extendFrom (fun w hw => by rw [closure_H]; exact hw.1) fun w hw => ?_
    by_cases hwH : w ∈ H
    · exact ⟨_, hTat w ⟨hwH, hw.2⟩⟩
    · have hw0 : w.im = 0 := le_antisymm (not_lt.1 hwH) hw.1
      obtain ⟨he, hx⟩ := hreal_mem w hw.2 hw0
      rw [he]
      exact ⟨_, hm _ hx⟩
  have hRBC : R16.IsRealBoundaryConformal φ x₀ δ := by
    refine ⟨hTd.congr fun w hw => hφT w hw, hφc, fun z hz hz0 => ?_, fun w hw => by rw [hφT w hw]; exact hTH hw,
      fun w hw w' hw' he => ?_⟩
    · obtain ⟨he, hx⟩ := hreal_mem z hz hz0
      rw [he, hφm _ hx, ofReal_im]
    · rw [hφT w hw, hφT w' hw'] at he
      exact hTi hw hw' he
  have hmono := Sec7.Aux37Side.strictMonoOn_re hRBC
  have heq : EqOn (fun t : ℝ => (φ t).re) m (Ioo (x₀ - δ) (x₀ + δ)) := fun x hx => by
    show (φ x).re = m x
    rw [hφm x hx, ofReal_re]
  refine ⟨fun a ha b hb hab => ?_, ?_⟩
  · have := hmono ha hb hab
    rwa [heq ha, heq hb] at this
  · have hcomp : ContinuousOn (fun t : ℝ => (φ t).re) (Ioo (x₀ - δ) (x₀ + δ)) := by
      refine Complex.continuous_re.comp_continuousOn (hφc.comp Complex.continuous_ofReal.continuousOn ?_)
      intro x hx
      refine ⟨show (0 : ℝ) ≤ ((x : ℂ)).im by simp, ?_⟩
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact hcomp.congr fun x hx => (heq hx).symm

/-- **The bundled boundary function of the transition** on a window of real points whose landings are piece points
before the prefix time (with the launch chart's forward limit there): a continuous strictly increasing function `m`,
nonzero, with `F̄_τ(m(x)) = η(t(x))` and the transition tending to `m(x)`. -/
theorem exists_boundary_fun {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ} {V : ℝ≥0 → ℝ} {α : ℝ≥0 → ℂ}
    (d : PieceData pc A f V α) {W : ℝ → ℝ} {η : ℝ → ℂ} {T' : ℝ} {τ : ℝ≥0} (hτT : (τ : ℝ) < T')
    (hWc : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η)
    (hpcT : ContinuousOn (pieceDrv pc) (Icc 0 T')) (hag : EqOn (pieceDrv pc) W (Icc 0 T'))
    (hηα : ∀ r ∈ Icc (0 : ℝ) T', η r = α r.toNNReal) (hinj : InjOn η (Icc 0 (τ : ℝ)))
    {c : Chart} (hc : c.IsConformal) (hdom : ∀ w ∈ H, c.2.1 w ∈ (prefixChart pc τ).dom)
    {x₀ δ : ℝ} {tf : ℝ → ℝ≥0}
    (hwin : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), (tf x : ℝ) < τ ∧ Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (f (α (tf x)))) ∧
      Tendsto pc.1.1 (𝓝[pc.1.2.1 '' H] (f (α (tf x)))) (𝓝 (α (tf x)))) :
    ∃ m : ℝ → ℝ, StrictMonoOn m (Ioo (x₀ - δ) (x₀ + δ)) ∧ ContinuousOn m (Ioo (x₀ - δ) (x₀ + δ)) ∧
      ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), m x ≠ 0 ∧ extendFrom H (fwdMapInv W τ) (m x) = η (tf x) ∧
        Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (m x : ℂ)) := by
  have hlim : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ y : ℝ, y ≠ 0 ∧ extendFrom H (fwdMapInv W τ) y = η (tf x) ∧
      Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) := by
    intro x hx
    obtain ⟨hlt, hl, hf⟩ := hwin x hx
    have hηt : η (tf x) = α (tf x) := by
      rw [hηα _ ⟨(tf x).coe_nonneg, hlt.le.trans hτT.le⟩, Real.toNNReal_coe]
    have hf' : Tendsto pc.1.1 (𝓝[pc.1.2.1 '' H] (f (α (tf x)))) (𝓝 (η (tf x))) := by rw [hηt]; exact hf
    exact exists_tendsto_transition d hτT hWc hW0 hη hpcT hag hinj hc one_pos (fun w hw => hdom w hw.1)
      (tf x).coe_nonneg hlt hl hf'
  choose! m hm0 hmF hmT using hlim
  by_cases hδ : 0 < δ
  · obtain ⟨hTd, hTH, hTi⟩ := transition_facts d.conf hτT hWc hW0 hpcT hag hc (S := H ∩ ball (x₀ : ℂ) δ)
      inter_subset_left fun w hw => hdom w hw.1
    obtain ⟨hmono, hmc⟩ := strictMonoOn_of_tendsto_real hTd hTH hTi hmT
    exact ⟨m, hmono, hmc, fun x hx => ⟨hm0 x hx, hmF x hx, hmT x hx⟩⟩
  · have hE : Ioo (x₀ - δ) (x₀ + δ) = ∅ := Ioo_eq_empty (by linarith)
    rw [hE]
    exact ⟨m, fun a ha _ _ _ => absurd ha (notMem_empty a), continuousOn_empty _,
      fun x hx => absurd hx (notMem_empty x)⟩

/-! ### Alive points are off the trace -/

/-- **A real trace point visited before `τ` is not alive at `τ`.** -/
theorem not_isForwardSol_of_trace {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hWc : Continuous W)
    (hW0 : W 0 = 0) {s τ : ℝ} (hs : 0 ≤ s) (hsτ : s < τ) {X : ℝ} (hX : η s = X) :
    ¬ ∃ u, IsForwardSol W (X : ℂ) τ u := by
  rintro ⟨u, hu⟩
  obtain ⟨r, hr, hnot⟩ := GB7a.exists_ball_notMem_fwdHull hWc (hs.trans hsτ.le) hu
  obtain ⟨ε, hε, hball⟩ := Metric.continuousWithinAt_iff.1 (hη.2.1 s hs) r hr
  obtain ⟨s', hs', hcut⟩ := YuanSimpleApprox.exists_isCutTime_mem_Ioo hη hWc hW0 hs
    (lt_min (lt_add_of_pos_right s hε) hsτ)
  have hs'0 : 0 ≤ s' := hs.trans hs'.1.le
  have hmem : η s' ∈ fwdHull W τ := by
    have h1 : η s' ∈ fwdHull W s' := by
      rw [hη.2.2 s' hs'0]
      exact mem_fillH_of_mem_closure hcut.1 (subset_closure ⟨s', ⟨hs'0, le_rfl⟩, rfl⟩)
    exact QuantumZipper.fwdHull_mono.1 (hs'.2.trans_le (min_le_right _ _)).le h1
  have hd : dist s' s < ε := by
    rw [Real.dist_eq, abs_of_pos (by linarith [hs'.1])]
    linarith [hs'.2.trans_le (min_le_left _ _)]
  have h2 := hball (show s' ∈ Ici (0 : ℝ) from hs'0) hd
  rw [hX, dist_eq_norm] at h2
  exact hnot _ h2 hmem

/-! ### The side at a landing -/

section Side

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {τ x₀ δ : ℝ} {m : ℝ → ℝ}

/-- An alive real point is not the image of a trace point of the window. -/
theorem notMem_image_of_alive (hη : IsLoewnerTrace W η) (hWc : Continuous W) (hW0 : W 0 = 0) (hτ0 : 0 ≤ τ)
    (htr : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Ico 0 τ, extendFrom H (fwdMapInv W τ) (m x) = η s)
    {X : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (X : ℂ) τ u) {x : ℝ} (hx : x ∈ Ioo (x₀ - δ) (x₀ + δ)) :
    m x ≠ (fwdMap W τ X).re := by
  intro he
  obtain ⟨s, hs, hse⟩ := htr x hx
  have h1 := WalkNorm.extendFrom_fwdMap_real hη hWc hW0 hτ0 hu
  rw [← he, hse] at h1
  exact not_isForwardSol_of_trace hη hWc hW0 hs.1 hs.2 h1 ⟨u, hu⟩

/-- **The left side and its margin at a landing whose right neighbours are later** (see the module docstring). -/
theorem neg_and_margin_of_later (hη : IsLoewnerTrace W η) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hinj : InjOn η (Icc 0 τ)) (hδ : 0 < δ) (hmono : StrictMonoOn m (Ioo (x₀ - δ) (x₀ + δ)))
    (hmc : ContinuousOn m (Ioo (x₀ - δ) (x₀ + δ))) (hm0 : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), m x ≠ 0)
    (htr : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Ico 0 τ, extendFrom H (fwdMapInv W τ) (m x) = η s)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hx₀ : extendFrom H (fwdMapInv W τ) (m x₀) = η t₀)
    {x₁ s₁ : ℝ} (hx₁ : x₁ ∈ Ioo x₀ (x₀ + δ)) (hs₁ : t₀ < s₁) (hs₁τ : s₁ < τ)
    (hH : ∀ s ∈ Icc s₁ τ, η s ∈ H) (hx₁s : extendFrom H (fwdMapInv W τ) (m x₁) = η s₁) :
    m x₀ < 0 ∧ ∃ ε > 0, ∀ X : ℝ, (∃ u, IsForwardSol W (X : ℂ) τ u) → (fwdMap W τ X).re < 0 →
      (fwdMap W τ X).re + ε < m x₀ := by
  have hτ0 : 0 ≤ τ := ht₀.trans (hs₁.trans hs₁τ).le
  have hs₁0 : 0 ≤ s₁ := ht₀.trans hs₁.le
  have hmem : ∀ x ∈ Icc (x₀ - δ / 2) x₁, x ∈ Ioo (x₀ - δ) (x₀ + δ) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2, hx₁.2]⟩
  have hx₀m : x₀ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have hx₁m : x₁ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith [hx₁.1], hx₁.2⟩
  have hlt01 : m x₀ < m x₁ := hmono hx₀m hx₁m hx₁.1
  have htip : extendFrom H (fwdMapInv W τ) 0 = η τ := ZhanGT4.extendFrom_zero_eq hη hWc hW0 hτ0
  have hs₁H : η s₁ ∈ H := hH s₁ ⟨le_rfl, hs₁τ.le⟩
  have hne1 : η τ ≠ η s₁ := fun h => hs₁τ.ne' (hinj ⟨hτ0, le_rfl⟩ ⟨hs₁0, hs₁τ.le⟩ h)
  have hne0 : η t₀ ≠ η s₁ := fun h => hs₁.ne (hinj ⟨ht₀, (hs₁.trans hs₁τ).le⟩ ⟨hs₁0, hs₁τ.le⟩ h)
  -- the sign at `x₀`
  have hneg : m x₀ < 0 := by
    rcases lt_or_gt_of_ne (hm0 x₀ hx₀m) with h | h
    · exact h
    exfalso
    obtain ⟨y', hy', hFy'⟩ := WalkNorm.exists_eq_of_cut hη hWc hW0 hs₁0 hs₁τ.le hinj hH (a := m x₀) (c := 0)
      (Or.inr ⟨t₀, ⟨ht₀, hs₁.le⟩, hx₀.symm⟩) (by rw [ofReal_zero]; exact htip)
    rw [uIcc_of_ge h.le] at hy'
    have hy0 : y' ≠ 0 := by
      rintro rfl
      rw [ofReal_zero, htip] at hFy'
      exact hne1 hFy'
    have hya : y' ≠ m x₀ := by
      rintro rfl
      rw [hx₀] at hFy'
      exact hne0 hFy'
    have hy0' : 0 < y' := lt_of_le_of_ne hy'.1 (Ne.symm hy0)
    have hya' : y' < m x₀ := lt_of_le_of_ne hy'.2 hya
    have := WalkWords.eq_of_extendFrom_eq_of_same_side hη hWc hW0 hs₁0 hs₁τ hinj hs₁H
      (mul_pos hy0' (by linarith)) hFy' hx₁s
    linarith
  -- the sign at `x₁`
  have hneg1 : m x₁ < 0 := by
    rcases lt_or_gt_of_ne (hm0 x₁ hx₁m) with h | h
    · exact h
    exfalso
    obtain ⟨x', hx', hx'0⟩ := isPreconnected_Icc.intermediate_value (a := x₀) (b := x₁)
      ⟨le_rfl, hx₁.1.le⟩ ⟨hx₁.1.le, le_rfl⟩ (hmc.mono fun x hx => hmem x ⟨by linarith [hx.1], hx.2⟩)
      (show (0 : ℝ) ∈ Icc (m x₀) (m x₁) from ⟨hneg.le, h.le⟩)
    exact hm0 x' (hmem x' ⟨by linarith [hx'.1], hx'.2⟩) hx'0
  -- the left side point of `η(s₁)` is `m x₁`
  obtain ⟨yl, hyl0, hFyl, ⟨εl, hεl, hmargin⟩, -⟩ := WalkNorm.exists_leftSide_of_cut hη hWc hW0 hs₁0 hs₁τ hinj hH
  have hyl : m x₁ = yl := WalkWords.eq_of_extendFrom_eq_of_same_side hη hWc hW0 hs₁0 hs₁τ hinj hs₁H
    (mul_pos_of_neg_of_neg hneg1 hyl0) hx₁s hFyl
  -- the margin
  set xm : ℝ := x₀ - δ / 2 with hxm
  have hxmm : xm ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have hltm : m xm < m x₀ := hmono hxmm hx₀m (by linarith)
  refine ⟨hneg, m x₀ - m xm, by linarith, fun X ⟨u, hu⟩ hX => ?_⟩
  set xX : ℝ := (fwdMap W τ X).re with hxX
  have h1 : xX + εl < yl := hmargin X ⟨u, hu⟩ hX
  by_contra hcon
  have h2 : m xm ≤ xX := by linarith
  have h3 : xX ≤ m x₁ := by linarith
  obtain ⟨x', hx', hx'e⟩ := isPreconnected_Icc.intermediate_value (a := xm) (b := x₁)
    ⟨le_rfl, by linarith [hx₁.1]⟩ ⟨by linarith [hx₁.1], le_rfl⟩ (hmc.mono hmem)
    (show xX ∈ Icc (m xm) (m x₁) from ⟨h2, h3⟩)
  exact notMem_image_of_alive hη hWc hW0 hτ0 htr hu (hmem x' hx') hx'e

/-- **The right side and its margin at a landing whose left neighbours are later** (mirror). -/
theorem pos_and_margin_of_later (hη : IsLoewnerTrace W η) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hinj : InjOn η (Icc 0 τ)) (hδ : 0 < δ) (hmono : StrictMonoOn m (Ioo (x₀ - δ) (x₀ + δ)))
    (hmc : ContinuousOn m (Ioo (x₀ - δ) (x₀ + δ))) (hm0 : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), m x ≠ 0)
    (htr : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Ico 0 τ, extendFrom H (fwdMapInv W τ) (m x) = η s)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hx₀ : extendFrom H (fwdMapInv W τ) (m x₀) = η t₀)
    {x₁ s₁ : ℝ} (hx₁ : x₁ ∈ Ioo (x₀ - δ) x₀) (hs₁ : t₀ < s₁) (hs₁τ : s₁ < τ)
    (hH : ∀ s ∈ Icc s₁ τ, η s ∈ H) (hx₁s : extendFrom H (fwdMapInv W τ) (m x₁) = η s₁) :
    0 < m x₀ ∧ ∃ ε > 0, ∀ X : ℝ, (∃ u, IsForwardSol W (X : ℂ) τ u) → 0 < (fwdMap W τ X).re →
      m x₀ + ε < (fwdMap W τ X).re := by
  have hτ0 : 0 ≤ τ := ht₀.trans (hs₁.trans hs₁τ).le
  have hs₁0 : 0 ≤ s₁ := ht₀.trans hs₁.le
  have hmem : ∀ x ∈ Icc x₁ (x₀ + δ / 2), x ∈ Ioo (x₀ - δ) (x₀ + δ) := fun x hx =>
    ⟨by linarith [hx.1, hx₁.1], by linarith [hx.2]⟩
  have hx₀m : x₀ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have hx₁m : x₁ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨hx₁.1, by linarith [hx₁.2]⟩
  have hlt01 : m x₁ < m x₀ := hmono hx₁m hx₀m hx₁.2
  have htip : extendFrom H (fwdMapInv W τ) 0 = η τ := ZhanGT4.extendFrom_zero_eq hη hWc hW0 hτ0
  have hs₁H : η s₁ ∈ H := hH s₁ ⟨le_rfl, hs₁τ.le⟩
  have hne1 : η τ ≠ η s₁ := fun h => hs₁τ.ne' (hinj ⟨hτ0, le_rfl⟩ ⟨hs₁0, hs₁τ.le⟩ h)
  have hne0 : η t₀ ≠ η s₁ := fun h => hs₁.ne (hinj ⟨ht₀, (hs₁.trans hs₁τ).le⟩ ⟨hs₁0, hs₁τ.le⟩ h)
  have hpos : 0 < m x₀ := by
    rcases lt_or_gt_of_ne (hm0 x₀ hx₀m) with h | h
    swap
    · exact h
    exfalso
    obtain ⟨y', hy', hFy'⟩ := WalkNorm.exists_eq_of_cut hη hWc hW0 hs₁0 hs₁τ.le hinj hH (a := m x₀) (c := 0)
      (Or.inr ⟨t₀, ⟨ht₀, hs₁.le⟩, hx₀.symm⟩) (by rw [ofReal_zero]; exact htip)
    rw [uIcc_of_le h.le] at hy'
    have hy0 : y' ≠ 0 := by
      rintro rfl
      rw [ofReal_zero, htip] at hFy'
      exact hne1 hFy'
    have hya : y' ≠ m x₀ := by
      rintro rfl
      rw [hx₀] at hFy'
      exact hne0 hFy'
    have hy0' : y' < 0 := lt_of_le_of_ne hy'.2 hy0
    have hya' : m x₀ < y' := lt_of_le_of_ne hy'.1 (Ne.symm hya)
    have := WalkWords.eq_of_extendFrom_eq_of_same_side hη hWc hW0 hs₁0 hs₁τ hinj hs₁H
      (mul_pos_of_neg_of_neg hy0' (by linarith)) hFy' hx₁s
    linarith
  have hpos1 : 0 < m x₁ := by
    rcases lt_or_gt_of_ne (hm0 x₁ hx₁m) with h | h
    swap
    · exact h
    exfalso
    obtain ⟨x', hx', hx'0⟩ := isPreconnected_Icc.intermediate_value (a := x₁) (b := x₀)
      ⟨le_rfl, hx₁.2.le⟩ ⟨hx₁.2.le, le_rfl⟩ (hmc.mono fun x hx => hmem x ⟨hx.1, by linarith [hx.2]⟩)
      (show (0 : ℝ) ∈ Icc (m x₁) (m x₀) from ⟨h.le, hpos.le⟩)
    exact hm0 x' (hmem x' ⟨hx'.1, by linarith [hx'.2]⟩) hx'0
  obtain ⟨yr, hyr0, hFyr, ⟨εr, hεr, hmargin⟩, -⟩ := WalkNorm.exists_rightSide_of_cut hη hWc hW0 hs₁0 hs₁τ hinj hH
  have hyr : m x₁ = yr := WalkWords.eq_of_extendFrom_eq_of_same_side hη hWc hW0 hs₁0 hs₁τ hinj hs₁H
    (mul_pos hpos1 hyr0) hx₁s hFyr
  set xp : ℝ := x₀ + δ / 2 with hxp
  have hxpm : xp ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have hltp : m x₀ < m xp := hmono hx₀m hxpm (by linarith)
  refine ⟨hpos, m xp - m x₀, by linarith, fun X ⟨u, hu⟩ hX => ?_⟩
  set xX : ℝ := (fwdMap W τ X).re with hxX
  have h1 : yr + εr < xX := hmargin X ⟨u, hu⟩ hX
  by_contra hcon
  have h2 : xX ≤ m xp := by linarith
  have h3 : m x₁ ≤ xX := by linarith
  obtain ⟨x', hx', hx'e⟩ := isPreconnected_Icc.intermediate_value (a := x₁) (b := xp)
    ⟨le_rfl, by linarith [hx₁.2]⟩ ⟨by linarith [hx₁.2], le_rfl⟩ (hmc.mono hmem)
    (show xX ∈ Icc (m x₁) (m xp) from ⟨h3, h2⟩)
  exact notMem_image_of_alive hη hWc hW0 hτ0 htr hu (hmem x' hx') hx'e

end Side

end InteractingSLE.Theorem14.WalkTch
