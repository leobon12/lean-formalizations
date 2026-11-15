/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3GeoSide
import InteractingSLE.Spec.Sec7.ReverseArcModel
import InteractingSLE.Spec.Sec7.ReverseArcSide
import InteractingSLE.Spec.Sec7.R6CorReflect
import InteractingSLE.Spec.Supplement.SBLvPinch
import InteractingSLE.Spec.Supplement.SBLwPath
import InteractingSLE.Spec.Supplement.SBLemmaS2Lift
import InteractingSLE.Spec.Supplement.S9BSide
import InteractingSLE.Spec.Supplement.SBS3EntryCollar

/-!
# Lemma S3: the second-path geometry

Worker PROVE-R6-CORNER (Theorem 1.4, Lemma S3, specification p. 580: "Its exposed second-left component joins an
untouched original-real interval … The protected nested-kernel comparison identifies this exposed side with its
second-path value `−λ − ϑχ`"). Deterministic; the geometric part of `S3.JointPhaseGaps` for the second path.

* `secondChart_facts`: the chart `f_q` of a stopped generating trace, its hull identity, map-out, holomorphy and finite
  fibres of the inverse extension `Φ_q` (`Lv.finite_fibre_of_paths`);
* `exists_tendsto_comp_of_collar`: `f_q ∘ g` has a limit at a boundary point along a collar (cluster values in a
  finite fibre, `SB.exists_tendsto_of_cluster`);
* `tendsto_zero_at_tip`, **`neg_tendsto_comp_of_lifted_arc`**: along S2's lifted common arc the composite is real,
  strictly increasing (Schwarz reflection, `R6Cor.strictMonoOn_continuousOn_re_of_forall`), nonzero and tends to `0`
  at the lifted tip, hence **negative**: the approach is from the left side of the second path;
* `exists_ball_disjoint_tail`, **`exists_ball_disjoint_second_transition`**: the second transition gap — a small
  half-disc at the left limit is mapped by `Φ_q` into the left side of the proper witness, hence off the old history
  and into the joint unbounded domain;
* **`exists_second_geometry_of_s2`**: on S2's lift (T14-S3's `exists_positive_left_joint_collar_of_s2`), for every
  common arc with interior tip: the collar is on the left of the witness and in the joint domain, `f_q` tends along
  `g_*(𝓝[ℍ] γ(t))` to a negative real `y` with `Φ_q(y) = η(t_L + t)`, and a ball about `y` misses the second
  transition hull.

R48 (as amended for Theorem 1.4): nothing here uses Theorem 1.4 or `Theorem14Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.SB.S3.Geo

open Supp9B (IsProperCurve leftSide rightSide closedRightSide lowerLeft)
open Sec7.ReverseArc

/-- **The chart of a stopped generating trace** (the second path of Lemma S3): the `ReverseArc` chart, the hull
identity, the map-out, and finite fibres of the boundary extension of the inverse. -/
theorem secondChart_facts {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < ζ) (hq0 : 0 < q) :
    IsChart η q (fwdMap (fun r : ℝ => w r.toNNReal) q) (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q)) ∧
      fwdHull (fun r : ℝ => w r.toNNReal) q = fillH (η '' Icc 0 q) ∧
      IsHPHull (fillH (η '' Icc 0 q)) ∧
      IsMapOut (fillH (η '' Icc 0 q)) (fun z => fwdMap (fun r : ℝ => w r.toNNReal) q z + w q) ∧
      DifferentiableOn ℂ (fwdMap (fun r : ℝ => w r.toNNReal) q) (H \ fillH (η '' Icc 0 q)) ∧
      ∀ z, (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  have hch := isChart hη hw hw0 hinj hq hq0
  obtain ⟨W, γ, T', hqT', hWc, hW0, hγ, hWeq, hγeq⟩ := exists_global_model hη hw hw0 hq
  have hq0' : (0 : ℝ) ≤ q := NNReal.coe_nonneg q
  have hf : fwdMap (fun r : ℝ => w r.toNNReal) q = fwdMap W q := funext fun z =>
    fwdMap_eq_of_eqOn hq0' fun r hr => (hWeq r ⟨hr.1, hr.2.trans hqT'.le⟩).symm
  have hΦ : fwdMapInv (fun r : ℝ => w r.toNNReal) q = fwdMapInv W q :=
    fwdMapInv_eq_of_eqOn hq0' hqT' fun r hr => (hWeq r hr).symm
  have hKW : fwdHull (fun r : ℝ => w r.toNNReal) q = fwdHull W q :=
    fwdHull_eq_of_eqOn hq0' hqT' fun r hr => (hWeq r hr).symm
  have himg : γ '' Icc 0 (q : ℝ) = η '' Icc 0 q := by
    rw [image_congr (fun r hr => hγeq r ⟨hr.1, hr.2.trans hqT'.le⟩), image_toNNReal_Icc η hq0',
      Real.toNNReal_coe]
  have hK : fwdHull W q = fillH (η '' Icc 0 q) := by rw [hγ.2.2 q hq0', himg]
  have hWq : W q = w q := by rw [hWeq q ⟨hq0', hqT'.le⟩, Real.toNNReal_coe]
  refine ⟨hch, hKW.trans hK, hK ▸ isHPHull_fwdHull hWc hq0', ?_, ?_, ?_⟩
  · have h := isMapOut_fwdMap hWc hW0 hq0'
    rw [hK] at h
    rw [hf]
    simpa only [hWq] using h
  · rw [hf, ← hK]; exact QuantumZipper.FwdHolo.differentiableOn_fwdMap hWc hq0'
  · intro z
    have hB : Lv.IsBoundaryMap (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q)) := by
      rw [hΦ]
      obtain ⟨hd, hc, hi, hreal⟩ := hγ.fiber_hyps hWc hW0 hq0'
      have himgH := ZhanGT4.extendFrom_image_H hWc hW0 hq0'
      obtain ⟨C, hC⟩ := InteractingSLE.exists_norm_fwdMapInv_sub_le hWc hW0 hq0'
      refine ⟨hd, hc, hi, fun v hv => ?_, ?_, fun x => hreal x (by simp), ?_⟩
      · rw [ZhanGT4.extendFrom_eq_fwdMapInv hWc hW0 hq0' hv]
        exact QuantumZipper.RS.fwdMapInv_mem_H hWc hW0 hq0' hv
      · rw [himgH]; exact (isHPHull_fwdHull hWc hq0').2.2.1
      · refine tendsto_norm_atTop_iff_cobounded.1 (tendsto_atTop_mono' _ ?_
          ((tendsto_atTop_add_const_right _ (-C) tendsto_norm_cobounded_atTop).mono_left inf_le_left))
        refine eventually_inf_principal.2 (Eventually.of_forall fun v hv => ?_)
        have h1 := hC v hv
        show ‖v‖ + -C ≤ ‖extendFrom H (fwdMapInv W q) v‖
        rw [ZhanGT4.extendFrom_eq_fwdMapInv hWc hW0 hq0' hv]
        have h2 : ‖v‖ ≤ ‖fwdMapInv W q v‖ + ‖fwdMapInv W q v - v‖ := by
          have := norm_sub_le (fwdMapInv W q v) (fwdMapInv W q v - v)
          rwa [sub_sub_cancel] at this
        linarith
    set p₁ : ℝ → ℂ := fun u => γ (u * q) with hp₁
    have hp₁c : ContinuousOn p₁ (Icc 0 1) :=
      hγ.2.1.comp (continuous_id.mul continuous_const).continuousOn fun u hu =>
        show (0 : ℝ) ≤ u * q from mul_nonneg hu.1 hq0'
    have hp₁img : p₁ '' Icc 0 1 = η '' Icc 0 q := by
      rw [← himg]
      ext v
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u * q, ⟨mul_nonneg hu.1 hq0', by nlinarith [hu.2]⟩, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        have hq0'' : (0 : ℝ) < q := by exact_mod_cast hq0
        refine ⟨r / q, ⟨div_nonneg hr.1 hq0', (div_le_one hq0'').2 hr.2⟩, ?_⟩
        show γ (r / q * q) = γ r
        rw [div_mul_cancel₀ _ hq0''.ne']
    have hp₁i : InjOn p₁ (Icc 0 1) := by
      intro u hu v hv huv
      have hq0'' : (0 : ℝ) < q := by exact_mod_cast hq0
      have hu' : u * q ∈ Icc (0 : ℝ) T' := ⟨mul_nonneg hu.1 hq0', by nlinarith [hu.2]⟩
      have hv' : v * q ∈ Icc (0 : ℝ) T' := ⟨mul_nonneg hv.1 hq0', by nlinarith [hv.2]⟩
      have h1 : η (u * q).toNNReal = η (v * q).toNNReal := by
        rw [← hγeq _ hu', ← hγeq _ hv']; exact huv
      have hle : ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ((s * q).toNNReal : ℝ≥0∞) ≤ ζ := fun s hs => by
        refine le_trans (ENNReal.coe_le_coe.2 ?_) hq.le
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (mul_nonneg hs.1 hq0')]
        nlinarith [hs.2]
      have h2 := hinj (hle u hu) (hle v hv) h1
      have h3 : u * q = v * q := by
        have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h2
        simp only [Real.coe_toNNReal _ (mul_nonneg hu.1 hq0'), Real.coe_toNNReal _ (mul_nonneg hv.1 hq0')] at this
        exact this
      exact mul_right_cancel₀ (by exact_mod_cast hq0.ne') h3
    refine Lv.finite_fibre_of_paths hB (n := 1) (p := fun _ => p₁) (fun _ => hp₁c)
      (fun _ z => Lw.finite_fibre_of_injOn hp₁i z) (fun _ => ?_) (fun x => ?_) z
    · rw [hp₁img]
      refine Set.disjoint_left.2 fun v hv hvF => ?_
      obtain ⟨u, hu, rfl⟩ := hvF
      have hm := hch.inv_mem hu
      exact hm.2 ⟨hm.1, Or.inl (subset_closure hv)⟩
    · have hHb : (x : ℂ) ∈ Hbar := by show (0 : ℝ) ≤ ((x : ℂ)).im; simp
      have hHb' : (0 : ℝ) ≤ (extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) (x : ℂ)).im :=
        hch.inv_mem_Hbar hHb
      rcases hHb'.lt_or_eq with hpos | h0
      · right
        refine ⟨0, ?_⟩
        rw [hp₁img]
        exact hch.bdry x hpos
      · exact Or.inl h0.symm

/-- **A chart of a filled hull with a continuous inverse extension**: the fields of `Sec7.ReverseArc.IsChart` except
the one-sided `free_real`. These are invariant under the reflection `z ↦ −z̄` and are all the second-path geometry
below uses; any chart of the second filled hull of this form will do (the Loewner chart of a generating trace:
`IsChart.toCore`). -/
structure IsChartCore (η : ℝ≥0 → ℂ) (q : ℝ≥0) (f Φ : ℂ → ℂ) : Prop where
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

/-- The Loewner chart model gives the core chart fields. -/
theorem IsChart.toCore {η : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ : ℂ → ℂ} (h : IsChart η q f Φ) : IsChartCore η q f Φ :=
  ⟨h.maps, h.injOn, h.cont, h.bdd, h.inv_cont, h.inv_mem, h.f_inv, h.inv_f, h.cluster, h.tip, h.tip_fibre, h.bdry⟩

/-- Boundary values of a core chart lie in the closed half-plane. -/
theorem IsChartCore.inv_mem_Hbar {η : ℝ≥0 → ℂ} {q : ℝ≥0} {f Φ : ℂ → ℂ} (hch : IsChartCore η q f Φ) {w : ℂ}
    (hw : w ∈ Hbar) : Φ w ∈ Hbar := by
  have hcl : Hbar = closure H := (closure_H).symm
  have hneb : (𝓝[H] w).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, ← hcl]; exact hw
  have hlim : Tendsto Φ (𝓝[H] w) (𝓝 (Φ w)) := ((hch.inv_cont w hw).mono H_subset_Hbar).tendsto
  have hc : IsClosed Hbar := by rw [hcl]; exact isClosed_closure
  exact hc.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun v hv => H_subset_Hbar (hch.inv_mem hv).1)

/-- **The second chart along a collar of a boundary point**: if `g` (continuous on `ℍ̄`) maps a half-disc at `x` into
the domain `H \ fill η([0, q])` of a chart `f` whose inverse extension `Φ` has finite fibres, then `f ∘ g` has a limit
`y ∈ ℍ̄` at `x` along `ℍ`, with `Φ(y) = g(x)`. -/
theorem exists_tendsto_comp_of_collar {f Φ : ℂ → ℂ} {η : ℝ≥0 → ℂ} {q : ℝ≥0} (hch : IsChartCore η q f Φ)
    (hfin : ∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    {x : ℂ} (hx : 0 ≤ x.im) {ρ : ℝ} (hρ : 0 < ρ) (hcol : g '' (ball x ρ ∩ H) ⊆ H \ fillH (η '' Icc 0 q)) :
    ∃ y, Tendsto (fun u => f (g u)) (𝓝[H] x) (𝓝 y) ∧ Φ y = g x ∧ 0 ≤ y.im := by
  set Y : Set ℂ := H ∩ ball x ρ with hY
  have hYH : ∀ u ∈ Y, g u ∈ H \ fillH (η '' Icc 0 q) := fun u hu => hcol ⟨u, ⟨hu.2, hu.1⟩, rfl⟩
  have hxcl : x ∈ closure Y := by
    rw [hY, inter_comm]
    refine (isOpen_ball.inter_closure (s := ball x ρ) (t := H)) ⟨mem_ball_self hρ, ?_⟩
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hx
  have hgY : ContinuousOn g Y := hgc.mono fun u hu => (le_of_lt hu.1 : 0 ≤ u.im)
  have hFc : ContinuousOn (fun u => f (g u)) Y := hch.cont.comp hgY hYH
  obtain ⟨C, hC⟩ := hch.bdd
  obtain ⟨ε₀, hε₀, hε₀g⟩ := Metric.continuousWithinAt_iff.1 (hgc x hx) 1 one_pos
  have hM : ∀ u ∈ Y ∩ ball x ε₀, ‖f (g u)‖ ≤ ‖g x‖ + 1 + C := by
    intro u hu
    have h1 := hC _ (hYH u hu.1)
    have h2 := hε₀g (show 0 ≤ u.im from le_of_lt hu.1.1) (mem_ball.1 hu.2)
    rw [dist_eq_norm] at h2
    have h3 : ‖f (g u)‖ ≤ ‖g u‖ + ‖f (g u) - g u‖ := by
      have := norm_add_le (g u) (f (g u) - g u)
      rwa [add_sub_cancel] at this
    have h4 : ‖g u‖ ≤ ‖g x‖ + ‖g u - g x‖ := by
      have := norm_add_le (g x) (g u - g x)
      rwa [add_sub_cancel] at this
    linarith
  have hgF : Tendsto (Φ ∘ fun u => f (g u)) (𝓝[Y] x) (𝓝 (g x)) := by
    refine ((hgc x hx).mono fun u hu => (le_of_lt hu.1 : 0 ≤ u.im)).tendsto.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hch.inv_f _ (hYH u hu)).symm
  have hFS : ∀ᶠ u in 𝓝[Y] x, (fun u => f (g u)) u ∈ {v : ℂ | 0 ≤ v.im} := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact le_of_lt (hch.maps (hYH u hu))
  have hScl : IsClosed {v : ℂ | 0 ≤ v.im} := isClosed_le continuous_const continuous_im
  have hcl : ∀ y, MapClusterPt y (𝓝[Y] x) (fun u => f (g u)) →
      y ∈ Φ ⁻¹' {g x} ∩ {v | 0 ≤ v.im} := fun y hy =>
    SB.mem_fiber_of_mapClusterPt hScl (hch.inv_cont.mono fun v hv => hv) hFS hgF hy
  have hlc : ∀ ε > 0, ∃ δ > 0, ∃ V ⊆ Y ∩ ball x ε, IsPreconnected V ∧ Y ∩ ball x δ ⊆ V := by
    intro ε hε
    refine ⟨min ε ρ, lt_min hε hρ, H ∩ ball x (min ε ρ), fun u hu => ⟨⟨hu.1, ball_subset_ball (min_le_right _ _) hu.2⟩,
      ball_subset_ball (min_le_left _ _) hu.2⟩, ?_, fun u hu => ⟨hu.1.1, hu.2⟩⟩
    exact (convex_H.inter (convex_ball x _)).isPreconnected
  obtain ⟨y, hy⟩ := SB.exists_tendsto_of_cluster (hfin (g x)) hxcl hFc hε₀ hM hcl hlc
  have hYeq : 𝓝[Y] x = 𝓝[H] x := by
    rw [hY]; exact nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hρ))
  have hne : (𝓝[Y] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxcl
  have hyc := hcl y hy.mapClusterPt
  rw [hYeq] at hy
  exact ⟨y, hy, hyc.1, hyc.2⟩

/-- At an interior tip of a chart the forward map tends to `0` along the domain. -/
theorem tendsto_zero_at_tip {f Φ : ℂ → ℂ} {η : ℝ≥0 → ℂ} {q : ℝ≥0} (hch : IsChartCore η q f Φ) (hq : η q ∈ H) :
    Tendsto f (𝓝[H \ fillH (η '' Icc 0 q)] (η q)) (𝓝 0) := by
  rw [Filter.tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨y, hyH, hfy, hΦy⟩ := hch.cluster U (η q) hU
  have hqK : η q ∈ fillH (η '' Icc 0 q) := mem_fillH_of_mem_H le_rfl hq
  have hyim : y.im = 0 := le_antisymm (not_lt.1 fun hpos => (hch.inv_mem hpos).2 (hΦy ▸ hqK)) hyH
  have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
  rw [hyr] at hΦy
  have h0 := hch.tip_fibre hq y.re hΦy
  rw [hyr, h0, ofReal_zero] at hfy
  exact hfy

/-- **The second chart's limit along the lifted common arc is on the left of its tip** (Lemma S3, the exposed second
side, p. 580). Let `g` be the inverse extension of a chart of the old domain and `γ` a lift, real on `[a, b]` with
strictly increasing coordinate on `(a, b)`, of the second trace `η` (`g ∘ γ = η(t_L + ·)`, `t_L + b = q`, interior
tip), with collars at every interior point mapped into the domain of the second chart `f`. Then at every interior
`t` the composite `f ∘ g` tends to a negative real `y` with `Φ(y) = η(t_L + t)`.

Proof. The composite is real-boundary conformal on the lifted arc (reflection), hence strictly increasing there; it
does not vanish (only the tip lands at `0`) and tends to `0` at the lifted tip, so it is negative. -/
theorem neg_tendsto_comp_of_lifted_arc {f Φ : ℂ → ℂ} {η : ℝ≥0 → ℂ} {q : ℝ≥0} (hch : IsChartCore η q f Φ)
    (hfd : DifferentiableOn ℂ f (H \ fillH (η '' Icc 0 q)))
    (hfin : ∀ z, (Φ ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite) (hq : η q ∈ H) (hinj : InjOn η (Icc 0 q))
    (hDo : IsOpen (H \ fillH (η '' Icc 0 q)))
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g H) (hgi : InjOn g H)
    {γ : ℝ≥0 → ℂ} (hγc : Continuous γ) {a b tL : ℝ≥0} (hab : a < b) (hqb : tL + b = q)
    (hreal : ∀ s ∈ Icc a b, (γ s).im = 0) (hmono : StrictMonoOn (fun s => (γ s).re) (Ioo a b))
    (hlift : ∀ s ∈ Icc a b, g (γ s) = η (tL + s))
    (hcol : ∀ s ∈ Ioo a b, ∃ ρ > 0, g '' (ball (γ s) ρ ∩ H) ⊆ H \ fillH (η '' Icc 0 q)) :
    ∀ t ∈ Ioo a b, ∃ y : ℝ, y < 0 ∧ Tendsto (fun u => f (g u)) (𝓝[H] (γ t)) (𝓝 (y : ℂ)) ∧
      Φ y = η (tL + t) := by
  set D : Set ℂ := H \ fillH (η '' Icc 0 q) with hD
  set α : ℝ := (γ a).re with hα
  set ω : ℝ := (γ b).re with hω
  have hγr : ∀ s ∈ Icc a b, γ s = ((γ s).re : ℂ) := fun s hs =>
    Complex.ext (by simp) (by simp [hreal s hs])
  have hreC : Continuous fun s => (γ s).re := continuous_re.comp hγc
  -- endpoints
  have hlt_left : ∀ t ∈ Ioo a b, α < (γ t).re := by
    intro t ht
    set s' := (a + t) / 2 with hs'
    have hs'I : s' ∈ Ioo a t := by
      constructor
      · rw [hs']; exact add_div_two_lt_right.2 ht.1 |> fun h => by
          have := left_lt_add_div_two.2 ht.1; exact this
      · exact add_div_two_lt_right.2 ht.1
    have h1 : (γ s').re < (γ t).re := hmono ⟨hs'I.1, hs'I.2.trans ht.2⟩ ht hs'I.2
    have h2 : α ≤ (γ s').re := by
      have hlim : Tendsto (fun s => (γ s).re) (𝓝[>] a) (𝓝 α) := (hreC.tendsto a).mono_left nhdsWithin_le_nhds
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsGT hs'I.1] with s hs
      exact (hmono ⟨hs.1, hs.2.trans (hs'I.2.trans ht.2)⟩ ⟨hs'I.1, hs'I.2.trans ht.2⟩ hs.2).le
    linarith
  have hlt_right : ∀ t ∈ Ioo a b, (γ t).re < ω := by
    intro t ht
    set s' := (t + b) / 2 with hs'
    have hs'I : s' ∈ Ioo t b := ⟨left_lt_add_div_two.2 ht.2, add_div_two_lt_right.2 ht.2⟩
    have h1 : (γ t).re < (γ s').re := hmono ht ⟨ht.1.trans hs'I.1, hs'I.2⟩ hs'I.1
    have h2 : (γ s').re ≤ ω := by
      have hlim : Tendsto (fun s => (γ s).re) (𝓝[<] b) (𝓝 ω) := (hreC.tendsto b).mono_left nhdsWithin_le_nhds
      have : (𝓝[<] b).NeBot := nhdsLT_neBot_of_exists_lt ⟨a, hab⟩
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioo_mem_nhdsLT hs'I.2] with s hs
      exact (hmono ⟨ht.1.trans hs'I.1, hs'I.2⟩ ⟨(ht.1.trans hs'I.1).trans hs.1, hs.2⟩ hs.1).le
    linarith
  -- every point of `(α, ω)` is a lifted point
  have hsurj : ∀ x ∈ Ioo α ω, ∃ s ∈ Ioo a b, (γ s).re = x := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := intermediate_value_Icc hab.le hreC.continuousOn ⟨hx.1.le, hx.2.le⟩
    refine ⟨s, ⟨lt_of_le_of_ne hs.1 ?_, lt_of_le_of_ne hs.2 ?_⟩, hsx⟩
    · rintro rfl; exact hx.1.ne hsx
    · rintro rfl; exact hx.2.ne' hsx
  -- the limits along the arc
  have hlim : ∀ s ∈ Ioo a b, ∃ y, Tendsto (fun u => f (g u)) (𝓝[H] (γ s)) (𝓝 y) ∧ Φ y = η (tL + s) ∧
      y.im = 0 := by
    intro s hs
    obtain ⟨ρ, hρ, hρc⟩ := hcol s hs
    have hsI : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
    obtain ⟨y, hy, hΦy, hyim⟩ := exists_tendsto_comp_of_collar hch hfin hgc
      (show 0 ≤ (γ s).im by rw [hreal s hsI]) hρ hρc
    rw [hlift s hsI] at hΦy
    have hle : tL + s ≤ q := by rw [← hqb]; exact add_le_add le_rfl hs.2.le
    refine ⟨y, hy, hΦy, le_antisymm (not_lt.1 fun hpos => ?_) hyim⟩
    have hH : η (tL + s) ∈ H := hΦy ▸ (hch.inv_mem hpos).1
    exact (hch.inv_mem hpos).2 (hΦy ▸ mem_fillH_of_mem_H hle hH)
  -- the extended composite
  set G : ℂ → ℂ := extendFrom H (fun u => f (g u)) with hG
  have hclH : Hbar ⊆ closure H := by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  -- collars at every point of `(α, ω)`
  have hrad : ∀ x ∈ Ioo α ω, ∃ r > 0, r ≤ min (x - α) (ω - x) ∧ g '' (ball (x : ℂ) r ∩ H) ⊆ D := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hsurj x hx
    obtain ⟨ρ, hρ, hρc⟩ := hcol s hs
    have hγs : γ s = (x : ℂ) := by rw [hγr s ⟨hs.1.le, hs.2.le⟩, hsx]
    refine ⟨min ρ (min (x - α) (ω - x)), lt_min hρ (lt_min (by linarith [hx.1]) (by linarith [hx.2])),
      min_le_right _ _, fun _ ⟨u, hu, he⟩ => hρc ⟨u, ⟨?_, hu.2⟩, he⟩⟩
    rw [hγs]; exact ball_subset_ball (min_le_left _ _) hu.1
  -- limits of the composite at the real points of `(α, ω)` and inside the collars
  have hlimR : ∀ x ∈ Ioo α ω, ∃ y, Tendsto (fun u => f (g u)) (𝓝[H] (x : ℂ)) (𝓝 y) ∧ y.im = 0 ∧
      ∃ s ∈ Ioo a b, (γ s).re = x ∧ Φ y = η (tL + s) := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hsurj x hx
    obtain ⟨y, hy, hΦy, hyim⟩ := hlim s hs
    have hγs : γ s = (x : ℂ) := by rw [hγr s ⟨hs.1.le, hs.2.le⟩, hsx]
    rw [hγs] at hy
    exact ⟨y, hy, hyim, s, hs, hsx, hΦy⟩
  have hlimH : ∀ x ∈ Ioo α ω, ∀ r > 0, g '' (ball (x : ℂ) r ∩ H) ⊆ D → ∀ z ∈ H ∩ ball (x : ℂ) r,
      Tendsto (fun u => f (g u)) (𝓝[H] z) (𝓝 (f (g z))) := by
    intro x _ r _ hrc z hz
    have hgz : g z ∈ D := hrc ⟨z, ⟨hz.2, hz.1⟩, rfl⟩
    have hgca : ContinuousAt g z :=
      (hgc.mono fun w (hw : w ∈ H) => (le_of_lt hw : 0 ≤ w.im)).continuousAt (QuantumZipper.isOpen_H.mem_nhds hz.1)
    have hfca : ContinuousAt f (g z) := hch.cont.continuousAt (hDo.mem_nhds hgz)
    exact (hfca.comp hgca).tendsto.mono_left nhdsWithin_le_nhds
  have hrbc : ∀ x ∈ Ioo α ω, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
    intro x hx
    obtain ⟨r, hr, hrle, hrc⟩ := hrad x hx
    have hreI : ∀ z ∈ ball (x : ℂ) r, z.re ∈ Ioo α ω := fun z hz => Sec7.R6Cor.re_mem_Ioo_of_mem_ball hrle hz
    have hGH : ∀ z ∈ H ∩ ball (x : ℂ) r, G z = f (g z) := fun z hz =>
      extendFrom_eq (subset_closure hz.1) (hlimH x hx r hr hrc z hz)
    have hgD : ∀ z ∈ H ∩ ball (x : ℂ) r, g z ∈ D := fun z hz => hrc ⟨z, ⟨hz.2, hz.1⟩, rfl⟩
    have hreal' : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ y, Tendsto (fun u => f (g u)) (𝓝[H] z) (𝓝 y) ∧ y.im = 0 := by
      intro z hz hz0
      obtain ⟨y, hy, hyim, -⟩ := hlimR z.re (hreI z hz)
      have hzr : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [hz0])
      rw [hzr] at hy
      exact ⟨y, hy, hyim⟩
    refine ⟨r, hr, ?_, ?_, fun z hz hz0 => ?_, fun z hz => ?_, fun z hz w hw hzw => ?_⟩
    · refine DifferentiableOn.congr ?_ hGH
      exact hfd.comp (hgd.mono inter_subset_left) hgD
    · refine continuousOn_extendFrom (fun z hz => hclH hz.1) fun z hz => ?_
      rcases (show 0 ≤ z.im from hz.1).lt_or_eq with hpos | h0
      · exact ⟨_, hlimH x hx r hr hrc z ⟨hpos, hz.2⟩⟩
      · obtain ⟨y, hy, -⟩ := hreal' z hz.2 h0.symm
        exact ⟨y, hy⟩
    · obtain ⟨y, hy, hyim⟩ := hreal' z hz hz0
      have hzcl : z ∈ closure H := hclH (show (0 : ℝ) ≤ z.im by rw [hz0])
      have hGz : G z = y := extendFrom_eq hzcl hy
      rw [hGz]
      exact hyim
    · rw [hGH z hz]; exact hch.maps (hgD z hz)
    · rw [hGH z hz, hGH w hw] at hzw
      exact hgi hz.1 hw.1 (hch.injOn (hgD z hz) (hgD w hw) hzw)
  have hmonoG := (Sec7.R6Cor.strictMonoOn_continuousOn_re_of_forall hrbc).1
  -- values on `(α, ω)`
  have hGval : ∀ x ∈ Ioo α ω, (G x).im = 0 ∧ ∃ s ∈ Ioo a b, (γ s).re = x ∧ Φ (G x) = η (tL + s) ∧
      Tendsto (fun u => f (g u)) (𝓝[H] (x : ℂ)) (𝓝 (G x)) := by
    intro x hx
    obtain ⟨y, hy, hyim, s, hs, hsx, hΦy⟩ := hlimR x hx
    have hxcl : (x : ℂ) ∈ closure H := hclH (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
    have hGx : G x = y := extendFrom_eq hxcl hy
    rw [hGx]
    exact ⟨hyim, s, hs, hsx, hΦy, hy⟩
  have hGne : ∀ x ∈ Ioo α ω, (G x).re ≠ 0 := by
    intro x hx h0
    obtain ⟨him, s, hs, -, hΦ, -⟩ := hGval x hx
    have hG0 : G x = 0 := Complex.ext h0 him
    rw [hG0, hch.tip] at hΦ
    have hsq : tL + s ∈ Icc 0 q := ⟨zero_le, by rw [← hqb]; exact add_le_add le_rfl hs.2.le⟩
    have hqI : q ∈ Icc 0 q := ⟨zero_le, le_rfl⟩
    have := hinj hqI hsq hΦ
    rw [← hqb] at this
    exact (ne_of_lt hs.2) (add_left_cancel this).symm
  -- the composite tends to `0` at the lifted tip
  have hγb : γ b = (ω : ℂ) := hγr b ⟨hab.le, le_rfl⟩
  have hsmall : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Ioo α ω, ω - x < δ → ‖G x‖ ≤ ε := by
    intro ε hε
    have ht0 := tendsto_zero_at_tip hch hq
    obtain ⟨δ₁, hδ₁, hf⟩ := Metric.tendsto_nhdsWithin_nhds.1 ht0 ε hε
    have hgb : g (γ b) = η q := by rw [hlift b ⟨hab.le, le_rfl⟩, hqb]
    obtain ⟨δ₂, hδ₂, hg⟩ := Metric.continuousWithinAt_iff.1
      (hgc (γ b) (show (0 : ℝ) ≤ (γ b).im by rw [hreal b ⟨hab.le, le_rfl⟩])) δ₁ hδ₁
    refine ⟨δ₂ / 2, half_pos hδ₂, fun x hx hxω => ?_⟩
    obtain ⟨r, hr, -, hrc⟩ := hrad x hx
    obtain ⟨-, -, -, -, -, hT⟩ := hGval x hx
    have hT' := hT.norm
    have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1
      (hclH (show (0 : ℝ) ≤ ((x : ℂ)).im by simp))
    refine le_of_tendsto hT' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (x : ℂ) (lt_min hr (half_pos hδ₂)))] with u hu hub
    have hgu : g u ∈ D := hrc ⟨u, ⟨ball_subset_ball (min_le_left _ _) hub, hu⟩, rfl⟩
    have hdu : dist u (γ b) < δ₂ := by
      rw [hγb]
      have h1 : dist u (x : ℂ) < δ₂ / 2 := lt_of_lt_of_le (mem_ball.1 hub) (min_le_right _ _)
      have h2 : dist (x : ℂ) (ω : ℂ) = ω - x := by
        rw [dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [hx.2])]
        ring
      linarith [dist_triangle u (x : ℂ) (ω : ℂ)]
    have h3 := hg (show 0 ≤ u.im from le_of_lt hu) hdu
    rw [hgb] at h3
    have h4 := hf hgu h3
    rw [dist_zero_right] at h4
    exact h4.le
  -- the sign
  have hneg : ∀ x ∈ Ioo α ω, (G x).re < 0 := by
    intro x hx
    refine lt_of_le_of_ne (not_lt.1 fun hpos => ?_) (hGne x hx)
    obtain ⟨δ, hδ, hδG⟩ := hsmall ((G x).re / 2) (half_pos hpos)
    set x' : ℝ := max ((x + ω) / 2) (ω - δ / 2) with hx'
    have hx'I : x' ∈ Ioo α ω := by
      refine ⟨lt_of_lt_of_le hx.1 (le_trans (le_of_lt (left_lt_add_div_two.2 hx.2)) (le_max_left _ _)), ?_⟩
      exact max_lt (add_div_two_lt_right.2 hx.2) (by linarith)
    have hxx' : x < x' := lt_of_lt_of_le (left_lt_add_div_two.2 hx.2) (le_max_left _ _)
    have h1 := hmonoG hx hx'I hxx'
    have h2 := hδG x' hx'I (by linarith [le_max_right ((x + ω) / 2) (ω - δ / 2)])
    have h3 := Complex.abs_re_le_norm (G x')
    have h4 := le_abs_self (G x').re
    linarith
  intro t ht
  have htI : (γ t).re ∈ Ioo α ω := ⟨hlt_left t ht, hlt_right t ht⟩
  obtain ⟨him, s, hs, hsx, hΦ, hT⟩ := hGval _ htI
  have hst : s = t := hmono.injOn hs ht hsx
  subst hst
  have hγs : ((((γ s).re : ℝ)) : ℂ) = γ s := (hγr s ⟨hs.1.le, hs.2.le⟩).symm
  have hGr : G ((γ s).re) = (((G ((γ s).re)).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨(G ((γ s).re)).re, hneg _ htI, ?_, ?_⟩
  · have hT2 := hT
    rw [hγs] at hT2
    rw [← hGr]
    convert hT2 using 2
    rw [hγs]
  · rw [← hGr]; exact hΦ

/-- A point of a proper curve before time `q` is at positive distance from the curve after `q`. -/
theorem exists_ball_disjoint_tail {β : ℝ≥0 → ℂ} (hβ : IsProperCurve β) {s₀ q : ℝ≥0} (hs₀ : s₀ < q) :
    ∃ δ > 0, ∀ u : ℝ≥0, q ≤ u → β u ∉ ball (β s₀) δ := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (hβ.2.2.2.eventually (eventually_gt_atTop (‖β s₀‖ + 1)))
  set T := max T₀ q with hT
  have hK : IsCompact (β '' Icc q T) := isCompact_Icc.image hβ.1
  have hnot : β s₀ ∉ β '' Icc q T := by
    rintro ⟨u, hu, he⟩
    exact (ne_of_gt (lt_of_lt_of_le hs₀ hu.1)) (hβ.2.1 he)
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl _ hnot
  refine ⟨min δ 1, lt_min hδ one_pos, fun u hu hub => ?_⟩
  rcases le_or_gt u T with huT | huT
  · exact hδK (ball_subset_ball (min_le_left _ _) hub) ⟨u, ⟨hu, huT⟩, rfl⟩
  · have h1 := hT₀ u (le_trans (le_max_left _ _) huT.le)
    have h2 : dist (β u) (β s₀) < 1 := lt_of_lt_of_le (mem_ball.1 hub) (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have h3 : ‖β u‖ ≤ ‖β s₀‖ + ‖β u - β s₀‖ := by
      have := norm_add_le (β s₀) (β u - β s₀)
      rwa [add_sub_cancel] at this
    linarith

/-- **The second transition gap** (Lemma S3, p. 580). Let `f`, `Φ` be the chart of `η([0, q])`, `β'` a proper
completion of `η` up to `q` with the old history `A` on its closed right side, and `F` a nontrivial approach to an
interior point `p = η(s₀)` from the left side of `β'` inside the joint domain along which `f → y`, `Φ(y) = p`. Then
a ball about `y` misses `f(fill(A ∪ η([0, q])) ∖ fill(η([0, q])))`. -/
theorem exists_ball_disjoint_second_transition {f Φ : ℂ → ℂ} {η : ℝ≥0 → ℂ} {q : ℝ≥0}
    (hch : IsChartCore η q f Φ) (hηc : IsCompact (η '' Icc 0 q))
    {β' : ℝ≥0 → ℂ} (hβ' : IsProperCurve β') (hβ'0 : (β' 0).im = 0) (hag : ∀ s ≤ q, β' s = η s)
    {A : Set ℂ} (hAc : IsCompact A) (hA : A ⊆ closedRightSide β')
    {F : Filter ℂ} [F.NeBot] (hFL : F ≤ 𝓟 (leftSide β')) (hFB : F ≤ 𝓟 (H \ fillH (A ∪ η '' Icc 0 q)))
    {s₀ : ℝ≥0} (hs₀ : s₀ < q) {y : ℝ} (hfy : Tendsto f F (𝓝 (y : ℂ))) (hΦy : Φ y = η s₀) :
    ∃ r > 0, Disjoint (ball (y : ℂ) r) (f '' (fillH (A ∪ η '' Icc 0 q) \ fillH (η '' Icc 0 q))) := by
  set X : Set ℂ := A ∪ η '' Icc 0 q with hX
  have hXc : IsClosed X := (hAc.union hηc).isClosed
  obtain ⟨δ, hδ, hδt⟩ := exists_ball_disjoint_tail hβ' hs₀
  have hyHb : (y : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((y : ℂ)).im by simp
  obtain ⟨r, hr, hrΦ⟩ := Metric.continuousWithinAt_iff.1 (hch.inv_cont _ hyHb) δ hδ
  refine ⟨r, hr, ?_⟩
  set S : Set ℂ := Φ '' (ball (y : ℂ) r ∩ H) with hS
  have hSpc : IsPreconnected S :=
    ((convex_ball _ _).inter convex_H).isPreconnected.image _
      (hch.inv_cont.mono fun w hw => QuantumZipper.H_subset_Hbar hw.2)
  have hSD : S ⊆ H \ fillH (η '' Icc 0 q) := by
    rintro _ ⟨w, hw, rfl⟩; exact hch.inv_mem hw.2
  have hSball : ∀ z ∈ S, dist z (β' s₀) < δ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hag s₀ hs₀.le, ← hΦy]
    exact hrΦ (QuantumZipper.H_subset_Hbar hw.2) (mem_ball.1 hw.1)
  have hScompl : S ⊆ (seedRayClosure β')ᶜ := by
    intro z hz hzS
    have hzH := (hSD hz).1
    rcases hzS with ⟨u, hu⟩ | ⟨-, him⟩
    · rcases le_or_gt u q with huq | huq
      · rw [hag u huq] at hu
        exact (hSD hz).2 (hu ▸ mem_fillH_of_mem_H huq (hu.symm ▸ hzH))
      · exact hδt u huq.le (by rw [mem_ball, hu]; exact hSball z hz)
    · rw [hβ'0] at him
      exact absurd hzH (not_lt.2 him)
  -- a point of the approach in `S`
  obtain ⟨z₀, hz₀L, hz₀B, hz₀f⟩ : ∃ z₀, z₀ ∈ leftSide β' ∧ z₀ ∈ H \ fillH X ∧ f z₀ ∈ ball (y : ℂ) r := by
    have hL1 : ∀ᶠ z in F, z ∈ leftSide β' := hFL (mem_principal_self _)
    have hB1 : ∀ᶠ z in F, z ∈ H \ fillH X := hFB (mem_principal_self _)
    have hf1 : ∀ᶠ z in F, f z ∈ ball (y : ℂ) r := hfy (ball_mem_nhds _ hr)
    have h1 : ∀ᶠ z in F, z ∈ leftSide β' ∧ z ∈ H \ fillH X ∧ f z ∈ ball (y : ℂ) r :=
      hL1.and (hB1.and hf1)
    exact h1.exists
  have hz₀D : z₀ ∈ H \ fillH (η '' Icc 0 q) :=
    ⟨hz₀B.1, fun hK => hz₀B.2 (fillH_mono subset_union_right hK)⟩
  have hz₀S : z₀ ∈ S := ⟨f z₀, ⟨hz₀f, hch.maps hz₀D⟩, hch.inv_f z₀ hz₀D⟩
  -- `S` lies on the left side of `β'`
  have hSL : S ⊆ leftSide β' := by
    have h1 := hSpc.subset_connectedComponentIn hz₀S hScompl
    unfold leftSide at hz₀L ⊢
    rwa [← connectedComponentIn_eq hz₀L] at h1
  -- hence off `A`, and in the joint unbounded domain
  have hSX : S ⊆ H \ closure X := by
    intro z hz
    refine ⟨(hSD hz).1, ?_⟩
    rw [hXc.closure_eq]
    rintro (hzA | hzη)
    · rcases hA hzA with hR | hS'
      · exact Set.disjoint_left.1 (Supp9B.disjoint_leftSide_rightSide hβ' hβ'0) (hSL hz) hR
      · exact hScompl hz hS'
    · exact (hSD hz).2 ⟨(hSD hz).1, Or.inl (subset_closure hzη)⟩
  have hSB : S ⊆ H \ fillH X := by
    intro z hz
    refine ⟨(hSD hz).1, fun hzK => ?_⟩
    rcases hzK.2 with hcl | hbd
    · exact (hSX hz).2 hcl
    · have hcc : connectedComponentIn (H \ closure X) z = connectedComponentIn (H \ closure X) z₀ := by
        have h1 := hSpc.subset_connectedComponentIn hz₀S hSX
        exact (connectedComponentIn_eq (h1 hz)).symm
      rw [hcc] at hbd
      exact hz₀B.2 ⟨hz₀B.1, Or.inr hbd⟩
  refine Set.disjoint_left.2 fun v hvb ⟨w, hw, hwv⟩ => ?_
  have hwD : w ∈ H \ fillH (η '' Icc 0 q) := ⟨hw.1.1, hw.2⟩
  have hwS : w ∈ S := ⟨f w, ⟨hwv ▸ hvb, hch.maps hwD⟩, hch.inv_f w hwD⟩
  exact (hSB hwS).2 hw.1

/-- **The second-path geometry of Lemma S3** (p. 580, "Its exposed second-left component …"), deterministic. Let
`A = p([0, 1])` be the old history with left entry chart `c` (inverse extension `g`, finite fibres), `β'` a proper
witness from `0` with `A` on its closed right side, and `η` the actual second trace (a generating trace of `w` up to
`ζ`, injective) agreeing with `β'` up to `q = t_L + b`. Then S2's lift `γ` (from `t_L`, `β'(t_L) = L`) satisfies, for
every common arc `β'([t_L + a, t_L + b]) ⊆ A` with interior tip `η(q)` and `q < ζ`, and every `t ∈ (a, b)`:
the old collar facts of `exists_positive_left_joint_collar_of_s2`, the collar lies on the left side of `β'`, and along
`F = g_*(𝓝[ℍ] γ(t))` the second chart `f_q` tends to a **negative** real `y` (the left prime end, `Φ_q(y) = η(t_L + t)`)
with a ball about `y` missing `f_q(fill(A ∪ η[0, q]) ∖ fill(η[0, q]))`. -/
theorem exists_second_geometry_of_s2 {p : ℝ → ℂ} (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
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
        Tendsto g (𝓝[H] (γ t)) (𝓝 (η (tL + t))) ∧
        ∃ y : ℝ, y < 0 ∧
          Tendsto (fwdMap (fun r : ℝ => w r.toNNReal) (tL + b)) (Filter.map g (𝓝[H] (γ t))) (𝓝[H] (y : ℂ)) ∧
          extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) (tL + b)) y = η (tL + t) ∧
          ∃ r > 0, Disjoint (ball (y : ℂ) r) (fwdMap (fun r : ℝ => w r.toNNReal) (tL + b) ''
            (fillH (p '' Icc 0 1 ∪ η '' Icc 0 (tL + b)) \ fillH (η '' Icc 0 (tL + b)))) := by
  obtain ⟨tL, γ, htL, hγp, hγ0, hlift, hcol⟩ :=
    exists_positive_left_joint_collar_of_s2 hp hp0 hpH hβ' hβ'0 hA hc hgc hgi hgf
  refine ⟨tL, γ, htL, hγp, hγ0, hlift, fun a b t ht harc hqζ hqH hag => ?_⟩
  set q : ℝ≥0 := tL + b with hqdef
  set A : Set ℂ := p '' Icc 0 1 with hAdef
  have hAc : IsCompact A := isCompact_Icc.image_of_continuousOn hp
  have hab : a < b := ht.1.trans ht.2
  have hq0 : 0 < q := lt_of_lt_of_le (lt_of_le_of_lt zero_le hab) le_add_self
  obtain ⟨hch, hK, hHull, -, hfd, hfin⟩ := secondChart_facts hη hw hw0 hinj hqζ hq0
  set f := fwdMap (fun r : ℝ => w r.toNNReal) q with hfdef
  set Φ := extendFrom H (fwdMapInv (fun r : ℝ => w r.toNNReal) q) with hΦdef
  have himg : β' '' Icc 0 q = η '' Icc 0 q := image_congr fun s hs => hag s hs.2
  have hηc : IsCompact (η '' Icc 0 q) := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hqζ.le)
  have hinjq : InjOn η (Icc 0 q) := hinj.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hqζ.le
  have hD := hc.1
  have hgd : DifferentiableOn ℂ g H := hD.isConformal.1.congr fun u hu => hgi hu
  have hgI : InjOn g H := (hgi.symm.injOn_iff.1 hD.isConformal.injOn)
  have hγc : Continuous γ := hγp.1
  have harc' : ∀ s ∈ Icc a b, g (γ s) ∈ A := fun s hs => by
    rw [hlift s]; exact harc ⟨tL + s, ⟨add_le_add le_rfl hs.1, add_le_add le_rfl hs.2⟩, rfl⟩
  have hreal : ∀ s ∈ Icc a b, (γ s).im = 0 := fun s hs =>
    im_eq_zero_of_landing_mem hD hgi (hγp.2.2.1 s) (harc' s hs)
  have hmono : StrictMonoOn (fun s => (γ s).re) (Ioo a b) :=
    strictMonoOn_re_of_lifted_common_arc hp hp0 hc hgc hgi hγp hγ0
      (by rintro _ ⟨s, hs, rfl⟩; exact harc' s ⟨hs.1.le, hs.2.le⟩)
  have hlift' : ∀ s ∈ Icc a b, g (γ s) = η (tL + s) := fun s hs => by
    rw [hlift s, hag]; exact add_le_add le_rfl hs.2
  have hfillsub : H \ fillH (A ∪ β' '' Icc 0 q) ⊆ H \ fillH (η '' Icc 0 q) := fun z hz =>
    ⟨hz.1, fun hK' => hz.2 (fillH_mono (by rw [himg]; exact subset_union_right) hK')⟩
  have hcol' : ∀ s ∈ Ioo a b, ∃ ρ > 0, g '' (ball (γ s) ρ ∩ H) ⊆ H \ fillH (η '' Icc 0 q) := by
    intro s hs
    obtain ⟨-, ρ, hρ, hρc, -, -, -⟩ := hcol a b s hs harc
    exact ⟨ρ, hρ, hρc.trans hfillsub⟩
  have hDo : IsOpen (H \ fillH (η '' Icc 0 q)) := hHull.2.2.1
  obtain ⟨y, hy0, hyT, hΦy⟩ := neg_tendsto_comp_of_lifted_arc (IsChart.toCore hch) hfd hfin hqH hinjq hDo hgc hgd
    hgI hγc hab rfl hreal hmono hlift' hcol' t ht
  obtain ⟨hpos, ρ, hρ, hρc, hρL, hne, hgT⟩ := hcol a b t ht harc
  have hFL : Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (leftSide β' ∩ (H \ fillH (A ∪ η '' Icc 0 q))) := by
    rw [le_principal_iff, mem_map]
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (γ t) hρ)] with u hu hub
    have hgu := hρc ⟨u, ⟨hub, hu⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h1 := image_leftSide_inter_H_subset hp hp0 hc hgc hgi hβ' htL hγp hγ0 hlift
        ⟨u, ⟨hρL ⟨hub, hu⟩, hu⟩, rfl⟩
      exact postCurve_leftSide_subset hβ' hβ'0 htL (realBase_facts hp hp0).2.2.2.1 h1
    · rw [← himg]; exact hgu
  have hFne : (Filter.map g (𝓝[H] (γ t))).NeBot := hne.map g
  have hgt : Tendsto g (𝓝[H] (γ t)) (𝓝 (η (tL + t))) := by
    rw [← hag (tL + t) (add_le_add le_rfl ht.2.le)]
    exact hgT.mono_right nhdsWithin_le_nhds
  have hfF : Tendsto f (Filter.map g (𝓝[H] (γ t))) (𝓝 (y : ℂ)) := hyT
  have hfFH : Tendsto f (Filter.map g (𝓝[H] (γ t))) (𝓝[H] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hfF, ?_⟩
    have := hFL (mem_principal_self _)
    filter_upwards [this] with z hz
    exact hch.maps ⟨hz.2.1, fun hK' => hz.2.2 (fillH_mono subset_union_right hK')⟩
  have hFL' : Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (leftSide β') :=
    hFL.trans (principal_mono.2 inter_subset_left)
  have hFB : Filter.map g (𝓝[H] (γ t)) ≤ 𝓟 (H \ fillH (A ∪ η '' Icc 0 q)) :=
    hFL.trans (principal_mono.2 inter_subset_right)
  obtain ⟨r, hr, hgap⟩ := exists_ball_disjoint_second_transition (IsChart.toCore hch) hηc hβ' (by rw [hβ'0]; simp)
    hag hAc hA hFL' hFB (show tL + t < q from add_lt_add_of_le_of_lt le_rfl ht.2) hfF hΦy
  exact ⟨hpos, hne, hFL, hgt, y, hy0, hfFH, hΦy, r, hr, hgap⟩

end InteractingSLE.Theorem14.SB.S3.Geo
