import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Loewner.YuanFiber

/-!
# Continuous Loewner traces: boundary extension of `F_t` and the tip

Packet GEO-YUAN of `planning/INFRA-GEO.md` §4 (input to Y. Yuan, *Topological characterisations
of Loewner traces*, Indiana Univ. Math. J. 71 (2022), arXiv:2003.05535v4, [Yua22]). Conventions of
QuantumZipper: `W` is a continuous driver with `W 0 = 0`, `K_t = fwdHull W t`, and
`F_t = fwdMapInv W t` is the centred inverse map `w ↦ g_t⁻¹(W_t + w)` of `ℍ` onto `ℍ \ K_t`.

## Main definitions

* `IsLoewnerTrace W η`: `η` is a continuous Loewner trace of `W` ([Yua22] §2): continuous on
  `[0, ∞)`, `η 0 = 0`, and `K_t = fill(η[0, t])` for every `t ≥ 0` (the frozen
  `IsGeneratingTrace` with `T = ∞`, in the `fillH` form).

## Main results

* `exists_norm_fwdMapInv_sub_le`: `F_t` (a conformal bijection `ℍ → ℍ \ K_t`,
  `isConformalBijection_fwdMapInv`) is at bounded distance from the identity.
* `IsLoewnerTrace.hasBdryLimits`: `F_t` has a limit at every point of `ℍ̄`, so its boundary
  extension `extendFrom H (fwdMapInv W t)` is continuous on `ℍ̄` (Carathéodory–Torhorst through
  `exists_continuousOn_extension_of_path_of_tendsto`), and no real point is mapped into `ℍ \ K_t`.
* `IsLoewnerTrace.exists_mem_diff`: strict growth; between `t` and `t'` the trace visits a point of
  `K_{t'} \ K_t`.
* `IsLoewnerTrace.tendsto_fwdMapInv_tip`: **the tip.** `F_t(w) → η(t)` as `w → 0` in `ℍ` (not
  only radially): the trace is the image of the driving point.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE

/-- `η` is a **continuous Loewner trace** of the driver `W` ([Yua22] §2, "a continuous trace ...
with `ξ` as driving function"; Specification p. 3): `η 0 = 0`, `η` is continuous on `[0, ∞)`, and
for every `t ≥ 0` the hull `K_t` of the chordal Loewner chain driven by `W` is the filling of
`η([0, t])`. -/
def IsLoewnerTrace (W : ℝ → ℝ) (η : ℝ → ℂ) : Prop :=
  η 0 = 0 ∧ ContinuousOn η (Ici 0) ∧ ∀ t : ℝ, 0 ≤ t → fwdHull W t = fillH (η '' Icc 0 t)

/-- A function on `ℍ` **has boundary limits** if it has a limit (within `ℍ`) at every point of
`ℍ̄`; its continuous extension to `ℍ̄` is then `extendFrom H f`. -/
def HasBdryLimits (f : ℂ → ℂ) : Prop :=
  ∀ x ∈ Hbar, ∃ y, Tendsto f (𝓝[H] x) (𝓝 y)

theorem closure_H : closure H = Hbar := QuantumZipper.CA.Car.closure_H_eq_Hbar

theorem HasBdryLimits.continuousOn {f : ℂ → ℂ} (hf : HasBdryLimits f) :
    ContinuousOn (extendFrom H f) Hbar :=
  continuousOn_extendFrom (by rw [closure_H]) hf

theorem HasBdryLimits.tendsto {f : ℂ → ℂ} (hf : HasBdryLimits f) {x : ℂ} (hx : x ∈ Hbar) :
    Tendsto f (𝓝[H] x) (𝓝 (extendFrom H f x)) :=
  tendsto_extendFrom (hf x hx)

theorem extendFrom_H_eq {f : ℂ → ℂ} (hf : ContinuousOn f H) {x : ℂ} (hx : x ∈ H) :
    extendFrom H f x = f x :=
  extendFrom_extends hf x hx

/-! ### The inverse Loewner map -/

variable {W : ℝ → ℝ}

theorem continuousOn_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fwdMapInv W t) H :=
  (isConformalBijection_fwdMapInv hW hW0 ht).1.continuousOn

theorem fwdMapInv_zero_time (hW : Continuous W) (hW0 : W 0 = 0) {w : ℂ} (hw : w ∈ H) :
    fwdMapInv W 0 w = w := by
  have h1 := QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 le_rfl hw
  rwa [fwdMap_zero_eq hW hW0 le_rfl
    (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 le_rfl hw)] at h1

/-- `F_t` moves points by a bounded amount: `‖F_t(w) − w‖ ≤ 24 M + 8 √t` if `|W| ≤ M` on
`[0, t]` (through the reverse flow, QuantumZipper `CoreArc.norm_revMap_sub_le`). -/
theorem norm_fwdMapInv_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M) {w : ℂ} (hw : w ∈ H) :
    ‖fwdMapInv W t w - w‖ ≤ 24 * M + 8 * Real.sqrt t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, ht⟩)
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0, fwdMapInv_zero_time hW hW0 hw, sub_self, norm_zero]
    positivity
  rw [QuantumZipper.UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hw]
  have hV : Continuous fun s => W (t - s) - W t :=
    (hW.comp (continuous_const.sub continuous_id)).sub continuous_const
  have := QuantumZipper.CoreArc.norm_revMap_sub_le hV (by simp) hpos (M := 2 * M)
    (fun r hr => ?_) hw
  · linarith
  have h1 := hM (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have h2 := hM t ⟨ht, le_rfl⟩
  calc |W (t - r) - W t| ≤ |W (t - r)| + |W t| := abs_sub _ _
    _ ≤ 2 * M := by linarith

theorem exists_norm_fwdMapInv_sub_le (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ C, ∀ w ∈ H, ‖fwdMapInv W t w - w‖ ≤ C := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hW t
  exact ⟨_, fun w hw => norm_fwdMapInv_sub_le hW hW0 ht hM hw⟩

theorem tendsto_fwdMapInv_cobounded (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fwdMapInv W t) (Bornology.cobounded ℂ ⊓ 𝓟 H) (Bornology.cobounded ℂ) := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ht
  have h1 : Tendsto (fun w : ℂ => ‖w‖) (Bornology.cobounded ℂ ⊓ 𝓟 H) atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have h3 : Tendsto (fun w => ‖fwdMapInv W t w‖) (Bornology.cobounded ℂ ⊓ 𝓟 H) atTop := by
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-C) h1)
    filter_upwards [mem_inf_of_right (mem_principal_self H)] with w hw
    have := hC w hw
    linarith [norm_sub_norm_le w (fwdMapInv W t w), norm_sub_rev w (fwdMapInv W t w)]
  simpa only [comap_norm_atTop] using tendsto_comap_iff.2 h3

/-! ### Fillings only see `ℍ` -/

theorem fillH_congr {A B : Set ℂ} (h : closure A ∩ H = closure B ∩ H) : fillH A = fillH B := by
  have key : ∀ z ∈ H, (z ∈ closure A ↔ z ∈ closure B) := fun z hz =>
    ⟨fun hA => ((Set.ext_iff.1 h z).1 ⟨hA, hz⟩).1, fun hB => ((Set.ext_iff.1 h z).2 ⟨hB, hz⟩).1⟩
  have hd : H \ closure A = H \ closure B := by
    ext z
    simp only [Set.mem_sdiff]
    exact ⟨fun ⟨hz, hn⟩ => ⟨hz, fun hb => hn ((key z hz).2 hb)⟩,
      fun ⟨hz, hn⟩ => ⟨hz, fun ha => hn ((key z hz).1 ha)⟩⟩
  ext z
  simp only [fillH, Set.mem_ofPred_eq, hd]
  constructor
  · rintro ⟨hz, h1 | h1⟩
    · exact ⟨hz, Or.inl ((key z hz).1 h1)⟩
    · exact ⟨hz, Or.inr h1⟩
  · rintro ⟨hz, h1 | h1⟩
    · exact ⟨hz, Or.inl ((key z hz).2 h1)⟩
    · exact ⟨hz, Or.inr h1⟩

/-- Vertical projection of `ℂ` onto `ℍ̄`. -/
def clipH (z : ℂ) : ℂ := (z.re : ℂ) + ((max z.im 0 : ℝ) : ℂ) * I

theorem continuous_clipH : Continuous clipH := by
  unfold clipH
  fun_prop

theorem clipH_im (z : ℂ) : (clipH z).im = max z.im 0 := by simp [clipH]

theorem clipH_mem_Hbar (z : ℂ) : clipH z ∈ Hbar :=
  show 0 ≤ (clipH z).im by rw [clipH_im]; exact le_max_right _ _

theorem clipH_of_mem_H {z : ℂ} (hz : z ∈ H) : clipH z = z := by
  apply Complex.ext <;> simp [clipH, le_of_lt (show 0 < z.im from hz)]

theorem image_clipH_inter_H (A : Set ℂ) : clipH '' A ∩ H = A ∩ H := by
  ext z
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hz⟩
    have hzH : 0 < (clipH a).im := hz
    rw [clipH_im] at hzH
    have haH : a ∈ H := show 0 < a.im by
      rcases le_or_gt a.im 0 with h | h
      · rw [max_eq_right h] at hzH; exact absurd hzH (lt_irrefl 0)
      · exact h
    rw [clipH_of_mem_H haH]
    exact ⟨ha, haH⟩
  · rintro ⟨hz, hzH⟩
    exact ⟨⟨z, hz, clipH_of_mem_H hzH⟩, hzH⟩

/-! ### The boundary extension of `F_t` along a continuous trace -/

variable {η : ℝ → ℂ}

theorem IsLoewnerTrace.isCompact_image (hη : IsLoewnerTrace W η) (t : ℝ) :
    IsCompact (η '' Icc 0 t) :=
  isCompact_Icc.image_of_continuousOn (hη.2.1.mono Icc_subset_Ici_self)

theorem IsLoewnerTrace.exists_extension (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ F : ℂ → ℂ, EqOn F (fwdMapInv W t) H ∧ ContinuousOn F Hbar ∧
      ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W t := by
  set γ : ℝ → ℂ := fun s => clipH (η s) with hγ
  have hγc : ContinuousOn γ (Icc 0 t) :=
    continuous_clipH.comp_continuousOn (hη.2.1.mono Icc_subset_Ici_self)
  have hγH : MapsTo γ (Icc 0 t) Hbar := fun s _ => clipH_mem_Hbar _
  have hfill : fillH (γ '' Icc 0 t) = fwdHull W t := by
    rw [hη.2.2 t ht]
    apply fillH_congr
    have hc1 : IsCompact (γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hγc
    rw [hc1.isClosed.closure_eq, (hη.isCompact_image t).isClosed.closure_eq]
    rw [show γ '' Icc 0 t = clipH '' (η '' Icc 0 t) from (image_image clipH η _).symm]
    exact image_clipH_inter_H _
  have hψ : IsConformalBijection (fwdMapInv W t) H (H \ fillH (γ '' Icc 0 t)) := by
    rw [hfill]; exact isConformalBijection_fwdMapInv hW hW0 ht
  obtain ⟨F, hFeq, hFc, hFfr, -⟩ := exists_continuousOn_extension_of_path_of_tendsto hγc hγH hψ
    (tendsto_fwdMapInv_cobounded hW hW0 ht)
  refine ⟨F, hFeq, hFc, fun x hx hFx => ?_⟩
  have hxH : x ∈ Hbar \ H := ⟨mem_Hbar_of_im_eq_zero hx, fun h => by
    have : 0 < x.im := h
    rw [hx] at this; exact lt_irrefl 0 this⟩
  have hfr := hFfr hxH
  rw [hfill, (isHPHull_fwdHull hW ht).isOpen.frontier_eq] at hfr
  exact hfr.2 hFx

theorem IsLoewnerTrace.hasBdryLimits (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) : HasBdryLimits (fwdMapInv W t) := by
  obtain ⟨F, hFeq, hFc, -⟩ := hη.exists_extension hW hW0 ht
  intro x hx
  refine ⟨F x, ?_⟩
  have h1 : Tendsto F (𝓝[H] x) (𝓝 (F x)) := (hFc x hx).mono H_subset_Hbar
  exact h1.congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)

/-- The boundary extension `F̄_t` of `F_t` maps no real point into `ℍ \ K_t`. -/
theorem IsLoewnerTrace.extendFrom_not_mem (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {x : ℂ} (hx : x.im = 0) :
    extendFrom H (fwdMapInv W t) x ∉ H \ fwdHull W t := by
  obtain ⟨F, hFeq, hFc, hFR⟩ := hη.exists_extension hW hW0 ht
  have hxH : x ∈ Hbar := mem_Hbar_of_im_eq_zero hx
  have h1 : Tendsto (fwdMapInv W t) (𝓝[H] x) (𝓝 (F x)) :=
    ((hFc x hxH).mono H_subset_Hbar).congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)
  rw [extendFrom_eq (by rw [closure_H]; exact hxH) h1]
  exact hFR x hx

/-- **Fibre hypotheses for `F̄_t`.** The extension `F̄_t = extendFrom H F_t` is holomorphic and
injective on `ℍ`, continuous on `ℍ̄`, and maps no real point into `F̄_t(ℍ) = ℍ \ K_t`, so the
fibre lemmas of `YuanFiber.lean` apply to it. -/
theorem IsLoewnerTrace.fiber_hyps (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    DifferentiableOn ℂ (extendFrom H (fwdMapInv W t)) H ∧
      ContinuousOn (extendFrom H (fwdMapInv W t)) Hbar ∧
      InjOn (extendFrom H (fwdMapInv W t)) H ∧
      ∀ x : ℂ, x.im = 0 →
        extendFrom H (fwdMapInv W t) x ∉ extendFrom H (fwdMapInv W t) '' H := by
  have hcb := isConformalBijection_fwdMapInv hW hW0 ht
  have heq : EqOn (extendFrom H (fwdMapInv W t)) (fwdMapInv W t) H := fun x hx =>
    extendFrom_H_eq hcb.1.continuousOn hx
  have himg : extendFrom H (fwdMapInv W t) '' H = H \ fwdHull W t := by
    rw [heq.image_eq]; exact hcb.2.image_eq
  refine ⟨hcb.1.congr heq, (hη.hasBdryLimits hW hW0 ht).continuousOn,
    hcb.2.injOn.congr heq.symm, fun x hx => ?_⟩
  rw [himg]
  exact hη.extendFrom_not_mem hW hW0 ht hx

/-! ### Strict growth -/

theorem fwdHull_mono' {t t' : ℝ} (h : t ≤ t') : fwdHull W t ⊆ fwdHull W t' :=
  (QuantumZipper.fwdHull_mono (W := W)).1 h

/-- The hulls grow strictly: `hcap(K_t) = 2t`. -/
theorem fwdHull_ne_of_lt (hW : Continuous W) (hW0 : W 0 = 0) {t t' : ℝ} (ht : 0 ≤ t)
    (htt' : t < t') : fwdHull W t ≠ fwdHull W t' := by
  intro h
  have ht' : 0 ≤ t' := ht.trans htt'.le
  have h1 := hcap_fwdHull hW hW0 ht
  have h2 := hcap_fwdHull hW hW0 ht'
  have e : (⟨fwdHull W t, isHPHull_fwdHull hW ht⟩ : HPHull) =
      ⟨fwdHull W t', isHPHull_fwdHull hW ht'⟩ := Subtype.ext h
  rw [e, h2] at h1
  linarith

/-- **Strict growth along the trace.** Between `t` and `t'` the trace visits a point of
`K_{t'} \ K_t`. -/
theorem IsLoewnerTrace.exists_mem_diff (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t t' : ℝ} (ht : 0 ≤ t) (htt' : t < t') :
    ∃ u ∈ Ioc t t', η u ∈ fwdHull W t' \ fwdHull W t := by
  by_contra hcon
  push Not at hcon
  have ht' : 0 ≤ t' := ht.trans htt'.le
  set A := η '' Icc 0 t with hA
  set A' := η '' Icc 0 t' with hA'
  have hAc : IsClosed A := (hη.isCompact_image t).isClosed
  have hA'c : IsClosed A' := (hη.isCompact_image t').isClosed
  have hK : fwdHull W t = fillH A := hη.2.2 t ht
  have hK' : fwdHull W t' = fillH A' := hη.2.2 t' ht'
  -- the new trace points in `ℍ` lie in the old hull
  have hsub : A' ∩ H ⊆ fwdHull W t := by
    rintro z ⟨⟨u, hu, rfl⟩, hzH⟩
    by_cases hut : u ≤ t
    · rw [hK]
      exact ⟨hzH, Or.inl (subset_closure ⟨u, ⟨hu.1, hut⟩, rfl⟩)⟩
    · have hmem : η u ∈ fwdHull W t' := by
        rw [hK']; exact ⟨hzH, Or.inl (subset_closure ⟨u, hu, rfl⟩)⟩
      by_contra hn
      exact hcon u ⟨not_le.1 hut, hu.2⟩ ⟨hmem, hn⟩
  obtain ⟨R, hR, hA'R⟩ := exists_closure_subset_ball (hη.isCompact_image t').isBounded
  have hAR : closure A ⊆ ball 0 R :=
    (closure_mono (image_mono (Icc_subset_Icc_right htt'.le))).trans hA'R
  have hU := H_diff_fillH hR hAR
  have hU' := H_diff_fillH hR hA'R
  have hincl : H \ fwdHull W t ⊆ H \ fwdHull W t' := by
    rw [hK, hK', hU, hU']
    refine (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn ?_) ?_
    · exact connectedComponentIn_subset _ _
        (setOf_lt_im_subset_connectedComponentIn hR hAR
          (show R < (((R + 1 : ℝ) : ℂ) * I).im by simp))
    · intro z hz
      have hz' : z ∈ H \ fillH A := by rw [hU]; exact hz
      refine ⟨hz'.1, fun hzA' => ?_⟩
      rw [hA'c.closure_eq] at hzA'
      exact hz'.2 (hK ▸ hsub ⟨hzA', hz'.1⟩)
  apply fwdHull_ne_of_lt hW hW0 ht htt'
  apply Subset.antisymm (fwdHull_mono' htt'.le)
  intro z hz
  by_contra hzt
  exact (hincl ⟨(QuantumZipper.fwdHull_mono (W := W)).2 t' hz, hzt⟩).2 hz

/-! ### The tip -/

/-- **The tip of a continuous Loewner trace.** `F_t(w) → η(t)` as `w → 0` in `ℍ` (an
unrestricted limit, not only along the imaginary axis). Proof: by strict growth there are times
`u ↓ t` with `η(u) ∈ K_{u} \ K_t`; local growth puts `ζ = g_t(η(u)) − W_t` within
`4 (osc W + √(u − t))` of `0`, and `η(u) = F_t(ζ)`; continuity of `F̄_t` at `0` and of `η` at `t`
give `F̄_t(0) = η(t)`. -/
theorem IsLoewnerTrace.tendsto_fwdMapInv_tip (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fwdMapInv W t) (𝓝[H] 0) (𝓝 (η t)) := by
  have hlim := (hη.hasBdryLimits hW hW0 ht).tendsto (mem_Hbar_of_im_eq_zero (z := 0) (by simp))
  suffices hE : extendFrom H (fwdMapInv W t) 0 = η t by rwa [hE] at hlim
  have hδ : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hex : ∀ n : ℕ, ∃ u ∈ Ioc t (t + 1 / ((n : ℝ) + 1)),
      η u ∈ fwdHull W (t + 1 / ((n : ℝ) + 1)) \ fwdHull W t := fun n =>
    hη.exists_mem_diff hW hW0 ht (by linarith [hδ n])
  choose u hu hmem using hex
  have hδ0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- `u n → t`
  have hut : Tendsto u atTop (𝓝[Ici 0] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).add hδ0
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n => (hu n).1.le) (fun n => (hu n).2)
    · exact ht.trans (hu n).1.le
  have hηu : Tendsto (fun n => η (u n)) atTop (𝓝 (η t)) := (hη.2.1 t ht).tendsto.comp hut
  -- the points `ζ n = f_t(η(u n))`
  set ζ : ℕ → ℂ := fun n => fwdMap W t (η (u n)) with hζ
  have hmemH : ∀ n, η (u n) ∈ H \ fwdHull W t := fun n =>
    ⟨(QuantumZipper.fwdHull_mono (W := W)).2 _ (hmem n).1, (hmem n).2⟩
  have hζH : ∀ n, ζ n ∈ H := fun n => QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht (hmemH n)
  have hFζ : ∀ n, fwdMapInv W t (ζ n) = η (u n) := fun n =>
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht (hmemH n)
  have hζ0 : Tendsto ζ atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨d, hd, hdW⟩ := Metric.continuous_iff.1 hW t (ε / 8) (by positivity)
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hδ0) (min d ((ε / 8) ^ 2)) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hδn := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_pos (hδ n)] at hδn
    set δ := 1 / ((n : ℝ) + 1) with hδdef
    have hM : ∀ s ∈ Icc (0 : ℝ) δ, |W (t + s) - W t| ≤ ε / 8 := by
      intro s hs
      have hs' : dist (t + s) t < d := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1]
        exact lt_of_le_of_lt hs.2 (lt_of_lt_of_le hδn (min_le_left _ _))
      exact (le_of_lt (hdW _ hs'))
    have hgrow := QuantumZipper.CoreArc.norm_fwdMap_le_of_mem_diff hW ht (hδ n).le hM
      (hmem n).1 (hmem n).2
    have hsq : Real.sqrt δ < ε / 8 := by
      rw [Real.sqrt_lt' (by positivity)]
      exact lt_of_lt_of_le hδn (min_le_right _ _)
    rw [dist_zero_right]
    calc ‖ζ n‖ ≤ 4 * (ε / 8 + Real.sqrt δ) := hgrow
      _ < ε := by linarith
  have hζH' : Tendsto ζ atTop (𝓝[H] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hζ0, Eventually.of_forall hζH⟩
  have h2 : Tendsto (fun n => η (u n)) atTop (𝓝 (extendFrom H (fwdMapInv W t) 0)) := by
    have := hlim.comp hζH'
    simpa only [Function.comp_def, hFζ] using this
  exact tendsto_nhds_unique h2 hηu

end InteractingSLE
