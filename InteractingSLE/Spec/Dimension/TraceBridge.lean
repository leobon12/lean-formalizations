import InteractingSLE.Foundations.Loewner.YuanTrace
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import QuantumZipper.Proofs.Thm18.ASepCentre

/-!
# The frozen generating trace is QuantumZipper's radial-limit trace

Packet PROVE-T11-DU2, input (O3) of Aux. lemma 15 (`planning/handoffs/PROVE-T11-DU.md`). The frozen
`IsGeneratingTrace w T η` (Specification p. 3) only says that `η` is continuous and generates the
hulls `K_t` for `t < T`. QuantumZipper's trace is the radial limit `γ(t) = lim_{y ↓ 0} F_t(iy)`. This
file proves that they agree before `T`: `F_t(w) → η(t)` as `w → 0` in `ℍ`, so `trace W t = η t`.

The argument is the one of `InteractingSLE.IsLoewnerTrace.tendsto_fwdMapInv_tip`
(`Foundations/Loewner/YuanTrace.lean`, packet GEO-YUAN), which assumes a trace on all of `[0, ∞)`;
here only a finite horizon is available (an evolution lives before its lifetime `ζ`), so the three
steps are redone with hulls and continuity assumed only before `T`:

* `IsLoewnerTraceLT.exists_extension`: `F_t` extends continuously to `ℍ̄` (Carathéodory–Torhorst,
  `exists_continuousOn_extension_of_path_of_tendsto`);
* `IsLoewnerTraceLT.exists_mem_diff`: strict growth, between `t < t' < T` the trace visits
  `K_{t'} \ K_t`;
* `IsLoewnerTraceLT.tendsto_fwdMapInv_tip`: `F_t(w) → η(t)` as `w → 0` in `ℍ`.

A driver of an evolution is continuous only before `ζ`; QuantumZipper's Loewner lemmas need a
continuous driver on `ℝ`. The congruence lemmas `fwdHull_eq_of_eqOn`, `fwdMap_eq_of_eqOn`,
`fwdMapInv_eq_of_eqOn`, `trace_eq_of_eqOn` (no continuity of either driver is needed) let one pass
to the driver frozen after a time `t₂ < ζ`.

## Main results

* `IsGeneratingTrace.tendsto_fwdMapInv_tip`, `IsGeneratingTrace.tendsto_fwdMapInv_mul_I`,
  `IsGeneratingTrace.trace_eq`: for the frozen trace and every `t < T`.
* `IsLoewnerTraceLT.frontier_compl_fwdHull_inter_H_subset`: the frontier of `ℍ \ K_t` in `ℍ` lies in
  `η([0, t])`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv trace IsForwardSol swallowTime)

namespace InteractingSLE

/-! ### Dependence on the driver (no continuity needed) -/

section Congr

variable {W W' : ℝ → ℝ}

theorem mem_fwdHull_iff_forall {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    z ∈ fwdHull W t ↔ z ∈ H ∧ ∀ T : ℝ, 0 ≤ T → (∃ u, IsForwardSol W z T u) → T ≤ t := by
  show (z ∈ H ∧ swallowTime W z ≤ ENNReal.ofReal t) ↔ _
  unfold swallowTime
  constructor
  · rintro ⟨hz, hs⟩
    refine ⟨hz, fun T hT hex => ?_⟩
    exact (ENNReal.ofReal_le_ofReal_iff ht).1 ((sSup_le_iff.1 hs) _ ⟨T, ⟨hT, hex⟩, rfl⟩)
  · rintro ⟨hz, h⟩
    refine ⟨hz, sSup_le ?_⟩
    rintro _ ⟨T, ⟨hT, hex⟩, rfl⟩
    exact ENNReal.ofReal_le_ofReal (h T hT hex)

/-- The hull at time `t` only depends on the driver on `[0, t₂]` for any `t₂ > t`. -/
theorem fwdHull_eq_of_eqOn {t t₂ : ℝ} (ht : 0 ≤ t) (htt₂ : t < t₂)
    (h : ∀ r ∈ Icc (0 : ℝ) t₂, W r = W' r) : fwdHull W t = fwdHull W' t := by
  have key : ∀ {V V' : ℝ → ℝ}, (∀ r ∈ Icc (0 : ℝ) t₂, V r = V' r) →
      fwdHull V t ⊆ fwdHull V' t := by
    intro V V' hV z hz
    rw [mem_fwdHull_iff_forall ht] at hz ⊢
    refine ⟨hz.1, fun T hT ⟨u, hu⟩ => ?_⟩
    by_contra hTt
    have hTt' : t < T := not_le.1 hTt
    have h0 : 0 ≤ min T t₂ := le_min hT (ht.trans htt₂.le)
    have hm : IsForwardSol V' z (min T t₂) u :=
      QuantumZipper.isForwardSol_restrict hu h0 (min_le_left _ _)
    have hm' : IsForwardSol V z (min T t₂) u :=
      QuantumZipper.isForwardSol_congr_drive
        (fun r hr => (hV r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩).symm) hm
    exact absurd (hz.2 _ h0 ⟨u, hm'⟩) (not_le.2 (lt_min hTt' htt₂))
  exact Subset.antisymm (key h) (key fun r hr => (h r hr).symm)

/-- The forward map at time `T` only depends on the driver on `[0, T]`. -/
theorem fwdMap_eq_of_eqOn {z : ℂ} {T : ℝ} (hT : 0 ≤ T) (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) :
    fwdMap W T z = fwdMap W' T z := by
  by_cases hex : ∃ u, IsForwardSol W z T u
  · have hex' : ∃ u, IsForwardSol W' z T u :=
      ⟨hex.choose, QuantumZipper.isForwardSol_congr_drive h hex.choose_spec⟩
    unfold QuantumZipper.fwdMap
    rw [dite_eq_left_of_eq_true (eq_true hex), dite_eq_left_of_eq_true (eq_true hex')]
    exact QuantumZipper.ASep.isForwardSol_unique_any
      (QuantumZipper.isForwardSol_congr_drive h hex.choose_spec) hex'.choose_spec ⟨hT, le_rfl⟩
  · have hex' : ¬ ∃ u, IsForwardSol W' z T u := fun ⟨u, hu⟩ =>
      hex ⟨u, QuantumZipper.isForwardSol_congr_drive (fun r hr => (h r hr).symm) hu⟩
    unfold QuantumZipper.fwdMap
    rw [dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex')]

open Classical in
/-- The inverse map at time `t` only depends on the driver on `[0, t₂]` for any `t₂ > t`. -/
theorem fwdMapInv_eq_of_eqOn {t t₂ : ℝ} (ht : 0 ≤ t) (htt₂ : t < t₂)
    (h : ∀ r ∈ Icc (0 : ℝ) t₂, W r = W' r) : fwdMapInv W t = fwdMapInv W' t := by
  have hK := fwdHull_eq_of_eqOn ht htt₂ h
  have hM : ∀ z, fwdMap W t z = fwdMap W' t z := fun z =>
    fwdMap_eq_of_eqOn ht fun r hr => h r ⟨hr.1, hr.2.trans htt₂.le⟩
  have key : ∀ P Q : ℂ → Prop, P = Q →
      (if h : ∃! z', P z' then h.choose else (0 : ℂ)) =
        (if h : ∃! z', Q z' then h.choose else (0 : ℂ)) := by
    rintro P Q rfl
    rfl
  funext w
  exact key _ _ (funext fun z' => by rw [hK, hM z'])

/-- The radial-limit trace at time `t` only depends on the driver on `[0, t₂]`, `t₂ > t`. -/
theorem trace_eq_of_eqOn {t t₂ : ℝ} (ht : 0 ≤ t) (htt₂ : t < t₂)
    (h : ∀ r ∈ Icc (0 : ℝ) t₂, W r = W' r) : trace W t = trace W' t := by
  unfold QuantumZipper.trace
  rw [fwdMapInv_eq_of_eqOn ht htt₂ h]

end Congr

/-! ### Continuous Loewner traces on a finite horizon -/

/-- `η` is a **continuous Loewner trace of `W` before the horizon `T`**: `η 0 = 0`, `η` is
continuous on `[0, T)`, and `K_t = fill(η[0, t])` for every `0 ≤ t < T` (the frozen
`IsGeneratingTrace` in the `fillH` form, `IsGeneratingTrace.isLoewnerTraceLT`; with `T = ∞` this is
`IsLoewnerTrace`). -/
def IsLoewnerTraceLT (W : ℝ → ℝ) (T : ℝ) (η : ℝ → ℂ) : Prop :=
  η 0 = 0 ∧ ContinuousOn η (Ico 0 T) ∧
    ∀ t : ℝ, 0 ≤ t → t < T → fwdHull W t = fillH (η '' Icc 0 t)

section Finite

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

theorem IsLoewnerTraceLT.isCompact_image (hη : IsLoewnerTraceLT W T η) {t : ℝ} (htT : t < T) :
    IsCompact (η '' Icc 0 t) :=
  isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun _ hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩)

/-- **Boundary extension** of `F_t` for `t < T`. -/
theorem IsLoewnerTraceLT.exists_extension (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    ∃ F : ℂ → ℂ, EqOn F (fwdMapInv W t) H ∧ ContinuousOn F Hbar ∧
      ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W t := by
  set γ : ℝ → ℂ := fun s => clipH (η s) with hγ
  have hηc : ContinuousOn η (Icc 0 t) := hη.2.1.mono fun _ hs => ⟨hs.1, lt_of_le_of_lt hs.2 htT⟩
  have hγc : ContinuousOn γ (Icc 0 t) := continuous_clipH.comp_continuousOn hηc
  have hγH : MapsTo γ (Icc 0 t) Hbar := fun s _ => clipH_mem_Hbar _
  have hfill : fillH (γ '' Icc 0 t) = fwdHull W t := by
    rw [hη.2.2 t ht htT]
    apply fillH_congr
    have hc1 : IsCompact (γ '' Icc 0 t) := isCompact_Icc.image_of_continuousOn hγc
    rw [hc1.isClosed.closure_eq, (hη.isCompact_image htT).isClosed.closure_eq]
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

theorem IsLoewnerTraceLT.hasBdryLimits (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) : HasBdryLimits (fwdMapInv W t) := by
  obtain ⟨F, hFeq, hFc, -⟩ := hη.exists_extension hW hW0 ht htT
  intro x hx
  refine ⟨F x, ?_⟩
  have h1 : Tendsto F (𝓝[H] x) (𝓝 (F x)) := (hFc x hx).mono H_subset_Hbar
  exact h1.congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)

/-- The extension `F̄_t` maps no real point into `ℍ \ K_t`. -/
theorem IsLoewnerTraceLT.extendFrom_not_mem (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) {x : ℂ} (hx : x.im = 0) :
    extendFrom H (fwdMapInv W t) x ∉ H \ fwdHull W t := by
  obtain ⟨F, hFeq, hFc, hFR⟩ := hη.exists_extension hW hW0 ht htT
  have hxH : x ∈ Hbar := mem_Hbar_of_im_eq_zero hx
  have h1 : Tendsto (fwdMapInv W t) (𝓝[H] x) (𝓝 (F x)) :=
    ((hFc x hxH).mono H_subset_Hbar).congr' (eventuallyEq_nhdsWithin_of_eqOn hFeq)
  rw [extendFrom_eq (by rw [closure_H]; exact hxH) h1]
  exact hFR x hx

/-- **Strict growth along the trace** before the horizon. -/
theorem IsLoewnerTraceLT.exists_mem_diff (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t t' : ℝ} (ht : 0 ≤ t) (htt' : t < t') (ht'T : t' < T) :
    ∃ u ∈ Ioc t t', η u ∈ fwdHull W t' \ fwdHull W t := by
  by_contra hcon
  push Not at hcon
  have ht' : 0 ≤ t' := ht.trans htt'.le
  set A := η '' Icc 0 t with hA
  set A' := η '' Icc 0 t' with hA'
  have hA'c : IsClosed A' := (hη.isCompact_image ht'T).isClosed
  have hK : fwdHull W t = fillH A := hη.2.2 t ht (htt'.trans ht'T)
  have hK' : fwdHull W t' = fillH A' := hη.2.2 t' ht' ht'T
  have hsub : A' ∩ H ⊆ fwdHull W t := by
    rintro z ⟨⟨u, hu, rfl⟩, hzH⟩
    by_cases hut : u ≤ t
    · rw [hK]
      exact ⟨hzH, Or.inl (subset_closure ⟨u, ⟨hu.1, hut⟩, rfl⟩)⟩
    · have hmem : η u ∈ fwdHull W t' := by
        rw [hK']; exact ⟨hzH, Or.inl (subset_closure ⟨u, hu, rfl⟩)⟩
      by_contra hn
      exact hcon u ⟨not_le.1 hut, hu.2⟩ ⟨hmem, hn⟩
  obtain ⟨R, hR, hA'R⟩ := exists_closure_subset_ball (hη.isCompact_image ht'T).isBounded
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

/-- **The tip** before the horizon: `F_t(w) → η(t)` as `w → 0` in `ℍ` (`0 ≤ t < T`). -/
theorem IsLoewnerTraceLT.tendsto_fwdMapInv_tip (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    Tendsto (fwdMapInv W t) (𝓝[H] 0) (𝓝 (η t)) := by
  have hlim := (hη.hasBdryLimits hW hW0 ht htT).tendsto
    (mem_Hbar_of_im_eq_zero (z := 0) (by simp))
  suffices hE : extendFrom H (fwdMapInv W t) 0 = η t by rwa [hE] at hlim
  set c : ℝ := (T - t) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hδ : ∀ n : ℕ, (0 : ℝ) < c / ((n : ℝ) + 1) := fun n => by positivity
  have hδT : ∀ n : ℕ, t + c / ((n : ℝ) + 1) < T := fun n => by
    have : c / ((n : ℝ) + 1) ≤ c := div_le_self hc0.le (by linarith [n.cast_nonneg (α := ℝ)])
    linarith
  have hex : ∀ n : ℕ, ∃ u ∈ Ioc t (t + c / ((n : ℝ) + 1)),
      η u ∈ fwdHull W (t + c / ((n : ℝ) + 1)) \ fwdHull W t := fun n =>
    hη.exists_mem_diff hW hW0 ht (by linarith [hδ n]) (hδT n)
  choose u hu hmem using hex
  have hδ0 : Tendsto (fun n : ℕ => c / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul c
    rw [mul_zero] at h1
    refine h1.congr fun n => ?_
    rw [mul_one_div]
  have hut : Tendsto u atTop (𝓝[Ico 0 T] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have hup : Tendsto (fun n : ℕ => t + c / ((n : ℝ) + 1)) atTop (𝓝 t) := by
        simpa using (tendsto_const_nhds (x := t)).add hδ0
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun n => (hu n).1.le) (fun n => (hu n).2)
    · exact ⟨ht.trans (hu n).1.le, lt_of_le_of_lt (hu n).2 (hδT n)⟩
  have hηu : Tendsto (fun n => η (u n)) atTop (𝓝 (η t)) :=
    (hη.2.1 t ⟨ht, htT⟩).tendsto.comp hut
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
    set δ := c / ((n : ℝ) + 1) with hδdef
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

/-- The boundary value of `F̄_t` at the driving point is the tip. -/
theorem IsLoewnerTraceLT.extendFrom_zero (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    extendFrom H (fwdMapInv W t) 0 = η t :=
  extendFrom_eq (by rw [closure_H]; exact mem_Hbar_of_im_eq_zero (z := 0) (by simp))
    (hη.tendsto_fwdMapInv_tip hW hW0 ht htT)

/-- **Radial limits**: `F_t(iy) → η(t)` as `y ↓ 0`, for `0 ≤ t < T`. -/
theorem IsLoewnerTraceLT.tendsto_fwdMapInv_mul_I (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] 0) (𝓝 (η t)) := by
  refine (hη.tendsto_fwdMapInv_tip hW hW0 ht htT).comp ?_
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun y hy => ?_⟩
  · have h1 : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
      (continuous_ofReal.mul continuous_const).tendsto 0
    simpa using h1.mono_left nhdsWithin_le_nhds
  · show 0 < ((y : ℂ) * I).im
    simpa using hy

/-- **The two traces agree** before the horizon: `trace W t = η t` for `0 ≤ t < T`. -/
theorem IsLoewnerTraceLT.trace_eq (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htT : t < T) : trace W t = η t :=
  (hη.tendsto_fwdMapInv_mul_I hW hW0 ht htT).limUnder_eq

/-- The frontier of `ℍ \ K_t` inside `ℍ` lies in the trace prefix `η([0, t])`, `0 ≤ t < T`. -/
theorem IsLoewnerTraceLT.frontier_compl_fwdHull_inter_H_subset (hη : IsLoewnerTraceLT W T η)
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    frontier (H \ fwdHull W t) ∩ H ⊆ η '' Icc 0 t := by
  have hAc : IsClosed (η '' Icc 0 t) := (hη.isCompact_image htT).isClosed
  obtain ⟨R, hR, hAR⟩ := exists_closure_subset_ball (hη.isCompact_image htT).isBounded
  have hU := H_diff_fillH hR hAR
  rw [hAc.closure_eq] at hU
  rw [hη.2.2 t ht htT, hU]
  rintro z ⟨hzf, hzH⟩
  by_contra hzA
  have hO : IsOpen (H \ η '' Icc 0 t) := QuantumZipper.isOpen_H.sdiff hAc
  have hzO : z ∈ H \ η '' Icc 0 t := ⟨hzH, hzA⟩
  set C := connectedComponentIn (H \ η '' Icc 0 t) (((R + 1 : ℝ) : ℂ) * I) with hC
  have hCo : IsOpen C := hO.connectedComponentIn
  have hVo : IsOpen (connectedComponentIn (H \ η '' Icc 0 t) z) := hO.connectedComponentIn
  have hzV : z ∈ connectedComponentIn (H \ η '' Icc 0 t) z := mem_connectedComponentIn hzO
  rw [hCo.frontier_eq] at hzf
  obtain ⟨w, hwV, hwC⟩ := mem_closure_iff.1 hzf.1 _ hVo hzV
  have hCz : C = connectedComponentIn (H \ η '' Icc 0 t) z := by
    rw [hC, connectedComponentIn_eq hwC, ← connectedComponentIn_eq hwV]
  exact hzf.2 (hCz ▸ hzV)

end Finite

/-! ### The frozen `IsGeneratingTrace` -/

section Frozen

/-- The driver `w` frozen after time `t₂` (as a function on `ℝ`): `s ↦ w((min s t₂)⁺)`. It is
continuous on `ℝ` as soon as `w` is continuous on `[0, t₂]`, and agrees with `s ↦ w(s⁺)` on
`[0, t₂]`. -/
def frozenDrive (w : ℝ≥0 → ℝ) (t₂ : ℝ) (s : ℝ) : ℝ := w (min s t₂).toNNReal

theorem continuous_frozenDrive {w : ℝ≥0 → ℝ} {t₂ : ℝ} (hw : ContinuousOn w (Iic t₂.toNNReal)) :
    Continuous (frozenDrive w t₂) :=
  hw.comp_continuous (continuous_real_toNNReal.comp (continuous_id.min continuous_const))
    fun s => show (min s t₂).toNNReal ≤ t₂.toNNReal from
      Real.toNNReal_le_toNNReal (min_le_right _ _)

theorem frozenDrive_eq {w : ℝ≥0 → ℝ} {t₂ : ℝ} {r : ℝ} (hr : r ∈ Icc (0 : ℝ) t₂) :
    frozenDrive w t₂ r = w r.toNNReal := by
  simp only [frozenDrive, min_eq_left hr.2]

theorem frozenDrive_zero {w : ℝ≥0 → ℝ} {t₂ : ℝ} (ht₂ : 0 ≤ t₂) : frozenDrive w t₂ 0 = w 0 := by
  rw [frozenDrive_eq ⟨le_rfl, ht₂⟩, Real.toNNReal_zero]

theorem image_toNNReal_Icc (η : ℝ≥0 → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (fun s : ℝ => η s.toNNReal) '' Icc 0 t = η '' Icc 0 t.toNNReal := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hs.2⟩, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨(r : ℝ), ⟨r.2, ?_⟩, by simp⟩
    have := hr.2
    rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht] at this

variable {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- The frozen generating trace, read on `ℝ`, is a continuous Loewner trace of the frozen driver
before every horizon `t₂ < T`. -/
theorem IsGeneratingTrace.isLoewnerTraceLT (hη : IsGeneratingTrace w T η) {t₂ : ℝ}
    (ht₂T : ENNReal.ofReal t₂ < T) :
    IsLoewnerTraceLT (frozenDrive w t₂) t₂ (fun s : ℝ => η s.toNNReal) := by
  have hle : ∀ s : ℝ, s ≤ t₂ → ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T := fun s hs =>
    (ENNReal.ofReal_le_ofReal hs).trans ht₂T.le
  refine ⟨by simpa using hη.1, ?_, fun t ht htt₂ => ?_⟩
  · refine hη.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    exact hle s hs.2.le
  · have htT : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
      (ENNReal.ofReal_le_ofReal htt₂.le).trans_lt ht₂T
    have hfill := hη.2.2 t.toNNReal htT
    rw [Real.coe_toNNReal _ ht] at hfill
    have hA : IsCompact (η '' Icc 0 t.toNNReal) := isCompact_Icc.image_of_continuousOn
      (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans htT.le)
    rw [fwdHull_eq_of_eqOn ht htt₂ (fun r hr => frozenDrive_eq hr), image_toNNReal_Icc η ht]
    exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed
      ((QuantumZipper.fwdHull_mono).2 _)).1 hfill

theorem exists_real_btwn_of_lt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    ∃ t₂ : ℝ, (t : ℝ) < t₂ ∧ ENNReal.ofReal t₂ < T := by
  obtain ⟨r, htr, hrT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  exact ⟨r, by exact_mod_cast ENNReal.coe_lt_coe.1 htr, by simpa using hrT⟩

theorem continuous_frozenDrive_of_lt (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) {t₂ : ℝ}
    (ht₂T : ENNReal.ofReal t₂ < T) : Continuous (frozenDrive w t₂) :=
  continuous_frozenDrive (hw.mono fun s hs => by
    show (s : ℝ≥0∞) < T
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (show s ≤ t₂.toNNReal from hs)) ht₂T)

/-- **(O3), tip form.** For the frozen generating trace and every `t < T`, `F_t(w) → η(t)` as
`w → 0` in `ℍ` (`w` continuous before `T`, `w 0 = 0`). -/
theorem IsGeneratingTrace.tendsto_fwdMapInv_tip (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) :
    Tendsto (fwdMapInv (fun s : ℝ => w s.toNNReal) t) (𝓝[H] 0) (𝓝 (η t)) := by
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  rw [fwdMapInv_eq_of_eqOn (W := fun s : ℝ => w s.toNNReal) (W' := frozenDrive w t₂) (NNReal.coe_nonneg t) htt₂
    (fun r hr => (frozenDrive_eq hr).symm)]
  have := (hη.isLoewnerTraceLT ht₂T).tendsto_fwdMapInv_tip
    (continuous_frozenDrive_of_lt hw ht₂T) (by rw [frozenDrive_zero ht₂, hw0]) (NNReal.coe_nonneg t) htt₂
  simpa using this

/-- **(O3), radial form.** `F_t(iy) → η(t)` as `y ↓ 0`, for every `t < T`. -/
theorem IsGeneratingTrace.tendsto_fwdMapInv_mul_I (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) :
    Tendsto (fun y : ℝ => fwdMapInv (fun s : ℝ => w s.toNNReal) t (y * I)) (𝓝[>] 0)
      (𝓝 (η t)) := by
  obtain ⟨t₂, htt₂, ht₂T⟩ := exists_real_btwn_of_lt ht
  have ht₂ : 0 ≤ t₂ := (NNReal.coe_nonneg t).trans htt₂.le
  rw [fwdMapInv_eq_of_eqOn (W := fun s : ℝ => w s.toNNReal) (W' := frozenDrive w t₂) (NNReal.coe_nonneg t) htt₂
    (fun r hr => (frozenDrive_eq hr).symm)]
  have := (hη.isLoewnerTraceLT ht₂T).tendsto_fwdMapInv_mul_I
    (continuous_frozenDrive_of_lt hw ht₂T) (by rw [frozenDrive_zero ht₂, hw0]) (NNReal.coe_nonneg t) htt₂
  simpa using this

/-- **(O3).** The frozen generating trace is QuantumZipper's radial-limit trace before `T`. -/
theorem IsGeneratingTrace.trace_eq (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) : trace (fun s : ℝ => w s.toNNReal) t = η t :=
  (hη.tendsto_fwdMapInv_mul_I hw hw0 ht).limUnder_eq

end Frozen

end InteractingSLE
