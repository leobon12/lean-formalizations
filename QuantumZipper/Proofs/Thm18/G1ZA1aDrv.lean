import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.G4Weld2Arc
import QuantumZipper.Proofs.Thm18.LWFarSideMain
import QuantumZipper.Proofs.Thm18.LWFarCondFlow
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.RS.TipA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1a (i): the unzipped and rescaled driver is good

Part (i) of `G1RerootAffineStmt` (`G1ZSplitDefs.lean`, handoff `G1-ZSPLIT.md` item 1): for a good
driver `W` (`G1zDrvGood`), `t > 0`, `a > 0`, the driver `W' = g1zNewDrv W t a`,
`W'(s) = (W(t + a² s⁺) − W t)/a`, is again good, with trace
`η'(s) = f_t(η(t + a² s))/a` (`s > 0`) and hulls `K'_s = η'(0,s]`.

* `tendsto_fwdMapInv_trace`: for a good driver the trace is a genuine limit
  `f̂_s(iy) → η(s)` (Carathéodory extension of the time-reversed reverse map, via
  `LWFar.lwfSide_ctx`; Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.1, 2.6).
* `trace_g1zNewDrv`: the trace of `W'` (Loewner flow property `f̂_{t+u} = f̂_t ∘ f̂^{(t)}_u` and
  Brownian scaling: Lawler, *Conformally Invariant Processes in the Plane*, §4.1, Prop. 4.4/4.13;
  Rohde–Schramm, *Basic properties of SLE*, Prop. 2.1; `RS.fwdMapInv_shift_eq`, `RS.trace_scale`).
* `fwdHull_shift_eq`: `K^{(t)}_u = f_t(η(t, t+u])` (`fwdHull_add_diff`).
* `g1zDrvGood_newDrv`: part (i).

Bookkeeping is own; every analytic input is a proved project lemma.
-/

noncomputable section

open Filter Set Complex
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1a

variable {W : ℝ → ℝ}

theorem tendsto_mul_I_Hbar :
    Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[Hbar] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 ((0 : ℝ) * I)) :=
      ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    show 0 ≤ ((y : ℂ) * I).im
    simpa using (le_of_lt (show (0 : ℝ) < y from hy))

/-- For a good driver, the trace is the genuine limit `f̂_s(iy) → η(s)`. -/
theorem tendsto_fwdMapInv_trace (hG : G1zDrvGood W) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun y : ℝ => fwdMapInv W s (y * I)) (𝓝[>] 0) (𝓝 (trace W s)) := by
  obtain ⟨hW, hW0, -, hη, hK⟩ := hG
  obtain ⟨F, hF⟩ := LWFar.lwfSide_ctx hW hW0 hη.1 hη.2.1 hη.2.2.1 hη.2.2.2.1 hK hs
  have h2 := (hF.Fcont 0 (show (0 : ℂ) ∈ Hbar by simp [Hbar])).tendsto.comp tendsto_mul_I_Hbar
  rw [← hF.F0]
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact hF.Feq (show 0 < ((y : ℂ) * I).im by simpa using (show (0 : ℝ) < y from hy))

/-- For a good driver, `‖f̂_s(w) − w‖` is bounded on `ℍ`. -/
theorem exists_bound_fwdMapInv (hG : G1zDrvGood W) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, ∀ w ∈ H, ‖fwdMapInv W s w - w‖ ≤ C := by
  obtain ⟨hW, hW0, -, hη, hK⟩ := hG
  obtain ⟨F, hF⟩ := LWFar.lwfSide_ctx hW hW0 hη.1 hη.2.1 hη.2.2.1 hη.2.2.2.1 hK hs
  obtain ⟨C, hC⟩ := hF.bound
  exact ⟨C, fun w hw => by rw [← hF.Feq hw]; exact hC w hw⟩

theorem fwdHull_mono_of_good (hG : G1zDrvGood W) {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) :
    fwdHull W s ⊆ fwdHull W u := by
  rw [hG.2.2.2.2 s hs, hG.2.2.2.2 u (hs.trans hsu)]
  exact image_mono fun v hv => ⟨hv.1, hv.2.trans hsu⟩

/-- The trace of the shifted driver `W(t + ·) − W t` is `f_t(η(t + ·))`, as a genuine limit. -/
theorem tendsto_fwdMapInv_shift (hG : G1zDrvGood W) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    Tendsto (fun y : ℝ => fwdMapInv (fun r => W (t + r) - W t) u (y * I)) (𝓝[>] 0)
      (𝓝 (fwdMap W t (trace W (t + u)))) := by
  have hW := hG.1
  have hW0 := hG.2.1
  have hη := hG.2.2.2.1
  have hK := hG.2.2.2.2
  have hmem : trace W (t + u) ∈ H \ fwdHull W t :=
    chord_mem_diff_fwdHull hη hK ht.le (by linarith)
  have hlim := tendsto_fwdMapInv_trace hG (show 0 < t + u by linarith)
  have hcont : ContinuousWithinAt (fwdMap W t) (H \ fwdHull W t) (trace W (t + u)) :=
    (FwdHolo.differentiableOn_fwdMap hW ht.le).continuousOn _ hmem
  have hin : Tendsto (fun y : ℝ => fwdMapInv W (t + u) (y * I)) (𝓝[>] 0)
      (𝓝[H \ fwdHull W t] (trace W (t + u))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    have h1 := RS.fwdMapInv_mem_compl_fwdHull hW hW0 (show (0 : ℝ) ≤ t + u by linarith)
      (RS.mul_I_mem_H hy)
    exact ⟨h1.1, fun hK' => h1.2 (fwdHull_mono_of_good hG ht.le (by linarith) hK')⟩
  refine (hcont.tendsto.comp hin).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (RS.fwdMapInv_shift_eq hW hW0 ht.le hu.le (RS.mul_I_mem_H hy)).symm

theorem g1zNewDrv_eqOn (W : ℝ → ℝ) (t a : ℝ) :
    EqOn (g1zNewDrv W t a) (fun r => (fun s => W (t + s) - W t) (a ^ 2 * r) / a) (Ici 0) := by
  intro r hr
  show (W (t + a ^ 2 * max r 0) - W t) / a = (W (t + a ^ 2 * r) - W t) / a
  rw [max_eq_left (show (0 : ℝ) ≤ r from hr)]

theorem continuous_g1zNewDrv (hW : Continuous W) (t a : ℝ) : Continuous (g1zNewDrv W t a) := by
  unfold g1zNewDrv; fun_prop

theorem g1zNewDrv_zero (W : ℝ → ℝ) (t a : ℝ) : g1zNewDrv W t a 0 = 0 := by
  simp [g1zNewDrv]

/-- **The trace of the new driver**: `η'(s) = f_t(η(t + a² s))/a` for `s > 0`, as a genuine
limit. -/
theorem trace_g1zNewDrv (hG : G1zDrvGood W) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) {s : ℝ}
    (hs : 0 < s) :
    Tendsto (fun y : ℝ => fwdMapInv (g1zNewDrv W t a) s (y * I)) (𝓝[>] 0)
        (𝓝 (fwdMap W t (trace W (t + a ^ 2 * s)) / a)) ∧
      trace (g1zNewDrv W t a) s = fwdMap W t (trace W (t + a ^ 2 * s)) / a := by
  have hW := hG.1
  have hVc : Continuous fun r => W (t + r) - W t := by fun_prop
  have hV0 : (fun r => W (t + r) - W t) 0 = 0 := by simp
  have hUc : Continuous fun r => (fun s => W (t + s) - W t) (a ^ 2 * r) / a := by fun_prop
  have hU0 : (fun r => (fun s => W (t + s) - W t) (a ^ 2 * r) / a) 0 = 0 := by simp
  have h1 := (RS.trace_scale hVc hV0 ha hs.le
    (tendsto_fwdMapInv_shift hG ht (by positivity : 0 < a ^ 2 * s))).1
  have hT : Tendsto (fun y : ℝ => fwdMapInv (g1zNewDrv W t a) s (y * I)) (𝓝[>] 0)
      (𝓝 (fwdMap W t (trace W (t + a ^ 2 * s)) / a)) := by
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (RS.fwdMapInv_congr_Ici (continuous_g1zNewDrv hW t a) (g1zNewDrv_zero W t a) hUc hU0
      (g1zNewDrv_eqOn W t a) hs.le (RS.mul_I_mem_H hy)).symm
  exact ⟨hT, hT.limUnder_eq⟩

/-- The hull of the shifted driver: `K^{(t)}_u = f_t(η(t, t+u])`. -/
theorem fwdHull_shift_eq (hG : G1zDrvGood W) {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    fwdHull (fun r => W (t + r) - W t) u =
      (fun v => fwdMap W t (trace W (t + v))) '' Ioc 0 u := by
  have hW := hG.1
  have hW0 := hG.2.1
  have hη := hG.2.2.2.1
  have hK := hG.2.2.2.2
  have hdiff := fwdHull_add_diff hW (t := t) (s := u) ht.le hu
  ext w
  constructor
  · intro hw
    have hwH : w ∈ H := hw.1
    set z := fwdMapInv W t w with hz
    have hzm := RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht.le hwH
    have hfz := RS.fwdMap_fwdMapInv hW hW0 ht.le hwH
    have hz' : z ∈ fwdHull W (t + u) \ fwdHull W t := by
      rw [hdiff]
      exact ⟨hzm, by rw [hfz]; exact hw⟩
    obtain ⟨hzK, hzK'⟩ := hz'
    rw [hK (t + u) (by linarith)] at hzK
    obtain ⟨v, hv, hvz⟩ := hzK
    have hvt : t < v := by
      by_contra hle
      exact hzK' (by rw [hK t ht.le]; exact ⟨v, ⟨hv.1, not_lt.1 hle⟩, hvz⟩)
    refine ⟨v - t, ⟨by linarith, by linarith [hv.2]⟩, ?_⟩
    show fwdMap W t (trace W (t + (v - t))) = w
    rw [show t + (v - t) = v by ring, hvz, ← hfz]
  · rintro ⟨r, hr, rfl⟩
    have hm : trace W (t + r) ∈ fwdHull W (t + u) \ fwdHull W t :=
      ⟨by rw [hK (t + u) (by linarith)]; exact ⟨t + r, ⟨by linarith [hr.1], by linarith [hr.2]⟩, rfl⟩,
        (chord_mem_diff_fwdHull hη hK ht.le (by linarith [hr.1])).2⟩
    rw [hdiff] at hm
    exact hm.2

/-- The hull of the new driver: `K'_s = η'(0, s]`. -/
theorem fwdHull_g1zNewDrv (hG : G1zDrvGood W) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) {s : ℝ}
    (hs : 0 ≤ s) :
    fwdHull (g1zNewDrv W t a) s = trace (g1zNewDrv W t a) '' Ioc 0 s := by
  have hW := hG.1
  have ha2 : 0 < a ^ 2 := by positivity
  have hUc : Continuous fun r => (fun s => W (t + s) - W t) (a ^ 2 * r) / a := by fun_prop
  ext z
  rw [LWFar.lwc_mem_fwdHull_congr (continuous_g1zNewDrv hW t a) hUc hs
    (fun r hr => g1zNewDrv_eqOn W t a (show (0 : ℝ) ≤ r from hr.1)),
    LoewnerAlgebra.mem_fwdHull_scale_iff (fun s => W (t + s) - W t) ha hs z, fwdHull_shift_eq hG ht (by positivity)]
  constructor
  · rintro ⟨v, hv, hvz⟩
    refine ⟨v / a ^ 2, ⟨div_pos hv.1 ha2, (div_le_iff₀ ha2).2 (by linarith [hv.2])⟩, ?_⟩
    rw [(trace_g1zNewDrv hG ht ha (div_pos hv.1 ha2)).2, mul_div_cancel₀ _ ha2.ne']
    have hvz' : fwdMap W t (trace W (t + v)) = (a : ℂ) * z := hvz
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    rw [hvz']
    field_simp
  · rintro ⟨r, hr, rfl⟩
    refine ⟨a ^ 2 * r, ⟨mul_pos ha2 hr.1, mul_le_mul_of_nonneg_left hr.2 ha2.le⟩, ?_⟩
    rw [(trace_g1zNewDrv hG ht ha hr.1).2]
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp

/-- The trace of the new driver is a simple chord. -/
theorem isSimpleChord_trace_g1zNewDrv (hG : G1zDrvGood W) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    IsSimpleChord (trace (g1zNewDrv W t a)) := by
  have hW := hG.1
  have hW0 := hG.2.1
  have hη := hG.2.2.2.1
  have hK := hG.2.2.2.2
  set g : ℝ → ℂ := fun s => fwdMap W t (trace W (t + a ^ 2 * s)) / a with hg
  have ha2 : 0 < a ^ 2 := by positivity
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have htr : ∀ s, 0 < s → trace (g1zNewDrv W t a) s = g s := fun s hs =>
    (trace_g1zNewDrv hG ht ha hs).2
  have htr0 : trace (g1zNewDrv W t a) 0 = 0 := by
    rw [G1Pkg.trace_zero_time (continuous_g1zNewDrv hW t a), g1zNewDrv_zero, Complex.ofReal_zero]
  have hlt : ∀ s : ℝ, 0 < s → t < t + a ^ 2 * s := fun s hs => by
    have := mul_pos ha2 hs; linarith
  have hmem : ∀ s : ℝ, 0 < s → trace W (t + a ^ 2 * s) ∈ H \ fwdHull W t := fun s hs =>
    chord_mem_diff_fwdHull hη hK ht.le (hlt s hs)
  have hgH : ∀ s : ℝ, 0 < s → g s ∈ H := fun s hs => by
    have h := FwdHolo.mapsTo_fwdMap hW ht.le (hmem s hs)
    show 0 < (fwdMap W t (trace W (t + a ^ 2 * s)) / (a : ℂ)).im
    rw [Complex.div_ofReal_im]
    exact div_pos h ha
  have hgc : ContinuousOn g (Ioi 0) := by
    refine ContinuousOn.div_const ?_ _
    refine (FwdHolo.differentiableOn_fwdMap hW ht.le).continuousOn.comp
      (hη.2.1.comp (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_)
      (fun s hs => hmem s hs)
    intro s hs
    exact mem_Ici.2 (by have := mem_Ioi.1 hs; positivity)
  have htip : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h1 := tendsto_fwdMap_chord_tip hW hη hK ht (lt_add_one t)
    have h2 : Tendsto (fun s : ℝ => t + a ^ 2 * s) (𝓝[>] 0) (𝓝[>] t) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun s hs => hlt s hs⟩
      have hc : Continuous fun s : ℝ => t + a ^ 2 * s := by fun_prop
      have := hc.tendsto 0
      simp only [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := (h1.comp h2).div_const (a : ℂ)
    simpa using this
  refine ⟨htr0, ?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases eq_or_lt_of_le (mem_Ici.1 hs) with h | h
    · subst h
      rw [← continuousWithinAt_Ioi_iff_Ici]
      show Tendsto _ (𝓝[>] 0) (𝓝 (trace (g1zNewDrv W t a) 0))
      rw [htr0]
      exact htip.congr' (eventually_nhdsWithin_of_forall fun y hy => (htr y hy).symm)
    · have hgs : ContinuousAt g s := (hgc s h).continuousAt (Ioi_mem_nhds h)
      have heq : g =ᶠ[𝓝 s] trace (g1zNewDrv W t a) :=
        Filter.eventually_of_mem (Ioi_mem_nhds h) fun y hy => (htr y hy).symm
      exact (hgs.congr heq).continuousWithinAt
  · have hgi : ∀ x y : ℝ, 0 < x → 0 < y → g x = g y → x = y := by
      intro x y hx hy hxy
      have h1 : fwdMap W t (trace W (t + a ^ 2 * x)) = fwdMap W t (trace W (t + a ^ 2 * y)) :=
        (div_left_inj' ha').1 hxy
      have h2 := FwdHolo.injOn_fwdMap hW ht.le (hmem x hx) (hmem y hy) h1
      have h3 := hη.2.2.1 (mem_Ici.2 (le_of_lt (ht.trans (hlt x hx))))
        (mem_Ici.2 (le_of_lt (ht.trans (hlt y hy)))) h2
      have h4 : a ^ 2 * x = a ^ 2 * y := by linarith
      exact mul_left_cancel₀ ha2.ne' h4
    intro x hx y hy hxy
    rcases eq_or_lt_of_le (mem_Ici.1 hx) with hx0 | hx0 <;>
      rcases eq_or_lt_of_le (mem_Ici.1 hy) with hy0 | hy0
    · rw [← hx0, ← hy0]
    · exfalso
      rw [← hx0, htr0, htr y hy0] at hxy
      have h := hgH y hy0
      rw [← hxy] at h
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)
    · exfalso
      rw [← hy0, htr0, htr x hx0] at hxy
      have h := hgH x hx0
      rw [hxy] at h
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)
    · rw [htr x hx0, htr y hy0] at hxy
      exact hgi x y hx0 hy0 hxy
  · intro s hs
    rw [htr s hs]
    exact hgH s hs
  · obtain ⟨C, hC⟩ := exists_bound_fwdMapInv hG ht
    have hlow : ∀ s : ℝ, 0 < s →
        (‖trace W (t + a ^ 2 * s)‖ + -C) / a ≤ ‖trace (g1zNewDrv W t a) s‖ := by
      intro s hs
      rw [htr s hs]
      have hfH := FwdHolo.mapsTo_fwdMap hW ht.le (hmem s hs)
      have hinv := RS.fwdMapInv_fwdMap hW hW0 ht.le (hmem s hs)
      have hb := hC _ hfH
      rw [hinv] at hb
      have h1 := norm_sub_norm_le (trace W (t + a ^ 2 * s)) (fwdMap W t (trace W (t + a ^ 2 * s)))
      show _ ≤ ‖fwdMap W t (trace W (t + a ^ 2 * s)) / (a : ℂ)‖
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      exact div_le_div_of_nonneg_right (by linarith) ha.le
    have hlin : Tendsto (fun s : ℝ => t + a ^ 2 * s) atTop atTop :=
      tendsto_atTop_add_const_left _ t (tendsto_id.const_mul_atTop ha2)
    have hbig : Tendsto (fun s : ℝ => (‖trace W (t + a ^ 2 * s)‖ + -C) / a) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-C) (hη.2.2.2.2.comp hlin)).atTop_div_const ha
    exact tendsto_atTop_mono' _ ((eventually_gt_atTop 0).mono hlow) hbig

/-- **G1Z-A1a (i).** For a good driver, `t > 0`, `a > 0`, the unzipped and rescaled driver
`g1zNewDrv W t a` is good. -/
theorem g1zDrvGood_newDrv (hG : G1zDrvGood W) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    G1zDrvGood (g1zNewDrv W t a) := by
  refine ⟨continuous_g1zNewDrv hG.1 t a, g1zNewDrv_zero W t a, fun s => ?_,
    isSimpleChord_trace_g1zNewDrv hG ht ha, fun s hs => fwdHull_g1zNewDrv hG ht ha hs⟩
  show (W (t + a ^ 2 * max s 0) - W t) / a = (W (t + a ^ 2 * max (max s 0) 0) - W t) / a
  rw [max_eq_left (le_max_right s 0)]

end G1ZA1a
end Thm18Asm
end QuantumZipper
