import QuantumZipper.Proofs.Thm18.G1PkgSel
import QuantumZipper.Proofs.Thm18.G1PkgPath
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.RS.HullBasics

/-!
# G1 package: the trace part `G1TraceSelStmt` of the measurable selection

`G1TraceSelStmt` (G1PkgSel.lean) asks for a version `Tr a` of the Loewner trace driven by
`√κ a`, measurable in the path `a : ℝ≥0 → ℝ` (product σ-algebras), equal to `pathTrace κ a` on
`[0,∞)` whenever `a` is continuous and `pathTrace κ a` is a simple chord.

Construction. Regularize the path (`G1Pkg.pathReg`, G1PkgPath.lean) and recentre it,
`B t a = pathReg a t − pathReg a 0`: a process on path space with measurable coordinates,
continuous paths and `B 0 = 0`, so `a ↦ f̂_t(w)` is measurable (`RS.measurable_fwdMapInv_drive`).
The trace `η(t) = lim_{y↓0} f̂_t(iy)` is a `limUnder` along `𝓝[>] 0`; since `y ↦ f̂_t(iy)` is
continuous on `(0,∞)` (`RS.differentiableOn_fwdMapInv`), it equals the `limUnder` along positive
rationals (`limUnder_rat_eq`; both are the same junk value when no limit exists), which is
measurable (`StronglyMeasurable.limUnder`). For a continuous path whose trace is a simple chord,
`η(0) = 0` forces `a 0 = 0` (`f̂_0(w) = w + W_0`), so `B · a = a` and the version is exact.

Sources: the trace as the radial limit `lim_{y↓0} f̂_t(iy)` is Rohde–Schramm, *Basic properties
of SLE*, Thm 5.1 (via `RS.exists_measurable_sleTrace`, which is the a.s. form of this statement);
the measurability bookkeeping (rational restriction of the radial limit, path regularization) is
an own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Function Topology
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Pkg

/-! ## Radial limits along positive rationals -/

/-- Positive rationals. -/
abbrev PosQ : Type := {q : ℚ // 0 < q}

/-- The filter of positive rationals tending to `0`. -/
def posQFilter : Filter PosQ := Filter.comap (fun q : PosQ => ((q : ℚ) : ℝ)) (𝓝[>] (0 : ℝ))

instance : (posQFilter).IsCountablyGenerated := by
  unfold posQFilter; infer_instance

instance : (posQFilter).NeBot := by
  unfold posQFilter
  refine comap_neBot fun s hs => ?_
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hs
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn (show (0 : ℝ) < ε from hε)
  exact ⟨⟨q, by exact_mod_cast hq0⟩, hsub ⟨hq0, hqε⟩⟩

theorem tendsto_of_rat {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) {L : ℂ}
    (h : Tendsto (fun q : PosQ => f ((q : ℚ) : ℝ)) posQFilter (𝓝 L)) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε hε
  have h2 := h (ε / 2) (by positivity)
  unfold posQFilter at h2
  rw [eventually_comap] at h2
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h2
  filter_upwards [Ioo_mem_nhdsGT hδ] with y hy
  have hc : ContinuousAt f y := hf.continuousAt (Ioi_mem_nhds hy.1)
  obtain ⟨ρ, hρ, hρc⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by positivity)
  obtain ⟨q, hyq, hqm⟩ := exists_rat_btwn (lt_min (by linarith : y < y + ρ) hy.2)
  have hq0 : (0 : ℝ) < q := lt_trans hy.1 hyq
  have hqδ : (q : ℝ) ∈ Ioo 0 δ := ⟨hq0, lt_of_lt_of_le hqm (min_le_right _ _)⟩
  have hqL : dist (f q) L < ε / 2 :=
    hsub hqδ ⟨q, by exact_mod_cast hq0⟩ rfl
  have hqy : dist (f q) (f y) < ε / 2 := by
    refine hρc ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [lt_of_lt_of_le hqm (min_le_left _ _)]
  calc dist (f y) L ≤ dist (f y) (f q) + dist (f q) L := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm] at hqy; exact add_lt_add hqy hqL
    _ = ε := by ring

/-- Junk values of `lim` coincide. -/
theorem lim_eq_of_not_exists {F₁ F₂ : Filter ℂ} (h1 : ¬∃ x, F₁ ≤ 𝓝 x) (h2 : ¬∃ x, F₂ ≤ 𝓝 x) :
    lim F₁ = lim F₂ := by
  simp only [lim, Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg h1,
    dif_neg h2]

/-- **The radial limit along positive rationals.** -/
theorem limUnder_rat_eq {f : ℝ → ℂ} (hf : ContinuousOn f (Ioi 0)) :
    limUnder posQFilter (fun q : PosQ => f ((q : ℚ) : ℝ)) = limUnder (𝓝[>] (0 : ℝ)) f := by
  by_cases hex : ∃ L, Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L)
  · obtain ⟨L, hL⟩ := hex
    have h' : Tendsto (fun q : PosQ => f ((q : ℚ) : ℝ)) posQFilter (𝓝 L) :=
      hL.comp tendsto_comap
    rw [h'.limUnder_eq, hL.limUnder_eq]
  · have hex' : ¬∃ L, Tendsto (fun q : PosQ => f ((q : ℚ) : ℝ)) posQFilter (𝓝 L) :=
      fun ⟨L, hL⟩ => hex ⟨L, tendsto_of_rat hf hL⟩
    exact lim_eq_of_not_exists hex' hex

/-! ## The trace at time `0` -/

theorem fwdMap_zero_time' (W : ℝ → ℝ) {z : ℂ} (hz : z ≠ W 0) : fwdMap W 0 z = z - W 0 := by
  have hex : ∃ u, IsForwardSol W z 0 u := by
    refine ⟨fun _ => z - W 0, continuousOn_const, fun t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    exact ⟨sub_ne_zero.2 hz, by simp⟩
  unfold fwdMap
  rw [dif_pos hex]
  have := (hex.choose_spec.2 0 ⟨le_rfl, le_rfl⟩).2
  simpa using this

theorem fwdMapInv_zero_time {W : ℝ → ℝ} (hW : Continuous W) {w : ℂ} (hw : 0 < w.im) :
    fwdMapInv W 0 w = w + W 0 := by
  have hP : ∀ z' : ℂ, (z' ∈ H \ fwdHull W 0 ∧ fwdMap W 0 z' = w) ↔ z' = w + W 0 := by
    intro z'
    rw [RS.fwdHull_zero_eq_empty hW, sdiff_empty]
    constructor
    · rintro ⟨hz, he⟩
      have hne : z' ≠ (W 0 : ℂ) := fun h => by
        have : (0 : ℝ) < z'.im := hz
        rw [h, Complex.ofReal_im] at this
        exact lt_irrefl _ this
      rw [fwdMap_zero_time' W hne] at he
      rw [← he]; ring
    · rintro rfl
      have him : 0 < (w + (W 0 : ℂ)).im := by simpa using hw
      have hne : w + (W 0 : ℂ) ≠ (W 0 : ℂ) := fun h => by
        rw [h, Complex.ofReal_im] at him; exact lt_irrefl _ him
      exact ⟨him, by rw [fwdMap_zero_time' W hne]; ring⟩
  have hex : ∃! z', z' ∈ H \ fwdHull W 0 ∧ fwdMap W 0 z' = w :=
    ⟨w + W 0, (hP _).2 rfl, fun y hy => (hP y).1 hy⟩
  unfold fwdMapInv
  rw [dif_pos hex]
  exact (hP _).1 hex.choose_spec.1

theorem trace_zero_time {W : ℝ → ℝ} (hW : Continuous W) : trace W 0 = W 0 := by
  unfold trace
  have h : (fun y : ℝ => fwdMapInv W 0 (y * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun y : ℝ => (y : ℂ) * Complex.I + W 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact fwdMapInv_zero_time hW (by simpa using hy)
  refine Tendsto.limUnder_eq ((tendsto_congr' h).2 ?_)
  have hc : Continuous fun y : ℝ => (y : ℂ) * Complex.I + W 0 := by fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  simpa using this

/-- A continuous path whose trace is a simple chord starts at `0`. -/
theorem path_zero_of_simpleChord {κ : ℝ} (hκ : 0 < κ) {a : ℝ≥0 → ℝ} (ha : Continuous a)
    (hs : IsSimpleChord (pathTrace κ a)) : a 0 = 0 := by
  have hW : Continuous fun t : ℝ => Real.sqrt κ * a t.toNNReal :=
    continuous_const.mul (ha.comp continuous_real_toNNReal)
  have h0 := hs.1
  unfold pathTrace at h0
  rw [trace_zero_time hW, Real.toNNReal_zero] at h0
  have h1 : Real.sqrt κ * a 0 = 0 := by exact_mod_cast h0
  have hsq : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  exact (mul_eq_zero.1 h1).resolve_left hsq

/-! ## The measurable version of the trace -/

/-- The recentred regularized path, as a process on path space. -/
def regB (t : ℝ≥0) (a : ℝ≥0 → ℝ) : ℝ := pathReg a t - pathReg a 0

theorem regB_measurable (t : ℝ≥0) : Measurable (regB t) := by
  have h := measurable_pi_iff.1 measurable_pathReg
  show Measurable fun a => pathReg a t - pathReg a 0
  exact (h t).sub (h 0)

theorem regB_continuous (a : ℝ≥0 → ℝ) : Continuous fun t => regB t a :=
  (pathReg_spec.2.1 a).sub continuous_const

theorem regB_zero (a : ℝ≥0 → ℝ) : regB 0 a = 0 := sub_self _

theorem drive_regB {κ : ℝ} {a : ℝ≥0 → ℝ} (ha : Continuous a) (ha0 : a 0 = 0) :
    drive κ regB a = fun t => Real.sqrt κ * a t.toNNReal := by
  funext t
  simp only [drive, regB, pathReg_spec.2.2 a ha, ha0, sub_zero]

/-- The path-measurable version of the trace. -/
def traceSel (κ : ℝ) (a : ℝ≥0 → ℝ) (t : ℝ) : ℂ :=
  if 0 ≤ t then limUnder posQFilter
    (fun q : PosQ => fwdMapInv (drive κ regB a) t ((((q : ℚ) : ℝ) : ℂ) * Complex.I)) else 0

theorem measurable_traceSel (κ : ℝ) : Measurable (traceSel κ) := by
  refine measurable_pi_iff.2 fun t => ?_
  by_cases ht : 0 ≤ t
  · simp only [traceSel, if_pos ht]
    refine (StronglyMeasurable.limUnder fun q : PosQ => ?_).measurable
    refine (RS.measurable_fwdMapInv_drive regB_measurable regB_continuous regB_zero κ ht
      ?_).stronglyMeasurable
    simpa using q.2
  · simp only [traceSel, if_neg ht]
    exact measurable_const

theorem traceSel_eq {κ : ℝ} {a : ℝ≥0 → ℝ} (ha : Continuous a) (ha0 : a 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : traceSel κ a t = pathTrace κ a t := by
  set W : ℝ → ℝ := fun t => Real.sqrt κ * a t.toNNReal with hWdef
  have hW : Continuous W := continuous_const.mul (ha.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [hWdef, ha0]
  have hcont : ContinuousOn (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (Ioi 0) := by
    refine (RS.differentiableOn_fwdMapInv hW hW0 ht).continuousOn.comp
      (by fun_prop) fun y hy => ?_
    show 0 < ((y : ℂ) * Complex.I).im
    simpa using hy
  simp only [traceSel, if_pos ht, drive_regB ha ha0]
  exact limUnder_rat_eq hcont

/-- **`G1TraceSelStmt` holds.** -/
theorem g1TraceSelStmt : G1TraceSelStmt := by
  intro κ hκ _
  refine ⟨traceSel κ, measurable_traceSel κ, fun a ha hs t ht => ?_⟩
  exact traceSel_eq ha (path_zero_of_simpleChord hκ ha hs) ht

end G1Pkg

/-- **`G1PsiSelStmt` from the chord part alone.** -/
theorem g1PsiSelStmt_of_chordUnifSel (hU : G1ChordUnifSelStmt) : G1PsiSelStmt :=
  g1PsiSelStmt_of_parts G1Pkg.g1TraceSelStmt hU

end Thm18Asm
end QuantumZipper
