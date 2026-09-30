import QuantumZipper.Proofs.Zipper.WedgeTipXReg
import QuantumZipper.Proofs.GFF.CoordRegPush
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.GFF.FoldBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `LogImDomRegStmt`: log-dominated functions are regular with their circle averages

For `g : ℂ → ℝ` continuous on `ℍ` with `|g v| ≤ A_R + B_R |log Im v|` on `ℍ ∩ B̄(0, R)`, the
witness `F (w, r) = ∫ g d fc(w, r)` makes `ofFun g` regular (`logImDomRegStmt_holds`).

Proof (own elementary assembly of existing project lemmas):

* **Localization.** `g` is only controlled on bounded sets, with an `R`-dependent coefficient
  `B_R`, and is arbitrary off `ℍ`. For each `R` we replace `g` by the measurable, globally
  log-bounded function `clampG` (`g` on `ℍ`, `0` off `ℍ`, divided by `|B_R| + 1` and clamped
  between `±(A + |log Im|)`), which agrees with `g / (|B_R| + 1)` on `ℍ ∩ B̄(0, R)`, so on every
  folded circle inside `B̄(0, R)` (`integral_eq_mul_clampG`). Folded circles of positive radius
  are a.e. in `ℍ` (`TwoPoint.foldedCircle_ae_mem_H`).
* **Continuity** on `Hbar × (0, ∞)`: `CoordReg.LogBounded.continuousOn` (dominated convergence,
  proved in `TwoPoint.continuousOn_integral_foldedCircle`) for the clamped function.
* **Clause (i)**: `RegClosure.tendsto_of_eval_eq`.
* **Smoothing clause**: the smoothing symmetry `CoordReg.LogBounded.integral_swap`
  (`∫ F(·, ρ) d fc(w, r) = ∫ F(·, r) d fc(w, ρ)`) reduces it to the locally uniform convergence
  `∫ F(·, r) d fc(w, ρ) → F(w, r)` for a function `F` continuous on `Hbar × (0, ∞)`
  (`tluo_fc_of_continuousOn`: uniform continuity on a compact neighbourhood).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace WedgeUnzip
namespace LogImDom

open CircleFubini
open scoped Classical

/-! ## Vanishing smoothing of a continuous witness in the centre variable -/

theorem tluo_fc_of_continuousOn {F : ℂ × ℝ → ℝ} (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) :
    TendstoLocallyUniformlyOn (fun (ρ : ℝ) (p : ℂ × ℝ) => ∫ v, F (v, p.2) ∂foldedCircle p.1 ρ)
      F (𝓝[>] 0) (Hbar ×ˢ Ioi 0) := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have hx2 : 0 < x.2 := hx.2
  set K : Set (ℂ × ℝ) := (closedBall (0 : ℂ) (‖x.1‖ + 2) ∩ Hbar) ×ˢ Icc (x.2 / 2) (x.2 + 1)
    with hK
  have hKc : IsCompact K :=
    ((isCompact_closedBall _ _).inter_right isClosed_Hbar).prod isCompact_Icc
  have hKs : K ⊆ Hbar ×ˢ Ioi 0 := fun q hq =>
    ⟨hq.1.2, show 0 < q.2 from lt_of_lt_of_le (by linarith) hq.2.1⟩
  have huc := hKc.uniformContinuousOn_of_continuous (hF.mono hKs)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc (ε / 2) (by positivity)
  set t : Set (ℂ × ℝ) := {p | ‖p.1‖ < ‖x.1‖ + 1 ∧ x.2 / 2 < p.2 ∧ p.2 < x.2 + 1} with ht_def
  have ht : t ∈ 𝓝[Hbar ×ˢ Ioi 0] x := by
    refine mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds ?_ ?_)
    · exact (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
        ((isOpen_lt continuous_const continuous_snd).inter
          (isOpen_lt continuous_snd continuous_const))
    · exact ⟨by linarith, by linarith, by linarith⟩
  refine ⟨t ∩ (Hbar ×ˢ Ioi 0), inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ one_pos)] with ρ hρ p hp
  obtain ⟨⟨hp1, hp2, hp3⟩, hpH, hp0⟩ := hp
  have hp0' : 0 < p.2 := hp0
  have hρ0 : 0 < ρ := hρ.1
  have hρδ : ρ < δ := hρ.2.trans_le (min_le_left _ _)
  have hρ1 : ρ < 1 := hρ.2.trans_le (min_le_right _ _)
  have hsl : ContinuousOn (fun u => F (u, p.2)) Hbar := RegClosure.continuousOn_slice hF hp0'
  have hpK : p ∈ K := ⟨⟨by rw [mem_closedBall, dist_zero_right]; linarith, hpH⟩,
    by linarith, by linarith⟩
  have key := RegClosure.abs_integral_fc_sub_le (g := fun _ => F p)
    (g' := fun u => F (u, p.2)) (w := p.1) (w' := p.1) (r := ρ) (r' := ρ) (C := ε / 2)
    continuousOn_const hsl (fun θ => by
      set v := foldH (circleMap p.1 ρ θ) with hv
      have hvd : ‖v - p.1‖ ≤ ρ := by
        have := FoldBound.fb_norm_foldH_sub_le (u := circleMap p.1 ρ θ) hpH
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hρ0] at this
        exact this
      have hvK : (v, p.2) ∈ K := by
        refine ⟨⟨?_, foldH_mem_Hbar' _⟩, by linarith, by linarith⟩
        rw [mem_closedBall, dist_zero_right]
        have := norm_sub_norm_le v p.1
        linarith
      have hdist : dist p (v, p.2) < δ := by
        rw [Prod.dist_eq, dist_self, dist_comm, dist_eq_norm]
        exact lt_of_le_of_lt (max_le hvd hρ0.le) hρδ
      have := hδ' p hpK (v, p.2) hvK hdist
      rw [Real.dist_eq] at this
      exact this.le)
  simp only [integral_const, probReal_univ, one_smul] at key
  rw [Real.dist_eq]
  linarith

/-! ## Localization of a log-dominated function -/

/-- The measurable modification: `g` on `ℍ`, `0` elsewhere. -/
def gH (g : ℂ → ℝ) : ℂ → ℝ := H.piecewise g 0

/-- `gH g / c`, clamped between `±(A + |log Im|)`. -/
def clampG (g : ℂ → ℝ) (c A : ℝ) (u : ℂ) : ℝ :=
  max (-(A + |Real.log u.im|)) (min (gH g u / c) (A + |Real.log u.im|))

theorem measurable_gH {g : ℂ → ℝ} (hg : ContinuousOn g H) : Measurable (gH g) :=
  hg.measurable_piecewise continuousOn_const isOpen_H.measurableSet

theorem logBounded_clampG {g : ℂ → ℝ} (hg : ContinuousOn g H) (c : ℝ) {A : ℝ} (hA : 0 ≤ A) :
    CoordReg.LogBounded (clampG g c A) := by
  have hl : Measurable fun u : ℂ => A + |Real.log u.im| :=
    measurable_const.add (continuous_abs.measurable.comp
      (Real.measurable_log.comp Complex.measurable_im))
  have hn : Measurable fun u : ℂ => -(A + |Real.log u.im|) := hl.neg
  refine ⟨Measurable.max hn (Measurable.min ((measurable_gH hg).div_const c) hl), ?_,
    fun R => ⟨A, hA, ?_⟩⟩
  · have hlc : ContinuousOn (fun u : ℂ => A + |Real.log u.im|) H :=
      continuousOn_const.add
        ((Complex.continuous_im.continuousOn.log fun u hu => ne_of_gt hu).abs)
    have hgc : ContinuousOn (fun u => gH g u / c) H :=
      (hg.congr fun u hu => piecewise_eq_of_mem _ _ _ hu).div_const c
    have hn : ContinuousOn (fun u : ℂ => -(A + |Real.log u.im|)) H := hlc.neg
    exact ContinuousOn.sup hn (ContinuousOn.inf hgc hlc)
  · intro u _ _
    have h0 : 0 ≤ A + |Real.log u.im| := by positivity
    rw [clampG, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- The constants of the localization at radius `R`. -/
theorem exists_clamp_consts {g : ℂ → ℝ}
    (hb : ∀ R : ℝ, 0 < R → ∃ A B : ℝ, ∀ v : ℂ, 0 < v.im → ‖v‖ ≤ R →
      |g v| ≤ A + B * |Real.log v.im|) {R : ℝ} (hR : 0 < R) :
    ∃ c A : ℝ, 0 < c ∧ 0 ≤ A ∧ ∀ u ∈ H, ‖u‖ ≤ R → |g u / c| ≤ A + |Real.log u.im| := by
  obtain ⟨A0, B0, h⟩ := hb R hR
  have hc : 0 < |B0| + 1 := by positivity
  refine ⟨|B0| + 1, |A0| / (|B0| + 1), hc, by positivity, fun u hu huR => ?_⟩
  have h1 := h u hu huR
  have hl := abs_nonneg (Real.log u.im)
  have h2 : B0 * |Real.log u.im| ≤ |B0| * |Real.log u.im| :=
    mul_le_mul_of_nonneg_right (le_abs_self B0) hl
  have h3 := le_abs_self A0
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc, add_mul, div_mul_cancel₀ _ hc.ne']
  nlinarith

theorem clampG_eq {g : ℂ → ℝ} {c A R : ℝ}
    (h : ∀ u ∈ H, ‖u‖ ≤ R → |g u / c| ≤ A + |Real.log u.im|) {u : ℂ} (hu : u ∈ H)
    (huR : ‖u‖ ≤ R) : clampG g c A u = g u / c := by
  have e : gH g u = g u := piecewise_eq_of_mem _ _ _ hu
  have hb := abs_le.1 (h u hu huR)
  rw [clampG, e, min_eq_left hb.2, max_eq_right hb.1]

/-- On folded circles inside `B̄(0, R)`, the integral of `g` is `c` times that of `clampG`. -/
theorem integral_eq_mul_clampG {g : ℂ → ℝ} {c A R : ℝ} (hc : 0 < c)
    (h : ∀ u ∈ H, ‖u‖ ≤ R → |g u / c| ≤ A + |Real.log u.im|) (w : ℂ) {r : ℝ} (hr : 0 < r)
    (hwR : ‖w‖ + r ≤ R) :
    ∫ u, g u ∂foldedCircle w r = c * ∫ u, clampG g c A u ∂foldedCircle w r := by
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr, TwoPoint.foldedCircle_ae_norm_le w hr.le]
    with u hu hun
  rw [clampG_eq h hu (hun.trans hwR), mul_div_cancel₀ _ hc.ne']

/-! ## Continuity and smoothing symmetry of the circle averages -/

section Main

variable {g : ℂ → ℝ} (hg : ContinuousOn g H)
  (hb : ∀ R : ℝ, 0 < R → ∃ A B : ℝ, ∀ v : ℂ, 0 < v.im → ‖v‖ ≤ R →
      |g v| ≤ A + B * |Real.log v.im|)

include hg hb in
theorem continuousOn_fcAvg :
    ContinuousOn (fun q : ℂ × ℝ => ∫ v, g v ∂foldedCircle q.1 q.2) {p | 0 < p.2} := by
  intro p₀ hp₀
  have hr₀ : 0 < p₀.2 := hp₀
  set R := ‖p₀.1‖ + p₀.2 + 1 with hR
  obtain ⟨c, A, hc, hA, h⟩ := exists_clamp_consts hb (R := R) (by positivity)
  have hcont := (logBounded_clampG hg c hA).continuousOn p₀ hp₀
  have hopen : IsOpen {p : ℂ × ℝ | ‖p.1‖ + p.2 < R} := isOpen_lt ((continuous_norm.comp continuous_fst).add continuous_snd) continuous_const
  have hmem : {p : ℂ × ℝ | ‖p.1‖ + p.2 < R} ∈ 𝓝 p₀ :=
    hopen.mem_nhds (show ‖p₀.1‖ + p₀.2 < R by linarith)
  refine (hcont.const_mul c).congr_of_eventuallyEq ?_
    (integral_eq_mul_clampG hc h p₀.1 hr₀ (by linarith))
  filter_upwards [mem_nhdsWithin_of_mem_nhds hmem, self_mem_nhdsWithin] with p hp hp2
  exact integral_eq_mul_clampG hc h p.1 hp2 (le_of_lt hp)

include hg hb in
theorem integral_fcAvg_swap (w : ℂ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) :
    ∫ u, (∫ v, g v ∂foldedCircle u ρ) ∂foldedCircle w r =
      ∫ u, (∫ v, g v ∂foldedCircle u r) ∂foldedCircle w ρ := by
  set R := ‖w‖ + r + ρ with hR
  obtain ⟨c, A, hc, hA, h⟩ := exists_clamp_consts hb (R := R) (by positivity)
  have e1 : ∫ u, (∫ v, g v ∂foldedCircle u ρ) ∂foldedCircle w r =
      c * ∫ u, (∫ v, clampG g c A v ∂foldedCircle u ρ) ∂foldedCircle w r := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [TwoPoint.foldedCircle_ae_norm_le w hr.le] with u hu
    exact integral_eq_mul_clampG hc h u hρ (by linarith)
  have e2 : ∫ u, (∫ v, g v ∂foldedCircle u r) ∂foldedCircle w ρ =
      c * ∫ u, (∫ v, clampG g c A v ∂foldedCircle u r) ∂foldedCircle w ρ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [TwoPoint.foldedCircle_ae_norm_le w hρ.le] with u hu
    exact integral_eq_mul_clampG hc h u hr (by linarith)
  rw [e1, e2, (logBounded_clampG hg c hA).integral_swap w hr hρ]

end Main

end LogImDom

open LogImDom in
/-- **Log-dominated functions are regular** with their own folded-circle averages. -/
theorem logImDomRegStmt_holds : LogImDomRegStmt := by
  intro g hg hb
  have hg' : ContinuousOn g H := hg
  have hFc : ContinuousOn (fun q : ℂ × ℝ => ∫ v, g v ∂foldedCircle q.1 q.2) (Hbar ×ˢ Ioi 0) :=
    (continuousOn_fcAvg hg' hb).mono fun q hq => hq.2
  refine ⟨hFc, fun k z hz => RegClosure.tendsto_of_eval_eq (y := ofFun g) hFc
    (fun d _ r _ => rfl) k hz, ?_⟩
  refine RegClosure.tluo_of_dist_le (tluo_fc_of_continuousOn hFc) ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
  rw [integral_fcAvg_swap hg' hb q.1 (show 0 < q.2 from hq.2) hρ]

end WedgeUnzip
end QuantumZipper
