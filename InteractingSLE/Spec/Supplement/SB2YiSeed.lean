/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YhSeed
import InteractingSLE.Spec.Supplement.SB2WfTip

/-!
# The post-head chart at the entrance point `R`

Packet PROVE-T14-SB2LIFT (round 33, D51 item 3). B's stage chart `c` (seed `S`, free line `(S, ∞)`) followed by the
Loewner map of B's head up to its first visit `τ` of a free real point `R > S`. No prime ends are used:

* `tendsto_e_of_tip` (in `SB2YhLine`'s setting): if the inverse boundary map takes the value `R` only at `0`, the
  forward boundary values on `(R, ∞)` tend to `0` at `R⁺` (every cluster value is a preimage of `R`);
* `e_lt_e`: the forward boundary values are strictly increasing on `(R, ∞)` (continuous, injective, unbounded);
* **`post_seed_facts`**: the post-head chart's boundary values on `(R, ∞)` tend to `0` at `R⁺`, and its inverse
  boundary map sends `0 ↦ R` and `(0, ∞)` into `(R, ∞)`. The tip of the head is fresh (no earlier real point of the head
  is right of it in stage coordinates, by `e_lt_e`), so `Wf.eq_zero_of_extendFrom_eq_tip` gives the single preimage.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Sx

section Line

variable {D : Set ℂ} {Ψ : Chart} {e : ℝ → ℝ} {g : ℂ → ℂ} {C R : ℝ}
variable (hΨD : IsDomainChart (H \ D) Ψ) (he : ∀ x : ℝ, R < x → Tendsto Ψ.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ)))
  (hfree : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) D)
  (hg : ∀ p ∈ Hbar, Tendsto Ψ.2.1 (𝓝[H] p) (𝓝 (g p)))

include hΨD he hfree hg in
/-- **The right entry value is `0` when `R` has the single preimage `0`.** -/
theorem tendsto_e_of_tip (hgc : ContinuousOn g Hbar) (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C)
    (htip : ∀ p ∈ Hbar, g p = R → p = 0) : Tendsto e (𝓝[>] R) (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  have hns' : Tendsto ns atTop (𝓝 R) := hns.mono_right nhdsWithin_le_nhds
  have hmem : ∀ᶠ n in atTop, R < ns n := (tendsto_nhdsWithin_iff.1 hns).2
  have hev : ∀ᶠ n in atTop, ns n ∈ Ioo R (R + 1) ∧ R < ns n :=
    (hns'.eventually (Iio_mem_nhds (show R < R + 1 by linarith))).and hmem |>.mono fun n h =>
      ⟨⟨h.2, h.1⟩, h.2⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set y : ℕ → ℝ := fun n => ns (n + N) with hy
  have hy' : ∀ n, y n ∈ Ioo R (R + 1) := fun n => (hN _ (by omega)).1
  have hbd : ∀ n, e (y n) ∈ closedBall (0 : ℝ) (|R| + |R + 1| + C) := by
    intro n
    have h1 := abs_e_sub_leR hΨD he hfree hg hgb (show R < y n from (hy' n).1)
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    have := hy' n
    have ha := neg_abs_le R
    have hb := le_abs_self (R + 1)
    have ha' := abs_nonneg (R + 1)
    have hb' := abs_nonneg R
    constructor <;> [linarith [(abs_le.1 h1).1, this.1]; linarith [(abs_le.1 h1).2, this.2]]
  obtain ⟨z, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hbd
  refine ⟨fun n => φ n + N, ?_⟩
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝 R) :=
    hns'.comp (tendsto_atTop_mono (fun n => Nat.le_add_right (φ n) N) hφ.tendsto_atTop)
  have hzH : (z : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (z : ℂ).im by simp
  have hlimC : Tendsto (fun n => ((e (y (φ n)) : ℝ) : ℂ)) atTop (𝓝[Hbar] (z : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto z).comp hlim,
      Eventually.of_forall fun n => show (0 : ℝ) ≤ ((e (y (φ n)) : ℝ) : ℂ).im by simp⟩
  have h1 := ((hgc _ hzH).tendsto).comp hlimC
  have h2 : Tendsto (fun n => g (e (y (φ n)))) atTop (𝓝 ((R : ℝ) : ℂ)) := by
    refine ((Complex.continuous_ofReal.tendsto R).comp hyφ).congr fun n => ?_
    exact (g_eR hΨD he hfree hg (show R < y (φ n) from (hy' (φ n)).1)).symm
  have hgz : g z = R := tendsto_nhds_unique h1 h2
  have hz0 : (z : ℂ) = 0 := htip _ hzH hgz
  have hz0' : z = 0 := by exact_mod_cast hz0
  rw [← hz0']
  exact hlim

include hΨD he hfree hg in
/-- **The forward boundary values are strictly increasing on `(R, ∞)`.** -/
theorem e_lt_e (hgc : ContinuousOn g Hbar) (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C) {x y : ℝ} (hx : R < x)
    (hxy : x < y) : e x < e y := by
  have hinj : InjOn e (Ioi R) := fun a ha a' ha' h => by
    have h1 := g_eR hΨD he hfree hg ha
    have h2 := g_eR hΨD he hfree hg ha'
    rw [h] at h1
    exact_mod_cast h1.symm.trans h2
  set b := max y (e x + C + 1) + 1 with hb
  have hyb : y ≤ b := by rw [hb]; linarith [le_max_left y (e x + C + 1)]
  have hRb : R < b := by linarith
  have heb : e x ≤ e b := by
    have := abs_e_sub_leR hΨD he hfree hg hgb hRb
    linarith [(abs_le.1 this).1, le_max_right y (e x + C + 1)]
  have hsub : Icc x b ⊆ Ioi R := fun t ht => show R < t by linarith [ht.1]
  have hmono := ContinuousOn.strictMonoOn_of_injOn_Icc (by linarith) heb
    ((continuousOn_eR hΨD he hfree hg hgc hgb).mono hsub) (hinj.mono hsub)
  exact hmono ⟨le_rfl, by linarith⟩ ⟨hxy.le, hyb⟩ hxy

end Line

/-- **The post-head chart at the entrance point `R`.** `c` is B's stage chart (domain `ℍ ∖ Y`, free line `(S, ∞)`,
right entry `0` at `S`), `α` the stage trace of B's piece, `τ > 0` its first visit of the stage point over `R > S`, and
`cc` a domain chart of `ℍ ∖ Y''` whose inverse is `c⁻¹ ∘ F_τ` (`F_τ` the inverse Loewner map of the head). -/
theorem post_seed_facts {c : Chart} {Y : Set ℂ} (hcD : IsDomainChart (H \ Y) c) {S : ℝ} {es : ℝ → ℝ}
    (hes : ∀ x : ℝ, S < x → Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (es x : ℂ)))
    (hfreeY : ∀ x : ℝ, S < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) Y)
    {gc : ℂ → ℂ} (hgc : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (gc q))) (hes0 : Tendsto es (𝓝[>] S) (𝓝 0))
    (hgcc : ContinuousOn gc Hbar) {Cc : ℝ} (hCc : ∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc)
    {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w ζ α) (hw0 : w 0 = 0)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) ≤ ζ}) {τ : ℝ≥0} (hτ0 : 0 < τ) (hτζ : (τ : ℝ≥0∞) < ζ)
    {R : ℝ} (hSR : S < R) (hRtip : gc (α τ) = R)
    (hhead : ∀ r : ℝ≥0, r < τ → ∀ P : ℝ, gc (α r) = P → P < R)
    {cc : Chart} {Y'' : Set ℂ} (hccD : IsDomainChart (H \ Y'') cc)
    (hcomp : ∀ v ∈ H, cc.2.1 v = c.2.1 (fwdMapInv (frozenDrive w τ) τ v))
    {ecc : ℝ → ℝ} (hecc : ∀ x : ℝ, R < x → Tendsto cc.1 (𝓝[H] (x : ℂ)) (𝓝 (ecc x : ℂ)))
    (hfreeY'' : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) Y'')
    {gcc : ℂ → ℂ} (hgcc' : ∀ q ∈ Hbar, Tendsto cc.2.1 (𝓝[H] q) (𝓝 (gcc q))) {Ccc : ℝ}
    (hCcc : ∀ q ∈ Hbar, ‖gcc q - q‖ ≤ Ccc) :
    Tendsto ecc (𝓝[>] R) (𝓝 0) ∧ gcc 0 = R ∧ (∀ y : ℝ, 0 < y → ∃ x : ℝ, R < x ∧ gcc (y : ℂ) = x) ∧
      Tendsto (fun y : ℝ => (gcc (y : ℂ)).re) (𝓝[>] 0) (𝓝[>] R) := by
  set U := frozenDrive w τ with hUdef
  have hU : Continuous U := continuous_frozenDrive (hwc.mono fun s (hs : s ≤ (τ : ℝ).toNNReal) =>
    show (s : ℝ≥0∞) ≤ ζ by rw [Real.toNNReal_coe] at hs; exact (ENNReal.coe_le_coe.2 hs).trans hτζ.le)
  have hU0 : U 0 = 0 := by simp [hUdef, frozenDrive, hw0]
  have hγ : IsLoewnerTraceLT U τ (fun s : ℝ => α s.toNNReal) :=
    hα.isLoewnerTraceLT (by rw [ENNReal.ofReal_coe_nnreal]; exact hτζ)
  have hγc : ContinuousOn (fun s : ℝ => α s.toNNReal) (Icc 0 τ) :=
    hα.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
      show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ζ from
        (ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hs.2)).trans hτζ.le
  have hτ0' : (0 : ℝ) < τ := hτ0
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hγ hU hU0 hτ0' hγc
  have hFH : ∀ v ∈ H, fwdMapInv U τ v ∈ H := fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hU hU0 τ.coe_nonneg hv
  have hFbar : ∀ p ∈ Hbar, extendFrom H (fwdMapInv U τ) p ∈ Hbar := fun p hp => by
    have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
    have h := mem_closure_of_tendsto (hB.tendsto hp) (eventually_nhdsWithin_of_forall hFH)
    rwa [closure_H] at h
  have hcompB : ∀ p ∈ Hbar, gcc p = gc (extendFrom H (fwdMapInv U τ) p) := fun p hp => by
    have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
    have h1 : Tendsto cc.2.1 (𝓝[H] p) (𝓝 (gc (extendFrom H (fwdMapInv U τ) p))) :=
      ((hgc _ (hFbar p hp)).comp (tendsto_nhdsWithin_iff.2 ⟨hB.tendsto hp,
        eventually_nhdsWithin_of_forall hFH⟩)).congr'
        (eventually_nhdsWithin_of_forall fun v hv => (hcomp v hv).symm)
    exact tendsto_nhds_unique (hgcc' p hp) h1
  -- the stage tip over `R`
  have hαH : α τ ∈ Hbar := Sec7.IsGeneratingTrace.mem_Hbar hα
    (hwc.mono fun s (hs : (s : ℝ≥0∞) < ζ) => (show (s : ℝ≥0∞) ≤ ζ from hs.le)) hw0 hτζ.le
  have hαR : α τ = es R := eq_e_of_gR hcD hes hgc hSR hαH hRtip
  have hq0 : 0 < es R := e_posR hcD hes hfreeY hgc hes0 hgcc hCc hSR
  -- the tip is fresh
  have hfresh : ∀ s : ℝ, 0 ≤ s → s < τ → ((es R : ℝ) : ℂ) ∉ closure (fwdHull U s) := by
    intro s hs0 hsτ
    rw [hγ.2.2 s hs0 hsτ]
    have hKc : IsCompact ((fun s : ℝ => α s.toNNReal) '' Icc 0 s) :=
      isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc_right hsτ.le))
    obtain ⟨ρ, hρ, hd⟩ := Lx.exists_ball_disjoint_fillH_right hKc (x := es R) (fun y hy => by
      obtain ⟨r, hr, hry⟩ := hy
      by_cases hy0 : y ≤ 0
      · linarith
      push Not at hy0
      obtain ⟨P, hSP, hgP⟩ := g_pos_of_posR hcD hes hfreeY hgc hes0 hgcc hCc hy0
      have hrτ : r.toNNReal < τ := (Real.toNNReal_lt_iff_lt_coe hr.1).2 (lt_of_le_of_lt hr.2 hsτ)
      have hry' : α r.toNNReal = (y : ℂ) := hry
      have hPR : P < R := hhead r.toNNReal hrτ P (by rw [hry']; exact hgP)
      have hyP : ((y : ℝ) : ℂ) = es P := eq_e_of_gR hcD hes hgc hSP (show (0 : ℝ) ≤ ((y : ℝ) : ℂ).im by simp) hgP
      have hyP' : y = es P := by exact_mod_cast hyP
      rw [hyP']
      exact e_lt_e hcD hes hfreeY hgc hgcc hCc hSP hPR)
    intro hcl
    obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.1 hcl ρ hρ
    exact disjoint_left.1 hd (by rw [mem_ball, dist_comm]; exact hzd) hz
  -- the single preimage of `R`
  have htip : ∀ p ∈ Hbar, gcc p = R → p = 0 := by
    intro p hp hgp
    rw [hcompB p hp] at hgp
    have hFp : extendFrom H (fwdMapInv U τ) p = es R := eq_e_of_gR hcD hes hgc hSR (hFbar p hp) hgp
    by_cases hpH : p ∈ H
    · exfalso
      have hFe : extendFrom H (fwdMapInv U τ) p = fwdMapInv U τ p :=
        extendFrom_H_eq (continuousOn_fwdMapInv hU hU0 τ.coe_nonneg) hpH
      have h := hFH p hpH
      rw [← hFe, hFp] at h
      have him : (0 : ℝ) < ((es R : ℝ) : ℂ).im := h
      simp at him
    · have hre : p.im = 0 := le_antisymm (not_lt.1 hpH) hp
      have hp' : p = ((p.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hre])
      have hx : extendFrom H (fwdMapInv U τ) ((p.re : ℝ) : ℂ) = (fun s : ℝ => α s.toNNReal) τ := by
        rw [← hp', hFp]
        simp only [Real.toNNReal_coe]
        exact hαR.symm
      have h0 := Wf.eq_zero_of_extendFrom_eq_tip hU hU0 hτ0' hγ hγc (q := es R)
        (by simp only [Real.toNNReal_coe]; exact hαR) hq0.ne' hfresh hx
      rw [hp', h0]
      simp
  have hgccC : ContinuousOn gcc Hbar := GW1P.continuousOn_of_tendsto hgcc'
  have he0'' := tendsto_e_of_tip hccD hecc hfreeY'' hgcc' hgccC hCcc htip
  exact ⟨he0'', g_zeroR hccD hecc hfreeY'' hgcc' he0'' hgccC,
    fun y hy => g_pos_of_posR hccD hecc hfreeY'' hgcc' he0'' hgccC hCcc hy,
    tendsto_g_re_right hccD hecc hfreeY'' hgcc' he0'' hgccC hCcc⟩

end InteractingSLE.Theorem14.SB.Sx
