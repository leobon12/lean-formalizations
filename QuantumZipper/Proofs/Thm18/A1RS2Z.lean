import QuantumZipper.Proofs.Thm18.A1RS2Pair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (5): (R2) for the unscaled wedge field `Z = X + α₀(−log|·|) + G` (deterministic)

Hypotheses as in `A1RF.loopUC_of_Z` (A1RFLoopY.lean): `X` regular, `G` continuous, the circle
values of `Z` those of `X + logSingField κ + G`, `V` continuous with `V 0 = 0`, and the `Γ⁰` flow
pairings of `X` along `V` converging uniformly on every box `flowBox m`.

* `exists_loop_limit_Z`: on the box slice `S_m = {q | (0, q) ∈ flowBox m}` the dyadic pairings of
  `Z` along `ν_q = (f_t⁻¹)_* fc(c, r)` converge uniformly to a continuous limit, equal to
  `evalReg Z ν_q` (`A1RF.tendstoUniformlyOn_Zpair`, `continuousOn_pair_loop`);
* `continuousOn_evalReg_loop_Z`: `q ↦ evalReg Z ν_q` is continuous on `(0,∞) × ℍ̄ × (0,∞)`;
* **`continuousOn_evalReg_smearFam_Z`**: for a good driver `V`,
  `(p, ρ) ↦ evalReg Z (smearFam V left p ρ)` is continuous on `smearU × (0, ∞)`.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm F1 B3d.ZipLen

variable {κ : ℝ} {X Z : FieldSample} {FX : ℂ × ℝ → ℝ} {G : ℂ → ℝ} {V : ℝ → ℝ}

/-- The regular witness of `Z` by its circle values. -/
theorem isRegularWith_Z (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r)) :
    IsRegularWith Z (fun q => evalReg Z (foldedCircle q.1 q.2)) := by
  have hFl := LogSingGood.regular_add_Lf hFX (Real.sqrt κ - 2 / Real.sqrt κ)
  have hZF := GoodSample.gs_add_ofFun hFl hGc.continuousOn
  have hZfc' : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → Z (foldedCircle d r) =
      (X + ofFun (LogSingGood.Lf (Real.sqrt κ - 2 / Real.sqrt κ)) + ofFun G)
        (foldedCircle d r) := fun d hd r hr => hZfc d hd r hr
  obtain ⟨FZ, hZ⟩ : IsRegularSample Z := ⟨_, WedgeUnzip.isRegularWith_of_fc hZfc' hZF⟩
  exact hZ.congr_evalReg

/-- The box slice at `u = 0`. -/
def sliceBox (m : ℕ) : Set (ℝ × ℂ × ℝ) := {q | ((0 : ℝ), q.1, q.2.1, q.2.2) ∈ flowBox m}

theorem sliceBox_subset (m : ℕ) :
    sliceBox m ⊆ loopBox ((m : ℝ) + 1) (3 * (m : ℝ) + 4) (1 / ((m : ℝ) + 2)) := by
  intro q hq
  have hq' : ((0 : ℝ), q.1, q.2.1, q.2.2) ∈ flowBox m := hq
  simp only [flowBox, mem_Icc] at hq'
  obtain ⟨-, ⟨hs0, hsT⟩, ⟨hre1, hre2⟩, ⟨him0, him1⟩, ⟨hr1, hr2⟩⟩ := hq'
  show q.1 ∈ Icc 0 ((m : ℝ) + 1) ∧ q.2.1 ∈ Hbar ∧ 1 / ((m : ℝ) + 2) ≤ q.2.2 ∧
    ‖q.2.1‖ + q.2.2 ≤ 3 * (m : ℝ) + 4
  refine ⟨⟨hs0, hsT⟩, him0, hr1, ?_⟩
  have hn := Complex.norm_le_abs_re_add_abs_im q.2.1
  have h1 : |q.2.1.re| ≤ (m : ℝ) + 1 := abs_le.2 ⟨hre1, hre2⟩
  have h2 : |q.2.1.im| ≤ (m : ℝ) + 1 := abs_le.2 ⟨by linarith, him1⟩
  linarith

/-- **Uniform dyadic limit on a box slice, continuous, equal to `evalReg`.** -/
theorem exists_loop_limit_Z (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m)) (m : ℕ) :
    ∃ L' : ℝ × ℂ × ℝ → ℝ, ContinuousOn L' (sliceBox m) ∧
      TendstoUniformlyOn (fun (k : ℕ) (q : ℝ × ℂ × ℝ) => ∫ v, avgReg Z k v
        ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1))) L' atTop (sliceBox m) ∧
      ∀ q ∈ sliceBox m, evalReg Z ((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1)) = L' q := by
  have hZc := isRegularWith_Z hFX hGc hZfc
  obtain ⟨L, hL⟩ := hS1 m
  obtain ⟨L', hL'⟩ := A1RF.tendstoUniformlyOn_Zpair hκ hFX hGc hZfc hV hV0 hfy hL
  have hsub := sliceBox_subset m
  have hr₀ : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  have hgc : ∀ σ : ℝ, 0 < σ → ContinuousOn (fun v : ℂ => evalReg Z (foldedCircle v σ)) Hbar := by
    intro σ hσ
    have hpm : ContinuousOn (fun v : ℂ => ((v, σ) : ℂ × ℝ)) Hbar :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hg : ContinuousOn ((fun q : ℂ × ℝ => evalReg Z (foldedCircle q.1 q.2)) ∘
        fun v : ℂ => ((v, σ) : ℂ × ℝ)) Hbar := hZc.1.comp hpm fun v hv => ⟨hv, hσ⟩
    exact hg
  have hcσ : ∀ σ : ℝ, 0 < σ → ContinuousOn (fun q : ℝ × ℂ × ℝ =>
      ∫ v, evalReg Z (foldedCircle v σ) ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1)))
      (sliceBox m) := by
    intro σ hσ
    have h := continuousOn_pair_loop (g := fun v => evalReg Z (foldedCircle v σ)) hV hV0
      (hgc σ hσ) (measurable_evalReg_fc Z σ) ((m : ℝ) + 1) (3 * (m : ℝ) + 4)
      (1 / ((m : ℝ) + 2)) hr₀
    exact h.mono hsub
  have hL'c : ContinuousOn L' (sliceBox m) :=
    hL'.continuousOn (Eventually.frequently (eventually_mem_nhdsWithin.mono fun σ hσ =>
      hcσ σ hσ))
  -- dyadic pairings are the circle pairings at radius `2^{-k}`
  have hdy : ∀ k : ℕ, ∀ q ∈ sliceBox m, ∫ v, avgReg Z k v
      ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1)) =
      ∫ v, evalReg Z (foldedCircle v (radius k))
        ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1)) := by
    intro k q hq
    have hmf : Measurable (fwdMapInv V q.1) :=
      RTBeur.measurable_fwdMapInv_rt hV hV0 (hsub hq).1.1
    have hae : ∀ᵐ v ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1)), v ∈ Hbar :=
      (ae_map_iff hmf.aemeasurable isClosed_Hbar.measurableSet).2
        (ae_of_all _ fun w => F1.fwdMapInv_mem_Hbar V _ _)
    refine integral_congr_ae ?_
    filter_upwards [hae] with v hv
    exact A1RF.avgReg_eq_of_regular hZc k hv
  have hσk : Tendsto radius atTop (𝓝[>] 0) := RegClosure.tendsto_radius_nhdsGT
  have hUk : TendstoUniformlyOn (fun (k : ℕ) (q : ℝ × ℂ × ℝ) => ∫ v, avgReg Z k v
      ∂((foldedCircle q.2.1 q.2.2).map (fwdMapInv V q.1))) L' atTop (sliceBox m) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hσk.eventually ((Metric.tendstoUniformlyOn_iff.1 hL') ε hε)] with k hk q hq
    rw [hdy k q hq]
    exact hk q hq
  refine ⟨L', hL'c, hUk, fun q hq => ?_⟩
  exact (hUk.tendsto_at hq).limUnder_eq

/-- **Continuity of the per-loop regularized pairings of `Z`.** -/
theorem continuousOn_evalReg_loop_Z (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m)) :
    ContinuousOn (fun q : ℝ × ℂ × ℝ => evalReg Z ((foldedCircle q.2.1 q.2.2).map
      (fwdMapInv V q.1))) (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)) := by
  intro q₀ hq₀
  obtain ⟨ht₀, hc₀, hr₀⟩ := hq₀
  have ht₀' : 0 < q₀.1 := ht₀
  have hr₀' : 0 < q₀.2.2 := hr₀
  have hc₀' : 0 ≤ q₀.2.1.im := hc₀
  obtain ⟨m, hm⟩ := exists_nat_gt (q₀.1 + |q₀.2.1.re| + q₀.2.1.im + q₀.2.2 + 1 / q₀.2.2)
  obtain ⟨L', hL'c, -, hEq⟩ := exists_loop_limit_Z hκ hFX hGc hZfc hV hV0 hfy hS1 m
  set O : Set (ℝ × ℂ × ℝ) := {q | q.1 < (m : ℝ) + 1 ∧ |q.2.1.re| < (m : ℝ) + 1 ∧
    q.2.1.im < (m : ℝ) + 1 ∧ 1 / ((m : ℝ) + 2) < q.2.2 ∧ q.2.2 < (m : ℝ) + 2} with hOdef
  have hO : IsOpen O := by
    have c1 : Continuous fun q : ℝ × ℂ × ℝ => q.2.1 := continuous_snd.fst
    have c2 : Continuous fun q : ℝ × ℂ × ℝ => q.2.2 := continuous_snd.snd
    exact (isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt (continuous_abs.comp (Complex.continuous_re.comp c1)) continuous_const).inter
      ((isOpen_lt (Complex.continuous_im.comp c1) continuous_const).inter
      ((isOpen_lt continuous_const c2).inter (isOpen_lt c2 continuous_const))))
  have hre := abs_nonneg q₀.2.1.re
  have hinv := one_div_pos.2 hr₀'
  have hq₀O : q₀ ∈ O := by
    refine ⟨by linarith, by linarith, by linarith, ?_, by linarith⟩
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 / q₀.2.2 < m := by linarith
    rw [div_lt_iff₀ hr₀'] at h1
    nlinarith
  have hsub : O ∩ (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)) ⊆ sliceBox m := by
    rintro q ⟨⟨h1, h2, h3, h4, h5⟩, ht, hc, hr⟩
    have ht' : 0 < q.1 := ht
    have hc' : 0 ≤ q.2.1.im := hc
    have ha := abs_lt.1 h2
    show ((0 : ℝ), q.1, q.2.1, q.2.2) ∈ flowBox m
    exact ⟨⟨le_rfl, by positivity⟩, ⟨ht'.le, h1.le⟩, ⟨by linarith [ha.1], by linarith [ha.2]⟩,
      ⟨hc', h3.le⟩, ⟨h4.le, h5.le⟩⟩
  have hmem : sliceBox m ∈ 𝓝[Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)] q₀ :=
    mem_nhdsWithin.2 ⟨O, hO, hq₀O, hsub⟩
  have hq₀S : q₀ ∈ sliceBox m := hsub ⟨hq₀O, ht₀, hc₀, hr₀⟩
  have h1 : ContinuousWithinAt L' (Ioi 0 ×ˢ (Hbar ×ˢ Ioi 0)) q₀ :=
    (hL'c q₀ hq₀S).mono_of_mem_nhdsWithin hmem
  exact h1.congr_of_eventuallyEq (eventually_of_mem hmem fun q hq => hEq q hq) (hEq q₀ hq₀S)

/-- **Per-loop uniform convergence for `Z`** on bounded sets of centres. -/
theorem loopUC_Z (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m)) {t : ℝ} (ht : 0 < t) {ρ : ℝ} (hρ : 0 < ρ) (R : ℝ) :
    TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg Z k u
        ∂((foldedCircle z ρ).map (fwdMapInv V t)))
      (fun z => evalReg Z ((foldedCircle z ρ).map (fwdMapInv V t))) atTop
      (Hbar ∩ closedBall 0 R) := by
  obtain ⟨m, hm⟩ := exists_nat_gt (t + |R| + ρ + 1 / ρ)
  have hinv := one_div_pos.2 hρ
  have hR0 := abs_nonneg R
  have hmemS : ∀ z ∈ Hbar ∩ closedBall (0 : ℂ) R, ((t, z, ρ) : ℝ × ℂ × ℝ) ∈ sliceBox m := by
    intro z hz
    have hzR : ‖z‖ ≤ |R| := by
      have := hz.2; rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    have hre : |z.re| ≤ |R| := (Complex.abs_re_le_norm z).trans hzR
    have him : z.im ≤ |R| := (Complex.im_le_norm z).trans hzR
    have ha := abs_le.1 hre
    have hρm : 1 / ((m : ℝ) + 2) ≤ ρ := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 1 / ρ < m := by linarith
      rw [div_lt_iff₀ hρ] at h1
      nlinarith
    show ((0 : ℝ), t, z, ρ) ∈ flowBox m
    exact ⟨⟨le_rfl, by positivity⟩, ⟨ht.le, by linarith⟩, ⟨by linarith [ha.1], by linarith [ha.2]⟩,
      ⟨hz.1, by linarith⟩, ⟨hρm, by linarith⟩⟩
  obtain ⟨L', -, hU, hEq⟩ := exists_loop_limit_Z hκ hFX hGc hZfc hV hV0 hfy hS1 m
  rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
  intro ε hε
  filter_upwards [hU ε hε] with k hk z hz
  have e := hEq (t, z, ρ) (hmemS z hz)
  dsimp only at e
  rw [e]
  exact hk _ (hmemS z hz)

/-- **(R2) for `Z`: joint continuity of the smeared-loop pairings at positive radius.** -/
theorem continuousOn_evalReg_smearFam_Z (hκ : 0 < κ) (hFX : IsRegularWith X FX) (hGc : Continuous G)
    (hZfc : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z (foldedCircle d r) = (X + F2.logSingField κ + ofFun G) (foldedCircle d r))
    (hV : Continuous V) (hV0 : V 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    (hS1 : ∀ m : ℕ, ∃ L : ℝ × ℝ × ℂ × ℝ → ℝ,
      TendstoUniformlyOn (fun ρ p => flowPhiYc κ X V ρ p) L (𝓝[>] 0) (flowBox m)) (hG : G1zDrvGood V) (left : Bool) :
    ContinuousOn (fun z : (Fin 4 → ℝ) × ℝ => evalReg Z (smearFam V left z.1 z.2))
      (smearU ×ˢ Ioi 0) :=
  continuousOn_evalReg_smearFam (isRegularWith_Z hFX hGc hZfc) hG left
    (continuousOn_evalReg_loop_Z hκ hFX hGc hZfc hV hV0 hfy hS1)
    fun _ ht _ hρ R => loopUC_Z hκ hFX hGc hZfc hV hV0 hfy hS1 ht hρ R

end A1RS
end R18
end QuantumZipper
