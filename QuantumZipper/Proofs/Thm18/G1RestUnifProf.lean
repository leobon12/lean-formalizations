import QuantumZipper.Proofs.Thm18.G1RestUnifDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST-UNIF-PROF: uniform convergence of the profile part on the compact boxes

`unifProfStmt_holds : UnifProfStmt`. For `ψ` as in `PsiGood`, `S > 0` and a radial profile `g`
continuous on `(0, ∞)` with `|g t| ≤ C (1 - log t)` on `(0, 1]`, the smoothed profile integrated
along `ψ_* fc(q)` converges to the unsmoothed one uniformly in `q ∈ GoodMeas.kbox m`.

Proof (tail/clamp argument, following `TwoPoint.continuousOn_integral_foldedCircle`):

* both integrands are bounded by `A + B |log Im z|` on `ℍ ∩ B̄(0, 2R + 1)`, uniformly in the
  smoothing index (`abs_smoothFun_rp_le` with the Koebe bound `logBd_log_norm`);
* replacing the integrand by its composition with `clampIm τ` costs `O(√τ (1 + |log τ|))`
  uniformly over folded circles of radius `≥ r₀` (`TwoPoint.integral_abs_sub_clamp_le`);
* on the compact set `S ψ(clampIm τ (B̄(0, R))) ⊆ ℍ` the circle smoothing converges uniformly
  (uniform continuity of `g` on a compact interval away from `0`).

The tail estimate is the repository's `TwoPoint.integral_abs_sub_clamp_le`; the pointwise
statement is `tendsto_profile_psi`. The uniform assembly is an own elementary argument
(AGENT_GUIDE cost rule); no literature source is needed.
-/

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open F1.RC3Two CA.Koebe

/-- Tail estimate for one integrand with a bound `A + B |log Im|`. -/
theorem unifProf_tail {G : ℂ → ℝ} (hGm : Measurable G) {A B R : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hGb : ∀ u ∈ H, ‖u‖ ≤ 2 * R + 1 → |G u| ≤ A + B * |Real.log u.im|) (w : ℂ) {r r₀ τ : ℝ}
    (hr₀ : 0 < r₀) (hr : r₀ ≤ r) (hwR : ‖w‖ + r ≤ R) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    Integrable G (foldedCircle w r) ∧
      Integrable (fun u => G (TwoPoint.clampIm τ u)) (foldedCircle w r) ∧
      |(∫ u, G u ∂foldedCircle w r) - ∫ u, G (TwoPoint.clampIm τ u) ∂foldedCircle w r| ≤
        (B + 1) * 18 * Real.sqrt (1 / r₀) * Real.sqrt τ *
          (2 * (A / (B + 1)) + 4 + 2 * |Real.log τ|) := by
  have hr0 : 0 < r := hr₀.trans_le hr
  have hR : 0 ≤ R := by linarith [norm_nonneg w]
  have hB1 : 0 < B + 1 := by linarith
  have hint1 : Integrable G (foldedCircle w r) := by
    refine ((integrable_const A).add
      ((TwoPoint.integrable_log_im_foldedCircle w hr0).abs.const_mul B)).mono'
        hGm.aestronglyMeasurable ?_
    filter_upwards [TwoPoint.foldedCircle_ae_norm_le w hr0.le,
      TwoPoint.foldedCircle_ae_mem_H w hr0] with u hu huH
    rw [Real.norm_eq_abs]
    exact hGb u huH (by linarith)
  have hcl : ∀ u, TwoPoint.clampIm τ u ∈ H := fun u =>
    show 0 < (TwoPoint.clampIm τ u).im by rw [TwoPoint.clampIm_im]; exact lt_max_of_lt_right hτ
  have hint2 : Integrable (fun u => G (TwoPoint.clampIm τ u)) (foldedCircle w r) := by
    refine (integrable_const (A + B * (|Real.log τ| + |Real.log (2 * R + 1)|))).mono'
      (hGm.comp (TwoPoint.continuous_clampIm τ).measurable).aestronglyMeasurable ?_
    filter_upwards [TwoPoint.foldedCircle_ae_norm_le w hr0.le] with u hu
    have hG2 := hGb _ (hcl u) ((TwoPoint.norm_clampIm_le hτ.le u).trans (by linarith))
    rw [TwoPoint.clampIm_im] at hG2
    have hmax : max u.im τ ≤ 2 * R + 1 :=
      max_le (by linarith [Complex.im_le_norm u]) (by linarith)
    have hl := TwoPoint.abs_log_le_of_mem hτ (le_max_right u.im τ) hmax
    rw [Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hl hB
    exact hG2.trans (by linarith)
  have hG'b : ∀ u ∈ H, ‖u‖ ≤ 2 * R + 1 → |G u / (B + 1)| ≤ A / (B + 1) + |Real.log u.im| := by
    intro u hu huR
    rw [abs_div, abs_of_pos hB1, div_le_iff₀ hB1, add_mul, div_mul_cancel₀ _ hB1.ne']
    have := hGb u hu huR
    have := abs_nonneg (Real.log u.im)
    nlinarith
  have htail := TwoPoint.integral_abs_sub_clamp_le (G := fun u => G u / (B + 1))
    (hGm.div_const _) (by positivity) hG'b w hr0 hτ hτ1 hwR
  refine ⟨hint1, hint2, ?_⟩
  rw [← integral_sub hint1 hint2]
  refine abs_integral_le_integral_abs.trans ?_
  have e : ∀ u, |G u - G (TwoPoint.clampIm τ u)| =
      (B + 1) * |G u / (B + 1) - G (TwoPoint.clampIm τ u) / (B + 1)| := by
    intro u
    rw [← sub_div, abs_div, abs_of_pos hB1, mul_div_cancel₀ _ hB1.ne']
  simp_rw [e]
  rw [integral_const_mul]
  have hs : Real.sqrt (τ / r) ≤ Real.sqrt (1 / r₀) * Real.sqrt τ := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    calc τ / r ≤ τ / r₀ := div_le_div_of_nonneg_left hτ.le hr₀ hr
      _ = 1 / r₀ * τ := by ring
  have hf : 0 ≤ 2 * (A / (B + 1)) + 2 * |Real.log τ| + 4 := by positivity
  calc (B + 1) * ∫ u, |G u / (B + 1) - G (TwoPoint.clampIm τ u) / (B + 1)| ∂foldedCircle w r
      ≤ (B + 1) * (18 * Real.sqrt (τ / r) * (2 * (A / (B + 1)) + 2 * |Real.log τ| + 4)) :=
        mul_le_mul_of_nonneg_left htail hB1.le
    _ ≤ (B + 1) * (18 * (Real.sqrt (1 / r₀) * Real.sqrt τ) *
          (2 * (A / (B + 1)) + 2 * |Real.log τ| + 4)) := by gcongr
    _ = _ := by ring

/-- **Uniform convergence of folded-circle integrals** from a uniform `A + B |log Im|` bound
and uniform convergence of the `Im`-clamped integrands. -/
theorem tendstoUniformlyOn_integral_fc_of_clamp {F : ℕ → ℂ → ℝ} {G : ℂ → ℝ} {A B R r₀ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr₀ : 0 < r₀) (hFm : ∀ k, Measurable (F k))
    (hGm : Measurable G)
    (hFb : ∀ᶠ k in atTop, ∀ u ∈ H, ‖u‖ ≤ 2 * R + 1 → |F k u| ≤ A + B * |Real.log u.im|)
    (hGb : ∀ u ∈ H, ‖u‖ ≤ 2 * R + 1 → |G u| ≤ A + B * |Real.log u.im|)
    (hmid : ∀ τ, 0 < τ → TendstoUniformlyOn (fun k u => F k (TwoPoint.clampIm τ u))
      (fun u => G (TwoPoint.clampIm τ u)) atTop (closedBall 0 R)) :
    TendstoUniformlyOn (fun k (q : ℂ × ℝ) => ∫ u, F k u ∂foldedCircle q.1 q.2)
      (fun q => ∫ u, G u ∂foldedCircle q.1 q.2) atTop {q | ‖q.1‖ + q.2 ≤ R ∧ r₀ ≤ q.2} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨τ, hτ0, hτ1, hτε⟩ := TwoPoint.exists_tail_small
    (K := (B + 1) * 18 * Real.sqrt (1 / r₀)) (c := 2 * (A / (B + 1)) + 4)
    (by positivity) (by positivity : 0 < ε / 3)
  have hmid' := Metric.tendstoUniformlyOn_iff.1 (hmid τ hτ0) (ε / 3) (by positivity)
  filter_upwards [hFb, hmid'] with k hk hkm
  intro q hq
  obtain ⟨hqR, hqr⟩ := hq
  have hr0 : 0 < q.2 := hr₀.trans_le hqr
  obtain ⟨i1, i2, t1⟩ := unifProf_tail hGm hA hB hGb q.1 hr₀ hqr hqR hτ0 hτ1
  obtain ⟨j1, j2, t2⟩ := unifProf_tail (hFm k) hA hB hk q.1 hr₀ hqr hqR hτ0 hτ1
  have hmidI : |(∫ u, G (TwoPoint.clampIm τ u) ∂foldedCircle q.1 q.2) -
      ∫ u, F k (TwoPoint.clampIm τ u) ∂foldedCircle q.1 q.2| ≤ ε / 3 := by
    rw [← integral_sub i2 j2, ← Real.norm_eq_abs]
    have := norm_integral_le_of_norm_le_const (μ := foldedCircle q.1 q.2) (C := ε / 3)
      (f := fun u => G (TwoPoint.clampIm τ u) - F k (TwoPoint.clampIm τ u)) (by
        filter_upwards [TwoPoint.foldedCircle_ae_norm_le q.1 hr0.le] with u hu
        rw [← dist_eq_norm]
        exact (hkm u (mem_closedBall_zero_iff.2 (by linarith))).le)
    simpa using this
  rw [Real.dist_eq]
  have a1 := abs_le.1 t1
  have a2 := abs_le.1 t2
  have a3 := abs_le.1 hmidI
  rw [abs_lt]
  constructor <;> linarith

variable {g : ℝ → ℝ} {C : ℝ}

/-- Circle smoothing of `rp g` converges uniformly on compact subsets of `ℍ`. -/
theorem exists_unif_smoothFun_rp (hgm : Measurable g) (hgc : ContinuousOn g (Ioi 0))
    (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t)) {W : Set ℂ} (hW : IsCompact W)
    (hWH : W ⊆ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ c ∈ W, ∀ ρ, 0 < ρ → ρ < η →
      |GoodSample.smoothFun (rp g) c ρ - rp g c| ≤ ε := by
  obtain ⟨δ, hδ, hδW⟩ : ∃ δ > 0, ∀ c ∈ W, δ ≤ ‖c‖ := by
    have h0 : (0 : ℂ) ∈ Wᶜ := fun h => ne_zero_of_mem_H' (hWH h) rfl
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hW.isClosed.isOpen_compl 0 h0
    refine ⟨δ, hδ, fun c hc => ?_⟩
    by_contra hlt
    exact hball (mem_ball_zero_iff.2 (not_le.1 hlt)) hc
  obtain ⟨M, hM⟩ := hW.isBounded.exists_norm_le
  have huc : UniformContinuousOn g (Icc (δ / 2) (M + δ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hgc.mono fun t ht =>
      show (0 : ℝ) < t from lt_of_lt_of_le (by positivity) ht.1)
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
  refine ⟨min η (δ / 2), by positivity, fun c hc ρ hρ hρη => ?_⟩
  have hρ1 : ρ < η := hρη.trans_le (min_le_left _ _)
  have hρ2 : ρ < δ / 2 := hρη.trans_le (min_le_right _ _)
  have hcH : c ∈ Hbar := H_subset_Hbar (hWH hc)
  have hI := (abs_smoothFun_rp_sub_le hgm hgc hbd (s := 1 / 2) (by norm_num) (by norm_num) c
    hρ).1
  have e : GoodSample.smoothFun (rp g) c ρ - rp g c =
      ∫ u, (rp g u - rp g c) ∂foldedCircle c ρ := by
    rw [integral_sub hI (integrable_const _)]
    simp [GoodSample.smoothFun]
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ε) ?_).trans (by simp)
  filter_upwards [foldedCircle_ae_dist_le' hcH hρ.le] with u hu
  have hc1 := hδW c hc
  have hc2 := hM c hc
  have hn : |‖u‖ - ‖c‖| ≤ ρ := (abs_norm_sub_norm_le u c).trans (by rwa [← dist_eq_norm])
  have hn' := abs_le.1 hn
  have hmem1 : ‖u‖ ∈ Icc (δ / 2) (M + δ) := ⟨by linarith, by linarith⟩
  have hmem2 : ‖c‖ ∈ Icc (δ / 2) (M + δ) := ⟨by linarith, by linarith⟩
  have := hηg _ hmem1 _ hmem2 (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq] at this
  rw [Real.norm_eq_abs]
  exact this.le

variable {ψ : ℂ → ℂ}

/-- The `Im`-clamped integrands converge uniformly on bounded sets. -/
theorem unifProf_mid (hψ : PsiGood ψ) {S : ℝ} (hS : 0 < S) (hgm : Measurable g)
    (hgc : ContinuousOn g (Ioi 0)) (hbd : ∀ t, 0 < t → t ≤ 1 → |g t| ≤ C * (1 - Real.log t))
    (R τ : ℝ) (hτ : 0 < τ) :
    TendstoUniformlyOn (fun (k : ℕ) u => GoodSample.smoothFun (rp g)
        ((S : ℂ) * ψ (TwoPoint.clampIm τ u)) (S * radius k))
      (fun u => rp g ((S : ℂ) * ψ (TwoPoint.clampIm τ u))) atTop (closedBall 0 R) := by
  have hcl : ∀ u, TwoPoint.clampIm τ u ∈ H := fun u =>
    show 0 < (TwoPoint.clampIm τ u).im by rw [TwoPoint.clampIm_im]; exact lt_max_of_lt_right hτ
  have hK : IsCompact (TwoPoint.clampIm τ '' closedBall (0 : ℂ) R) :=
    (isCompact_closedBall _ _).image (TwoPoint.continuous_clampIm τ)
  have hKH : TwoPoint.clampIm τ '' closedBall (0 : ℂ) R ⊆ H := by
    rintro _ ⟨u, -, rfl⟩; exact hcl u
  have hW : IsCompact ((fun z => (S : ℂ) * ψ z) '' (TwoPoint.clampIm τ '' closedBall (0 : ℂ) R)) :=
    hK.image_of_continuousOn ((continuousOn_const.mul hψ.2.1.continuousOn).mono hKH)
  have hWH : (fun z => (S : ℂ) * ψ z) '' (TwoPoint.clampIm τ '' closedBall (0 : ℂ) R) ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩; exact mul_psi_mem_H hψ hS (hKH hz)
  have hρ : Tendsto (fun k : ℕ => S * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hS (radius_pos k)⟩
    simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul S
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨η, hη, hηW⟩ := exists_unif_smoothFun_rp hgm hgc hbd hW hWH (half_pos hε)
  filter_upwards [hρ (Ioo_mem_nhdsGT hη)] with k hk u hu
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt (hηW ((S : ℂ) * ψ (TwoPoint.clampIm τ u))
    (mem_image_of_mem _ (mem_image_of_mem _ hu)) _ hk.1 hk.2) (half_lt_self hε)

/-- **G1-REST-UNIF-PROF.** Uniform convergence of the profile part on the compact boxes. -/
theorem unifProfStmt_holds : UnifProfStmt := by
  intro ψ hψ S hS g C hgm hgc hbd m
  have hC := nonneg_of_bd hbd
  have hκ := koebeDistExp_pos
  obtain ⟨M, hM⟩ := norm_mul_psi_le hψ hS (2 * (2 * (m : ℝ) + 1) + 1)
  obtain ⟨B₀, hB₀⟩ := abs_smoothFun_rp_le hgm hgc hbd M
  obtain ⟨A₁, hA₁⟩ := (logBd_log_norm hψ hS).2.2.2 (2 * (2 * (m : ℝ) + 1) + 1)
  have hP := logBd_profile hψ hS hgm hgc hbd
  obtain ⟨A₂, hA₂⟩ := hP.2.2.2 (2 * (2 * (m : ℝ) + 1) + 1)
  have hρ : Tendsto (fun k : ℕ => S * radius k) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hS (radius_pos k)⟩
    simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul S
  refine (tendstoUniformlyOn_integral_fc_of_clamp
    (F := fun k z => GoodSample.smoothFun (rp g) ((S : ℂ) * ψ z) (S * radius k))
    (G := fun z => rp g ((S : ℂ) * ψ z))
    (A := |B₀ + 8 * C * A₁| + |A₂|) (B := 8 * C * (1 + koebeDistExp))
    (R := 2 * (m : ℝ) + 1) (r₀ := 1 / ((m : ℝ) + 1)) (by positivity) (by positivity)
    (by positivity) (fun k => ?_) hP.1 ?_ ?_
    fun τ hτ => unifProf_mid hψ hS hgm hgc hbd _ τ hτ).mono ?_
  · exact (continuous_smoothFun_rp hgm hgc hbd (mul_pos hS (radius_pos k))).measurable.comp
      (measurable_const.mul hψ.1)
  · filter_upwards [hρ (Ioo_mem_nhdsGT one_pos)] with k hk u hu huR
    have h1 := hB₀ _ (hM u hu huR) (ne_zero_of_mem_H' (mul_psi_mem_H hψ hS hu)) _ hk.1 hk.2.le
    have h2 : |Real.log ‖(S : ℂ) * ψ u‖| ≤ A₁ + (1 + koebeDistExp) * |Real.log u.im| :=
      hA₁ u hu huR
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * C)
    have := le_abs_self (B₀ + 8 * C * A₁)
    have := abs_nonneg A₂
    show |GoodSample.smoothFun (rp g) ((S : ℂ) * ψ u) (S * radius k)| ≤ _
    linarith
  · intro u hu huR
    have h1 : |rp g ((S : ℂ) * ψ u)| ≤ A₂ + C * (1 + koebeDistExp) * |Real.log u.im| :=
      hA₂ u hu huR
    have := le_abs_self A₂
    have := abs_nonneg (B₀ + 8 * C * A₁)
    have : 0 ≤ C * (1 + koebeDistExp) * |Real.log u.im| := by positivity
    show |rp g ((S : ℂ) * ψ u)| ≤ _
    linarith
  · rintro ⟨w, r⟩ ⟨⟨hw, -⟩, hr1, hr2⟩
    rw [mem_closedBall_zero_iff] at hw
    exact ⟨by simp only; linarith, hr1⟩

end G1RC
end Thm18Asm
end QuantumZipper
