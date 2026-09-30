import QuantumZipper.Proofs.Zipper.E4L3Basic

/-!
# E4-L3, deterministic inputs II: the normalizer terms as `s ↑ τ`

`handoff/E4.md`, item L3. With `ϖ_s = varpiT V s ϖ`, `γ = √κ` and `a s → 0` (the real flow of
the point `x` at its hitting time):

* `integral_shiftFun_eq`: `∫ shiftFun γ h₀ ϖ' a dν = ∫ h₀ dν + γ/2 (neuPot ν a − k(ν, ϖ'))`;
* `tendsto_kk`: `k(ϖ_s, ϖ_s) → k(ϖ_τ, ϖ_τ)` (dominated convergence on `ϖ ⊗ ϖ`, with the bound
  `|N(z,w)| + L` from the two-point bounds `TwoPoint.twoPoint_lower_sq`, `twoPoint_upper_sq`);
* `tendsto_kernelCov_left`: `k(ϖ_s, ν) → k(ϖ_τ, ν)` for a good measure `ν` (continuity of the
  Neumann potential of `ν`);
* `tendsto_energy`: the Neumann energy `kernelCov2 N (ϖ_s, ϖ_τ) (ϖ_s, ϖ_τ) → 0`;
* `tendsto_shift_fc`, `tendsto_shift_varpi`: the two shift integrals of `targetField`.

Own elementary arguments (dominated convergence).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace E4Grid

open E1 TwoPoint PalmNorm

variable {V : ℝ → ℝ}

/-- Splitting the shift integral. -/
theorem integral_shiftFun_eq {ν ϖ' : Measure ℂ} (hν : GoodMeas ν) (hϖ' : IsAdmissibleH ϖ')
    (γ κ a : ℝ) :
    ∫ u, shiftFun γ (h0rev κ) ϖ' a u ∂ν =
      ∫ u, h0rev κ u ∂ν + γ / 2 * (neuPot ν a - kernelCov neumannH ν ϖ') := by
  have := hν.prob
  have := hϖ'.1
  obtain ⟨α, C, hα, -, hC, hF⟩ := hν.frost
  obtain ⟨B, hB0, hB⟩ := hν.bdd
  have hlog : ∀ x : ℂ, Integrable (fun y => Real.log ‖x - y‖) ν :=
    frostman_integrable_log hF hα hC hB0 hB
  have h0 : Integrable (h0rev κ) ν := by
    refine ((hlog 0).const_mul (2 / Real.sqrt κ)).congr (Eventually.of_forall fun y => ?_)
    simp [h0rev]
  have hN : Integrable (fun u => neumannH (a : ℂ) u) ν := by
    refine ((hlog a).neg.sub (hlog (conj (a : ℂ)))).congr (Eventually.of_forall fun y => ?_)
    simp only [neumannH, Pi.sub_apply, Pi.neg_apply, norm_sub_conj_eq]
  have hk : Integrable (kPot ϖ') ν :=
    (integrable_neumannH_prod hν.adm hϖ').integral_prod_left
  have hsub : Integrable (fun u => γ / 2 * (neumannH (a : ℂ) u - kPot ϖ' u)) ν :=
    (hN.sub hk).const_mul _
  unfold shiftFun
  rw [integral_add h0 hsub, integral_const_mul, integral_sub hN hk]
  rfl

theorem kernelCov_map_left {ϖ : Measure ℂ} {f : ℂ → ℂ} (hf : Measurable f) (ν : Measure ℂ)
    [IsFiniteMeasure ν] : kernelCov neumannH (ϖ.map f) ν = ∫ z, neuPot ν (f z) ∂ϖ := by
  unfold kernelCov
  rw [integral_map hf.aemeasurable]
  · rfl
  · exact (measurable_neuPot ν).aestronglyMeasurable

theorem kernelCov_map_eq_prod {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {f : ℂ → ℂ}
    (hf : Measurable f) (hadm : IsAdmissibleH (ϖ.map f)) :
    kernelCov neumannH (ϖ.map f) (ϖ.map f) = ∫ p, neumannH (f p.1) (f p.2) ∂(ϖ.prod ϖ) := by
  have := hadm.1
  have h1 := integral_prod (fun p : ℂ × ℂ => neumannH p.1 p.2) (integrable_neumannH_prod hadm hadm)
  unfold kernelCov
  rw [← h1, Measure.map_prod_map ϖ ϖ hf hf,
    integral_map (hf.prodMap hf).aemeasurable measurable_neumannH.aestronglyMeasurable]
  rfl

theorem ne_conj_of_im_pos {p q : ℂ} (hp : 0 < p.im) (hq : 0 < q.im) : p ≠ conj q := by
  intro h; have := congrArg Complex.im h; simp at this; linarith

theorem abs_log_norm_sub_conj_le {p q : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hp : δ ≤ p.im) (hq : δ ≤ q.im)
    (hpR : ‖p‖ ≤ R) (hqR : ‖q‖ ≤ R) :
    |Real.log ‖p - conj q‖| ≤ |Real.log (2 * δ)| + |Real.log (2 * R)| := by
  refine abs_log_le_of_mem (by positivity) ?_ ?_
  · have : (p - conj q).im = p.im + q.im := by simp
    have h := Complex.abs_im_le_norm (p - conj q)
    rw [this, abs_of_pos (by linarith)] at h
    linarith
  · have := norm_sub_le p (conj q)
    rw [Complex.norm_conj] at this
    linarith

/-- The key bound: `|N(a,b)| ≤ |N(z,w)| + L` under two-point comparability. -/
theorem abs_neumannH_le {z w a b : ℂ} {δ R : ℝ} (hδ : 0 < δ) (hz : δ ≤ z.im) (hw : δ ≤ w.im)
    (ha : δ ≤ a.im) (hb : δ ≤ b.im) (hzR : ‖z‖ ≤ R) (hwR : ‖w‖ ≤ R) (haR : ‖a‖ ≤ R)
    (hbR : ‖b‖ ≤ R) (h1 : ‖z - w‖ * δ ≤ ‖a - b‖ * R) (h2 : ‖a - b‖ * δ ≤ ‖z - w‖ * R) :
    |neumannH a b| ≤ |neumannH z w| +
      (|Real.log (R / δ)| + 2 * (|Real.log (2 * δ)| + |Real.log (2 * R)|)) := by
  have hR : 0 < R := hδ.trans_le (ha.trans ((le_abs_self _).trans ((Complex.abs_im_le_norm a).trans haR)))
  have c1 := abs_log_norm_sub_conj_le hδ ha hb haR hbR
  have c2 := abs_log_norm_sub_conj_le hδ hz hw hzR hwR
  have hr : |Real.log ‖a - b‖ - Real.log ‖z - w‖| ≤ |Real.log (R / δ)| := by
    rcases eq_or_ne (z - w) 0 with h0 | h0
    · rw [h0, norm_zero, zero_mul] at h2
      have : ‖a - b‖ = 0 := le_antisymm (nonpos_of_mul_nonpos_left h2 hδ) (norm_nonneg _)
      rw [this, h0, norm_zero, Real.log_zero, sub_self, abs_zero]
      exact abs_nonneg _
    · have hd : 0 < ‖z - w‖ := norm_pos_iff.2 h0
      have he : 0 < ‖a - b‖ := by
        by_contra hn
        have : ‖a - b‖ = 0 := le_antisymm (not_lt.1 hn) (norm_nonneg _)
        rw [this, zero_mul] at h1
        nlinarith
      have e1 : Real.log ‖a - b‖ ≤ Real.log ‖z - w‖ + Real.log (R / δ) := by
        rw [← Real.log_mul hd.ne' (by positivity)]
        exact Real.log_le_log he (by rw [← mul_div_assoc, le_div_iff₀ hδ]; exact h2)
      have e2 : Real.log ‖z - w‖ ≤ Real.log ‖a - b‖ + Real.log (R / δ) := by
        rw [← Real.log_mul he.ne' (by positivity)]
        exact Real.log_le_log hd (by rw [← mul_div_assoc, le_div_iff₀ hδ]; exact h1)
      rw [abs_le]; constructor <;> linarith [le_abs_self (Real.log (R / δ))]
  unfold neumannH
  rw [abs_le] at c1 c2 hr ⊢
  constructor <;>
    cases abs_cases (-Real.log ‖z - w‖ - Real.log ‖z - conj w‖) <;> linarith

/-- Two-point comparability of the reverse flow on `{Im ≥ δ, ‖·‖ ≤ R}`. -/
theorem twoPoint_cmp (hV : Continuous V) {K : Set ℂ} (hKH : K ⊆ H) {δ R τ : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hb : ∀ z ∈ K, δ ≤ z.im ∧ ‖z‖ ≤ R ∧
      ∀ s ∈ Icc (0 : ℝ) τ, ‖revMap V s z‖ ≤ R ∧ δ ≤ (revMap V s z).im)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) {z w : ℂ} (hz : z ∈ K) (hw : w ∈ K) :
    ‖z - w‖ * δ ≤ ‖revMap V s z - revMap V s w‖ * R ∧
      ‖revMap V s z - revMap V s w‖ * δ ≤ ‖z - w‖ * R := by
    obtain ⟨hz1, hz2, hz3⟩ := hb z hz
    obtain ⟨hw1, hw2, hw3⟩ := hb w hw
    obtain ⟨hfz1, hfz2⟩ := hz3 s hs
    obtain ⟨hfw1, hfw2⟩ := hw3 s hs
    have imle : ∀ u : ℂ, ‖u‖ ≤ R → u.im ≤ R := fun u hu =>
      (le_abs_self _).trans ((Complex.abs_im_le_norm u).trans hu)
    have hlo := twoPoint_lower_sq hV (hKH hz) (hKH hw) hs.1
    have hup := twoPoint_upper_sq hV (hKH hz) (hKH hw) hs.1
    have d2 : δ ^ 2 ≤ z.im * w.im := by
      rw [sq]; exact mul_le_mul hz1 hw1 hδ.le (hδ.le.trans hz1)
    have d2' : δ ^ 2 ≤ (revMap V s z).im * (revMap V s w).im := by
      rw [sq]; exact mul_le_mul hfz2 hfw2 hδ.le (hδ.le.trans hfz2)
    have r2 : z.im * w.im ≤ R ^ 2 := by
      rw [sq]; exact mul_le_mul (imle z hz2) (imle w hw2) (hδ.le.trans hw1) hR.le
    have r2' : (revMap V s z).im * (revMap V s w).im ≤ R ^ 2 := by
      rw [sq]; exact mul_le_mul (imle _ hfz1) (imle _ hfw1) (hδ.le.trans hfw2) hR.le
    set d := ‖z - w‖
    set e := ‖revMap V s z - revMap V s w‖
    have hd0 : 0 ≤ d ^ 2 := sq_nonneg _
    have he0 : 0 ≤ e ^ 2 := sq_nonneg _
    constructor
    · rw [← sq_le_sq₀ (mul_nonneg (norm_nonneg _) hδ.le) (mul_nonneg (norm_nonneg _) hR.le)]
      calc (d * δ) ^ 2 = d ^ 2 * δ ^ 2 := by ring
        _ ≤ d ^ 2 * (z.im * w.im) := mul_le_mul_of_nonneg_left d2 hd0
        _ ≤ e ^ 2 * ((revMap V s z).im * (revMap V s w).im) := hlo
        _ ≤ e ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left r2' he0
        _ = (e * R) ^ 2 := by ring
    · rw [← sq_le_sq₀ (mul_nonneg (norm_nonneg _) hδ.le) (mul_nonneg (norm_nonneg _) hR.le)]
      calc (e * δ) ^ 2 = e ^ 2 * δ ^ 2 := by ring
        _ ≤ e ^ 2 * (z.im * w.im) := mul_le_mul_of_nonneg_left d2 he0
        _ ≤ d ^ 2 * ((revMap V s z).im * (revMap V s w).im) := hup
        _ ≤ d ^ 2 * R ^ 2 := mul_le_mul_of_nonneg_left r2' hd0
        _ = (d * R) ^ 2 := by ring

theorem tendsto_neumannH_comp {l : Filter ℝ} {g₁ g₂ : ℝ → ℂ} {p q : ℂ}
    (h₁ : Tendsto g₁ l (𝓝 p)) (h₂ : Tendsto g₂ l (𝓝 q)) (hne : p ≠ q) (hc : p ≠ conj q) :
    Tendsto (fun s => neumannH (g₁ s) (g₂ s)) l (𝓝 (neumannH p q)) := by
  have hc₂ : Tendsto (fun s => conj (g₂ s)) l (𝓝 (conj q)) :=
    (Complex.continuous_conj.tendsto q).comp h₂
  unfold neumannH
  exact (((h₁.sub h₂).norm.log (norm_ne_zero_iff.2 (sub_ne_zero.2 hne))).neg).sub
    ((h₁.sub hc₂).norm.log (norm_ne_zero_iff.2 (sub_ne_zero.2 hc)))

theorem tendsto_neumannH_diag {l : Filter ℝ} {g : ℝ → ℂ} {p : ℂ} (h : Tendsto g l (𝓝 p))
    (hp : 0 < p.im) : Tendsto (fun s => neumannH (g s) (g s)) l (𝓝 (neumannH p p)) := by
  have e : ∀ u : ℂ, neumannH u u = -Real.log ‖u - conj u‖ := fun u => by simp [neumannH]
  simp only [e]
  have hc : ContinuousAt (fun u : ℂ => -Real.log ‖u - conj u‖) p :=
    (ContinuousAt.log (f := fun u : ℂ => ‖u - conj u‖) (by fun_prop)
      (norm_ne_zero_iff.2 (sub_ne_zero.2 (ne_conj_of_im_pos hp hp)))).neg
  exact hc.tendsto.comp h

theorem tendsto_neumannH_revMap (hV : Continuous V) {z w : ℂ} (hzH : z ∈ H) (hwH : w ∈ H)
    {τ : ℝ} (hτ : 0 < τ) (hinj : z ≠ w → revMap V τ z ≠ revMap V τ w) :
    Tendsto (fun s => neumannH (revMap V s z) (revMap V s w)) (𝓝[<] τ)
      (𝓝 (neumannH (revMap V τ z) (revMap V τ w))) := by
  have hpz := im_revMap_pos hV hzH hτ.le
  have hpw := im_revMap_pos hV hwH hτ.le
  by_cases hzw : z = w
  · subst hzw
    exact tendsto_neumannH_diag (g := fun s => revMap V s z) (tendsto_revMap_nhdsLT hV hzH hτ) hpz
  · exact tendsto_neumannH_comp (g₁ := fun s => revMap V s z) (g₂ := fun s => revMap V s w)
      (tendsto_revMap_nhdsLT hV hzH hτ) (tendsto_revMap_nhdsLT hV hwH hτ) (hinj hzw)
      (ne_conj_of_im_pos hpz hpw)

variable {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ} {α C τ : ℝ}

/-- **`k(ϖ_s, ϖ_s) → k(ϖ_τ, ϖ_τ)`.** -/
theorem tendsto_kk (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H) (hϖK : ϖ Kᶜ = 0)
    (hα : 0 < α) (hF : IsFrostman ϖ α C) (hτ : 0 < τ) :
    Tendsto (fun s => kernelCov neumannH (varpiT V s ϖ) (varpiT V s ϖ)) (𝓝[<] τ)
      (𝓝 (kernelCov neumannH (varpiT V τ ϖ) (varpiT V τ ϖ))) := by
  obtain ⟨δ, R, hδ, hR, hb⟩ := revMap_bounds hV hK hKH τ
  have hKae := ae_mem_of_compl_null hϖK
  have hadm : IsAdmissibleH ϖ := by
    refine FrostmanReg.isAdmissibleH_of_frostman (R := R) (measure_mono_null ?_ hϖK) hF hα
    refine compl_subset_compl.2 fun z hz => ⟨mem_closedBall_zero_iff.2 (hb z hz).2.1, ?_⟩
    exact le_of_lt (show 0 < z.im from hKH hz)
  have heq : ∀ s, 0 ≤ s → kernelCov neumannH (varpiT V s ϖ) (varpiT V s ϖ) =
      ∫ p, neumannH (revMap V s p.1) (revMap V s p.2) ∂(ϖ.prod ϖ) := fun s hs =>
    kernelCov_map_eq_prod (measurable_revMap hV hs)
      (varpiT_good hV hK hKH hϖK hα hF hs).adm
  have hae : ∀ᵐ p ∂ϖ.prod ϖ, p.1 ∈ K ∧ p.2 ∈ K :=
    (Measure.quasiMeasurePreserving_fst.ae hKae).and
      (Measure.quasiMeasurePreserving_snd.ae hKae)
  have hbd : Integrable (fun p : ℂ × ℂ => |neumannH p.1 p.2| +
      (|Real.log (R / δ)| + 2 * (|Real.log (2 * δ)| + |Real.log (2 * R)|))) (ϖ.prod ϖ) :=
    (integrable_neumannH_prod hadm hadm).abs.add (integrable_const _)
  have hmeas : ∀ᶠ s in 𝓝[<] τ, AEStronglyMeasurable
      (fun p : ℂ × ℂ => neumannH (revMap V s p.1) (revMap V s p.2)) (ϖ.prod ϖ) := by
    filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
    have hm := measurable_revMap hV hs.1.le
    exact (measurable_neumannH.comp ((hm.comp measurable_fst).prodMk
      (hm.comp measurable_snd))).aestronglyMeasurable
  have hbound : ∀ᶠ s in 𝓝[<] τ, ∀ᵐ p ∂(ϖ.prod ϖ),
      ‖neumannH (revMap V s p.1) (revMap V s p.2)‖ ≤ |neumannH p.1 p.2| +
        (|Real.log (R / δ)| + 2 * (|Real.log (2 * δ)| + |Real.log (2 * R)|)) := by
    filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
    filter_upwards [hae] with p hp
    have hs' : s ∈ Icc (0 : ℝ) τ := ⟨hs.1.le, hs.2.le⟩
    obtain ⟨hz1, hz2, hz3⟩ := hb p.1 hp.1
    obtain ⟨hw1, hw2, hw3⟩ := hb p.2 hp.2
    obtain ⟨c1, c2⟩ := twoPoint_cmp hV hKH hδ hR hb hs' hp.1 hp.2
    rw [Real.norm_eq_abs]
    exact abs_neumannH_le hδ hz1 hw1 (hz3 s hs').2 (hw3 s hs').2 hz2 hw2 (hz3 s hs').1
      (hw3 s hs').1 c1 c2
  have hlim : ∀ᵐ p ∂(ϖ.prod ϖ), Tendsto
      (fun s => neumannH (revMap V s p.1) (revMap V s p.2)) (𝓝[<] τ)
      (𝓝 (neumannH (revMap V τ p.1) (revMap V τ p.2))) := by
    filter_upwards [hae] with p hp
    refine tendsto_neumannH_revMap hV (hKH hp.1) (hKH hp.2) hτ fun hzw h => hzw ?_
    have c := (twoPoint_cmp hV hKH hδ hR hb ⟨hτ.le, le_rfl⟩ hp.1 hp.2).1
    rw [h, sub_self, norm_zero, zero_mul] at c
    have : ‖p.1 - p.2‖ = 0 := le_antisymm (nonpos_of_mul_nonpos_left c hδ) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  have hT := tendsto_integral_filter_of_dominated_convergence _ hmeas hbound hbd hlim
  rw [heq τ hτ.le]
  refine hT.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
  exact (heq s hs.1.le).symm

/-- **`k(ϖ_s, ν) → k(ϖ_τ, ν)`** for a good measure `ν`. -/
theorem tendsto_kernelCov_left (hV : Continuous V) (hK : IsCompact K) (hKH : K ⊆ H)
    (hϖK : ϖ Kᶜ = 0) (hτ : 0 < τ) {ν : Measure ℂ} (hν : GoodMeas ν) :
    Tendsto (fun s => kernelCov neumannH (varpiT V s ϖ) ν) (𝓝[<] τ)
      (𝓝 (kernelCov neumannH (varpiT V τ ϖ) ν)) := by
  have := hν.prob
  have hc := hν.continuous_neuPot
  rw [varpiT, kernelCov_map_left (measurable_revMap hV hτ.le)]
  refine (tendsto_integral_comp_revMap hV hK hKH hϖK hτ (G := fun _ w => neuPot ν w)
    ((measurable_neuPot ν).comp measurable_snd) (a := fun _ => 0) (a₀ := 0) tendsto_const_nhds
    (hc.comp continuous_snd).continuousOn).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hτ] with s hs
  rw [varpiT, kernelCov_map_left (measurable_revMap hV hs.1.le)]

end E4Grid
end QuantumZipper
