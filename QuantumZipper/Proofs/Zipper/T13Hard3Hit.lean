import QuantumZipper.Proofs.Probability.CameronMartin
import QuantumZipper.Proofs.ItoLite.Oscillation
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpreadHitPure
import QuantumZipper.Proofs.Zipper.D3PlusN2HeartMix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# T13-HARD3-HIT: the hitting-time spread of a drifted Brownian motion (`HitLevSpreadStmt`)

For a Brownian motion `b`, `ν = Q − α > 0` and `c ≥ 0`, the first passage times
`T_L = inf {t ≥ 0 : L + √2 b_t − ν t ≤ 0}` and `T_{L+c}` have laws at total-variation distance
`→ 0` as `L → ∞` (`D3Plus.hitLevSpreadStmt_holds`).

The textbook proof (explicit inverse-Gaussian density of `T_L`, e.g. Karatzas–Shreve,
*Brownian Motion and Stochastic Calculus*, §3.5.C) needs the reflection principle and Girsanov's
theorem, which the repository lacks. We use instead an **own argument by Cameron–Martin shift
coupling** (recorded as own argument):

* with `τ = L/(2ν)` and `λ = c/(√2 τ)`, the Cameron–Martin shift `h(t) = λ min(t, τ)` (the
  covariance shift `K(·, λ δ_τ)` of Brownian motion) changes the law of the whole path by at most
  `(exp(λ²τ) − 1)^{1/2} = (exp(c²ν/L) − 1)^{1/2}` on every measurable path set
  (repository Blueprint A9, `CameronMartin.abs_measureReal_shift_sub_le`); the hitting time is a
  measurable function of the path on continuous paths (`D3Plus.measurable_Tc_of_cont`, applied on
  the subtype of continuous paths);
* deterministically, `√2 h(t) = c min(t,τ)/τ`, so the shifted path at level `L` coincides with the
  unshifted path at level `L + c` after time `τ`, and both are positive on `[0, τ]` as soon as
  `sup_{[0,τ]} |b| ≤ L/4`; hence the two hitting times coincide off that event (coupling
  inequality `D3Plus.tvDist_map_le_of_ae_eq_off`);
* the oscillation tail `BMOsc.bmOsc_tail` (Doob's maximal inequality) gives
  `P(sup_{[0,τ]} |b| > L/4) ≤ 2 exp(−νL/16)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace T13Hit

open CameronMartin

theorem covShift_single_hit {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : I → Ω → ℝ}
    (τ : I) (lam : ℝ) (j : I) :
    covShift X P (Finsupp.single τ lam) j = lam * covK X P j τ := by
  classical
  unfold covShift
  rw [Finset.sum_subset Finsupp.support_single_subset (fun i _ hi => by
    rw [Finsupp.mem_support_iff, not_not] at hi; rw [hi, zero_mul]), Finset.sum_singleton,
    Finsupp.single_eq_same]

theorem covNorm_single_hit {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : I → Ω → ℝ}
    (τ : I) (lam : ℝ) :
    covNorm X P (Finsupp.single τ lam) = lam * (lam * covK X P τ τ) := by
  classical
  unfold covNorm
  rw [Finset.sum_subset Finsupp.support_single_subset (fun i _ hi => by
    rw [Finsupp.mem_support_iff, not_not] at hi; rw [hi, zero_mul]), Finset.sum_singleton,
    Finsupp.single_eq_same, covShift_single_hit]

/-- Deterministic core of the coupling: two paths positive on `[0, τ]` and equal after `τ` have
the same first passage time below `0`. -/
theorem sInf_eq_of_agree_hit (f g : ℝ → ℝ) (τ : ℝ)
    (hf : ∀ t, 0 ≤ t → t ≤ τ → 0 < f t) (hg : ∀ t, 0 ≤ t → t ≤ τ → 0 < g t)
    (hfg : ∀ t, τ ≤ t → f t = g t) :
    sInf {t | 0 ≤ t ∧ f t ≤ 0} = sInf {t | 0 ≤ t ∧ g t ≤ 0} := by
  congr 1
  ext t
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h⟩
    rcases le_total t τ with h1 | h1
    · exact absurd h (not_le.2 (hf t h0 h1))
    · exact ⟨h0, hfg t h1 ▸ h⟩
  · rintro ⟨h0, h⟩
    rcases le_total t τ with h1 | h1
    · exact absurd h (not_le.2 (hg t h0 h1))
    · exact ⟨h0, (hfg t h1).symm ▸ h⟩

/-- A continuous path is dominated on `[t, t+s]` by its oscillation. -/
theorem abs_sub_le_bmOsc_hit {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    {t s r : ℝ≥0} (hr : r ∈ Icc t (t + s)) : |B r ω - B t ω| ≤ bmOsc B t s ω := by
  rw [bmOsc_eq_iSup_subtype hc]
  have hK := (isCompact_Icc (a := t) (b := t + s)).image
    (f := fun r => |B r ω - B t ω|) ((hc.sub continuous_const).abs)
  have hbdd : BddAbove (Set.range fun x : Set.Icc t (t + s) => |B x ω - B t ω|) := by
    have h := hK.bddAbove
    rwa [Set.image_eq_range] at h
  exact le_ciSup hbdd ⟨r, hr⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Cameron–Martin step.** A Cameron–Martin shift moves the law of the hitting time by at most
`(exp K(σ,σ) − 1)^{1/2}` in total variation. -/
theorem tv_shift_le_hit {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, Measurable (W t)) (hWc : ∀ ω, Continuous fun t => W t ω)
    (σ : ℝ≥0 →₀ ℝ) (α Q L : ℝ) :
    TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q L W ω)
      (P.map fun ω => ZoomRadial.Tc α Q L (fun j ω => W j ω + covShift W P σ j) ω) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (covNorm W P σ) - 1)) := by
  let C := {f : ℝ≥0 → ℝ // Continuous f}
  have hTC : Measurable fun f : C => ZoomRadial.Tc α Q L (fun t (f : C) => f.1 t) f :=
    D3Plus.measurable_Tc_of_cont (fun f => f.2)
      (fun t => (measurable_pi_apply _).comp measurable_subtype_coe) α Q L
  have hWG : IsGaussianProcess W P := hW.toIsPreBrownianReal.isGaussianProcess
  have hYm : ∀ t, Measurable fun ω => W t ω + covShift W P σ t :=
    fun t => (hWm t).add_const _
  have hYc : ∀ ω, Continuous fun t => W t ω + covShift W P σ t := by
    intro ω
    have hcs : ∀ t, covShift W P σ t = ∑ i ∈ σ.support, σ i * ((min t i : ℝ≥0) : ℝ) := by
      intro t
      unfold covShift covK
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hW.toIsPreBrownianReal.covariance_eval]
    simp only [hcs]
    exact (hWc ω).add (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (NNReal.continuous_coe.comp (continuous_id.min continuous_const)))
  have hT1 := D3Plus.measurable_Tc_of_cont hWc (fun t => hWm _) α Q L
  have hT2 := D3Plus.measurable_Tc_of_cont (b := fun j ω => W j ω + covShift W P σ j) hYc
    (fun t => hYm _) α Q L
  refine D3Plus.tvDist_le_ofReal_of_abs fun S hS => ?_
  obtain ⟨A, hA, hAeq⟩ := hTC hS
  have key : ∀ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) → (∀ ω, Continuous fun t => Y t ω) →
      (P.map fun ω => ZoomRadial.Tc α Q L Y ω) S = (P.map fun ω j => Y j ω) A := by
    intro Y hYm' hYc'
    rw [Measure.map_apply (D3Plus.measurable_Tc_of_cont hYc' (fun t => hYm' _) α Q L) hS,
      Measure.map_apply (measurable_pi_iff.2 hYm') hA]
    congr 1
    ext ω
    rw [Set.ext_iff] at hAeq
    exact (hAeq ⟨fun t => Y t ω, hYc' ω⟩).symm
  rw [key W hWm hWc, key _ hYm hYc, abs_sub_comm]
  exact abs_measureReal_shift_sub_le hWG hWm (fun i => hW.toIsPreBrownianReal.integral_eval i)
    σ A hA

/-- **Coupling step.** Off the event `{osc_{[0,τ]} W > L/4}`, the shifted hitting time at level
`L` equals the unshifted hitting time at level `L + c`. -/
theorem tv_couple_le_hit {W : ℝ≥0 → Ω → ℝ} (hWm : ∀ t, Measurable (W t))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    {α Q L c lam : ℝ} {τ : ℝ≥0} (h : ℝ≥0 → ℝ) (hh : ∀ j : ℝ≥0, h j = lam * min (j : ℝ) τ)
    (hhc : Continuous h) (hQ : α < Q) (hL : 0 < L) (hτ : (τ : ℝ) = L / (2 * (Q - α)))
    (hlam : Real.sqrt 2 * lam * τ = c) (hlam0 : 0 ≤ lam) :
    TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q L (fun j ω => W j ω + h j) ω)
      (P.map fun ω => ZoomRadial.Tc α Q (L + c) W ω) ≤ P {ω | L / 4 < bmOsc W 0 τ ω} := by
  have hYc : ∀ ω, Continuous fun t => W t ω + h t := fun ω => (hWc ω).add hhc
  refine D3Plus.tvDist_map_le_of_ae_eq_off
    (D3Plus.measurable_Tc_of_cont (b := fun j ω => W j ω + h j) hYc
      (fun t => (hWm _).add_const _) α Q L).aemeasurable
    (D3Plus.measurable_Tc_of_cont hWc (fun t => hWm _) α Q (L + c)).aemeasurable _
    (ae_of_all _ fun ω hω => ?_)
  simp only [mem_ofPred_eq, not_lt] at hω
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := by positivity
  have hs2lt : Real.sqrt 2 < 2 := by nlinarith
  have hν : 0 < Q - α := by linarith
  have hντ : (Q - α) * τ = L / 2 := by rw [hτ]; field_simp
  have hbd : ∀ t : ℝ, 0 ≤ t → t ≤ τ → 0 < L + Real.sqrt 2 * W t.toNNReal ω + (α - Q) * t := by
    intro t h0 ht
    have hmem : t.toNNReal ∈ Icc (0 : ℝ≥0) (0 + τ) := ⟨zero_le, by
      rw [zero_add, ← NNReal.coe_le_coe, Real.coe_toNNReal _ h0]; exact ht⟩
    have h1 := (abs_sub_le_bmOsc_hit (hWc ω) hmem).trans hω
    rw [hW0, sub_zero] at h1
    have h2 := neg_abs_le (W t.toNNReal ω)
    have h3 : (Q - α) * t ≤ L / 2 := hντ ▸ mul_le_mul_of_nonneg_left ht hν.le
    have h4 : 0 ≤ Real.sqrt 2 * (W t.toNNReal ω + L / 4) := mul_nonneg hs2p.le (by linarith)
    have h5 : 0 < (2 - Real.sqrt 2) * L := mul_pos (by linarith) hL
    nlinarith
  unfold ZoomRadial.Tc
  refine sInf_eq_of_agree_hit _ _ τ (fun t h0 ht => ?_) (fun t h0 ht => ?_) (fun t ht => ?_)
  · simp only [ZoomRadial.Xc, hh]
    have h1 := hbd t h0 ht
    have h2 : 0 ≤ Real.sqrt 2 * (lam * min ((t.toNNReal : ℝ≥0) : ℝ) τ) :=
      mul_nonneg hs2p.le (mul_nonneg hlam0 (le_min (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)))
    nlinarith
  · simp only [ZoomRadial.Xc]
    have h1 := hbd t h0 ht
    have hc : 0 ≤ c := by rw [← hlam]; positivity
    linarith
  · simp only [ZoomRadial.Xc, hh]
    have h0 : (0 : ℝ) ≤ t := τ.2.trans ht
    rw [Real.coe_toNNReal _ h0, min_eq_right ht, ← hlam]
    ring

/-- **Main estimate for a good version.** -/
theorem tv_good_le_hit {W : ℝ≥0 → Ω → ℝ} (hW : IsBrownianReal W P)
    (hWm : ∀ t, Measurable (W t)) (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    {α Q c L : ℝ} (hQ : α < Q) (hc : 0 ≤ c) (hL : 0 < L) :
    TV.tvDist (P.map fun ω => ZoomRadial.Tc α Q L W ω)
      (P.map fun ω => ZoomRadial.Tc α Q (L + c) W ω) ≤
      ENNReal.ofReal (Real.sqrt (Real.exp (c ^ 2 * (Q - α) / L) - 1)) +
        ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * L))) := by
  have hν : 0 < Q - α := by linarith
  have hτ0 : 0 < L / (2 * (Q - α)) := by positivity
  set τ : ℝ≥0 := ⟨L / (2 * (Q - α)), hτ0.le⟩ with hτdef
  have hτ : (τ : ℝ) = L / (2 * (Q - α)) := rfl
  have hτp : (0 : ℝ) < τ := hτ0
  have hs2p : 0 < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set lam : ℝ := c / (Real.sqrt 2 * τ) with hlamdef
  have hlam : Real.sqrt 2 * lam * τ = c := by rw [hlamdef]; field_simp
  have hlam0 : 0 ≤ lam := by positivity
  set σ : ℝ≥0 →₀ ℝ := Finsupp.single τ lam with hσ
  have hcovK : ∀ j, covK W P j τ = min (j : ℝ) τ := fun j => by
    unfold covK; rw [hW.toIsPreBrownianReal.covariance_eval]; simp
  have hh : ∀ j : ℝ≥0, covShift W P σ j = lam * min (j : ℝ) τ := fun j => by
    rw [hσ, covShift_single_hit, hcovK]
  have h2τ : 2 * (τ : ℝ) * (Q - α) = L := by rw [hτ]; field_simp
  have hc2 : c ^ 2 = 2 * (lam * (lam * τ)) * τ := by
    rw [← hlam]; linear_combination (lam * τ) ^ 2 * hs2
  have hN : covNorm W P σ = c ^ 2 * (Q - α) / L := by
    rw [hσ, covNorm_single_hit, hcovK, min_self, eq_div_iff hL.ne']
    nth_rewrite 1 [← h2τ]
    rw [hc2]; ring
  have hhc : Continuous fun j : ℝ≥0 => covShift W P σ j := by
    simp only [hh]
    exact continuous_const.mul (NNReal.continuous_coe.min continuous_const)
  have e1 := tv_shift_le_hit hW hWm hWc σ α Q L
  rw [hN] at e1
  have e2 := tv_couple_le_hit (P := P) hWm hWc hW0 (fun j => covShift W P σ j) hh hhc hQ hL hτ
    hlam hlam0
  have e3 := BMOsc.bmOsc_tail hW.toIsPreBrownianReal hWm (fun ω => hWc ω) 0 τ
    (NNReal.coe_pos.1 hτp) (a := L / 4) (by positivity)
  have hexp : -(L / 4) ^ 2 / (2 * (τ : ℝ)) = -((Q - α) / 16 * L) := by
    rw [hτ]; field_simp; ring
  rw [hexp] at e3
  calc _ ≤ _ := TV.tvDist_triangle
    _ ≤ _ := add_le_add e1 (e2.trans e3)

end T13Hit

namespace D3Plus

/-- **`HitLevSpreadStmt` holds** (T13-HARD3-HIT): own Cameron–Martin shift-coupling argument,
see the module docstring. -/
theorem hitLevSpreadStmt_holds : HitLevSpreadStmt := by
  intro α Q Ω _ P _ b hb hQ
  obtain ⟨W, hWm, hWc, hW0, hW, hWb⟩ := RS.exists_good_version0 hb
  have hmap : ∀ L, (P.map fun ω => ZoomRadial.Tc α Q L b ω) =
      P.map fun ω => ZoomRadial.Tc α Q L W ω := fun L =>
    Measure.map_congr (hWb.mono fun ω h => Tc_congr fun t => (h t).symm)
  simp only [hmap]
  have hν : 0 < Q - α := by linarith
  have pos : ∀ c : ℝ, 0 ≤ c → Tendsto (fun L => TV.tvDist
      (P.map fun ω => ZoomRadial.Tc α Q L W ω)
      (P.map fun ω => ZoomRadial.Tc α Q (L + c) W ω)) atTop (𝓝 0) := by
    intro c hc
    have hlim : Tendsto (fun L : ℝ =>
        ENNReal.ofReal (Real.sqrt (Real.exp (c ^ 2 * (Q - α) / L) - 1)) +
          ENNReal.ofReal (2 * Real.exp (-((Q - α) / 16 * L)))) atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 + ENNReal.ofReal 0 by simp]
      refine (ENNReal.tendsto_ofReal ?_).add (ENNReal.tendsto_ofReal ?_)
      · have h1 : Tendsto (fun L : ℝ => c ^ 2 * (Q - α) / L) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop tendsto_id
        have h2 := (((Real.continuous_exp.tendsto 0).comp h1).sub_const 1)
        have h3 := (Real.continuous_sqrt.tendsto _).comp h2
        rw [Real.exp_zero, sub_self, Real.sqrt_zero] at h3
        exact h3
      · have h1 : Tendsto (fun L : ℝ => (Q - α) / 16 * L) atTop atTop :=
          tendsto_id.const_mul_atTop (by positivity)
        have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul 2
        simpa using h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    exact T13Hit.tv_good_le_hit hW hWm hWc hW0 hQ hc hL
  intro c
  rcases le_total 0 c with hc | hc
  · exact pos c hc
  · have h := (pos (-c) (by linarith)).comp (tendsto_atTop_add_const_right atTop c tendsto_id)
    refine h.congr fun L => ?_
    simp only [Function.comp_apply, id]
    rw [TV.tvDist_comm, show L + c + -c = L by ring]

end D3Plus
end QuantumZipper
