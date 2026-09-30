import QuantumZipper.Proofs.Thm18.G1PairQuantDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PAIR-QUANT (2): the modulus for every Lipschitz function from the countable certificate

For a function `F : ℂ × ℝ → ℝ` continuous on `Hbar × (0,∞)` (the continuous witness of a regular
sample), the pairings `Φ_f(t) = ∫ F(u,t) f(u) du` with continuous `f` vanishing off a compact
subset of `Hbar` are continuous in `t > 0`. A modulus bound for a dense sequence of `LipSet m N`
passes to all of `LipSet m N` (dominated convergence: the members are bounded by `N ‖u‖` on
`Kb m`) and from rational to real radii (continuity). Result: `lipBound_of_count`, and the
oscillation criterion `exists_tendsto_of_sqrt_bound`.

Own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

variable {F : ℂ × ℝ → ℝ}

theorem integrable_dF_mul (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {f : ℂ → ℝ} (hfc : Continuous f)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar) (hf0 : ∀ z ∉ K, f z = 0) {t s : ℝ}
    (ht : 0 < t) (hs : 0 < s) : Integrable (fun u => (F (u, t) - F (u, s)) * f u) := by
  have h1 : ContinuousOn (fun u => F (u, t)) K :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun u hu => ⟨hKH hu, ht⟩
  have h2 : ContinuousOn (fun u => F (u, s)) K :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun u hu => ⟨hKH hu, hs⟩
  exact (((h1.sub h2).mul hfc.continuousOn).integrableOn_compact hK).integrable_of_forall_notMem_eq_zero
    fun u hu => by simp [hf0 u hu]

theorem integrable_F_mul (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {f : ℂ → ℝ} (hfc : Continuous f)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar) (hf0 : ∀ z ∉ K, f z = 0) {t : ℝ}
    (ht : 0 < t) : Integrable (fun u => F (u, t) * f u) := by
  have h1 : ContinuousOn (fun u => F (u, t)) K :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun u hu => ⟨hKH hu, ht⟩
  exact ((h1.mul hfc.continuousOn).integrableOn_compact hK).integrable_of_forall_notMem_eq_zero
    fun u hu => by simp [hf0 u hu]

/-- The retraction `u ↦ Re u + i |Im u|` onto `Hbar`. -/
def retr (u : ℂ) : ℂ := (u.re : ℂ) + (|u.im| : ℝ) * Complex.I

theorem continuous_retr : Continuous retr := by unfold retr; fun_prop

theorem retr_mem (u : ℂ) : retr u ∈ Hbar := by
  show (0 : ℝ) ≤ (retr u).im
  simp [retr]

theorem retr_of_mem {u : ℂ} (hu : u ∈ Hbar) : retr u = u := by
  have hu' : (0 : ℝ) ≤ u.im := hu
  apply Complex.ext <;> simp [retr, abs_of_nonneg hu']

/-- **Continuity of the pairings in the radius.** -/
theorem continuousOn_Phi (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {f : ℂ → ℝ} (hfc : Continuous f)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ Hbar) (hf0 : ∀ z ∉ K, f z = 0) :
    ContinuousOn (fun t => ∫ u, F (u, t) * f u) (Ioi 0) := by
  intro t0 ht0
  have ht0' : (0 : ℝ) < t0 := ht0
  set G : ℝ → ℂ → ℝ := fun t u => F (retr u, max t (t0 / 2)) * f u with hG
  have hGc : Continuous (uncurry G) := by
    refine Continuous.mul ?_ (hfc.comp continuous_snd)
    refine hF.comp_continuous ((continuous_retr.comp continuous_snd).prodMk
      (continuous_fst.max continuous_const)) fun p => ⟨retr_mem _, ?_⟩
    show (0 : ℝ) < max p.1 (t0 / 2)
    exact lt_max_of_lt_right (by linarith)
  have hcont : Continuous fun t => ∫ u in K, G t u :=
    continuous_parametric_integral_of_continuous hGc hK
  have heq : (fun t => ∫ u in K, G t u) =ᶠ[𝓝 t0] fun t => ∫ u, F (u, t) * f u := by
    filter_upwards [Ioi_mem_nhds (show t0 / 2 < t0 by linarith)] with t ht
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (μ := volume)
      (f := fun u => F (u, t) * f u) fun u hu => by simp [hf0 u hu]]
    refine setIntegral_congr_fun hK.isClosed.measurableSet fun u hu => ?_
    simp only [hG, retr_of_mem (hKH hu), max_eq_left (le_of_lt (show t0 / 2 < t from ht))]
  exact (hcont.continuousAt.congr heq).continuousWithinAt

/-- **Density step**: a bound for the dense sequence of `LipSet m N` holds on all of it. -/
theorem bound_of_dseq (hF : ContinuousOn F (Hbar ×ˢ Ioi 0)) {m N : ℕ} {f : C(ℂ, ℝ)}
    (hf : f ∈ LipSet m N) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) {B : ℝ}
    (hB : ∀ i, |∫ u, (F (u, t) - F (u, s)) * dseq m N i u| ≤ B) :
    |∫ u, (F (u, t) - F (u, s)) * f u| ≤ B := by
  obtain ⟨k, hk⟩ := exists_dseq_tendsto hf
  set D : ℂ → ℝ := fun u => F (u, t) - F (u, s) with hD
  have hDc : ContinuousOn D (Kb m) :=
    ((hF.comp (continuous_id.prodMk continuous_const).continuousOn
      fun u hu => ⟨Kb_subset_Hbar m hu, ht⟩).sub
    (hF.comp (continuous_id.prodMk continuous_const).continuousOn
      fun u hu => ⟨Kb_subset_Hbar m hu, hs⟩))
  set bd : ℂ → ℝ := (Kb m).indicator fun u => |D u| * ((N : ℝ) * ‖u‖) with hbd
  have hbdi : Integrable bd := by
    refine (integrable_indicator_iff (isCompact_Kb m).isClosed.measurableSet).2 ?_
    exact ((hDc.abs).mul (continuousOn_const.mul continuous_norm.continuousOn)).integrableOn_compact
      (isCompact_Kb m)
  have hmem : ∀ g ∈ LipSet m N, ∀ u, ‖D u * g u‖ ≤ bd u := by
    intro g hg u
    by_cases hu : u ∈ Kb m
    · rw [hbd, indicator_of_mem hu, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h0 : g 0 = 0 := hg.2 0 (zero_notMem_Kb m)
      have := hg.1.dist_le_mul u 0
      rw [Real.dist_eq, h0, sub_zero, dist_zero_right] at this
      simpa using this
    · rw [hbd, indicator_of_notMem hu, hg.2 u hu, mul_zero, norm_zero]
  have hlim : Tendsto (fun n => ∫ u, D u * dseq m N (k n) u) atTop (𝓝 (∫ u, D u * f u)) := by
    refine tendsto_integral_of_dominated_convergence bd (fun n => ?_) hbdi
      (fun n => ae_of_all _ (hmem _ (dseq_mem m N (k n)))) (ae_of_all _ fun u => ?_)
    · exact (integrable_dF_mul hF (dseq m N (k n)).continuous (isCompact_Kb m)
        (Kb_subset_Hbar m) (dseq_mem m N (k n)).2 ht hs).aestronglyMeasurable
    · exact (((continuous_eval_const u).tendsto f).comp hk).const_mul (D u)
  exact le_of_tendsto' hlim.abs fun n => hB (k n)

/-- **Rational to real radii.** -/
theorem bound_real {Φ : ℝ → ℝ} (hΦ : ContinuousOn Φ (Ioi 0)) {C δ : ℝ}
    (h : ∀ t s : ℚ, (0 : ℝ) < t → (t : ℝ) < δ → (0 : ℝ) < s → (s : ℝ) < δ →
      |Φ t - Φ s| ≤ C * Real.sqrt (max (t : ℝ) s)) :
    ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ, |Φ t - Φ s| ≤ C * Real.sqrt (max t s) := by
  intro t ht s hs
  by_contra hlt
  push Not at hlt
  set φ : ℝ × ℝ → ℝ := fun p => |Φ p.1 - Φ p.2| - C * Real.sqrt (max p.1 p.2) with hφ
  have hφc : ContinuousOn φ (Ioo 0 δ ×ˢ Ioo 0 δ) := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Φ p.1) (Ioo 0 δ ×ˢ Ioo 0 δ) :=
      hΦ.comp continuous_fst.continuousOn fun p hp => (hp.1.1 : (0 : ℝ) < p.1)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Φ p.2) (Ioo 0 δ ×ˢ Ioo 0 δ) :=
      hΦ.comp continuous_snd.continuousOn fun p hp => (hp.2.1 : (0 : ℝ) < p.2)
    exact ((h1.sub h2).abs).sub (continuousOn_const.mul
      (Real.continuous_sqrt.comp (continuous_fst.max continuous_snd)).continuousOn)
  have hU : IsOpen (Ioo 0 δ ×ˢ Ioo 0 δ ∩ φ ⁻¹' Ioi 0) :=
    hφc.isOpen_inter_preimage (isOpen_Ioo.prod isOpen_Ioo) isOpen_Ioi
  have hne : (Ioo 0 δ ×ˢ Ioo 0 δ ∩ φ ⁻¹' Ioi 0).Nonempty :=
    ⟨(t, s), ⟨ht, hs⟩, show (0 : ℝ) < φ (t, s) by simp only [hφ]; linarith⟩
  obtain ⟨q, hq1, hq2⟩ := ((Rat.denseRange_cast (𝕜 := ℝ)).prodMap
    (Rat.denseRange_cast (𝕜 := ℝ))).exists_mem_open hU hne
  have hb := h q.1 q.2 hq1.1.1 hq1.1.2 hq1.2.1 hq1.2.2
  have : (0 : ℝ) < φ ((q.1 : ℝ), (q.2 : ℝ)) := hq2
  simp only [hφ] at this
  linarith

/-- **Oscillation criterion with a `√` modulus.** -/
theorem exists_tendsto_of_sqrt_bound {Φ : ℝ → ℝ} {C δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ, |Φ t - Φ s| ≤ C * Real.sqrt (max t s)) :
    ∃ L : ℝ, Tendsto Φ (𝓝[>] 0) (𝓝 L) := by
  refine D3Plus.exists_tendsto_of_oscillation fun ε hε => ?_
  have hM : 0 < |C| + 1 := by positivity
  refine ⟨min δ ((ε / (|C| + 1)) ^ 2), lt_min hδ (by positivity), fun t ht s hs => ?_⟩
  have hm : max t s < (ε / (|C| + 1)) ^ 2 :=
    max_lt (ht.2.trans_le (min_le_right _ _)) (hs.2.trans_le (min_le_right _ _))
  have hsq : Real.sqrt (max t s) < ε / (|C| + 1) :=
    (Real.sqrt_lt' (by positivity)).2 hm
  have hs0 := Real.sqrt_nonneg (max t s)
  calc |Φ t - Φ s| ≤ C * Real.sqrt (max t s) :=
        h t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩ s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩
    _ ≤ (|C| + 1) * Real.sqrt (max t s) := by nlinarith [le_abs_self C]
    _ ≤ (|C| + 1) * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left hsq.le hM.le
    _ = ε := by field_simp

/-- The certificate integrals are the `F`-integrals, for functions vanishing off `Kb m`. -/
theorem pairInt_eq {x : FieldSample} (hFx : IsRegularWith x F) {m : ℕ} {g : ℂ → ℝ}
    (hg0 : ∀ z ∉ Kb m, g z = 0) {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    pairInt x g t s = ∫ u, (F (u, t) - F (u, s)) * g u := by
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  by_cases hu : u ∈ Kb m
  · simp only
    rw [hFx.evalReg_fc_of_mem (Kb_subset_Hbar m hu) ht,
      hFx.evalReg_fc_of_mem (Kb_subset_Hbar m hu) hs]
  · simp [hg0 u hu]

/-- **The modulus for every Lipschitz function**, from the countable certificate. -/
theorem lipBound_of_count {x : FieldSample} (hFx : IsRegularWith x F) (hc : CountCond x)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {L : ℝ≥0} {f : ℂ → ℝ} (hf : LipschitzWith L f)
    (hf0 : ∀ z ∉ K, f z = 0) : ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ, ∀ s ∈ Ioo 0 δ,
      |(∫ u, F (u, t) * f u) - ∫ u, F (u, s) * f u| ≤ C * Real.sqrt (max t s) := by
  obtain ⟨m, hm⟩ := exists_Kb hK hKH
  set N : ℕ := ⌈L⌉₊ with hN
  set fc : C(ℂ, ℝ) := ⟨f, hf.continuous⟩ with hfc
  have hfm : fc ∈ LipSet m N :=
    ⟨hf.weaken (Nat.le_ceil L), fun z hz => hf0 z fun h => hz (hm h)⟩
  obtain ⟨C, e, hCe⟩ := hc m N
  have hF := hFx.1
  have hδ : (0 : ℝ) < 1 / ((e : ℝ) + 1) := by positivity
  refine ⟨C * N, 1 / ((e : ℝ) + 1), hδ, bound_real
    (continuousOn_Phi hF hf.continuous (isCompact_Kb m) (Kb_subset_Hbar m) hfm.2) ?_⟩
  intro t s ht0 ht hs0 hs
  have hsub : (∫ u, F (u, t) * f u) - ∫ u, F (u, s) * f u =
      ∫ u, (F (u, t) - F (u, s)) * fc u := by
    rw [← integral_sub (integrable_F_mul hF hf.continuous (isCompact_Kb m) (Kb_subset_Hbar m)
      hfm.2 ht0) (integrable_F_mul hF hf.continuous (isCompact_Kb m) (Kb_subset_Hbar m)
      hfm.2 hs0)]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    simp only [hfc, ContinuousMap.coe_mk]
    ring
  rw [hsub, mul_assoc]
  refine bound_of_dseq hF hfm ht0 hs0 fun i => ?_
  rw [← pairInt_eq hFx (dseq_mem m N i).2 ht0 hs0, ← mul_assoc]
  exact hCe i t s ht0 ht hs0 hs

end G1Rest
end Thm18Asm
end QuantumZipper
