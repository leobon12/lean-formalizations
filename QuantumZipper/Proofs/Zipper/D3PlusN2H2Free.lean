import QuantumZipper.Proofs.Zipper.D3PlusN2H2FreeCore
import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinDens
import QuantumZipper.Proofs.Zipper.D3PlusN2H2Repr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H2 free-field regularization identity (task N2H2-FREE)

`N2H2ReprFreeStmt` (`D3PlusN2H2Repr.lean`) asks, for a free field `X`, a random constant `c` and
a scale `a > 0`, that **almost surely, at every window index `i` simultaneously**,

  `evalReg (lateralPart (X − c)) (a·μ_i) = evalReg X (a·μ_i) − ∫ radAvgReg X (a‖z‖) dμ_i`.

Proved here:

* `ae_n2H2ReprFree_circ`: the identity a.s. **simultaneously at all folded circles** of the
  window (convergence of the regularizations by clause 3 of `IsRegularWith`, at every circle);
* `ae_n2H2ReprFree_dens`: the identity a.s. at **each fixed density** of the window
  (convergence by `ae_contPair_G_density`);
* hence the per-index form `N2H2ReprFreeIStmt` (`n2H2ReprFreeIStmt_holds`).

The uniform-in-densities form (the order `∀ᵐ ω, ∀ i` of `N2H2ReprFreeStmt`) is not proved: at a
density whose regularizations diverge both sides are junk values that differ by
`∫ radAvgReg X (a‖z‖) dμ_i`, and for a GFF such densities exist a.s. (see the task report).

Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78
(`h = h† + h_{|·|}(0)`). Pathwise bookkeeping: own elementary work. The radial profile
`ρ ↦ G(0, ρ)` of the regular version is `radPsi + G(0, R)` (`ae_zRadB_eq`), log-dominated by the
strong law of large numbers for the radial Brownian motion (`logDom_radPsi`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK

section Good

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → FieldSample}

/-- The good event of the free field at radius `R`: good sample, log-dominated radial profile,
and convergence of the regularization to the raw value at every dyadic folded circle. -/
theorem ae_free_good (hX : IsFreeGFFModConstH X P) {G : Ω → ℂ × ℝ → ℝ}
    (hG : IsRegVersion X P G) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, GoodRad (X ω) (G ω) ∧
      (∃ C D : ℝ, LogDom (fun ρ => radPsi X R ω ρ + G ω (0, R)) R C D) ∧
      (∀ ρ, 0 < ρ → ρ ≤ R → G ω (0, ρ) = radPsi X R ω ρ + G ω (0, R)) ∧
      (∀ n k : ℕ, ∀ d ∈ range (dyadicRoundC n),
        Tendsto (fun k' => ∫ w, avgReg (X ω) k' w ∂foldedCircle d (radius k)) atTop
          (𝓝 (X ω (foldedCircle d (radius k))))) := by
  have hBM := isBrownianReal_zRadB hX hR
  have hEae : ∀ᵐ ω ∂P, ∀ n k : ℕ, ∀ d ∈ range (dyadicRoundC n),
      Tendsto (fun k' => ∫ w, avgReg (X ω) k' w ∂foldedCircle d (radius k)) atTop
        (𝓝 (X ω (foldedCircle d (radius k)))) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    rw [ae_ball_iff (countable_range_dyadicRoundC n)]
    intro d _
    exact regAt_foldedCircle hX d (radius_pos k)
  filter_upwards [hG.ae_good, hBM.cont, WedgeInf.ae_abs_le_of_isBrownianReal hBM,
    ae_zRadB_eq hX hR hG, hEae] with ω hg hc hgr hz hE
  obtain ⟨K', hK'⟩ := hgr 1 one_pos
  refine ⟨hg, ⟨_, _, (logDom_radPsi hR hc hK').add (logDom_const_free (G ω (0, R)) R)⟩,
    fun ρ hρ hρR => ?_, hE⟩
  have ht : 0 ≤ Real.log (R / ρ) := Real.log_nonneg ((one_le_div hρ).2 hρR)
  have he : R * Real.exp (-((Real.log (R / ρ)).toNNReal : ℝ)) = ρ := by
    rw [Real.coe_toNNReal _ ht, Real.exp_neg, Real.exp_log (div_pos hR hρ)]
    field_simp
  simp only [radPsi]
  rw [hz, he, mul_inv_cancel_left₀ (by positivity)]
  ring

end Good

/-- **The identity at all folded circles of the window simultaneously.** -/
theorem ae_n2H2ReprFree_circ (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) (hX : IsFreeGFFModConstH X P)
    (c : Ω → ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ p : WinCirc K,
      evalReg (lateralPart fun μ => X ω μ - (μ Set.univ).toReal * c ω)
        ((winIdx K (Sum.inl p)).map fun z => (a : ℂ) * z) = latWinFreeW K a X ω (Sum.inl p) := by
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  have hR : 0 < a * K + 1 := by positivity
  filter_upwards [ae_free_good hX hG hR] with ω hω
  obtain ⟨hg, ⟨C, D, hψ⟩, hψg, hE⟩ := hω
  intro p
  have : IsFiniteMeasure (winIdx K (Sum.inl p)) := (isAdmissibleH_winIdx K _).1
  have hρ : 0 < p.1.2 := p.2.1
  have hdK : ‖p.1.1‖ + p.1.2 < K := p.2.2
  have haρ : 0 < a * p.1.2 := mul_pos ha hρ
  have hμ : (winIdx K (Sum.inl p)).map (fun z => (a : ℂ) * z) =
      foldedCircle ((a : ℂ) * p.1.1) (a * p.1.2) := by
    rw [winIdx_circ, fc_map_mul _ _ ha]
  have hm : ‖(a : ℂ) * p.1.1‖ + a * p.1.2 < a * K + 1 := by
    rw [F1.norm_mul_real ha]
    nlinarith [mul_pos ha (sub_pos.2 hdK)]
  refine evalReg_lat_sub_const_win (l := G ω (foldH ((a : ℂ) * p.1.1), a * p.1.2)) hg hψ hR
    hψg hE (c ω) ha hm ?_ ?_ ?_
  · rw [hμ]; exact ae_fc_supp_free _ haρ
  · rw [hμ]; exact CoordReg.integrable_log_norm_foldedCircle _ _
  · rw [hμ]
    have hp : (foldH ((a : ℂ) * p.1.1), a * p.1.2) ∈ Hbar ×ˢ Ioi (0 : ℝ) :=
      ⟨CircleFubini.foldH_mem_Hbar' _, haρ⟩
    have hT' := (hg.1.2.2.tendsto_at hp).comp RegClosure.tendsto_radius_nhdsGT
    refine hT'.congr fun k => ?_
    simp only [Function.comp_apply, fc_foldH_eq]

/-- **The identity at a fixed density of the window.** -/
theorem ae_n2H2ReprFree_dens (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) (hX : IsFreeGFFModConstH X P)
    (c : Ω → ℝ) {a : ℝ} (ha : 0 < a) (f : WinDens K) :
    ∀ᵐ ω ∂P,
      evalReg (lateralPart fun μ => X ω μ - (μ Set.univ).toReal * c ω)
        ((winIdx K (Sum.inr f)).map fun z => (a : ℂ) * z) = latWinFreeW K a X ω (Sum.inr f) := by
  obtain ⟨M, δ, hd⟩ := f.2
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  set S := Metric.closedBall (0 : ℂ) (winRad K) ∩ Hbar with hS_def
  have hcs : HasCompactSupport f.1 :=
    HasCompactSupport.intro hd.compact fun z hz => hd.supp z hz
  have hsupp : Function.support f.1 ⊆ S := fun z hz => by_contra fun h => hz (hd.supp z h)
  have hts : tsupport f.1 ⊆ QuantumZipper.H :=
    (closure_minimal hsupp hd.compact.isClosed).trans hd.subH
  have hR : 0 < a * K + 1 := by positivity
  filter_upwards [ae_free_good hX hG hR, ae_contPair_G_density hX hG hd.cont hcs hts]
    with ω hω hL
  obtain ⟨hg, ⟨C, D, hψ⟩, hψg, hE⟩ := hω
  set μ := CharFun.tdens f.1 with hμ_def
  have hμ : winIdx K (Sum.inr f) = μ := rfl
  have : IsFiniteMeasure μ := hd.admissible.1
  have hemb := F1.measurableEmbedding_mul_real ha
  have hμS : ∀ᵐ u ∂μ, u ∈ S := by
    rw [ae_iff]; simpa only [Set.compl_def] using hd.tdens_compl
  have hμS' : ∀ᵐ u ∂μ, u ≠ 0 ∧ u ∈ Hbar ∧ ‖u‖ ≤ winRad K := by
    filter_upwards [hμS] with u hu
    refine ⟨fun h0 => ?_, hu.2, by simpa using hu.1⟩
    have := hd.delta.trans (hd.sub hu)
    rw [h0, Complex.zero_im] at this
    exact lt_irrefl _ this
  have hm : a * winRad K < a * K + 1 := by
    have := winRad_lt K
    have hw : winRad K ≤ (K : ℝ) := by
      unfold winRad
      exact max_le (by linarith) (Nat.cast_nonneg K)
    nlinarith
  obtain ⟨Lg, hLg⟩ := hL a ha
  rw [hμ]
  refine evalReg_lat_sub_const_win (l := Lg) hg hψ hR hψg hE (c ω) ha hm ?_ ?_ ?_
  · rw [hemb.ae_map_iff]
    filter_upwards [hμS'] with u hu
    refine ⟨?_, mul_ne_zero (Complex.ofReal_ne_zero.2 ha.ne') hu.1, ?_⟩
    · show 0 ≤ ((a : ℂ) * u).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_nonneg ha.le hu.2.1
    · rw [F1.norm_mul_real ha]
      exact mul_le_mul_of_nonneg_left hu.2.2 ha.le
  · rw [hemb.integrable_map_iff]
    refine ((integrable_const (Real.log a)).add
      (WedgeRes.integrable_log_norm_adm hd.admissible)).congr ?_
    filter_upwards [hμS'] with u hu
    simp only [Function.comp_apply]
    rw [F1.norm_mul_real ha, Real.log_mul ha.ne' (norm_pos_iff.2 hu.1).ne']
    rfl
  · refine (hLg.comp RegClosure.tendsto_radius_nhdsGT).congr fun k => ?_
    simp only [Function.comp_apply]
    rw [hemb.integral_map]
    rfl

/-- **Per-index free-field regularization identity** (the corrected form of
`N2H2ReprFreeStmt`: the index quantifier outside the almost-sure quantifier). -/
def N2H2ReprFreeIStmt : Prop :=
  ∀ (K : ℕ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P → ∀ (c : Ω → ℝ) (a : ℝ), 0 < a →
      ∀ i : WinIdx K, ∀ᵐ ω ∂P,
        evalReg (lateralPart fun μ => X ω μ - (μ Set.univ).toReal * c ω)
          ((winIdx K i).map fun z => (a : ℂ) * z) = latWinFreeW K a X ω i

/-- **The per-index free-field regularization identity: PROVED.** -/
theorem n2H2ReprFreeIStmt_holds : N2H2ReprFreeIStmt := by
  intro K Ω _ P _ X hX c a ha i
  rcases i with p | f
  · filter_upwards [ae_n2H2ReprFree_circ K P X hX c ha] with ω h
    exact h p
  · exact ae_n2H2ReprFree_dens K P X hX c ha f

end D3Plus
end QuantumZipper
