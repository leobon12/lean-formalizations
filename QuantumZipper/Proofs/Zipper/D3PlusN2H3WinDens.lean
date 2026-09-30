import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinCirc
import QuantumZipper.Proofs.Zipper.D3PlusN2ContPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2-H3': the lateral/radial splitting on the whole restricted window index (PROVED)

Task N2H3-SPLITWIN (Decision D36). The density part `WinDens K` of the restricted window index,
and with the circle part (`n2H3SplitWinCircStmt_holds`, `D3PlusN2H3WinCirc.lean`) the full node
`N2H3SplitWinStmt` (`D3PlusN2RHeart.lean`): `n2H3SplitWinStmt_holds`.

For a bounded continuous density `f` carried by a compact `K ⊆ {δ < Im}` inside the window, the
rescaled measure `ν = (f dz).map (a ·)` satisfies the hypotheses of the generic splitting
`n2Split_of_good`: its support is a compact part of `Hbar \ {0}` inside `ball 0 (r/2)`, `log‖·‖`
is bounded there, and the regularizations of the regular version converge at `ν` for every scale
`a` simultaneously (`ae_contPair_G_density`, `D3PlusN2ContPair.lean`: the circle-regularized
pairings with the dilated density converge, all scales at once). Sources as in
`D3PlusN2H3WinCirc.lean` (Duplantier–Miller–Sheffield, arXiv:1409.7055, pp. 77–78).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

open WedgeTK

/-- **N2-H3-SPLIT' on the densities of the window.** -/
def N2H3SplitWinDensStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), 0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K : ℕ, 0 < K → ∀ L, 0 < n2Lev γ α L r → ∀ f : WinDens K, ∀ᵐ ω ∂P,
      Real.log K + 1 ≤ ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω →
      Integrable (fun z => radAvgReg (locZField X r ω) (n2EmbScale γ α L r X ω * ‖z‖))
        (winIdx K (Sum.inr f)) ∧
      evalReg (n2Model γ α L r X ω)
          ((winIdx K (Sum.inr f)).map fun z => (n2EmbScale γ α L r X ω : ℂ) * z) =
        evalReg (n2LatY X r ω)
          ((winIdx K (Sum.inr f)).map fun z => (n2EmbScale γ α L r X ω : ℂ) * z) +
        ∫ z, (radAvgReg (locZField X r ω) (n2EmbScale γ α L r X ω * ‖z‖) +
          α * (-Real.log (n2EmbScale γ α L r X ω * ‖z‖)) + L / γ) ∂(winIdx K (Sum.inr f))

/-- **N2-H3-SPLIT' on the densities of the window: PROVED.** -/
theorem n2H3SplitWinDensStmt_holds : N2H3SplitWinDensStmt := by
  intro γ α r Ω _ P _ X _ _ _ hr hX K hK L _ f
  obtain ⟨M, δ, hd⟩ := f.2
  obtain ⟨G, hG⟩ := exists_isRegVersion hX
  set S := Metric.closedBall (0 : ℂ) (winRad K) ∩ Hbar with hS_def
  have hcs : HasCompactSupport f.1 :=
    HasCompactSupport.intro hd.compact fun z hz => hd.supp z hz
  have hsupp : Function.support f.1 ⊆ S := fun z hz => by_contra fun h => hz (hd.supp z h)
  have hts : tsupport f.1 ⊆ QuantumZipper.H :=
    (closure_minimal hsupp hd.compact.isClosed).trans hd.subH
  have hr₁0 : 0 < r / 2 := by positivity
  have hr₁r : r / 2 < r := by linarith
  have hBM := isBrownianReal_zRadB hX hr
  filter_upwards [hG.reg, ae_locZField_dyadic_fc hX hr hr₁0 hr₁r,
    ae_evalReg_locZField_dyadic hX hr hr₁r, hBM.cont,
    WedgeInf.ae_abs_le_of_isBrownianReal hBM, ae_contPair_G_density hX hG hd.cont hcs hts]
    with ω hF hA hE hc hgr hL
  intro hT
  obtain ⟨K', hK'⟩ := hgr 1 one_pos
  have haK := n2EmbScale_mul_lt (α := α) (L := L) (γ := γ) hr hK hT
  set a := n2EmbScale γ α L r X ω with ha_def
  have ha : 0 < a := mul_pos hr (Real.exp_pos _)
  set μ := CharFun.tdens f.1 with hμ_def
  have hμ : winIdx K (Sum.inr f) = μ := rfl
  have : IsFiniteMeasure μ := hd.admissible.1
  have hemb := F1.measurableEmbedding_mul_real ha
  set ν := μ.map fun u => (a : ℂ) * u with hν_def
  -- the support of the density
  have hμS : ∀ᵐ u ∂μ, u ∈ S := by
    rw [ae_iff]; simpa only [Set.compl_def] using hd.tdens_compl
  have hμS' : ∀ᵐ u ∂μ, u ≠ 0 ∧ u ∈ Hbar ∧ ‖u‖ ≤ winRad K := by
    filter_upwards [hμS] with u hu
    refine ⟨fun h0 => ?_, hu.2, by simpa using hu.1⟩
    have := hd.delta.trans (hd.sub hu)
    rw [h0, Complex.zero_im] at this
    exact lt_irrefl _ this
  set m := a * winRad K with hm_def
  have hm : m < r / 2 := by
    have := winRad_lt K hK
    have : a * winRad K < a * K := mul_lt_mul_of_pos_left this ha
    linarith
  have hν : ∀ᵐ w ∂ν, w ∈ Hbar ∧ w ≠ 0 ∧ ‖w‖ ≤ m := by
    rw [hν_def, hemb.ae_map_iff]
    filter_upwards [hμS'] with u hu
    refine ⟨?_, mul_ne_zero (Complex.ofReal_ne_zero.2 ha.ne') hu.1, ?_⟩
    · show 0 ≤ ((a : ℂ) * u).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_nonneg ha.le hu.2.1
    · rw [F1.norm_mul_real ha]
      exact mul_le_mul_of_nonneg_left hu.2.2 ha.le
  have hlog : Integrable (fun w => Real.log ‖w‖) ν := by
    rw [hν_def, hemb.integrable_map_iff]
    refine ((integrable_const (Real.log a)).add
      (WedgeRes.integrable_log_norm_adm hd.admissible)).congr ?_
    filter_upwards [hμS'] with u hu
    simp only [Function.comp_apply]
    rw [F1.norm_mul_real ha, Real.log_mul ha.ne' (norm_pos_iff.2 hu.1).ne']
    rfl
  -- convergence of the regularizations at `ν` (all scales at once)
  obtain ⟨Lg, hLg⟩ := hL a ha
  have hGl : Tendsto (fun k => ∫ w, G ω (w, radius k) ∂ν) atTop (𝓝 Lg) := by
    refine (hLg.comp RegClosure.tendsto_radius_nhdsGT).congr fun k => ?_
    simp only [Function.comp_apply, hν_def]
    rw [hemb.integral_map]
    rfl
  obtain ⟨hint, hsplit⟩ := n2Split_of_good (γ := γ) (α := α) (L := L) hr hF (hG.cont ω)
    (K3.continuous_harmH hX hr hr₁0 hr₁r ω) hA hE hc hK' hm hν hlog hGl
  -- back to the window measure
  have hpt : ∀ᵐ u ∂μ,
      radPsi X r ω ‖(a : ℂ) * u‖ = radAvgReg (locZField X r ω) (a * ‖u‖) := by
    filter_upwards [hμS'] with u hu
    have h1 : a * ‖u‖ ≤ m := mul_le_mul_of_nonneg_left hu.2.2 ha.le
    rw [F1.norm_mul_real ha,
      radAvgReg_eq_radPsi X hr ω (mul_pos ha (norm_pos_iff.2 hu.1)) (by linarith)]
  rw [hμ]
  refine ⟨?_, ?_⟩
  · have := hint
    rw [hν_def, hemb.integrable_map_iff] at this
    exact this.congr hpt
  · rw [hsplit, hν_def, hemb.integral_map]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hpt] with u hu
    rw [hu, F1.norm_mul_real ha]

/-- **N2-H3-SPLIT' (restricted window index, D36): PROVED.** -/
theorem n2H3SplitWinStmt_holds : N2H3SplitWinStmt := by
  intro γ α r Ω _ P _ X hγ hγ2 hα hr hX K hK L hL i
  rcases i with p | f
  · exact n2H3SplitWinCircStmt_holds γ α r P X hγ hγ2 hα hr hX K hK L hL p
  · exact n2H3SplitWinDensStmt_holds γ α r P X hγ hγ2 hα hr hX K hK L hL f

end D3Plus
end QuantumZipper
