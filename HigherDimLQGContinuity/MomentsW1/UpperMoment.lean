import HigherDimLQGContinuity.MomentsW1.MomentGrowth

/-! Appendix A, confined upper chaining with a measurable moment envelope. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set Metric HigherDimLFPP HigherDimLQGMetric.DGZ
open scoped ENNReal

theorem wnUpperMoment {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) (hE : UExpRate d κ)
    (h52 : UCor52Shape d κ) (hQ : UQuantCompShape d κ)
    (_hN : UNondegShape d κ) : WNUpperMomentShape d κ := by
  intro b μ hb hμ hμ1 σ hσ hσμ p hp hbudget
  obtain ⟨ρ,hρ0,hρ,q,q',hq0,hqq',hq'1,hεθ⟩ := wnQuantile_choice hκ
  obtain ⟨CN,hCN,hcost⟩ := wnNormalized_costs hE h52 hQ hb hμ hσμ hq0 hqq' hq'1
  obtain ⟨K,hK,hpoint⟩ := wnPointwise_constant hd hμ1 hσ hσμ
  let Q : ℝ := Real.sqrt (2*d)+(μ-σ)/(2*b)
  have hQcrit : Real.sqrt (2*d) < Q := by
    dsimp [Q]
    have hdiv : 0 < (μ-σ)/(2*b) := div_pos (by linarith) (by positivity)
    linarith
  have hl : 0 < 2*p*b := by positivity
  have hlcrit : 2*p*b ≤ Real.sqrt (2*d)/4 := by linarith
  obtain ⟨CZ,hCZ,hjoint⟩ := wnZR_joint hd hκ hl hlcrit
  obtain ⟨Cz,hCz,hjoint'⟩ := hjoint Q hQcrit
  have hlM : 0 < 8*p*Real.log 2 := by positivity
  obtain ⟨CM,hCM,hMmoment⟩ := wnBadScale_expMoment hκ hρ hlM
  let D : ℝ := max 1 (K*CN)
  let A₀ : ℝ := Real.sqrt (2*d)*CZ
  let A : ℝ := A₀+d
  let C : ℝ := Real.exp (p*Real.log D+A₀*Real.log 2)*(Cz+CM)
  have hD : 1 ≤ D := le_max_left _ _
  have hDpos : 0 < D := by linarith
  have hDkn : K*CN ≤ D := le_max_right _ _
  refine ⟨C,A,?_⟩
  intro ξ hξ Ω _ P W H hH n R hR
  letI : IsProbabilityMeasure P := hH.whiteNoise.isProbabilityMeasure
  let Hr : Ω → ℝ := wnEnvelope (d := d) (P := P) b R Q CZ D H ξ q n
  have hHrmeas : Measurable Hr := measurable_wnEnvelope hH b R Q CZ D ξ q n
  have hHrge : ∀ ω, 1 ≤ Hr ω :=
    fun ω => wnEnvelope_ge_one hb.le hR hCZ.le hD H ξ q n ω
  obtain ⟨hfinite,hmZ⟩ := hjoint' hH R hR
  have hM : ∫⁻ ω, ENNReal.ofReal
      (Real.exp ((8*p*Real.log 2)*(wnBadScale P H ξ R q n ω:ℝ))) ∂P ≤
      ENNReal.ofReal (CM*(1+R)^d) := by
    exact hMmoment Ω P W H hH ξ R hR q hq0 (lt_trans hqq' hq'1)
      n _ (L33.theta_le_one d) hεθ (L33.three_pow_mul_theta_le d)
  have hZmeas : Measurable (fun ω => p*b*wnZR (d := d) R Q CZ H ω) :=
    measurable_const.mul (measurable_wnZR_of_realization hH R Q CZ)
  have hMmeas : Measurable (fun ω => 4*p*Real.log 2*
      (wnBadScale P H ξ R q n ω:ℝ)) :=
    measurable_const.mul ((MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
      (measurable_wnBadScale hH ξ R q n))
  have hZ : ∫⁻ ω, ENNReal.ofReal
      (Real.exp (2*(p*b*wnZR (d := d) R Q CZ H ω))) ∂P ≤ ENNReal.ofReal Cz := by
    convert hmZ using 1
    congr 1
    funext ω
    congr 1
    ring_nf
  have hM' : ∫⁻ ω, ENNReal.ofReal
      (Real.exp (2*(4*p*Real.log 2*(wnBadScale P H ξ R q n ω:ℝ)))) ∂P ≤
      ENNReal.ofReal (CM*(1+R)^d) := by
    convert hM using 1
    congr 1
    funext ω
    congr 1
    ring_nf
  have hCMR : 0 ≤ CM*(1+R)^d := by positivity
  have hmixed := wnExp_sum_moment P hZmeas hMmeas hCz.le hCMR hZ hM'
    (p*(Real.log D+b*CZ*Real.log (2+R)))
  have hmoment : ∫⁻ ω, ENNReal.ofReal (Hr ω ^ p) ∂P ≤
      ENNReal.ofReal (C*(1+R)^A) := by
    have hidentity : (fun ω => ENNReal.ofReal (Hr ω ^ p)) =
        (fun ω => ENNReal.ofReal (Real.exp
          (p*(Real.log D+b*CZ*Real.log (2+R))+
            p*b*wnZR (d := d) R Q CZ H ω+
            4*p*Real.log 2*(wnBadScale P H ξ R q n ω:ℝ)))) := by
      funext ω
      exact congrArg ENNReal.ofReal (wnEnvelope_power b R Q CZ D H ξ q n p ω)
    rw [hidentity]
    exact hmixed.trans (ENNReal.ofReal_le_ofReal
      (wnMoment_growth hb hp hCZ hR hCz.le hCM.le hbudget))
  refine ⟨Hr,hHrmeas,hHrge,hmoment,?_⟩
  filter_upwards [hfinite] with ω hω
  intro z hz s hs x hx y hy
  obtain ⟨hcost',hterminal⟩ := hcost ξ hξ Ω P W H hH n R CZ hR hCZ.le ω
  have hξ0 : 0 ≤ ξ := hξ.base.xi_pos.le
  have hbound := hpoint hH hξ0 hR hCN.le hq0 (lt_trans hqq' hq'1) hω
    hcost' hterminal z hz s hs x hx y hy
  have hF : 0 < wnCoarseFactor (d := d) b R Q CZ H ω :=
    wnCoarseFactor_pos b R Q CZ H ω
  have ha : 0 < aQ P H ξ n 2⁻¹ := tight_aQ_pos (by omega : 0 < d)
    hH ξ n (by norm_num) (by norm_num)
  have hs0 : 0 ≤ s^σ := Real.rpow_nonneg hs.1.le _
  let T : ℝ := ((2:ℝ)^(wnBadScale P H ξ R q n ω))^4
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hfactor : 0 ≤ wnCoarseFactor (d := d) b R Q CZ H ω *
      aQ P H ξ n 2⁻¹ * T * s^σ := by positivity
  have hKCN : (K*CN)*(wnCoarseFactor (d := d) b R Q CZ H ω *
      aQ P H ξ n 2⁻¹ * T * s^σ) ≤
      D*(wnCoarseFactor (d := d) b R Q CZ H ω *
        aQ P H ξ n 2⁻¹ * T * s^σ) :=
    mul_le_mul_of_nonneg_right hDkn hfactor
  calc
    lfppDistOn ξ (fun w => H n w ω) (ball z (3/2*s)) x y ≤
        K*(CN*wnCoarseFactor (d := d) b R Q CZ H ω*aQ P H ξ n 2⁻¹)*T*s^σ :=
      hbound
    _ = (K*CN)*(wnCoarseFactor (d := d) b R Q CZ H ω*
        aQ P H ξ n 2⁻¹*T*s^σ) := by ring
    _ ≤ D*(wnCoarseFactor (d := d) b R Q CZ H ω*
        aQ P H ξ n 2⁻¹*T*s^σ) := hKCN
    _ = Hr ω*s^σ*aQ P H ξ n 2⁻¹ := by
      rw [show Hr ω = D*wnCoarseFactor (d := d) b R Q CZ H ω*T from
        wnEnvelope_factor b R Q CZ D hDpos H ξ q n ω]
      ring

end HigherDimLQGContinuity
