import SmallGammaGeodesics.NIC.Increments

/-!
# NIC, part 2: `CC.NICInput` (near-identity conformal coupling, ruling G20, with G24)

Packet P-G2; design D-P2 of `planning/handoffs/P-G1.md`; GA2 D5 Steps 3–8; blueprint `lem:nic`.

**`nicInput_holds : CC.NICInput`**, with `ε₀ = 1/32` and `C = 144 · C_var`, `C_var` the constant of
the deterministic bump lemma `exists_logCov_sbump_le`. Given `Φ, Ψ, U, ε` with
`CC.IsNearIdDiffeo Φ Ψ U ε`, `0 ≤ ε ≤ 1/32`, `U` open, and `D := NearIdPair.ofDiffeo` (`δ = 2ε`):

* `Ω = ℕ → ℝ` with `stdP`, a white noise `W` (`exists_isWhiteNoise`);
* `h` := the GFF of `W`, `h̄` := the GFF of `W ∘ O`, `O = U_τ ⊕ 1` (`exists_gff_of_whiteNoise`,
  `isWhiteNoise_comp_linearIsometry`, `NearIdPair.wnIsom`);
* `K ω := harmRep (T ω)`, `T ω = (h ω ∘ τ − h̄ ω)|_U` (`NearIdPair.nicDist`), harmonic on `U` for
  every `ω` and jointly measurable (`measurable_harmRep`);
* coupling: `NearIdPair.coupling_of_isWeakHarm` on the a.s. event `NearIdPair.ae_isWeakHarm`;
* increments: `K z − K w = W((τ̃ − U_τ) J g)` a.s. (`NearIdPair.ae_harmRep_sub_eq`), so they form
  a centred Gaussian process (G24), and
  `E(K z − K w)² ≤ ‖G − 1‖² logCov g g ≤ (12ε)² · C_var · min(t, 1 + log(1 + t))`
  (`norm_gram_sub_one_le_ofDiffeo`, `exists_logCov_sbump_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric LQGMetric.GFFExist LQGMetric.WhiteNoise

/-- **NIC** (`CC.NICInput`): the near-identity conformal coupling, with `ε₀ = 1/32` and
`C = 144 · C_var`. -/
theorem nicInput_holds : CC.NICInput := by
  obtain ⟨Cv, hCv, hbound⟩ := exists_logCov_sbump_le
  refine ⟨1 / 32, 144 * Cv, by norm_num, by positivity, ?_⟩
  intro Φ Ψ U ε hU hε0 hε hΦ
  set D := NearIdPair.ofDiffeo hΦ hε0 hε with hD
  let U' : Opens ℂ := ⟨U, hU⟩
  have hΨ : DifferentiableOn ℂ D.Ψ U' := hΦ.holo_inv
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have hP := hW.isProbabilityMeasure
  obtain ⟨h, hh, hae⟩ := exists_gff_of_whiteNoise hW
  obtain ⟨hb, hhb, hbae⟩ := exists_gff_of_whiteNoise (isWhiteNoise_comp_linearIsometry hW D.wnIsom)
  have hbae' : ∀ φ : TestC, (fun ω => hb ω φ) =ᵐ[LQGDimension.ExistAsm.stdP]
      W (D.wnIsom (testL2 φ)) := hbae
  have hmeasT := D.measurable_nicDist_apply hh.measurable hhb.measurable U'
  refine ⟨ℕ → ℝ, inferInstance, LQGDimension.ExistAsm.stdP, hP, h, hb,
    fun ω => harmRep (D.nicDist U' (h ω) (hb ω)), hh, hhb, measurable_harmRep hmeasT,
    fun ω => harmonicOnNhd_harmRep _, ?_, ?_, ?_, ?_⟩
  · -- the increments form a Gaussian process (ruling G24)
    have hball : ∀ p : U × U, ∃ s : ℝ, 0 < s ∧ closedBall (p.1 : ℂ) s ⊆ U ∧
        closedBall (p.2 : ℂ) s ⊆ U := fun p => exists_closedBall_pair hU p.1.2 p.2.2
    choose s hs hs1 hs2 using hball
    refine (hW.isGaussianProcess_comp (fun p => D.incVec (hs p) p.1 p.2)).congr fun p => ?_
    exact (D.ae_harmRep_sub_eq hW (U := U') hΨ hae hbae' (hs p) (hs1 p) (hs2 p)).symm
  · -- the increments are centred
    intro p
    obtain ⟨s, hs, hs1, hs2⟩ := exists_closedBall_pair hU p.1.2 p.2.2
    rw [integral_congr_ae (D.ae_harmRep_sub_eq hW (U := U') hΨ hae hbae' hs hs1 hs2),
      QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)]
  · -- the coupling `h ∘ Φ⁻¹ = h̄ + K` on `U`
    filter_upwards [D.ae_isWeakHarm hΨ hae hbae'] with ω hT g τg hg hτ
    have hτg : τg = D.transport g := TestFunction.ext fun x => by
      rw [hτ x]
      rfl
    rw [hτg]
    exact D.coupling_of_isWeakHarm hT g hg
  · -- the increment bound
    intro z w s hs hz hw
    have h1 := D.integral_harmRep_sub_sq_le hW (U := U') hΨ hae hbae' hs hz hw
    have h2 := hbound s hs z w
    have h3 : ‖D.gram - 1‖ ≤ 12 * ε := norm_gram_sub_one_le_ofDiffeo hΦ hε0 hε
    have h0 : 0 ≤ ‖D.gram - 1‖ := (D.gram - 1).opNorm_nonneg
    have h4 : ‖D.gram - 1‖ ^ 2 ≤ 144 * ε ^ 2 := by
      have := pow_le_pow_left₀ h0 h3 2
      rw [mul_pow] at this
      linarith
    have hlc : 0 ≤ logCov (sbumpC hs z - sbumpC hs w : TestC)
        (sbumpC hs z - sbumpC hs w : TestC) := by
      have e : logCov (sbumpC hs z - sbumpC hs w : TestC) (sbumpC hs z - sbumpC hs w : TestC) =
          ‖jH (sbumpDiff hs z w)‖ ^ 2 := (norm_jH_sq (sbumpDiff hs z w)).symm
      rw [e]
      positivity
    calc ∫ ω, (harmRep (D.nicDist U' (h ω) (hb ω)) z - harmRep (D.nicDist U' (h ω) (hb ω)) w) ^ 2
          ∂LQGDimension.ExistAsm.stdP
        ≤ ‖D.gram - 1‖ ^ 2 *
          logCov (sbumpC hs z - sbumpC hs w : TestC) (sbumpC hs z - sbumpC hs w : TestC) := h1
      _ ≤ 144 * ε ^ 2 *
          logCov (sbumpC hs z - sbumpC hs w : TestC) (sbumpC hs z - sbumpC hs w : TestC) :=
        mul_le_mul_of_nonneg_right h4 hlc
      _ ≤ 144 * ε ^ 2 * (Cv * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 144 * Cv * ε ^ 2 * min (‖z - w‖ / s) (1 + Real.log (1 + ‖z - w‖ / s)) := by ring

end NIC
end SmallGammaGeodesics
