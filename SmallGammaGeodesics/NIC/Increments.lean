import SmallGammaGeodesics.NIC.Harmonic

/-!
# NIC, part 2 (steps 8–9): the increments of `K`

Packet P-G2; design D-P2 of `planning/handoffs/P-G1.md` (steps 8–9, with the scaled radial bumps
of `NIC.Bump`), GA2 D5 Step 8, blueprint `lem:nic` Step F, ruling G24 (ii).

For `B̄(z, s), B̄(w, s) ⊆ U` and `g := ψ_{s,z} − ψ_{s,w} ∈ 𝓓₀` (`sbumpDiff`):

* `NearIdPair.ae_harmRep_sub_eq`: a.s. `K z − K w = T g = ⟨h, τ g⟩ − ⟨h̄, g⟩ = W(f)` with
  `f := (τ̃ − U_τ) J g` (`incVec`): `⟨h, τ g⟩ = W(J τ g) = W(τ̃ J g)` and
  `⟨h̄, g⟩ = W(O J g) = W(U_τ J g)` a.s., and `W` is a.s. linear;
* `NearIdPair.integral_harmRep_sub_sq_le`: `E(K z − K w)² = ‖f‖² ≤ ‖G − 1‖² logCov g g`
  (`norm_tauH_sub_polar_le`: `τ̃ − U_τ = U_τ (S − 1)` and `‖S − 1‖ ≤ ‖G − 1‖`).

Hence the increments of `K` are white-noise variables `W(f)`: jointly centred Gaussian (G24).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric LQGMetric.GFFExist LQGMetric.WhiteNoise

/-- two points of an open set have a common radius of closed balls inside it -/
lemma exists_closedBall_pair {U : Set ℂ} (hU : IsOpen U) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ U ∧ closedBall w s ⊆ U := by
  obtain ⟨a, ha, haU⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨b, hb, hbU⟩ := Metric.isOpen_iff.1 hU w hw
  have hm : 0 < min a b := lt_min ha hb
  refine ⟨min a b / 2, by positivity, (closedBall_subset_ball ?_).trans haU,
    (closedBall_subset_ball ?_).trans hbU⟩
  · linarith [min_le_left a b]
  · linarith [min_le_right a b]

/-- the mean-zero bump difference `ψ_{s,z} − ψ_{s,w} ∈ 𝓓₀` -/
def sbumpDiff {s : ℝ} (hs : 0 < s) (z w : ℂ) : testC0Sub :=
  ⟨sbumpC hs z - sbumpC hs w, by
    rw [mem_testC0Sub]
    show ∫ x, (sbump s z x - sbump s w x) = 0
    rw [integral_sub (integrable_sbump hs z) (integrable_sbump hs w), integral_sbump hs,
      integral_sbump hs, sub_self]⟩

@[simp] lemma coe_sbumpDiff {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    (sbumpDiff hs z w : TestC) = sbumpC hs z - sbumpC hs w := rfl

namespace NearIdPair

variable (D : NearIdPair)

/-- the white-noise vector of the increment: `f := (τ̃ − U_τ) J(ψ_{s,z} − ψ_{s,w})` -/
def incVec {s : ℝ} (hs : 0 < s) (z w : ℂ) : WNSpace :=
  ((D.tauH (jH (sbumpDiff hs z w)) - D.polar (jH (sbumpDiff hs z w)) : Hstar) : WNSpace)

/-- `‖f‖² ≤ ‖G − 1‖² · logCov g g` -/
lemma norm_incVec_sq_le {s : ℝ} (hs : 0 < s) (z w : ℂ) :
    ‖D.incVec hs z w‖ ^ 2 ≤ ‖D.gram - 1‖ ^ 2 *
      logCov (sbumpC hs z - sbumpC hs w : TestC) (sbumpC hs z - sbumpC hs w : TestC) := by
  have h : ‖D.incVec hs z w‖ ≤ ‖D.gram - 1‖ * ‖jH (sbumpDiff hs z w)‖ := by
    rw [incVec, Submodule.norm_coe]
    exact D.norm_tauH_sub_polar_le _
  have e : logCov (sbumpC hs z - sbumpC hs w : TestC) (sbumpC hs z - sbumpC hs w : TestC) =
      ‖jH (sbumpDiff hs z w)‖ ^ 2 := (norm_jH_sq (sbumpDiff hs z w)).symm
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
  {h hb : Ω → DistC}

/-- **Step 8: the increments of `K` are white-noise variables**: `K z − K w = W(f)` a.s. -/
theorem ae_harmRep_sub_eq (hW : IsWhiteNoise P W) {U : Opens ℂ}
    (hΨ : DifferentiableOn ℂ D.Ψ U)
    (hae : ∀ φ : TestC, (fun ω => h ω φ) =ᵐ[P] W (testL2 φ))
    (hbae : ∀ φ : TestC, (fun ω => hb ω φ) =ᵐ[P] W (D.wnIsom (testL2 φ)))
    {z w : ℂ} {s : ℝ} (hs : 0 < s) (hz : closedBall z s ⊆ U) (hw : closedBall w s ⊆ U) :
    (fun ω => harmRep (D.nicDist U (h ω) (hb ω)) z - harmRep (D.nicDist U (h ω) (hb ω)) w)
      =ᵐ[P] W (D.incVec hs z w) := by
  set g := sbumpDiff hs z w with hg
  filter_upwards [D.ae_isWeakHarm hΨ hae hbae, hae (D.transport g), hbae g,
    wn_sub_ae hW (D.tauH (jH g) : WNSpace) (D.polar (jH g) : WNSpace)] with ω hT h1 h2 h3
  rw [D.harmRep_sub_eq hT hs hz hw, ← coe_sbumpDiff hs z w, ← hg, h1, h2, ← D.coe_tauH_jH,
    D.wnIsom_testL2, incVec, ← hg, Submodule.coe_sub, h3]

/-- **Step 8: the second moment**: `E(K z − K w)² ≤ ‖G − 1‖² · logCov g g` -/
theorem integral_harmRep_sub_sq_le (hW : IsWhiteNoise P W) {U : Opens ℂ}
    (hΨ : DifferentiableOn ℂ D.Ψ U)
    (hae : ∀ φ : TestC, (fun ω => h ω φ) =ᵐ[P] W (testL2 φ))
    (hbae : ∀ φ : TestC, (fun ω => hb ω φ) =ᵐ[P] W (D.wnIsom (testL2 φ)))
    {z w : ℂ} {s : ℝ} (hs : 0 < s) (hz : closedBall z s ⊆ U) (hw : closedBall w s ⊆ U) :
    ∫ ω, (harmRep (D.nicDist U (h ω) (hb ω)) z - harmRep (D.nicDist U (h ω) (hb ω)) w) ^ 2 ∂P
      ≤ ‖D.gram - 1‖ ^ 2 *
        logCov (sbumpC hs z - sbumpC hs w : TestC) (sbumpC hs z - sbumpC hs w : TestC) := by
  have hae' : (fun ω => (harmRep (D.nicDist U (h ω) (hb ω)) z -
      harmRep (D.nicDist U (h ω) (hb ω)) w) ^ 2) =ᵐ[P] fun ω => W (D.incVec hs z w) ω ^ 2 := by
    filter_upwards [D.ae_harmRep_sub_eq hW hΨ hae hbae hs hz hw] with ω hω
    rw [hω]
  rw [integral_congr_ae hae', wn_integral_sq hW]
  exact D.norm_incVec_sq_le hs z w

end NearIdPair

end NIC
end SmallGammaGeodesics
