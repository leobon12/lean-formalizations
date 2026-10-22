import HigherDimLQGContinuity.ForcingCount.PathGeom

/-!
# Standing hypotheses of the count and the constant arithmetic

Packet Q9. `CountHyp` bundles the hypotheses of Part B `b:lem-lowmult` and `b:lem-upcount` (the site-certificate
contract of the label catalogue, the parameters, the bump height `M_ξ = ξ⁻¹ log θ⁻¹`, the trigger threshold
`btrig = aout/32`, the Weyl allowance `|η - ξ| M_ξ ≤ v/100` and the validity of the catalogue). The arithmetic of the
(F2) constants (`aout`, `btrig`, `ε₀`) and of `a₀ = Hlo⁻¹ - 3ε₀` follows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- The standing hypotheses of the lower multiplicity and of the upper count. -/
structure CountHyp (K : CountData d) (𝔆 : Catalogue d)
    (Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ) : Prop where
  contract : SiteContract K.cat Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt
  ξ_pos : 0 < K.ξ
  η_pos : 0 < K.η
  M_eq : K.M = K.ξ⁻¹ * Real.log θ⁻¹
  btrig_eq : K.btrig = siteBtrig mc Hlo
  Hlo_ge : 1 ≤ Hlo
  mc_pos : 0 < mc
  A0_ge : Hlo⁻¹ ≤ A0
  d₀_pos : 0 < d₀
  v_pos : 0 < v
  v_le : v ≤ 1 / 100
  mismatch : |K.η - K.ξ| * K.M ≤ v / 100
  valid : 𝔆.Valid K.x K.y

/-- The saving per unit of a site, `a₀ = Hlo⁻¹ - 3ε₀`. -/
def q9SiteA0 (mc Hlo : ℝ) : ℝ := Hlo⁻¹ - 3 * siteEps0 mc Hlo

/-- The (F2) arithmetic. -/
theorem q9_siteF2 {mc Hlo : ℝ} (hmc : 0 < mc) (hHlo : 1 ≤ Hlo) :
    0 < siteEps0 mc Hlo ∧ 3 * siteEps0 mc Hlo < 2 * siteAout mc Hlo ∧
      7 * siteEps0 mc Hlo < siteBtrig mc Hlo ∧ 32 * siteBtrig mc Hlo ≤ q9SiteA0 mc Hlo ∧
      0 < siteBtrig mc Hlo ∧ 2 * siteBtrig mc Hlo < q9SiteA0 mc Hlo / 2 ∧ 0 < q9SiteA0 mc Hlo ∧
      q9SiteA0 mc Hlo ≤ Hlo⁻¹ := by
  have hH : 0 < Hlo⁻¹ := inv_pos.2 (by linarith)
  have hm : 0 < min mc Hlo⁻¹ := lt_min hmc hH
  have hmle : min mc Hlo⁻¹ ≤ Hlo⁻¹ := min_le_right _ _
  simp only [q9SiteA0, siteEps0, siteBtrig, siteAout]
  refine ⟨by positivity, by linarith, by linarith, by linarith, by positivity, by linarith, by linarith,
    by linarith [show 0 < min mc Hlo⁻¹ / 2 / 32 / 8 by positivity]⟩

namespace CountHyp

variable {K : CountData d} {𝔆 : Catalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}

theorem s_pos (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) : 0 < 𝔆.s :=
  hK.valid.1

theorem θ_pos (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) : 0 < θ :=
  (Real.exp_pos _).trans_le hK.contract.θ_lower

theorem log_θ_inv_pos (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) :
    0 < Real.log θ⁻¹ := by
  apply Real.log_pos
  rw [one_lt_inv₀ hK.θ_pos]
  exact hK.contract.θ_lt_one

theorem M_pos (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) : 0 < K.M := by
  rw [hK.M_eq]
  exact mul_pos (inv_pos.2 hK.ξ_pos) hK.log_θ_inv_pos

theorem prof_nonneg (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    (ℓ : K.cat.Label) (x : Rd d) : 0 ≤ K.cat.prof ℓ x :=
  ((hK.contract.prof ℓ).1 x).1

theorem prof_tsupport (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    (ℓ : K.cat.Label) : tsupport (K.cat.prof ℓ) ⊆ siteC d :=
  (hK.contract.prof ℓ).2.1.trans interior_subset

theorem btrig_pos (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) : 0 < K.btrig := by
  rw [hK.btrig_eq]
  exact (q9_siteF2 hK.mc_pos hK.Hlo_ge).2.2.2.2.1

theorem a0_pos (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) :
    0 < q9SiteA0 mc Hlo :=
  (q9_siteF2 hK.mc_pos hK.Hlo_ge).2.2.2.2.2.2.1

theorem A0_pos (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) : 0 < A0 :=
  (inv_pos.2 (by linarith [hK.Hlo_ge])).trans_le hK.A0_ge

theorem a0_le_A0 (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt) :
    q9SiteA0 mc Hlo ≤ A0 :=
  (q9_siteF2 hK.mc_pos hK.Hlo_ge).2.2.2.2.2.2.2.trans hK.A0_ge

/-- The certificate function of a label is the scaled profile `M • ψ_ℓ`. -/
theorem cert_fun (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    (ℓ : K.cat.Label) {D E : ContMetric d} (hD : D.IsLength) (hsrc : K.cat.Source ℓ D E) :
    Nonempty (ForcingCert D E (K.M • K.cat.prof ℓ) K.ξ K.M θ ς δsep (siteEps0 mc Hlo) εnet εatt
      (siteAout mc Hlo) Hlo b v d₀) := by
  rw [hK.M_eq]
  exact hK.contract.cert K.ξ hK.ξ_pos ℓ D E hD hsrc

end CountHyp

end HigherDimLQGContinuity
