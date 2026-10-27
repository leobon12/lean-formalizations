import MatedCRTHarmonic.Growth.ChainRates
import MatedCRTHarmonic.CellFamily.BadEventProposition
import MatedCRTHarmonic.CellFamily.ProducersBadEventItinerary
import MatedCRTHarmonic.MesoGrid.Uniform
import MatedCRTHarmonic.MesoModel.MesoInterfaces
import MatedCRTHarmonic.MesoModel.MesoSkeleton

/-!
# Conditional mesoscopic control for the mated-CRT cell embedding

This assembles scaling, cell-count, and annular estimates into mesoscopic control. The
remaining stochastic/geometric inputs stay named interfaces in `MesoInterfaces` and
`CellFamily.Interfaces`.

The scaled-grid estimate is used in its bad-event form
(`CellFamily.cellFamily_compl_of_interfaces_bad`), so the Borel–Cantelli step needs no measurability of
the mesh events, and the output is `UnitMesoscopicOutput` (`unitMesoscopicOutput_of_interfaces`),
with no Borel premise; `cellModelExists_of_interfaces` composes it with the cell-model assembly.
-/

set_option autoImplicit false
-- The scale theorem and the full coupling specialization exceed Lean's default reduction budget.
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

private theorem cellFamilyMesh_eq_realRpow (k : ℕ) :
    CellFamily.mesh k = (2 : ℝ) ^ (-(k : ℝ)) := by
  simp [CellFamily.mesh, zpow_neg, zpow_natCast, Real.rpow_neg, Real.rpow_natCast]

private theorem cellFamilyMesh_pos (k : ℕ) : 0 < CellFamily.mesh k := by
  rw [cellFamilyMesh_eq_realRpow]
  positivity

private theorem summable_const_mul_mesh_rpow {a C : ℝ} (ha : 0 < a) :
    Summable (fun k : ℕ => C * (CellFamily.mesh k) ^ a) := by
  have hratio : 0 ≤ (2 : ℝ) ^ (-a) := by positivity
  have hratio_lt : (2 : ℝ) ^ (-a) < 1 := by
    calc
      (2 : ℝ) ^ (-a) < (2 : ℝ) ^ (0 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = 1 := by simp
  have hgeom : Summable (fun k : ℕ => ((2 : ℝ) ^ (-a)) ^ k) :=
    summable_geometric_of_lt_one hratio hratio_lt
  have hpow : ∀ k : ℕ, (CellFamily.mesh k) ^ a = ((2 : ℝ) ^ (-a)) ^ k := by
    intro k
    rw [cellFamilyMesh_eq_realRpow]
    calc
      ((2 : ℝ) ^ (-(k : ℝ))) ^ a = (2 : ℝ) ^ ((-(k : ℝ)) * a) := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ ((-a) * (k : ℝ)) := by congr 1; ring
      _ = ((2 : ℝ) ^ (-a)) ^ (k : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ((2 : ℝ) ^ (-a)) ^ k := by rw [Real.rpow_natCast]
  refine (hgeom.mul_left C).congr ?_
  intro k
  rw [hpow]

/-- the joint-scaling identity (event transfer) + the bad-event mesh scaled-grid estimate + Borel–Cantelli: almost
surely the unit-scale scaled-grid event holds for all large `k`. No measurability of the mesh
events is used: the failure bound is an outer-measure bound (the outer-measure interface). -/
private theorem unitScaledGridControl_ae_of_prop23
    {γ : ℝ} (M : MatedCRTUnitMesoModel γ)
    (h23 : MatedCRTProposition23GridScalingInput M)
    (χ β α p₀ C : ℝ) (hα : 0 < α)
    (hScaledBad : ∀ k, M.coupled.family.P
      {ω | (M.coupled.family.H k ω).ScaledGridControl 1
        (CellFamily.mesh k) χ β M.q M.ρ p₀}ᶜ ≤ ENNReal.ofReal (C * (CellFamily.mesh k) ^ α)) :
    ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop,
      (M.unitEmbedding ω).ScaledGridControl (M.radius ω k) (CellFamily.mesh k)
        χ β M.q M.ρ p₀ := by
  let BadUnit : ℕ → Set M.coupled.family.Ω := fun k =>
    {ω | ¬ (M.unitEmbedding ω).ScaledGridControl (M.radius ω k) (CellFamily.mesh k)
      χ β M.q M.ρ p₀}
  have hratio : ∀ k, M.coupled.family.P (BadUnit k) ≤
      ENNReal.ofReal (max 0 C * (CellFamily.mesh k) ^ α) := by
    intro k
    calc
      M.coupled.family.P (BadUnit k) =
          M.coupled.family.P
            {ω | ¬ (M.coupled.family.H k ω).ScaledGridControl 1
              (CellFamily.mesh k) χ β M.q M.ρ p₀} := h23 k χ β p₀
      _ ≤ ENNReal.ofReal (C * (CellFamily.mesh k) ^ α) := hScaledBad k
      _ ≤ ENNReal.ofReal (max 0 C * (CellFamily.mesh k) ^ α) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (le_max_right 0 C)
          (Real.rpow_nonneg (le_of_lt (cellFamilyMesh_pos k)) α)
  have hAvoid : ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop, ω ∉ BadUnit k := by
    apply Growth.ae_eventually_notMem_of_real_summable_bound
      M.coupled.family.P BadUnit (fun k => max 0 C * (CellFamily.mesh k) ^ α)
    · intro k
      exact mul_nonneg (le_max_left 0 C)
        (Real.rpow_nonneg (le_of_lt (cellFamilyMesh_pos k)) α)
    · exact summable_const_mul_mesh_rpow hα
    · exact hratio
  filter_upwards [hAvoid] with ω hω
  have hev : ∀ᶠ k : ℕ in atTop,
      (M.unitEmbedding ω).ScaledGridControl (M.radius ω k) (CellFamily.mesh k)
        χ β M.q M.ρ p₀ := by
    simpa [BadUnit] using hω
  filter_upwards [hev] with k hk
  simpa [BadUnit] using hk

private theorem unitVertexCount_ae_of_prop25
    {γ : ℝ} (M : MatedCRTUnitMesoModel γ)
    (h25 : MatedCRTProposition25CellCountInput M) :
    ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop,
      (verticesMeeting (M.unitEmbedding ω).cell (ball 0 (M.radius ω k))).encard ≤
        (2 : ℕ∞) ^ (2 * k) := by
  filter_upwards [h25 1 (by norm_num)] with ω hω
  filter_upwards [hω] with k hk
  let V := verticesMeeting (M.unitEmbedding ω).cell (ball 0 (M.radius ω k))
  change V.Finite ∧ (V.encard.toNat : ℝ) ≤ 2 ^ ((1 + 1) * (k : ℝ)) at hk
  have hsize : (V.encard.toNat : ℝ) ≤ (2 : ℝ) ^ (2 * (k : ℝ)) := by
    norm_num at hk ⊢
    exact hk.2
  have hnat : V.encard.toNat ≤ 2 ^ (2 * k) := by exact_mod_cast hsize
  rw [hk.1.encard_eq_coe]
  exact_mod_cast hnat

private theorem p61MesoscopicWitness
    (a ρ p χ β q : ℝ)
    (ha : 0 < a) (hρ : 0 < ρ) (hρone : ρ < 1) (hp : 0 < p)
    (hβ : 0 < β) (hβχ : β < χ) (hβq : β < q) (hβa : β < a) :
    ∃ σ ν : ℝ, 0 < σ ∧ 0 < ν ∧
      ∀ {V E : Type*} (G : LFMultigraph V E) (o : V) (H : CellularEmbedding G o)
        (R : ℕ → ℝ), (∀ k, 0 < R k) →
        Tendsto (fun k : ℕ => Real.logb 2 (R k) / k) atTop (𝓝 a) →
        (∀ᶠ k : ℕ in atTop,
          H.ScaledGridControl (R k) ((2 : ℝ) ^ (-(k : ℝ))) χ β q ρ p) →
        (∀ᶠ k : ℕ in atTop,
          (verticesMeeting H.cell (ball 0 (R k))).encard ≤ (2 : ℕ∞) ^ (2 * k)) →
        H.MesoscopicControlWith (min p (1 / 2)) σ ν := by
  exact MesoGrid.mesoscopicControlWith_of_scaledGridControl_uniform
    a ρ p χ β q ha hρ hρone hp hβ hβχ hβq hβa

private theorem matedCRTUnitRadiusExponent_pos {γ : ℝ}
    (hγ : γ ∈ Set.Ioo 0 2) : 0 < matedCRTUnitRadiusExponent γ := by
  have hsum : 0 < 2 + γ := by linarith [hγ.1]
  have hprod : 0 < (2 - γ) * (2 + γ) := mul_pos (sub_pos.mpr hγ.2) hsum
  have hidentity : (2 - γ) * (2 + γ) = 4 - γ ^ 2 := by ring
  have hsqpos : 0 < 4 - γ ^ 2 := by rw [← hidentity]; exact hprod
  have hsq : γ ^ 2 < 4 := by linarith
  have hhalf : γ ^ 2 / 2 < 2 := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith)
  exact one_div_pos.mpr (sub_pos.mpr hhalf)

private theorem matedCRT_q_lt_radiusExponent {γ q : ℝ}
    (hγ : γ ∈ Set.Ioo 0 2) (hq : q < 2 / (2 + γ) ^ 2) :
    q < matedCRTUnitRadiusExponent γ := by
  have hsum : 0 < 2 + γ := by linarith [hγ.1]
  have hden : 0 < 2 - γ ^ 2 / 2 := by
    have hpos := matedCRTUnitRadiusExponent_pos hγ
    exact (one_div_pos.mp hpos)
  have hden' : 0 < (2 + γ) ^ 2 := sq_pos_of_pos hsum
  have hfrac : 2 / (2 + γ) ^ 2 ≤ 1 / (2 - γ ^ 2 / 2) := by
    apply (div_le_div_iff₀ hden' hden).2
    calc
      2 * (2 - γ ^ 2 / 2) = 4 - γ ^ 2 := by ring
      _ ≤ 4 := by linarith [sq_nonneg γ]
      _ ≤ 4 + 4 * γ + γ ^ 2 := by
        have hγnonneg : 0 ≤ γ := hγ.1.le
        have hsqnonneg : 0 ≤ γ ^ 2 := sq_nonneg γ
        linarith
      _ = (2 + γ) ^ 2 := by ring
      _ = 1 * (2 + γ) ^ 2 := by ring
  exact lt_of_lt_of_le hq hfrac

private def UnitMesoscopicParameters {γ : ℝ}
    (M : MatedCRTUnitMesoModel γ) (χ β α p₀ C σ ν : ℝ) : Prop :=
  0 < χ ∧ 0 < β ∧ β < min χ M.q ∧ 0 < α ∧ 0 < p₀ ∧
    (∀ k, M.coupled.family.P
      {ω | (M.coupled.family.H k ω).ScaledGridControl 1 (CellFamily.mesh k)
        χ β M.q M.ρ p₀}ᶜ ≤ ENNReal.ofReal (C * (CellFamily.mesh k) ^ α)) ∧
    0 < σ ∧ 0 < ν ∧
    (∀ {V E : Type} (G : LFMultigraph V E) (o : V)
      (H : CellularEmbedding G o) (R : ℕ → ℝ), (∀ k, 0 < R k) →
      Tendsto (fun k : ℕ => Real.logb 2 (R k) / k) atTop
        (𝓝 (matedCRTUnitRadiusExponent γ)) →
      (∀ᶠ k : ℕ in atTop,
        H.ScaledGridControl (R k) ((2 : ℝ) ^ (-(k : ℝ))) χ β M.q M.ρ p₀) →
      (∀ᶠ k : ℕ in atTop,
        (verticesMeeting H.cell (ball 0 (R k))).encard ≤ (2 : ℕ∞) ^ (2 * k)) →
      H.MesoscopicControlWith (min p₀ (1 / 2)) σ ν)

/-- The bad-event mesh scaled-grid estimate on the model's family, from the corrected interface bundle
: the corrected waypoint input through `itineraryEstimateBad_of_lemma38Bad_fixed2`, whose two
graph premises are produced (connectivity from the frozen mated-CRT anchor's provider, looplessness
from the multigraph identity), then `cellFamily_compl_of_interfaces_bad`. No measurability. -/
theorem cellFamilyCompl_of_interfaces {γ : ℝ} (M : MatedCRTUnitMesoModel γ)
    (h26 : MatedCRTCellFamilyInterfaces M) :
    ∃ χ β α p₀ C : ℝ, 0 < χ ∧ 0 < β ∧ β < min χ M.q ∧ 0 < α ∧ 0 < p₀ ∧
      ∀ k, M.coupled.family.P
        {ω | (M.coupled.family.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β M.q M.ρ p₀}ᶜ ≤
          ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  rcases h26 with ⟨h27, h38, hWaypoint, hPeanosphereG0⟩
  have hConnected : CellFamily.GraphConnected M.coupled.family :=
    CellFamily.graphConnected_ofCellCoupling M.coupled.toCellCoupledRandomFamily
  have hLoopless : CellFamily.GraphLoopless M.coupled.family := M.coupled.ae_loopless
  have hSeparation :=
    CellFamily.templateSeparation_of_peanosphereG0 M.coupled.family hPeanosphereG0
  have hItinerary := CellFamily.itineraryEstimateBad_of_lemma38Bad_fixed2
    M.coupled.family M.q M.ρ h27 h38 hConnected hLoopless M.hq.1 hWaypoint
  exact CellFamily.cellFamily_compl_of_interfaces_bad M.coupled.family γ M.ρ M.q M.hγ M.hρ M.hq
    h27 hItinerary (CellFamily.finiteGridCount_holds M.ρ) hConnected hSeparation

private theorem unitMesoscopicWitness_of_interfaces
    {γ : ℝ} (M : MatedCRTUnitMesoModel γ)
    (h26 : MatedCRTCellFamilyInterfaces M) :
    ∃ χ β α p₀ C σ ν, UnitMesoscopicParameters M χ β α p₀ C σ ν := by
  obtain ⟨χ, β, α, p₀, C, hχ, hβ, hβmin, hα, hp₀, hScaled⟩ :=
    cellFamilyCompl_of_interfaces M h26
  have ha : 0 < matedCRTUnitRadiusExponent γ := matedCRTUnitRadiusExponent_pos M.hγ
  have hq_lt_a : M.q < matedCRTUnitRadiusExponent γ :=
    matedCRT_q_lt_radiusExponent M.hγ M.hq.2
  have hβχ : β < χ := lt_of_lt_of_le hβmin (min_le_left χ M.q)
  have hβq : β < M.q := lt_of_lt_of_le hβmin (min_le_right χ M.q)
  have hβa : β < matedCRTUnitRadiusExponent γ := lt_trans hβq hq_lt_a
  obtain ⟨σ, ν, hσ, hν, hCore⟩ :=
    p61MesoscopicWitness (matedCRTUnitRadiusExponent γ) M.ρ p₀ χ β M.q ha
      M.hρ.1 M.hρ.2 hp₀ hβ hβχ hβq hβa
  exact ⟨χ, β, α, p₀, C, σ, ν,
    hχ, hβ, hβmin, hα, hp₀, hScaled, hσ, hν, hCore⟩

private theorem unitEmbeddingMeso_ae_of_witness
    {γ : ℝ} (M : MatedCRTUnitMesoModel γ)
    (χ β α p₀ C σ ν : ℝ)
    (hW : UnitMesoscopicParameters M χ β α p₀ C σ ν)
    (h23 : MatedCRTProposition23GridScalingInput M)
    (h24 : MatedCRTProposition24RadiusInput M)
    (h25 : MatedCRTProposition25CellCountInput M) :
    ∀ᵐ ω ∂M.coupled.family.P,
      (M.unitEmbedding ω).MesoscopicControlWith (min p₀ (1 / 2)) σ ν := by
  rcases hW with ⟨_hχ, _hβ, _hβmin, hα, _hp₀, hScaled, _hσ, _hν, hCore⟩
  have hEventuallyScaled := unitScaledGridControl_ae_of_prop23 M h23
    χ β α p₀ C hα hScaled
  have hEventuallyScaled' : ∀ᵐ ω ∂M.coupled.family.P, ∀ᶠ k : ℕ in atTop,
      (M.unitEmbedding ω).ScaledGridControl (M.radius ω k)
        ((2 : ℝ) ^ (-(k : ℝ))) χ β M.q M.ρ p₀ := by
    filter_upwards [hEventuallyScaled] with ω hω
    filter_upwards [hω] with k hk
    simpa [cellFamilyMesh_eq_realRpow] using hk
  have hCount := unitVertexCount_ae_of_prop25 M h25
  filter_upwards [h24, hCount, hEventuallyScaled'] with ω h24ω hCountω hScaledω
  exact hCore
    (G := MatedCRT.graph 1 (M.coupled.bm ω) (M.unitLocallyFinite ω)) (o := 0)
    (H := M.unitEmbedding ω) (M.radius ω) (M.radius_pos ω) h24ω hScaledω hCountω

/-- **Mesoscopic output for the cell-model assembly:** scaling, cell-count, and annular estimates
give mesoscopic control for the model's own unit-mesh embedding with deterministic constants.
The scaled-grid bound is exported by `CellFamily.cellFamily_compl_of_interfaces_bad`; the
Borel–Cantelli and deterministic scale conversion use `Growth.ae_eventually_notMem_of_real_summable_bound`
and `MesoGrid.mesoscopicControlWith_of_scaledGridControl_uniform`. No Borel premise. -/
theorem unitMesoscopicOutput_of_interfaces
    {γ : ℝ} (M : MatedCRTUnitMesoModel γ)
    (h23 : MatedCRTProposition23GridScalingInput M)
    (h24 : MatedCRTProposition24RadiusInput M)
    (h25 : MatedCRTProposition25CellCountInput M)
    (h26 : MatedCRTCellFamilyInterfaces M) :
    UnitMesoscopicOutput M := by
  rcases unitMesoscopicWitness_of_interfaces M h26 with
    ⟨χ, β, α, p₀, C, σ, ν, hW⟩
  exact ⟨min p₀ (1 / 2), σ, ν,
    unitEmbeddingMeso_ae_of_witness M χ β α p₀ C σ ν hW h23 h24 h25⟩

end MatedCRTHarmonic.MesoModel
