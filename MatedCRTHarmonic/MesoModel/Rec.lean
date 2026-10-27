import MatedCRTHarmonic.GMS3.Theorem14
import MatedCRTHarmonic.CellFamily.Interfaces
import MatedCRTHarmonic.MesoModel.TransferScaling
import MatedCRTHarmonic.MesoModel.AssemblyInterfaces
import MatedCRTHarmonic.MesoModel.CloseCellModel

/-!
# The recurrence producer for the mated-CRT cell model

This is the scale-free route (the scale-free argument). A high-probability application of G3's one-scale
Theorem 1.4 estimate on `graph (2⁻ᵏ) bm`, followed by Brownian scaling, supplies arbitrarily small
effective conductances for the unit graph. G3's energy criterion then gives recurrence. Proposition
2.4 and the random radii `R_{2^k}` are not used on this route.

The producer input below records an outer-measure bound on failure of the polynomially likely G3
event (Lemma 2.7 and Proposition 2.10) at each dyadic mesh. The scale map is a measurable
equivalence, so its measure-map formula applies to arbitrary sets and no event measurability is
needed.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-- The event that the mesh-`ε` mated-CRT graph admits a cellular embedding satisfying the exact
inputs of G3's Theorem 1.4. Its probabilistic producer is the combination of GMSLemma27's Lemma 2.7
bound and GMS4's Proposition 2.10 bounds, transported by the cell-model graph/cell adapter. -/
def matedCRTTheorem14MeshGood (ε ρ ρ₁ q β β' α A : ℝ)
    (ω : MatedCRT.Path2) : Prop :=
  ∃ h : MatedCRT.IsLocallyFinite ε ω,
    ∃ H : CellularEmbedding (MatedCRT.graph ε ω h) 0,
      GMS3.Theorem14Inputs H ε ρ ρ₁ q β β' α A

/-- The one-scale probabilistic output required from Lemma 2.7 and Proposition 2.10: for every
correlated Brownian law, the outer measure of failure of the joint G3 event on
`graph (2⁻ᵏ) bm` is polynomially small. -/
def MatedCRTRecurrencePathScaleInput (γ : ℝ) : Prop :=
  ∀ (μ : Measure MatedCRT.Path2), MatedCRT.IsCorrelatedBM2 γ μ →
    ∃ ρ ρ₁ q β β' α A C : ℝ,
      0 < ρ ∧ ρ < ρ₁ ∧ 0 < β ∧ 3 * β < q ∧ 2 * β < β' ∧ β' ≤ q ∧
        2 * β < α ∧ 0 ≤ A ∧ 0 ≤ C ∧
        ∀ k : ℕ,
          μ {ω | ¬ matedCRTTheorem14MeshGood (CellFamily.mesh k)
            ρ ρ₁ q β β' α A ω} ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α)

/-- The event that the unit-mesh graph has a finite vertex set around the root with effective
conductance at most `1/(n+1)`. The predicate is independent of the local-finiteness proof by proof
irrelevance. -/
def MatedCRTResistanceLevelSet (n : ℕ) : Set MatedCRT.Path2 :=
  {ω | ∃ h : MatedCRT.IsLocallyFinite 1 ω, ∃ U : Finset ℤ,
    (0 : ℤ) ∈ U ∧
      GMS3.effCond (MatedCRT.graph 1 ω h) 0 U ≤ 1 / ((n : ℝ) + 1)}

private theorem matedCRT_mesh_eq_inv_pow (k : ℕ) :
    CellFamily.mesh k = ((2 : ℝ) ^ k)⁻¹ := by
  simp [CellFamily.mesh, zpow_neg, zpow_natCast]

private theorem matedCRT_mesh_pos (k : ℕ) : 0 < CellFamily.mesh k := by
  unfold CellFamily.mesh
  positivity

private theorem matedCRT_mesh_tendsto_zero :
    Tendsto CellFamily.mesh atTop (𝓝 0) := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  rw [show CellFamily.mesh = fun k : ℕ => ((2 : ℝ) ^ k)⁻¹ from by
    funext k; exact matedCRT_mesh_eq_inv_pow k]
  exact tendsto_inv_atTop_zero.comp hp

/-- The Brownian mesh-rescaling map is a measurable equivalence. Its map formula therefore
preserves outer measures of arbitrary path events, with no measurability hypothesis on the event.
-/
private def unitRescalePathMeasurableEquiv (ε : ℝ) (hε : 0 < ε) :
    MatedCRT.Path2 ≃ᵐ MatedCRT.Path2 where
  toEquiv :=
    { toFun := unitRescalePath ε
      invFun := unitRescalePath ε⁻¹
      left_inv := by
        intro ω
        have hsqrt : Real.sqrt ε ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hε)
        ext t <;> simp [unitRescalePath, Real.sqrt_inv, hε.ne', mul_assoc, smul_smul]
          <;> field_simp [hsqrt]
      right_inv := by
        intro ω
        have hsqrt : Real.sqrt ε ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hε)
        ext t <;> simp [unitRescalePath, Real.sqrt_inv, hε.ne', mul_assoc, smul_smul]
          <;> field_simp [hsqrt] }
  measurable_toFun := measurable_unitRescalePath ε
  measurable_invFun := measurable_unitRescalePath ε⁻¹

/-- A good one-scale G3 input gives a small effective conductance for the corresponding finite
cell region. This is the conductance form of the one-scale Green lower bound in G3's Theorem 1.4. -/
private theorem matedCRT_theorem14_effCond_le
    {ε ρ ρ₁ q β β' α A : ℝ} {ω : MatedCRT.Path2}
    (hε : 0 < ε) (hρ : 0 < ρ) (hβ'q : β' ≤ q) (hA : 0 ≤ A)
    (hside : ε < 1 ∧ ε ^ β < ρ ∧ 6 * ε ^ q ≤ ε ^ β ∧
      ε ^ q < ρ - ε ^ β ∧ ρ + ε ^ q < ρ₁)
    (hgood : matedCRTTheorem14MeshGood ε ρ ρ₁ q β β' α A ω) :
    ∃ h : MatedCRT.IsLocallyFinite ε ω, ∃ U : Finset ℤ,
      (0 : ℤ) ∈ U ∧
      GMS3.effCond (MatedCRT.graph ε ω h) 0 U ≤
        GMS3.lemma34Bound (ε ^ β) ρ (ε ^ q) (ε ^ β') A (ε ^ α) := by
  rcases hgood with ⟨h, H, hinputs⟩
  rcases hinputs with ⟨h27, hF, h1, hg⟩
  let G := MatedCRT.graph ε ω h
  have hconn : G.adj.Connected := GMS3.matedCRT_connected ε ω h
  have hs : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hδ0 : 0 ≤ ε ^ q := (Real.rpow_pos_of_pos hε q).le
  have hw : 0 < ε ^ β' := Real.rpow_pos_of_pos hε β'
  have hδw : ε ^ q ≤ ε ^ β' :=
    Real.rpow_le_rpow_of_exponent_ge hε hside.1.le hβ'q
  have hη0 : 0 ≤ ε ^ α := (Real.rpow_pos_of_pos hε α).le
  obtain ⟨g, hgo, hg0, hgE⟩ := GMS3.lemma34 H hs hside.2.1 hδ0 hside.2.2.1
    hside.2.2.2.1 hside.2.2.2.2 hw
    hδw hA hη0 h27 hF h1 hg
  have hroot : (0 : ℤ) ∈ GMS3.vFin H (ball (0 : ℂ) ρ) :=
    (GMS3.mem_vFin H isBounded_ball).mpr ⟨0, H.zero_mem_root, mem_ball_self hρ⟩
  refine ⟨h, GMS3.vFin H (ball (0 : ℂ) ρ), hroot, ?_⟩
  calc
    GMS3.effCond G 0 (GMS3.vFin H (ball (0 : ℂ) ρ)) ≤
        GMS3.energy G (GMS3.nbhd G (GMS3.vFin H (ball (0 : ℂ) ρ))) g :=
      GMS3.effCond_le_energy G hconn hroot hgo hg0
    _ ≤ GMS3.lemma34Bound (ε ^ β) ρ (ε ^ q) (ε ^ β') A (ε ^ α) := hgE

universe u

private theorem matedCRT_effCond_castGraph
    {E F : Type u} {hEF : E = F} {G : LFMultigraph ℤ E} {G' : LFMultigraph ℤ F}
    (hG : cast (congrArg (LFMultigraph ℤ) hEF) G = G')
    (a : ℤ) (U : Finset ℤ) :
    GMS3.effCond G a U = GMS3.effCond G' a U := by
  cases hEF
  change G = G' at hG
  subst G'
  rfl

private theorem matedCRT_mesh_good_gives_unit_resistance_level
    {ε ρ ρ₁ q β β' α A : ℝ} {ω : MatedCRT.Path2} {n : ℕ}
    (hε : 0 < ε) (hρ : 0 < ρ) (hβ'q : β' ≤ q) (hA : 0 ≤ A)
    (hside : ε < 1 ∧ ε ^ β < ρ ∧ 6 * ε ^ q ≤ ε ^ β ∧
      ε ^ q < ρ - ε ^ β ∧ ρ + ε ^ q < ρ₁)
    (hbound : GMS3.lemma34Bound (ε ^ β) ρ (ε ^ q) (ε ^ β') A (ε ^ α) ≤
      1 / ((n : ℝ) + 1))
    (hgood : matedCRTTheorem14MeshGood ε ρ ρ₁ q β β' α A ω) :
    unitRescalePath ε ω ∈ MatedCRTResistanceLevelSet n := by
  obtain ⟨hεlf, U, hU, hcond⟩ :=
    matedCRT_theorem14_effCond_le hε hρ hβ'q hA hside hgood
  have h1lf : MatedCRT.IsLocallyFinite 1 (unitRescalePath ε ω) :=
    (isLocallyFinite_unitRescalePath_iff hε ω).mp hεlf
  have hgraph := graphCast_eq_unitRescalePath hε ω hεlf h1lf
  have htype := edgeTypeEq_unitRescalePath hε ω
  have heff := matedCRT_effCond_castGraph (hEF := htype) hgraph 0 U
  have hcond' :
      GMS3.effCond (MatedCRT.graph 1 (unitRescalePath ε ω) h1lf) 0 U ≤
        1 / ((n : ℝ) + 1) := by
    rw [← heff]
    exact hcond.trans hbound
  exact ⟨h1lf, U, hU, hcond'⟩

/-- Given the exact per-mesh G3 event bound from Lemma 2.7/Proposition 2.10 and the one missing
measurability adapter, the unit-mesh mated-CRT graph is recurrent almost surely. Brownian scaling
makes each fixed conductance level a probability-one event; G3's energy criterion then gives
recurrence. -/
theorem matedCRTRecurrenceInput_of_theorem14ScaleInput
    {γ : ℝ} (hin : MatedCRTRecurrencePathScaleInput γ) : MatedCRTRecurrenceInput γ := by
  intro ε hε μ hμ
  let _ : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  rcases hin μ hμ with ⟨ρ, ρ₁, q, β, β', α, A, C, hρ, hρ₁, hβ, hq, hβ', hβ'q,
    hα, hA, hC, hmesh⟩
  have hlocal : ∀ᵐ ω ∂μ, MatedCRT.IsLocallyFinite 1 ω :=
    MatedCRTHarmonic.ae_isLocallyFinite_holds γ μ hμ 1 one_pos
  have hscaledLaw (δ : ℝ) (hδ : 0 < δ) :
      μ.map (unitRescalePath δ) = μ := by
    have hs := isCorrelatedBM2_map_unitRescalePath hδ hμ
    exact MatedCRTHarmonic.isCorrelatedBM2_unique_holds γ _ _ hs hμ
  have hmeshPos : ∀ k, 0 < CellFamily.mesh k := matedCRT_mesh_pos
  have hmesh0 : Tendsto CellFamily.mesh atTop (𝓝 0) := matedCRT_mesh_tendsto_zero
  have hB : Tendsto (fun k : ℕ =>
      GMS3.lemma34Bound (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ q)
        (CellFamily.mesh k ^ β') A (CellFamily.mesh k ^ α)) atTop (𝓝 0) :=
    GMS3.tendsto_lemma34Bound hmeshPos hmesh0 hρ hβ hq hβ' hα
  have herrorReal : Tendsto (fun k : ℕ => C * CellFamily.mesh k ^ α) atTop (𝓝 0) := by
    have hαpos : 0 < α := by linarith
    simpa using (GMS3.tendsto_rpow_of_tendsto_zero hmesh0 hαpos).const_mul C
  have herror : Tendsto (fun k : ℕ => ENNReal.ofReal (C * CellFamily.mesh k ^ α))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal herrorReal
  have hside : ∀ᶠ k : ℕ in atTop,
      CellFamily.mesh k < 1 ∧ CellFamily.mesh k ^ β < ρ ∧
        6 * CellFamily.mesh k ^ q ≤ CellFamily.mesh k ^ β ∧
        CellFamily.mesh k ^ q < ρ - CellFamily.mesh k ^ β ∧
        ρ + CellFamily.mesh k ^ q < ρ₁ := by
    have hratio := GMS3.tendsto_rpow_div_pow hmeshPos hmesh0
      (a := q) (b := β) (n := 1) (by push_cast; linarith)
    filter_upwards [hmesh0.eventually (gt_mem_nhds one_pos),
      (GMS3.tendsto_rpow_of_tendsto_zero hmesh0 hβ).eventually
        (gt_mem_nhds (by linarith : (0 : ℝ) < ρ / 2)),
      (GMS3.tendsto_rpow_of_tendsto_zero hmesh0 (by linarith : 0 < q)).eventually
        (gt_mem_nhds (by linarith : (0 : ℝ) < ρ / 2)),
      (GMS3.tendsto_rpow_of_tendsto_zero hmesh0 (by linarith : 0 < q)).eventually
        (gt_mem_nhds (by linarith : (0 : ℝ) < ρ₁ - ρ)),
      hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 6))]
      with k hε1 hs hδ1 hδ2 hratio
    have hspos : 0 < CellFamily.mesh k ^ β := Real.rpow_pos_of_pos (hmeshPos k) β
    have h6 : 6 * CellFamily.mesh k ^ q ≤ CellFamily.mesh k ^ β := by
      rw [pow_one, div_lt_iff₀ hspos] at hratio
      nlinarith
    exact ⟨hε1, by linarith, h6, by linarith, by linarith⟩
  have hlevels : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      ω ∈ MatedCRTResistanceLevelSet n := by
    intro n
    let τ : ℝ := 1 / ((n : ℝ) + 1)
    have hτ : 0 < τ := by positivity
    have hBsmall : ∀ᶠ k : ℕ in atTop,
        GMS3.lemma34Bound (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ q)
          (CellFamily.mesh k ^ β') A (CellFamily.mesh k ^ α) < τ :=
      hB.eventually (gt_mem_nhds hτ)
    have hboundAt (k : ℕ)
        (hk : CellFamily.mesh k < 1 ∧ CellFamily.mesh k ^ β < ρ ∧
          6 * CellFamily.mesh k ^ q ≤ CellFamily.mesh k ^ β ∧
          CellFamily.mesh k ^ q < ρ - CellFamily.mesh k ^ β ∧
          ρ + CellFamily.mesh k ^ q < ρ₁)
        (hbk : GMS3.lemma34Bound (CellFamily.mesh k ^ β) ρ (CellFamily.mesh k ^ q)
          (CellFamily.mesh k ^ β') A (CellFamily.mesh k ^ α) < τ) :
        μ (MatedCRTResistanceLevelSet n)ᶜ ≤ ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
      let εk := CellFamily.mesh k
      have hbadProb := hmesh k
      have hscaleEq := hscaledLaw εk (matedCRT_mesh_pos k)
      have hpre :
          unitRescalePath εk ⁻¹' (MatedCRTResistanceLevelSet n)ᶜ ⊆
            {ω | matedCRTTheorem14MeshGood εk ρ ρ₁ q β β' α A ω}ᶜ := by
        intro ω hω hgood
        apply hω
        exact matedCRT_mesh_good_gives_unit_resistance_level
          (matedCRT_mesh_pos k) hρ hβ'q hA hk
          (by simpa [εk, τ] using hbk.le) hgood
      calc
        μ (MatedCRTResistanceLevelSet n)ᶜ =
            μ.map (unitRescalePath εk) (MatedCRTResistanceLevelSet n)ᶜ := by
              rw [hscaleEq]
        _ = μ (unitRescalePath εk ⁻¹' (MatedCRTResistanceLevelSet n)ᶜ) :=
              (unitRescalePathMeasurableEquiv εk (matedCRT_mesh_pos k)).map_apply _
        _ ≤ μ {ω | matedCRTTheorem14MeshGood εk ρ ρ₁ q β β' α A ω}ᶜ :=
              measure_mono hpre
        _ ≤ ENNReal.ofReal (C * εk ^ α) := hbadProb
    have hmeasure : μ (MatedCRTResistanceLevelSet n)ᶜ = 0 := by
      refine le_antisymm (ENNReal.le_of_forall_pos_le_add (b := 0) ?_) bot_le
      intro η hη _
      obtain ⟨k, ⟨hk, hbk⟩, herr⟩ :=
        ((hside.and hBsmall).and (herror.eventually
          (gt_mem_nhds (show (0 : ℝ≥0∞) < (η : ℝ≥0∞) by exact_mod_cast hη)))).exists
      simpa using (hboundAt k hk hbk).trans herr.le
    have hae : ∀ᵐ ω ∂μ, ω ∈ MatedCRTResistanceLevelSet n := by
      rw [ae_iff]
      have hset : {ω | ¬ ω ∈ MatedCRTResistanceLevelSet n} =
          (MatedCRTResistanceLevelSet n)ᶜ := by
        ext ω
        simp
      rw [hset]
      exact hmeasure
    exact hae
  have hlevelsAll : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      ω ∈ MatedCRTResistanceLevelSet n := ae_all_iff.mpr hlevels
  have hunitRec : ∀ᵐ ω ∂μ, ∀ h1lf : MatedCRT.IsLocallyFinite 1 ω,
      (MatedCRT.graph 1 ω h1lf).Recurrent := by
    filter_upwards [hlocal, hlevelsAll] with ω hloc hlev
    intro h1lf
    have h1eq : h1lf = hloc := Subsingleton.elim _ _
    subst h1lf
    have hconn := GMS3.matedCRT_connected 1 ω hloc
    let G := MatedCRT.graph 1 ω hloc
    apply GMS3.recurrent_of_forall_energy_le G hconn 0
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt δ⁻¹
    have hprod : 1 < δ * (N : ℝ) := by
      have h := mul_lt_mul_of_pos_left hN hδ
      rwa [mul_inv_cancel₀ hδ.ne'] at h
    have hthreshold : 1 / ((N : ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)]
      nlinarith
    rcases hlev N with ⟨h', U, hU, hcond⟩
    have h'Eq : h' = hloc := Subsingleton.elim _ _
    subst h'
    refine ⟨U, GMS3.voltage G 0 U, hU, GMS3.voltage_self G 0 U,
      fun x hx => GMS3.voltage_of_notMem G hU hx, ?_⟩
    have henergy := GMS3.effCond_eq_energy G hconn hU
    rw [← henergy]
    exact hcond.trans hthreshold
  have hlocalε : ∀ᵐ ω ∂μ, MatedCRT.IsLocallyFinite ε ω :=
    MatedCRTHarmonic.ae_isLocallyFinite_holds γ μ hμ ε hε
  have hscaledRec : ∀ᵐ ω ∂μ, ∀ h1lf : MatedCRT.IsLocallyFinite 1 (unitRescalePath ε ω),
      (MatedCRT.graph 1 (unitRescalePath ε ω) h1lf).Recurrent := by
    have hmap : ∀ᵐ ω ∂μ.map (unitRescalePath ε),
        ∀ h1lf : MatedCRT.IsLocallyFinite 1 ω,
          (MatedCRT.graph 1 ω h1lf).Recurrent := by
      rw [hscaledLaw ε hε]
      exact hunitRec
    exact ae_of_ae_map (measurable_unitRescalePath ε).aemeasurable hmap
  filter_upwards [hlocalε, hscaledRec] with ω hεlf hrec
  intro hεlf'
  have hεlfEq : hεlf' = hεlf := Subsingleton.elim _ _
  subst hεlf'
  have h1lf : MatedCRT.IsLocallyFinite 1 (unitRescalePath ε ω) :=
    (isLocallyFinite_unitRescalePath_iff hε ω).mp hεlf
  exact closeRecurrent_of_unitRescalePath hε ω hεlf h1lf (hrec h1lf)

end MatedCRTHarmonic.MesoModel

