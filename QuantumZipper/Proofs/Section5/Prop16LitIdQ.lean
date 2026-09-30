import QuantumZipper.Proofs.Section5.Prop16LitIdPalm
import QuantumZipper.Proofs.Section5.Prop16LitWire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: clause (1) of the covariance node, proved (COORD-CHANGE, D98)

`Prop16Lit.prop16LitCov1Each_proved`: for every level `C`, a.e. under the weighted law, the chart
identity `(μ_{zoomFieldLit})_{B(0,r₀ x) ∩ ℍ}.map ψ_x = (μ_{zoomField})|_{ψ_x(B(0,r₀ x) ∩ ℍ)}` holds.
Route: the Borel event `IdGood` on the local readings (`measurableSet_litIdSet`) holds at the
Palm-shifted readings (`ae_idGood_palm`), hence, by the Palm transfer (`ae_readings_of_palm`;
Duplantier–Sheffield arXiv:0808.1560 §3.3), at the weighted readings; with the two local limits
(`ExA.prop16LitExA_holds`, `prop16ZoomAreaStmt_of_loc`) the event forces the identity
(`identity_of_idGood`: equality against the countable cutoff family and
`VagueOpen.eq_of_integral_cutoff_eq`). This replaces the node `Prop16LitRepMeasAtStmt`:
`theorem1_6_literal_of_dil_exB`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA Prop16Asm CoordChangeArea
open G1Side (pullMu pullMu_apply)

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

/-- **The event forces the chart identity.** -/
theorem identity_of_idGood {γ : ℝ} (hfam : LitFamily D a b ψ r₀) (hDH : D ⊆ H) {x : ℝ}
    (hx : x ∈ Ioo a b) {Z Y : FieldSample} {μZ μY : Measure ℂ}
    (hμZ : IsVagueLimitOn (ball 0 (r₀ x) ∩ H) (areaApprox γ Z) μZ)
    (hμY : IsVagueLimitOn (zoomDomain D x) (areaApprox γ Y) μY) (hI : IdGood ψ a b r₀ γ Z Y x) :
    μZ.map (ψ x) = μY.restrict (ψ x '' (ball 0 (r₀ x) ∩ H)) := by
  obtain ⟨hψd, hψi, -⟩ := hfam.2.2 x hx
  have hψm : Measurable (ψ x) := hfam.1.comp (measurable_const.prodMk measurable_id)
  set U := ball (0 : ℂ) (r₀ x) ∩ H with hUdef
  have hUo : IsOpen U := isOpen_ball.inter isOpen_H
  have hUH : U ⊆ H := inter_subset_right
  have heq : ∀ n : ℕ, ∀ g ∈ famF, ∫ z, hbCut (r₀ x) n z * g z ∂μZ =
      ∫ z, hbCut (r₀ x) n z * g z ∂((pullMu μY (ψ x)).restrict U) := by
    intro n g hg
    obtain ⟨l, h1, h2⟩ := hI n g hg
    obtain ⟨hc, hs, hU⟩ := FnT_test (r₀ := r₀) hg n x
    obtain ⟨hc', hs', hV⟩ := pullT_test hfam hDH hx hg n
    have e1 : ∫ z, FnT r₀ g n x z ∂μZ = l := tendsto_nhds_unique (hμZ.2.2 _ hc hs hU) h1
    have e2 : ∫ w, pullT ψ a b r₀ (FnT r₀ g n) x w ∂μY = l :=
      tendsto_nhds_unique (hμY.2.2 _ hc' hs' (hV.trans (chart_image_subset hfam hx))) h2
    rw [integral_pullT hfam hx hc hU] at e2
    have e3 : ∫ z, FnT r₀ g n x z ∂((pullMu μY (ψ x)).restrict U) =
        ∫ z, FnT r₀ g n x z ∂(pullMu μY (ψ x)) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h => hz (hU h)
    show ∫ z, FnT r₀ g n x z ∂μZ = ∫ z, FnT r₀ g n x z ∂((pullMu μY (ψ x)).restrict U)
    rw [e3, e1, e2]
  have hK₂ : ∀ K, IsCompact K → K ⊆ U → (pullMu μY (ψ x)).restrict U K < ∞ := by
    intro K hK hKU
    refine (Measure.restrict_apply_le _ _).trans_lt ?_
    rw [pullMu_apply hψd.continuousOn hψi hK.isClosed.measurableSet,
      inter_eq_left.2 (hKU.trans hUH)]
    exact hμY.2.1 _ (hK.image_of_continuousOn (hψd.continuousOn.mono (hKU.trans hUH)))
      ((image_mono hKU).trans (chart_image_subset hfam hx))
  have hμ : μZ = (pullMu μY (ψ x)).restrict U :=
    VagueOpen.eq_of_integral_cutoff_eq hUo hUH (continuous_hbCut _) (hbCut_nonneg _)
      (hbCut_le_one _) (tsupport_hbCut _) (fun K hK hKU => hbCut_eventually_one hK hKU)
      famF_dense hμZ.1 (by rw [Measure.restrict_apply' hUo.measurableSet, compl_inter_self,
        measure_empty]) hμZ.2.1 hK₂ heq
  have h := map_pullMu_withDensity hψm hψd.continuousOn hψi (ν := μY) hUo.measurableSet hUH
    (f := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [withDensity_const, one_smul] at h
  rw [hμ, h]

/-- Locality of the straight zoom. -/
theorem circAgree_zoomField_rep {γ C : ℝ} {c d : ℝ} (hgeo : K3.Prop16Geometry D c d)
    (hca : c ≤ a) (hbd : b ≤ d) (Y : FieldSample) (y : ℕ → ℝ)
    (hy : ∀ i, y i = Y (repMeas D a b i)) (t : ℝ) :
    Prop16Area.G.CircAgree (zoomDomain D t) (zoomField γ C Y t)
      (zoomField γ C (repFam D a b 0 y) t) := by
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  have hDW : D ⊆ W := fun z hz => by
    have : z ∈ W ∩ Hbar := by rw [hWV]; exact Or.inl hz
    exact this.1
  have hag : Prop16Area.G.CircAgree W Y (repFam D a b 0 y) :=
    circAgree_repFam hWV Y y (fun i hi => by rw [hy i]; simp [repMeas, hi])
  have e : ∀ y' : FieldSample, zoomField γ C y' t = addConst (zoomField γ C y' t) 0 := by
    intro y'; funext μ; simp [addConst]
  intro n k z hz hs
  rw [e Y, e (repFam D a b 0 y)]
  exact circAgree_zoomFree_nc hWo hag γ C 0 t n k z hz (hs.trans fun u hu => hDW hu)

/-- **Clause (1) of `Prop16LitCovStmt`, level by level, proved.** -/
theorem prop16LitCov1Each_proved {γ : ℝ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} (hdat : Prop16Data γ D c d a b h0 P X)
    (hfam : LitFamily D a b ψ r₀) (C : ℝ) :
    ∀ᵐ p ∂(prop16Q γ h0 a b P X), litIdent γ C D (ψ p.2) (r₀ p.2) (ofFun h0 + X p.1) p.2 := by
  obtain ⟨-, -, hgeo, -, hca, hbd, -⟩ := id hdat
  have hDo : IsOpen D := hgeo.1
  have hDH : D ⊆ H := hgeo.2.2.2.1
  have hgood := ae_readings_of_palm hdat (measurableSet_litIdSet hfam γ C) (fun x hx => by
    filter_upwards [ae_idGood_palm hdat hfam C x hx] with ω hω
    refine (mem_litIdSet_iff hfam γ C hx).2 (idGood_congr hfam hDo hDH hx ?_ ?_ hω)
    · exact circAgree_litRep hgeo hca hbd hfam _ _ (fun i => rfl) x hx
    · exact circAgree_zoomField_rep hgeo hca hbd _ _ (fun i => rfl) x)
  have hloc := prop16LocGoodStmt_of_coupling prop16MixedFreeLocCoupling_mm
  filter_upwards [ae_mem_Ioo_prop16Q hdat, hgood, prop16LitExA_holds hdat hfam C,
    prop16ZoomAreaStmt_of_loc hloc γ D c d a b h0 P X hdat C] with p hp1 hp2 hZ hY
  have hI := (mem_litIdSet_iff hfam γ C hp1).1 (hp2 hp1)
  have hsymm : ∀ {U : Set ℂ} {x x' : FieldSample}, Prop16Area.G.CircAgree U x x' →
      Prop16Area.G.CircAgree U x' x := fun h n k z hz hs => (h n k z hz hs).symm
  have hI' := idGood_congr hfam hDo hDH hp1
    (hsymm (circAgree_litRep (γ := γ) (C := C) hgeo hca hbd hfam (ofFun h0 + X p.1)
      (rawCoords h0 X (repMeas D a b) p.1) (fun i => rfl) p.2 hp1))
    (hsymm (circAgree_zoomField_rep (γ := γ) (C := C) hgeo hca hbd (ofFun h0 + X p.1)
      (rawCoords h0 X (repMeas D a b) p.1) (fun i => rfl) p.2)) hI
  obtain ⟨μZ, hμZ⟩ := hZ
  obtain ⟨μY, hμY⟩ := hY
  have hVo : IsOpen (zoomDomain D p.2) := hDo.preimage (continuous_id.add continuous_const)
  unfold litIdent
  rw [LocalRule.qAreaMeasureOn_eq (isOpen_ball.inter isOpen_H) hμZ,
    LocalRule.qAreaMeasureOn_eq hVo hμY]
  exact identity_of_idGood hfam hDH hp1 hμZ hμY hI'

/-- **Node: the canonical-domain half of `Prop16LitExStmt`.** -/
def Prop16LitExBStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16Data γ D c d a b h0 P X →
    ∀ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), LitFamily D a b ψ r₀ → ∀ C : ℝ,
    ∀ᵐ p ∂(prop16Q γ h0 a b P X),
      ∃ m, IsVagueLimitOn (canonicalDomainOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (ball 0 (r₀ p.2) ∩ H))
        (areaApprox γ (canonicalOn γ (zoomFieldLit γ C (ofFun h0 + X p.1) p.2 (ψ p.2))
          (ball 0 (r₀ p.2) ∩ H))) m

theorem prop16LitExStmt_of_B (hB : Prop16LitExBStmt) : Prop16LitExStmt := by
  intro γ D c d a b h0 Ω _ P X hdat ψ r₀ hfam C
  filter_upwards [prop16LitExA_holds hdat hfam C, hB γ D c d a b h0 P X hdat ψ r₀ hfam C]
    with p h1 h2 using ⟨h1, h2⟩

/-- **Proposition 1.6, literal form, from the dilation clause and the canonical-domain
existence.** -/
theorem theorem1_6_literal_of_dil_exB (hDil : Prop16LitDilEachStmt) (hB : Prop16LitExBStmt) :
    theorem1_6_literal := by
  refine theorem1_6_literal_of_covEach_meas ?_ (prop16LitMeasStmt_of_exists (prop16LitExStmt_of_B hB))
  intro γ D c d a b h0 Ω _ P X hdat ψ r₀ hfam C
  filter_upwards [prop16LitCov1Each_proved hdat hfam C, hDil γ D c d a b h0 P X hdat ψ r₀ hfam C]
    with p h1 h2
  exact ⟨h1, h2⟩

end Prop16Lit
end QuantumZipper
