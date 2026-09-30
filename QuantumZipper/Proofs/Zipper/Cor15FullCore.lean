import QuantumZipper.Proofs.Zipper.Cor15LastZc

/-!
# Corollary 1.5, clause (c): existence and uniqueness of the welding driver (D97)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18):
"f^h_t and f^η_t are also a.s. determined by this pair". The paper gives no proof (it is immediate
from Theorems 1.3 and 1.4). This file reuses the Cor 1.5 proof chain verbatim:

* `cor15Full_exists_uniqSet`: the deterministic core `exists_weldRead_of_goodSet_cont`
  (`Cor15LastCore`, same measurable set `A` of `b1Data` values, same argument) with the conclusion
  that for `b1Data x ∈ A` the field `x.1` has a welding driver with removable hulls (hence, by
  weld-driver uniqueness `WeldingConsistency.eqOn_of_isWeldingDriver`, every two welding drivers
  agree on `[0,t]`);
* `cor15Full_ae_weldUniq`: `A` is charged a.s. by the unzipped configuration (Theorem 1.4(a) for
  the Theorem 1.3 coupling of an independent Brownian motion, as in `exists_weldRead_cont_ae`),
  and the charge moves to `c = (𝔥₀ + X, √κ B)` by the B1 law identity (`b1_full`, Theorem 1.2's
  law identity for the unzipped field), as in `exists_readVp`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull Thm14Determination Thm14WeldingData Thm14GoodDriverSet

/-- Existence of a welding driver at time `t` and uniqueness on `[0,t]`. -/
def Cor15FullWeldUniq (γ : ℝ) (y : FieldSample) (t : ℝ) : Prop :=
  (∃ W : ℝ → ℝ, IsWeldingDriver γ y t W) ∧
    ∀ W₁ W₂ : ℝ → ℝ, IsWeldingDriver γ y t W₁ → IsWeldingDriver γ y t W₂ →
      ∀ s ∈ Icc 0 t, W₁ s = W₂ s

theorem cor15Full_isWeldingDriver_fieldOf {x : FieldSample} (hx : BdryConvAE x) (γ t : ℝ) :
    IsWeldingDriver γ (fieldOf x) t = IsWeldingDriver γ x t := by
  rw [isWeldingDriver_congr_regEq (regEq_fieldOf x), nrm_eq_addConst]
  have hw : ∀ s, weldHomR γ (addConst x (-(x (foldedCircle 0 1)))) s = weldHomR γ x s :=
    weldHomR_eq_of_smul (LocalRule.ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top
      (qBoundaryMeasure_addConst_ae hx γ _)
  funext W'
  unfold IsWeldingDriver
  simp only [hw]

/-- **Deterministic core** (`exists_weldRead_of_goodSet_cont`, same set `A`): on `A` the field
has a welding driver with removable hulls, hence a unique one on `[0,t]`. -/
theorem cor15Full_exists_uniqSet (γ : ℝ) {t : ℝ} (ht : 0 < t)
    {G : Set C(Icc (0 : ℝ) t, ℝ)} (hGm : MeasurableSet G)
    (hgood : ∀ g ∈ G, GoodPathR ht.le g) :
    ∃ A : Set B1E, MeasurableSet A ∧
      (∀ x : FieldSample × (ℝ → ℝ), b1Data x ∈ A → Cor15FullWeldUniq γ x.1 t) ∧
      ∀ e : B1E, (∃ a : ℝ, Thm14WDG.candData (weldReadB1 γ e, a) ∈ weldingDataC ht.le '' G) →
        BdryConvAE (E1.fromC e.1.1) → E1.M4.BCert γ (E1.fromC e.1.1) →
        AtomQ γ (E1.fromC e.1.1) → InfQ γ (E1.fromC e.1.1) → e ∈ A := by
  have hgood' : ∀ g ∈ G, GoodDriver t (extIccPath ht.le g) := fun g hg => (hgood g hg).1
  have hinj := Thm14DriverSide.injOn_weldingDataC_of_good CaraR.revMapCaratheodory ht hgood'
  have hD : MeasurableSet (weldingDataC ht.le '' G) :=
    hGm.image_of_measurable_injOn (measurable_weldingDataC ht.le) hinj
  have hdat : ∀ f ∈ G, weldingDataC ht.le f = weldingData (extIccPath ht.le f) t := fun f hf =>
    weldingDataC_eq ht.le CaraR.revMapCaratheodory ht (hgood' f hf).1 (hgood' f hf).2.1
  -- the `0₋` selection
  let Gz : Set ((ℚ → ℝ) × ℝ) := Thm14WDG.candData ⁻¹' (weldingDataC ht.le '' G)
  have hGzm : MeasurableSet Gz := Thm14WDG.measurable_candData hD
  have hGzg : IsPartialGraph Gz := by
    rintro r a a' ⟨f, hf, hfe⟩ ⟨f', hf', hfe'⟩
    rw [hdat f hf] at hfe
    rw [hdat f' hf'] at hfe'
    set W₁ := extIccPath ht.le f
    set W₂ := extIccPath ht.le f'
    obtain ⟨h₁0, hK₁, hrem₁, -⟩ := hgood' f hf
    obtain ⟨h₂0, hK₂, hrem₂, -⟩ := hgood' f' hf'
    have hW₁ : Continuous W₁ := continuous_extIccPath ht.le f
    have hW₂ : Continuous W₂ := continuous_extIccPath ht.le f'
    have ha : zeroMinus W₁ t = a := congrArg Prod.fst hfe
    have ha' : zeroMinus W₂ t = a' := congrArg Prod.fst hfe'
    have hv : ∀ q : ℚ, a ≤ (q : ℝ) → (q : ℝ) ≤ 0 → weldingHom W₁ t q = r q := by
      intro q h1 h2
      have := congrFun (congrArg Prod.snd hfe) q
      simp only [weldingData, Thm14WDG.candData, ha] at this
      rwa [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨h1, h2⟩] at this
    have hv' : ∀ q : ℚ, a' ≤ (q : ℝ) → (q : ℝ) ≤ 0 → weldingHom W₂ t q = r q := by
      intro q h1 h2
      have := congrFun (congrArg Prod.snd hfe') q
      simp only [weldingData, Thm14WDG.candData, ha'] at this
      rwa [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨h1, h2⟩] at this
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exfalso
      refine Thm14WDG.not_zeroMinus_lt_of_weld hW₂ hW₁ h₂0 h₁0 ht hK₂ hK₁ hrem₂
        (by rw [ha, ha']; exact hlt) fun q h1 h2 => ?_
      rw [ha'] at h1
      rw [hv' q h1 h2, hv q (hlt.le.trans h1) h2]
    · exact heq
    · exfalso
      refine Thm14WDG.not_zeroMinus_lt_of_weld hW₁ hW₂ h₁0 h₂0 ht hK₁ hK₂ hrem₁
        (by rw [ha, ha']; exact hgt) fun q h1 h2 => ?_
      rw [ha] at h1
      rw [hv q h1 h2, hv' q (hgt.le.trans h1) h2]
  obtain ⟨Z, hZ, hZG⟩ := exists_measurable_of_partialGraph hGzm hGzg
  set rd : B1E → ℚ → ℝ := weldReadB1 γ with hrd
  have hrdm : Measurable rd := measurable_weldReadB1 γ
  have hy : Measurable fun e : B1E => E1.fromC e.1.1 :=
    measurable_fromC.comp (measurable_fst.comp measurable_fst)
  refine ⟨{e | (rd e, Z (rd e)) ∈ Gz} ∩ {e | BdryConvAE (E1.fromC e.1.1)} ∩
      {e | E1.M4.BCert γ (E1.fromC e.1.1)} ∩ {e | AtomQ γ (E1.fromC e.1.1)} ∩
      {e | InfQ γ (E1.fromC e.1.1)}, ?_, ?_, ?_⟩
  · refine (((((hrdm.prodMk (hZ.comp hrdm)) hGzm).inter ?_).inter ?_).inter ?_).inter ?_
    · exact (measurable_fst.comp measurable_fst) measurableSet_bdryConvAE_fromC
    · exact hy (E1.M4.measurableSet_bCert γ)
    · exact hy (measurableSet_atomQ γ)
    · exact hy (measurableSet_infQ γ)
  · rintro x ⟨⟨⟨⟨hGz, hbc⟩, hcert⟩, hatom⟩, hinfq⟩
    obtain ⟨g, hg, hge⟩ := hGz
    set W := extIccPath ht.le g with hW
    obtain ⟨⟨hW0, hK, hrem, -⟩, hremq⟩ := hgood g hg
    have hWc : Continuous W := continuous_extIccPath ht.le g
    rw [hdat g hg] at hge
    set r := rd (b1Data x)
    have ha : zeroMinus W t = Z r := congrArg Prod.fst hge
    have hv : ∀ q : ℚ, Z r ≤ (q : ℝ) → (q : ℝ) ≤ 0 → weldingHom W t q = r q := by
      intro q h1 h2
      have h1' : zeroMinus W t ≤ (q : ℝ) := ha ▸ h1
      have := congrFun (congrArg Prod.snd hge) q
      simp only [weldingData, Thm14WDG.candData] at this
      rwa [ite_eq_left ⟨h1', h2⟩, ite_eq_left ⟨h1, h2⟩] at this
    set y := E1.fromC (b1Data x).1.1 with hydef
    obtain ⟨ν, hν⟩ := E1.M4.exists_isVagueLimitR_of_bCert hcert
    have := hν.1
    have hRy : ∀ s, weldHomR γ y s = Thm14WDG.wRm ν s := fun s => by
      rw [show weldHomR γ y s = Thm14WDG.wRm (qBoundaryMeasure γ y) s from rfl,
        qBoundaryMeasure_eq hν]
    have hrq : ∀ q : ℚ, r q = Thm14WDG.wRm ν q := fun q => Thm14WDG.weldReadF_eq hν q
    obtain ⟨Fc, hFc⟩ := CaraR.revMapCaratheodory W hWc hW0 t ht hK
    have hext := wRm_eqOn_of_rat (measure_Ici_eq_top_of_infQ hν hinfq)
      (fun s _ => measure_singleton_eq_zero_of_atomQ hν hatom s)
      (continuousOn_weldingHom_of_car hFc) (fun s hs => (weldingHom_mem_of_car hFc hs).1)
      (fun q h1 h2 => by rw [← hrq, ← hv q (ha ▸ h1) h2])
    have hWD : IsWeldingDriver γ y t W :=
      ⟨hWc, hW0, Or.inr hK, fun s hs => by rw [hRy]; exact (hext s hs).symm⟩
    have hbcx : BdryConvAE x.1 := (bdryConvAE_fieldOf_iff x.1).1 hbc
    have hP : IsWeldingDriver γ y t = IsWeldingDriver γ x.1 t :=
      cor15Full_isWeldingDriver_fieldOf hbcx γ t
    refine ⟨⟨W, hP ▸ hWD⟩, fun W₁ W₂ h₁ h₂ s hs => ?_⟩
    have e1 := WeldingConsistency.eqOn_of_isWeldingDriver CaraR.revMapCaratheodory
      CoreArc.loewnerSubhullsOfArc ht hWD (hP ▸ h₁) hrem hremq
    have e2 := WeldingConsistency.eqOn_of_isWeldingDriver CaraR.revMapCaratheodory
      CoreArc.loewnerSubhullsOfArc ht hWD (hP ▸ h₂) hrem hremq
    rw [← e1 hs, e2 hs]
  · rintro e ⟨a, hmem⟩ hbc hcert hatom hinfq
    have hZa : Z (rd e) = a := hZG (rd e, a) hmem
    refine ⟨⟨⟨⟨?_, hbc⟩, hcert⟩, hatom⟩, hinfq⟩
    show (rd e, Z (rd e)) ∈ Gz
    rw [hZa]; exact hmem

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Clause (c) for `t > 0`** (from Theorem 1.3 and Rohde–Schramm): almost surely the field
`𝔥₀ + X` has a welding driver at time `t`, unique on `[0,t]`. -/
theorem cor15Full_ae_weldUniq (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, Cor15FullWeldUniq (Real.sqrt κ) (ofFun (h0rev κ) + X ω) t := by
  set γ := Real.sqrt κ
  obtain ⟨B', hB', hind', hae⟩ := ae_coordsFull_unzip_map κ hB hX hind ht.le
  obtain ⟨G, hGm, hgood, hGae⟩ := exists_goodPathRSet hRSS hκ hκ4 ht P B' hB'
  obtain ⟨A, hAm, hdet, hcrit⟩ := cor15Full_exists_uniqSet γ ht hGm hgood
  have h4a := Thm14Wire.theorem1_4a_of_theorem1_3_rss h13 hRSS κ hκ hκ4 t ht P B' X hB' hX hind'
  have hrc := RevCouplingReg.revCouplingBoundaryMeasureRegular κ hκ hκ4 t ht P B' X hB' hX hind'
  -- the unzipped side charges `A`
  have hyA : ∀ᵐ ω ∂P,
      b1Data (zipCapDown γ t (ofFun (h0rev κ) + X ω, drive κ B ω)) ∈ A := by
    filter_upwards [hae, h4a, hGae, hrc, ae_reg_zipCapDown hκ hκ4 hB hX hind ht] with ω ⟨_, hC⟩
      ⟨⟨_, hw⟩, _⟩ ⟨hc, hmemG⟩ ⟨hatom, _, _⟩ ⟨hbc, hcert, hinf⟩
    set y := zipCapDown γ t (ofFun (h0rev κ) + X ω, drive κ B ω) with hy
    set V := drive κ B' ω
    have hqy : qBoundaryMeasure γ y.1 =
        qBoundaryMeasure γ (couplingFieldRev κ V t (X ω)) :=
      UnzipFull.qBoundaryMeasure_congr_of_coordsFull _ hC
    have hcertf := bCert_fieldOf hbc hcert
    obtain ⟨ν, hν⟩ := E1.M4.exists_isVagueLimitR_of_bCert hcertf
    have hνe : ν = _ • qBoundaryMeasure γ y.1 :=
      (qBoundaryMeasure_eq hν).symm.trans (qBoundaryMeasure_fieldOf hbc γ)
    refine hcrit _ ⟨zeroMinus V t, pathC t V, hmemG, ?_⟩ ((bdryConvAE_fieldOf_iff y.1).2 hbc)
      hcertf (atomQ_of_atomless hν fun s => ?_) (infQ_of_measure_Ici hν ?_)
    · rw [weldingDataC_eq ht.le CaraR.revMapCaratheodory ht (hgood _ hmemG).1.1
        (hgood _ hmemG).1.2.1, weldingData_congr (extIccPath_pathC ht.le hc)]
      unfold weldingData Thm14WDG.candData
      refine Prod.ext rfl (funext fun q => ?_)
      simp only
      split_ifs with hq
      · rw [← weldHomR_eq_weldReadB1 hbc hν q, hw q hq]
        show weldR γ (couplingFieldRev κ V t (X ω)) q = weldHomR γ y.1 q
        unfold weldR weldHomR
        rw [hqy]
      · rfl
    · rw [hνe, Measure.smul_apply, hqy, hatom s, smul_zero]
    · rw [hνe, Measure.smul_apply, hinf, smul_eq_mul, ENNReal.mul_top]
      exact LocalRule.ofReal_exp_ne_zero _
  -- transfer to the zipped side (B1 law identity)
  have hl : P.map (fun ω => b1Data (zipCapDown γ t (ofFun (h0rev κ) + X ω,
      drive κ B ω))) = P.map (fun ω => b1Data (ofFun (h0rev κ) + X ω, drive κ B ω)) :=
    b1_full κ hκ P B X hB hX hind ht
  have hcA := ae_mem_of_map_eq hAm (aemeasurable_b1Data_c κ hB hX)
    (aemeasurable_b1Data_unzip κ hκ hB hX hind ht) hl.symm hyA
  filter_upwards [hcA] with ω hA
  exact hdet (ofFun (h0rev κ) + X ω, drive κ B ω) hA

end Cor15Group
end QuantumZipper
