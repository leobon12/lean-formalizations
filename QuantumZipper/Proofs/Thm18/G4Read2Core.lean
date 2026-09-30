import QuantumZipper.Proofs.Thm18.G4Read2Bdry
import QuantumZipper.Proofs.Thm18.G4ReadDrv
import QuantumZipper.Proofs.Zipper.Cor15WRCore
import QuantumZipper.Proofs.Zipper.Cor15LawCongr
import QuantumZipper.Proofs.Zipper.UnzipFullSplit

/-!
# Theorem 1.8, node G4: the deterministic core of the length-welding driver reading

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1) ("`Z^LEN_t`
is a.s. uniquely defined via conformal welding"). Task G4-READ2.

The random-time analogue of `Cor15Group.exists_weldRead_of_goodSet`. Drivers at a random time
are parametrized by `p = (g, T) ∈ C([0,1], ℝ) × ℝ` (`sclDrv`, `G4Read2Bdry.lean`). Given a Borel
set `Good` of such pairs with positive time, simple and removable reverse hull,
`exists_lenDrvReading_of_good` builds a measurable reading `(G, F)` of good length-`ℓ` welding
drivers (`LenDrvReading`) with an explicit sufficient criterion for membership in `G`.

Route (own assembly on the pattern of `Cor15WRCore`):
* `GamS`: the Borel set of pairs (circle coordinates `c`, `p`) with boundary certificates on the
  field `E1.fromC c` (`BCert`, `AtomQ`, `InfQ`), `p ∈ Good`, `0₋(p) = x₋(c)` (read by `zmS`,
  `xmR`) and welding homeomorphism `= R_c` at the rationals of `[x₋, 0]` (read by `whS`,
  `weldReadF`);
* on `GamS`, `p` is a length-welding driver of `E1.fromC c` (`isLenWeldingDriver_of_mem`: rational
  agreement extends to `[x₋,0]` by `wRm_eqOn_of_rat`), so `GamS` is a partial graph by uniqueness
  of good length-welding drivers (`isLenWeldingDriver_unique_of_good`);
* Lusin–Souslin selection (`exists_measurable_of_partialGraph`; Kechris, *Classical Descriptive
  Set Theory*, Thm 15.1) gives a measurable `Z` on the coordinates; `F d = (T, sclDrv (Z d))`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

open Thm14WeldingData Thm14Determination Cor15Group

/-- The boundary certificates of the field rebuilt from circle coordinates `c`. -/
def CertC (γ : ℝ) (c : ℕ → ℝ) : Prop :=
  E1.M4.BCert γ (E1.fromC c) ∧ AtomQ γ (E1.fromC c) ∧ InfQ γ (E1.fromC c)

theorem measurableSet_certC (γ : ℝ) : MeasurableSet {c : ℕ → ℝ | CertC γ c} :=
  (measurable_fromC (E1.M4.measurableSet_bCert γ)).inter
    ((measurable_fromC (measurableSet_atomQ γ)).inter (measurable_fromC (measurableSet_infQ γ)))

/-- The left welding point `x₋`, read at the rationals. -/
def xmR (γ ℓ : ℝ) (c : ℕ → ℝ) : ℝ :=
  sSup (((↑) : ℚ → ℝ) ''
    {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ Thm14WDG.mIcc γ q 0 (E1.fromC c)})

theorem measurable_xmR (γ ℓ : ℝ) : Measurable (xmR γ ℓ) :=
  measurable_sSup_rat _
    (fun q => measurableSet_setOfPred.2 (measurable_const.and (measurableSet_setOfPred.1
      (measurableSet_le measurable_const ((Thm14WDG.measurable_mIcc _ _ _).comp
        measurable_fromC)))))
    (fun _ => ⟨0, by rintro _ ⟨q, hq, rfl⟩; exact hq.1⟩)

theorem xmR_eq {γ ℓ : ℝ} {c : ℕ → ℝ} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ (E1.fromC c)) ν) :
    xmR γ ℓ c = lenWeldPoint γ (E1.fromC c) ℓ := by
  unfold xmR lenWeldPoint
  rw [qBoundaryMeasure_eq hν]
  simp only [Thm14WDG.mIcc_eq hν]
  have hdown : ∀ s ∈ {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)}, ∀ s' ≤ s,
      s' ∈ {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)} := fun s hs s' h =>
    ⟨h.trans hs.1, hs.2.trans (measure_mono (Icc_subset_Icc_left h))⟩
  have hsub : ((↑) : ℚ → ℝ) '' {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc (q : ℝ) 0)} ⊆
      {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)} := by
    rintro _ ⟨q, hq, rfl⟩
    exact hq
  rcases ({s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)}).eq_empty_or_nonempty with he | hne
  · have h2 := subset_empty_iff.1 (he ▸ hsub)
    rw [he, h2]
  · have hbdd : BddAbove {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)} :=
      ⟨0, fun s hs => hs.1⟩
    obtain ⟨s0, hs0⟩ := hne
    obtain ⟨q0, hq0⟩ := exists_rat_lt s0
    have hne' : (((↑) : ℚ → ℝ) ''
        {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc (q : ℝ) 0)}).Nonempty :=
      ⟨q0, q0, hdown s0 hs0 q0 hq0.le, rfl⟩
    refine le_antisymm (csSup_le_csSup hbdd hne' hsub) ?_
    refine csSup_le ⟨s0, hs0⟩ fun s hs => le_of_forall_lt fun b hb => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hb
    exact lt_of_lt_of_le hq1 (le_csSup (hbdd.mono hsub) ⟨q, hdown s hs q hq2.le, rfl⟩)

/-- Good pairs: positive time, driver starting at `0`, simple and removable reverse hull. -/
def GoodP (p : PathT) : Prop :=
  0 < p.2 ∧ sclDrv p 0 = 0 ∧ IsSimpleCurveHull (revHull (sclDrv p) p.2) ∧
    RemHull (p.2, sclDrv p)

/-- The Borel graph of the reading. -/
def GamS (γ ℓ : ℝ) (Good : Set PathT) : Set ((ℕ → ℝ) × PathT) :=
  {cp | CertC γ cp.1 ∧ cp.2 ∈ Good ∧ zmS cp.2 = xmR γ ℓ cp.1 ∧
    ∀ q : ℚ, xmR γ ℓ cp.1 ≤ (q : ℝ) → (q : ℝ) ≤ 0 →
      whS cp.2 q = Thm14WDG.weldReadF γ q (E1.fromC cp.1)}

theorem measurableSet_gamS (γ ℓ : ℝ) {Good : Set PathT} (hG : MeasurableSet Good) :
    MeasurableSet (GamS γ ℓ Good) := by
  have hx : Measurable fun cp : (ℕ → ℝ) × PathT => xmR γ ℓ cp.1 :=
    (measurable_xmR γ ℓ).comp measurable_fst
  have hQ : ∀ q : ℚ, MeasurableSet {cp : (ℕ → ℝ) × PathT | xmR γ ℓ cp.1 ≤ (q : ℝ) →
      (q : ℝ) ≤ 0 → whS cp.2 q = Thm14WDG.weldReadF γ q (E1.fromC cp.1)} := by
    intro q
    have e : {cp : (ℕ → ℝ) × PathT | xmR γ ℓ cp.1 ≤ (q : ℝ) →
        (q : ℝ) ≤ 0 → whS cp.2 q = Thm14WDG.weldReadF γ q (E1.fromC cp.1)} =
        {cp | xmR γ ℓ cp.1 ≤ (q : ℝ)}ᶜ ∪ ({_cp | (q : ℝ) ≤ 0}ᶜ ∪
          {cp | whS cp.2 q = Thm14WDG.weldReadF γ q (E1.fromC cp.1)}) := by
      ext cp
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [e]
    refine (measurableSet_le hx measurable_const).compl.union
      ((MeasurableSet.const _).compl.union (measurableSet_eq_fun
        ((measurable_whS q).comp measurable_snd)
        ((Thm14WDG.measurable_weldReadF γ q).comp (measurable_fromC.comp measurable_fst))))
  have e2 : GamS γ ℓ Good = (Prod.fst ⁻¹' {c | CertC γ c}) ∩ ((Prod.snd ⁻¹' Good) ∩
      ({cp | zmS cp.2 = xmR γ ℓ cp.1} ∩ ⋂ q : ℚ, {cp : (ℕ → ℝ) × PathT |
        xmR γ ℓ cp.1 ≤ (q : ℝ) → (q : ℝ) ≤ 0 →
          whS cp.2 q = Thm14WDG.weldReadF γ q (E1.fromC cp.1)})) := by
    ext cp
    simp only [GamS, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter]
  rw [e2]
  exact (measurable_fst (measurableSet_certC γ)).inter ((measurable_snd hG).inter
    ((measurableSet_eq_fun (measurable_zmS.comp measurable_snd) hx).inter
      (MeasurableSet.iInter hQ)))

theorem weldHomR_eq_wRm {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) (s : ℝ) : weldHomR γ y s = Thm14WDG.wRm ν s := by
  rw [show weldHomR γ y s = Thm14WDG.wRm (qBoundaryMeasure γ y) s from rfl,
    qBoundaryMeasure_eq hν]

/-- On `GamS`, the pair is a length-welding driver of the rebuilt field. -/
theorem isLenWeldingDriver_of_mem {γ ℓ : ℝ} {Good : Set PathT} (hgood : ∀ p ∈ Good, GoodP p)
    {c : ℕ → ℝ} {p : PathT} (h : (c, p) ∈ GamS γ ℓ Good) :
    IsLenWeldingDriver γ (E1.fromC c) ℓ (p.2, sclDrv p) := by
  obtain ⟨⟨hcert, hatom, hinfq⟩, hpG, hzm, hwh⟩ := h
  obtain ⟨hT, h0, hK, -⟩ := hgood p hpG
  obtain ⟨ν, hν⟩ := E1.M4.exists_isVagueLimitR_of_bCert hcert
  have := hν.1
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory (sclDrv p) (continuous_sclDrv p) h0 p.2 hT hK
  have hz : zeroMinus (sclDrv p) p.2 = xmR γ ℓ c := by rw [← zmS_eq_of_car hT hF, hzm]
  have hext := wRm_eqOn_of_rat (measure_Ici_eq_top_of_infQ hν hinfq)
    (fun s _ => measure_singleton_eq_zero_of_atomQ hν hatom s)
    (continuousOn_weldingHom_of_car hF) (fun s hs => (weldingHom_mem_of_car hF hs).1)
    (fun q h1 h2 => by
      rw [← Thm14WDG.weldReadF_eq hν q, ← hwh q (hz ▸ h1) h2, whS_eq_of_car hT hF ⟨h1, h2⟩])
  refine ⟨hT.le, continuous_sclDrv p, h0, Or.inr hK, by rw [hz, xmR_eq hν], fun s hs => ?_⟩
  rw [weldHomR_eq_wRm hν]
  exact (hext s hs).symm

/-- A length-welding driver from `Good` of a certified field lies in `GamS`. -/
theorem mem_gamS {γ ℓ : ℝ} {Good : Set PathT} (hgood : ∀ p ∈ Good, GoodP p) {c : ℕ → ℝ}
    {p : PathT} (hc : CertC γ c) (hp : p ∈ Good)
    (hL : IsLenWeldingDriver γ (E1.fromC c) ℓ (p.2, sclDrv p)) : (c, p) ∈ GamS γ ℓ Good := by
  obtain ⟨hT, h0, hK, -⟩ := hgood p hp
  obtain ⟨ν, hν⟩ := E1.M4.exists_isVagueLimitR_of_bCert hc.1
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory (sclDrv p) (continuous_sclDrv p) h0 p.2 hT hK
  have hz : zmS p = xmR γ ℓ c := by
    rw [zmS_eq_of_car hT hF, xmR_eq hν]
    exact hL.2.2.2.2.1
  refine ⟨hc, hp, hz, fun q h1 h2 => ?_⟩
  have h1' : zeroMinus (sclDrv p) p.2 ≤ q := by rw [← zmS_eq_of_car hT hF, hz]; exact h1
  rw [whS_eq_of_car hT hF ⟨h1', h2⟩, hL.2.2.2.2.2 q ⟨h1', h2⟩, Thm14WDG.weldReadF_eq hν,
    weldHomR_eq_wRm hν]

theorem isPartialGraph_gamS {γ ℓ : ℝ} {Good : Set PathT} (hgood : ∀ p ∈ Good, GoodP p) :
    IsPartialGraph (GamS γ ℓ Good) := by
  rintro c p p' hp hp'
  have hL := isLenWeldingDriver_of_mem hgood hp
  have hL' := isLenWeldingDriver_of_mem hgood hp'
  obtain ⟨hT, -, -, hrem⟩ := hgood p hp.2.1
  obtain ⟨h1, h2⟩ := isLenWeldingDriver_unique_of_good hL hT hrem _ _ hL hL'
  refine Prod.ext ?_ h1
  ext ⟨u, hu⟩
  have := h2 (p.2 * u) ⟨mul_nonneg hT.le hu.1, by nlinarith [hu.2]⟩
  have h1' : p.2 = p'.2 := h1
  simp only [sclDrv] at this
  rw [← h1', mul_div_cancel_left₀ _ hT.ne', extIccPath_of_mem _ _ hu,
    extIccPath_of_mem _ _ hu] at this
  exact mul_left_cancel₀ (Real.sqrt_pos.2 hT).ne' this

theorem measurable_sclDrv_uncurry : Measurable fun q : PathT × ℝ => sclDrv q.1 q.2 := by
  have hev : Measurable fun r : C(Icc (0 : ℝ) 1, ℝ) × Icc (0 : ℝ) 1 => r.1 r.2 :=
    continuous_eval.measurable
  have hpr : Measurable fun q : PathT × ℝ => projIcc (0 : ℝ) 1 zero_le_one (q.2 / q.1.2) :=
    continuous_projIcc.measurable.comp (measurable_snd.div (measurable_snd.comp measurable_fst))
  exact (Real.continuous_sqrt.measurable.comp (measurable_snd.comp measurable_fst)).mul
    (hev.comp ((measurable_fst.comp measurable_fst).prodMk hpr))

/-- Length-welding drivers of `x` and of the field rebuilt from its circle coordinates agree. -/
theorem isLenWeldingDriver_fromC_iff (γ ℓ : ℝ) (x : FieldSample) (q : ℝ × (ℝ → ℝ)) :
    IsLenWeldingDriver γ (E1.fromC (CoordsFull.coordsFull x)) ℓ q ↔
      IsLenWeldingDriver γ x ℓ q := by
  have h := qBoundaryMeasure_congr_regEq'
    (UnzipFull.regEq_of_coordsFull (E1.coordsFull_fromC x)) γ
  have h1 : lenWeldPoint γ (E1.fromC (CoordsFull.coordsFull x)) ℓ = lenWeldPoint γ x ℓ := by
    unfold lenWeldPoint
    rw [h]
  have h2 : ∀ s, weldHomR γ (E1.fromC (CoordsFull.coordsFull x)) s = weldHomR γ x s :=
    fun s => by
      show Thm14WDG.wRm _ s = Thm14WDG.wRm _ s
      rw [h]
  unfold IsLenWeldingDriver
  rw [h1]
  simp only [h2]

/-- **Deterministic core of the length-welding driver reading** (random time). -/
theorem exists_lenDrvReading_of_good (γ ℓ : ℝ) {Good : Set PathT} (hGm : MeasurableSet Good)
    (hgood : ∀ p ∈ Good, GoodP p) :
    ∃ (G : Set E6.FullData) (F : E6.FullData → ℝ × (ℝ → ℝ)), LenDrvReading γ ℓ G F ∧
      ∀ x : FieldSample × (ℝ → ℝ), CertC γ (CoordsFull.coordsFull x.1) →
        (∃ p ∈ Good, IsLenWeldingDriver γ x.1 ℓ (p.2, sclDrv p)) → cfgData x ∈ G := by
  obtain ⟨Z, hZ, hZG⟩ :=
    exists_measurable_of_partialGraph (measurableSet_gamS γ ℓ hGm) (isPartialGraph_gamS hgood)
  have hc : Measurable fun d : E6.FullData => d.1.1 := measurable_fst.comp measurable_fst
  refine ⟨{d | (d.1.1, Z d.1.1) ∈ GamS γ ℓ Good}, fun d => ((Z d.1.1).2, sclDrv (Z d.1.1)),
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (hc.prodMk (hZ.comp hc)) (measurableSet_gamS γ ℓ hGm)
  · exact measurable_snd.comp (hZ.comp hc)
  · exact measurable_sclDrv_uncurry.comp ((hZ.comp (hc.comp measurable_fst)).prodMk
      measurable_snd)
  · intro x hx
    have hL := isLenWeldingDriver_of_mem hgood hx
    obtain ⟨hT, -, -, hrem⟩ := hgood _ hx.2.1
    exact ⟨(isLenWeldingDriver_fromC_iff γ ℓ x.1 _).1 hL, hT, hrem⟩
  · rintro x hcert ⟨p, hp, hL⟩
    have hmem := mem_gamS hgood hcert hp ((isLenWeldingDriver_fromC_iff γ ℓ x.1 _).2 hL)
    have e : Z (CoordsFull.coordsFull x.1) = p := hZG _ hmem
    show (CoordsFull.coordsFull x.1, Z (CoordsFull.coordsFull x.1)) ∈ GamS γ ℓ Good
    rw [e]
    exact hmem

end Thm18Asm
end QuantumZipper
