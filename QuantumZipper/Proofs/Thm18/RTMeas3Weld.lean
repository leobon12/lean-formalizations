import QuantumZipper.Proofs.Thm18.RTMeas3Arc
import QuantumZipper.Proofs.Thm18.RT6bRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS3, part 2: the open-arc welding driver of the pieces, read by Lusin–Souslin

The open-arc copy of `Thm18Asm.GamS` / `exists_lenDrvReading_of_good` (G4Read2Core.lean): on the
encoded data `y ∈ RD` (a standard Borel space), the pieces' field `Xf y` and a good pair
`p ∈ Good` are related by `GamO` when the open-arc certificate `CertO` holds, the welding point
`0₋(p)` equals the rational reading `xmO`, and the welding map of `p` equals the rational
reading `wRO` at the rationals. On `GamO`, `p` is an open-arc length-welding driver
(`isLenWeldingDriverO_of_memO`, with `Cor15Group.wRm_eqOn_of_rat`), so `GamO` is a partial
graph by uniqueness of welding (`isLenWeldingDriverO_eq_of_good`, the open-arc copy of
`isLenWeldingDriver_eq_of_good`; conformal removability), and Lusin–Souslin selection
(`exists_measurable_of_partialGraph`; Kechris Thm 15.1) gives a measurable reader `ZO`.

Own elementary bookkeeping, copied from G4Read2Core.lean / G4WeldUniq.lean.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ComplexConjugate

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm14WeldingData Thm14Determination Cor15Group

/-- The pieces' field of encoded data. -/
def Xf (y : RD) : FieldSample := readOffField (dfull (decM y))

theorem measurable_Xf : Measurable Xf :=
  measurable_readOffField.comp (measurable_dfull.comp measurable_decM)

/-- **Uniqueness against a good open-arc length-welding driver** (deterministic). -/
theorem isLenWeldingDriverO_eq_of_good {γ ℓ : ℝ} {x : FieldSample} {p q : ℝ × (ℝ → ℝ)}
    (hp : IsLenWeldingDriverO γ x ℓ p) (hp0 : 0 < p.1)
    (hrem : IsConformallyRemovable
      (closure (revHull p.2 p.1) ∪ conj '' closure (revHull p.2 p.1)))
    (hq : IsLenWeldingDriverO γ x ℓ q) :
    q.1 = p.1 ∧ EqOn p.2 q.2 (Icc 0 p.1) := by
  have hCar := CaraR.revMapCaratheodory
  have hArc := CoreArc.loewnerSubhullsOfArc
  obtain ⟨-, hpc, hp00, hpK', hpz, hpw⟩ := hp
  obtain ⟨hq1, hqc, hq00, hqK', hqz, hqw⟩ := hq
  have hpK : IsSimpleCurveHull (revHull p.2 p.1) := hpK'.resolve_left hp0.ne'
  obtain ⟨F, hF⟩ := hCar p.2 hpc hp00 p.1 hp0 hpK
  have hneg : zeroMinus p.2 p.1 < 0 :=
    (WeldingConsistency.car_basic hpc hp0 hF (WeldingConsistency.simpleCurveHull_nonempty hpK)).1
  have hzm : zeroMinus p.2 p.1 = zeroMinus q.2 q.1 := hpz.trans hqz.symm
  have hq0 : 0 < q.1 := by
    rcases hq1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, B5.zeroMinus_zero_time hqc hq00] at hzm
      linarith
  have hqK : IsSimpleCurveHull (revHull q.2 q.1) := hqK'.resolve_left hq0.ne'
  have hweld : EqOn (weldingHom p.2 p.1) (weldingHom q.2 q.1) (Icc (zeroMinus p.2 p.1) 0) := by
    intro s hs
    rw [hpw s hs, hqw s (hzm ▸ hs)]
  have hrev := revMap_eq_of_welding_eq hCar hpc hqc hp00 hq00 hp0 hq0 hpK hqK hzm hweld hrem
  obtain ⟨-, hT⟩ := WeldingUniqueness.drive_and_time_eq_of_revMap_eq hpc hqc hp0.le hq0.le hrev
  refine ⟨hT.symm, ?_⟩
  rw [← hT] at hrev
  exact WeldingConsistency.eqOn_of_revMap_eq_general hCar hArc hpc hqc hp00 hq00 hp0 hpK hrev

/-- The Borel graph of the open-arc reading. -/
def GamO (γ ℓ : ℝ) (Good : Set PathT) : Set (RD × PathT) :=
  {yp | CertO γ (Xf yp.1) ∧ yp.2 ∈ Good ∧ zmS yp.2 = xmO γ ℓ (Xf yp.1) ∧
    ∀ q : ℚ, xmO γ ℓ (Xf yp.1) ≤ (q : ℝ) → (q : ℝ) ≤ 0 → whS yp.2 q = wRO γ q (Xf yp.1)}

theorem measurableSet_gamO (γ ℓ : ℝ) {Good : Set PathT} (hG : MeasurableSet Good) :
    MeasurableSet (GamO γ ℓ Good) := by
  have hX : Measurable fun yp : RD × PathT => Xf yp.1 := measurable_Xf.comp measurable_fst
  have hx : Measurable fun yp : RD × PathT => xmO γ ℓ (Xf yp.1) := (measurable_xmO γ ℓ).comp hX
  have hQ : ∀ q : ℚ, MeasurableSet {yp : RD × PathT | xmO γ ℓ (Xf yp.1) ≤ (q : ℝ) →
      (q : ℝ) ≤ 0 → whS yp.2 q = wRO γ q (Xf yp.1)} := by
    intro q
    have e : {yp : RD × PathT | xmO γ ℓ (Xf yp.1) ≤ (q : ℝ) →
        (q : ℝ) ≤ 0 → whS yp.2 q = wRO γ q (Xf yp.1)} =
        {yp | xmO γ ℓ (Xf yp.1) ≤ (q : ℝ)}ᶜ ∪ ({_yp | (q : ℝ) ≤ 0}ᶜ ∪
          {yp | whS yp.2 q = wRO γ q (Xf yp.1)}) := by
      ext yp
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [e]
    exact (measurableSet_le hx measurable_const).compl.union
      ((MeasurableSet.const _).compl.union (measurableSet_eq_fun
        ((measurable_whS q).comp measurable_snd) ((measurable_wRO γ q).comp hX)))
  have e2 : GamO γ ℓ Good = ((fun yp : RD × PathT => Xf yp.1) ⁻¹' {x | CertO γ x}) ∩
      ((Prod.snd ⁻¹' Good) ∩ ({yp | zmS yp.2 = xmO γ ℓ (Xf yp.1)} ∩
        ⋂ q : ℚ, {yp : RD × PathT | xmO γ ℓ (Xf yp.1) ≤ (q : ℝ) → (q : ℝ) ≤ 0 →
          whS yp.2 q = wRO γ q (Xf yp.1)})) := by
    ext yp
    simp only [GamO, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_iInter]
  rw [e2]
  exact (hX (measurableSet_certO γ)).inter ((measurable_snd hG).inter
    ((measurableSet_eq_fun (measurable_zmS.comp measurable_snd) hx).inter
      (MeasurableSet.iInter hQ)))

/-- On `GamO`, the pair is an open-arc length-welding driver of the pieces' field. -/
theorem isLenWeldingDriverO_of_memO {γ ℓ : ℝ} {Good : Set PathT} (hgood : ∀ p ∈ Good, GoodP p)
    {y : RD} {p : PathT} (h : (y, p) ∈ GamO γ ℓ Good) :
    IsLenWeldingDriverO γ (Xf y) ℓ (p.2, sclDrv p) := by
  obtain ⟨hcert, hpG, hzm, hwh⟩ := h
  obtain ⟨hT, h0, hK, -⟩ := hgood p hpG
  obtain ⟨ν, hν⟩ := hcert.spec
  have := hν.lf
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory (sclDrv p) (continuous_sclDrv p) h0 p.2 hT hK
  have hz : zeroMinus (sclDrv p) p.2 = xmO γ ℓ (Xf y) := by rw [← zmS_eq_of_car hT hF, hzm]
  have hext := wRm_eqOn_of_rat hν.inf (fun s _ => hν.atom s)
    (continuousOn_weldingHom_of_car hF) (fun s hs => (weldingHom_mem_of_car hF hs).1)
    (fun q h1 h2 => by
      rw [← wRO_eq hν h2, ← hwh q (hz ▸ h1) h2, whS_eq_of_car hT hF ⟨h1, h2⟩])
  refine ⟨hT.le, continuous_sclDrv p, h0, Or.inr hK, by rw [hz, xmO_eq hν], fun s hs => ?_⟩
  rw [weldHomRO_eq_wRm hν hs.2]
  exact (hext s hs).symm

/-- An open-arc length-welding driver from `Good` of a certified field lies in `GamO`. -/
theorem mem_gamO {γ ℓ : ℝ} {Good : Set PathT} (hgood : ∀ p ∈ Good, GoodP p) {y : RD}
    {p : PathT} (hc : CertO γ (Xf y)) (hp : p ∈ Good)
    (hL : IsLenWeldingDriverO γ (Xf y) ℓ (p.2, sclDrv p)) : (y, p) ∈ GamO γ ℓ Good := by
  obtain ⟨hT, h0, hK, -⟩ := hgood p hp
  obtain ⟨ν, hν⟩ := hc.spec
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory (sclDrv p) (continuous_sclDrv p) h0 p.2 hT hK
  have hz : zmS p = xmO γ ℓ (Xf y) := by
    rw [zmS_eq_of_car hT hF, xmO_eq hν]
    exact hL.2.2.2.2.1
  refine ⟨hc, hp, hz, fun q h1 h2 => ?_⟩
  have h1' : zeroMinus (sclDrv p) p.2 ≤ q := by rw [← zmS_eq_of_car hT hF, hz]; exact h1
  rw [whS_eq_of_car hT hF ⟨h1', h2⟩, hL.2.2.2.2.2 q ⟨h1', h2⟩, wRO_eq hν h2,
    weldHomRO_eq_wRm hν h2]

theorem isPartialGraph_gamO {γ ℓ : ℝ} {Good : Set PathT} (hgood : ∀ p ∈ Good, GoodP p) :
    IsPartialGraph (GamO γ ℓ Good) := by
  rintro y p p' hp hp'
  have hL := isLenWeldingDriverO_of_memO hgood hp
  have hL' := isLenWeldingDriverO_of_memO hgood hp'
  obtain ⟨hT, -, -, hrem⟩ := hgood p hp.2.1
  obtain ⟨h1, h2⟩ := isLenWeldingDriverO_eq_of_good hL hT hrem hL'
  refine Prod.ext ?_ h1.symm
  ext ⟨u, hu⟩
  have := @h2 (p.2 * u) ⟨mul_nonneg hT.le hu.1, by nlinarith [hu.2]⟩
  have h1' : p.2 = p'.2 := h1.symm
  simp only [sclDrv] at this
  rw [← h1', mul_div_cancel_left₀ _ hT.ne', extIccPath_of_mem _ _ hu,
    extIccPath_of_mem _ _ hu] at this
  exact mul_left_cancel₀ (Real.sqrt_pos.2 hT).ne' this

/-- **The measurable open-arc welding reader.** -/
theorem exists_weldReaderO (γ ℓ : ℝ) {Good : Set PathT} (hGm : MeasurableSet Good)
    (hgood : ∀ p ∈ Good, GoodP p) :
    ∃ ZO : RD → PathT, Measurable ZO ∧ ∀ yp ∈ GamO γ ℓ Good, ZO yp.1 = yp.2 :=
  exists_measurable_of_partialGraph (measurableSet_gamO γ ℓ hGm) (isPartialGraph_gamO hgood)

end RTMeas
end R18
end QuantumZipper
