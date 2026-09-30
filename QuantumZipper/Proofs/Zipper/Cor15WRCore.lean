import QuantumZipper.Proofs.Zipper.Cor15WRExt
import QuantumZipper.Proofs.Zipper.Cor15WRConv
import QuantumZipper.Proofs.Thm14.ZeroMinusWeld
import QuantumZipper.Proofs.Thm14.DriverSide
import QuantumZipper.Proofs.Zipper.E1TransferM4Cert

/-!
# Corollary 1.5(a), `t > 0`: the measurable welding-driver reading (deterministic core)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5
(pp. 17–18; no proof in the paper) and Theorem 1.4 ("`R` determines `η_T`"). Task COR15-WR.

Given a Borel set `G` of good paths on `[0,t]` (simple, removable at `t` and at all rational
times in `(0,t)`), `exists_weldRead_of_goodSet` builds a measurable `F` and a measurable set `A`
of `b1Data` values such that `weldDriver √κ x.1 t = F (b1Data x)` on `[0,t]` whenever
`b1Data x ∈ A`, together with an explicit sufficient criterion for membership in `A`.

Route (own assembly, on the pattern of `Thm14WDG.zeroMinusOfWeldR` and
`Thm14DriverSide.exists_measurable_driver_of_weldingData`):
* the rational values `r` of `R_h` are read measurably from `b1Data` (`weldReadB1`);
* `0₋` is selected measurably from `r` (Borel partial graph `Gz`, Lusin–Souslin
  `exists_measurable_of_partialGraph`; uniqueness from `not_zeroMinus_lt_of_weld`);
* the driver is read off the welding data by the measurable inverse of `weldingDataC` on `G`
  (`exists_partialGraph_of_injOn`, `injOn_weldingDataC_of_good`) and `recoverDrive`;
* on `A` the recovered path `W` is a welding driver of `fieldOf x.1`: rational agreement is
  extended to all of `[0₋,0]`, endpoint included, by `wRm_eqOn_of_rat` (needs no atoms and
  `ν[0,∞) = ∞`, certified countably by `AtomQ`, `InfQ`); weld-driver uniqueness
  (`WeldingConsistency.eqOn_of_isWeldingDriver`) and `weldDriver_fieldOf` conclude.

Lusin–Souslin: Kechris, *Classical Descriptive Set Theory*, Thm 15.1 (via mathlib).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Cor15Group

open B1Full CoordsFull Thm14Determination Thm14WeldingData Thm14GoodDriverSet

/-- Countable certificate for `ν[0,∞) = ∞`. -/
def InfQ (γ : ℝ) (y : FieldSample) : Prop :=
  ∀ N : ℕ, ∃ r : ℕ, (N : ℝ≥0∞) ≤ Thm14WDG.mIcc γ 0 r y

theorem measurableSet_infQ (γ : ℝ) : MeasurableSet {y : FieldSample | InfQ γ y} := by
  have e : {y : FieldSample | InfQ γ y} =
      ⋂ N : ℕ, ⋃ r : ℕ, {y | (N : ℝ≥0∞) ≤ Thm14WDG.mIcc γ 0 r y} := by
    ext y; simp [InfQ]
  rw [e]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun r =>
    measurableSet_le measurable_const (Thm14WDG.measurable_mIcc _ _ _)

theorem measure_Ici_eq_top_of_infQ {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) (h : InfQ γ y) : ν (Ici 0) = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun c => ?_
  obtain ⟨r, hr⟩ := h ⌈(c : ℝ≥0)⌉₊
  rw [Thm14WDG.mIcc_eq hν] at hr
  have hc : (c : ℝ≥0∞) ≤ (⌈(c : ℝ≥0)⌉₊ : ℝ≥0∞) := by exact_mod_cast Nat.le_ceil c
  exact hc.trans (hr.trans (measure_mono Icc_subset_Ici_self))

theorem infQ_of_measure_Ici {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) (h : ν (Ici 0) = ⊤) : InfQ γ y := by
  have hU : (⋃ n : ℕ, Icc (0 : ℝ) n) = Ici 0 := by
    ext x
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨⌈x⌉₊, h, Nat.le_ceil x⟩⟩
  have ht : Tendsto (fun n : ℕ => ν (Icc (0 : ℝ) n)) atTop (𝓝 ⊤) := by
    rw [← h, ← hU]
    exact tendsto_measure_iUnion_atTop fun n m hnm =>
      Icc_subset_Icc_right (by exact_mod_cast hnm)
  intro N
  obtain ⟨n, hn⟩ := (ht.eventually (lt_mem_nhds (ENNReal.natCast_lt_top N))).exists
  exact ⟨n, by rw [Thm14WDG.mIcc_eq hν]; exact hn.le⟩

/-- A path on `[0,t]` which is good at time `t` and has removable hulls at rational times. -/
def GoodPathR {t : ℝ} (ht : 0 ≤ t) (g : C(Icc (0 : ℝ) t, ℝ)) : Prop :=
  GoodDriver t (extIccPath ht g) ∧ ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t →
    IsConformallyRemovable (closure (revHull (extIccPath ht g) q) ∪
      conj '' closure (revHull (extIccPath ht g) q))

/-- The `b1Data` value space. -/
abbrev B1E := ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)

/-- **Deterministic core of the driver reading.** -/
theorem exists_weldRead_of_goodSet (γ : ℝ) {t : ℝ} (ht : 0 < t)
    {G : Set C(Icc (0 : ℝ) t, ℝ)} (hGm : MeasurableSet G)
    (hgood : ∀ g ∈ G, GoodPathR ht.le g) :
    ∃ F : B1E → ℝ → ℝ, Measurable F ∧ ∃ A : Set B1E, MeasurableSet A ∧
      (∀ x, b1Data x ∈ A → EqOn (weldDriver γ x.1 t) (F (b1Data x)) (Icc 0 t)) ∧
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
  -- the measurable inverse of the welding data on `G`
  obtain ⟨G', hG'm, hG'g, hG'mem⟩ :=
    exists_partialGraph_of_injOn ht.le (weldingDataC ht.le) (measurable_weldingDataC ht.le)
      hGm hinj
  obtain ⟨F₀, hF₀, hF₀G⟩ := exists_measurable_of_partialGraph hG'm hG'g
  set rd : B1E → ℚ → ℝ := weldReadB1 γ with hrd
  have hrdm : Measurable rd := measurable_weldReadB1 γ
  have hy : Measurable fun e : B1E => E1.fromC e.1.1 :=
    measurable_fromC.comp (measurable_fst.comp measurable_fst)
  refine ⟨fun e => recoverDrive (F₀ (Thm14WDG.candData (rd e, Z (rd e)))),
    measurable_recoverDrive.comp (hF₀.comp (Thm14WDG.measurable_candData.comp
      (hrdm.prodMk (hZ.comp hrdm)))),
    {e | (rd e, Z (rd e)) ∈ Gz} ∩ {e | BdryConvAE (E1.fromC e.1.1)} ∩
      {e | E1.M4.BCert γ (E1.fromC e.1.1)} ∩ {e | AtomQ γ (E1.fromC e.1.1)} ∩
      {e | InfQ γ (E1.fromC e.1.1)}, ?_, ?_, ?_⟩
  · refine (((((hrdm.prodMk (hZ.comp hrdm)) hGzm).inter ?_).inter ?_).inter ?_).inter ?_
    · exact (measurable_fst.comp measurable_fst) measurableSet_bdryConvAE_fromC
    · exact hy (E1.M4.measurableSet_bCert γ)
    · exact hy (measurableSet_atomQ γ)
    · exact hy (measurableSet_infQ γ)
  · rintro x ⟨⟨⟨⟨hGz, hbc⟩, hcert⟩, hatom⟩, hinfq⟩
    obtain ⟨g, hg, hge0⟩ := hGz
    have hge := hge0
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
    have hE := WeldingConsistency.eqOn_of_isWeldingDriver CaraR.revMapCaratheodory
      CoreArc.loewnerSubhullsOfArc ht hWD (weldDriver_spec ⟨_, hWD⟩) hrem hremq
    have hbcx : BdryConvAE x.1 := (bdryConvAE_fieldOf_iff x.1).1 hbc
    intro s hs
    have h1 : weldDriver γ x.1 t s = weldDriver γ y t s := by
      rw [← weldDriver_fieldOf hbcx]; rfl
    have h2 : F₀ (Thm14WDG.candData (r, Z r)) = sampleC ht.le g := by
      rw [← hge0]; exact hF₀G _ (hG'mem g hg)
    show weldDriver γ x.1 t s = recoverDrive (F₀ (Thm14WDG.candData (r, Z r))) s
    rw [h1, ← hE hs, h2]
    exact (recoverDrive_sampleDrive hWc hs).symm
  · rintro e ⟨a, hmem⟩ hbc hcert hatom hinfq
    have hZa : Z (rd e) = a := hZG (rd e, a) hmem
    refine ⟨⟨⟨⟨?_, hbc⟩, hcert⟩, hatom⟩, hinfq⟩
    show (rd e, Z (rd e)) ∈ Gz
    rw [hZa]; exact hmem

end Cor15Group
end QuantumZipper
