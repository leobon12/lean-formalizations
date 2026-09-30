import QuantumZipper.Proofs.Thm14.WDGReduce
import QuantumZipper.Proofs.Loewner.CoreArc3e

/-!
# ZM-WELD: `R_h` determines `0₋` (field-side input 2 of Theorem 1.4(b))

Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1.4, pp. 16–17:
`R = R_h : (−∞,0] → [0,∞)`, `ν_h[x,0] = ν_h[0,R(x)]`, and "Theorem 1.4 implies that `R`
determines `η_T` almost surely". The paper does not say how `0₋` is read off from `R`; we prove
`Thm14WDG.ZeroMinusOfWeldR` as follows.

* **Uniqueness of `0₋` given the welding** (`not_zeroMinus_lt_of_weld`, deterministic). If two
  continuous drivers `W₁, W₂` from `0` have simple reverse hulls at time `T`, the first one with
  removable doubled hull, and `0₋(W₂,T) < 0₋(W₁,T)` while their welding homeomorphisms agree at
  the rationals of `[0₋(W₁,T), 0]`, pick `s < T` with `0₋(W₂,s) = 0₋(W₁,T)` (intermediate values
  of `s ↦ 0₋(W₂,s)`); by welding consistency across times, `W₁` at time `T` and `W₂` at time `s`
  have the same welding data, so welding uniqueness (removability) gives `s = T`, absurd. This
  is the first case of the proof of `WeldingConsistency.eqOn_of_isWeldingDriver` (AUDIT-3 M3),
  i.e. the half-plane capacity of the welded curve is strictly monotone in the welded interval.
* **Borel graph** (`zeroMinusOfWeldR`). On the Borel good set of paths `G`
  (`Thm14OptB.exists_goodDriverSet'`, all removable at time `T`) the Borel welding data is
  injective, so its image `D` is Borel (Lusin–Souslin). The set of pairs `(r, a)` such that
  `(a, r|ℚ∩[a,0])` lies in `D` is a Borel partial graph (by the uniqueness above, applied in
  both directions), and contains `(R_h|ℚ, 0₋)` a.s. by the first clause of Theorem 1.4(a).
  Lusin–Souslin selection (`Thm14Determination.exists_measurable_ae_eq_of_partialGraph`) gives
  the measurable `Z`.

The assembly is our own (routine given the cited welding uniqueness and Lusin–Souslin); no
separate published source spells it out.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace Thm14WDG

open Thm14Determination Thm14WeldingData Thm14GoodDriverSet WeldingConsistency

/-- **Uniqueness of `0₋` given the welding.** Two simple reverse hulls at the same time `T`,
the first one with removable doubled hull, whose welding homeomorphisms agree at the rationals
of `[0₋(W₁,T), 0]`, cannot have `0₋(W₂,T) < 0₋(W₁,T)`. -/
theorem not_zeroMinus_lt_of_weld {W₁ W₂ : ℝ → ℝ} (hW₁ : Continuous W₁) (hW₂ : Continuous W₂)
    (h₁0 : W₁ 0 = 0) (h₂0 : W₂ 0 = 0) {T : ℝ} (hT : 0 < T)
    (hK₁ : IsSimpleCurveHull (revHull W₁ T)) (hK₂ : IsSimpleCurveHull (revHull W₂ T))
    (hrem₁ : IsConformallyRemovable (closure (revHull W₁ T) ∪ conj '' closure (revHull W₁ T)))
    (hlt : zeroMinus W₂ T < zeroMinus W₁ T)
    (hq : ∀ q : ℚ, zeroMinus W₁ T ≤ (q : ℝ) → (q : ℝ) ≤ 0 →
      weldingHom W₁ T q = weldingHom W₂ T q) : False := by
  obtain ⟨F₁, hF₁⟩ := CaraR.revMapCaratheodory W₁ hW₁ h₁0 T hT hK₁
  obtain ⟨ha₁, -, -⟩ := car_basic hW₁ hT hF₁ (simpleCurveHull_nonempty hK₁)
  obtain ⟨s, hs, hsa⟩ := exists_zeroMinus_eq CaraR.revMapCaratheodory
    CoreArc.loewnerSubhullsOfArc hW₂ h₂0 hT hK₂ hlt.le ha₁
  have hst : s < T := lt_of_le_of_ne hs.2 fun h => by rw [h] at hsa; linarith
  have hK₂s := isSimpleCurveHull_revHull_of_le CoreArc.loewnerSubhullsOfArc hW₂ h₂0 hT hK₂
    hs.1 hs.2
  have hdata : weldingData W₁ T = weldingData W₂ s := by
    unfold weldingData
    rw [hsa]
    refine Prod.ext rfl (funext fun q => ?_)
    simp only
    split_ifs with h
    · rw [hq q h.1 h.2, weldingHom_eq_of_le CaraR.revMapCaratheodory
        CoreArc.loewnerSubhullsOfArc hW₂ h₂0 hT hK₂ hs.1 hs.2 ⟨hsa.le.trans h.1, h.2⟩]
    · rfl
  obtain ⟨F₂, hF₂⟩ := CaraR.revMapCaratheodory W₂ hW₂ h₂0 s hs.1 hK₂s
  obtain ⟨hz, hweld⟩ := weldingHom_eqOn_of_weldingData_eq hF₁ hF₂ hdata
  have := (time_eq_of_welding_eq CaraR.revMapCaratheodory hW₁ hW₂ h₁0 h₂0 hT
    hs.1 hK₁ hK₂s hz hweld hrem₁).1
  linarith

/-- The welding data `(a, r|ℚ∩[a,0])` of a candidate `0₋ = a` and rational values `r` of `R`. -/
def candData (p : (ℚ → ℝ) × ℝ) : ℝ × (ℚ → ℝ) :=
  (p.2, fun q => if p.2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 0 then p.1 q else 0)

theorem measurable_candData : Measurable candData := by
  refine measurable_snd.prodMk (measurable_pi_iff.2 fun q => ?_)
  refine Measurable.ite ?_ ((measurable_pi_apply q).comp measurable_fst) measurable_const
  exact (measurableSet_le measurable_snd measurable_const).inter
    (MeasurableSet.const ((q : ℝ) ≤ 0))

/-- **Field-side input 2 of Theorem 1.4(b)**: `R_h` at rational points determines `0₋`,
measurably, almost surely. -/
theorem zeroMinusOfWeldR (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple) :
    ZeroMinusOfWeldR := by
  intro κ hκ0 hκ4 T hT Ω _ P _ B X hB hX hind
  obtain ⟨G, hGm, hgood, hae⟩ :=
    Thm14OptB.exists_goodDriverSet' CaraR.revMapCaratheodory hRSS hκ0 hκ4 hT P B hB
  have hinj := Thm14DriverSide.injOn_weldingDataC_of_good CaraR.revMapCaratheodory hT hgood
  have hD : MeasurableSet (weldingDataC hT.le '' G) :=
    hGm.image_of_measurable_injOn (measurable_weldingDataC hT.le) hinj
  -- data of a good path, in terms of its extension
  have hdat : ∀ f ∈ G, weldingDataC hT.le f = weldingData (extIccPath hT.le f) T := fun f hf =>
    weldingDataC_eq hT.le CaraR.revMapCaratheodory hT (hgood f hf).1 (hgood f hf).2.1
  let Gz : Set ((ℚ → ℝ) × ℝ) := candData ⁻¹' (weldingDataC hT.le '' G)
  have hGzm : MeasurableSet Gz := measurable_candData hD
  have hGzg : IsPartialGraph Gz := by
    rintro r a a' ⟨f, hf, hfe⟩ ⟨f', hf', hfe'⟩
    rw [hdat f hf] at hfe
    rw [hdat f' hf'] at hfe'
    set W₁ := extIccPath hT.le f
    set W₂ := extIccPath hT.le f'
    obtain ⟨h₁0, hK₁, hrem₁, -⟩ := hgood f hf
    obtain ⟨h₂0, hK₂, hrem₂, -⟩ := hgood f' hf'
    have hW₁ : Continuous W₁ := continuous_extIccPath hT.le f
    have hW₂ : Continuous W₂ := continuous_extIccPath hT.le f'
    have ha : zeroMinus W₁ T = a := congrArg Prod.fst hfe
    have ha' : zeroMinus W₂ T = a' := congrArg Prod.fst hfe'
    -- welding values at rationals in the respective intervals
    have hv : ∀ q : ℚ, a ≤ (q : ℝ) → (q : ℝ) ≤ 0 → weldingHom W₁ T q = r q := by
      intro q h1 h2
      have := congrFun (congrArg Prod.snd hfe) q
      simp only [weldingData, candData, ha] at this
      rwa [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨h1, h2⟩] at this
    have hv' : ∀ q : ℚ, a' ≤ (q : ℝ) → (q : ℝ) ≤ 0 → weldingHom W₂ T q = r q := by
      intro q h1 h2
      have := congrFun (congrArg Prod.snd hfe') q
      simp only [weldingData, candData, ha'] at this
      rwa [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨h1, h2⟩] at this
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exfalso
      refine not_zeroMinus_lt_of_weld hW₂ hW₁ h₂0 h₁0 hT hK₂ hK₁ hrem₂ (by rw [ha, ha']; exact hlt)
        fun q h1 h2 => ?_
      rw [ha'] at h1
      rw [hv' q h1 h2, hv q (hlt.le.trans h1) h2]
    · exact heq
    · exfalso
      refine not_zeroMinus_lt_of_weld hW₁ hW₂ h₁0 h₂0 hT hK₁ hK₂ hrem₁ (by rw [ha, ha']; exact hgt)
        fun q h1 h2 => ?_
      rw [ha] at h1
      rw [hv q h1 h2, hv' q (hgt.le.trans h1) h2]
  have h14a := Thm14Wire.theorem1_4a_of_theorem1_3_rss h13 hRSS κ hκ0 hκ4 T hT P B X hB hX hind
  have hmem : ∀ᵐ ω ∂P, ((fun q : ℚ => weldR (Real.sqrt κ)
      (couplingFieldRev κ (drive κ B ω) T (X ω)) q), zeroMinus (drive κ B ω) T) ∈ Gz := by
    filter_upwards [hae, h14a] with ω ⟨hc, hmemG⟩ h14ω
    refine ⟨pathC T (drive κ B ω), hmemG, ?_⟩
    rw [hdat _ hmemG, weldingData_congr (extIccPath_pathC hT.le hc)]
    unfold weldingData candData
    refine Prod.ext rfl (funext fun q => ?_)
    simp only
    split_ifs with hq
    · exact h14ω.1.2 q hq
    · rfl
  obtain ⟨Z, hZ, hZae⟩ := exists_measurable_ae_eq_of_partialGraph P hGzm hGzg _ _ hmem
  exact ⟨Z, hZ, hZae⟩

/-- **Theorem 1.4(b)** from Theorem 1.3, Rohde–Schramm simplicity and the remaining field-side
input `WeldRPairingReadable` (`ZeroMinusOfWeldR` is now proved). -/
theorem theorem1_4b_of_theorem1_3_rss_pairing (h13 : theorem1_3)
    (hRSS : Blueprint.RohdeSchrammSimple) (hR : WeldRPairingReadable) : theorem1_4b :=
  theorem1_4b_of_theorem1_3_rss h13 hRSS hR (zeroMinusOfWeldR h13 hRSS)

end Thm14WDG

end QuantumZipper
