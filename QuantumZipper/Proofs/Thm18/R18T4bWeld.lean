import QuantumZipper.Proofs.Thm18.R18UpWeld
import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Thm18.G4WeldUniq
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.Thm18.G4GoodSet
import QuantumZipper.Proofs.Thm18.G4CMeasProj

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T4b: existence and uniqueness of the length-welding driver of the wedge field

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
the inverse `Z^LEN_t` of `Z^LEN_{−t}` "is a.s. uniquely defined (via conformal welding)".

**`g4WeldAStmt_holds (hX1) : R18.G4WeldAStmt`**, the old route (`g4WeldStmt_of_good`,
G4WeldUniq.lean; the good set of `g4UnzipGoodSetStmt_of_roundUp`, G4GoodSet.lean; the Borel
reading graph `GamS`, G4Read2Core.lean) with the new premises:

* by E6 on open arcs (`e6StmtArc_of_X1`, `e6Arc_thm18`) the wedge configuration has the law of
  its unzipping `Z_{−ℓ} c` (`zipLenDownArc`), which a.s. equals the field part of
  `zipLenDownA` (`ae_toPair_zipLenDownA_eq`);
* for that unzipped field the rescaled time reversal `revDrv W t a` of the SLE driver
  (`t = lenTimeOpen`, `a = areaScale` of the carried area) IS a length-welding driver
  (`g4UpWeldCoreAStmt_of_X1`); it agrees on `[0, t/a²]` with an element of a Borel set `Good` of
  pairs with simple, conformally removable (Jones–Smirnov) reverse hull
  (`exists_goodSet_allTimes`, the construction of `g4UnzipGoodSetStmt_of_roundUp` at all times
  and scales simultaneously, so no measurability of `t`, `a` is needed);
* the event "the circle coordinates lie in the projection of the Borel graph `GamS`" is
  measurable (Lusin–Souslin, Kechris *Classical Descriptive Set Theory* Thm 15.1 / Cor 15.2,
  `measurableSet_image_fst_of_partialGraph`), holds a.s. for the unzipped field (boundary
  certificates transferred by E6 from `g4WedgeCertStmt`), hence a.s. for `Y` by the law equality;
* on it, `Y ω` has a good length-welding driver, so drivers exist and are unique
  (`isLenWeldingDriver_unique_of_good`).

The measurability of the welding event is left implicit in the paper; the bookkeeping here is an
own elementary argument on top of the cited selection theorem.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G1ZA1c LocLen D3Plus Thm14WeldingData Thm14GoodDriverSet

/-- **A Borel good set at all times and scales** (copy of the construction of
`g4UnzipGoodSetStmt_of_roundUp`, G4GoodSet.lean, uniform in the time `t'` and scale `a`). -/
theorem exists_goodSet_allTimes {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∃ Good : Set PathT, MeasurableSet Good ∧ (∀ p ∈ Good, GoodP p) ∧
      ∀ᵐ ω ∂P, ∀ t' a : ℝ, 0 < t' → 0 < a → ∃ p ∈ Good, p.2 = t' / a ^ 2 ∧
        ∀ u : Icc (0 : ℝ) 1, p.1 u = gStarVal (drive (γ ^ 2) B ω) t' u := by
  choose K hKc hKg hKae using fun n : ℕ => exists_goodCompacts hγ hγ2 hB (P := P) n
  let L : ℕ → ℕ → ℕ → Set PathT := fun n m j =>
    gsMap n '' (K n m ×ˢ (gsParam n j ×ˢ Icc (1 / ((j : ℝ) + 1)) ((j : ℝ) + 1)))
  refine ⟨⋃ n, ⋃ m, ⋃ j, L n m j, ?_, ?_, ?_⟩
  · refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun j => ?_
    exact (((hKc n m).prod ((isCompact_gsParam n j).prod isCompact_Icc)).image
      (continuous_gsMap n)).isClosed.measurableSet
  · intro p hp
    simp only [L, mem_iUnion] at hp
    obtain ⟨n, m, j, ⟨V, ⟨t, r⟩, T⟩, ⟨hV, ⟨⟨ht, -⟩, hrt⟩, hT⟩, rfl⟩ := hp
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    exact goodP_gsMap (hKg n m V hV) (hj.trans_le ht.1) ht.2 hrt (hj.trans_le hT.1)
  · filter_upwards [ae_all_iff.2 hKae] with ω hK t' a ht ha
    set n := ⌈t'⌉₊ with hn_def
    have hn : 0 < n := Nat.ceil_pos.2 ht
    have htn : t' ≤ n := Nat.le_ceil t'
    obtain ⟨hc, m, hm⟩ := hK n hn
    have hst : 0 < Real.sqrt t' := Real.sqrt_pos.2 ht
    have hT : 0 < t' / a ^ 2 := by positivity
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / t' + 1 / Real.sqrt t' + a ^ 2 / t' + t' / a ^ 2)
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have e1 : 0 ≤ 1 / t' := by positivity
    have e2 : 0 ≤ 1 / Real.sqrt t' := by positivity
    have e3 : 0 ≤ a ^ 2 / t' := by positivity
    have b1 : 1 / ((j : ℝ) + 1) ≤ t' := (one_div_le hj1 ht).2 (by linarith)
    have b3 : 1 / ((j : ℝ) + 1) ≤ t' / a ^ 2 :=
      (one_div_le hj1 hT).2 (by rw [one_div_div]; linarith)
    refine ⟨gsMap n (pathC n (drive (γ ^ 2) (Thm14FromThm13.revBM B (n : ℝ).toNNReal) ω),
      ((t', 1 / Real.sqrt t'), t' / a ^ 2)), ?_, rfl, fun u => ?_⟩
    · simp only [L, mem_iUnion]
      have b2 : 1 / Real.sqrt t' ≤ (j : ℝ) + 1 := by linarith
      have b4 : t' / a ^ 2 ≤ (j : ℝ) + 1 := by linarith
      have hrt : 1 / Real.sqrt t' * Real.sqrt t' = 1 := one_div_mul_cancel hst.ne'
      refine ⟨n, m, j, _, ⟨hm, ⟨⟨⟨b1, htn⟩, ⟨e2, b2⟩⟩, ?_⟩, ⟨b3, b4⟩⟩, rfl⟩
      exact hrt
    · have hE := extIccPath_pathC (Nat.cast_nonneg n) hc
      have hR := Thm14FromThm13.drive_revBM (κ := γ ^ 2) (T := (n : ℝ)) B ω
      have hu := u.2
      have hm1 : (n : ℝ) - t' + t' * u ∈ Icc (0 : ℝ) n :=
        ⟨by nlinarith [hu.1, hu.2], by nlinarith [hu.1, hu.2]⟩
      have hm2 : (n : ℝ) - t' ∈ Icc (0 : ℝ) n := ⟨by linarith, by linarith⟩
      simp only [gsMap, gsPath, ContinuousMap.coe_mk]
      rw [hE hm1, hE hm2, ← hR hm1, ← hR hm2]
      simp only [gStarVal]
      rw [show (n : ℝ) - (n - t' + t' * u) = t' * (1 - u) by ring,
        show (n : ℝ) - (n - t') = t' by ring]
      ring

/-- **T4b: `R18.G4WeldAStmt`** (existence and uniqueness of the length-welding driver of the
wedge field) from X1 (⇐ Field–Lawler) alone. -/
theorem g4WeldAStmt_holds (hX1 : BaseFin.BaseFiniteStmt) : G4WeldAStmt := by
  intro γ Ω _ P _ B Y hS hIn hE6A hEq ℓ hℓ
  have hU := g4UpWeldCoreAStmt_of_X1 hX1 γ P B Y hS hIn hE6A hEq ℓ hℓ
  have hE6 := e6StmtArc_of_X1 hX1
  have hum := unzipMeasArc_of_X1 hX1
  obtain ⟨Good, hGm, hGood, hGae⟩ := exists_goodSet_allTimes hS.1 hS.2.1 hS.2.2.1 (P := P)
  set c := wedgeConfig γ B Y with hc
  set c' := fun ω => zipLenDownArc γ ℓ (c ω) with hc'
  have hmc : AEMeasurable (fun ω => Thm18Asm.cfgData (c ω)) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hmc' : AEMeasurable (fun ω => Thm18Asm.cfgData (c' ω)) P :=
    aemeasurable_cfgData_zipLenDownArc hum hS hℓ
  have hlaw : P.map (fun ω => Thm18Asm.cfgData (c' ω)) =
      P.map (fun ω => Thm18Asm.cfgData (c ω)) := e6Arc_thm18 hE6 hS ℓ hℓ
  have hcert' : ∀ᵐ ω ∂P, Thm18Asm.cfgData (c' ω) ∈ {d : E6.FullData | CertC γ d.1.1} :=
    Cor15Group.ae_mem_of_map_eq ((measurable_fst.comp measurable_fst) (measurableSet_certC γ))
      hmc' hmc hlaw (g4WedgeCertStmt γ P B Y hS hIn)
  set S : Set (ℕ → ℝ) := Prod.fst '' GamS γ ℓ Good with hSdef
  have hSm : MeasurableSet S := G4Core.measurableSet_image_fst_of_partialGraph
    (measurableSet_gamS γ ℓ hGm) (isPartialGraph_gamS hGood)
  have hA : MeasurableSet {d : E6.FullData | d.1.1 ∈ S} := (measurable_fst.comp measurable_fst) hSm
  have h' : ∀ᵐ ω ∂P, Thm18Asm.cfgData (c' ω) ∈ {d : E6.FullData | d.1.1 ∈ S} := by
    filter_upwards [hU, ae_toPair_zipLenDownA_eq hS ℓ, D74.ae_wedgeConfig_snd_good hS, hIn.2.2,
      hcert', hGae] with ω hu htp hω hin hcw hG
    obtain ⟨ha, ht, hz, hwe⟩ := hu
    have hfld : (zipLenDownA γ ℓ (wedgeAConfig γ B Y ω)).fld = (c' ω).1 :=
      congrArg Prod.fst htp
    rw [hfld] at hz hwe
    set t := lenTimeOpen γ ℓ (wedgeAConfig γ B Y ω).toPair with htdef
    set a := areaScale (zipCapDownA γ t (wedgeAConfig γ B Y ω)).area with hadef
    have hpe : upDrvA γ ℓ (wedgeAConfig γ B Y ω) = revDrv (drive (γ ^ 2) B ω) t a := rfl
    rw [hpe] at hz hwe
    have hp0 : 0 < (revDrv (drive (γ ^ 2) B ω) t a).1 := div_pos ht (pow_pos ha 2)
    have hp : IsLenWeldingDriver γ (c' ω).1 ℓ (revDrv (drive (γ ^ 2) B ω) t a) := by
      refine ⟨hp0.le, ?_, ?_, Or.inr ?_, hz, hwe⟩
      · exact ((hω.1.comp (continuous_const.sub (continuous_const.mul continuous_id))).sub
          continuous_const).div_const _
      · simp [revDrv]
      · exact isSimpleCurveHull_revDrv hω.1 hω.2 ht ha hin.1 (hin.2.1 _ ht.le)
    obtain ⟨p, hpG, hpT, hpg⟩ := hG t a ht ha
    have hEqOn := sclDrv_eqOn_revDrv ht ha hpT hpg
    rw [hpT] at hEqOn
    have hL0 : IsLenWeldingDriver γ (c' ω).1 ℓ (t / a ^ 2, sclDrv p) :=
      isLenWeldingDriver_of_eqOn (T := t / a ^ 2) (V := (revDrv (drive (γ ^ 2) B ω) t a).2)
        hp (continuous_sclDrv p) (hGood p hpG).2.1 hEqOn
    rw [← hpT] at hL0
    exact ⟨(CoordsFull.coordsFull (c' ω).1, p),
      mem_gamS hGood hcw hpG ((isLenWeldingDriver_fromC_iff γ ℓ _ _).2 hL0), rfl⟩
  have hY := Cor15Group.ae_mem_of_map_eq hA hmc hmc' hlaw.symm h'
  filter_upwards [hY] with ω hω
  obtain ⟨⟨c0, p⟩, hmem, he⟩ := hω
  have he' : c0 = CoordsFull.coordsFull (Y ω) := he
  subst he'
  have hL := (isLenWeldingDriver_fromC_iff γ ℓ (Y ω) _).1 (isLenWeldingDriver_of_mem hGood hmem)
  obtain ⟨hT, -, -, hrem⟩ := hGood p hmem.2.1
  exact ⟨⟨_, hL⟩, isLenWeldingDriver_unique_of_good hL hT hrem⟩

end R18
end QuantumZipper
