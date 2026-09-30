import QuantumZipper.Proofs.Thm18.G3Fid2Inst
import QuantumZipper.Proofs.Thm18.G3Concrete
import QuantumZipper.Proofs.LQG.AtomlessUncond

/-!
# G3 fidelity fact F2 for the concrete scheme

`handoff/G3.md`, G3-M123, fidelity fact (F2): almost surely, for every index `i = (δ, η, C)`,
the region fields and the gap field of the concrete G3 scheme have the boundary certificate
`BCert`, and

* `ν₁ + ν₀ = ν_h` on `(−δ − η/4, 3η/4)`,
* `ν₀ + ν₂ = ν_h` on `(−3η/4, 1/2 + η/4)`,

where `ν_h = qBoundaryMeasure γ h` for Theorem 1.2's field `h = normField γ X₀` (`g3Fid2`).

Route (handoff): locality of the boundary measure (the region field is `h` on the folded circles
inside its disc, junk `0` elsewhere, so its approximations are those of `h` inside and
`2^{-kγ²/4}` outside, up to the tangential circles at the disc edges; `G3Fid2Geom`,
`G3Fid2Region`), the cut lemma for vague limits (`G3Fid2Cut`), and the absence of atoms of `ν_h`
(the edges `−δ − η/4, −3η/4, 3η/4, 1/2 + η/4` carry no mass). The a.s. input is that of
Theorem 1.2's field: `h` agrees on folded circles with `Z + (2/γ) log|·|` (`Z` the free field
normalized on the unit semicircle), whose boundary measure exists and equals
`|t|^{−1} ν_Z|_{ℝ∖{0}}` (M4-P4, `LogSing.ae_logSingularity`; Duplantier–Sheffield, *LQG and KPZ*,
§3), and `ν_Z` has no atoms (M4-P5, `AtomlessUncond.ae_noAtoms_zField'`).
Sources: Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 70–71) for the scheme; the
bookkeeping here is our own (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Fid

/-! ## Theorem 1.2's field on folded circles -/

theorem logPot_eq_h0rev {γ : ℝ} (hγ : 0 < γ) :
    LogSing.logPot (-(2 / γ)) 0 = h0rev (γ ^ 2) := by
  funext v
  simp only [LogSing.logPot, h0rev, Complex.ofReal_zero, sub_zero, Real.sqrt_sq hγ.le]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample} {γ : ℝ}

theorem normField_fc (hγ : 0 < γ) (ω : Ω) (c : ℂ) (ρ : ℝ) :
    normField γ X ω (foldedCircle c ρ) = (BdryExist.zField X 1 ω +
      ofFun (LogSing.logPot (-(2 / γ)) 0)) (foldedCircle c ρ) := by
  simp only [normField, BdryExist.zField, addConst, Pi.add_apply, measure_univ,
    ENNReal.toReal_one, mul_one, logPot_eq_h0rev hγ]
  ring

theorem bdryApprox_normField (hγ : 0 < γ) (ω : Ω) :
    bdryApprox γ (normField γ X ω) = bdryApprox γ (BdryExist.zField X 1 ω +
      ofFun (LogSing.logPot (-(2 / γ)) 0)) := by
  funext k
  have e : ∀ z, avgReg (normField γ X ω) k z = avgReg (BdryExist.zField X 1 ω +
      ofFun (LogSing.logPot (-(2 / γ)) 0)) k z := fun z => by
    unfold avgReg
    simp_rw [normField_fc hγ ω]
  simp only [bdryApprox, e]

/-- **A.s. input.** Theorem 1.2's field has a boundary measure, finite approximations on compacts,
and no atoms. -/
theorem ae_normField_good [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsVagueLimitR (bdryApprox γ (normField γ X ω))
        (qBoundaryMeasure γ (normField γ X ω)) ∧
      (∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (normField γ X ω) k)) ∧
      ∀ s, qBoundaryMeasure γ (normField γ X ω) {s} = 0 := by
  have hαQ : -(2 / γ) < Qc γ := by
    unfold Qc; have : 0 < 2 / γ := by positivity
    linarith [div_pos hγ (show (0 : ℝ) < 2 by norm_num)]
  filter_upwards [LogSing.ae_logSingularity hX hγ hγ2 1 hαQ 0
      (LogSing.p3bBound hX hγ hγ2 one_pos (by simp)), RegSample.ae_isRegularSample hX,
      AtomlessUncond.ae_noAtoms_zField' hX hγ hγ2 1] with ω hω hreg hat
  obtain ⟨hglob, hform, -⟩ := hω
  have hY : IsRegularSample (BdryExist.zField X 1 ω + ofFun (LogSing.logPot (-(2 / γ)) 0)) :=
    (hreg.addConst' _).add_ofFun_log' _ 0
  have hb := bdryApprox_normField (X := X) hγ ω
  have hv : IsVagueLimitR (bdryApprox γ (normField γ X ω)) (qBoundaryMeasure γ
      (BdryExist.zField X 1 ω + ofFun (LogSing.logPot (-(2 / γ)) 0))) := by
    rw [hb]; exact hglob
  have hq := qBoundaryMeasure_eq hv
  refine ⟨hq ▸ hv, fun k => ?_, fun s => ?_⟩
  · rw [hb]; exact LogSing.isFiniteMeasureOnCompacts_bdryApprox hY γ k
  · rw [hq, hform]
    exact withDensity_absolutelyContinuous _ _
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self (hat.measure_singleton s))

/-! ## The concrete scheme -/

/-- Adding the two restrictions on the neighbouring pieces recovers `ν` (no atom at the
junction). -/
theorem restrict_add_restrict_eq {ν : Measure ℝ} (hat : ∀ s, ν {s} = 0) {a b c : ℝ}
    (hab : a < b) (hbc : b < c) {A G : Set ℝ}
    (hAU : Ioo a c ∩ A = Ioo a b) (hGU : Ioo a c ∩ G = Ioo b c) :
    (ν.restrict A + ν.restrict G).restrict (Ioo a c) = ν.restrict (Ioo a c) := by
  rw [Measure.restrict_add, Measure.restrict_restrict measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo, hAU, hGU,
    ← Measure.restrict_union (disjoint_left.2 fun x h1 h2 => lt_asymm h1.2 h2.1)
      measurableSet_Ioo]
  have hset : Ioo a c = (Ioo a b ∪ Ioo b c) ∪ {b} := by
    ext x
    simp only [mem_Ioo, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy x b with h | h | h
      · exact Or.inl (Or.inl ⟨h1, h⟩)
      · exact Or.inr h
      · exact Or.inl (Or.inr ⟨h, h2⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | rfl) <;> constructor <;> linarith
  rw [hset, Measure.restrict_union (disjoint_singleton_right.2 (by simp))
    (measurableSet_singleton b), Measure.restrict_eq_zero.2 (hat b), add_zero]

theorem Ioo_inter_Ioo_left {a b c : ℝ} (hbc : b ≤ c) : Ioo a c ∩ Ioo a b = Ioo a b :=
  inter_eq_right.2 (Ioo_subset_Ioo_right hbc)

theorem Ioo_inter_Ioo_right {b c d : ℝ} (hbc : b ≤ c) : Ioo b d ∩ Ioo c d = Ioo c d :=
  inter_eq_right.2 (Ioo_subset_Ioo_left hbc)

theorem Ioo_inter_gap {a b c d u v : ℝ} (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d)
    (hu : a ≤ u) (hu' : u ≤ b) (hv : c ≤ v) (hv' : v ≤ d) :
    Ioo u v ∩ (Icc a b ∪ Icc c d)ᶜ = Ioo b c := by
  ext x
  simp only [mem_inter_iff, mem_Ioo, mem_compl_iff, mem_union, mem_Icc, not_or, not_and_or,
    not_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    rcases h3 with h3 | h3
    · exfalso; linarith
    · rcases h4 with h4 | h4
      · exact ⟨h3, h4⟩
      · exfalso; linarith
  · rintro ⟨h1, h2⟩
    exact ⟨⟨by linarith, by linarith⟩, Or.inr h1, Or.inl h2⟩

/-- **F2 (fidelity of the concrete G3 scheme).** Almost surely, for every index, the region and
gap fields have the boundary certificate, and `ν₁ + ν₀ = ν_h` on `(−δ − η/4, 3η/4)`,
`ν₀ + ν₂ = ν_h` on `(−3η/4, 1/2 + η/4)`. -/
theorem g3Fid2 (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx,
      E1.M4.BCert γ (regionField γ i.t₁ i.r₁ gffBase.X ω) ∧
      E1.M4.BCert γ (regionField γ i.t₂ i.r₂ gffBase.X ω) ∧
      E1.M4.BCert γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ gffBase.X ω) ∧
      (g3ν₁ γ i ω + g3ν₀ γ i ω).restrict (Ioo (-i.δ - i.η / 4) (3 * i.η / 4)) =
        (qBoundaryMeasure γ (normField γ gffBase.X ω)).restrict
          (Ioo (-i.δ - i.η / 4) (3 * i.η / 4)) ∧
      (g3ν₀ γ i ω + g3ν₂ γ i ω).restrict (Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4)) =
        (qBoundaryMeasure γ (normField γ gffBase.X ω)).restrict
          (Ioo (-(3 * i.η / 4)) (1 / 2 + i.η / 4)) := by
  filter_upwards [ae_normField_good gffBase.gff hγ hγ2] with ω hω i
  obtain ⟨hv, hfin, hat⟩ := hω
  obtain ⟨hB1, e1⟩ := regionCut hγ hv hfin hat (t := i.t₁) i.r₁_pos
  obtain ⟨hB2, e2⟩ := regionCut hγ hv hfin hat (t := i.t₂) i.r₂_pos
  obtain ⟨hB0, e0⟩ := gapCut hγ hv hfin hat (t₁ := i.t₁) (t₂ := i.t₂) i.r₁_pos i.r₂_pos
  have ha : i.t₁ - i.r₁ = -i.δ - i.η / 4 := by unfold G3Idx.t₁ G3Idx.r₁; ring
  have hb : i.t₁ + i.r₁ = -(3 * i.η / 4) := by unfold G3Idx.t₁ G3Idx.r₁; ring
  have hc : i.t₂ - i.r₂ = 3 * i.η / 4 := by unfold G3Idx.t₂ G3Idx.r₂; ring
  have hd : i.t₂ + i.r₂ = 1 / 2 + i.η / 4 := by unfold G3Idx.t₂ G3Idx.r₂; ring
  have n1 : g3ν₁ γ i ω = (qBoundaryMeasure γ (normField γ gffBase.X ω)).restrict
      (Ioo (-i.δ - i.η / 4) (-(3 * i.η / 4))) := by
    rw [g3ν₁, bdryM, regionField, if_pos hB1, ← ha, ← hb]; exact e1
  have n2 : g3ν₂ γ i ω = (qBoundaryMeasure γ (normField γ gffBase.X ω)).restrict
      (Ioo (3 * i.η / 4) (1 / 2 + i.η / 4)) := by
    rw [g3ν₂, bdryM, regionField, if_pos hB2, ← hc, ← hd]; exact e2
  have n0 : g3ν₀ γ i ω = (qBoundaryMeasure γ (normField γ gffBase.X ω)).restrict
      (Icc (-i.δ - i.η / 4) (-(3 * i.η / 4)) ∪ Icc (3 * i.η / 4) (1 / 2 + i.η / 4))ᶜ := by
    rw [g3ν₀, bdryM, gapField, if_pos hB0, ← ha, ← hb, ← hc, ← hd]; exact e0
  have := i.hη; have := i.hηδ; have := i.hδ
  have h1 : -i.δ - i.η / 4 < -(3 * i.η / 4) := by linarith
  have h2 : -(3 * i.η / 4) < 3 * i.η / 4 := by linarith
  have h3 : 3 * i.η / 4 < 1 / 2 + i.η / 4 := by linarith
  refine ⟨hB1, hB2, hB0, ?_, ?_⟩
  · rw [n1, n0]
    exact restrict_add_restrict_eq hat h1 h2 (Ioo_inter_Ioo_left h2.le)
      (Ioo_inter_gap h1.le h2 h3.le le_rfl h1.le le_rfl h3.le)
  · rw [n0, n2]
    exact restrict_add_restrict_eq hat h2 h3
      (Ioo_inter_gap h1.le h2 h3.le h1.le le_rfl h3.le le_rfl) (Ioo_inter_Ioo_right h2.le)

end G3Fid
end Thm18Asm
end QuantumZipper
