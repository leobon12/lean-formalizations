import QuantumZipper.Proofs.Thm18.G1Z2MeasCore
import QuantumZipper.Proofs.Section5.Prop16GNu

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z2-MEAS, part 4: Giry-measurability of the side boundary measure

`g1z2_aemeasurable_sideNu`: if the dyadic coordinates of a field family `Z` are a.e.-measurable
and a.s. the boundary approximations of `Z ω` have a vague limit on the side half-line, then
`ω ↦ g1SideNu γ left (Z ω)` is a.e.-measurable. The side half-line is exhausted by the open
intervals `I n`; on each, the local boundary measure is a.e.-measurable
(`Prop16Area.G.aemeasurable_qBoundaryMeasureOn_Ioo_of_ae`, applied to the field rebuilt from a
measurable version of the coordinates), it is the restriction of the side measure, and the side
measure is the sum of these restrictions over the disjointed pieces. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization

/-- Restriction of a vague limit on `S` to an open `I ⊆ S`. -/
theorem g1z2_isVagueLimitOnR_restrict {S I : Set ℝ} {νs : ℕ → Measure ℝ} {ν : Measure ℝ}
    (h : IsVagueLimitOnR S νs ν) (hI : IsOpen I) (hIS : I ⊆ S) :
    IsVagueLimitOnR I νs (ν.restrict I) := by
  refine ⟨?_, fun K hK hKI => ?_, fun f hf hfc hfI => ?_⟩
  · rw [Measure.restrict_apply hI.measurableSet.compl, compl_inter_self, measure_empty]
  · exact lt_of_le_of_lt (Measure.restrict_le_self K) (h.2.1 K hK (hKI.trans hIS))
  · have e : ∫ t, f t ∂(ν.restrict I) = ∫ t, f t ∂ν :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
        image_eq_zero_of_notMem_tsupport fun h' => ht (hfI h')
    rw [e]
    exact h.2.2 f hf hfc (hfI.trans hIS)

/-- The chosen local boundary measure is a vague limit when one exists. -/
theorem g1z2_qBoundaryMeasureOn_spec {γ : ℝ} {x : FieldSample} {I : Set ℝ}
    (h : ∃ ν, IsVagueLimitOnR I (bdryApprox γ x) ν) :
    IsVagueLimitOnR I (bdryApprox γ x) (qBoundaryMeasureOn γ x I) := by
  classical
  unfold qBoundaryMeasureOn
  rw [dif_pos h]
  exact h.choose_spec

/-- Left end of the `n`-th exhausting interval of the side half-line. -/
def g1z2A (left : Bool) (n : ℕ) : ℝ := if left then -((n : ℝ) + 1) else 0

/-- Right end of the `n`-th exhausting interval of the side half-line. -/
def g1z2B (left : Bool) (n : ℕ) : ℝ := if left then 0 else (n : ℝ) + 1

theorem g1z2_Ioo_subset (left : Bool) (n : ℕ) :
    Ioo (g1z2A left n) (g1z2B left n) ⊆ g1SideHalf left := by
  cases left
  · intro t ht; exact ht.1
  · intro t ht; exact ht.2

theorem g1z2_iUnion_Ioo (left : Bool) :
    (⋃ n, Ioo (g1z2A left n) (g1z2B left n)) = g1SideHalf left := by
  refine subset_antisymm (iUnion_subset fun n => g1z2_Ioo_subset left n) fun t ht => ?_
  cases left
  · have ht' : 0 < t := ht
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact mem_iUnion.2 ⟨n, by
      simp only [g1z2A, g1z2B, Bool.false_eq_true, ite_false, mem_Ioo]; exact ⟨ht', by linarith⟩⟩
  · have ht' : t < 0 := ht
    obtain ⟨n, hn⟩ := exists_nat_gt (-t)
    exact mem_iUnion.2 ⟨n, by
      simp only [g1z2A, g1z2B, ite_true, mem_Ioo]; exact ⟨by linarith, ht'⟩⟩

/-- **Giry-measurability of the side boundary measure.** -/
theorem g1z2_aemeasurable_sideNu {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {left : Bool} {Z : Ω → FieldSample} (hc : AEMeasurable (fun ω => coords (Z ω)) P)
    (hex : ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitOnR (g1SideHalf left) (bdryApprox γ (Z ω)) ν) :
    AEMeasurable (fun ω => g1SideNu γ left (Z ω)) P := by
  set I : ℕ → Set ℝ := fun n => Ioo (g1z2A left n) (g1z2B left n) with hI
  set D : ℕ → Set ℝ := disjointed I with hD
  have hDm : ∀ n, MeasurableSet (D n) := fun n =>
    MeasurableSet.disjointed (fun m => measurableSet_Ioo) n
  set Y' : Ω → FieldSample := fun ω => reconstruct (hc.mk _ ω) with hY'
  have hYm : ∀ μ, Measurable fun ω => Y' ω μ := fun μ =>
    (measurable_pi_apply μ).comp (measurable_reconstruct.comp hc.measurable_mk)
  have hbd : ∀ᵐ ω ∂P, bdryApprox γ (Y' ω) = bdryApprox γ (Z ω) := by
    filter_upwards [hc.ae_eq_mk] with ω hω
    have havg : avgReg (Y' ω) = avgReg (Z ω) := by
      simp only [hY']
      rw [← hω]
      exact avgReg_reconstruct_coords (Z ω)
    funext k
    unfold bdryApprox
    rw [havg]
  have hexn : ∀ n, ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitOnR (Ioo (g1z2A left n) (g1z2B left n))
      (bdryApprox γ (Y' ω)) ν := fun n => by
    filter_upwards [hex, hbd] with ω ⟨ν, hν⟩ hb
    rw [hb]
    exact ⟨_, g1z2_isVagueLimitOnR_restrict hν isOpen_Ioo (g1z2_Ioo_subset left n)⟩
  have hM : ∀ n, AEMeasurable (fun ω => qBoundaryMeasureOn γ (Y' ω) (I n)) P := fun n =>
    Prop16Area.G.aemeasurable_qBoundaryMeasureOn_Ioo_of_ae hYm (hexn n)
  set G : Ω → Measure ℝ := fun ω => Measure.sum fun n => ((hM n).mk _ ω).restrict (D n) with hG
  have hGm : Measurable G := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [hG, Measure.sum_apply _ hs]
    refine Measurable.ennreal_tsum fun n => ?_
    simp only [Measure.restrict_apply hs]
    exact (Measure.measurable_coe (hs.inter (hDm n))).comp (hM n).measurable_mk
  refine ⟨G, hGm, ?_⟩
  have hmk : ∀ᵐ ω ∂P, ∀ n, qBoundaryMeasureOn γ (Y' ω) (I n) = (hM n).mk _ ω :=
    ae_all_iff.2 fun n => (hM n).ae_eq_mk
  filter_upwards [hex, hbd, hmk] with ω hω hb hmkω
  have hspec := g1z2_qBoundaryMeasureOn_spec hω
  set ν := qBoundaryMeasureOn γ (Z ω) (g1SideHalf left) with hν
  have hn : ∀ n, (hM n).mk _ ω = ν.restrict (I n) := fun n => by
    rw [← hmkω n]
    refine LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo ?_
    rw [hb]
    exact g1z2_isVagueLimitOnR_restrict hspec isOpen_Ioo (g1z2_Ioo_subset left n)
  show ν = G ω
  simp only [hG, hn]
  have hself : ν = ν.restrict (g1SideHalf left) :=
    (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 (show ν {a | a ∉ g1SideHalf left} = 0 from hspec.1))).symm
  have hU : (⋃ n, D n) = g1SideHalf left := by
    rw [hD, iUnion_disjointed]; exact g1z2_iUnion_Ioo left
  conv_lhs => rw [hself, ← hU, Measure.restrict_iUnion (disjoint_disjointed I) hDm]
  congr 1
  funext n
  rw [Measure.restrict_restrict_of_subset (disjointed_subset I n)]

end Thm18Asm
end QuantumZipper
