import HigherDimLQGContinuity.Core.Interfaces
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Hölder constants on a subset of Euclidean space

This is the dimension-independent form of the functional used in the
planar GaussianLQG library, with the exponent as a parameter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)

/-- The `β`-Hölder constant of a pair function on `K`, in `[0, ∞]`. -/
def holderConstRd {d : ℕ} (F : Rd d × Rd d → ℝ) (K : Set (Rd d)) (β : ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ K, ⨆ y ∈ K, ⨆ (_ : x ≠ y), ENNReal.ofReal (F (x, y) / ‖x - y‖ ^ β)

/-- Every off-diagonal pair contributes to the Hölder constant. -/
theorem ofReal_div_le_holderConstRd {d : ℕ} (F : Rd d × Rd d → ℝ) {K : Set (Rd d)}
    {β : ℝ} {x y : Rd d} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) :
    ENNReal.ofReal (F (x, y) / ‖x - y‖ ^ β) ≤ holderConstRd F K β :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

/-- A paired-index form of the Hölder constant. -/
theorem holderConstRd_eq_biSup_pairs {d : ℕ} (F : Rd d × Rd d → ℝ)
    (K : Set (Rd d)) (β : ℝ) :
    holderConstRd F K β =
      ⨆ p ∈ {p : Rd d × Rd d | p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 ≠ p.2},
        ENNReal.ofReal (F p / ‖p.1 - p.2‖ ^ β) := by
  unfold holderConstRd
  refine le_antisymm (iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_)
    (iSup₂_le fun p hp => ?_)
  · exact le_iSup₂ (f := fun (p : Rd d × Rd d)
      (_ : p ∈ {p : Rd d × Rd d | p.1 ∈ K ∧ p.2 ∈ K ∧ p.1 ≠ p.2}) =>
      ENNReal.ofReal (F p / ‖p.1 - p.2‖ ^ β)) (x, y) ⟨hx, hy, hxy⟩
  · exact le_iSup₂_of_le p.1 hp.1 (le_iSup₂_of_le p.2 hp.2.1
      (le_iSup_of_le hp.2.2 le_rfl))

private theorem n5_biSup_eq_of_dense {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hTS : T ⊆ S) (hST : S ⊆ closure T) {F : X → ℝ≥0∞} (hF : ContinuousOn F S) :
    ⨆ x ∈ S, F x = ⨆ x ∈ T, F x := by
  refine le_antisymm (iSup₂_le fun x hx => ?_) (biSup_mono hTS)
  have h1 : F x ∈ closure (F '' T) := ((hF x hx).mono hTS).mem_closure_image (hST hx)
  have h2 : F '' T ⊆ Iic (⨆ y ∈ T, F y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact le_iSup₂ (f := fun y (_ : y ∈ T) => F y) y hy
  exact closure_minimal h2 isClosed_Iic h1

private theorem n5_measurable_biSup {X β : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace β] (S : Set X)
    {G : β → X → ℝ≥0∞} (hG : ∀ b, ContinuousOn (G b) S)
    (hGm : ∀ x, Measurable fun b => G b x) :
    Measurable fun b => ⨆ x ∈ S, G b x := by
  obtain ⟨T, hTc, hTS, hST⟩ := TopologicalSpace.exists_countable_dense_subset S
  have h : (fun b => ⨆ x ∈ S, G b x) = fun b => ⨆ x ∈ T, G b x :=
    funext fun b => n5_biSup_eq_of_dense hTS hST (hG b)
  rw [h]
  exact Measurable.biSup T hTc fun x _ => hGm x

/-- Measurability of the Hölder functional on the space of continuous pair functions. -/
theorem measurable_holderConstRd_cont {d : ℕ} (K : Set (Rd d)) (β : ℝ) :
    Measurable fun F : C(Rd d × Rd d, ℝ) => holderConstRd F K β := by
  simp_rw [holderConstRd_eq_biSup_pairs]
  refine n5_measurable_biSup _ (fun F => ?_)
    fun p => ENNReal.measurable_ofReal.comp ((ContinuousMap.measurable_eval p).div_const _)
  refine ENNReal.continuous_ofReal.comp_continuousOn
    (ContinuousOn.div F.continuous.continuousOn ?_ fun p hp => ?_)
  · exact (Continuous.continuousOn (by fun_prop)).rpow_const fun p hp => Or.inl (norm_pos_iff.mpr (sub_ne_zero.mpr hp.2.2)).ne'
  · exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp.2.2)) _).ne'

end HigherDimLQGContinuity
