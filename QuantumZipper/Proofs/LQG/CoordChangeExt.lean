import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# M4-T4: a global homeomorphism extending `Re ψ` on `[a, b]`

To write `ψ⁻¹_*` as a pushforward by a continuous map, extend `φ = Re ψ|_{[a,b]}` (continuous,
strictly increasing) to `extR φ a b : ℝ → ℝ`, equal to `φ` on `[a, b]` and of slope `1` outside.
It is a strictly increasing surjection, hence an order isomorphism `extIso` of `ℝ` with a
continuous inverse.
-/

noncomputable section

open Set Filter Topology

namespace QuantumZipper
namespace CoordChange

/-- Clamping into `[a, b]`. -/
def clampI (a b t : ℝ) : ℝ := max a (min t b)

/-- The extension of `φ|_{[a,b]}` with slope `1` outside `[a, b]`. -/
def extR (φ : ℝ → ℝ) (a b : ℝ) (t : ℝ) : ℝ := φ (clampI a b t) + (t - clampI a b t)

variable {a b : ℝ} {φ : ℝ → ℝ}

theorem clampI_mem (hab : a ≤ b) (t : ℝ) : clampI a b t ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem clampI_of_mem {t : ℝ} (ht : t ∈ Icc a b) : clampI a b t = t := by
  unfold clampI; rw [min_eq_left ht.2, max_eq_right ht.1]

theorem clampI_mono (t s : ℝ) (h : t ≤ s) : clampI a b t ≤ clampI a b s :=
  max_le_max le_rfl (min_le_min_right b h)

theorem sub_clampI_eq (hab : a ≤ b) (t : ℝ) :
    t - clampI a b t = max (t - b) 0 + min (t - a) 0 := by
  unfold clampI
  rcases le_total t a with h1 | h1
  · rw [min_eq_left (h1.trans hab), max_eq_left h1, max_eq_right (by linarith),
      min_eq_left (by linarith)]; ring
  · rcases le_total t b with h2 | h2
    · rw [min_eq_left h2, max_eq_right h1, max_eq_right (by linarith), min_eq_right (by linarith)]
      ring
    · rw [min_eq_right h2, max_eq_right hab, max_eq_left (by linarith),
        min_eq_right (by linarith)]; ring

theorem extR_eq {t : ℝ} (ht : t ∈ Icc a b) : extR φ a b t = φ t := by
  unfold extR; rw [clampI_of_mem ht]; ring

theorem continuous_extR (hab : a ≤ b) (hφc : ContinuousOn φ (Icc a b)) :
    Continuous (extR φ a b) := by
  have hcl : Continuous (clampI a b) :=
    continuous_const.max (continuous_id.min continuous_const)
  exact (hφc.comp_continuous hcl (clampI_mem hab)).add (continuous_id.sub hcl)

theorem strictMono_extR (hab : a ≤ b) (hφm : StrictMonoOn φ (Icc a b)) :
    StrictMono (extR φ a b) := by
  intro t s hts
  have hc := clampI_mono (a := a) (b := b) t s hts.le
  have hd : t - clampI a b t ≤ s - clampI a b s := by
    rw [sub_clampI_eq hab, sub_clampI_eq hab]
    exact add_le_add (max_le_max (by linarith) le_rfl) (min_le_min (by linarith) le_rfl)
  unfold extR
  rcases hc.lt_or_eq with hlt | heq
  · have := hφm (clampI_mem hab t) (clampI_mem hab s) hlt
    linarith
  · rw [heq]
    linarith

theorem tendsto_extR_atTop (hab : a ≤ b) : Tendsto (extR φ a b) atTop atTop := by
  have e : ∀ᶠ t in atTop, t + (φ b - b) = extR φ a b t := by
    filter_upwards [eventually_ge_atTop b] with t ht
    unfold extR clampI
    rw [min_eq_right ht, max_eq_right hab]; ring
  exact (tendsto_atTop_add_const_right _ _ tendsto_id).congr' e

theorem tendsto_extR_atBot (hab : a ≤ b) : Tendsto (extR φ a b) atBot atBot := by
  have e : ∀ᶠ t in atBot, t + (φ a - a) = extR φ a b t := by
    filter_upwards [eventually_le_atBot a] with t ht
    unfold extR clampI
    rw [min_eq_left (ht.trans hab), max_eq_left ht]; ring
  exact (tendsto_atBot_add_const_right _ _ tendsto_id).congr' e

theorem surjective_extR (hab : a ≤ b) (hφc : ContinuousOn φ (Icc a b)) :
    Function.Surjective (extR φ a b) :=
  (continuous_extR hab hφc).surjective (tendsto_extR_atTop hab) (tendsto_extR_atBot hab)

/-- The order isomorphism extending `φ|_{[a,b]}`. -/
def extIso (hab : a ≤ b) (hφc : ContinuousOn φ (Icc a b)) (hφm : StrictMonoOn φ (Icc a b)) :
    ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (extR φ a b) (strictMono_extR hab hφm)
    (surjective_extR hab hφc)

theorem extIso_eq (hab : a ≤ b) (hφc : ContinuousOn φ (Icc a b))
    (hφm : StrictMonoOn φ (Icc a b)) {t : ℝ} (ht : t ∈ Icc a b) : extIso hab hφc hφm t = φ t :=
  extR_eq ht

end CoordChange
end QuantumZipper
