import QuantumZipper.Proofs.Thm18.ASep3Fam
import QuantumZipper.Proofs.Thm18.ASepBoxData
import QuantumZipper.Proofs.Thm18.ASepFreeOpen
import QuantumZipper.Proofs.Thm18.ASepPathDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 6): the parameter set with the scale, and `GenFam` on its rational boxes

* `ScaleGood W d r`: parameters `q = (τ, a, s)` with `(τ, a)` good (`GoodSet`) and `s > 0`;
  open (`isOpen_scaleGood`);
* `ratBox_eq_dilSet`: a rational box in `ℝⁿ⁺¹` is the dilated set of its first `n` coordinates;
* **`genFam_scaleBox`**: on every nonempty rational box inside `ScaleGood`, the dilated A-sep
  family with a dyadic radius cap is a `GenFam` (from `genFam_muA0_dil`, box data `boxData_A0`).

These are the parameter-set inputs of the scale run of the engine (`ae_tendsto_open_depShift`,
ASep3Engine.lean). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open GenUC

/-- Good parameters with a positive scale. -/
def ScaleGood (W : ℝ → ℝ) (d : ℂ) (r : ℝ) : Set (Fin 3 → ℝ) :=
  {q | Fin.init q ∈ GoodSet W d r ∧ 0 < q (Fin.last 2)}

theorem isOpen_scaleGood (W : ℝ → ℝ) (d : ℂ) (r : ℝ) : IsOpen (ScaleGood W d r) := by
  have hR : (0 : ℝ) ≤ ‖d‖ + |r| := by positivity
  have hK : foldSph d r ⊆ closedBall 0 (‖d‖ + |r|) := fun x hx => by
    rw [mem_closedBall, dist_zero_right]
    exact (norm_le_of_mem_foldSph hx).trans (by linarith [le_abs_self r])
  have hU : IsOpen (GoodSet W d r) := isOpen_parGood hR hK
  have hinit : Continuous (fun q : Fin 3 → ℝ => Fin.init q) :=
    continuous_pi fun i => continuous_apply _
  exact (hU.preimage hinit).inter (isOpen_lt continuous_const (continuous_apply _))

theorem ratBox_eq_dilSet {n : ℕ} (a b : Fin (n + 1) → ℚ) :
    ratBox a b = dilSet (ratBox (Fin.init a) (Fin.init b)) (a (Fin.last n)) (b (Fin.last n)) := by
  ext q
  simp only [ratBox, dilSet, Set.mem_pi, mem_univ, true_implies, Set.mem_setOf_eq, Fin.init]
  constructor
  · intro h
    exact ⟨fun i => h i.castSucc, h (Fin.last n)⟩
  · rintro ⟨h1, h2⟩ i
    induction i using Fin.lastCases with
    | last => exact h2
    | cast j => exact h1 j

/-- **`GenFam` on a rational box of good scaled parameters.** -/
theorem genFam_scaleBox {W : ℝ → ℝ} (hWg : DrvGood W) {d : ℂ} (hd : d ∈ Hbar) {r : ℝ}
    (hr : 0 < r) {a b : Fin 3 → ℚ} (hsub : ratBox a b ⊆ ScaleGood W d r)
    (hne : (ratBox a b).Nonempty) :
    ∃ m₀ : ℕ, ∃ K c : ℝ,
      GenFam (ratBox a b) (dilFam fun p ρ => muA0 W d r p (radius m₀ * ρ)) 1 K c := by
  obtain ⟨hW, hW0, hHol, -⟩ := hWg
  obtain ⟨q₀, hq₀⟩ := hne
  have hab : ∀ i, (a i : ℝ) ≤ b i := fun i => (hq₀ i (mem_univ i)).1.trans (hq₀ i (mem_univ i)).2
  have hsnoc : ∀ p ∈ ratBox (Fin.init a) (Fin.init b), ∀ t : ℝ,
      t ∈ Icc (a (Fin.last 2) : ℝ) (b (Fin.last 2)) → (Fin.snoc p t : Fin 3 → ℝ) ∈ ratBox a b := by
    intro p hp t ht
    rw [ratBox_eq_dilSet]
    refine ⟨?_, ?_⟩
    · show Fin.init (Fin.snoc p t : Fin 3 → ℝ) ∈ _
      rw [Fin.init_snoc]; exact hp
    · show (Fin.snoc p t : Fin 3 → ℝ) (Fin.last 2) ∈ _
      rw [Fin.snoc_last]; exact ht
  have hSsub : ratBox (Fin.init a) (Fin.init b) ⊆ {p | ParGood W (foldSph d r) p} := by
    intro p hp
    have := (hsub (hsnoc p hp _ ⟨le_rfl, hab _⟩)).1
    rw [Fin.init_snoc] at this
    exact this
  have hSne : (ratBox (Fin.init a) (Fin.init b)).Nonempty := by
    refine ⟨Fin.init q₀, ?_⟩
    have := (ratBox_eq_dilSet a b ▸ hq₀ : q₀ ∈ dilSet _ _ _)
    exact this.1
  obtain ⟨T, a₀, a₁, δ, hT, ha₀, hδ, -, hSb, hgood, -⟩ := boxData_A0 hr hSsub hSne
  obtain ⟨α, CH, hα, hα1, hCH, hH⟩ := hHol T hT
  obtain ⟨m₀, hm₀⟩ := genFam_muA0_dil hW hW0 hT hα hα1 hCH hH hd hr ha₀
    (isCompact_ratBox _ _) (fun p hp => ⟨(hSb p hp).1, (hSb p hp).2.1⟩) hδ hgood
  have hs₀ : (0 : ℝ) < a (Fin.last 2) := by
    obtain ⟨p, hp⟩ := hSne
    have := (hsub (hsnoc p hp _ ⟨le_rfl, hab _⟩)).2
    rw [Fin.snoc_last] at this
    exact this
  obtain ⟨K, c, hF⟩ := hm₀ _ (b (Fin.last 2)) hs₀
  exact ⟨m₀, K, c, by rw [ratBox_eq_dilSet]; exact hF⟩

end ASep
end QuantumZipper
