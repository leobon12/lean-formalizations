import QuantumZipper.Proofs.Zipper.FieldLawler4L33
import QuantumZipper.Proofs.Zipper.FieldLawlerSubSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM round 4: the positive half of `FLImageSumBoundStmt` from the per-arc chain

`fl4_pos_sum`: in the setting of `FLImageSumBoundStmt`, for the crosscuts with positive feet, if
each one satisfies the per-arc inequality `excR (h j) (Iic 0) ≤ fl2FluxR R g` (for every harmonic
measure `g` of its preimage arc in `D₁ \ arc`; this is Field–Lawler's chain on p. 9: symmetry,
(2.1), symmetry), then the sum is `≤ ofReal (128 π ε / R) · ofReal π` (Lemma 3.3 + (2.4),
`fl4_lemma33_loewner`). Own bookkeeping (finite partial sums of the `tsum`).
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

theorem fl4_fwdMapInv_injOn {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : InjOn (fwdMapInv W t) H := fun p hp q hq e => by
  rw [← RS.fwdMap_fwdMapInv hW hW0 ht hp, ← RS.fwdMap_fwdMapInv hW hW0 ht hq, e]

theorem fl4_pos_sum {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {t R ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hR : 4 * ε ≤ R)
    (htr0 : trace W 0 = 0) (hcont : ContinuousOn (trace W) (Icc 0 t))
    (hH : ∀ s ∈ Ioc 0 t, trace W s ∈ H) (hhull : fwdHull W t = trace W '' Ioc 0 t)
    (hγR : ∀ s ∈ Ico 0 t, ‖trace W s‖ < R) (hγt : ‖trace W t‖ = R)
    (S : Set ℕ) (η : ℕ → ℝ → ℂ) (h : ℕ → ℂ → ℝ)
    (hS : ∀ j ∈ S, arcH (η j) ⊆ H)
    (hdisj : S.PairwiseDisjoint (fun j => arcH (η j)))
    (hdata : ∀ j ∈ S, ∃ α β : ℝ, (0 ≤ α ∧ α < β ∧ β < π) ∧
      fwdMapInv W t '' arcH (η j) = flCircArc ε α β ∧
      ((ε : ℂ) * exp (α * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} ∧
        (ε : ℂ) * exp (β * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re}) ∧
      flCircArc ε α β ⊆ H \ trace W '' Ioc 0 t)
    (hper : ∀ j ∈ S, ∀ (α β : ℝ) (g : ℂ → ℝ), fwdMapInv W t '' arcH (η j) = flCircArc ε α β →
      IsHarmMeas (fl4D₁ W t R \ flCircArc ε α β) (flCircArc ε α β) g →
      excR (h j) (Iic 0) ≤ fl2FluxR R g) :
    ∑' j, S.indicator (fun j => excR (h j) (Iic 0)) j ≤
      ENNReal.ofReal (128 * π * ε / R) * ENNReal.ofReal π := by
  classical
  have hεR : ε < R := by linarith
  -- choose the angles
  have hdata' : ∀ j, ∃ α β : ℝ, j ∈ S → ((0 ≤ α ∧ α < β ∧ β < π) ∧
      fwdMapInv W t '' arcH (η j) = flCircArc ε α β ∧
      ((ε : ℂ) * exp (α * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} ∧
        (ε : ℂ) * exp (β * I) ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re}) ∧
      flCircArc ε α β ⊆ H \ trace W '' Ioc 0 t) := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨α, β, hab⟩ := hdata j hj
      exact ⟨α, β, fun _ => hab⟩
    · exact ⟨0, 0, fun h => absurd h hj⟩
  choose α β hαβ using hdata'
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  set F' := F.filter (· ∈ S) with hF'
  have hsum : ∑ j ∈ F, S.indicator (fun j => excR (h j) (Iic 0)) j =
      ∑ j ∈ F', excR (h j) (Iic 0) := by
    rw [hF', Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j ∈ S
    · rw [indicator_of_mem hj, if_pos hj]
    · rw [indicator_of_notMem hj, if_neg hj]
  rw [hsum]
  have hF'S : ∀ j ∈ F', j ∈ S := fun j hj => (Finset.mem_filter.1 hj).2
  -- harmonic measures of the single arcs
  have hg : ∀ j ∈ F', ∃ g : ℂ → ℝ,
      IsHarmMeas (fl4D₁ W t R \ flCircArc ε (α j) (β j)) (flCircArc ε (α j) (β j)) g := by
    intro j hj
    obtain ⟨hab, -, hend, harc⟩ := hαβ j (hF'S j hj)
    obtain ⟨g, hg⟩ := flExist_loewner_arcs_trace hW hW0 ht hε hεR htr0 hcont hH hhull hγR hγt
      ({j} : Finset ℕ) (α := α) (β := β) (fun i hi => by
        rw [Finset.mem_singleton.1 hi]; exact hab.2.1.le)
      (fun i hi => by
        rw [Finset.mem_singleton.1 hi]
        exact ⟨hend.1.elim Or.inl (fun h => Or.inr h.1), hend.2.elim Or.inl (fun h => Or.inr h.1)⟩)
      (fun i hi => by rw [Finset.mem_singleton.1 hi]; exact harc)
    refine ⟨g, ?_⟩
    have e : (⋃ i ∈ ({j} : Finset ℕ), flCircArc ε (α i) (β i)) = flCircArc ε (α j) (β j) := by
      simp
    rw [e] at hg
    exact hg
  have hg' : ∀ j, ∃ g : ℂ → ℝ, j ∈ F' →
      IsHarmMeas (fl4D₁ W t R \ flCircArc ε (α j) (β j)) (flCircArc ε (α j) (β j)) g := by
    intro j
    by_cases hj : j ∈ F'
    · obtain ⟨g, hg⟩ := hg j hj; exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => 0, fun h => absurd h hj⟩
  choose g hgm using hg'
  have hstep : ∑ j ∈ F', excR (h j) (Iic 0) ≤ ∑ j ∈ F', fl2FluxR R (g j) :=
    Finset.sum_le_sum fun j hj =>
      hper j (hF'S j hj) (α j) (β j) (g j) (hαβ j (hF'S j hj)).2.1 (hgm j hj)
  refine hstep.trans ?_
  -- reindex by `Fin n`
  set e := F'.equivFin with he
  have hre : ∑ j ∈ F', fl2FluxR R (g j) = ∑ k : Fin F'.card, fl2FluxR R (g (e.symm k)) := by
    rw [← Finset.sum_coe_sort F']
    exact (Equiv.sum_comp e.symm (fun j : F' => fl2FluxR R (g j))).symm
  rw [hre]
  have hmemF : ∀ k : Fin F'.card, ((e.symm k : F') : ℕ) ∈ F' := fun k => (e.symm k).2
  refine fl4_lemma33_loewner hW hW0 ht hε hR htr0 hcont hH hhull hγR hγt
    (α := fun k => α (e.symm k)) (β := fun k => β (e.symm k))
    (fun k => (hαβ _ (hF'S _ (hmemF k))).1) (fun k => (hαβ _ (hF'S _ (hmemF k))).2.2.1)
    (fun k => (hαβ _ (hF'S _ (hmemF k))).2.2.2) ?_ (fun k => hgm _ (hmemF k))
  -- disjointness of the preimage arcs
  intro i k hik
  have hne : ((e.symm i : F') : ℕ) ≠ ((e.symm k : F') : ℕ) := fun h =>
    hik (e.symm.injective (Subtype.ext h))
  have hd := hdisj (hF'S _ (hmemF i)) (hF'S _ (hmemF k)) hne
  rw [← (hαβ _ (hF'S _ (hmemF i))).2.1, ← (hαβ _ (hF'S _ (hmemF k))).2.1]
  have hinj := fl4_fwdMapInv_injOn hW hW0 ht
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
  have := hinj (hS _ (hF'S _ (hmemF k)) hq) (hS _ (hF'S _ (hmemF i)) hp) hpq
  subst this
  exact Set.disjoint_left.1 hd hp hq

end FieldLawler
end QuantumZipper
