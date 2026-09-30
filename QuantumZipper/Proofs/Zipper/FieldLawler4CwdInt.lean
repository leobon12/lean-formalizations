import QuantumZipper.Proofs.Zipper.FieldLawler3SymHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-CWD (C2): boundary arcs go to intervals under a uniformization

Task FL4-CWD. If `F` uniformizes `Ω` (`FL3Unif`), and `ψ` is continuous and injective on
`[A, B]` with `ψ([A, B]) ⊆ ∂Ω`, then `x ↦ Re F(ψ x)` is continuous and injective on `[A, B]`
(`F` is real and injective on `∂Ω`), hence strictly monotone, and maps `(A, B)` onto an open
interval `(a, b)` and `[A, B]` onto `[a, b]` (`fl4cwd_interval`). Two such arcs with disjoint
closed images give strictly separated intervals (`fl4cwd_interval_sep`), the hypothesis
`hdisj` of `fl3_first_symm` / `fl3Wd_excR_symm`.

Own elementary argument (intermediate value theorem; mathlib
`ContinuousOn.strictMonoOn_of_injOn_Icc'`, `ContinuousOn.image_Ioo_of_strictMonoOn`).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {Ω : Set ℂ} {F : ℂ → ℂ}

lemma fl4cwd_re_inj (hF : FL3Unif Ω F) {z w : ℂ} (hz : z ∈ frontier Ω) (hw : w ∈ frontier Ω)
    (h : (F z).re = (F w).re) : z = w :=
  hF.bdry_inj hz hw (Complex.ext h (by rw [hF.bdry_real z hz, hF.bdry_real w hw]))

/-- **(C2) Interval lemma.** -/
theorem fl4cwd_interval (hF : FL3Unif Ω F) {ψ : ℂ → ℂ} {A B : ℝ} (hAB : A < B)
    (hψc : ContinuousOn (fun x : ℝ => ψ x) (Icc A B))
    (hfr : ∀ x ∈ Icc A B, ψ x ∈ frontier Ω) (hinj : InjOn (fun x : ℝ => ψ x) (Icc A B)) :
    ∃ a b : ℝ, a < b ∧ (fun x : ℝ => (F (ψ x)).re) '' Ioo A B = Ioo a b ∧
      (fun x : ℝ => (F (ψ x)).re) '' Icc A B = Icc a b := by
  set g := fun x : ℝ => (F (ψ x)).re with hg
  have hgc : ContinuousOn g (Icc A B) :=
    continuous_re.comp_continuousOn (hF.cont.comp hψc fun x hx => frontier_subset_closure (hfr x hx))
  have hgi : InjOn g (Icc A B) := fun x hx y hy h => hinj hx hy (fl4cwd_re_inj hF (hfr x hx) (hfr y hy) h)
  rcases hgc.strictMonoOn_of_injOn_Icc' hAB.le hgi with hm | hm
  · exact ⟨g A, g B, hm (left_mem_Icc.2 hAB.le) (right_mem_Icc.2 hAB.le) hAB,
      hgc.image_Ioo_of_strictMonoOn hAB.le hm, hgc.image_Icc_of_monotoneOn hAB.le hm.monotoneOn⟩
  · exact ⟨g B, g A, hm (left_mem_Icc.2 hAB.le) (right_mem_Icc.2 hAB.le) hAB,
      hgc.image_Ioo_of_strictAntiOn hAB.le hm, hgc.image_Icc_of_antitoneOn hAB.le hm.antitoneOn⟩

/-- **(C2) Separation.** Arcs with disjoint closed images give strictly separated intervals. -/
theorem fl4cwd_interval_sep (hF : FL3Unif Ω F) {ψA ψB : ℂ → ℂ} {A B A' B' a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hfrA : ∀ x ∈ Icc A B, ψA x ∈ frontier Ω) (hfrB : ∀ x ∈ Icc A' B', ψB x ∈ frontier Ω)
    (hIA : (fun x : ℝ => (F (ψA x)).re) '' Icc A B = Icc a b)
    (hIB : (fun x : ℝ => (F (ψB x)).re) '' Icc A' B' = Icc c d)
    (hdisj : Disjoint ((fun x : ℝ => ψA x) '' Icc A B) ((fun x : ℝ => ψB x) '' Icc A' B')) :
    b < c ∨ d < a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  set v := max a c
  have hvA : v ∈ Icc a b := ⟨le_max_left _ _, max_le hab.le h1⟩
  have hvB : v ∈ Icc c d := ⟨le_max_right _ _, max_le h2 hcd.le⟩
  rw [← hIA] at hvA; rw [← hIB] at hvB
  obtain ⟨x, hx, hxv⟩ := hvA
  obtain ⟨y, hy, hyv⟩ := hvB
  have e := fl4cwd_re_inj hF (hfrA x hx) (hfrB y hy) (hxv.trans hyv.symm)
  exact Set.disjoint_left.1 hdisj ⟨x, hx, rfl⟩ ⟨y, hy, e.symm⟩

end FieldLawler
end QuantumZipper
