import QuantumZipper.Proofs.Zipper.FieldLawler3WdHarm
import QuantumZipper.Proofs.Zipper.FieldLawler3Sym

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-WD (Sym): the excursion-flux symmetry in a bounded domain

`fl3Wd_excR_symm`: `fl3Sym_excR_symm'` for a bounded domain `D`, through the Möbius image
`T_p(D)` (`T_p z = 1/(z - p)`, `p ∈ ∂D` away from both arcs), which is where `FL3Unif` can hold
(`fl3Wd_not_FL3Unif_of_bounded`, `fl3Wd_FL3Unif_of_car`). Charts are transported by `T_p`
(`fl3Wd_arc`) and harmonic measures by `T_p⁻¹` (`fl3Wd_isHarmMeas`).

Source: symmetry of the excursion measure (Lawler, *Conformally Invariant Processes in the
Plane*, 2005, Def. 5.7, Prop. 5.8, Remark 5.9, p. 105), which is stated for any domain; the
Möbius transport is routine (own elementary argument).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

variable {p : ℂ} {D : Set ℂ}

lemma fl3WdTi_T' (z : ℂ) : fl3WdTi p (fl3WdT p z) = z := by
  simp [fl3WdT, fl3WdTi]

/-- **Transport of an arc chart by `T_p`.** -/
theorem fl3Wd_arc {R₀ : ℝ} (hDo : IsOpen D) (hDb : D ⊆ ball 0 R₀) (hne : D.Nonempty)
    (hpD : p ∉ D) {ψ : ℂ → ℂ} {J : Set ℝ} (hA : FL3Arc D ψ J) (hpJ : ∀ x ∈ J, ψ x ≠ p) :
    FL3Arc (fl3WdT p '' D) (fun z => fl3WdT p (ψ z)) J := by
  have hfr := fl3Wd_frontierT hDo hDb hne hpD
  refine ⟨hA.meas, fun x hx => ?_, fun x hx y hy h => hA.inj hx hy
    (fl3WdT_inj (hpJ x hx) (hpJ y hy) h)⟩
  obtain ⟨r, hr, hd, hmap, hreal⟩ := hA.chart x hx
  have hcont : ContinuousAt ψ (x : ℂ) :=
    (hd.differentiableAt (ball_mem_nhds _ hr)).continuousAt
  obtain ⟨r', hr', hr'sub⟩ := Metric.isOpen_iff.1
    (hd.continuousOn.isOpen_inter_preimage isOpen_ball (isOpen_compl_singleton : IsOpen ({p}ᶜ : Set ℂ)))
    (x : ℂ) ⟨mem_ball_self hr, hpJ x hx⟩
  refine ⟨r', hr', fun z hz => ?_, fun z hz => ?_, fun z hz hzim => ?_⟩
  · have hz' := hr'sub hz
    exact (((hd.differentiableAt (isOpen_ball.mem_nhds hz'.1)).sub_const p).inv
      (sub_ne_zero.2 hz'.2)).differentiableWithinAt
  · exact ⟨ψ z, hmap ⟨hz.1, (hr'sub hz.2).1⟩, rfl⟩
  · have hz' := hr'sub hz
    rw [hfr]
    exact ⟨ψ z, ⟨hreal z hz'.1 hzim, hz'.2⟩, rfl⟩

/-- **Excursion-flux symmetry in a bounded domain** (via `T_p`). -/
theorem fl3Wd_excR_symm {R₀ : ℝ} (hDo : IsOpen D) (hDb : D ⊆ ball 0 R₀) (hne : D.Nonempty)
    (hp : p ∈ frontier D) {F : ℂ → ℂ} (hF : FL3Unif (fl3WdT p '' D) F)
    {ψA ψB : ℂ → ℂ} {JA JB : Set ℝ} (hA : FL3Arc D ψA JA) (hB : FL3Arc D ψB JB)
    (hpA : p ∉ closure (ψA '' (((↑) : ℝ → ℂ) '' JA)))
    (hpB : p ∉ closure (ψB '' (((↑) : ℝ → ℂ) '' JB)))
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) (hdisj : b < c ∨ d < a)
    (hIA : (fun x : ℝ => (F (fl3WdT p (ψA x))).re) '' JA = Ioo a b)
    (hIB : (fun x : ℝ => (F (fl3WdT p (ψB x))).re) '' JB = Ioo c d) {ωA ωB : ℂ → ℝ}
    (hωA : IsHarmMeas D (ψA '' (((↑) : ℝ → ℂ) '' JA)) ωA)
    (hωB : IsHarmMeas D (ψB '' (((↑) : ℝ → ℂ) '' JB)) ωB) :
    excR (ωB ∘ ψA) JA = excR (ωA ∘ ψB) JB := by
  have hpD : p ∉ D := fun h => by rw [hDo.frontier_eq] at hp; exact hp.2 h
  have hpJA : ∀ x ∈ JA, ψA x ≠ p := fun x hx e =>
    hpA (e ▸ subset_closure ⟨(x : ℂ), ⟨x, hx, rfl⟩, rfl⟩)
  have hpJB : ∀ x ∈ JB, ψB x ≠ p := fun x hx e =>
    hpB (e ▸ subset_closure ⟨(x : ℂ), ⟨x, hx, rfl⟩, rfl⟩)
  have himg : ∀ (ψ : ℂ → ℂ) (J : Set ℝ), (fun z => fl3WdT p (ψ z)) '' (((↑) : ℝ → ℂ) '' J) =
      fl3WdT p '' (ψ '' (((↑) : ℝ → ℂ) '' J)) := fun ψ J => by
    exact (image_image _ _ _).symm
  have hA' := fl3Wd_isHarmMeas hDo hDb hne hp hpA hωA
  have hB' := fl3Wd_isHarmMeas hDo hDb hne hp hpB hωB
  rw [← himg] at hA' hB'
  have := fl3Sym_excR_symm' hF (fl3Wd_arc hDo hDb hne hpD hA hpJA)
    (fl3Wd_arc hDo hDb hne hpD hB hpJB) hab hcd hdisj hIA hIB hA' hB'
  have e1 : ((fun w => ωB (fl3WdTi p w)) ∘ fun z => fl3WdT p (ψA z)) = ωB ∘ ψA := by
    funext z; simp only [Function.comp_apply, fl3WdTi_T']
  have e2 : ((fun w => ωA (fl3WdTi p w)) ∘ fun z => fl3WdT p (ψB z)) = ωA ∘ ψB := by
    funext z; simp only [Function.comp_apply, fl3WdTi_T']
  rwa [e1, e2] at this

end FieldLawler
end QuantumZipper
