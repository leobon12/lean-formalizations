import QuantumZipper.Proofs.Zipper.FieldLawler3CrossId
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-SYM (1): harmonic measure of a boundary arc through a uniformization onto `ℍ`

Towards the symmetry of the excursion flux `ℰ_Ω(A, B) = ℰ_Ω(B, A)` (Field–Lawler, EJP 20 (2015),
§2, p. 5; Lawler, *Conformally Invariant Processes in the Plane*, AMS 2005, Def. 5.7 and (5.10),
p. 105, with conformal invariance Prop. 5.8 and Remark 5.9, p. 105). Lawler reduces a simply
connected domain to `ℍ` by a conformal map; we do the same analytically.

`FL3Unif Ω F` records what a conformal map `F : Ω → ℍ` with a Carathéodory extension gives
(holomorphic, `Ω → ℍ`, continuous on `Ω̄`, real and injective on `∂Ω`, `F → ∞` at `∞`); neither
injectivity on `Ω` nor surjectivity is needed here.

`fl3Sym_harm_eq`: a harmonic measure `ω` in `Ω` of the arc `B = ∂Ω ∩ F⁻¹(c, d)` equals
`fl3IntHarm c d ∘ F` (Lindelöf maximum principle `fl2_harm_le_zero_off_finite` with the at most two
exceptional points `F⁻¹{c, d} ∩ ∂Ω`), as in the proof of `fl3_isHarmMeas_eq`. Own routine
transport argument (the conformal invariance of harmonic measure used by Lawler, loc. cit.).
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- A uniformization of `Ω` into `ℍ` with boundary correspondence. -/
structure FL3Unif (Ω : Set ℂ) (F : ℂ → ℂ) : Prop where
  isOpen : IsOpen Ω
  holo : DifferentiableOn ℂ F Ω
  mapsTo : MapsTo F Ω H
  cont : ContinuousOn F (closure Ω)
  bdry_real : ∀ z ∈ frontier Ω, (F z).im = 0
  bdry_inj : InjOn F (frontier Ω)
  infty : Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 (closure Ω)) (Bornology.cobounded ℂ)

/-- The boundary arc `∂Ω ∩ F⁻¹(c, d)`. -/
def fl3SymArc (Ω : Set ℂ) (F : ℂ → ℂ) (c d : ℝ) : Set ℂ :=
  frontier Ω ∩ F ⁻¹' (((↑) : ℝ → ℂ) '' Ioo c d)

variable {Ω : Set ℂ} {F : ℂ → ℂ}

theorem fl3Sym_tendsto (hF : FL3Unif Ω F) {x₀ : ℂ} (hx₀ : x₀ ∈ closure Ω) :
    Tendsto F (𝓝[Ω] x₀) (𝓝[H] (F x₀)) :=
  tendsto_nhdsWithin_iff.2 ⟨((hF.cont x₀ hx₀).mono_left (nhdsWithin_mono _ subset_closure)),
    eventually_nhdsWithin_of_forall fun _ hy => hF.mapsTo hy⟩

theorem fl3Sym_arc_sub (c d : ℝ) : closure (fl3SymArc Ω F c d) ⊆ closure Ω := by
  refine closure_minimal ?_ isClosed_closure
  exact fun z hz => frontier_subset_closure hz.1

theorem fl3Sym_closure_arc (hF : FL3Unif Ω F) {c d : ℝ} {x₀ : ℂ}
    (hx : x₀ ∈ closure (fl3SymArc Ω F c d)) : c ≤ (F x₀).re ∧ (F x₀).re ≤ d := by
  have h1 := (hF.cont.mono (fl3Sym_arc_sub c d)).image_closure ⟨x₀, hx, rfl⟩
  have hS : IsClosed {z : ℂ | c ≤ z.re ∧ z.re ≤ d} :=
    (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)
  refine hS.closure_subset_iff.2 ?_ h1
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨t, ht, he⟩ := hz.2
  rw [← he]
  simp only [mem_ofPred_eq, ofReal_re]
  exact ⟨ht.1.le, ht.2.le⟩

theorem fl3Sym_closure_compl (hF : FL3Unif Ω F) {c d : ℝ} {x₀ : ℂ}
    (hx : x₀ ∈ closure (frontier Ω \ fl3SymArc Ω F c d)) :
    (F x₀).re ≤ c ∨ d ≤ (F x₀).re := by
  have hsub : closure (frontier Ω \ fl3SymArc Ω F c d) ⊆ closure Ω :=
    closure_minimal (fun z hz => frontier_subset_closure hz.1) isClosed_closure
  have h1 := (hF.cont.mono hsub).image_closure ⟨x₀, hx, rfl⟩
  have hS : IsClosed {z : ℂ | z.re ≤ c ∨ d ≤ z.re} :=
    (isClosed_le Complex.continuous_re continuous_const).union
      (isClosed_le continuous_const Complex.continuous_re)
  refine hS.closure_subset_iff.2 ?_ h1
  rintro _ ⟨z, ⟨hz, hzB⟩, rfl⟩
  simp only [mem_ofPred_eq]
  by_contra hcon
  push Not at hcon
  exact hzB ⟨hz, ⟨(F z).re, hcon, Complex.ext (by simp) (by simp [hF.bdry_real z hz])⟩⟩

theorem fl3Sym_arc_bdd (hF : FL3Unif Ω F) (c d : ℝ) :
    Bornology.IsBounded (fl3SymArc Ω F c d) := by
  set K : Set ℂ := closedBall 0 (|c| + |d|)
  have hK : Kᶜ ∈ Bornology.cobounded ℂ := isBounded_closedBall
  have h := mem_inf_principal.1 (hF.infty hK)
  refine (Bornology.isBounded_def.2 (by rw [compl_compl]; exact h)).subset ?_
  rintro _ ⟨hz, t, ht, he⟩
  simp only [mem_compl_iff, mem_ofPred_eq, mem_preimage, not_imp, not_not]
  refine ⟨frontier_subset_closure hz, ?_⟩
  rw [← he, mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs]
  rcases le_total 0 t with h0 | h0
  · rw [abs_of_nonneg h0]; linarith [ht.2, le_abs_self d, abs_nonneg c]
  · rw [abs_of_nonpos h0]; linarith [ht.1, neg_abs_le c, abs_nonneg d]

theorem fl3Sym_tendsto_infty (hF : FL3Unif Ω F) :
    Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 Ω) (Bornology.cobounded ℂ ⊓ 𝓟 H) :=
  tendsto_inf.2 ⟨hF.infty.mono_left (inf_le_inf_left _ (principal_mono.2 subset_closure)),
    tendsto_principal.2 (mem_inf_of_right (mem_principal.2 hF.mapsTo))⟩

theorem fl3Sym_eps_of_tendsto {f : ℂ → ℝ} {x₀ : ℂ} (hf : Tendsto f (𝓝[Ω] x₀) (𝓝 0)) :
    ∀ ε > 0, ∃ δ > 0, ∀ y ∈ Ω, dist y x₀ < δ → f y ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhdsWithin_nhds.1 hf ε hε
  refine ⟨δ, hδ, fun y hy hd => ?_⟩
  have := h hy hd
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

theorem fl3Sym_R_of_tendsto {f : ℂ → ℝ}
    (hf : Tendsto f (Bornology.cobounded ℂ ⊓ 𝓟 Ω) (𝓝 0)) :
    ∀ ε > 0, ∃ R, ∀ y ∈ Ω, R ≤ ‖y‖ → f y ≤ ε := by
  intro ε hε
  have hev : ∀ᶠ y in Bornology.cobounded ℂ ⊓ 𝓟 Ω, f y < ε := hf (Iio_mem_nhds hε)
  rw [Filter.eventually_inf_principal] at hev
  obtain ⟨r, -, hr⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 hev
  refine ⟨r + 1, fun y hy hR => (hr ?_ hy).le⟩
  simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
  linarith

theorem fl3Sym_harm_comp (hF : FL3Unif Ω F) {c d : ℝ} (hcd : c < d) :
    InnerProductSpace.HarmonicOnNhd (fun p => fl3IntHarm c d (F p)) Ω := fun _ hz =>
  fl_harmonicAt_comp (h := fl3IntHarm c d) (hF.holo.analyticAt (hF.isOpen.mem_nhds hz))
    (fl3IntHarm_harm hcd _ (hF.mapsTo hz))

/-- **Conformal transport of the harmonic measure of a boundary arc**: every harmonic measure of
`B = ∂Ω ∩ F⁻¹(c, d)` in `Ω` equals `fl3IntHarm c d ∘ F`. -/
theorem fl3Sym_harm_eq (hF : FL3Unif Ω F) {c d : ℝ} (hcd : c < d) {ω : ℂ → ℝ}
    (hω : IsHarmMeas Ω (fl3SymArc Ω F c d) ω) : ∀ p ∈ Ω, ω p = fl3IntHarm c d (F p) := by
  set B := fl3SymArc Ω F c d with hBdef
  set g : ℂ → ℝ := fun p => fl3IntHarm c d (F p) with hg
  set Ef : Set ℂ := frontier Ω ∩ F ⁻¹' {(c : ℂ), (d : ℂ)} with hEf
  have hEfin : Ef.Finite := by
    refine Set.Finite.of_finite_image ((Set.toFinite ({(c : ℂ), (d : ℂ)} : Set ℂ)).subset ?_)
      (hF.bdry_inj.mono inter_subset_left)
    rintro _ ⟨z, hz, rfl⟩
    exact hz.2
  set E : Finset ℂ := hEfin.toFinset
  have hlim : ∀ x₀ ∈ frontier Ω, x₀ ∉ (E : Set ℂ) →
      Tendsto (fun y => ω y - g y) (𝓝[Ω] x₀) (𝓝 0) := by
    intro x₀ hx₀ hE
    have hre : F x₀ = ((F x₀).re : ℂ) := Complex.ext (by simp) (by simp [hF.bdry_real x₀ hx₀])
    set x := (F x₀).re
    have hxc : x ≠ c := fun e => hE (by
      rw [Set.Finite.coe_toFinset]; exact ⟨hx₀, by simp [hre, e]⟩)
    have hxd : x ≠ d := fun e => hE (by
      rw [Set.Finite.coe_toFinset]; exact ⟨hx₀, by simp [hre, e]⟩)
    have hT : Tendsto F (𝓝[Ω] x₀) (𝓝[H] (x : ℂ)) := by
      rw [← hre]; exact fl3Sym_tendsto hF (frontier_subset_closure hx₀)
    by_cases hin : x ∈ Ioo c d
    · have hxB : x₀ ∈ B := ⟨hx₀, x, hin, hre.symm⟩
      have hncl : x₀ ∉ closure (frontier Ω \ B) := fun hm => by
        rcases fl3Sym_closure_compl hF hm with h1 | h1
        · exact absurd hin.1 (not_lt.2 h1)
        · exact absurd hin.2 (not_lt.2 h1)
      have := (hω.one x₀ hxB hncl).sub ((fl3IntHarm_tendsto_one hcd hin).comp hT)
      rwa [sub_self] at this
    · have hout : x < c ∨ d < x := by
        simp only [mem_Ioo, not_and_or, not_lt] at hin
        rcases hin with h1 | h1
        · exact Or.inl (lt_of_le_of_ne h1 hxc)
        · exact Or.inr (lt_of_le_of_ne h1 (Ne.symm hxd))
      have hncl : x₀ ∉ closure B := fun hm => by
        have := fl3Sym_closure_arc hF hm
        rcases hout with h1 | h1
        · exact absurd this.1 (not_le.2 h1)
        · exact absurd this.2 (not_le.2 h1)
      have := (hω.zero x₀ hx₀ hncl).sub ((fl3IntHarm_tendsto_zero hcd hout).comp hT)
      rwa [sub_self] at this
  have hinf : Tendsto (fun y => ω y - g y) (Bornology.cobounded ℂ ⊓ 𝓟 Ω) (𝓝 0) := by
    have hg0 : Tendsto g (Bornology.cobounded ℂ ⊓ 𝓟 Ω) (𝓝 0) :=
      (fl3IntHarm_tendsto_infty (c := c) (d := d)).comp (fl3Sym_tendsto_infty hF)
    have := (hω.infty (fl3Sym_arc_bdd hF c d)).sub hg0
    rwa [sub_self] at this
  have hgm : ∀ y ∈ Ω, 0 ≤ g y ∧ g y ≤ 1 := fun y hy => fl3IntHarm_mem01 hcd (hF.mapsTo hy)
  have h1 : ∀ y ∈ Ω, ω y - g y ≤ 0 :=
    fl2_harm_le_zero_off_finite E hF.isOpen (hω.harm.sub (fl3Sym_harm_comp hF hcd))
      ⟨1, by rintro _ ⟨y, hy, rfl⟩; linarith [(hω.mem01 y hy).2, (hgm y hy).1]⟩
      (fun x₀ hx₀ hE => fl3Sym_eps_of_tendsto (hlim x₀ hx₀ hE)) (fl3Sym_R_of_tendsto hinf)
  have h2 : ∀ y ∈ Ω, g y - ω y ≤ 0 := by
    refine fl2_harm_le_zero_off_finite E hF.isOpen ((fl3Sym_harm_comp hF hcd).sub hω.harm)
      ⟨1, by rintro _ ⟨y, hy, rfl⟩; linarith [(hω.mem01 y hy).1, (hgm y hy).2]⟩
      (fun x₀ hx₀ hE => fl3Sym_eps_of_tendsto ?_) (fl3Sym_R_of_tendsto ?_)
    · have := (hlim x₀ hx₀ hE).neg
      simpa [neg_sub] using this
    · have := hinf.neg
      simpa [neg_sub] using this
  intro p hp
  linarith [h1 p hp, h2 p hp]

end FieldLawler
end QuantumZipper
