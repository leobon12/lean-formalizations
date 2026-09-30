import QuantumZipper.Proofs.Zipper.FieldLawler3SymHarm
import QuantumZipper.Proofs.Zipper.FieldLawler3Refl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-SYM (2): symmetry of the excursion flux between two boundary arcs

For a uniformization `F : Ω → ℍ` (`FL3Unif`, `FieldLawler3SymHarm.lean`) and two boundary arcs
given by analytic charts `ψ_A, ψ_B` on real sets `J_A, J_B` (`FL3Arc`) with `F(A) = (a, b)`,
`F(B) = (c, d)`, `b < c`, the fluxes of the harmonic measures agree:
`excR (ω_B ∘ ψ_A) J_A = excR (ω_A ∘ ψ_B) J_B` (`fl3Sym_excR_symm`).

Source: symmetry of the Brownian excursion measure `μ_D(Γ₁, Γ₂)` (Lawler, *Conformally Invariant
Processes in the Plane*, AMS 2005, Def. 5.7, (5.10), Prop. 5.8 and Remark 5.9, p. 105;
Field–Lawler, EJP 20 (2015), §2, p. 5), proved as Lawler does by conformal invariance to `ℍ`:
1. `ω_B = fl3IntHarm c d ∘ F` (`fl3Sym_harm_eq`);
2. `excR (ω_B ∘ ψ_A) J_A = excR (fl3IntHarm c d) (a, b)` (`fl3Sym_excR_chart`): Schwarz reflection
   of `F ∘ ψ_A` (`fl3Refl_arc_pos`), glued into one function `fl3Glue`, has real positive
   derivative on `J_A`, and `lwHarm_excR_comp` (Lawler §5.2) changes variables;
3. the explicit symmetry `fl3_excR_symm` in `ℍ`.
-/

noncomputable section

open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal ComplexConjugate

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- An analytic boundary arc chart: `ψ` is holomorphic near each point of the real set `J`, maps
the upper half of a disc into `Ω` and its real diameter into `∂Ω`, and is injective on `J`. -/
structure FL3Arc (Ω : Set ℂ) (ψ : ℂ → ℂ) (J : Set ℝ) : Prop where
  meas : MeasurableSet J
  chart : ∀ x ∈ J, ∃ r > 0, DifferentiableOn ℂ ψ (ball (x : ℂ) r) ∧
    MapsTo ψ (H ∩ ball (x : ℂ) r) Ω ∧ ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ψ z ∈ frontier Ω
  inj : InjOn (fun x : ℝ => ψ x) J

/-- `yDer` only sees the values on a vertical segment above `x`. -/
theorem fl3Sym_yDer_congr {h₁ h₂ : ℂ → ℝ} {x ε : ℝ} (hε : 0 < ε)
    (heq : ∀ y ∈ Ioo 0 ε, h₁ ((x : ℂ) + (y : ℂ) * I) = h₂ ((x : ℂ) + (y : ℂ) * I)) :
    yDer h₁ x = yDer h₂ x := by
  have hev : (fun y : ℝ => h₁ ((x : ℂ) + (y : ℂ) * I) / y) =ᶠ[𝓝[>] 0]
      (fun y : ℝ => h₂ ((x : ℂ) + (y : ℂ) * I) / y) := by
    filter_upwards [Ioo_mem_nhdsGT hε] with y hy
    rw [heq y hy]
  have e1 : (∃ L : ℝ, Tendsto (fun y : ℝ => h₁ ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 L)) ↔
      ∃ L : ℝ, Tendsto (fun y : ℝ => h₂ ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 L) :=
    exists_congr fun L => tendsto_congr' hev
  have e2 : limUnder (𝓝[>] (0 : ℝ)) (fun y : ℝ => h₁ ((x : ℂ) + (y : ℂ) * I) / y) =
      limUnder (𝓝[>] (0 : ℝ)) (fun y : ℝ => h₂ ((x : ℂ) + (y : ℂ) * I) / y) := by
    unfold limUnder
    rw [Filter.map_congr hev]
  unfold yDer
  by_cases h : ∃ L : ℝ, Tendsto (fun y : ℝ => h₁ ((x : ℂ) + (y : ℂ) * I) / y) (𝓝[>] 0) (𝓝 L)
  · rw [if_pos h, if_pos (e1.1 h), e2]
  · rw [if_neg h, if_neg (mt e1.2 h)]

/-- `K` on `ℍ̄`, reflected below. -/
def fl3Glue (K : ℂ → ℂ) (z : ℂ) : ℂ := if 0 ≤ z.im then K z else conj (K (conj z))

theorem fl3Glue_of_nonneg (K : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) : fl3Glue K z = K z := if_pos hz

theorem fl3Glue_eqOn {K G : ℂ → ℂ} {x r : ℝ} (hGK : EqOn G K (Hbar ∩ ball (x : ℂ) r))
    (hsym : ∀ z ∈ ball (x : ℂ) r, G (conj z) = conj (G z)) :
    EqOn (fl3Glue K) G (ball (x : ℂ) r) := by
  intro z hz
  unfold fl3Glue
  split_ifs with h
  · exact (hGK ⟨h, hz⟩).symm
  · push Not at h
    have hc : conj z ∈ ball (x : ℂ) r := by
      rw [mem_ball, ← conj_ofReal, dist_conj_conj]; exact hz
    have h1 : conj z ∈ Hbar ∩ ball (x : ℂ) r :=
      ⟨show 0 ≤ (conj z).im by rw [conj_im]; linarith, hc⟩
    rw [← hGK h1, hsym z hz, conj_conj]

/-- A real derivative at `x` of a map sending `x` to `ℝ` and `x + iy` (`y ↓ 0`) into `ℍ` is
nonnegative. -/
theorem fl3Sym_deriv_nonneg {G : ℂ → ℂ} {x d : ℝ} (hG : HasDerivAt G (d : ℂ) (x : ℂ))
    (h0 : (G x).im = 0) (hpos : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), 0 < (G ((x : ℂ) + (y : ℂ) * I)).im) :
    0 ≤ d := by
  set γ : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * I
  have hγ : HasDerivAt γ I 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const I).const_add (x : ℂ)
    simpa [γ] using this
  have hγ0 : γ 0 = x := by simp [γ]
  have hGγ : HasDerivAt (G ∘ γ) ((d : ℂ) * I) 0 := by
    rw [← hγ0] at hG
    exact hG.comp 0 hγ
  have hφ : HasDerivAt (fun t => (G (γ t)).im) d 0 := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hGγ
    have e : Complex.imCLM ((d : ℂ) * I) = d := by simp
    rw [e] at this
    exact this
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (s := Ioi (0 : ℝ)) (by simp)).1
    hφ.hasDerivWithinAt
  refine ge_of_tendsto hs ?_
  filter_upwards [hpos, self_mem_nhdsWithin] with y hy hy0
  rw [slope_def_field, hγ0, h0, sub_zero, sub_zero]
  exact div_nonneg hy.le (le_of_lt hy0)

variable {Ω : Set ℂ} {F : ℂ → ℂ}

theorem fl3IntHarm_real_zero {c d t : ℝ} (hcd : c < d) (ht : t < c ∨ d < t) :
    fl3IntHarm c d (t : ℂ) = 0 := by
  have hpos : 0 ≤ (t - d) / (t - c) := by
    rcases ht with h | h
    · exact (div_pos_of_neg_of_neg (by linarith) (by linarith)).le
    · exact (div_pos (by linarith) (by linarith)).le
  rw [fl3IntHarm_eq_arg, fl3Q_real, arg_ofReal_of_nonneg hpos, zero_div]

theorem fl3IntHarm_real_diff {c d t : ℝ} (hcd : c < d) (ht : t < c ∨ d < t) :
    DifferentiableAt ℝ (fl3IntHarm c d) (t : ℂ) := by
  have h1 := Complex.imCLM.hasFDerivAt.comp (t : ℂ)
    ((fl3_hasDerivAt_F hcd ht).hasFDerivAt.restrictScalars ℝ)
  have h2 := h1.const_smul (π⁻¹ : ℝ)
  have hfe : fl3IntHarm c d = (π⁻¹ : ℝ) • (⇑Complex.imCLM ∘ fl3IntF c d) := by
    funext p
    simp [fl3IntHarm, div_eq_inv_mul, smul_eq_mul]
  rw [hfe]
  exact h2.differentiableAt

/-- **Step 2: the flux into a chart arc of the harmonic measure of `F⁻¹(c, d)`** equals the flux
in `ℍ` of `fl3IntHarm c d` into the image of the arc. -/
theorem fl3Sym_excR_chart (hF : FL3Unif Ω F) {ψ : ℂ → ℂ} {J : Set ℝ} (hA : FL3Arc Ω ψ J)
    {c d : ℝ} (hcd : c < d) (hout : ∀ x ∈ J, (F (ψ x)).re < c ∨ d < (F (ψ x)).re)
    {ω : ℂ → ℝ} (hω : IsHarmMeas Ω (fl3SymArc Ω F c d) ω) :
    excR (ω ∘ ψ) J = excR (fl3IntHarm c d) ((fun x : ℝ => (F (ψ x)).re) '' J) := by
  set G : ℂ → ℂ := fl3Glue (F ∘ ψ) with hGdef
  have hGr : ∀ x : ℝ, G x = F (ψ x) := fun x => fl3Glue_of_nonneg _ (by simp)
  have hfr : ∀ x ∈ J, ψ x ∈ frontier Ω := fun x hx => by
    obtain ⟨r, hr, -, -, h3⟩ := hA.chart x hx
    exact h3 _ (mem_ball_self hr) (by simp)
  have hre : ∀ x ∈ J, (G x).im = 0 := fun x hx => by
    rw [hGr]; exact hF.bdry_real _ (hfr x hx)
  -- local data at each point of `J`
  have hloc : ∀ x ∈ J, ∃ r : ℝ, 0 < r ∧ (∀ y ∈ Ioo 0 r, ψ ((x : ℂ) + (y : ℂ) * I) ∈ Ω) ∧
      HasDerivAt G (((deriv G x).re : ℝ) : ℂ) x ∧ 0 ≤ (deriv G x).re := by
    intro x hx
    obtain ⟨r, hr, hψd, hψΩ, hψfr⟩ := hA.chart x hx
    have hseg : ∀ y ∈ Ioo 0 r, (x : ℂ) + (y : ℂ) * I ∈ H ∩ ball (x : ℂ) r := fun y hy => by
      refine ⟨show (0 : ℝ) < ((x : ℂ) + (y : ℂ) * I).im by simpa using hy.1, ?_⟩
      rw [mem_ball, dist_eq, add_sub_cancel_left, norm_mul, norm_real, norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hy.1]
      exact hy.2
    have hFc : ContinuousOn F (ψ '' (Hbar ∩ ball (x : ℂ) r)) := by
      refine hF.cont.mono ?_
      rintro _ ⟨z, ⟨hz0, hz⟩, rfl⟩
      rcases (show (0 : ℝ) ≤ z.im from hz0).lt_or_eq with h | h
      · exact subset_closure (hψΩ ⟨h, hz⟩)
      · exact frontier_subset_closure (hψfr z hz h.symm)
    obtain ⟨G₀, hG₀d, hG₀eq, hsym, hdreal, -⟩ := fl3Refl_arc_pos hr hψd hψΩ hF.holo hFc
      (by rintro _ ⟨z, ⟨hz, hz0⟩, rfl⟩; exact hF.bdry_real _ (hψfr z hz hz0))
      (fun z hz => hF.mapsTo (hψΩ hz))
    have hEq : EqOn G G₀ (ball (x : ℂ) r) := fl3Glue_eqOn hG₀eq hsym
    have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
    have hD : HasDerivAt G (deriv G₀ x) x :=
      ((hG₀d.differentiableAt (isOpen_ball.mem_nhds hxB)).hasDerivAt).congr_of_eventuallyEq
        (eventuallyEq_of_mem (isOpen_ball.mem_nhds hxB) hEq)
    have hdG : deriv G x = deriv G₀ x := hD.deriv
    have hreal : deriv G₀ x = (((deriv G₀ x).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simpa using hdreal x hxB)
    have hD' : HasDerivAt G (((deriv G x).re : ℝ) : ℂ) x := by rw [hdG, ← hreal]; exact hD
    refine ⟨r, hr, fun y hy => hψΩ (hseg y hy), hD', fl3Sym_deriv_nonneg hD' (hre x hx) ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hr] with y hy
    rw [hGdef, fl3Glue_of_nonneg _ (le_of_lt (hseg y hy).1)]
    exact hF.mapsTo (hψΩ (hseg y hy))
  -- replace `ω ∘ ψ` by `fl3IntHarm c d ∘ G`
  have h1 : excR (ω ∘ ψ) J = excR (fl3IntHarm c d ∘ G) J := by
    unfold excR
    refine setLIntegral_congr_fun hA.meas fun x hx => ?_
    obtain ⟨r, hr, hseg, -, -⟩ := hloc x hx
    rw [fl3Sym_yDer_congr hr (h₂ := fl3IntHarm c d ∘ G) fun y hy => ?_]
    simp only [Function.comp_apply]
    rw [fl3Sym_harm_eq hF hcd hω _ (hseg y hy), hGdef,
      fl3Glue_of_nonneg _ (by simpa using hy.1.le)]
    rfl
  rw [h1, lwHarm_excR_comp hA.meas (d := fun x => (deriv G x).re) (fun x hx => (hloc x hx).choose_spec.2.2.1)
    (fun x hx => (hloc x hx).choose_spec.2.2.2) hre ?_ ?_ ?_]
  · congr 1
    exact image_congr fun x _ => by rw [hGr]
  · intro x hx y hy hxy
    simp only [hGr] at hxy
    have e : F (ψ x) = F (ψ y) := Complex.ext hxy (by
      rw [hF.bdry_real _ (hfr x hx), hF.bdry_real _ (hfr y hy)])
    exact hA.inj hx hy (hF.bdry_inj (hfr x hx) (hfr y hy) e)
  · intro x hx
    rw [show G x = (((G x).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [hre x hx]), hGr]
    exact fl3IntHarm_real_diff hcd (hout x hx)
  · intro x hx
    rw [show G x = (((G x).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [hre x hx]), hGr]
    exact fl3IntHarm_real_zero hcd (hout x hx)

/-- The chart arc `ψ(J)` is the boundary arc `∂Ω ∩ F⁻¹(a, b)` when `F ∘ ψ` maps `J` onto `(a, b)`. -/
theorem fl3Sym_arc_eq (hF : FL3Unif Ω F) {ψ : ℂ → ℂ} {J : Set ℝ} (hA : FL3Arc Ω ψ J) {a b : ℝ}
    (hI : (fun x : ℝ => (F (ψ x)).re) '' J = Ioo a b) :
    ψ '' (((↑) : ℝ → ℂ) '' J) = fl3SymArc Ω F a b := by
  have hfr : ∀ x ∈ J, ψ x ∈ frontier Ω := fun x hx => by
    obtain ⟨r, hr, -, -, h3⟩ := hA.chart x hx
    exact h3 _ (mem_ball_self hr) (by simp)
  have hreal : ∀ z ∈ frontier Ω, F z = (((F z).re : ℝ) : ℂ) := fun z hz =>
    Complex.ext (by simp) (by simp [hF.bdry_real z hz])
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨hfr x hx, (F (ψ x)).re, ?_, (hreal _ (hfr x hx)).symm⟩
    rw [← hI]
    exact ⟨x, hx, rfl⟩
  · rintro ⟨hz, t, ht, he⟩
    rw [← hI] at ht
    obtain ⟨x, hx, hxt⟩ := ht
    refine ⟨x, ⟨x, hx, rfl⟩, hF.bdry_inj (hfr x hx) hz ?_⟩
    rw [hreal _ (hfr x hx), ← he]
    exact congrArg _ hxt

/-- **Symmetry of the excursion flux between two boundary arcs** (Lawler, *Conformally Invariant
Processes in the Plane*, Def. 5.7, (5.10), Prop. 5.8, p. 105; Field–Lawler, EJP 20 (2015), §2,
p. 5): for disjoint arcs `A = ψ_A(J_A)`, `B = ψ_B(J_B)` with `F(A) = (a, b)`, `F(B) = (c, d)`,
`b < c`, `excR (ω_B ∘ ψ_A) J_A = excR (ω_A ∘ ψ_B) J_B`. -/
theorem fl3Sym_excR_symm (hF : FL3Unif Ω F) {ψA ψB : ℂ → ℂ} {JA JB : Set ℝ}
    (hA : FL3Arc Ω ψA JA) (hB : FL3Arc Ω ψB JB) {a b c d : ℝ} (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hIA : (fun x : ℝ => (F (ψA x)).re) '' JA = Ioo a b)
    (hIB : (fun x : ℝ => (F (ψB x)).re) '' JB = Ioo c d) {ωA ωB : ℂ → ℝ}
    (hωA : IsHarmMeas Ω (ψA '' (((↑) : ℝ → ℂ) '' JA)) ωA)
    (hωB : IsHarmMeas Ω (ψB '' (((↑) : ℝ → ℂ) '' JB)) ωB) :
    excR (ωB ∘ ψA) JA = excR (ωA ∘ ψB) JB := by
  rw [fl3Sym_arc_eq hF hA hIA] at hωA
  rw [fl3Sym_arc_eq hF hB hIB] at hωB
  have hmA : ∀ x ∈ JA, (F (ψA x)).re ∈ Ioo a b := fun x hx => by rw [← hIA]; exact ⟨x, hx, rfl⟩
  have hmB : ∀ x ∈ JB, (F (ψB x)).re ∈ Ioo c d := fun x hx => by rw [← hIB]; exact ⟨x, hx, rfl⟩
  rw [fl3Sym_excR_chart hF hA hcd (fun x hx => Or.inl ((hmA x hx).2.trans hbc)) hωB,
    fl3Sym_excR_chart hF hB hab (fun x hx => Or.inr (hbc.trans (hmB x hx).1)) hωA, hIA, hIB]
  exact fl3_excR_symm hab hbc hcd

/-- `fl3Sym_excR_symm` for two disjoint image intervals in either order. -/
theorem fl3Sym_excR_symm' (hF : FL3Unif Ω F) {ψA ψB : ℂ → ℂ} {JA JB : Set ℝ}
    (hA : FL3Arc Ω ψA JA) (hB : FL3Arc Ω ψB JB) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hdisj : b < c ∨ d < a) (hIA : (fun x : ℝ => (F (ψA x)).re) '' JA = Ioo a b)
    (hIB : (fun x : ℝ => (F (ψB x)).re) '' JB = Ioo c d) {ωA ωB : ℂ → ℝ}
    (hωA : IsHarmMeas Ω (ψA '' (((↑) : ℝ → ℂ) '' JA)) ωA)
    (hωB : IsHarmMeas Ω (ψB '' (((↑) : ℝ → ℂ) '' JB)) ωB) :
    excR (ωB ∘ ψA) JA = excR (ωA ∘ ψB) JB := by
  rcases hdisj with h | h
  · exact fl3Sym_excR_symm hF hA hB hab h hcd hIA hIB hωA hωB
  · exact (fl3Sym_excR_symm hF hB hA hcd h hab hIB hIA hωB hωA).symm

end FieldLawler
end QuantumZipper
