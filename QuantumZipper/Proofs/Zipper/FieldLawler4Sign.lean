import QuantumZipper.Proofs.Zipper.FieldLawler4ArcEnd
import QuantumZipper.Proofs.Zipper.FieldLawler2Circ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL4-SIGN (S2): which end points an image crosscut with feet of one sign can have

Task FL4-SIGN (Track A round 4). For the boundary extension `F` of `Z_t⁻¹` of a simple curve
(`SideCtx` + injectivity of the trace):

* `fl4sign_F_pos`, `fl4sign_F_neg`: `F` maps `(0, ∞)` into `γ ∪ [0, ∞)` and `(-∞, 0)` into
  `γ ∪ (-∞, 0]` (no real point of the wrong sign). Proof: `F` agrees on `ℍ̄` with the
  Carathéodory extension of `flTop_ctx` (both continuous on `ℍ̄ = closure ℍ`, equal on `ℍ`), whose
  real-line structure is `CaraR.revExt_real_outside` / `CaraR.revExt_structure_S` (Pommerenke,
  *Boundary Behaviour of Conformal Maps* (1992), Prop. 2.5, Thm 2.6, pp. 23–24).
* `fl4sign_ends_pos`, `fl4sign_ends_neg`: for the arc `(α, β)` of `fl4_arc_chart`, positive feet
  force `β < π` and end points in `γ[0,t] ∪ {Im ≤ 0, Re ≥ 0}`; negative feet force `0 < α` and
  end points in `γ[0,t] ∪ {Im ≤ 0, Re ≤ 0}`.
* `fl4sign_arc_subset`: `ηD ⊆ ℍ \ γ(0,t]`.

Source: Field–Lawler, EJP 20 (2015), proof of Prop. 3.4, p. 9 (the arcs `ηⱼ` with feet in
`ℝ₊`, resp. `ℝ₋`, used without comment). Own elementary bookkeeping on top of the cited
boundary-correspondence facts.
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

variable {W : ℝ → ℝ} {t : ℝ} {F : ℂ → ℂ}

/-- The real-line structure of `F`: there are `a₀ < 0 < b₀` with `F(a₀,b₀) ⊆ ℍ`,
`F a₀ = F b₀ = 0`, `F` real negative left of `a₀` and real positive right of `b₀`. -/
theorem fl4sign_struct (hc : SideCtx W t F) (hinj : InjOn (trace W) (Icc 0 t)) :
    ∃ a₀ b₀ : ℝ, a₀ < 0 ∧ 0 < b₀ ∧ F a₀ = 0 ∧ F b₀ = 0 ∧ (∀ x ∈ Ioo a₀ b₀, F x ∈ H) ∧
      (∀ x : ℝ, x < a₀ → (F x).im = 0 ∧ (F x).re < 0) ∧
      (∀ x : ℝ, b₀ < x → (F x).im = 0 ∧ 0 < (F x).re) := by
  have ht := hc.tpos
  have htrH : ∀ s ∈ Ioc 0 t, trace W s ∈ H := fun s hs => by
    have : trace W s ∈ fwdHull W t := by rw [hc.hull]; exact ⟨s, hs, rfl⟩
    exact this.1
  obtain ⟨F', hc', hF'⟩ := flTop_ctx hc.cont hc.zero ht hc.tr0 hc.trCont hinj htrH hc.hull
  -- `F = F'` on `ℍ̄`
  have hcl : Hbar ⊆ closure H := by
    rw [show closure H = Hbar from Complex.closure_setOfPred_lt_im 0]
  have hEq : EqOn F F' Hbar :=
    Set.EqOn.of_subset_closure (hc.Feq.trans hc'.Feq.symm) hc.Fcont hc'.Fcont
      (fun z (hz : 0 < z.im) => show 0 ≤ z.im from hz.le) hcl
  have hR : ∀ x : ℝ, F x = F' x := fun x => hEq (show (0 : ℝ) ≤ (x : ℂ).im by simp)
  -- the simple-curve data for the time-reversed driver
  set γ : ℝ → ℂ := fun s => trace W (t * s) with hγdef
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, t * s ∈ Icc 0 t := fun s hs =>
    ⟨mul_nonneg ht.le hs.1, mul_le_of_le_one_right ht.le hs.2⟩
  have hγc : ContinuousOn γ (Icc 0 1) :=
    hc.trCont.comp (continuousOn_const.mul continuousOn_id) hmem
  have hγi : InjOn γ (Icc 0 1) := fun a ha b hb h =>
    mul_left_cancel₀ ht.ne' (hinj (hmem a ha) (hmem b hb) h)
  have hγ0 : (γ 0).im = 0 := by simp [hγdef, hc.tr0]
  have hγH : ∀ u ∈ Ioc (0 : ℝ) 1, γ u ∈ H := fun u hu =>
    htrH _ ⟨mul_pos ht hu.1, mul_le_of_le_one_right ht.le hu.2⟩
  have himg : γ '' Ioc 0 1 = trace W '' Ioc 0 t := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨t * s, ⟨mul_pos ht hs.1, mul_le_of_le_one_right ht.le hs.2⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r / t, ⟨div_pos hr.1 ht, (div_le_one ht).2 hr.2⟩, by
        simp only [hγdef, mul_div_cancel₀ _ ht.ne']⟩
  have hK : revHull (ArcDriver.trev W t) t = γ '' Ioc 0 1 := by
    rw [ArcDriver.revHull_trev hc.cont hc.zero ht, hc.hull, himg]
  have hW' := ArcDriver.continuous_trev hc.cont t
  have hW0' := ArcDriver.trev_zero W t
  have hγ00 := CaraR.arc_base_eq_zero hW' hW0' ht hγc hγH hK
  have htip := CaraR.revExt_zero_eq_tip CaraR.extExists hW' hW0' ht hγc hγi hγ0 hγH hK hF'
  obtain ⟨a, b, -, -, hS⟩ := CaraR.swallowedSet_eq_Icc hW' hW0' ht.le
  obtain ⟨ha0, hb0, ha, hb⟩ :=
    CaraR.revExt_ends CaraR.extExists hW' hW0' ht hγc hγi hγ0 hγH hK hF' htip hS
  obtain ⟨hleft, hright, htop, hbot⟩ := CaraR.revExt_real_outside hW' hW0' ht hF' hS
  obtain ⟨hmid, -, -, -⟩ :=
    CaraR.revExt_structure_S hγc hγi hγH hF' hγ00 htip ha0 hb0 ha hb hleft hright htop hbot
  refine ⟨a, b, ha0, hb0, by rw [hR]; exact ha, by rw [hR]; exact hb, fun x hx => ?_,
    fun x hx => by rw [hR]; exact hleft x hx, fun x hx => by rw [hR]; exact hright x hx⟩
  obtain ⟨s, hs, hsx⟩ := hmid x hx
  rw [hR, ← hsx]
  exact hγH s hs

/-- `F` maps positive reals into `ℍ ∪ [0, ∞)`: no negative real value. -/
theorem fl4sign_F_pos (hc : SideCtx W t F) (hinj : InjOn (trace W) (Icc 0 t)) {x : ℝ}
    (hx : 0 < x) : ¬ ((F x).im = 0 ∧ (F x).re < 0) := by
  obtain ⟨a₀, b₀, ha₀, -, -, hb, hmid, -, hright⟩ := fl4sign_struct hc hinj
  rintro ⟨him, hre⟩
  rcases lt_trichotomy x b₀ with h | h | h
  · have : (0 : ℝ) < (F x).im := hmid x ⟨ha₀.trans hx, h⟩
    linarith
  · subst h; rw [hb] at hre; simp at hre
  · linarith [(hright x h).2]

/-- `F` maps negative reals into `ℍ ∪ (-∞, 0]`: no positive real value. -/
theorem fl4sign_F_neg (hc : SideCtx W t F) (hinj : InjOn (trace W) (Icc 0 t)) {x : ℝ}
    (hx : x < 0) : ¬ ((F x).im = 0 ∧ 0 < (F x).re) := by
  obtain ⟨a₀, b₀, -, hb₀, ha, -, hmid, hleft, -⟩ := fl4sign_struct hc hinj
  rintro ⟨him, hre⟩
  rcases lt_trichotomy x a₀ with h | h | h
  · linarith [(hleft x h).2]
  · subst h; rw [ha] at hre; simp at hre
  · have : (0 : ℝ) < (F x).im := hmid x ⟨h, hx.trans hb₀⟩
    linarith

lemma fl4sign_flCirc_pi (ε : ℝ) : flCirc ε π = -(ε : ℂ) := by
  simp [flCirc, Complex.exp_pi_mul_I]

lemma fl4sign_flCirc_zero (ε : ℝ) : flCirc ε 0 = (ε : ℂ) := by
  simp [flCirc]

/-- **(S2a) Positive feet.** For the arc `(α, β)` and end points of `fl4_arc_chart`, if both
feet are positive then `β < π` and both end points lie in `γ[0,t] ∪ {Im ≤ 0, Re ≥ 0}`. -/
theorem fl4sign_ends_pos (hc : SideCtx W t F) (hinj : InjOn (trace W) (Icc 0 t)) {ε α β : ℝ}
    (hε : 0 < ε) (h0α : 0 ≤ α) (hαβ : α < β) (hβπ : β ≤ π)
    (hαD : flCirc ε α ∉ H \ fwdHull W t) (hβD : flCirc ε β ∉ H \ fwdHull W t) {a b : ℝ}
    (hfeet : (F a = flCirc ε α ∧ F b = flCirc ε β) ∨ (F a = flCirc ε β ∧ F b = flCirc ε α))
    (ha : 0 < a) (hb : 0 < b) :
    β < π ∧ flCirc ε α ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} ∧
      flCirc ε β ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} := by
  -- every end point is `F` of a positive foot
  have hfoot : ∀ θ, θ = α ∨ θ = β → ∃ x : ℝ, 0 < x ∧ F x = flCirc ε θ := by
    rintro θ (rfl | rfl) <;> rcases hfeet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    exacts [⟨a, ha, h1⟩, ⟨b, hb, h2⟩, ⟨b, hb, h2⟩, ⟨a, ha, h1⟩]
  have hend : ∀ θ, θ = α ∨ θ = β → flCirc ε θ ∉ H \ fwdHull W t →
      flCirc ε θ ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ 0 ≤ z.re} := by
    intro θ hθ hD
    have hθI : θ ∈ Icc 0 π := by
      rcases hθ with rfl | rfl
      exacts [⟨h0α, hαβ.le.trans hβπ⟩, ⟨h0α.trans hαβ.le, hβπ⟩]
    obtain ⟨x, hx, hFx⟩ := hfoot θ hθ
    rcases fl4_end_mem hc hε hθI hD with h | h
    · exact Or.inl (image_mono Ioc_subset_Icc_self h)
    · refine Or.inr ⟨le_of_eq h, not_lt.1 fun hre => fl4sign_F_pos hc hinj hx ?_⟩
      rw [hFx]; exact ⟨h, hre⟩
  refine ⟨lt_of_le_of_ne hβπ fun hβ => ?_, hend α (Or.inl rfl) hαD, hend β (Or.inr rfl) hβD⟩
  obtain ⟨x, hx, hFx⟩ := hfoot β (Or.inr rfl)
  refine fl4sign_F_pos hc hinj hx ?_
  rw [hFx, hβ, fl4sign_flCirc_pi]
  simp [hε]

/-- **(S2b) Negative feet.** Mirror of `fl4sign_ends_pos`: `0 < α` and both end points lie in
`γ[0,t] ∪ {Im ≤ 0, Re ≤ 0}`. -/
theorem fl4sign_ends_neg (hc : SideCtx W t F) (hinj : InjOn (trace W) (Icc 0 t)) {ε α β : ℝ}
    (hε : 0 < ε) (h0α : 0 ≤ α) (hαβ : α < β) (hβπ : β ≤ π)
    (hαD : flCirc ε α ∉ H \ fwdHull W t) (hβD : flCirc ε β ∉ H \ fwdHull W t) {a b : ℝ}
    (hfeet : (F a = flCirc ε α ∧ F b = flCirc ε β) ∨ (F a = flCirc ε β ∧ F b = flCirc ε α))
    (ha : a < 0) (hb : b < 0) :
    0 < α ∧ flCirc ε α ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} ∧
      flCirc ε β ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} := by
  have hfoot : ∀ θ, θ = α ∨ θ = β → ∃ x : ℝ, x < 0 ∧ F x = flCirc ε θ := by
    rintro θ (rfl | rfl) <;> rcases hfeet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    exacts [⟨a, ha, h1⟩, ⟨b, hb, h2⟩, ⟨b, hb, h2⟩, ⟨a, ha, h1⟩]
  have hend : ∀ θ, θ = α ∨ θ = β → flCirc ε θ ∉ H \ fwdHull W t →
      flCirc ε θ ∈ trace W '' Icc 0 t ∪ {z : ℂ | z.im ≤ 0 ∧ z.re ≤ 0} := by
    intro θ hθ hD
    have hθI : θ ∈ Icc 0 π := by
      rcases hθ with rfl | rfl
      exacts [⟨h0α, hαβ.le.trans hβπ⟩, ⟨h0α.trans hαβ.le, hβπ⟩]
    obtain ⟨x, hx, hFx⟩ := hfoot θ hθ
    rcases fl4_end_mem hc hε hθI hD with h | h
    · exact Or.inl (image_mono Ioc_subset_Icc_self h)
    · refine Or.inr ⟨le_of_eq h, not_lt.1 fun hre => fl4sign_F_neg hc hinj hx ?_⟩
      rw [hFx]; exact ⟨h, hre⟩
  refine ⟨lt_of_le_of_ne h0α fun hα => ?_, hend α (Or.inl rfl) hαD, hend β (Or.inr rfl) hβD⟩
  obtain ⟨x, hx, hFx⟩ := hfoot α (Or.inl rfl)
  refine fl4sign_F_neg hc hinj hx ?_
  rw [hFx, ← hα, fl4sign_flCirc_zero]
  simp [hε]

/-- The `D`-arc of an image crosscut lies in `ℍ \ γ(0,t]`. -/
theorem fl4sign_arc_subset (hc : SideCtx W t F) {ε α β : ℝ} {η : ℝ → ℂ} (hη : IsCrosscutH η)
    (hηD : fwdMapInv W t '' arcH η = flCircArc ε α β) :
    flCircArc ε α β ⊆ H \ trace W '' Ioc 0 t := by
  rw [← hηD, ← hc.hull]
  rintro _ ⟨p, ⟨s, hs, rfl⟩, rfl⟩
  have hp : η s ∈ H := hη.2.2.1 hs
  rw [← hc.Feq hp]
  exact hc.F_mem_dom hp

end FieldLawler
end QuantumZipper
