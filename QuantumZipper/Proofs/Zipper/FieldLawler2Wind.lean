import QuantumZipper.Proofs.Zipper.FieldLawlerSubSepWind

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL2-WIND: a symmetric path cannot separate two points of a connected set

Topological core of Field–Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
§4, proof of Prop. 4.1, p. 10: "On the event `E_x ∩ Ē_x`, the path `B[0,σ_η] ∪ conj(B[0,σ_η])`
lies entirely within `D`, but separates one endpoint of `η` from the other. But this is
impossible, as the two endpoints of `η` lie in the same connected component of `D^c`."

Field–Lawler state the separation without proof. We make it precise with the winding index
(Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §2.1, p. 116: the index is constant off the loop;
`flSepIdx_eventuallyEq`). Own elementary argument for the parity: for a path `γ` from the real
point `x` to the real point `y`, let `Γ = γ ⋆ conj(γ)⁻¹`. For a real `r` off `γ`, a continuous
logarithm `L` of `γ - r` gives the logarithm `L ⋆ (conj L + c)⁻¹` of `Γ - r`, so the index `n`
of `Γ` about `r` satisfies `Im(L 1 - L 0) = nπ`, and hence
`y - r = (x - r) · e^R · cos(nπ)` (`fl2Wind_real_idx`). The sign of `cos(nπ)` is therefore
negative for `r ∈ (x, y)` and positive for `r ∉ [x, y]`, while the index is constant on a
connected set avoiding `Γ`.
-/

noncomputable section

open Set Complex ComplexConjugate
open scoped Real

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.CA.Topo

/-- The reflected path `conj ∘ γ`, still from `x` to `y` (real endpoints). -/
def fl2WindConj {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) : Path (x : ℂ) (y : ℂ) :=
  (γ.map Complex.continuous_conj).cast (by simp) (by simp)

theorem fl2WindConj_apply {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) (t : unitInterval) :
    fl2WindConj γ t = conj (γ t) := rfl

/-- The closed loop `Γ = γ ⋆ (conj ∘ γ)⁻¹`. -/
def fl2WindLoop {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) : C(unitInterval, ℂ) :=
  (γ.trans (fl2WindConj γ).symm).toContinuousMap

theorem fl2WindLoop_apply {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) (t : unitInterval) :
    fl2WindLoop γ t = (γ.trans (fl2WindConj γ).symm) t := rfl

theorem fl2WindLoop_closed {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) :
    fl2WindLoop γ 0 = fl2WindLoop γ 1 := by
  rw [fl2WindLoop_apply, fl2WindLoop_apply, Path.source, Path.target]

/-- Every point of the loop is a point of `γ` or of its reflection. -/
theorem fl2WindLoop_mem {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) (t : unitInterval) :
    ∃ s, fl2WindLoop γ t = γ s ∨ fl2WindLoop γ t = conj (γ s) := by
  rw [fl2WindLoop_apply, Path.trans_apply]
  split_ifs
  · exact ⟨_, Or.inl rfl⟩
  · exact ⟨_, Or.inr (by rw [Path.symm_apply, Function.comp_apply, fl2WindConj_apply])⟩

/-- **Parity of the index about a real point.** -/
theorem fl2Wind_real_idx {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) {r : ℝ}
    (hr : ∀ t, γ t ≠ r) :
    ∃ R : ℝ, y - r = (x - r) * (Real.exp R * Real.cos (flSepIdx (fl2WindLoop γ) r * π)) := by
  set g : C(unitInterval, ℂ) := ⟨fun t => γ t - r, by fun_prop⟩ with hg
  have hg0 : ∀ t, g t ≠ 0 := fun t => sub_ne_zero.2 (hr t)
  obtain ⟨L, hL⟩ := exists_lift_exp g hg0
  have hL' : ∀ t, Complex.exp (L t) = γ t - r := hL
  set c : ℂ := L 1 - conj (L 1) with hc
  have hc1 : Complex.exp c = 1 := by
    rw [hc, Complex.exp_sub, Complex.exp_conj, hL', Path.target]
    have : ((y : ℂ) - r) ≠ 0 := by
      have := hr 1; rw [Path.target] at this; exact sub_ne_zero.2 this
    rw [show conj ((y : ℂ) - r) = (y : ℂ) - r by simp [map_sub]]
    exact div_self this
  -- the lift of `Γ - r`
  let P : Path (L 0) (L 1) := ⟨L, rfl, rfl⟩
  let Q₀ : Path (conj (L 0) + c) (conj (L 1) + c) :=
    ⟨⟨fun t => conj (L t) + c, by fun_prop⟩, rfl, rfl⟩
  let Q : Path (L 1) (conj (L 0) + c) := Q₀.symm.cast (by rw [hc]; ring) rfl
  have hΓ : ∀ t, fl2WindLoop γ t ≠ r := by
    intro t h
    obtain ⟨s, hs | hs⟩ := fl2WindLoop_mem γ t
    · exact hr s (hs ▸ h)
    · apply hr s
      rw [hs] at h
      simpa using congrArg conj h
  have hne : ∀ t, flSepShift (fl2WindLoop γ) r t ≠ 0 := fun t => sub_ne_zero.2 (hΓ t)
  have hexp : ∀ t, Complex.exp ((P.trans Q) t) = flSepShift (fl2WindLoop γ) r t := by
    intro t
    show _ = fl2WindLoop γ t - r
    rw [fl2WindLoop_apply, Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hL' _
    · rw [Path.symm_apply, Function.comp_apply, fl2WindConj_apply, Path.cast_coe,
        Path.symm_apply, Function.comp_apply]
      show Complex.exp (conj (L _) + c) = _
      rw [Complex.exp_add, hc1, mul_one, Complex.exp_conj, hL']
      simp [map_sub]
  have hdeg := loopDeg_eq_of_lift _ hne (by simp [flSepShift, fl2WindLoop_closed])
    (P.trans Q).continuous hexp
  rw [Path.source, Path.target, ← flSepIdx_eq _ hne] at hdeg
  set n := flSepIdx (fl2WindLoop γ) r
  -- imaginary part: `Im (L 1 - L 0) = n π`
  have him : (L 1 - L 0).im = n * π := by
    have := congrArg Complex.im hdeg
    simp [hc] at this
    rw [Complex.sub_im]
    linarith
  refine ⟨(L 1 - L 0).re, ?_⟩
  have h0 : Complex.exp (L 0) = (x : ℂ) - r := by rw [hL', Path.source]
  have h1 : Complex.exp (L 1) = (y : ℂ) - r := by rw [hL', Path.target]
  have hmul : (y : ℂ) - r = ((x : ℂ) - r) * Complex.exp (L 1 - L 0) := by
    rw [← h0, ← h1, ← Complex.exp_add]; ring_nf
  have := congrArg Complex.re hmul
  rw [Complex.mul_re, Complex.exp_re, him] at this
  simpa using this

/-- **Field–Lawler 2015, Prop. 4.1, p. 10 (topological step).** A path `γ` in `D` from the real
point `x` to the real point `y`, whose reflection also lies in `D`, cannot have a connected set
`K` disjoint from `D` meet the real line both inside `(x, y)` and outside `[x, y]`. -/
theorem fl2_symm_path_absurd {D K : Set ℂ} {x y : ℝ} (γ : Path (x : ℂ) (y : ℂ)) {e e' : ℝ}
    (hγ : ∀ t, γ t ∈ D) (hγc : ∀ t, conj (γ t) ∈ D)
    (hK : IsConnected K) (hKD : Disjoint K D) (he : (e : ℂ) ∈ K) (he' : (e' : ℂ) ∈ K)
    (hxey : x < e ∧ e < y) (he'out : e' < x ∨ y < e') : False := by
  set Γ := fl2WindLoop γ
  have hoff : ∀ z ∈ K, ∀ t, Γ t ≠ z := by
    intro z hz t h
    obtain ⟨s, hs | hs⟩ := fl2WindLoop_mem γ t
    · exact hKD.ne_of_mem hz (hγ s) (h ▸ hs)
    · exact hKD.ne_of_mem hz (hγc s) (h ▸ hs)
  have hconst : flSepIdx Γ e = flSepIdx Γ e' := by
    refine hK.isPreconnected.constant (f := flSepIdx Γ) (fun w hw => ?_) he he'
    exact (continuousAt_const.congr ((flSepIdx_eventuallyEq Γ (fl2WindLoop_closed γ)
      (hoff w hw)).mono fun _ hy => hy.symm)).continuousWithinAt
  have hr : ∀ r : ℝ, (r : ℂ) ∈ K → ∀ t, γ t ≠ r := fun r hr t h =>
    hKD.ne_of_mem hr (hγ t) h.symm
  obtain ⟨R, hR⟩ := fl2Wind_real_idx γ (hr e he)
  obtain ⟨R', hR'⟩ := fl2Wind_real_idx γ (hr e' he')
  rw [hconst] at hR
  set cs := Real.cos (flSepIdx Γ e' * π)
  have hE := Real.exp_pos R
  have hE' := Real.exp_pos R'
  -- `e ∈ (x, y)`: `cs < 0`
  have hneg : cs < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hE.le h]
  rcases he'out with h | h
  · nlinarith [mul_neg_of_pos_of_neg hE' hneg]
  · nlinarith [mul_neg_of_pos_of_neg hE' hneg]

end FieldLawler
end QuantumZipper
