/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualTimeChangeBMFrozen
import InteractingSLE.Spec.Sec2.AddMarksGirsanov

/-!
# (D10), IV: the image path is a local force-point evolution (identification)

Packet PROVE-ZHAN-GT4-A11. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L353–L355, R38):
"The time change `du = A²_{j,1} dt_j`, Lévy's characterization, and uniqueness in law of the integrated force system
identify the claimed conditional image law inside this rectangle."

PROVE-ZHAN-GT4-A10 produced, under `Q = (M̃_S/M̃_0)·P`, the Brownian motion `B̂` of the time-changed filtration
`𝓗_u = 𝓕_{C'⁻¹(u)}` (`FrzD10Hyp.isFilteredBrownianReal_bm`) and the force-point equation of the image driver
(`FrzD10Hyp.bmY_invClockT_eq`). Here the image path itself is shown to be a **local integrated `SLE_κ(ρ)` evolution
before `a(S)`** in the sense of `Sec2.IsSLEEvolutionUpTo` (the object to which the localized uniqueness in law of
`Spec/Sec2/AddMarksUnique` applies):

* the image driver `W̃_u = W'(u) − w₀` (`w₀ = W'(0)`, the same for every `ω`: `FrzMartHyp.W'_zero_eq`);
* the image marks `Ṽ_o(u) − w₀`, `Ṽ_o = imgV W' (pos o)`, for the marks `o : Option (Fin n)` — the other tip
  `none ↦ ζ₀` with weight `−κ/2` and the force marks `some m ↦ ζ m` with weights `κ r_m` (`markPos`, `markWt`) —
  sorted into left and right families by an equivalence `e : Fin nL ⊕ Fin nR ≃ Option (Fin n)`;

**`FrzD10Hyp.isSLEEvolutionUpTo_img`**. The path conditions hold for every `ω`: the real form of the Loewner flow of
an alive real point (`imgV_eq_integral`), the separation (D9) in image time (`FrzMartHyp.le_abs_imgV_sub`, …) which
keeps every gap nonzero and every order fixed (`lt_of_continuousOn_of_ne`), and the splitting of the drift sum
(`imgDrift_eq_sum`). Adaptedness in `𝓗` comes from optional sampling of the continuous adapted processes
`r ↦ X(a(r ∧ S))` at the finite stopping times `C'⁻¹(u)` (`measurable_comp_invClockT`,
`FrzD10Hyp.adaptedBefore_img`). **`FrzD10Hyp.exists_isSLEEvolutionUpTo_img`** chooses the sorting itself
(`exists_sort_marks`), and `FrzMartHyp.exists_W'_zero_eq` supplies `w₀`.

The statement is orientation-free (it is stated for `FrzD10Hyp`), so it applies to both `exists_frzD10Hyp` and
`exists_frzD10Hyp_left`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### The real Loewner flow of an alive real point -/

section RealFlow

variable {W : ℝ → ℝ} {x T : ℝ} {v : ℝ → ℂ}

/-- The image of an alive real point is the real part of its centred solution plus the driver. -/
theorem imgV_eq_re (hW : Continuous W) (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    imgV W x t = (v t).re + W t := by
  rw [imgV, fwdMap_eq_of_isForwardSol hW hv ht]

/-- An alive real point starts at itself. -/
theorem imgV_zero (hW : Continuous W) (hv : IsForwardSol W (x : ℂ) T v) (hT : 0 ≤ T) : imgV W x 0 = x := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  rw [imgV_eq_re hW hv h0, (hv.2 0 h0).2, intervalIntegral.integral_same, add_zero]
  simp

/-- The image of an alive real point is continuous on its lifetime interval. -/
theorem continuousOn_imgV (hW : Continuous W) (hv : IsForwardSol W (x : ℂ) T v) :
    ContinuousOn (imgV W x) (Icc 0 T) :=
  ((Complex.continuous_re.comp_continuousOn hv.1).add hW.continuousOn).congr fun _ ht => imgV_eq_re hW hv ht

/-- **The real Loewner equation of an alive real point**: `g_t(x) = x + ∫₀ᵗ 2/(g_s(x) − W_s) ds`. -/
theorem imgV_eq_integral (hW : Continuous W) (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    imgV W x t = x + ∫ s in (0 : ℝ)..t, 2 / (imgV W x s - W s) := by
  have him : ∀ s ∈ Icc (0 : ℝ) T, (v s).im = 0 := fun s hs => im_eq_zero_of_isForwardSol_real hW hv hs
  have hcongr : (∫ s in (0 : ℝ)..t, 2 / v s) = ∫ s in (0 : ℝ)..t, ((2 / (imgV W x s - W s) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
    have hvs : v s = ((v s).re : ℂ) := Complex.ext (by simp) (by simp [him s hs'])
    rw [imgV_eq_re hW hv hs', add_sub_cancel_right]
    calc 2 / v s = 2 / ((v s).re : ℂ) := by conv_lhs => rw [hvs]
      _ = ((2 / (v s).re : ℝ) : ℂ) := by push_cast; rfl
  have e := congrArg Complex.re (hv.2 t ht).2
  rw [hcongr, intervalIntegral.integral_ofReal] at e
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re] at e
  rw [imgV_eq_re hW hv ht, e]
  ring

end RealFlow

/-! ### Order preservation by nonvanishing gaps -/

/-- If two functions are continuous on `[0, c]`, never equal there, and `f 0 < g 0`, then `f < g` on `[0, c]`. -/
theorem lt_of_continuousOn_of_ne {f g : ℝ → ℝ} {c : ℝ} (hf : ContinuousOn f (Icc 0 c)) (hg : ContinuousOn g (Icc 0 c))
    (hne : ∀ u ∈ Icc (0 : ℝ) c, f u ≠ g u) (h0 : f 0 < g 0) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) c) : f u < g u := by
  by_contra hle
  push Not at hle
  have hsub : Icc (0 : ℝ) u ⊆ Icc 0 c := Icc_subset_Icc_right hu.2
  have hc : ContinuousOn (fun s => g s - f s) (Icc 0 u) := (hg.sub hf).mono hsub
  have hmem : (0 : ℝ) ∈ Icc ((fun s => g s - f s) u) ((fun s => g s - f s) 0) :=
    ⟨by simp only; linarith, by simp only; linarith⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' hu.1 hc hmem
  exact hne s (hsub hs) (by simp only at hs0; linarith)

/-! ### The image marks -/

/-- **Positions of the image marks**: the other tip `none ↦ ζ₀` and the force marks `some m ↦ ζ m`. -/
def markPos {n : ℕ} (ζ₀ : ℝ) (ζ : Fin n → ℝ) (o : Option (Fin n)) : ℝ := o.elim ζ₀ ζ

/-- **Weights of the image marks**: `−κ/2` at the other tip, `ρ_m = κ r_m` at the force marks. -/
def markWt {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (o : Option (Fin n)) : ℝ := o.elim (-(κ / 2)) fun m => κ * rr m

/-- **The image drift as one sum over the marks**: `−κ/(2(W' − Ṽ₀)) + Σ ρ_m/(W' − Ṽ_m) = Σ_o w_o/(W' − Ṽ_o)`. -/
theorem imgDrift_eq_sum {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ) (W' : ℝ → ℝ) (ζ₀ : ℝ) (ζ : Fin n → ℝ) (v : ℝ) :
    imgDrift κ rr W' ζ₀ ζ v = ∑ o, markWt κ rr o / (W' v - imgV W' (markPos ζ₀ ζ o) v) := by
  rw [Fintype.sum_option]
  simp only [imgDrift, markWt, markPos, Option.elim]
  rw [neg_div, div_div]

/-- **The drift split along a sorting of the marks** `e : Fin nL ⊕ Fin nR ≃ Option (Fin n)`. -/
theorem imgDrift_eq_sum_sum {n nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) (κ : ℝ) (rr : Fin n → ℝ)
    (W' : ℝ → ℝ) (ζ₀ : ℝ) (ζ : Fin n → ℝ) (v : ℝ) :
    imgDrift κ rr W' ζ₀ ζ v =
      (∑ i, markWt κ rr (e (Sum.inl i)) / (W' v - imgV W' (markPos ζ₀ ζ (e (Sum.inl i))) v)) +
        ∑ i, markWt κ rr (e (Sum.inr i)) / (W' v - imgV W' (markPos ζ₀ ζ (e (Sum.inr i))) v) := by
  rw [imgDrift_eq_sum, ← Equiv.sum_comp e, Fintype.sum_sum_type]

/-- Distinct marks have distinct positions. -/
theorem markPos_injective {n : ℕ} {ζ₀ : ℝ} {ζ : Fin n → ℝ} (hne : ∀ m, ζ m ≠ ζ₀) (hinj : Function.Injective ζ) :
    Function.Injective (markPos ζ₀ ζ) := by
  rintro (_ | m) (_ | k) h
  · rfl
  · exact absurd h.symm (hne k)
  · exact absurd h (hne m)
  · exact congrArg some (hinj h)

/-- **Sorting finitely many distinct marks around a point**: the marks left of `w₀` in decreasing order and those right
of `w₀` in increasing order (the index conventions of `IsSLEPathUpTo`). -/
theorem exists_sort_marks {ι : Type*} [Fintype ι] {pos : ι → ℝ} (hinj : Function.Injective pos) {w₀ : ℝ}
    (hne : ∀ o, pos o ≠ w₀) : ∃ (nL nR : ℕ) (e : Fin nL ⊕ Fin nR ≃ ι), (∀ i, pos (e (Sum.inl i)) < w₀) ∧
      (∀ i, w₀ < pos (e (Sum.inr i))) ∧ Antitone (fun i => pos (e (Sum.inl i))) ∧
      Monotone (fun i => pos (e (Sum.inr i))) := by
  classical
  let oα : LinearOrder {o // pos o < w₀} :=
    LinearOrder.lift' (fun o => -pos o.1) fun x y h => Subtype.ext (hinj (neg_injective h))
  let oβ : LinearOrder {o // ¬ pos o < w₀} := LinearOrder.lift' (fun o => pos o.1) fun x y h => Subtype.ext (hinj h)
  let eα := monoEquivOfFin {o // pos o < w₀} rfl
  let eβ := monoEquivOfFin {o // ¬ pos o < w₀} rfl
  refine ⟨_, _, (Equiv.sumCongr eα.toEquiv eβ.toEquiv).trans (Equiv.sumCompl fun o => pos o < w₀), fun i => ?_,
    fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (eα i).2
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact lt_of_le_of_ne (not_lt.1 (eβ i).2) (hne _).symm
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    have h : eα i ≤ eα j := eα.monotone hij
    exact neg_le_neg_iff.1 h
  · simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact eβ.monotone hij

/-! ### The frozen configuration in image time -/

section FrozenImage

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace FrzMartHyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

/-- **The image driver starts at the same point for every `ω`**: `W'(0)` is the boundary value of `φ` at the
common starting point `0` of the curves. -/
theorem W'_zero_eq (ω ω' : Ω) : W' ω 0 = W' ω' 0 := by
  have hI := (hH.own ω).toImgData
  have hI' := (hH.own ω').toImgData
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (T ω) := ⟨le_rfl, (hH.own ω).pos.le⟩
  -- `φ` tends to `W'_ω(0)` at the starting point
  have hR : IsMapOut ((fun z => fwdMap (drive κ B ω) 0 z + drive κ B ω 0) '' A) φ := by
    have himg0 : (fun z => fwdMap (drive κ B ω) 0 z + drive κ B ω 0) '' A = A := by
      have hdisj0 := hI.disjoint_A_K h0
      ext w; constructor
      · rintro ⟨z, hz, rfl⟩
        have hzK0 : z ∉ fwdHull (drive κ B ω) 0 := fun hz0 => Set.disjoint_left.1 hdisj0 hz hz0
        show fwdMap (drive κ B ω) 0 z + ((drive κ B ω 0 : ℝ) : ℂ) ∈ A
        rw [fwdMap_zero_gen hI.cont (hI.hull.1 hz) hzK0, sub_add_cancel]; exact hz
      · intro hw
        have hwK0 : w ∉ fwdHull (drive κ B ω) 0 := fun hw0 => Set.disjoint_left.1 hdisj0 hw hw0
        refine ⟨w, hw, ?_⟩
        show fwdMap (drive κ B ω) 0 w + ((drive κ B ω 0 : ℝ) : ℂ) = w
        rw [fwdMap_zero_gen hI.cont (hI.hull.1 hw) hwK0, sub_add_cancel]
    rw [himg0]; exact hI.mapOut
  have ht := (hI.rate 0 h0 φ hR).2.1
  rw [hI.a0, (hH.own ω).zero] at ht
  have h1 := hI'.W'_zero_eq (L := (W' ω 0 : ℂ)) (by rw [(hH.own ω').zero]; exact ht)
  exact_mod_cast h1.symm

/-- The common starting point `w₀` of the image drivers (supplies `hw₀` of `FrzD10Hyp.isSLEEvolutionUpTo_img`). -/
theorem exists_W'_zero_eq [Nonempty Ω] : ∃ w₀ : ℝ, ∀ ω, W' ω 0 = w₀ := by
  obtain ⟨ω₀⟩ := ‹Nonempty Ω›
  exact ⟨W' ω₀ 0, fun ω => hH.W'_zero_eq ω ω₀⟩

/-- Every image-time point `u ∈ [0, a(T)]` is `a(t)` for some own time `t ∈ [0, T]`. -/
theorem exists_a_eq (ω : Ω) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (a ω (T ω))) : ∃ t ∈ Icc (0 : ℝ) (T ω), a ω t = u := by
  have h := intermediate_value_Icc (hH.own ω).pos.le (hH.own ω).contA
  rw [(hH.own ω).a0] at h
  exact h hu

/-- Every image mark is alive on `[0, a(T)]`. -/
theorem alive_mark (ω : Ω) (o : Option (Fin n)) : ∃ v, IsForwardSol (W' ω) (markPos ζ₀ ζ o : ℂ) (a ω (T ω)) v := by
  cases o with
  | none => exact hH.alive₀ ω
  | some m => exact hH.alive ω m

/-- `0 ≤ a(T)`. -/
theorem a_T_nonneg (ω : Ω) : 0 ≤ a ω (T ω) := by
  rw [← (hH.own ω).a0]
  exact (hH.own ω).mono.monotoneOn ⟨le_rfl, (hH.own ω).pos.le⟩ ⟨(hH.own ω).pos.le, le_rfl⟩ (hH.own ω).pos.le

/-- The image marks are continuous in image time on `[0, a(T)]`. -/
theorem continuousOn_imgV_mark (ω : Ω) (o : Option (Fin n)) :
    ContinuousOn (imgV (W' ω) (markPos ζ₀ ζ o)) (Icc 0 (a ω (T ω))) :=
  continuousOn_imgV (hH.own ω).contW' (hH.alive_mark ω o).choose_spec

/-- **(D9) in image time, driver gaps**: `γ ≤ |W'(u) − Ṽ_o(u)|` on `[0, a(T)]`. -/
theorem le_abs_sub_imgV (ω : Ω) (o : Option (Fin n)) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (a ω (T ω))) :
    γ ≤ |W' ω u - imgV (W' ω) (markPos ζ₀ ζ o) u| := by
  obtain ⟨t, ht, rfl⟩ := hH.exists_a_eq ω hu
  have hA0 : (frzDataOf κ B W' a φ rr ζ₀ ζ ω).A 0 t = W' ω (a ω t) := (hH.own ω).frzA_zero ht
  cases o with
  | none =>
    have h := ((hH.d9 ω).E0 t ht).1
    rw [hA0, abs_sub_comm] at h
    exact h
  | some m =>
    have h := ((hH.d9 ω).Em t ht m).1
    rw [hA0, abs_sub_comm] at h
    exact h

/-- **(D9) in image time, mark gaps**: `γ ≤ |Ṽ_o(u) − Ṽ_{o'}(u)|` for distinct marks on `[0, a(T)]`. -/
theorem le_abs_imgV_sub (ω : Ω) {o o' : Option (Fin n)} (hoo : o ≠ o') {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (a ω (T ω))) :
    γ ≤ |imgV (W' ω) (markPos ζ₀ ζ o) u - imgV (W' ω) (markPos ζ₀ ζ o') u| := by
  obtain ⟨t, ht, rfl⟩ := hH.exists_a_eq ω hu
  cases o with
  | none =>
    cases o' with
    | none => exact absurd rfl hoo
    | some k => exact ((hH.d9 ω).E2m t ht k).1
  | some m =>
    cases o' with
    | none =>
      have h := ((hH.d9 ω).E2m t ht m).1
      rw [abs_sub_comm] at h
      exact h
    | some k => exact ((hH.d9 ω).Cmk t ht m k fun h => hoo (congrArg some h)).1

theorem gamma_pos (ω : Ω) : 0 < γ := (hH.d9 ω).g0

/-- No image mark starts at the image driver. -/
theorem markPos_ne (ω : Ω) (o : Option (Fin n)) : markPos ζ₀ ζ o ≠ W' ω 0 := fun h => by
  have h0 := hH.le_abs_sub_imgV ω o ⟨le_rfl, hH.a_T_nonneg ω⟩
  rw [imgV_zero (hH.own ω).contW' (hH.alive_mark ω o).choose_spec (hH.a_T_nonneg ω), h, sub_self, abs_zero] at h0
  exact absurd h0 (not_le.2 (hH.gamma_pos ω))

/-- **The side of each image mark is fixed**: an image mark left (right) of the starting driver stays left (right). -/
theorem imgV_lt_of_lt (ω : Ω) (o : Option (Fin n)) (h0 : markPos ζ₀ ζ o < W' ω 0) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (a ω (T ω))) : imgV (W' ω) (markPos ζ₀ ζ o) u < W' ω u := by
  refine lt_of_continuousOn_of_ne (hH.continuousOn_imgV_mark ω o) (hH.own ω).contW'.continuousOn
    (fun s hs h => ?_) ?_ hu
  · have := hH.le_abs_sub_imgV ω o hs
    rw [h, sub_self, abs_zero] at this
    exact absurd this (not_le.2 (hH.gamma_pos ω))
  · rw [imgV_zero (hH.own ω).contW' (hH.alive_mark ω o).choose_spec (hH.a_T_nonneg ω)]; exact h0

theorem lt_imgV_of_lt (ω : Ω) (o : Option (Fin n)) (h0 : W' ω 0 < markPos ζ₀ ζ o) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (a ω (T ω))) : W' ω u < imgV (W' ω) (markPos ζ₀ ζ o) u := by
  refine lt_of_continuousOn_of_ne (hH.own ω).contW'.continuousOn (hH.continuousOn_imgV_mark ω o)
    (fun s hs h => ?_) ?_ hu
  · have := hH.le_abs_sub_imgV ω o hs
    rw [h, sub_self, abs_zero] at this
    exact absurd this (not_le.2 (hH.gamma_pos ω))
  · rw [imgV_zero (hH.own ω).contW' (hH.alive_mark ω o).choose_spec (hH.a_T_nonneg ω)]; exact h0

/-- **The order of the image marks is fixed.** -/
theorem imgV_lt_imgV_of_lt (ω : Ω) {o o' : Option (Fin n)} (h0 : markPos ζ₀ ζ o < markPos ζ₀ ζ o') {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (a ω (T ω))) :
    imgV (W' ω) (markPos ζ₀ ζ o) u < imgV (W' ω) (markPos ζ₀ ζ o') u := by
  have hoo : o ≠ o' := fun h => by rw [h] at h0; exact lt_irrefl _ h0
  refine lt_of_continuousOn_of_ne (hH.continuousOn_imgV_mark ω o) (hH.continuousOn_imgV_mark ω o')
    (fun s hs h => ?_) ?_ hu
  · have := hH.le_abs_imgV_sub ω hoo hs
    rw [h, sub_self, abs_zero] at this
    exact absurd this (not_le.2 (hH.gamma_pos ω))
  · rw [imgV_zero (hH.own ω).contW' (hH.alive_mark ω o).choose_spec (hH.a_T_nonneg ω),
      imgV_zero (hH.own ω).contW' (hH.alive_mark ω o').choose_spec (hH.a_T_nonneg ω)]
    exact h0

end FrzMartHyp

end FrozenImage

/-! ### Adaptedness in the capacity-time filtration -/

section Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem coe_lt_ofReal_iff (u : ℝ≥0) (x : ℝ) : (u : ℝ≥0∞) < ENNReal.ofReal x ↔ (u : ℝ) < x := by
  rw [ENNReal.ofReal, ENNReal.coe_lt_coe, Real.lt_toNNReal_iff_coe_lt]

/-- A function continuous on `[0, S]` read at `r ∧ S` is continuous in `r`. -/
theorem continuous_comp_min {S : ℝ≥0} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 (S : ℝ))) :
    Continuous fun r : ℝ≥0 => f ((min r S : ℝ≥0) : ℝ) :=
  hf.comp_continuous (NNReal.continuous_coe.comp (continuous_id.min continuous_const))
    fun _ => ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩

/-- **Stopped image processes are adapted.** If `r ↦ X_ω(a_ω(r))` is continuous on `[0, S]` and its restriction to
`{r ≤ S}` is `𝓕_r`-measurable, then `X_ω(a_ω(r ∧ S))` is `𝓕_r`-measurable. -/
theorem measurable_comp_min {𝓕 : Filtration ℝ≥0 mΩ} {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {X a : Ω → ℝ → ℝ}
    (hK : ∀ r : ℝ≥0, Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => X ω (a ω r)))
    (hc : ∀ ω, ContinuousOn (fun r : ℝ => X ω (a ω r)) (Icc 0 (S ω : ℝ))) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => X ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)) := by
  have h := Ito.measurable_stopped_of_agree (β := ℝ) (X := fun (u : ℝ≥0) ω => X ω (a ω u))
    (K := fun (u : ℝ≥0) ω => {ω | u ≤ S ω}.indicator (fun ω => X ω (a ω u)) ω) hS hK (G := univ)
    MeasurableSet.univ 0 (fun ω _ u hu => indicator_of_mem (show ω ∈ {ω | u ≤ S ω} from hu) _)
    (fun ω _ => (hc ω).comp NNReal.continuous_coe.continuousOn fun u hu =>
      ⟨u.coe_nonneg, NNReal.coe_le_coe.2 hu⟩) t
  simpa only [mem_univ, ite_true] using h

/-- **Optional sampling of a continuous adapted process at a clock inverse.** -/
theorem measurable_comp_invClockT {𝓕 : Filtration ℝ≥0 mΩ} {C : Ω → ℝ≥0 → ℝ} {u : ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (invClock C u)) {Y : ℝ≥0 → Ω → ℝ} (hYm : ∀ r, Measurable[𝓕 r] (Y r))
    (hYc : ∀ ω, Continuous (Y · ω)) : Measurable[hτ.measurableSpace] fun ω => Y (invClockT C u ω) ω := by
  have hYp : IsStronglyProgressive 𝓕 Y :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun r => (hYm r).stronglyMeasurable) hYc
  exact measurable_stoppedValue hYp hτ

namespace FrzD10Hyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

/-- `a(S) ≤ a(T)`. -/
theorem a_S_le (ω : Ω) : a ω (S ω) ≤ a ω (T ω) :=
  (hH.own ω).mono.monotoneOn ⟨(S ω).coe_nonneg, hH.le ω⟩ ⟨(hH.own ω).pos.le, le_rfl⟩ (hH.le ω)

theorem mem_Icc_of_lt_ofReal (ω : Ω) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω))) :
    (u : ℝ) ∈ Icc (0 : ℝ) (a ω (T ω)) :=
  ⟨u.coe_nonneg, ((coe_lt_ofReal_iff u _).1 hu).le.trans (hH.a_S_le ω)⟩

omit hH in
/-- `C'(S) = a(S)`. -/
theorem bmClk_S (ω : Ω) : bmClk a S ω (S ω) = a ω (S ω) := by
  simp only [bmClk, min_self, sub_self, add_zero]

/-- **The clock inverse before `a(S)`**: for `u ≤ a(S)`, `θ_u = C'⁻¹(u) ≤ S` and `a(θ_u) = u`. -/
theorem invClockT_le_and_a_eq {u : ℝ≥0} {ω : Ω} (hu : (u : ℝ) ≤ a ω (S ω)) :
    invClockT (bmClk a S) u ω ≤ S ω ∧ a ω (invClockT (bmClk a S) u ω) = u := by
  have ha₀ := (hH.d9 ω).a0
  have hc : 0 < min (a₀ ^ 2) 1 := lt_min (pow_pos ha₀ 2) one_pos
  obtain ⟨-, hC, -⟩ := invClock_eq_coe hH.continuous_bmClk hH.bmClk_zero hc hH.le_bmClk u ω
  set θ := invClockT (bmClk a S) u ω with hθ
  have hθS : θ ≤ S ω := by
    by_contra h
    push Not at h
    have e : bmClk a S ω θ = a ω (S ω) + ((θ : ℝ) - S ω) := by simp only [bmClk, min_eq_right h.le]
    have hθS' : (S ω : ℝ) < θ := h
    linarith
  refine ⟨hθS, ?_⟩
  have e : bmClk a S ω θ = a ω θ := by simp only [bmClk, min_eq_left hθS, sub_self, add_zero]
  rw [← e, hC]

/-- **Before `a(S)` iff the clock inverse is before `S`.** -/
theorem lt_a_S_iff (u : ℝ≥0) (ω : Ω) :
    (u : ℝ) < a ω (S ω) ↔ invClock (bmClk a S) u ω < (S ω : WithTop ℝ≥0) := by
  have ha₀ := (hH.d9 ω).a0
  have hc : 0 < min (a₀ ^ 2) 1 := lt_min (pow_pos ha₀ 2) one_pos
  obtain ⟨he, hC, -⟩ := invClock_eq_coe hH.continuous_bmClk hH.bmClk_zero hc hH.le_bmClk u ω
  rw [he, WithTop.coe_lt_coe, ← (hH.strictMono_bmClk ω).lt_iff_lt, hC, bmClk_S ω]

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- **Adaptedness before `a(S)` in the capacity-time filtration** `𝓗_u = 𝓕_{C'⁻¹(u)}`: if `r ↦ X_ω(a_ω(r ∧ S))` is
continuous and `𝓕`-adapted, then `u ↦ X_ω(u) − c` is adapted before `a(S)` to `𝓗`. -/
theorem adaptedBefore_img (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {X : Ω → ℝ → ℝ}
    (hY : ∀ t : ℝ≥0, Measurable[𝓕 t] fun ω => X ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)))
    (hYc : ∀ ω, Continuous fun t : ℝ≥0 => X ω (a ω ((min t (S ω) : ℝ≥0) : ℝ))) (c : ℝ) :
    AdaptedBefore
      (Zhan.Retarget.timeChangeFilt 𝓕
        (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
          (hH.measurable_bmClk hBm hBc hS))
        (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
      (fun ω => ENNReal.ofReal (a ω (S ω))) (fun (u : ℝ≥0) ω => X ω u - c) := by
  intro u A hA
  have hθ := isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
    (hH.measurable_bmClk hBm hBc hS) u
  have e : {ω | (u : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω)) ∧ X ω u - c ∈ A} =
      {ω | (S ω : WithTop ℝ≥0) ≤ invClock (bmClk a S) u ω}ᶜ ∩
        (fun ω => X ω (a ω ((min (invClockT (bmClk a S) u ω) (S ω) : ℝ≥0) : ℝ)) - c) ⁻¹' A := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, not_le, mem_preimage]
    rw [coe_lt_ofReal_iff, hH.lt_a_S_iff u ω]
    refine and_congr_right fun hlt => ?_
    have hle : (u : ℝ) ≤ a ω (S ω) := ((hH.lt_a_S_iff u ω).2 hlt).le
    obtain ⟨hθS, haθ⟩ := hH.invClockT_le_and_a_eq hle
    rw [min_eq_left hθS, haθ]
  rw [e]
  refine (hS.measurableSet_stopping_time_le hθ).compl.inter ?_
  exact ((measurable_comp_invClockT hθ hY hYc).sub_const c) hA

end FrzD10Hyp

end Adapted

/-! ### The pathwise force-point conditions -/

section Path

/-- Reading a function continuous on `[0, c]` at `s⁺` is interval integrable on `[0, t]`, `t ∈ [0, c]`. -/
theorem intervalIntegrable_comp_toNNReal {F : ℝ → ℝ} {c t : ℝ} (hF : ContinuousOn F (Icc 0 c))
    (ht : t ∈ Icc (0 : ℝ) c) : IntervalIntegrable (fun s : ℝ => F ((s.toNNReal : ℝ≥0) : ℝ)) MeasureTheory.volume 0 t :=
  (hF.comp (NNReal.continuous_coe.comp continuous_real_toNNReal).continuousOn fun s hs => by
    simp only [Function.comp_apply, Real.coe_toNNReal _ hs.1]; exact ⟨hs.1, hs.2.trans ht.2⟩).intervalIntegrable_of_Icc ht.1

/-- On `[0, t]`, reading at `s⁺` does not change an integral. -/
theorem integral_comp_toNNReal (F : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, F ((s.toNNReal : ℝ≥0) : ℝ) = ∫ s in (0 : ℝ)..t, F s := by
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  simp only [Real.coe_toNNReal _ hs.1]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace FrzD10Hyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

/-- The drift term of one mark is continuous in image time on `[0, a(T)]`. -/
theorem continuousOn_markTerm (ω : Ω) (o : Option (Fin n)) :
    ContinuousOn (fun v => markWt κ rr o / (W' ω v - imgV (W' ω) (markPos ζ₀ ζ o) v)) (Icc 0 (a ω (T ω))) :=
  continuousOn_const.div ((hH.own ω).contW'.continuousOn.sub (hH.toFrzMartHyp.continuousOn_imgV_mark ω o))
    fun v hv h => by
      have := hH.toFrzMartHyp.le_abs_sub_imgV ω o hv
      rw [h, abs_zero] at this
      exact absurd this (not_le.2 (hH.toFrzMartHyp.gamma_pos ω))

/-- **The force-point equation in sum form**: for `u ≤ a(S)`,
`W'(u) − W'(0) = √κ B̂_u + Σ_{left} ∫₀ᵘ ρ/(W' − Ṽ) + Σ_{right} ∫₀ᵘ ρ/(W' − Ṽ)`. -/
theorem sub_eq_bm_add_sum {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) (hκ : 0 < κ) {u : ℝ≥0} {ω : Ω}
    (hu : (u : ℝ) ≤ a ω (S ω)) :
    W' ω u - W' ω 0 = Real.sqrt κ * bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω +
      (∑ i, ∫ v in (0 : ℝ)..u, markWt κ rr (e (Sum.inl i)) /
        (W' ω v - imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) v)) +
      (∑ i, ∫ v in (0 : ℝ)..u, markWt κ rr (e (Sum.inr i)) /
        (W' ω v - imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr i))) v)) := by
  have hmem : (u : ℝ) ∈ Icc (0 : ℝ) (a ω (T ω)) := ⟨u.coe_nonneg, hu.trans (hH.a_S_le ω)⟩
  have hint : ∀ o, IntervalIntegrable (fun v => markWt κ rr o / (W' ω v - imgV (W' ω) (markPos ζ₀ ζ o) v))
      MeasureTheory.volume 0 u := fun o =>
    ((hH.continuousOn_markTerm ω o).mono (Icc_subset_Icc_right hmem.2)).intervalIntegrable_of_Icc hmem.1
  have hI : ∫ v in (0 : ℝ)..u, imgDrift κ rr (W' ω) ζ₀ ζ v =
      (∑ i, ∫ v in (0 : ℝ)..u, markWt κ rr (e (Sum.inl i)) /
        (W' ω v - imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) v)) +
      (∑ i, ∫ v in (0 : ℝ)..u, markWt κ rr (e (Sum.inr i)) /
        (W' ω v - imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr i))) v)) := by
    have hsum : ∀ g : Fin nL ⊕ Fin nR → Option (Fin n), ∀ (ι : Type) [Fintype ι] (j : ι → Fin nL ⊕ Fin nR),
        IntervalIntegrable (fun v => ∑ i, markWt κ rr (g (j i)) /
          (W' ω v - imgV (W' ω) (markPos ζ₀ ζ (g (j i))) v)) MeasureTheory.volume 0 u := fun g ι _ j =>
      (continuousOn_finsetSum _ fun i _ => (hH.continuousOn_markTerm ω (g (j i))).mono
        (Icc_subset_Icc_right hmem.2)).intervalIntegrable_of_Icc hmem.1
    simp_rw [imgDrift_eq_sum_sum e]
    rw [intervalIntegral.integral_add (hsum e (Fin nL) Sum.inl) (hsum e (Fin nR) Sum.inr),
      intervalIntegral.integral_finsetSum fun i _ => hint _, intervalIntegral.integral_finsetSum fun i _ => hint _]
  have hb := hH.bmY_invClockT_eq hu
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [hb, mul_div_cancel₀ _ hs, hI]
  ring

/-- **The image path is a local force-point path before `a(S)`** (for every `ω`): driver `W' − w₀`, image marks
`Ṽ_o − w₀` sorted by `e` into left and right families, noise `B̂`, horizon `a(S)`. -/
theorem isSLEPathUpTo_img (hκ : 0 < κ) {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) {w₀ : ℝ}
    (hw₀ : ∀ ω, W' ω 0 = w₀) (hL : ∀ i, markPos ζ₀ ζ (e (Sum.inl i)) < w₀)
    (hR : ∀ i, w₀ < markPos ζ₀ ζ (e (Sum.inr i))) (hLa : Antitone fun i => markPos ζ₀ ζ (e (Sum.inl i)))
    (hRm : Monotone fun i => markPos ζ₀ ζ (e (Sum.inr i))) (ω : Ω) :
    Sec2.IsSLEPathUpTo κ (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀) (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀)
      (fun i => markWt κ rr (e (Sum.inl i))) (fun i => markWt κ rr (e (Sum.inr i)))
      (fun t => W' ω t - w₀) (fun i t => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) t - w₀)
      (fun i t => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr i))) t - w₀)
      (fun t => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) t ω) ω) (ENNReal.ofReal (a ω (S ω))) := by
  have hF := hH.toFrzMartHyp
  have hpinj : Function.Injective (markPos ζ₀ ζ) := markPos_injective hF.ne hF.inj
  have hT := hF.a_T_nonneg ω
  have hmem : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω)) → (t : ℝ) ∈ Icc (0 : ℝ) (a ω (T ω)) :=
    fun ht => hH.mem_Icc_of_lt_ofReal ω ht
  have hz : ∀ o, imgV (W' ω) (markPos ζ₀ ζ o) 0 = markPos ζ₀ ζ o := fun o =>
    imgV_zero (hH.own ω).contW' (hF.alive_mark ω o).choose_spec hT
  have hcont : ∀ F : ℝ → ℝ, ContinuousOn F (Icc 0 (a ω (T ω))) →
      ContinuousOn (fun t : ℝ≥0 => F t) {t : ℝ≥0 | (t : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω))} := fun F hF' =>
    hF'.comp NNReal.continuous_coe.continuousOn fun _ ht => hmem ht
  have hgap : ∀ o {u : ℝ}, u ∈ Icc (0 : ℝ) (a ω (T ω)) → W' ω u - imgV (W' ω) (markPos ζ₀ ζ o) u ≠ 0 :=
    fun o u hu h => by
      have := hF.le_abs_sub_imgV ω o hu
      rw [h, abs_zero] at this
      exact absurd this (not_le.2 (hF.gamma_pos ω))
  have hinv : ∀ o {t : ℝ≥0}, (t : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω)) →
      IntervalIntegrable (fun s : ℝ => (W' ω (s.toNNReal : ℝ) - w₀ -
        (imgV (W' ω) (markPos ζ₀ ζ o) (s.toNNReal : ℝ) - w₀))⁻¹) MeasureTheory.volume 0 t := fun o t ht => by
    have h := intervalIntegrable_comp_toNNReal (F := fun u => (W' ω u - imgV (W' ω) (markPos ζ₀ ζ o) u)⁻¹)
      (((hH.own ω).contW'.continuousOn.sub (hF.continuousOn_imgV_mark ω o)).inv₀ fun u hu => hgap o hu) (hmem ht)
    simpa only [sub_sub_sub_cancel_right] using h
  have hODE : ∀ o {t : ℝ≥0}, (t : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω)) →
      imgV (W' ω) (markPos ζ₀ ζ o) t - w₀ = markPos ζ₀ ζ o - w₀ + ∫ s in (0 : ℝ)..t,
        2 / (imgV (W' ω) (markPos ζ₀ ζ o) (s.toNNReal : ℝ) - w₀ - (W' ω (s.toNNReal : ℝ) - w₀)) := fun o t ht => by
    simp only [sub_sub_sub_cancel_right]
    have hc := integral_comp_toNNReal (fun x => 2 / (imgV (W' ω) (markPos ζ₀ ζ o) x - W' ω x)) t.coe_nonneg
    rw [hc, imgV_eq_integral (hH.own ω).contW' (hF.alive_mark ω o).choose_spec (hmem ht)]
    ring
  have hcol : ∀ o, MeasureTheory.volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω)) ∧
      W' ω (s.toNNReal : ℝ) - w₀ = imgV (W' ω) (markPos ζ₀ ζ o) (s.toNNReal : ℝ) - w₀} = 0 := fun o => by
    have he : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ENNReal.ofReal (a ω (S ω)) ∧
        W' ω (s.toNNReal : ℝ) - w₀ = imgV (W' ω) (markPos ζ₀ ζ o) (s.toNNReal : ℝ) - w₀} = ∅ := by
      ext s
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ hs h
      exact hgap o (hmem hs) (by linarith)
    rw [he, MeasureTheory.measure_empty]
  have hidx : ∀ {α : Type} (j : α → Fin nL ⊕ Fin nR), Function.Injective j → ∀ {i k : α}, i ≠ k →
      markPos ζ₀ ζ (e (j i)) ≠ markPos ζ₀ ζ (e (j k)) := fun j hj i k hik h =>
    hik (hj (e.injective (hpinj h)))
  refine
    { w_zero := by simp only [NNReal.coe_zero, hw₀ ω, sub_self]
      vL_zero := fun i => by simp only [NNReal.coe_zero, hz]
      vR_zero := fun i => by simp only [NNReal.coe_zero, hz]
      continuousOn_w := (((hH.own ω).contW'.comp NNReal.continuous_coe).sub continuous_const).continuousOn
      continuousOn_vL := fun i => (hcont _ (hF.continuousOn_imgV_mark ω _)).sub continuousOn_const
      continuousOn_vR := fun i => (hcont _ (hF.continuousOn_imgV_mark ω _)).sub continuousOn_const
      antitone_vL := fun {t} ht i k hik => by
        rcases eq_or_ne i k with rfl | hne
        · exact le_rfl
        · exact sub_le_sub_right (hF.imgV_lt_imgV_of_lt ω (lt_of_le_of_ne (hLa hik)
            (hidx Sum.inl Sum.inl_injective hne.symm)) (hmem ht)).le w₀
      vL_le_w := fun {t} ht i =>
        sub_le_sub_right (hF.imgV_lt_of_lt ω _ (by rw [hw₀ ω]; exact hL i) (hmem ht)).le w₀
      w_le_vR := fun {t} ht i =>
        sub_le_sub_right (hF.lt_imgV_of_lt ω _ (by rw [hw₀ ω]; exact hR i) (hmem ht)).le w₀
      monotone_vR := fun {t} ht i k hik => by
        rcases eq_or_ne i k with rfl | hne
        · exact le_rfl
        · exact sub_le_sub_right (hF.imgV_lt_imgV_of_lt ω (lt_of_le_of_ne (hRm hik)
            (hidx Sum.inr Sum.inr_injective hne)) (hmem ht)).le w₀
      integrable_gapL := fun {t} ht i => hinv _ ht
      integrable_gapR := fun {t} ht i => hinv _ ht
      w_eq := fun {t} ht => by
        have h := hH.sub_eq_bm_add_sum e hκ ((coe_lt_ofReal_iff t _).1 ht).le
        rw [hw₀ ω] at h
        have hi : ∀ o, ∫ s in (0 : ℝ)..t, markWt κ rr o / (W' ω (s.toNNReal : ℝ) - w₀ -
            (imgV (W' ω) (markPos ζ₀ ζ o) (s.toNNReal : ℝ) - w₀)) =
            ∫ s in (0 : ℝ)..t, markWt κ rr o / (W' ω s - imgV (W' ω) (markPos ζ₀ ζ o) s) := fun o => by
          simp only [sub_sub_sub_cancel_right]
          exact integral_comp_toNNReal (fun x => markWt κ rr o / (W' ω x - imgV (W' ω) (markPos ζ₀ ζ o) x))
            t.coe_nonneg
        simp only [hi]
        exact h
      vL_eq := fun {t} ht i => hODE _ ht
      vR_eq := fun {t} ht i => hODE _ ht
      volume_collisionL := fun i => hcol _
      volume_collisionR := fun i => hcol _
      not_threshold := fun {t} ht hth => by
        have hne : ∀ o, imgV (W' ω) (markPos ζ₀ ζ o) t - w₀ ≠ W' ω t - w₀ := fun o h =>
          hgap o (hmem ht) (by linarith)
        unfold ForceWord.ThresholdCondition at hth
        rw [Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 (hne _),
          Finset.sum_eq_zero fun i hi => absurd (Finset.mem_filter.1 hi).2 (hne _)] at hth
        norm_num at hth }

end FrzD10Hyp

end Path

/-! ### The identification -/

section Ident

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace FrzD10Hyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzD10Hyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

/-- `a` maps `[0, S]` into `[0, a(T)]`. -/
theorem a_mem_Icc_aT (ω : Ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (S ω)) : a ω t ∈ Icc (0 : ℝ) (a ω (T ω)) := by
  have htT : t ∈ Icc (0 : ℝ) (T ω) := ⟨ht.1, ht.2.trans (hH.le ω)⟩
  exact ⟨(hH.a_mem_Icc ω htT).1, (hH.own ω).mono.monotoneOn htT ⟨(hH.own ω).pos.le, le_rfl⟩ htT.2⟩

theorem continuousOn_W'_a (ω : Ω) : ContinuousOn (fun t => W' ω (a ω t)) (Icc 0 (S ω : ℝ)) :=
  (hH.own ω).contW'.comp_continuousOn ((hH.own ω).contA.mono (Icc_subset_Icc_right (hH.le ω)))

theorem continuousOn_imgV_a (ω : Ω) (o : Option (Fin n)) :
    ContinuousOn (fun t => imgV (W' ω) (markPos ζ₀ ζ o) (a ω t)) (Icc 0 (S ω : ℝ)) :=
  (hH.toFrzMartHyp.continuousOn_imgV_mark ω o).comp ((hH.own ω).contA.mono (Icc_subset_Icc_right (hH.le ω)))
    fun _ ht => hH.a_mem_Icc_aT ω ht

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The stopped image driver** `W'(a(r ∧ S)) = A_{j,0}(r ∧ S)` is `𝓕`-adapted. -/
theorem measurable_W'_min (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => W' ω (a ω ((min t (S ω) : ℝ≥0) : ℝ)) := by
  refine measurable_comp_min (X := W') hS (fun r => ?_) hH.continuousOn_W'_a t
  have h := (hH.toFrzMartHyp.measurable_parts hBm hBc hS r).1 0
  have e : ({ω | r ≤ S ω}.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 0 r) =
      {ω | r ≤ S ω}.indicator fun ω => W' ω (a ω r) := by
    funext ω
    by_cases hω : ω ∈ {ω | r ≤ S ω}
    · rw [indicator_of_mem hω, indicator_of_mem hω,
        (hH.own ω).frzA_zero ⟨r.coe_nonneg, (NNReal.coe_le_coe.2 hω).trans (hH.le ω)⟩]
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  rw [e] at h
  exact h

/-- **The stopped image marks** `Ṽ_o(a(r ∧ S))` are `𝓕`-adapted. -/
theorem measurable_imgV_min (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (o : Option (Fin n)) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω => imgV (W' ω) (markPos ζ₀ ζ o) (a ω ((min t (S ω) : ℝ≥0) : ℝ)) := by
  refine measurable_comp_min (X := fun ω => imgV (W' ω) (markPos ζ₀ ζ o)) hS (fun r => ?_)
    (fun ω => hH.continuousOn_imgV_a ω o) t
  obtain ⟨-, h₀, hm, -, -, -⟩ := hH.toFrzMartHyp.measurable_parts hBm hBc hS r
  cases o with
  | none => exact h₀
  | some m => exact hm m

/-- **The identification (§A.1.3): the image path is a local force-point evolution before `a(S)`.** Under
`Q = (M̃_S/M̃_0)·P`, in the capacity-time filtration `𝓗_u = 𝓕_{C'⁻¹(u)}`, with the `Q`-Brownian motion
`B̂_u = Y_{C'⁻¹(u)}` of `𝓗`, the image driver `W'(u) − w₀` and the image marks `Ṽ_o(u) − w₀` — the other tip with
weight `−κ/2`, the force marks with weights `ρ_m = κ r_m`, sorted into left and right families by `e` — form a
local integrated `SLE_κ(ρ)` evolution (`Sec2.IsSLEEvolutionUpTo`) before `a(S)`, from the marks `pos − w₀`. -/
theorem isSLEEvolutionUpTo_img {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ}
    (hBb : ∀ ω (r : ℝ≥0), r ≤ S ω → |B r ω| ≤ NB) {nL nR : ℕ} (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)) {w₀ : ℝ}
    (hw₀ : ∀ ω, W' ω 0 = w₀) (hL : ∀ i, markPos ζ₀ ζ (e (Sum.inl i)) < w₀)
    (hR : ∀ i, w₀ < markPos ζ₀ ζ (e (Sum.inr i))) (hLa : Antitone fun i => markPos ζ₀ ζ (e (Sum.inl i)))
    (hRm : Monotone fun i => markPos ζ₀ ζ (e (Sum.inr i))) :
    Sec2.IsSLEEvolutionUpTo κ (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀)
      (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀) (fun i => markWt κ rr (e (Sum.inl i)))
      (fun i => markWt κ rr (e (Sum.inr i)))
      (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
      (Zhan.Retarget.timeChangeFilt 𝓕
        (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
          (hH.measurable_bmClk (fun u => hB.2.1 u) hBc hS))
        (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
      (fun u ω => W' ω u - w₀) (fun i u ω => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) u - w₀)
      (fun i u ω => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr i))) u - w₀)
      (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω)
      (fun ω => ENNReal.ofReal (a ω (S ω))) where
  brownian := hH.isFilteredBrownianReal_bm hκ hB hBc hS hBb
  adapted_W := hH.adaptedBefore_img (fun u => hB.2.1 u) hBc hS (X := W')
    (hH.measurable_W'_min (fun u => hB.2.1 u) hBc hS) (fun ω => continuous_comp_min (hH.continuousOn_W'_a ω)) w₀
  adapted_VL i := hH.adaptedBefore_img (fun u => hB.2.1 u) hBc hS
    (X := fun ω => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))))
    (hH.measurable_imgV_min (fun u => hB.2.1 u) hBc hS _) (fun ω => continuous_comp_min (hH.continuousOn_imgV_a ω _))
    w₀
  adapted_VR i := hH.adaptedBefore_img (fun u => hB.2.1 u) hBc hS
    (X := fun ω => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr i))))
    (hH.measurable_imgV_min (fun u => hB.2.1 u) hBc hS _) (fun ω => continuous_comp_min (hH.continuousOn_imgV_a ω _))
    w₀
  ae_path := Eventually.of_forall fun ω => hH.isSLEPathUpTo_img hκ e hw₀ hL hR hLa hRm ω

/-- **The identification, marks sorted automatically**: there is a sorting `e` of the image marks into left and right
families for which the conclusion of `isSLEEvolutionUpTo_img` holds. -/
theorem exists_isSLEEvolutionUpTo_img {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {NB : ℝ}
    (hBb : ∀ ω (r : ℝ≥0), r ≤ S ω → |B r ω| ≤ NB) {w₀ : ℝ} (hw₀ : ∀ ω, W' ω 0 = w₀) :
    ∃ (nL nR : ℕ) (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)),
      Sec2.IsSLEEvolutionUpTo κ (fun i => markPos ζ₀ ζ (e (Sum.inl i)) - w₀)
        (fun i => markPos ζ₀ ζ (e (Sum.inr i)) - w₀) (fun i => markWt κ rr (e (Sum.inl i)))
        (fun i => markWt κ rr (e (Sum.inr i)))
        (girsMeasure P (Real.sqrt κ) B S fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell)
        (Zhan.Retarget.timeChangeFilt 𝓕
          (isStoppingTime_invClock hH.continuous_bmClk (fun ω => (hH.strictMono_bmClk ω).monotone)
            (hH.measurable_bmClk (fun u => hB.2.1 u) hBc hS))
          (invClock_mono hH.continuous_bmClk fun ω => (hH.strictMono_bmClk ω).monotone))
        (fun u ω => W' ω u - w₀) (fun i u ω => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inl i))) u - w₀)
        (fun i u ω => imgV (W' ω) (markPos ζ₀ ζ (e (Sum.inr i))) u - w₀)
        (fun u ω => bmY κ B W' a φ rr ζ₀ ζ S (invClockT (bmClk a S) u ω) ω)
        (fun ω => ENNReal.ofReal (a ω (S ω))) := by
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have hF := hH.toFrzMartHyp
  obtain ⟨nL, nR, e, hL, hR, hLa, hRm⟩ := exists_sort_marks (markPos_injective hF.ne hF.inj) (w₀ := w₀)
    fun o => by rw [← hw₀ ω₀]; exact hF.markPos_ne ω₀ o
  exact ⟨nL, nR, e, hH.isSLEEvolutionUpTo_img hκ hB hBc hS hBb e hw₀ hL hR hLa hRm⟩

end FrzD10Hyp

end Ident

end InteractingSLE.ZhanGT4
