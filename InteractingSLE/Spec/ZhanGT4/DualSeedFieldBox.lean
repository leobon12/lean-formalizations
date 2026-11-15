/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedField

/-!
# Zhan's A.1.6, the seeded field IV: the seeded log-density is a regular log-field on a box

Packet PROVE-ZHAN-GT4-A20. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38): "At positive own time, differentiating (D13)–(D15) by Itô and the force ODE
is the same cancelled calculation leading to (D8)."

On a box `[b, c] × B(y, r_b)` around the driver (A4's box hypotheses `hdisj`, `hWm`, `hq0`) during which the own-chart
marks follow the force ODE (`V' = 2/(V − W)`, `G⁰' = −2G⁰/(V⁰ − W)²`), keep a disc clear of the frozen hull image
(`hmcl`) and do not degenerate (`TimeNd`), the seeded log-density `SeedData.ell` of `DualSeedField` has the formal
derivatives `ellX`, `ellXX`, `ellXXX`, `ellT`:

* `SeedData.hasDerivWithinAt_A21`, `…_B0`, `…_B1` ((D3) along the marks, `DualSeedFieldMark`), `…_LT`, `…_LT0`,
  `…_LS`, `…_LS0` and **`SeedData.hasDerivWithinAt_ell`**: `∂_t ℓ = ellT` within `[b, c]`;
* **`SeedData.hasDerivAt_ell`**, `…_ellX`, `…_ellXX`: the space derivatives on the region `|x − y| < 3ρ` (`3ρ ≤ r_b`)
  where the space factors do not degenerate (`SpaceNd`);
* **`SeedData.isLogField`**: given a bound `K` on the region, `ℓ` is a regular log-field (`IsLogField`), the pathwise
  input of the Itô step.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

namespace SeedData

variable {n : ℕ} (d : SeedData n)

/-- **The nondegeneracy of the time factors** of the seeded field at time `t`. -/
structure TimeNd (t : ℝ) : Prop where
  G₀ : d.G₀ t ≠ 0
  V₀W : d.V₀ t - d.W t ≠ 0
  VW : ∀ m, d.V m t - d.W t ≠ 0
  V₀V : ∀ m, d.V₀ t - d.V m t ≠ 0
  VV : ∀ m k, m ≠ k → d.V m t - d.V k t ≠ 0
  BA : ∀ m, d.B0 t m - d.A 0 t ≠ 0
  A2B : ∀ m, d.A20 t - d.B0 t m ≠ 0
  BB : ∀ m k, m ≠ k → d.B0 t m - d.B0 t k ≠ 0
  B1 : ∀ m, d.B1 t m ≠ 0

/-- **The nondegeneracy of the space factors** at `(t, x)`. -/
structure SpaceNd (t x : ℝ) : Prop where
  F1 : d.F 1 t x ≠ 0
  FA : d.F 0 t x - d.A20 t ≠ 0
  FB : ∀ m, d.F 0 t x - d.B0 t m ≠ 0
  xV₀ : x - d.V₀ t ≠ 0
  xV : ∀ m, x - d.V m t ≠ 0

section Box

variable {A : Set ℂ} {T : ℝ} (h : OwnData d.W A d.φ T d.a d.W')
  {v₀ : ℝ → ℂ} (hv₀ : IsForwardSol d.W' d.ζ₀ (d.a T) v₀)
  {b c y rb : ℝ} (hJ : Icc b c ⊆ Icc 0 T)
  (hdisj : ∀ t ∈ Icc b c, Disjoint (ball (y : ℂ) (2 * rb)) ((fun z => fwdMap d.W t z + d.W t) '' A))
  (hWm : ∀ t ∈ Icc b c, (d.W t : ℂ) ∈ ball (y : ℂ) rb)
  (hq0 : ∀ t ∈ Icc b c, ∀ z ∈ ball (y : ℂ) rb, dslope (ownExt d.W d.W' d.a d.φ t) (d.W t) z ≠ 0)
  (hV₀ : ∀ t ∈ Icc b c, HasDerivWithinAt d.V₀ (2 / (d.V₀ t - d.W t)) (Icc b c) t)
  (hG₀ : ∀ t ∈ Icc b c, HasDerivWithinAt d.G₀ (-2 * d.G₀ t / (d.V₀ t - d.W t) ^ 2) (Icc b c) t)
  (hV : ∀ m, ∀ t ∈ Icc b c, HasDerivWithinAt (d.V m) (2 / (d.V m t - d.W t)) (Icc b c) t)
  (hmcl : ∀ m, ∀ t ∈ Icc b c, ∃ ρm > (0 : ℝ), ∃ η₀ > (0 : ℝ), ∀ s ∈ Icc (max 0 (t - η₀)) (min T (t + η₀)),
    Disjoint (ball (d.V m t : ℂ) ρm) ((fun z => fwdMap d.W s z + d.W s) '' A))
  (hnt : ∀ t ∈ Icc b c, d.TimeNd t)

/-! ### Time derivatives of the time factors -/

include h hJ in
theorem A0_eq {t : ℝ} (ht : t ∈ Icc b c) : d.A 0 t = d.W' (d.a t) := h.frzA_zero (hJ ht)

include h hJ hV hmcl hnt in
/-- `∂_t B_{m,0} = 2A₁²/(B_{m,0} − A₀)` within `[b, c]`. -/
theorem hasDerivWithinAt_B0 (m : Fin n) {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivWithinAt (fun s => d.B0 s m) (2 * d.A 1 t ^ 2 / (d.B0 t m - d.A 0 t)) (Icc b c) t := by
  obtain ⟨ρm, hρm, η₀, hη₀, hcl⟩ := hmcl m t ht
  have e0 := d.A0_eq h hJ ht
  have hVF : (ownExt d.W d.W' d.a d.φ t (d.V m t)).re ≠ d.W' (d.a t) := by
    have := (hnt t ht).BA m
    rw [e0] at this
    exact sub_ne_zero.1 this
  have key := h.hasDerivWithinAt_markVal hJ (hJ ht) (hV m t ht) hρm hη₀ hcl (sub_ne_zero.1 ((hnt t ht).VW m)) hVF
  rw [e0]
  exact key

include h hJ hV hmcl hnt in
/-- `∂_t B_{m,1} = −2A₁²B_{m,1}/(A₀ − B_{m,0})² + 2/(V^m − W)² B_{m,1}` within `[b, c]`. -/
theorem hasDerivWithinAt_B1 (m : Fin n) {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivWithinAt (fun s => d.B1 s m)
      (-2 * d.A 1 t ^ 2 * d.B1 t m / (d.A 0 t - d.B0 t m) ^ 2 + 2 / (d.V m t - d.W t) ^ 2 * d.B1 t m)
      (Icc b c) t := by
  obtain ⟨ρm, hρm, η₀, hη₀, hcl⟩ := hmcl m t ht
  have e0 := d.A0_eq h hJ ht
  have hVF : (ownExt d.W d.W' d.a d.φ t (d.V m t)).re ≠ d.W' (d.a t) := by
    have := (hnt t ht).BA m
    rw [e0] at this
    exact sub_ne_zero.1 this
  have key := h.hasDerivWithinAt_markDeriv hJ (hJ ht) (hV m t ht) hρm hη₀ hcl (sub_ne_zero.1 ((hnt t ht).VW m))
    hVF
  refine key.congr_deriv ?_
  rw [e0]
  simp only [SeedData.B1, SeedData.B0, SeedData.F, SeedData.A, Function.iterate_one, Function.iterate_zero, id]
  ring

include h hv₀ hJ hG₀ hnt in
/-- `∂_t (A_{k,1}/G⁰) = −2A₁²(A_{k,1}/G⁰)/(A₀ − A_{k,0})² + 2/(V⁰ − W)² (A_{k,1}/G⁰)` within `[b, c]`. -/
theorem hasDerivWithinAt_A21 {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivWithinAt d.A21
      (-2 * d.A 1 t ^ 2 * d.A21 t / (d.A 0 t - d.A20 t) ^ 2 + 2 / (d.V₀ t - d.W t) ^ 2 * d.A21 t) (Icc b c) t := by
  have hN := (h.hasDerivWithinAt_frzImgD hv₀ (hJ ht)).mono hJ
  have hG0 := (hnt t ht).G₀
  have hVW := (hnt t ht).V₀W
  have hE : frzImg d.W' d.a d.ζ₀ t - frzA d.W d.W' d.a d.φ 0 t ≠ 0 := h.frzImg_sub_ne_zero hv₀ (hJ ht)
  have hE' : frzA d.W d.W' d.a d.φ 0 t - frzImg d.W' d.a d.ζ₀ t ≠ 0 := fun h0 => hE (by linarith)
  refine (hN.div (hG₀ t ht) hG0).congr_deriv ?_
  simp only [SeedData.A21, SeedData.A, SeedData.A20]
  field_simp
  ring

include h hv₀ hJ in
theorem hasDerivWithinAt_A20 {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivWithinAt d.A20 (2 * d.A 1 t ^ 2 / (d.A20 t - d.A 0 t)) (Icc b c) t :=
  (h.hasDerivWithinAt_frzImg hv₀ (hJ ht)).mono hJ

include h hJ in
theorem hasDerivWithinAt_L {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivWithinAt d.L (frzRate d.W d.W' d.a d.φ t) (Icc b c) t :=
  (h.hasDerivWithinAt_frzLogF (hJ ht)).mono hJ

include h hv₀ hJ hG₀ hV hmcl hnt in
/-- **The time part at height `y`**: `∂_t LT = LTT` (A19's `seedTimeT`) within `[b, c]`. -/
theorem hasDerivWithinAt_LT {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivWithinAt d.LT (d.LTT t) (Icc b c) t := by
  have h21 : d.A21 t ≠ 0 := div_ne_zero (deriv_fwdMap_real h.contW' hv₀ (h.mapsTo_clock (hJ ht))).2.ne'
    (hnt t ht).G₀
  exact hasDerivWithinAt_dualLogTime (κ := d.κ) (r := d.r) (A21 := d.A21) (L := d.L) (A20 := d.A20) (B0 := d.B0)
    (B1 := d.B1) (d.hasDerivWithinAt_A21 h hv₀ hJ hG₀ hnt ht) (d.hasDerivWithinAt_L h hJ ht)
    (d.hasDerivWithinAt_A20 h hv₀ hJ ht) (fun m => d.hasDerivWithinAt_B0 h hJ hV hmcl hnt m ht)
    (fun m => d.hasDerivWithinAt_B1 h hJ hV hmcl hnt m ht) h21 (hnt t ht).B1 (hnt t ht).A2B (hnt t ht).BB

include hV₀ hV hnt in
/-- **The time part at height `0`**: `∂_t LT0 = LT0T` within `[b, c]`. -/
theorem hasDerivWithinAt_LT0 {t : ℝ} (ht : t ∈ Icc b c) :
    HasDerivWithinAt d.LT0 (d.LT0T t) (Icc b c) t := by
  have hnt' := hnt t ht
  have c0 : HasDerivWithinAt (fun _ : ℝ => (1 : ℝ))
      (-2 * 1 ^ 2 * 1 / (d.W t - d.V₀ t) ^ 2 + 2 / (d.V₀ t - d.W t) ^ 2 * 1) (Icc b c) t := by
    refine (hasDerivWithinAt_const t (Icc b c) (1 : ℝ)).congr_deriv ?_
    rw [show (d.W t - d.V₀ t) ^ 2 = (d.V₀ t - d.W t) ^ 2 by ring]; ring
  have cm : ∀ m, HasDerivWithinAt (fun _ : ℝ => (1 : ℝ))
      (-2 * 1 ^ 2 * 1 / (d.W t - d.Vv t m) ^ 2 + 2 / (d.Vv t m - d.W t) ^ 2 * 1) (Icc b c) t := fun m => by
    refine (hasDerivWithinAt_const t (Icc b c) (1 : ℝ)).congr_deriv ?_
    rw [show (d.W t - d.Vv t m) ^ 2 = (d.Vv t m - d.W t) ^ 2 by ring]; ring
  have hA20 : HasDerivWithinAt d.V₀ (2 * 1 ^ 2 / (d.V₀ t - d.W t)) (Icc b c) t :=
    (hV₀ t ht).congr_deriv (by ring)
  have hB0 : ∀ m, HasDerivWithinAt (fun u => d.Vv u m) (2 * 1 ^ 2 / (d.Vv t m - d.W t)) (Icc b c) t :=
    fun m => (hV m t ht).congr_deriv (by simp only [SeedData.Vv]; ring)
  exact hasDerivWithinAt_dualLogTime (κ := d.κ) (r := d.r) (A21 := fun _ => (1 : ℝ)) (L := fun _ => (0 : ℝ))
    (A20 := d.V₀) (B0 := d.Vv) (B1 := fun _ _ => (1 : ℝ)) c0 (hasDerivWithinAt_const t (Icc b c) (0 : ℝ)) hA20 hB0
    cm one_ne_zero (fun _ => one_ne_zero) hnt'.V₀V hnt'.VV

/-! ### Time derivatives of the space parts and of `ℓ` -/

include h hv₀ hJ hdisj hWm hq0 hV hmcl hnt in
/-- `∂_t LS(t, x) = LST(t, x)` at a fixed real `x` of the box disc ((D1) in the removable form). -/
theorem hasDerivWithinAt_LS {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) rb)
    (hsx : d.SpaceNd t x) : HasDerivWithinAt (fun s => d.LS s x) (d.LST t x) (Icc b c) t :=
  hasDerivWithinAt_dualLogSpace_time (κ := d.κ) (r := d.r) (J := Icc b c) (f := fun s => d.F 0 s x)
    (f1 := fun s => d.F 1 s x) (A0 := d.A20) (B0 := d.B0) (h.hasDerivWithinAt_re_ownExt_box hJ hdisj hWm hq0 ht hx)
    (h.hasDerivWithinAt_re_deriv_ownExt_box hJ hdisj hWm hq0 ht hx) (d.hasDerivWithinAt_A20 h hv₀ hJ ht)
    (fun m => d.hasDerivWithinAt_B0 h hJ hV hmcl hnt m ht) hsx.F1 hsx.FA hsx.FB

include hV₀ hV in
/-- `∂_t LS0(t, x) = LS0T(t, x)` at a fixed `x` (the force ODE). -/
theorem hasDerivWithinAt_LS0 {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hsx : d.SpaceNd t x) :
    HasDerivWithinAt (fun s => d.LS0 s x) (d.LS0T t x) (Icc b c) t :=
  hasDerivWithinAt_dualLogSpace_time (κ := d.κ) (r := d.r) (J := Icc b c) (f := fun _ => x)
    (f1 := fun _ => (1 : ℝ)) (A0 := d.V₀) (B0 := d.Vv) (hasDerivWithinAt_const t _ x)
    (hasDerivWithinAt_const t _ (1 : ℝ)) (hV₀ t ht) (fun m => hV m t ht) one_ne_zero hsx.xV₀ hsx.xV

include h hv₀ hJ hdisj hWm hq0 hV₀ hG₀ hV hmcl hnt in
/-- **`∂_t ℓ = ellT`** within `[b, c]`, at every real point of the box disc where the space factors do not
degenerate. -/
theorem hasDerivWithinAt_ell {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) rb)
    (hsx : d.SpaceNd t x) : HasDerivWithinAt (fun s => d.ell s x) (d.ellT t x) (Icc b c) t :=
  ((d.hasDerivWithinAt_LT h hv₀ hJ hG₀ hV hmcl hnt ht).add
    (d.hasDerivWithinAt_LS h hv₀ hJ hdisj hWm hq0 hV hmcl hnt ht hx hsx)).sub
    ((d.hasDerivWithinAt_LT0 hV₀ hV hnt ht).add (d.hasDerivWithinAt_LS0 hV₀ hV ht hsx))

/-! ### Space derivatives -/

include h hJ hdisj in
theorem hasDerivAt_F {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) rb) (k : ℕ) :
    HasDerivAt (d.F k t) (d.F (k + 1) t x) x :=
  h.hasDerivAt_re_iterDeriv_box hJ hdisj ht hx k

include h hJ hdisj in
/-- `∂_x ℓ = ellX`. -/
theorem hasDerivAt_ell {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) rb)
    (hsx : d.SpaceNd t x) : HasDerivAt (d.ell t) (d.ellX t x) x := by
  have hF := d.hasDerivAt_F h hJ hdisj ht hx
  have e1 := hasDerivAt_dualLogSpace (κ := d.κ) (r := d.r) (A0 := d.A20 t) (B0 := d.B0 t) (hF 0) (hF 1)
    hsx.F1 hsx.FA hsx.FB
  have e2 := hasDerivAt_dualLogSpace (κ := d.κ) (r := d.r) (f := fun y => y) (f1 := fun _ => (1 : ℝ))
    (A0 := d.V₀ t) (B0 := d.Vv t) (hasDerivAt_id x) (hasDerivAt_const x (1 : ℝ)) one_ne_zero hsx.xV₀ hsx.xV
  exact (e1.const_add (d.LT t)).sub (e2.const_add (d.LT0 t))

include h hJ hdisj in
/-- `∂_x ellX = ellXX`. -/
theorem hasDerivAt_ellX {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) rb)
    (hsx : d.SpaceNd t x) : HasDerivAt (d.ellX t) (d.ellXX t x) x := by
  have hF := d.hasDerivAt_F h hJ hdisj ht hx
  have e1 := hasDerivAt_dualLogSpaceX (κ := d.κ) (r := d.r) (A0 := d.A20 t) (B0 := d.B0 t) (hF 0) (hF 1) (hF 2)
    hsx.F1 hsx.FA hsx.FB
  have e2 := hasDerivAt_dualLogSpaceX (κ := d.κ) (r := d.r) (f := fun y => y) (f1 := fun _ => (1 : ℝ))
    (f2 := fun _ => (0 : ℝ)) (A0 := d.V₀ t) (B0 := d.Vv t) (hasDerivAt_id x) (hasDerivAt_const x (1 : ℝ))
    (hasDerivAt_const x (0 : ℝ)) one_ne_zero hsx.xV₀ hsx.xV
  exact e1.sub e2

include h hJ hdisj in
/-- `∂_x ellXX = ellXXX`. -/
theorem hasDerivAt_ellXX {t : ℝ} (ht : t ∈ Icc b c) {x : ℝ} (hx : (x : ℂ) ∈ ball (y : ℂ) rb)
    (hsx : d.SpaceNd t x) : HasDerivAt (d.ellXX t) (d.ellXXX t x) x := by
  have hF := d.hasDerivAt_F h hJ hdisj ht hx
  have e1 := hasDerivAt_dualLogSpaceXX (κ := d.κ) (r := d.r) (A0 := d.A20 t) (B0 := d.B0 t) (hF 0) (hF 1) (hF 2)
    (hF 3) hsx.F1 hsx.FA hsx.FB
  have e2 := hasDerivAt_dualLogSpaceXX (κ := d.κ) (r := d.r) (f := fun y => y) (f1 := fun _ => (1 : ℝ))
    (f2 := fun _ => (0 : ℝ)) (f3 := fun _ => (0 : ℝ)) (A0 := d.V₀ t) (B0 := d.Vv t) (hasDerivAt_id x)
    (hasDerivAt_const x (1 : ℝ)) (hasDerivAt_const x (0 : ℝ)) (hasDerivAt_const x (0 : ℝ)) one_ne_zero hsx.xV₀ hsx.xV
  exact e1.sub e2

/-! ### Continuity of the time factors and of their derivatives -/

include h hv₀ hJ in
theorem sub_A0_ne {t : ℝ} (ht : t ∈ Icc b c) : d.A20 t - d.A 0 t ≠ 0 := h.frzImg_sub_ne_zero hv₀ (hJ ht)

include h hv₀ hJ in
theorem A0_sub_ne {t : ℝ} (ht : t ∈ Icc b c) : d.A 0 t - d.A20 t ≠ 0 :=
  sub_ne_zero.2 (sub_ne_zero.1 (d.sub_A0_ne h hv₀ hJ ht)).symm

include h hv₀ hJ hnt in
theorem A21_ne {t : ℝ} (ht : t ∈ Icc b c) : d.A21 t ≠ 0 :=
  div_ne_zero (deriv_fwdMap_real h.contW' hv₀ (h.mapsTo_clock (hJ ht))).2.ne' (hnt t ht).G₀

include h hv₀ hJ hG₀ hV₀ hV hmcl hnt in
/-- **Continuity of `LTT`** on `[b, c]`. -/
theorem continuousOn_LTT : ContinuousOn d.LTT (Icc b c) := by
  have cA : ∀ k, ContinuousOn (d.A k) (Icc b c) := fun k => (h.continuousOn_frzA k).mono hJ
  have c21 : ContinuousOn d.A21 (Icc b c) := fun t ht =>
    (d.hasDerivWithinAt_A21 h hv₀ hJ hG₀ hnt ht).continuousWithinAt
  have c20 : ContinuousOn d.A20 (Icc b c) := fun t ht => (d.hasDerivWithinAt_A20 h hv₀ hJ ht).continuousWithinAt
  have cB0 : ∀ m, ContinuousOn (fun t => d.B0 t m) (Icc b c) := fun m t ht =>
    (d.hasDerivWithinAt_B0 h hJ hV hmcl hnt m ht).continuousWithinAt
  have cB1 : ∀ m, ContinuousOn (fun t => d.B1 t m) (Icc b c) := fun m t ht =>
    (d.hasDerivWithinAt_B1 h hJ hV hmcl hnt m ht).continuousWithinAt
  have cV₀ : ContinuousOn d.V₀ (Icc b c) := fun t ht => (hV₀ t ht).continuousWithinAt
  have cV : ∀ m, ContinuousOn (fun t => d.Vv t m) (Icc b c) := fun m t ht => (hV m t ht).continuousWithinAt
  have cW : ContinuousOn d.W (Icc b c) := h.cont.continuousOn
  unfold SeedData.LTT seedTimeT
  refine continuousOn_dualLogTimeT (κ := d.κ) (r := d.r) (A21 := d.A21) (A20 := d.A20) (B0 := d.B0) (B1 := d.B1)
    (dA21 := fun t => -2 * d.A 1 t ^ 2 * d.A21 t / (d.A 0 t - d.A20 t) ^ 2 + 2 / (d.V₀ t - d.W t) ^ 2 * d.A21 t)
    (dL := frzRate d.W d.W' d.a d.φ) (dA20 := fun t => 2 * d.A 1 t ^ 2 / (d.A20 t - d.A 0 t))
    (dB0 := fun t m => 2 * d.A 1 t ^ 2 / (d.B0 t m - d.A 0 t))
    (dB1 := fun t m => -2 * d.A 1 t ^ 2 * d.B1 t m / (d.A 0 t - d.B0 t m) ^ 2 + 2 / (d.Vv t m - d.W t) ^ 2 * d.B1 t m)
    c21 c20 cB0 cB1 ?_ (h.continuousOn_frzRate.mono hJ) ?_ (fun m => ?_) (fun m => ?_)
    (fun t ht => d.A21_ne h hv₀ hJ hnt ht) (fun t ht => (hnt t ht).B1) (fun t ht => (hnt t ht).A2B)
    (fun t ht => (hnt t ht).BB)
  · exact (((continuousOn_const.mul ((cA 1).pow 2)).mul c21).div (((cA 0).sub c20).pow 2)
      fun t ht => pow_ne_zero 2 (d.A0_sub_ne h hv₀ hJ ht)).add
      ((continuousOn_const.div ((cV₀.sub cW).pow 2) fun t ht => pow_ne_zero 2 (hnt t ht).V₀W).mul c21)
  · exact (continuousOn_const.mul ((cA 1).pow 2)).div (c20.sub (cA 0)) fun t ht => d.sub_A0_ne h hv₀ hJ ht
  · exact (continuousOn_const.mul ((cA 1).pow 2)).div ((cB0 m).sub (cA 0)) fun t ht => (hnt t ht).BA m
  · exact (((continuousOn_const.mul ((cA 1).pow 2)).mul (cB1 m)).div (((cA 0).sub (cB0 m)).pow 2)
      fun t ht => pow_ne_zero 2 (sub_ne_zero.2 (sub_ne_zero.1 ((hnt t ht).BA m)).symm)).add
      ((continuousOn_const.div (((cV m).sub cW).pow 2) fun t ht => pow_ne_zero 2 ((hnt t ht).VW m)).mul (cB1 m))

include h hV₀ hV hnt in
/-- **Continuity of `LT0T`** on `[b, c]`. -/
theorem continuousOn_LT0T : ContinuousOn d.LT0T (Icc b c) := by
  have cV₀ : ContinuousOn d.V₀ (Icc b c) := fun t ht => (hV₀ t ht).continuousWithinAt
  have cV : ∀ m, ContinuousOn (fun t => d.Vv t m) (Icc b c) := fun m t ht => (hV m t ht).continuousWithinAt
  have cW : ContinuousOn d.W (Icc b c) := h.cont.continuousOn
  have hWV₀ : ∀ t ∈ Icc b c, d.W t - d.V₀ t ≠ 0 := fun t ht =>
    sub_ne_zero.2 (sub_ne_zero.1 (hnt t ht).V₀W).symm
  have hWV : ∀ m, ∀ t ∈ Icc b c, d.W t - d.Vv t m ≠ 0 := fun m t ht =>
    sub_ne_zero.2 (sub_ne_zero.1 ((hnt t ht).VW m)).symm
  unfold SeedData.LT0T seedTimeT
  refine continuousOn_dualLogTimeT (κ := d.κ) (r := d.r) (A21 := fun _ => (1 : ℝ)) (A20 := d.V₀) (B0 := d.Vv)
    (B1 := fun _ _ => (1 : ℝ))
    (dA21 := fun t => -2 * 1 ^ 2 * 1 / (d.W t - d.V₀ t) ^ 2 + 2 / (d.V₀ t - d.W t) ^ 2 * 1)
    (dL := fun _ => (0 : ℝ)) (dA20 := fun t => 2 * 1 ^ 2 / (d.V₀ t - d.W t))
    (dB0 := fun t m => 2 * 1 ^ 2 / (d.Vv t m - d.W t))
    (dB1 := fun t m => -2 * 1 ^ 2 * 1 / (d.W t - d.Vv t m) ^ 2 + 2 / (d.Vv t m - d.W t) ^ 2 * 1)
    continuousOn_const cV₀ cV (fun _ => continuousOn_const) ?_ continuousOn_const ?_ (fun m => ?_) (fun m => ?_)
    (fun _ _ => one_ne_zero) (fun _ _ _ => one_ne_zero) (fun t ht => (hnt t ht).V₀V) (fun t ht => (hnt t ht).VV)
  · exact (continuousOn_const.div ((cW.sub cV₀).pow 2) fun t ht => pow_ne_zero 2 (hWV₀ t ht)).add
      ((continuousOn_const.div ((cV₀.sub cW).pow 2) fun t ht => pow_ne_zero 2 (hnt t ht).V₀W).mul continuousOn_const)
  · exact continuousOn_const.div (cV₀.sub cW) fun t ht => (hnt t ht).V₀W
  · exact continuousOn_const.div ((cV m).sub cW) fun t ht => (hnt t ht).VW m
  · exact (continuousOn_const.div ((cW.sub (cV m)).pow 2) fun t ht => pow_ne_zero 2 (hWV m t ht)).add
      ((continuousOn_const.div (((cV m).sub cW).pow 2) fun t ht => pow_ne_zero 2 ((hnt t ht).VW m)).mul
        continuousOn_const)

/-! ### The seeded density is a regular log-field on the box -/

include h hv₀ hJ hdisj hWm hq0 hV₀ hG₀ hV hmcl hnt in
/-- **The seeded log-density is a regular log-field on the box** `[b, c] × (y − 3ρ, y + 3ρ)` (`3ρ ≤ r_b`), given the
nondegeneracy of the space factors there and a bound `K` for `ℓ` and its derivatives: the pathwise input of the Itô
step (A5, A8) for the seeded density of §A.1.6. -/
theorem isLogField {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 ≤ K) (h3 : 3 * ρ ≤ rb)
    (hnd : ∀ t ∈ Icc b c, ∀ x : ℝ, |x - y| < 3 * ρ → d.SpaceNd t x)
    (hb : ∀ t ∈ Icc b c, ∀ x, |x - y| < 3 * ρ → |d.ell t x| ≤ K ∧ |d.ellX t x| ≤ K ∧ |d.ellXX t x| ≤ K ∧
      |d.ellXXX t x| ≤ K ∧ |d.ellT t x| ≤ K) :
    IsLogField d.ell d.ellX d.ellXX d.ellXXX d.ellT b c y ρ K := by
  set R := Icc b c ×ˢ {x : ℝ | |x - y| < 3 * ρ} with hR
  have hfst : MapsTo Prod.fst R (Icc b c) := fun p hp => hp.1
  have cfst : ∀ g : ℝ → ℝ, ContinuousOn g (Icc b c) → ContinuousOn (fun p : ℝ × ℝ => g p.1) R :=
    fun g hg => hg.comp continuousOn_fst hfst
  have cF : ∀ k, ContinuousOn (fun p : ℝ × ℝ => d.F k p.1 p.2) R := fun k => by
    have := (h.farBox_iterDeriv hJ hdisj k).2.comp FrzData.continuous_region.continuousOn (FrzData.mapsTo_region h3)
    exact continuous_re.comp_continuousOn this
  have cA : ∀ k, ContinuousOn (fun p : ℝ × ℝ => d.A k p.1) R := fun k =>
    cfst (d.A k) ((h.continuousOn_frzA k).mono hJ)
  have c20 : ContinuousOn (fun p : ℝ × ℝ => d.A20 p.1) R :=
    cfst d.A20 fun t ht => (d.hasDerivWithinAt_A20 h hv₀ hJ ht).continuousWithinAt
  have cB0 : ∀ m, ContinuousOn (fun p : ℝ × ℝ => d.B0 p.1 m) R := fun m =>
    cfst (fun t => d.B0 t m) fun t ht => (d.hasDerivWithinAt_B0 h hJ hV hmcl hnt m ht).continuousWithinAt
  have cV₀ : ContinuousOn (fun p : ℝ × ℝ => d.V₀ p.1) R :=
    cfst d.V₀ fun t ht => (hV₀ t ht).continuousWithinAt
  have cV : ∀ m, ContinuousOn (fun p : ℝ × ℝ => d.Vv p.1 m) R := fun m =>
    cfst (d.V m) fun t ht => (hV m t ht).continuousWithinAt
  have cW : ContinuousOn (fun p : ℝ × ℝ => d.W p.1) R := (h.cont.comp continuous_fst).continuousOn
  have cLT : ContinuousOn (fun p : ℝ × ℝ => d.LT p.1) R :=
    cfst d.LT fun t ht => (d.hasDerivWithinAt_LT h hv₀ hJ hG₀ hV hmcl hnt ht).continuousWithinAt
  have cLT0 : ContinuousOn (fun p : ℝ × ℝ => d.LT0 p.1) R :=
    cfst d.LT0 fun t ht => (d.hasDerivWithinAt_LT0 hV₀ hV hnt ht).continuousWithinAt
  have n1 : ∀ p ∈ R, d.F 1 p.1 p.2 ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).F1
  have n0 : ∀ p ∈ R, d.F 0 p.1 p.2 - d.A20 p.1 ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).FA
  have nm : ∀ p ∈ R, ∀ m, d.F 0 p.1 p.2 - d.B0 p.1 m ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).FB
  have n1' : ∀ p ∈ R, (fun _ : ℝ × ℝ => (1 : ℝ)) p ≠ 0 := fun _ _ => one_ne_zero
  have n0' : ∀ p ∈ R, p.2 - d.V₀ p.1 ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).xV₀
  have nm' : ∀ p ∈ R, ∀ m, p.2 - d.Vv p.1 m ≠ 0 := fun p hp => (hnd p.1 hp.1 p.2 hp.2).xV
  have cx : ContinuousOn (fun p : ℝ × ℝ => p.2) R := continuousOn_snd
  have c1 : ContinuousOn (fun _ : ℝ × ℝ => (1 : ℝ)) R := continuousOn_const
  have c0 : ContinuousOn (fun _ : ℝ × ℝ => (0 : ℝ)) R := continuousOn_const
  refine ⟨hρ, hK, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, ?_, ?_, ?_,
    ?_, hb⟩
  · exact d.hasDerivAt_ell h hJ hdisj ht (FrzData.mem_ball_of_near h3 hx) (hnd t ht x hx)
  · exact d.hasDerivAt_ellX h hJ hdisj ht (FrzData.mem_ball_of_near h3 hx) (hnd t ht x hx)
  · exact d.hasDerivAt_ellXX h hJ hdisj ht (FrzData.mem_ball_of_near h3 hx) (hnd t ht x hx)
  · exact d.hasDerivWithinAt_ell h hv₀ hJ hdisj hWm hq0 hV₀ hG₀ hV hmcl hnt ht (FrzData.mem_ball_of_near h3 hx)
      (hnd t ht x hx)
  · exact (cLT.add (continuousOn_dualLogSpace (cF 0) (cF 1) c20 cB0 n1 n0 nm)).sub
      (cLT0.add (continuousOn_dualLogSpace cx c1 cV₀ cV n1' n0' nm'))
  · exact (continuousOn_dualLogSpaceX (cF 0) (cF 1) (cF 2) c20 cB0 n1 n0 nm).sub
      (continuousOn_dualLogSpaceX cx c1 c0 cV₀ cV n1' n0' nm')
  · exact (continuousOn_dualLogSpaceXX (cF 0) (cF 1) (cF 2) (cF 3) c20 cB0 n1 n0 nm).sub
      (continuousOn_dualLogSpaceXX cx c1 c0 c0 cV₀ cV n1' n0' nm')
  · have hdf0 := (h.continuousOn_dHat_box hJ hdisj hWm hq0).comp FrzData.continuous_region.continuousOn
      (FrzData.mapsTo_region (b := b) (c := c) (y := y) h3)
    have hdf := continuous_re.comp_continuousOn hdf0
    have hdf10 := (h.continuousOn_deriv_dHat_box hJ hdisj hWm hq0).comp FrzData.continuous_region.continuousOn
      (FrzData.mapsTo_region (b := b) (c := c) (y := y) h3)
    have hdf1 := continuous_re.comp_continuousOn hdf10
    simp only [Function.comp_def] at hdf hdf1
    have hdA0 : ContinuousOn (fun p : ℝ × ℝ => 2 * d.A 1 p.1 ^ 2 / (d.A20 p.1 - d.A 0 p.1)) R :=
      (continuousOn_const.mul ((cA 1).pow 2)).div (c20.sub (cA 0)) fun p hp => d.sub_A0_ne h hv₀ hJ hp.1
    have hdB0 : ∀ m, ContinuousOn (fun p : ℝ × ℝ => 2 * d.A 1 p.1 ^ 2 / (d.B0 p.1 m - d.A 0 p.1)) R := fun m =>
      (continuousOn_const.mul ((cA 1).pow 2)).div ((cB0 m).sub (cA 0)) fun p hp => (hnt p.1 hp.1).BA m
    have hdV₀ : ContinuousOn (fun p : ℝ × ℝ => 2 / (d.V₀ p.1 - d.W p.1)) R :=
      continuousOn_const.div (cV₀.sub cW) fun p hp => (hnt p.1 hp.1).V₀W
    have hdV : ∀ m, ContinuousOn (fun p : ℝ × ℝ => 2 / (d.V m p.1 - d.W p.1)) R := fun m =>
      continuousOn_const.div ((cV m).sub cW) fun p hp => (hnt p.1 hp.1).VW m
    have cLTT : ContinuousOn (fun p : ℝ × ℝ => d.LTT p.1) R :=
      cfst d.LTT (d.continuousOn_LTT h hv₀ hJ hV₀ hG₀ hV hmcl hnt)
    have cLT0T : ContinuousOn (fun p : ℝ × ℝ => d.LT0T p.1) R :=
      cfst d.LT0T (d.continuousOn_LT0T h hV₀ hV hnt)
    exact (cLTT.add (continuousOn_dualLogSpaceT (cF 0) (cF 1) c20 cB0 hdf hdf1 hdA0 hdB0 n1 n0 nm)).sub
      (cLT0T.add (continuousOn_dualLogSpaceT cx c1 cV₀ cV c0 c0 hdV₀ hdV n1' n0' nm'))

end Box

end SeedData

end InteractingSLE.ZhanGT4
