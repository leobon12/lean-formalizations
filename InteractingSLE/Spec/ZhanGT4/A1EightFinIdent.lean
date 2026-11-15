/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightFinView

/-!
# Zhan's A.1 (Eight): the column records' seeded logarithm in closed form

Packet PROVE-A1-EIGHTFIN. Source: Astra, *Follow-up proofs*, §A.1.6 (`ig1_followup_proofs.txt` L426–L500: (D13)–(D15),
"do not substitute the seed into the unnormalized factors") and follow-up 4 §2.5 (L739–L788).

For the column records `srcRec W₁ S V₂ t …` of one protected rectangle (`ViewSetup`):

* `SeedData.ell_eq_zero_of_identity`, `ell_srcRec_zero_height`: at frozen height `0` (identity chart) the raw
  seeded logarithm `ell s x` vanishes at every own time and every position;
* `normEll_srcRec_own_zero`: when the one-source fused exponent `−1/2 + Σ −(κ/4) r_m` vanishes (the Eight charges),
  the normalized logarithm vanishes at own time `0` at every height (A22's `normEll_zero_eq_fused_axis`);
* `normEll_srcRec_eq_ell`: at positive heights and positive own times the normalized logarithm is the raw one at the
  driver (A22's remote scales and interval bounds rule out every collision).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1EightFin

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed

variable {n : ℕ}

/-! ### Frozen height zero: the raw logarithm vanishes -/

section HeightZero

/-- **The raw seeded logarithm vanishes for the identity chart**: with `F_t = id`, unit derivative factors, the other
tip's image at its own coordinate and no two-time factor, `ell t x = 0` at every position `x`. -/
theorem _root_.InteractingSLE.ZhanGT4.SeedData.ell_eq_zero_of_identity (d : SeedData n) (t x : ℝ)
    (hf : d.F 0 t = id) (hf1 : d.F 1 t x = 1) (h21 : Real.log (d.A21 t) = 0) (hB : ∀ m, d.B1 t m = 1)
    (h20 : d.A20 t = d.V₀ t) (hL : d.L t = 0) : d.ell t x = 0 := by
  have hB0 : d.B0 t = d.Vv t := by
    funext m
    change d.F 0 t (d.V m t) = d.V m t
    rw [hf]
    rfl
  have hB1 : d.B1 t = fun _ => 1 := funext hB
  have hx : d.F 0 t x = x := by rw [hf]; rfl
  simp only [SeedData.ell, SeedData.LT, SeedData.LT0, SeedData.LS, SeedData.LS0, hB0, hB1, h20, hL, hx, hf1,
    dualLogTime, h21, Real.log_one, mul_zero]
  ring

/-- **The raw seeded logarithm of a record with the identity chart vanishes** on the horizon, at every position. -/
theorem ell_fromSource_empty_eq_zero {W c J : ℝ → ℝ} {T : ℝ} (h : OwnData W ∅ id T c J) (κ : ℝ)
    (rr : Fin n → ℝ) (p : ℝ) (V : Fin n → ℝ → ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : ℝ) :
    (SeedData.fromSource W J c id κ rr p p V).ell s x = 0 := by
  have hext : ∀ v ∈ Icc (0 : ℝ) T, ownExt W J c id v = id := fun v hv => h.ownExt_eq_of_empty hv
  have hclk : c s = s := h.clock_eq_of_empty hs
  have himg : fwdMap J (c s) = fwdMap W s := by
    funext z
    rw [hclk]
    exact Ito.fwdMap_congr_of_eqOn fun v hv => h.W'_eq_of_empty ⟨hv.1, hv.2.trans hs.2⟩
  have hdrv : J (c s) = W s := by rw [hclk]; exact h.W'_eq_of_empty hs
  have hd1 : ∀ y : ℝ, (deriv^[1] (ownExt W J c id s) y).re = 1 := fun y => by
    rw [hext s hs, Function.iterate_one, deriv_id']
    simp
  refine SeedData.ell_eq_zero_of_identity _ s x ?_ (hd1 x) ?_ (fun m => hd1 _) ?_ ?_
  · funext y
    change (deriv^[0] (ownExt W J c id s) y).re = y
    rw [hext s hs]
    simp
  · change Real.log ((deriv (fwdMap J (c s)) p).re / (deriv (fwdMap W s) p).re) = 0
    rw [himg, Real.log_div_self]
  · change (fwdMap J (c s) p).re + J (c s) = (fwdMap W s p).re + W s
    rw [himg, hdrv]
  · change frzLogF W J c id s = 0
    unfold frzLogF
    have e : ∀ v ∈ uIcc (0 : ℝ) s, frzRate W J c id v = 0 := fun v hv => by
      rw [uIcc_of_le hs.1] at hv
      have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv.1, hv.2.trans hs.2⟩
      unfold frzRate frzA
      rw [hext v hvT, show (2 : ℕ) = 0 + 2 from rfl, iterate_deriv_id_two_add 0,
        show (3 : ℕ) = 1 + 2 from rfl, iterate_deriv_id_two_add 1]
      simp
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_zero]

/-- **At frozen height zero the record's raw seeded logarithm vanishes** on the horizon, at every position. -/
theorem ell_srcRec_zero_height {W Wf : ℝ → ℝ} {T κ p : ℝ} {rr : Fin n → ℝ} {V : Fin n → ℝ → ℝ}
    (hWf : Continuous Wf) (hWf0 : Wf 0 = p) (hex : ∃ a W', OwnData W (fwdHull Wf 0) (frzChart Wf 0) T a W') {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (x : ℝ) : (srcRec W T Wf 0 κ rr p V).ell s x = 0 := by
  have hown := ownData_imgChain hex
  have hK : fwdHull Wf 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hWf
  have hφ : frzChart Wf 0 = id := frzChart_zero_eq_id Wf
  unfold srcRec
  rw [hK, hφ] at hown ⊢
  rw [hWf0]
  exact ell_fromSource_empty_eq_zero hown κ rr p V hs x

end HeightZero

/-! ### Own time zero and positive own times -/

section Record

variable {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}

/-- `γ(0) = 0`: a vanishing exponent has vanishing conformal weight. -/
theorem dualGamma_zero (κ : ℝ) : dualGamma κ 0 = 0 := by
  simp only [dualGamma, mul_zero, zero_mul, add_zero]

/-- **With vanishing fused exponent the records' normalized logarithm vanishes at own time zero**, at every height
`t ≤ Y` (A22's fused-axis formula at the coincident entrance, `normEll_zero_eq_fused_axis`). -/
theorem normEll_srcRec_own_zero (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {κ : ℝ} (hκ : κ ≠ 0)
    {rr : Fin n → ℝ} (hE : -1 / 2 + ∑ m, -(κ / 4) * rr m = 0) {V : Fin n → ℝ → ℝ} (hV : ∀ m, V m 0 = W₁ 0)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y) : (srcRec W₁ S V₂ t κ rr p V).normEll 0 = 0 := by
  obtain ⟨hown, v, hv⟩ := h.sOwn ht
  have hG : (deriv (fwdMap W₁ 0) p).re = 1 := by
    have e : fwdMap W₁ 0 = fun z : ℂ => z - (W₁ 0 : ℂ) := funext (fwdMap_zero_eq_sub W₁)
    rw [e, deriv_sub_const, deriv_id'', Complex.one_re]
  rw [srcRec_eq_sSel W₁ V₂ h.pos₁.le ht.2]
  have hax := SeedData.normEll_zero_eq_fused_axis
    (SeedData.fromSource W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
      (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) κ rr (V₂ t) p V) hown hκ hv hV hG
  rw [hax]
  change dualGamma (16 / κ) (-1 / 2 + ∑ m, -(κ / 4) * rr m) * _ + (-1 / 2 + ∑ m, -(κ / 4) * rr m) * _ = 0
  rw [hE, dualGamma_zero, zero_mul, zero_mul, add_zero]

/-- **At positive heights and positive own times the normalized logarithm is the raw one at the driver**: the
remote scales (`exists_seed_remoteScale_right`) and the interval derivative bounds
(`exists_seed_interval_own_bounds_right`) give every noncollision of `normEll_eq_ell`. -/
theorem normEll_srcRec_eq_ell (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) (κ : ℝ) (rr : Fin n → ℝ)
    {V : Fin n → ℝ → ℝ} (hVs : ∀ m, IsSeedCoordinate W₁ (V m) S)
    (hVI : ∀ u ∈ Icc (0 : ℝ) S, ∀ m, V m u ∈ uIcc (Vlo u) (Vhi u))
    (hVV : ∀ u ∈ Ioc (0 : ℝ) S, Function.Injective fun m => V m u) {t a : ℝ} (ht : t ∈ Ioc (0 : ℝ) Y)
    (ha : a ∈ Ioc (0 : ℝ) S) :
    (srcRec W₁ S V₂ t κ rr p V).normEll a = (srcRec W₁ S V₂ t κ rr p V).ell a (W₁ a) := by
  have htI : t ∈ Icc (0 : ℝ) Y := Ioc_subset_Icc_self ht
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  obtain ⟨hown, -⟩ := h.sOwn htI
  rw [srcRec_eq_sSel W₁ V₂ h.pos₁.le ht.2]
  set d := SeedData.fromSource W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
    (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) κ rr (V₂ t) p V with hd
  have hW0H : ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono h.K₁ (start_mem_closure_fwdHull h.cont₁ h.pos₁)
  have hV₂H : ((V₂ 0 : ℝ) : ℂ) ∈ closure H₂ := by rw [h.zero₂]; exact h.pp.src
  have hK₂t : fwdHull V₂ t ⊆ H₂ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans h.K₂
  obtain ⟨r, L₀, hr, -, hinterval⟩ := exists_seed_interval_own_bounds_right h.pp.hull₁ h.pp.hull₂ h.pp.sep_pos
    h.pp.sep h.pp.rad_pos h.pp.prot Tm
  have hint := hinterval W₁ V₂ Vlo Vhi S t _ _ hown h.cont₂ ht.1 hW0H hV₂H
    (by rw [h.zero₁]; exact h.pp.prot_pos) (by rw [h.zero₂]; exact h.pp.prot_lt) (ht.2.trans h.le₂) h.K₁ hK₂t
    h.lo h.hi a haI
  obtain ⟨Lrem, -, hrem⟩ := exists_seed_remoteScale_right h.pp.hull₁ h.pp.hull₂ h.pp.sep_pos h.pp.sep h.pp.src
    h.pp.prot_pos h.pp.prot_lt h.pp.rad_pos h.pp.prot Tm
  have hremote : d.RemoteScale a Lrem := hrem κ rr W₁ V₂ _ _ Vlo Vhi V S t hown h.cont₂ h.zero₂ ht.1
    (ht.2.trans h.le₂) h.le₁ h.K₁ hK₂t h.lo h.hi h.drv hVI a haI
  have hdiff : ∀ x ∈ uIcc (Vlo a) (Vhi a), DifferentiableAt ℂ (ownExt d.W d.W' d.a d.φ a) x := by
    intro x hx
    have hdo := (hown.ownExt_props haI (hint x hx).1).1
    exact hdo.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  apply d.normEll_eq_ell_of_gapVal_ne
  exact d.gapVal_ne_zero_of_remoteScale hremote (convex_uIcc _ _)
    (fun x hx => (hdiff x hx).hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt)
    (fun x hx => (Real.exp_pos _).trans_le (hint x hx).2.1)
    (fun x hx => (d.deriv_F_zero (hdiff x hx)).symm) (h.drv a haI) (hVI a haI)
    (fun m => (hVs m).ne a ha) (hVV a ha)

end Record

end InteractingSLE.ZhanGT4.A1EightFin
