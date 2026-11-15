/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightFinRecip
import InteractingSLE.Spec.ZhanGT4.A1G3CalcRecord

/-!
# Zhan's A.1 (G3): the row of the seeded field with an ordinary mark is the opposite view's logarithm

Packet PROVE-A1-G3ROW2. Source: Astra, *Follow-up proofs*, §A.1.1–A.1.3 and (D6) (`ig1_followup_proofs.txt`
L190–L355: "the normalised density is the same in both views"; "the same argument at each protected force mark
controls all derivative and distance ratios in (D6)") and follow-up 4 §2.5 (L739–L788).

A1-EIGHTFIN proved the row identity of one protected rectangle for seed marks only (`normEll_srcRec_sub_eq_eView`):
the marks there lie in the seed interval `[V_lo, V_hi]` and the fused exponent vanishes. In (G3) the small curve also
carries an **ordinary mark** `x` (right of the seeds, at its own original coordinate), so the marks lie in the extended
interval `[V_lo(t), g_t(q) + W_t]` of A1-G3CALC. This file proves the part of the row identity that does not see the
own-time-`0` normalization, for marks anywhere in the extended interval:

* `G3Setup`: A1-EIGHTFIN's `ViewSetup` plus A1-G3CALC's segment condition, the driver and the marks in the extended
  interval, the marks mark coordinates and distinct at positive times;
* `exists_ext_clear`: one radius clears every point of the extended interval from every frozen large hull;
* `access_of_clear`, `eView_factors_of_clear`, `ell_eView_eq_of_clear`: A1-EIGHTFIN's factor identities and
  reciprocity for any mark with a clearance (seeds and ordinary marks alike);
* `normEll_srcRec_eq_ell_ext`: at positive heights and own times the normalized logarithm is the raw one;
* **`normEll_srcRec_eq_eView_sub`**: at a positive own time `a ≤ S` and every height `t ≤ Y`,
  `d_t.normEll a = e.ell t (V₂ t − p) − e.ell 0 0` (`e` the opposite view frozen at `a`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1G3Id

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed A1EightFin A1G3Calc

variable {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}

/-- **One protected rectangle with seeds and ordinary marks**: A1-EIGHTFIN's `ViewSetup`, the segment `(0, q]` clear
of the large enclosure (`IsProtectedPairG.seg`), the small driver and the marks `V` in the extended interval
`[V_lo(u), g_u(q) + W_u]`, the marks mark coordinates of the small driver, distinct at positive own times. -/
structure G3Setup (H₁ H₂ : Set ℂ) (δ p q dd Tm : ℝ) (W₁ V₂ : ℝ → ℝ) (S Y : ℝ) (Vlo Vhi : ℝ → ℝ)
    (V : Fin n → ℝ → ℝ) : Prop where
  view : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi
  seg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖
  drvE : ∀ u ∈ Icc (0 : ℝ) S, W₁ u ∈ uIcc (Vlo u) ((fwdMap W₁ u q).re + W₁ u)
  marks : ∀ u ∈ Icc (0 : ℝ) S, ∀ m, V m u ∈ uIcc (Vlo u) ((fwdMap W₁ u q).re + W₁ u)
  mark : ∀ m, IsMarkCoordinate W₁ (V m) S
  inj : ∀ u ∈ Ioc (0 : ℝ) S, Function.Injective fun m => V m u

/-! ### Clearance and the opposite view's factors -/

/-- **One radius clears the whole extended interval from every frozen large hull**: there is `r > 0` such that at
every own time `a ≤ S`, every point of `[V_lo(a), g_a(q) + W_a]` has its `r`-disc disjoint from the small chart's
image of the large hull at every height `t ≤ Y`. -/
theorem exists_ext_clear {V : Fin n → ℝ → ℝ} (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V) :
    ∃ r > (0 : ℝ), ∀ a ∈ Icc (0 : ℝ) S, ∀ x ∈ uIcc (Vlo a) ((fwdMap W₁ a q).re + W₁ a),
      ∀ t ∈ Icc (0 : ℝ) Y, Disjoint (ball (x : ℂ) r) ((fun z => fwdMap W₁ a z + W₁ a) '' fwdHull V₂ t) := by
  have hv := h.view
  obtain ⟨r, L₀, hr, -, hinterval⟩ := exists_ext_interval_own_bounds_right hv.pp.hull₁ hv.pp.hull₂ hv.pp.sep_pos
    hv.pp.sep hv.pp.prot_pos hv.pp.rad_pos hv.pp.prot h.seg Tm
  have hW0H : ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono hv.K₁ (start_mem_closure_fwdHull hv.cont₁ hv.pos₁)
  have hV₂H : ((V₂ 0 : ℝ) : ℂ) ∈ closure H₂ := by rw [hv.zero₂]; exact hv.pp.src
  refine ⟨r, hr, fun a ha x hx t ht => ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty hv.cont₂, Set.image_empty]
    exact disjoint_empty _
  · obtain ⟨hown, -⟩ := hv.sOwn ht
    have hK₂t : fwdHull V₂ t ⊆ H₂ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hv.K₂
    exact (hinterval W₁ V₂ Vlo Vhi S t _ _ hown hv.cont₂ hpos hW0H hV₂H (by rw [hv.zero₂]; exact hv.pp.prot_lt)
      (ht.2.trans hv.le₂) hv.K₁ hK₂t hv.lo hv.hi a ha x hx).1

/-- **A cleared real point is an access of the opposite view**: at own time `a ≤ S`, a real point `v` whose disc of a
positive radius misses the small chart's image of every large hull up to `Y` is alive for the opposite image chain as
`v − p`, and the column records' own map at `v` has value `frzImg (v − p) + p` and derivative `frzImgD (v − p)` of the
opposite image chain, at every height `t ≤ Y`. -/
theorem access_of_clear (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    {v ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ t ∈ Icc (0 : ℝ) Y, Disjoint (ball (v : ℂ) ρ) ((fun z => fwdMap W₁ a z + W₁ a) '' fwdHull V₂ t)) :
    ∃ qv, IsForwardSol (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a) ((v - V₂ 0 : ℝ) : ℂ)
        (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a Y) qv ∧
      ∀ t ∈ Icc (0 : ℝ) Y,
        (ownExt W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
            (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) a v).re =
          frzImg (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a)
            (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a) (v - V₂ 0) t + V₂ 0 ∧
        (deriv (ownExt W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
            (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) a) v).re =
          frzImgD (tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a)
            (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a) (v - V₂ 0) t :=
  OwnData.seed_access_value_deriv_translated (fun _ ht => (h.sOwn ht).1) ha (h.tOwn ha).1 hρ hc

/-- **The factor identities at one corner** `(a, t)` for marks with clearances (A1-EIGHTFIN's `eView_factors`, the
marks only cleared rather than in the seed interval): every factor of the opposite view at its own time `t` is a factor
of the column record at own time `a`, translated by `−p` where it is a value. -/
theorem eView_factors_of_clear (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {κ : ℝ} (rr : Fin n → ℝ)
    {V : Fin n → ℝ → ℝ} {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) Y)
    (hclr : ∀ m, ∃ ρ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) Y,
      Disjoint (ball ((V m a : ℝ) : ℂ) ρ) ((fun z => fwdMap W₁ a z + W₁ a) '' fwdHull V₂ t)) :
    (eView κ rr W₁ V₂ S Y V a).F 0 t (V₂ t - V₂ 0) = (srcRec W₁ S V₂ t κ rr p V).A20 a - V₂ 0 ∧
      (eView κ rr W₁ V₂ S Y V a).F 1 t (V₂ t - V₂ 0) =
        (srcRec W₁ S V₂ t κ rr p V).A21 a * (deriv (fwdMap W₁ a) p).re ∧
      (eView κ rr W₁ V₂ S Y V a).A20 t = (srcRec W₁ S V₂ t κ rr p V).A 0 a - V₂ 0 ∧
      (eView κ rr W₁ V₂ S Y V a).A21 t = (srcRec W₁ S V₂ t κ rr p V).A 1 a ∧
      (∀ m, (eView κ rr W₁ V₂ S Y V a).B0 t m = (srcRec W₁ S V₂ t κ rr p V).B0 a m - V₂ 0) ∧
      (∀ m, (eView κ rr W₁ V₂ S Y V a).B1 t m = (srcRec W₁ S V₂ t κ rr p V).B1 a m) ∧
      frzLogF (eView κ rr W₁ V₂ S Y V a).W (eView κ rr W₁ V₂ S Y V a).W' (eView κ rr W₁ V₂ S Y V a).a
        (eView κ rr W₁ V₂ S Y V a).φ t = (srcRec W₁ S V₂ t κ rr p V).L a ∧
      0 < (srcRec W₁ S V₂ t κ rr p V).A21 a := by
  rw [srcRec_eq_sSel W₁ V₂ h.pos₁.le ht.2]
  set as := sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) with has
  set Ws := sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) with hWs
  set bt := tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) with hbt
  set Wt := tSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) with hWt
  set d := SeedData.fromSource W₁ (Ws t) (as t) (frzChart V₂ t) κ rr (V₂ t) p V with hd
  set e := eView κ rr W₁ V₂ S Y V a with he
  obtain ⟨hs, v, hv⟩ := h.sOwn ht
  obtain ⟨ht', w, hw⟩ := h.tOwn ha
  have hG := h.srcDeriv_pos ha
  have a0 := sView_F_zero (κ := κ) (r := rr) (p := fun _ => (0 : ℝ)) hs ha ht' ht hw
  have a1 := sView_F_one (κ := κ) (r := rr) (p := fun _ => (0 : ℝ)) hs ha ht' ht hw
  have b0 := tView_F_zero (κ := κ) (r := rr) (p := fun _ => (0 : ℝ)) hs ha ht' ht hv
  have b1 := tView_F_one (κ := κ) (r := rr) (p := fun _ => (0 : ℝ)) hs ha ht' ht hv
  have hL := ((h.twoViewRect).mono ha ht).frzLogF_eq
  have hF0 : e.F 0 t (V₂ t - V₂ 0) = d.A20 a - V₂ 0 := b0
  have hF1 : e.F 1 t (V₂ t - V₂ 0) = d.A21 a * (deriv (fwdMap W₁ a) p).re := by
    change _ = frzImgD (Ws t) (as t) (V₂ t) a / (deriv (fwdMap W₁ a) p).re * (deriv (fwdMap W₁ a) p).re
    rw [div_mul_cancel₀ _ hG.ne']
    exact b1
  have h20 : e.A20 t = d.A 0 a - V₂ 0 := by
    have : d.A 0 a = (tView κ rr W₁ V₂ bt Wt (fun _ => (0 : ℝ)) a).A20 t + V₂ 0 := a0
    rw [this]
    change (tView κ rr W₁ V₂ bt Wt (fun _ => (0 : ℝ)) a).A20 t = _
    ring
  have h21 : e.A21 t = d.A 1 a := a1.symm
  have hB0 : ∀ m, e.B0 t m = d.B0 a m - V₂ 0 := fun m => by
    obtain ⟨ρ, hρ, hc⟩ := hclr m
    obtain ⟨_, -, hacc⟩ := access_of_clear h ha hρ hc
    have hb := (hacc t ht).1
    change frzImg (Wt a) (bt a) (V m a - V₂ 0) t = (ownExt W₁ (Ws t) (as t) (frzChart V₂ t) a (V m a)).re - V₂ 0
    linarith
  have hB1 : ∀ m, e.B1 t m = d.B1 a m := fun m => by
    obtain ⟨ρ, hρ, hc⟩ := hclr m
    obtain ⟨_, -, hacc⟩ := access_of_clear h ha hρ hc
    exact (hacc t ht).2.symm
  have hd21 : 0 < d.A21 a := by
    have hax := hs.mapsTo_clock ha
    have hpos := (deriv_fwdMap_real hs.contW' hv hax).2
    exact div_pos hpos hG
  exact ⟨hF0, hF1, h20, h21, hB0, hB1, hL.symm, hd21⟩

/-- **Reciprocity at one corner** `(a, t)` for marks with clearances (A1-EIGHTFIN's `ell_eView_eq`): the opposite
view's raw logarithm at its driver is the column record's raw logarithm at its driver plus the small curve's one-curve
reference terms and the source factor, which do not depend on the height `t`. -/
theorem ell_eView_eq_of_clear (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {κ : ℝ} (hκ : κ ≠ 0)
    (rr : Fin n → ℝ) {V : Fin n → ℝ → ℝ} {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) Y)
    (hclr : ∀ m, ∃ ρ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) Y,
      Disjoint (ball ((V m a : ℝ) : ℂ) ρ) ((fun z => fwdMap W₁ a z + W₁ a) '' fwdHull V₂ t)) :
    (eView κ rr W₁ V₂ S Y V a).ell t (V₂ t - V₂ 0) =
      (srcRec W₁ S V₂ t κ rr p V).ell a (W₁ a) +
        ((srcRec W₁ S V₂ t κ rr p V).LT0 a + (srcRec W₁ S V₂ t κ rr p V).LS0 a (W₁ a)) +
          dualAlpha (16 / κ) * Real.log (deriv (fwdMap W₁ a) p).re := by
  obtain ⟨hF0, hF1, h20, h21, hB0, hB1, hL, hd21⟩ := eView_factors_of_clear h (κ := κ) rr ha ht hclr
  exact seed_access_log_reciprocity_translated _ _ hκ rfl rfl hF0 hF1 h20 h21 hB0 hB1 hL hd21.ne'
    (h.srcDeriv_pos ha).ne'

/-- The marks of a `G3Setup` at an own time `a ≤ S` have a common clearance from every frozen large hull. -/
theorem mark_clear {V : Fin n → ℝ → ℝ} (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) S) : ∀ m, ∃ ρ > (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) Y,
      Disjoint (ball ((V m a : ℝ) : ℂ) ρ) ((fun z => fwdMap W₁ a z + W₁ a) '' fwdHull V₂ t) := by
  obtain ⟨r, hr, hclr⟩ := exists_ext_clear h
  exact fun m => ⟨r, hr, fun t ht => hclr a ha _ (h.marks a ha m) t ht⟩

/-! ### Positive own times -/

/-- **At positive heights and positive own times the normalized logarithm is the raw one at the driver**, for marks in
the extended interval (A1-EIGHTFIN's `normEll_srcRec_eq_ell` with A1-G3CALC's extended remote scales and interval
bounds). -/
theorem normEll_srcRec_eq_ell_ext {V : Fin n → ℝ → ℝ} (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V) (κ : ℝ)
    (rr : Fin n → ℝ) {t a : ℝ} (ht : t ∈ Ioc (0 : ℝ) Y) (ha : a ∈ Ioc (0 : ℝ) S) :
    (srcRec W₁ S V₂ t κ rr p V).normEll a = (srcRec W₁ S V₂ t κ rr p V).ell a (W₁ a) := by
  have hv := h.view
  have htI : t ∈ Icc (0 : ℝ) Y := Ioc_subset_Icc_self ht
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  obtain ⟨hown, -⟩ := hv.sOwn htI
  rw [srcRec_eq_sSel W₁ V₂ hv.pos₁.le ht.2]
  set d := SeedData.fromSource W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
    (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) κ rr (V₂ t) p V with hd
  have hW0H : ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono hv.K₁ (start_mem_closure_fwdHull hv.cont₁ hv.pos₁)
  have hV₂H : ((V₂ 0 : ℝ) : ℂ) ∈ closure H₂ := by rw [hv.zero₂]; exact hv.pp.src
  have hK₂t : fwdHull V₂ t ⊆ H₂ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hv.K₂
  obtain ⟨r, L₀, hr, -, hinterval⟩ := exists_ext_interval_own_bounds_right hv.pp.hull₁ hv.pp.hull₂ hv.pp.sep_pos
    hv.pp.sep hv.pp.prot_pos hv.pp.rad_pos hv.pp.prot h.seg Tm
  have hint := hinterval W₁ V₂ Vlo Vhi S t _ _ hown hv.cont₂ ht.1 hW0H hV₂H
    (by rw [hv.zero₂]; exact hv.pp.prot_lt) (ht.2.trans hv.le₂) hv.K₁ hK₂t hv.lo hv.hi a haI
  obtain ⟨Lrem, -, hrem⟩ := exists_ext_remoteScale_right hv.pp.hull₁ hv.pp.hull₂ hv.pp.sep_pos hv.pp.sep hv.pp.src
    hv.pp.prot_pos hv.pp.prot_lt hv.pp.rad_pos hv.pp.prot h.seg Tm
  have hremote : d.RemoteScale a Lrem := hrem κ rr W₁ V₂ _ _ Vlo Vhi V S t hown hv.cont₂ hv.zero₂ ht.1
    (ht.2.trans hv.le₂) hv.le₁ hv.K₁ hK₂t hv.lo hv.hi h.drvE h.marks a haI
  have hdiff : ∀ x ∈ uIcc (Vlo a) ((fwdMap W₁ a q).re + W₁ a),
      DifferentiableAt ℂ (ownExt d.W d.W' d.a d.φ a) x := by
    intro x hx
    have hdo := (hown.ownExt_props haI (hint x hx).1).1
    exact hdo.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  apply d.normEll_eq_ell_of_gapVal_ne
  exact d.gapVal_ne_zero_of_remoteScale hremote (convex_uIcc _ _)
    (fun x hx => (hdiff x hx).hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt)
    (fun x hx => (Real.exp_pos _).trans_le (hint x hx).2.1)
    (fun x hx => (d.deriv_F_zero (hdiff x hx)).symm) (h.drvE a haI) (h.marks a haI)
    (fun m => (h.mark m).ne a ha) (h.inj a ha)

/-! ### The row without the own-time-`0` normalization -/

/-- **The column records' normalized logarithm at a positive own time is the opposite view's logarithm increment**:
at a positive own time `a ≤ S` and every height `t ≤ Y`,
`d_t.normEll a = e.ell t (V₂ t − p) − e.ell 0 (V₂ 0 − p)`, `e = eView … a` the opposite view (curve `1` frozen at
`a`) with the marks' accesses as marks. Seeds and ordinary marks are treated alike; no fused exponent is assumed (the
own-time-`0` value `d_t.normEll 0` is computed separately). -/
theorem normEll_srcRec_eq_eView_sub {V : Fin n → ℝ → ℝ} (h : G3Setup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi V)
    {κ : ℝ} (hκ : κ ≠ 0) (rr : Fin n → ℝ) {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Y) :
    (srcRec W₁ S V₂ t κ rr p V).normEll a =
      (eView κ rr W₁ V₂ S Y V a).ell t (V₂ t - V₂ 0) - (eView κ rr W₁ V₂ S Y V a).ell 0 (V₂ 0 - V₂ 0) := by
  have hv := h.view
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  have h0Y : (0 : ℝ) ∈ Icc (0 : ℝ) Y := ⟨le_rfl, hv.pos₂.le⟩
  have hex : ∃ c W', OwnData W₁ (fwdHull V₂ 0) (frzChart V₂ 0) S c W' := ⟨_, _, (hv.sOwn h0Y).1⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [normEll_srcRec_zero_height hv.cont₂ hv.zero₂ hex haI, sub_self]
  · have hclr := mark_clear h haI
    have r_t := ell_eView_eq_of_clear hv hκ rr haI ht hclr
    have r_0 := ell_eView_eq_of_clear hv hκ rr haI h0Y hclr
    have hz : (srcRec W₁ S V₂ 0 κ rr p V).ell a (W₁ a) = 0 :=
      ell_srcRec_zero_height hv.cont₂ hv.zero₂ hex haI _
    have hC : (srcRec W₁ S V₂ t κ rr p V).LT0 a + (srcRec W₁ S V₂ t κ rr p V).LS0 a (W₁ a) =
        (srcRec W₁ S V₂ 0 κ rr p V).LT0 a + (srcRec W₁ S V₂ 0 κ rr p V).LS0 a (W₁ a) := rfl
    rw [normEll_srcRec_eq_ell_ext h κ rr ⟨hpos, ht.2⟩ ha, r_t, r_0, hz, hC]
    ring

end InteractingSLE.ZhanGT4.A1G3Id
