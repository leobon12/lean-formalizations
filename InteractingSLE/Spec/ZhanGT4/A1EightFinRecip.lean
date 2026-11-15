/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightFinIdent

/-!
# Zhan's A.1 (Eight): the row of the seeded field is the opposite view's fused logarithm

Packet PROVE-A1-EIGHTFIN. Source: Astra, *Follow-up proofs*, §A.1.1–A.1.2 and (D6) (`ig1_followup_proofs.txt`
L190–L296) and follow-up 4 §2.5 (L739–L788: "the seed factors are evaluated at the integrated seed coordinates; the
opposite view reads them as boundary accesses of the frozen hull").

For one protected rectangle (`ViewSetup`) with column records `d t = srcRec W₁ S V₂ t κ rr p V` (curve `2` frozen at
height `t`) and the opposite view `e = eView κ rr W₁ V₂ S Y V a` (curve `1` frozen at own time `a`):

* `exists_seed_access_clear`: one radius clears every point of the seed interval from every frozen large hull
  (A22's interval bounds, uniformly in the height);
* `eView_marks`: the seed accesses are alive for the opposite image chain, and the column records' seed factors are
  the opposite view's mark factors (`OwnData.seed_access_value_deriv_translated`);
* **`ell_eView_eq`** (reciprocity): `e.ell t (V₂ t − p) = d_t.ell a (W₁ a) + C(a)` with `C(a)` the small curve's
  one-curve reference terms (independent of `t`), from A15's driver/tip interchange, the two-time factor
  (`TwoViewRect.frzLogF_eq`) and A22's translated reciprocity algebra;
* **`normEll_srcRec_sub_eq_eView`**: with vanishing fused exponent (Eight), at every height `t ≤ Y`,
  `d_t.normEll a − d_t.normEll 0 = e.ell t (V₂ t − p) − e.ell 0 0`: the row of the seeded field is the exponential of
  the opposite view's (fused) logarithm, normalized at height `0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1EightFin

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed

variable {n : ℕ} {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}

namespace ViewSetup

variable (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi)
include h

/-- **One radius clears the whole seed interval from every frozen large hull**: there is `r > 0` such that at every own
time `a ≤ S`, every point of `[Vlo a, Vhi a]` has its `r`-disc disjoint from the small chart's image of the large
hull at every height `t ≤ Y`. -/
theorem exists_seed_access_clear : ∃ r > (0 : ℝ), ∀ a ∈ Icc (0 : ℝ) S, ∀ x ∈ uIcc (Vlo a) (Vhi a),
    ∀ t ∈ Icc (0 : ℝ) Y, Disjoint (ball (x : ℂ) r) ((fun z => fwdMap W₁ a z + W₁ a) '' fwdHull V₂ t) := by
  obtain ⟨r, L₀, hr, -, hinterval⟩ := exists_seed_interval_own_bounds_right h.pp.hull₁ h.pp.hull₂ h.pp.sep_pos
    h.pp.sep h.pp.rad_pos h.pp.prot Tm
  have hW0H : ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono h.K₁ (start_mem_closure_fwdHull h.cont₁ h.pos₁)
  have hV₂H : ((V₂ 0 : ℝ) : ℂ) ∈ closure H₂ := by rw [h.zero₂]; exact h.pp.src
  refine ⟨r, hr, fun a ha x hx t ht => ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty h.cont₂, Set.image_empty]
    exact disjoint_empty _
  · obtain ⟨hown, -⟩ := h.sOwn ht
    have hK₂t : fwdHull V₂ t ⊆ H₂ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans h.K₂
    exact (hinterval W₁ V₂ Vlo Vhi S t _ _ hown h.cont₂ hpos hW0H hV₂H (by rw [h.zero₁]; exact h.pp.prot_pos)
      (by rw [h.zero₂]; exact h.pp.prot_lt) (ht.2.trans h.le₂) h.K₁ hK₂t h.lo h.hi a ha x hx).1

/-- The large curve's source `p` is alive for the small driver up to `S`. -/
theorem exists_src_alive : ∃ u, IsForwardSol W₁ (p : ℂ) S u := by
  have hpne : p ≠ W₁ 0 := by rw [h.zero₁]; exact (h.pp.prot_pos.trans h.pp.prot_lt).ne'
  refine exists_isForwardSol_of_disjoint_ball_gen h.cont₁ hpne h.pos₁.le h.pp.sep_pos ?_
  refine Set.disjoint_left.2 fun z hz hzK => ?_
  have h1 := le_norm_of_mem_closure h.pp.sep h.pp.src (h.K₁ hzK)
  rw [mem_ball, dist_eq_norm] at hz
  rw [norm_sub_rev] at h1
  linarith [h.pp.sep_pos]

/-- The source factor `G₀(a) = Re g_a'(p)` is positive on the horizon. -/
theorem srcDeriv_pos {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S) : 0 < (deriv (fwdMap W₁ a) p).re := by
  obtain ⟨u, hu⟩ := h.exists_src_alive
  exact (deriv_fwdMap_real h.cont₁ hu ha).2

/-- **The seed accesses in the opposite view**: at own time `a ≤ S`, a mark `v` of the seed interval is alive for the
opposite image chain as the access `v − p`, and at every height `t ≤ Y` the column record's own map at `v` has value
`frzImg (v − p) + p` and derivative `frzImgD (v − p)` of the opposite image chain. -/
theorem seed_access {a : ℝ} (ha : a ∈ Icc (0 : ℝ) S) {v : ℝ} (hv : v ∈ uIcc (Vlo a) (Vhi a)) :
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
            (tSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) a) (v - V₂ 0) t := by
  obtain ⟨r, hr, hclr⟩ := h.exists_seed_access_clear
  exact OwnData.seed_access_value_deriv_translated (fun t ht => (h.sOwn ht).1) ha (h.tOwn ha).1 hr
    (hclr a ha v hv)

/-- **The factor identities at one corner** `(a, t)` of the rectangle (A15's driver/tip interchange, the two-time
factor and the seed-access transport): every factor of the opposite view at its own time `t` is a factor of the
column record at own time `a`, translated by `−p` where it is a value. -/
theorem eView_factors {κ : ℝ} (rr : Fin n → ℝ) {V : Fin n → ℝ → ℝ}
    (hVI : ∀ u ∈ Icc (0 : ℝ) S, ∀ m, V m u ∈ uIcc (Vlo u) (Vhi u)) {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    (ht : t ∈ Icc (0 : ℝ) Y) :
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
    obtain ⟨_, -, hacc⟩ := h.seed_access ha (hVI a ha m)
    have hb := (hacc t ht).1
    change frzImg (Wt a) (bt a) (V m a - V₂ 0) t = (ownExt W₁ (Ws t) (as t) (frzChart V₂ t) a (V m a)).re - V₂ 0
    linarith
  have hB1 : ∀ m, e.B1 t m = d.B1 a m := fun m => by
    obtain ⟨_, -, hacc⟩ := h.seed_access ha (hVI a ha m)
    exact (hacc t ht).2.symm
  have hd21 : 0 < d.A21 a := by
    have hax := hs.mapsTo_clock ha
    have hpos := (deriv_fwdMap_real hs.contW' hv hax).2
    exact div_pos hpos hG
  exact ⟨hF0, hF1, h20, h21, hB0, hB1, hL.symm, hd21⟩

/-- **Reciprocity at one corner** `(a, t)` of the rectangle: the opposite view's raw logarithm at its driver is the
column record's raw logarithm at its driver plus the small curve's one-curve reference terms and the source factor,
which do not depend on the height `t`. -/
theorem ell_eView_eq {κ : ℝ} (hκ : κ ≠ 0) (rr : Fin n → ℝ) {V : Fin n → ℝ → ℝ}
    (hVI : ∀ u ∈ Icc (0 : ℝ) S, ∀ m, V m u ∈ uIcc (Vlo u) (Vhi u)) {a t : ℝ} (ha : a ∈ Icc (0 : ℝ) S)
    (ht : t ∈ Icc (0 : ℝ) Y) :
    (eView κ rr W₁ V₂ S Y V a).ell t (V₂ t - V₂ 0) =
      (srcRec W₁ S V₂ t κ rr p V).ell a (W₁ a) +
        ((srcRec W₁ S V₂ t κ rr p V).LT0 a + (srcRec W₁ S V₂ t κ rr p V).LS0 a (W₁ a)) +
          dualAlpha (16 / κ) * Real.log (deriv (fwdMap W₁ a) p).re := by
  obtain ⟨hF0, hF1, h20, h21, hB0, hB1, hL, hd21⟩ := h.eView_factors (κ := κ) rr hVI ha ht
  exact seed_access_log_reciprocity_translated _ _ hκ rfl rfl hF0 hF1 h20 h21 hB0 hB1 hL hd21.ne'
    (h.srcDeriv_pos ha).ne'

/-- **The row of the seeded field is the opposite view's logarithm** (Eight, vanishing fused exponent): at a positive
own time `a ≤ S` and every height `t ≤ Y`,
`d_t.normEll a − d_t.normEll 0 = e.ell t (V₂ t − p) − e.ell 0 (V₂ 0 − p)`, where `d_t` are the column records and
`e = eView … a` is the opposite view with the seed accesses as marks. -/
theorem normEll_srcRec_sub_eq_eView {κ : ℝ} (hκ : κ ≠ 0) {rr : Fin n → ℝ}
    (hE : -1 / 2 + ∑ m, -(κ / 4) * rr m = 0) {V : Fin n → ℝ → ℝ} (hVs : ∀ m, IsSeedCoordinate W₁ (V m) S)
    (hVI : ∀ u ∈ Icc (0 : ℝ) S, ∀ m, V m u ∈ uIcc (Vlo u) (Vhi u))
    (hVV : ∀ u ∈ Ioc (0 : ℝ) S, Function.Injective fun m => V m u) {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) S) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) Y) :
    (srcRec W₁ S V₂ t κ rr p V).normEll a - (srcRec W₁ S V₂ t κ rr p V).normEll 0 =
      (eView κ rr W₁ V₂ S Y V a).ell t (V₂ t - V₂ 0) - (eView κ rr W₁ V₂ S Y V a).ell 0 (V₂ 0 - V₂ 0) := by
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  have h0Y : (0 : ℝ) ∈ Icc (0 : ℝ) Y := ⟨le_rfl, h.pos₂.le⟩
  have hV0 : ∀ m, V m 0 = W₁ 0 := fun m => (hVs m).zero
  rw [normEll_srcRec_own_zero h hκ hE hV0 ht, sub_zero]
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have hex : ∃ c W', OwnData W₁ (fwdHull V₂ 0) (frzChart V₂ 0) S c W' := ⟨_, _, (h.sOwn h0Y).1⟩
    rw [normEll_srcRec_zero_height h.cont₂ h.zero₂ hex haI, sub_self]
  · have hex : ∃ c W', OwnData W₁ (fwdHull V₂ 0) (frzChart V₂ 0) S c W' := ⟨_, _, (h.sOwn h0Y).1⟩
    have r_t := h.ell_eView_eq hκ rr hVI haI ht
    have r_0 := h.ell_eView_eq hκ rr hVI haI h0Y
    have hz : (srcRec W₁ S V₂ 0 κ rr p V).ell a (W₁ a) = 0 :=
      ell_srcRec_zero_height h.cont₂ h.zero₂ hex haI _
    have hC : (srcRec W₁ S V₂ t κ rr p V).LT0 a + (srcRec W₁ S V₂ t κ rr p V).LS0 a (W₁ a) =
        (srcRec W₁ S V₂ 0 κ rr p V).LT0 a + (srcRec W₁ S V₂ 0 κ rr p V).LS0 a (W₁ a) := rfl
    rw [normEll_srcRec_eq_ell h κ rr hVs hVI hVV ⟨hpos, ht.2⟩ ha, r_t, r_0, hz, hC]
    ring

end ViewSetup

end InteractingSLE.ZhanGT4.A1EightFin
