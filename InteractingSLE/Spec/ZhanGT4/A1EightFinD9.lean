/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightFinRecip

/-!
# Zhan's A.1 (Eight): the opposite view's (D9) constants from the column records

Packet PROVE-A1-EIGHTFIN. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L330, (D9): "the
constants depend only on the enclosures and the time bound") and follow-up 4 §2.5 (L739–L788).

A22's fused martingale (`seedAccess_density_facts`) needs the (D9) constants `FrzData.D9Const` of the opposite view
`eView … a` (curve `2` grows, curve `1` frozen at own time `a`, the seed accesses as marks) **uniformly in the large
curve**. By the factor identities of `A1EightFinRecip` every factor of the opposite view at its own time `t` is a factor
of the column record `d_t` at the fixed own time `a`. The column records are controlled uniformly by A22's remote scales
and interval derivative bounds (`ColBounds`); the small curve's gaps at `a` are fixed numbers. Hence:

* `abs_sub_bounds_of_deriv`: two-sided mean-value bounds on a real interval;
* `ColBounds`, `exists_colBounds` (uniform in both curves, at every height including `0`);
* `exists_clr_eView`: the opposite driver's clearance from the frozen small hull (A6's uniform clearance);
* `gapMin`, `gapSum`, `ViewSetup.gapMin_pos`;
* **`ViewSetup.d9_eView`**: `D9Const` of the opposite view with constants built from `ColBounds`' scale, the
  clearance radius, the source derivative `Re g_a'(p)` and the small curve's gaps at `a` only.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4.A1EightFin

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1SeedField A1EightSeed

/-! ### Mean-value bounds -/

/-- **Two-sided mean-value bounds**: if `f` is differentiable on `[u, v]` with derivative in `[e^{−L}, e^L]`, then
`e^{−L} |x − y| ≤ |f x − f y| ≤ e^L |x − y|` on `[u, v]`. -/
theorem abs_sub_bounds_of_deriv {f : ℝ → ℝ} {u v L : ℝ} (hd : DifferentiableOn ℝ f (uIcc u v))
    (hder : ∀ x ∈ uIcc u v, deriv f x ∈ Icc (Real.exp (-L)) (Real.exp L)) {x y : ℝ} (hx : x ∈ uIcc u v)
    (hy : y ∈ uIcc u v) :
    Real.exp (-L) * |x - y| ≤ |f x - f y| ∧ |f x - f y| ≤ Real.exp L * |x - y| := by
  wlog hxy : y ≤ x generalizing x y
  · have := this hy hx (le_of_not_ge hxy)
    rwa [abs_sub_comm x y, abs_sub_comm (f x)]
  have hD : Convex ℝ (uIcc u v) := convex_uIcc u v
  have hc := hd.continuousOn
  have hdi : DifferentiableOn ℝ f (interior (uIcc u v)) := hd.mono interior_subset
  have h1 := hD.mul_sub_le_image_sub_of_le_deriv (C := Real.exp (-L)) hc hdi
    (fun z hz => (hder z (interior_subset hz)).1) y hy x hx hxy
  have h2 := hD.image_sub_le_mul_sub_of_deriv_le (C := Real.exp L) hc hdi
    (fun z hz => (hder z (interior_subset hz)).2) y hy x hx hxy
  have hpos : 0 ≤ f x - f y := le_trans (mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 hxy)) h1
  rw [abs_of_nonneg (sub_nonneg.2 hxy), abs_of_nonneg hpos]
  exact ⟨h1, h2⟩

/-! ### The column bounds -/

/-- **The bounds of a column record at own time `a`** used for the opposite view: the scale of the other tip's
derivative factor, of the driver and mark ratios (A22's `RemoteScale`), and the derivative of the own map on the seed
interval. -/
structure ColBounds (d : SeedData 2) (a L : ℝ) : Prop where
  A21 : InScale L (d.A21 a)
  driver : InScale L ((d.A 0 a - d.A20 a) / (d.W a - d.V₀ a))
  mark : ∀ m, InScale L ((d.A20 a - d.B0 a m) / (d.V₀ a - d.V m a))
  diff : DifferentiableOn ℝ (d.F 0 a) (uIcc (d.V 0 a) (d.V 1 a))
  derivB : ∀ x ∈ uIcc (d.V 0 a) (d.V 1 a), _root_.deriv (d.F 0 a) x ∈ Icc (Real.exp (-L)) (Real.exp L)
  F1 : ∀ x ∈ uIcc (d.V 0 a) (d.V 1 a), d.F 1 a x = _root_.deriv (d.F 0 a) x

/-- `InScale L 1` for `L ≥ 0`. -/
theorem inScale_one {L : ℝ} (hL : 0 ≤ L) : InScale L 1 := by
  refine ⟨?_, ?_⟩ <;> simp only [abs_one]
  · exact Real.exp_le_one_iff.2 (by linarith)
  · exact Real.one_le_exp hL

variable {n : ℕ}

/-- **The factors of a record at frozen height zero** (identity chart): the own map is the identity, its derivative
is one, the other tip sits at its own-chart coordinate and its normalized derivative factor is one. -/
theorem srcRec_zero_facts {W Wf : ℝ → ℝ} {T κ p : ℝ} {rr : Fin n → ℝ} {V : Fin n → ℝ → ℝ}
    (hWf : Continuous Wf) (hWf0 : Wf 0 = p) (hex : ∃ a W', OwnData W (fwdHull Wf 0) (frzChart Wf 0) T a W') {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (hG : (deriv (fwdMap W s) p).re ≠ 0) :
    (srcRec W T Wf 0 κ rr p V).F 0 s = id ∧ (∀ x, (srcRec W T Wf 0 κ rr p V).F 1 s x = 1) ∧
      (srcRec W T Wf 0 κ rr p V).A21 s = 1 ∧
      (srcRec W T Wf 0 κ rr p V).A20 s = (srcRec W T Wf 0 κ rr p V).V₀ s := by
  have hown := ownData_imgChain hex
  have hK : fwdHull Wf 0 = ∅ := QuantumZipper.RS.fwdHull_zero_eq_empty hWf
  have hφ : frzChart Wf 0 = id := frzChart_zero_eq_id Wf
  unfold srcRec
  rw [hK, hφ] at hown ⊢
  rw [hWf0]
  set J := (imgChain W ∅ id T).2
  set c := (imgChain W ∅ id T).1
  have hext : ownExt W J c id s = id := hown.ownExt_eq_of_empty hs
  have hclk : c s = s := hown.clock_eq_of_empty hs
  have himg : fwdMap J (c s) = fwdMap W s := by
    funext z
    rw [hclk]
    exact Ito.fwdMap_congr_of_eqOn fun v hv => hown.W'_eq_of_empty ⟨hv.1, hv.2.trans hs.2⟩
  have hdrv : J (c s) = W s := by rw [hclk]; exact hown.W'_eq_of_empty hs
  refine ⟨?_, fun x => ?_, ?_, ?_⟩
  · funext y
    change (deriv^[0] (ownExt W J c id s) y).re = y
    rw [hext]
    simp
  · change (deriv^[1] (ownExt W J c id s) x).re = 1
    rw [hext, Function.iterate_one, deriv_id']
    simp
  · change (deriv (fwdMap J (c s)) p).re / (deriv (fwdMap W s) p).re = 1
    rw [himg, div_self hG]
  · change (fwdMap J (c s) p).re + J (c s) = (fwdMap W s p).re + W s
    rw [himg, hdrv]

/-- **Uniform column bounds**: for a protected pair and a time bound there is one scale `L ≥ 0` such that every
column record `srcRec W₁ S V₂ t …` (seed marks `![Vlo, Vhi]`) of every rectangle (`ViewSetup`) satisfies `ColBounds`
at every height `t ≤ Y` (including `0`) and every own time `a ≤ S`. -/
theorem exists_colBounds {H₁ H₂ : Set ℂ} {δ p q dd : ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd) (Tm : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (κ : ℝ) (rr : Fin 2 → ℝ) (W₁ V₂ : ℝ → ℝ) (S Y : ℝ) (Vlo Vhi : ℝ → ℝ),
      ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi →
      ∀ t ∈ Icc (0 : ℝ) Y, ∀ a ∈ Icc (0 : ℝ) S, ColBounds (srcRec W₁ S V₂ t κ rr p ![Vlo, Vhi]) a L := by
  obtain ⟨Lrem, hLrem, hrem⟩ := exists_seed_remoteScale_right hpp.hull₁ hpp.hull₂ hpp.sep_pos hpp.sep hpp.src
    hpp.prot_pos hpp.prot_lt hpp.rad_pos hpp.prot Tm
  obtain ⟨r, L₀, hr, hL₀, hinterval⟩ := exists_seed_interval_own_bounds_right hpp.hull₁ hpp.hull₂ hpp.sep_pos
    hpp.sep hpp.rad_pos hpp.prot Tm
  obtain ⟨c₀, hc₀, hsrc⟩ := exists_original_source_gap_right hpp.hull₁ hpp.sep_pos hpp.sep hpp.src hpp.prot_pos
    hpp.prot_lt hpp.rad_pos hpp.prot Tm
  refine ⟨max Lrem L₀, le_max_of_le_left hLrem, ?_⟩
  intro κ rr W₁ V₂ S Y Vlo Vhi h t ht a ha
  have hLr : Lrem ≤ max Lrem L₀ := le_max_left _ _
  have hL0 : L₀ ≤ max Lrem L₀ := le_max_right _ _
  have hicc : Icc (Real.exp (-L₀)) (Real.exp L₀) ⊆ Icc (Real.exp (-max Lrem L₀)) (Real.exp (max Lrem L₀)) :=
    Icc_subset_Icc (Real.exp_le_exp.2 (by linarith)) (Real.exp_le_exp.2 hL0)
  have hVI : ∀ u ∈ Icc (0 : ℝ) S, ∀ m, ![Vlo, Vhi] m u ∈ uIcc (Vlo u) (Vhi u) := fun u _ m =>
    seedPair_marks Vlo Vhi u m
  rcases ht.1.eq_or_lt with h0 | hpos
  · -- height zero: the identity chart
    subst h0
    have hex : ∃ c W', OwnData W₁ (fwdHull V₂ 0) (frzChart V₂ 0) S c W' := ⟨_, _, (h.sOwn ht).1⟩
    have hG := h.srcDeriv_pos ha
    obtain ⟨hF0, hF1, h21, h20⟩ := srcRec_zero_facts (κ := κ) (rr := rr) (V := ![Vlo, Vhi]) h.cont₂ h.zero₂ hex ha
      hG.ne'
    set d := srcRec W₁ S V₂ 0 κ rr p ![Vlo, Vhi] with hd
    have hsg := fun x hx => hsrc W₁ Vlo Vhi S h.cont₁ h.zero₁ h.pos₁ h.le₁ h.K₁ h.lo h.hi a ha x hx
    have hA0 : d.A 0 a = d.W a := by
      change d.F 0 a (d.W a) = d.W a
      rw [hF0]; rfl
    have hB0 : ∀ m, d.B0 a m = d.V m a := fun m => by
      change d.F 0 a (d.V m a) = d.V m a
      rw [hF0]; rfl
    have hWV : d.W a - d.V₀ a ≠ 0 := by
      intro he
      have := hsg (W₁ a) (h.drv a ha)
      change c₀ ≤ |d.V₀ a - d.W a| at this
      rw [← neg_sub, he, neg_zero, abs_zero] at this
      linarith
    have hVV : ∀ m, d.V₀ a - d.V m a ≠ 0 := fun m he => by
      have := hsg (![Vlo, Vhi] m a) (hVI a ha m)
      change c₀ ≤ |d.V₀ a - d.V m a| at this
      rw [he, abs_zero] at this
      linarith
    have hderiv : ∀ x, deriv (d.F 0 a) x = 1 := fun x => by rw [hF0]; exact deriv_id x
    refine ⟨?_, ?_, fun m => ?_, ?_, fun x _ => ?_, fun x _ => ?_⟩
    · rw [h21]; exact inScale_one (le_max_of_le_left hLrem)
    · rw [hA0, h20, div_self hWV]; exact inScale_one (le_max_of_le_left hLrem)
    · rw [hB0, h20, div_self (hVV m)]; exact inScale_one (le_max_of_le_left hLrem)
    · rw [hF0]; exact differentiableOn_id
    · rw [hderiv]
      have hLp : 0 ≤ max Lrem L₀ := le_max_of_le_left hLrem
      exact ⟨Real.exp_le_one_iff.2 (by linarith), Real.one_le_exp hLp⟩
    · rw [hF1, hderiv]
  · -- positive heights: A22's remote scales and interval bounds
    have hown := (h.sOwn ht).1
    have hW0H : ((W₁ 0 : ℝ) : ℂ) ∈ closure H₁ := closure_mono h.K₁ (start_mem_closure_fwdHull h.cont₁ h.pos₁)
    have hV₂H : ((V₂ 0 : ℝ) : ℂ) ∈ closure H₂ := by rw [h.zero₂]; exact h.pp.src
    have hK₂t : fwdHull V₂ t ⊆ H₂ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans h.K₂
    have hint := hinterval W₁ V₂ Vlo Vhi S t _ _ hown h.cont₂ hpos hW0H hV₂H
      (by rw [h.zero₁]; exact h.pp.prot_pos) (by rw [h.zero₂]; exact h.pp.prot_lt) (ht.2.trans h.le₂) h.K₁ hK₂t
      h.lo h.hi a ha
    have hremote := hrem κ rr W₁ V₂ _ _ Vlo Vhi ![Vlo, Vhi] S t hown h.cont₂ h.zero₂ hpos (ht.2.trans h.le₂) h.le₁
      h.K₁ hK₂t h.lo h.hi h.drv hVI a ha
    rw [srcRec_eq_sSel W₁ V₂ h.pos₁.le ht.2]
    set d := SeedData.fromSource W₁ (sSelW W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t)
      (sSelA W₁ V₂ (fun _ : Unit => S) (fun _ : Unit => Y) t) (frzChart V₂ t) κ rr (V₂ t) p ![Vlo, Vhi] with hd
    have hdiff : ∀ x ∈ uIcc (Vlo a) (Vhi a), DifferentiableAt ℂ (ownExt d.W d.W' d.a d.φ a) x := by
      intro x hx
      have hdo := (hown.ownExt_props ha (hint x hx).1).1
      exact hdo.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    refine ⟨FrzData.inScale_mono hremote.A21 hLr, FrzData.inScale_mono hremote.driver hLr,
      fun m => FrzData.inScale_mono (hremote.mark m) hLr, fun x hx => ?_, fun x hx => hicc (hint x hx).2,
      fun x hx => (d.deriv_F_zero (hdiff x hx)).symm⟩
    exact (hdiff x hx).hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt

/-! ### The clearance of the opposite driver and the small curve's gaps -/

/-- **The opposite driver's clearance** (A6's uniform clearance for the large curve, translated by `−p`): one radius
`r > 0` clears the driver of the opposite view from its image of the frozen small hull, for every rectangle with the
given protected pair, every frozen own time `a ≤ S` and every time `t ≤ Y`. -/
theorem exists_clr_eView {H₁ H₂ : Set ℂ} {δ p q dd : ℝ} (hpp : IsProtectedPair H₁ H₂ δ p q dd) (Tm : ℝ) :
    ∃ r > (0 : ℝ), ∀ (W₁ V₂ : ℝ → ℝ) (S Y : ℝ) (Vlo Vhi : ℝ → ℝ), ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi →
      ∀ a ∈ Icc (0 : ℝ) S, ∀ t ∈ Icc (0 : ℝ) Y,
        Disjoint (ball ((V₂ t - V₂ 0 : ℝ) : ℂ) r)
          ((fun z => fwdMap (fun u => V₂ u - V₂ 0) t z + ((V₂ t - V₂ 0 : ℝ) : ℂ)) ''
            fwdHull (fun u => W₁ u - V₂ 0) a) := by
  have hsep' : ∀ a ∈ H₁, ∀ z ∈ H₂, 2 * δ ≤ ‖a - z‖ := fun a ha z hz => by
    rw [norm_sub_rev]; exact hpp.sep z hz a ha
  have hF := isHPHull_transl hpp.hull₁ (-p)
  obtain ⟨r, hr, hcl⟩ := exists_le_norm_fwdMap_uniform (isHPHull_transl hpp.hull₂ (-p)) hF.2.1 hF.1 hpp.sep_pos
    (sep_transl hsep' (-p))
  refine ⟨r, hr, fun W₁ V₂ S Y Vlo Vhi h a ha t ht => ?_⟩
  have hc : Continuous fun u => V₂ u - V₂ 0 := h.cont₂.sub continuous_const
  have h0 : (((fun u => V₂ u - V₂ 0) 0 : ℝ) : ℂ) ∈ closure (transl (-p) H₂) := by
    have := mem_closure_transl h.pp.src (-p)
    simpa only [sub_self, ofReal_zero, ofReal_neg, add_neg_cancel] using this
  have hK : fwdHull (fun u => V₂ u - V₂ 0) Y ⊆ transl (-p) H₂ := by
    have := fwdHull_sub_const_subset (c := V₂ 0) h.K₂
    rw [h.zero₂] at this ⊢
    exact this
  refine Set.disjoint_left.2 fun w hw hwK => ?_
  obtain ⟨z, hz, rfl⟩ := hwK
  have hzF : z ∈ transl (-p) H₁ := by
    have := fwdHull_sub_const_subset (c := V₂ 0) (((QuantumZipper.fwdHull_mono).1 ha.2).trans h.K₁)
    rw [h.zero₂] at this hz
    exact this hz
  have hle := hcl _ hc h0 Y hK t ht z hzF
  rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at hw
  linarith

/-- The smallest of the small curve's six gaps at a frozen own time (driver `w`, other source `v₀`, seeds `lo`,
`hi`). -/
def gapMin (w v₀ lo hi : ℝ) : ℝ :=
  min (min |w - v₀| (min |v₀ - lo| |v₀ - hi|)) (min (min |w - lo| |w - hi|) |lo - hi|)

/-- The sum of the small curve's six gaps at a frozen own time. -/
def gapSum (w v₀ lo hi : ℝ) : ℝ := |w - v₀| + |v₀ - lo| + |v₀ - hi| + |w - lo| + |w - hi| + |lo - hi|

theorem gapMin_le (w v₀ lo hi : ℝ) :
    gapMin w v₀ lo hi ≤ |w - v₀| ∧ gapMin w v₀ lo hi ≤ |v₀ - lo| ∧ gapMin w v₀ lo hi ≤ |v₀ - hi| ∧
      gapMin w v₀ lo hi ≤ |w - lo| ∧ gapMin w v₀ lo hi ≤ |w - hi| ∧ gapMin w v₀ lo hi ≤ |lo - hi| := by
  unfold gapMin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [min_le_iff, le_refl, true_or, or_true]

theorem le_gapSum (w v₀ lo hi : ℝ) :
    |w - v₀| ≤ gapSum w v₀ lo hi ∧ |v₀ - lo| ≤ gapSum w v₀ lo hi ∧ |v₀ - hi| ≤ gapSum w v₀ lo hi ∧
      |w - lo| ≤ gapSum w v₀ lo hi ∧ |w - hi| ≤ gapSum w v₀ lo hi ∧ |lo - hi| ≤ gapSum w v₀ lo hi := by
  unfold gapSum
  have := abs_nonneg (w - v₀); have := abs_nonneg (v₀ - lo); have := abs_nonneg (v₀ - hi)
  have := abs_nonneg (w - lo); have := abs_nonneg (w - hi); have := abs_nonneg (lo - hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The small curve's gaps at a positive own time are positive**: the other source's coordinate stays off the seed
interval (A22's `exists_original_source_gap_right`), the seeds stay off the driver and are distinct. -/
theorem ViewSetup.gapMin_pos {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}
    (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi) {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) S) :
    0 < gapMin (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a) := by
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  obtain ⟨c₀, hc₀, hsrc⟩ := exists_original_source_gap_right h.pp.hull₁ h.pp.sep_pos h.pp.sep h.pp.src
    h.pp.prot_pos h.pp.prot_lt h.pp.rad_pos h.pp.prot Tm
  have hsg := fun x hx => hsrc W₁ Vlo Vhi S h.cont₁ h.zero₁ h.pos₁ h.le₁ h.K₁ h.lo h.hi a haI x hx
  have h1 : 0 < |W₁ a - ((fwdMap W₁ a p).re + W₁ a)| := by
    have := hsg (W₁ a) (h.drv a haI)
    rw [abs_sub_comm]; linarith
  have h2 : 0 < |(fwdMap W₁ a p).re + W₁ a - Vlo a| := lt_of_lt_of_le hc₀ (hsg _ left_mem_uIcc)
  have h3 : 0 < |(fwdMap W₁ a p).re + W₁ a - Vhi a| := lt_of_lt_of_le hc₀ (hsg _ right_mem_uIcc)
  have h4 : 0 < |W₁ a - Vlo a| := abs_pos.2 (sub_ne_zero.2 (h.lo.ne a ha).symm)
  have h5 : 0 < |W₁ a - Vhi a| := abs_pos.2 (sub_ne_zero.2 (h.hi.ne a ha).symm)
  have h6 : 0 < |Vlo a - Vhi a| := abs_pos.2 (sub_ne_zero.2 (h.inj a ha))
  unfold gapMin
  exact lt_min (lt_min h1 (lt_min h2 h3)) (lt_min (lt_min h4 h5) h6)

/-! ### The opposite view's (D9) constants -/

theorem abs_bounds_of_inScale_div {x y L : ℝ} (h : InScale L (x / y)) :
    Real.exp (-L) * |y| ≤ |x| ∧ |x| ≤ Real.exp L * |y| := by
  have hy : y ≠ 0 := by
    rintro rfl
    have := h.1
    rw [div_zero, abs_zero] at this
    linarith [Real.exp_pos (-L)]
  have hx : |x| = |x / y| * |y| := by rw [abs_div, div_mul_cancel₀ _ (abs_pos.2 hy).ne']
  rw [hx]
  exact ⟨mul_le_mul_of_nonneg_right h.1 (abs_nonneg _), mul_le_mul_of_nonneg_right h.2 (abs_nonneg _)⟩

theorem d9_pair {x y L g G : ℝ} (hb : Real.exp (-L) * |y| ≤ |x| ∧ |x| ≤ Real.exp L * |y|) (hg : g ≤ |y|)
    (hG : |y| ≤ G) : Real.exp (-L) * g ≤ |x| ∧ |x| ≤ Real.exp L * G :=
  ⟨(mul_le_mul_of_nonneg_left hg (Real.exp_pos _).le).trans hb.1,
    hb.2.trans (mul_le_mul_of_nonneg_left hG (Real.exp_pos _).le)⟩

theorem inScale_of_mem_Icc {L u : ℝ} (h : u ∈ Icc (Real.exp (-L)) (Real.exp L)) : InScale L u := by
  have hu : 0 ≤ u := (Real.exp_pos _).le.trans h.1
  exact ⟨by rw [abs_of_nonneg hu]; exact h.1, by rw [abs_of_nonneg hu]; exact h.2⟩

namespace ViewSetup

variable {H₁ H₂ : Set ℂ} {δ p q dd Tm : ℝ} {W₁ V₂ : ℝ → ℝ} {S Y : ℝ} {Vlo Vhi : ℝ → ℝ}
  (h : ViewSetup H₁ H₂ δ p q dd Tm W₁ V₂ S Y Vlo Vhi)
include h

/-- **The opposite view's (D9) bounds at one of its own times `t ≤ Y`**, from the column record's bounds at the
fixed own time `a` (`ColBounds`) and the small curve's gaps at `a`. -/
theorem d9_eView_at {κ : ℝ} (rr : Fin 2 → ℝ) {L a t : ℝ} (ha : a ∈ Ioc (0 : ℝ) S) (ht : t ∈ Icc (0 : ℝ) Y)
    (cb : ColBounds (srcRec W₁ S V₂ t κ rr p ![Vlo, Vhi]) a L) :
    let e := eView κ rr W₁ V₂ S Y ![Vlo, Vhi] a
    let g := gapMin (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a)
    let G := gapSum (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a)
    Real.exp (-L) * (deriv (fwdMap W₁ a) p).re ≤ e.A 1 t ∧
      (Real.exp (-L) * g ≤ |e.A20 t - e.A 0 t| ∧ |e.A20 t - e.A 0 t| ≤ Real.exp L * G) ∧
      (∀ m, Real.exp (-L) * g ≤ |e.B0 t m - e.A 0 t| ∧ |e.B0 t m - e.A 0 t| ≤ Real.exp L * G) ∧
      (∀ m, Real.exp (-L) * g ≤ |e.A20 t - e.B0 t m| ∧ |e.A20 t - e.B0 t m| ≤ Real.exp L * G) ∧
      (∀ m k, m ≠ k → Real.exp (-L) * g ≤ |e.B0 t m - e.B0 t k| ∧ |e.B0 t m - e.B0 t k| ≤ Real.exp L * G) ∧
      InScale L (e.A21 t) ∧ ∀ m, InScale L (e.B1 t m) := by
  intro e g G
  have haI : a ∈ Icc (0 : ℝ) S := Ioc_subset_Icc_self ha
  obtain ⟨hF0, hF1, h20, h21, hB0, hB1, -, hA21⟩ :=
    h.eView_factors (κ := κ) rr (fun u _ m => seedPair_marks Vlo Vhi u m) haI ht
  set d := srcRec W₁ S V₂ t κ rr p ![Vlo, Vhi] with hd
  have hA0 : e.A 0 t = d.A20 a - V₂ 0 := hF0
  have hA1 : e.A 1 t = d.A21 a * (deriv (fwdMap W₁ a) p).re := hF1
  have hWI : d.W a ∈ uIcc (d.V 0 a) (d.V 1 a) := h.drv a haI
  have hVI : ∀ m, d.V m a ∈ uIcc (d.V 0 a) (d.V 1 a) := fun m => seedPair_marks Vlo Vhi a m
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := gapMin_le (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a)
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := le_gapSum (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a)
  have hsh : ∀ u v c : ℝ, (u - c) - (v - c) = u - v := fun u v c => by ring
  have hFV : ∀ m, d.B0 a m = d.F 0 a (d.V m a) := fun m => rfl
  have hFW : d.A 0 a = d.F 0 a (d.W a) := rfl
  refine ⟨?_, ?_, fun m => ?_, fun m => ?_, fun m k hmk => ?_, ?_, fun m => ?_⟩
  · rw [hA1]
    have hlow : Real.exp (-L) ≤ d.A21 a := by
      have := cb.A21.1
      rwa [abs_of_pos hA21] at this
    exact mul_le_mul_of_nonneg_right hlow (h.srcDeriv_pos haI).le
  · rw [h20, hA0, hsh]
    exact d9_pair (abs_bounds_of_inScale_div cb.driver) g1 s1
  · rw [hB0, hA0, hsh, abs_sub_comm]
    have hb := abs_bounds_of_inScale_div (cb.mark m)
    fin_cases m
    · exact d9_pair hb g2 s2
    · exact d9_pair hb g3 s3
  · rw [h20, hB0, hsh, hFW, hFV]
    have hb := abs_sub_bounds_of_deriv cb.diff cb.derivB hWI (hVI m)
    fin_cases m
    · exact d9_pair hb g4 s4
    · exact d9_pair hb g5 s5
  · rw [hB0, hB0, hsh, hFV, hFV]
    have hb := abs_sub_bounds_of_deriv cb.diff cb.derivB (hVI m) (hVI k)
    fin_cases m <;> fin_cases k
    · exact absurd rfl hmk
    · exact d9_pair hb g6 s6
    · exact d9_pair hb (g6.trans_eq (abs_sub_comm _ _)) ((abs_sub_comm _ _).trans_le s6)
    · exact absurd rfl hmk
  · rw [h21]
    apply inScale_of_mem_Icc
    change d.F 1 a (d.W a) ∈ _
    rw [cb.F1 _ hWI]
    exact cb.derivB _ hWI
  · rw [hB1]
    apply inScale_of_mem_Icc
    change d.F 1 a (d.V m a) ∈ _
    rw [cb.F1 _ (hVI m)]
    exact cb.derivB _ (hVI m)

/-- **The opposite view's (D9) constants** (`FrzData.D9Const`): the clearance radius `r`, the derivative scale
`e^{−L} Re g_a'(p)`, the gap bounds `e^{−L} gapMin`, `e^L gapSum` and the scale `L`. All of them depend only on the
column bounds' scale, the clearance radius and the small curve at the frozen own time `a`, not on the large curve. -/
theorem d9_eView {κ : ℝ} (rr : Fin 2 → ℝ) {L r a : ℝ} (hr : 0 < r) (ha : a ∈ Ioc (0 : ℝ) S)
    (hcb : ∀ t ∈ Icc (0 : ℝ) Y, ColBounds (srcRec W₁ S V₂ t κ rr p ![Vlo, Vhi]) a L)
    (hclr : ∀ t ∈ Icc (0 : ℝ) Y, Disjoint (ball ((V₂ t - V₂ 0 : ℝ) : ℂ) r)
      ((fun z => fwdMap (fun u => V₂ u - V₂ 0) t z + ((V₂ t - V₂ 0 : ℝ) : ℂ)) ''
        fwdHull (fun u => W₁ u - V₂ 0) a)) :
    (eView κ rr W₁ V₂ S Y ![Vlo, Vhi] a).D9Const (fwdHull (fun u => W₁ u - V₂ 0) a) Y r
      (Real.exp (-L) * (deriv (fwdMap W₁ a) p).re)
      (Real.exp (-L) * gapMin (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a))
      (Real.exp L * gapSum (W₁ a) ((fwdMap W₁ a p).re + W₁ a) (Vlo a) (Vhi a)) L where
  r0 := hr
  a0 := mul_pos (Real.exp_pos _) (h.srcDeriv_pos (Ioc_subset_Icc_self ha))
  g0 := mul_pos (Real.exp_pos _) (h.gapMin_pos ha)
  clr := hclr
  A1 := fun t ht => (h.d9_eView_at rr ha ht (hcb t ht)).1
  E0 := fun t ht => (h.d9_eView_at rr ha ht (hcb t ht)).2.1
  Em := fun t ht => (h.d9_eView_at rr ha ht (hcb t ht)).2.2.1
  E2m := fun t ht => (h.d9_eView_at rr ha ht (hcb t ht)).2.2.2.1
  Cmk := fun t ht => (h.d9_eView_at rr ha ht (hcb t ht)).2.2.2.2.1
  A21 := fun t ht => (h.d9_eView_at rr ha ht (hcb t ht)).2.2.2.2.2.1
  B1 := fun t ht => (h.d9_eView_at rr ha ht (hcb t ht)).2.2.2.2.2.2

end ViewSetup

end InteractingSLE.ZhanGT4.A1EightFin
