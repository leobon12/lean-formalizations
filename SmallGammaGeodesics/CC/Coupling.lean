import SmallGammaGeodesics.CC.PullbackConv
import SmallGammaGeodesics.CC.PullbackMobius
import LQGMetric.Field.GFFInvariance
import LQGMetric.Field.Measurable

/-!
# Coupling algebra (track CC, packet CC1; [3] (1.10), (1.12))

Source: Gwynne–Miller arXiv:1905.00384 ([3]), (1.10), (1.12) and the last paragraph of the proof of
Thm 1.3, as corrected and planned in `planning/audits/CC0-conformal-covariance-plan.md`, Details (a)
**D1** items 4–6. `IsConfCoupling γ ϕ W V h h̄ f` (`Core/Interfaces.lean`) says
`(h ∘ ϕ⁻¹ + Q log|(ϕ⁻¹)'|)|_{ϕ(V)} = (h̄ + f)|_{ϕ(V)}` in the weak (tested) sense.

* **T5** (D1.5) `IsConfCoupling.addConst`: `(h + c, h̄ + c, f)` is again a coupling.
* **T4** (D1.4) the reversal: `IsConfNbhd.inv` (in `CC/Pullback.lean`) and
  `IsConfCoupling.reverse`: for any `f'` with `f' = -f ∘ ϕ` on `V`, `(h̄, h, f')` is a coupling for
  the inverse `ψ` on `(ϕ '' W, ϕ '' V)`; `exists_reverse_coupling` is the packet's form. The
  explicit choice `revCont` (`f' = -β · (f ∘ ϕ)` with a cutoff `β`) is continuous in `f`
  (`continuous_revCont`), so it is measurable for random `f`.
* **T6** (D1.6) `IsConfCoupling.zoom`: the zoom `(ϕ̃, W̃, Ṽ, h(z + r·) + c, h̄(ϕ(z) + r·),
  f(ϕ(z) + r·) + c)` is again a coupling; `measurable_zoomCont` for random `f` and `c`.
* (D17) `IsConfCoupling.confPair0_eq`: in `σ₀` coordinates the coupling reads
  `confPair0 γ ϕ W V h = pair0On (ϕ '' V) (addFun h̄ f)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Function

namespace SmallGammaGeodesics.CC

open LQGMetric

variable {γ : ℝ} {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {h hbar : DistC} {f : C(ℂ, ℝ)}

/-! ## T5: constants (D1.5) -/

/-- **T5** (D1.5): adding the same constant to both fields keeps a coupling, since `∫ τg = ∫ g`. -/
theorem IsConfCoupling.addConst (hϕ : IsConfNbhd ϕ W V) (hc : IsConfCoupling γ ϕ W V h hbar f)
    (c : ℝ) : IsConfCoupling γ ϕ W V (LQGMetric.addConst h c) (LQGMetric.addConst hbar c) f := by
  intro g τg hg hτ
  rw [GFFInv.addConst_apply, GFFInv.addConst_apply, hτ.integral_eq hϕ hg]
  have := hc g τg hg hτ
  linarith

/-! ## T4: reversal (D1.4) -/

/-- **T4** (D1.4): **reversal of a coupling**. If `(h, h̄, f)` is a coupling for `(ϕ, W, V)` and
`f' = -f ∘ ϕ` on `V`, then `(h̄, h, f')` is a coupling for the inverse `ψ` on `(ϕ '' W, ϕ '' V)`. -/
theorem IsConfCoupling.reverse (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    (hc : IsConfCoupling γ ϕ W V h hbar f) {f' : C(ℂ, ℝ)} (hf' : ∀ z ∈ V, f' z = -f (ϕ z)) :
    IsConfCoupling γ ψ (ϕ '' W) (ϕ '' V) hbar h f' := by
  intro g τg hg hτ
  have hinv := hϕ.inv hψ
  have hφψ : ∀ y ∈ ϕ '' W, ϕ (ψ y) = y := leftInv_leftInv hψ
  have hgV : tsupport (g : ℂ → ℝ) ⊆ V := by rwa [hϕ.image_inv_image hψ] at hg
  -- the `ψ`-pullback `τg` is supported in `ϕ '' V`, and its `ϕ`-pullback is `g`
  have hτsupp : tsupport (τg : ℂ → ℝ) ⊆ ϕ '' V :=
    (hτ.tsupport_subset hinv hφψ hg).trans (image_mono hgV)
  have hpull : IsConfPull ϕ W τg g := hτ.of_inv hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ
    fun x hx => image_eq_zero_of_notMem_tsupport fun hx' => hx (hϕ.subset (hgV hx'))
  have key := hc τg g hτsupp hpull
  -- the change of variables for `ψ`
  have h2 := hτ.integral_log_mul hinv hφψ hg
  have h3 := hτ.integral_mul hinv hφψ hg f
  have h4 : ∫ y, f y * τg y = ∫ y, τg y * f y := by
    congr 1
    funext y
    ring
  have h5 : ∫ y, f' y * g y = -∫ y, g y * f (ϕ y) := by
    rw [← integral_neg]
    congr 1
    funext y
    by_cases hy : y ∈ V
    · rw [hf' y hy]
      ring
    · rw [image_eq_zero_of_notMem_tsupport fun h => hy (hgV h)]
      ring
  rw [h2, h5]
  rw [h4, h3] at key
  linarith

/-- a continuous cutoff with compact support in `W`, equal to `1` on `closure V` -/
theorem IsConfNbhd.exists_cutoff (hϕ : IsConfNbhd ϕ W V) :
    ∃ β : C(ℂ, ℝ), HasCompactSupport β ∧ tsupport β ⊆ W ∧ ∀ z ∈ closure V, β z = 1 := by
  obtain ⟨L, hL, hVL, hLW⟩ :=
    exists_compact_between hϕ.isCompact_closure hϕ.isOpen_W hϕ.closure_subset
  obtain ⟨β, hβ1, hβ0, hβc, -⟩ := exists_continuous_one_zero_of_isCompact hϕ.isCompact_closure
    isOpen_interior.isClosed_compl (disjoint_compl_right_iff_subset.mpr hVL)
  refine ⟨β, hβc, ?_, fun z hz => hβ1 hz⟩
  have hsupp : support β ⊆ L := fun x hx => by
    by_contra hxL
    exact hx (hβ0 fun hxi => hxL (interior_subset hxi))
  exact (closure_minimal hsupp hL.isClosed).trans hLW

/-- `(f, x) ↦ -β x · f (ϕ x)` is jointly continuous when `tsupport β ⊆ W`, `W` is open and `ϕ` is
continuous on `W`: near a point of `W` it is a composition of continuous maps, and near a point
off `W` (hence off `tsupport β`) it vanishes. -/
theorem continuous_revFun_uncurry (hW : IsOpen W) (hϕc : ContinuousOn ϕ W) {β : C(ℂ, ℝ)}
    (hβ : tsupport β ⊆ W) :
    Continuous fun p : C(ℂ, ℝ) × ℂ => -(β p.2 * p.1 (ϕ p.2)) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  by_cases hp : p.2 ∈ W
  · have hϕa : ContinuousAt (fun q : C(ℂ, ℝ) × ℂ => ϕ q.2) p :=
      (hϕc.continuousAt (hW.mem_nhds hp)).comp continuous_snd.continuousAt
    have hev : ContinuousAt (fun q : C(ℂ, ℝ) × ℂ => q.1 (ϕ q.2)) p :=
      continuous_eval.continuousAt.comp (continuous_fst.continuousAt.prodMk hϕa)
    exact ((β.continuous.comp continuous_snd).continuousAt.mul hev).neg
  · have hp' : p.2 ∉ tsupport β := fun h => hp (hβ h)
    have hzero : ∀ᶠ q in 𝓝 p, -(β q.2 * q.1 (ϕ q.2)) = 0 := by
      have : ∀ᶠ q in 𝓝 p, q.2 ∉ tsupport β :=
        continuous_snd.continuousAt ((isClosed_tsupport β).isOpen_compl.mem_nhds hp')
      filter_upwards [this] with q hq
      rw [image_eq_zero_of_notMem_tsupport hq, zero_mul, neg_zero]
    have hp0 : -(β p.2 * p.1 (ϕ p.2)) = 0 := by
      rw [image_eq_zero_of_notMem_tsupport hp', zero_mul, neg_zero]
    rw [ContinuousAt, hp0]
    exact tendsto_const_nhds.congr' (hzero.mono fun q hq => hq.symm)

/-- **The reversed continuous function** `f' = -β · (f ∘ ϕ)` (D1.4), for a cutoff `β` with
`tsupport β ⊆ W`. -/
def revCont (hW : IsOpen W) (hϕc : ContinuousOn ϕ W) (β : C(ℂ, ℝ)) (hβ : tsupport β ⊆ W)
    (f : C(ℂ, ℝ)) : C(ℂ, ℝ) :=
  ⟨fun x => -(β x * f (ϕ x)),
    (continuous_revFun_uncurry hW hϕc hβ).comp (continuous_const.prodMk continuous_id)⟩

theorem revCont_apply (hW : IsOpen W) (hϕc : ContinuousOn ϕ W) (β : C(ℂ, ℝ))
    (hβ : tsupport β ⊆ W) (f : C(ℂ, ℝ)) (x : ℂ) :
    revCont hW hϕc β hβ f x = -(β x * f (ϕ x)) :=
  rfl

/-- `f ↦ revCont … f` is continuous `C(ℂ, ℝ) → C(ℂ, ℝ)` (compact-open topology), hence
measurable: a measurable random `f` gives a measurable reversed `f'`. -/
theorem continuous_revCont (hW : IsOpen W) (hϕc : ContinuousOn ϕ W) (β : C(ℂ, ℝ))
    (hβ : tsupport β ⊆ W) : Continuous (revCont hW hϕc β hβ) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_revFun_uncurry hW hϕc hβ)

theorem measurable_revCont (hW : IsOpen W) (hϕc : ContinuousOn ϕ W) (β : C(ℂ, ℝ))
    (hβ : tsupport β ⊆ W) : Measurable (revCont hW hϕc β hβ) :=
  (continuous_revCont hW hϕc β hβ).measurable

theorem revCont_eq_on (hW : IsOpen W) (hϕc : ContinuousOn ϕ W) {β : C(ℂ, ℝ)}
    (hβ : tsupport β ⊆ W) {S : Set ℂ} (hβ1 : ∀ z ∈ S, β z = 1) (f : C(ℂ, ℝ)) :
    ∀ z ∈ S, revCont hW hϕc β hβ f z = -f (ϕ z) := fun z hz => by
  rw [revCont_apply, hβ1 z hz, one_mul]

/-- **T4** (D1.4), the packet's form: a reversed coupling exists, with `W' = ϕ '' W` and
`f' = -β · (f ∘ ϕ)`. -/
theorem exists_reverse_coupling (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ z ∈ W, ψ (ϕ z) = z)
    (hc : IsConfCoupling γ ϕ W V h hbar f) :
    ∃ (W' : Set ℂ) (f' : C(ℂ, ℝ)), IsConfNbhd ψ W' (ϕ '' V) ∧ (∀ z ∈ V, f' z = -f (ϕ z)) ∧
      IsConfCoupling γ ψ W' (ϕ '' V) hbar h f' := by
  obtain ⟨β, -, hβW, hβ1⟩ := hϕ.exists_cutoff
  have hf' := revCont_eq_on hϕ.isOpen_W hϕ.differentiableOn.continuousOn hβW
    (fun z hz => hβ1 z (subset_closure hz)) f
  exact ⟨ϕ '' W, _, hϕ.inv hψ, hf', hc.reverse hϕ hψ hf'⟩

/-- **T4, random form**: one cutoff `β` (depending only on `(ϕ, W, V)`) gives, for every coupling,
the reversed coupling with `f' = revCont … f`; the map `f ↦ f'` is measurable. -/
theorem exists_reverse_coupling_measurable (hϕ : IsConfNbhd ϕ W V) :
    ∃ F : C(ℂ, ℝ) → C(ℂ, ℝ), Measurable F ∧ (∀ f : C(ℂ, ℝ), ∀ z ∈ V, F f z = -f (ϕ z)) ∧
      ∀ (ψ : ℂ → ℂ), (∀ z ∈ W, ψ (ϕ z) = z) → ∀ (h hbar : DistC) (f : C(ℂ, ℝ)),
        IsConfCoupling γ ϕ W V h hbar f → IsConfCoupling γ ψ (ϕ '' W) (ϕ '' V) hbar h (F f) := by
  obtain ⟨β, -, hβW, hβ1⟩ := hϕ.exists_cutoff
  have hF := revCont_eq_on hϕ.isOpen_W hϕ.differentiableOn.continuousOn hβW
    (fun z hz => hβ1 z (subset_closure hz))
  exact ⟨_, measurable_revCont _ _ β hβW, hF, fun ψ hψ h hbar f hc => hc.reverse hϕ hψ (hF f)⟩

/-! ## The coupling in `σ₀` coordinates (D17) -/

/-- **The coupling in `σ₀` coordinates** (D17): on mean-zero test functions supported in `ϕ(V)`,
the pairing vector `confPair0` of `h ∘ ϕ⁻¹ + Q log|(ϕ⁻¹)'|` (built with the chosen pullback
`confPull`) is the pairing vector of `h̄ + f`. -/
theorem IsConfCoupling.confPair0_eq (hϕ : IsConfNbhd ϕ W V)
    (hc : IsConfCoupling γ ϕ W V h hbar f) :
    confPair0 γ ϕ W V h = pair0On (ϕ '' V) (addFun hbar f) := by
  funext g
  rw [confPair0, hc _ _ g.2 (isConfPull_confPull hϕ g.2), pair0On]
  show _ = hbar g.1.1 + ofCont f g.1.1
  rw [ofCont_apply]
  congr 2
  funext y
  ring

/-! ## T6: zoom (D1.6) -/

/-- the zoomed continuous function `y ↦ f (a + r y) + c` -/
def zoomCont (f : C(ℂ, ℝ)) (a : ℂ) (r c : ℝ) : C(ℂ, ℝ) :=
  ⟨fun y => f (a + (r : ℂ) * y) + c, by fun_prop⟩

theorem zoomCont_apply (f : C(ℂ, ℝ)) (a : ℂ) (r c : ℝ) (y : ℂ) :
    zoomCont f a r c y = f (a + (r : ℂ) * y) + c :=
  rfl

private theorem real_smul_add_eq (r : ℝ) (a w : ℂ) : r • w + a = a + (r : ℂ) * w := by
  rw [Complex.real_smul, add_comm]

/-- `(f, c) ↦ f(a + r·) + c` is continuous `C(ℂ, ℝ) × ℝ → C(ℂ, ℝ)`. -/
theorem continuous_zoomCont (a : ℂ) (r : ℝ) :
    Continuous fun p : C(ℂ, ℝ) × ℝ => zoomCont p.1 a r p.2 := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  show Continuous fun q : (C(ℂ, ℝ) × ℝ) × ℂ => q.1.1 (a + (r : ℂ) * q.2) + q.1.2
  exact (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    (by fun_prop))).add (continuous_snd.comp continuous_fst)

/-- For a measurable random `f` and a measurable random constant `c` (e.g. `c = -h_r(z)`, D8), the
zoomed `f̃ = f(a + r·) + c` is measurable. -/
theorem measurable_zoomCont {Ω : Type*} [MeasurableSpace Ω] {f : Ω → C(ℂ, ℝ)} {c : Ω → ℝ}
    (hf : Measurable f) (hc : Measurable c) (a : ℂ) (r : ℝ) :
    Measurable fun ω => zoomCont (f ω) a r (c ω) :=
  (continuous_zoomCont a r).measurable.comp (hf.prodMk hc)

/-- **T6** (D1.6): **zoom of a coupling**. For `z ∈ ℂ`, `r > 0` and `c ∈ ℝ`, put
`ϕ̃(w) = r⁻¹(ϕ(z + r w) − ϕ(z))`, `W̃ = r⁻¹(W − z)`, `Ṽ = r⁻¹(V − z)`, `h̃ = h(z + r·) + c`,
`h̄̃ = h̄(ϕ(z) + r·)` and `f̃ = f(ϕ(z) + r·) + c`. Then `(h̃, h̄̃, f̃)` is a coupling for
`(ϕ̃, W̃, Ṽ)`. The fields `h(z + r·)` and `h̄(ϕ(z) + r·)` are LQGMetric's `affineComp`. -/
theorem IsConfCoupling.zoom (hϕ : IsConfNbhd ϕ W V) (hc : IsConfCoupling γ ϕ W V h hbar f)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (c : ℝ) :
    IsConfCoupling γ (zoomMap ϕ z r) (zoomSet z r W) (zoomSet z r V)
      (LQGMetric.addConst (affineComp r z h) c) (affineComp r (ϕ z) hbar)
      (zoomCont f (ϕ z) r c) := by
  intro g τg hg hτ
  have hr0 : r ≠ 0 := hr.ne'
  have hZ := hϕ.zoom z hr0
  set G : TestC := testAffinePull r (ϕ z) g with hG
  set T : TestC := testAffinePull r z τg with hT
  have hGs : tsupport (G : ℂ → ℝ) ⊆ ϕ '' V := tsupport_testAffinePull_subset_zoom hr0 hg
  have hTG : IsConfPull ϕ W G T := hτ.zoom hr0 hϕ.isOpen_W hϕ.differentiableOn
  have key := hc G T hGs hTG
  -- (i) the Liouville term, after `x = z + r w`
  have hA : ∫ x, Real.log ‖deriv ϕ x‖ * T x =
      r ^ 2 * ∫ w, Real.log ‖deriv (zoomMap ϕ z r) w‖ * τg w := by
    rw [GFFInv.integral_eq_smul_add _ hr z]
    congr 2
    funext w
    rw [hT, testAffinePull_apply r z hr0, real_smul_add_eq, div_zoomAff hr0]
    by_cases hw : w ∈ zoomSet z r W
    · rw [deriv_zoomMap hr0 (hϕ.differentiableOn.differentiableAt (hϕ.isOpen_W.mem_nhds hw))]
    · rw [hτ w, indicator_of_notMem hw, mul_zero, mul_zero]
  -- (ii) the continuous-function term, after `y = ϕ(z) + r v`
  have hB : ∫ y, f y * G y = r ^ 2 * ∫ v, f (ϕ z + (r : ℂ) * v) * g v := by
    rw [GFFInv.integral_eq_smul_add _ hr (ϕ z)]
    congr 2
    funext v
    rw [hG, testAffinePull_apply r (ϕ z) hr0, real_smul_add_eq, div_zoomAff hr0]
  -- (iii) `∫ τ̃ = ∫ g̃`
  have hI := hτ.integral_eq hZ hg
  -- (iv) split the right-hand side
  have hgi : Integrable (fun y => g y) := GFFInv.integrable_test g
  have hfgi : Integrable (fun v => f (ϕ z + (r : ℂ) * v) * g v) :=
    (by fun_prop : Continuous fun v => f (ϕ z + (r : ℂ) * v) * g v).integrable_of_hasCompactSupport
      g.hasCompactSupport.mul_left
  have hsplit : ∫ y, zoomCont f (ϕ z) r c y * g y =
      (∫ v, f (ϕ z + (r : ℂ) * v) * g v) + c * ∫ y, g y := by
    simp_rw [zoomCont_apply, add_mul]
    rw [integral_add hfgi (hgi.const_mul c), integral_const_mul]
  rw [GFFInv.addConst_apply, GFFInv.affineComp_apply, GFFInv.affineComp_apply, hI, hsplit]
  have hTv : h T = hbar G + r ^ 2 * (∫ v, f (ϕ z + (r : ℂ) * v) * g v) +
      Q γ * (r ^ 2 * ∫ w, Real.log ‖deriv (zoomMap ϕ z r) w‖ * τg w) := by
    rw [← hA, ← hB]
    linarith
  rw [hTv]
  field_simp
  ring

end SmallGammaGeodesics.CC
