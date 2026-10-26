import SupercriticalConformalCovariance.Lemma31.Random

/-!
# Lemma 3.1 for realized domain fields

The repaired Lemma 3.1 (`lem-3.1#repaired`) for fields given on an open
neighbourhood `V` of `K′` through realizations in the sense of the candidate
`SupercriticalConformalCovariance.IsDomainRealization`: `h n = h0 n|_V + k n` with `h0 n` a
whole-plane GFF plus a continuous function and `k n ∈ C(V)`. The intrinsic metric on `K` of the field
`h n + f n` (`f n ∈ C(K′)`) is `confined ξ (D (h0 n)) hKK' (k n|_{K′} + f n)`, i.e.
`e^{ξ (k n + f n)} · D_{h0 n}(·, ·; K)`, ∞ off `K × K`.
Reduction to `confinedConvergence_subseq_of_events`: with the explicit cutoff `χ_m` of
`SupercriticalConformalCovariance.Domain` (`= 1` on `exW V m ⊇ K`), the whole-plane fields `G n = h0 n + χ_m k n` agree with
`h n` on `U ⊓ exW V m` and have the same confined metrics.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Lemma31

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont addFun ofCont)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric LSCTendsto)
open SupercriticalConformalCovariance (IsDomainRealization weylScaleOn)
open SupercriticalConformalCovariance.Domain (confined resC restrictOn restrictOn_restrictTo exW exWO exWO_le cutF cutF_eq
  ae_restrictTo_cutF ae_weylScaleOn_eq_internal isGFFPlusCont_addFun_of_measurable coe_monoCLM
  measurable_cutExt exists_subset_exW)

theorem restrictOn_restrictOn {W U V : Opens ℂ} (hWU : W ≤ U) (hUV : U ≤ V) (h : DistOn V) :
    restrictOn hWU (restrictOn hUV h) = restrictOn (hWU.trans hUV) h := by
  ext φ
  show h _ = h _
  congr 1
  ext x
  simp only [ContinuousLinearMap.coe_coe]
  rw [coe_monoCLM hUV, coe_monoCLM hWU, coe_monoCLM (hWU.trans hUV)]

theorem addFun_addFun (x : DistC) (A B : C(ℂ, ℝ)) :
    addFun (addFun x A) B = addFun x (A + B) := by
  simp only [addFun, SupercriticalConformalCovariance.Domain.ofCont_add, add_assoc]

/-- **Field reduction.** For a realization `(h0, k)` of `h` on `V`, a.s. the cut-off whole-plane
field `h0 + χ_m k` restricted to `W ≤ exW V m` is `h|_W`. -/
theorem ae_restrictTo_cut_eq {V : Opens ℂ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn V} {h₀ : Ω → DistC} {k : Ω → C(V, ℝ)} (hR : IsDomainRealization V P h h₀ k)
    (m : ℕ) {W : Opens ℂ} (hW : W ≤ exWO V m) :
    ∀ᵐ ω ∂P, restrictTo W (addFun (h₀ ω) (cutF V m (k ω))) =
      restrictOn (hW.trans (exWO_le V m)) (h ω) := by
  filter_upwards [ae_restrictTo_cutF hR m] with ω hω
  have e : restrictTo (exWO V m) (addFun (h₀ ω) (cutF V m (k ω))) =
      restrictOn (exWO_le V m) (h ω) := by
    ext φ
    exact hω φ
  rw [← restrictOn_restrictTo hW, e, restrictOn_restrictOn]

/-- **Metric reduction** (one sample). On the consistency events of `D_{h0}` and `D_{h0 + χ_m k}`
(`ae_weylScaleOn_eq_internal`), if `K ⊆ exW V m`, the confined metric of `h0 + k + f` equals that of
`(h0 + χ_m k) + f`, for every `f ∈ C(K′)`. -/
theorem confined_cut_eq {ξ : ℝ} {D : DistC → LSCMetric} {V : Opens ℂ} {x : DistC} (k : C(V, ℝ))
    (m : ℕ) (c : ℂ) {R : ℝ} (hR : 0 < R) {K' : Set ℂ} (hKK' : closedBall c R ⊆ K')
    (hK'V : K' ⊆ V) (hKm : closedBall c R ⊆ exW V m)
    (hx : ∀ (K : Set ℂ) (f : C(K, ℝ)) (F : C(ℂ, ℝ)), (∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) →
      ∀ p : K × K, weylScaleOn ξ f (D x) p = (D (addFun x F)).internal K p)
    (hG : ∀ (K : Set ℂ) (f : C(K, ℝ)) (F : C(ℂ, ℝ)), (∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) →
      ∀ p : K × K, weylScaleOn ξ f (D (addFun x (cutF V m k))) p =
        (D (addFun (addFun x (cutF V m k)) F)).internal K p)
    (f : C(K', ℝ)) :
    confined ξ (D x) hKK' (resC hK'V k + f) = confined ξ (D (addFun x (cutF V m k))) hKK' f := by
  funext q
  unfold confined
  split_ifs with hq
  · set p : closedBall c R × closedBall c R := (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)
    rw [hx _ _ (cutF V m k + diskExt c hR (resC hKK' f)) ?_ p,
      hG _ _ (diskExt c hR (resC hKK' f)) (fun z hz => diskExt_eq c hR _ z hz) p, addFun_addFun]
    intro z hz
    rw [ContinuousMap.add_apply, cutF_eq V m k z (hKm hz), diskExt_eq c hR _ z hz]
    rfl
  · rfl

/-- **Lemma 3.1 (repaired, `lem-3.1#repaired`) for realized fields.** Fields `h n`, `hL` on an open
`V ⊇ K′`, realized by `(h0 n, k n)`, `(h0L, kL)` (`IsDomainRealization`), on one probability space;
corrections `f n, fL ∈ C(K′)` (`fL` measurable). If `P[h_n|_U ≠ hL|_U] → 0` (`U ≤ V` open, `K ⊆ U`)
and `sup_{K′}|f_n − fL| → 0` in probability, then every subsequence has a further subsequence along
which, a.s., the intrinsic metrics on `K` of `h_n + f_n` converge (DG Definition 1.2, ∞ off `K × K`)
to that of `hL + fL`, and `h_n|_U = hL|_U` eventually. -/
theorem confinedConvergence_subseq_realized {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {K' : Set ℂ} (hKK' : closedBall c R ⊆ K') (V : Opens ℂ) (hK'V : K' ⊆ V) (U : Opens ℂ)
    (hUV : U ≤ V) (hKU : closedBall c R ⊆ U)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : ℕ → Ω → DistOn V) (h₀ : ℕ → Ω → DistC) (k : ℕ → Ω → C(V, ℝ))
    (hRn : ∀ n, IsDomainRealization V P (h n) (h₀ n) (k n))
    (hL : Ω → DistOn V) (h₀L : Ω → DistC) (kL : Ω → C(V, ℝ))
    (hRL : IsDomainRealization V P hL h₀L kL)
    (f : ℕ → Ω → C(K', ℝ)) (fL : Ω → C(K', ℝ)) (hfL : Measurable fL)
    (hcoup : Tendsto (fun n => P {ω | restrictOn hUV (h n ω) ≠ restrictOn hUV (hL ω)}) atTop
      (𝓝 0))
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ∃ x : K', ε < |f n ω x - fL ω x|}) atTop (𝓝 0)) :
    ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂P,
      LSCTendsto
        (fun j q => (confined (ξ : ℝ) (D (h₀ (ns (ms j)) ω)) hKK'
          (resC hK'V (k (ns (ms j)) ω) + f (ns (ms j)) ω) q : EReal))
        (fun q => (confined (ξ : ℝ) (D (h₀L ω)) hKK' (resC hK'V (kL ω) + fL ω) q : EReal)) ∧
      ∀ᶠ j in atTop, restrictOn hUV (h (ns (ms j)) ω) = restrictOn hUV (hL ω) := by
  intro ns hns
  obtain ⟨m, hm⟩ := exists_subset_exW V.isOpen (isCompact_closedBall c R) (hKK'.trans hK'V)
  set U' : Opens ℂ := U ⊓ exWO V m with hU'
  have hU'W : U' ≤ exWO V m := inf_le_right
  have hU'U : U' ≤ U := inf_le_left
  have hKU' : closedBall c R ⊆ U' := fun z hz => ⟨hKU hz, hm hz⟩
  set G : ℕ → Ω → DistC := fun n ω => addFun (h₀ n ω) (cutF V m (k n ω)) with hGdef
  set Glim : Ω → DistC := fun ω => addFun (h₀L ω) (cutF V m (kL ω)) with hGlimdef
  have hG : ∀ n, IsGFFPlusCont (G n) P := fun n =>
    isGFFPlusCont_addFun_of_measurable (hRn n).2.1 (measurable_cutExt V.isOpen _ (hRn n).2.2.1)
  have hGlim : IsGFFPlusCont Glim P :=
    isGFFPlusCont_addFun_of_measurable hRL.2.1 (measurable_cutExt V.isOpen _ hRL.2.2.1)
  set E : ℕ → Set Ω := fun n => {ω | restrictOn hUV (h n ω) = restrictOn hUV (hL ω)} with hEdef
  have hEU : ∀ᵐ ω ∂P, ∀ n, ω ∈ E n → restrictTo U' (G n ω) = restrictTo U' (Glim ω) := by
    filter_upwards [ae_all_iff.2 fun n => ae_restrictTo_cut_eq (hRn n) m hU'W,
      ae_restrictTo_cut_eq hRL m hU'W] with ω hn hLω n hE
    rw [hn n, hLω, ← restrictOn_restrictOn hU'U hUV, ← restrictOn_restrictOn hU'U hUV]
    exact congrArg _ hE
  obtain ⟨ms, hms, hae⟩ := confinedConvergence_subseq_of_events hD c hR hKK' U' hKU' P G Glim hG
    hGlim f fL hfL E hcoup hEU hconv ns hns
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae, ae_all_iff.2 fun n => ae_weylScaleOn_eq_internal hD P (hRn n).2.1,
    ae_all_iff.2 fun n => ae_weylScaleOn_eq_internal hD P (hG n),
    ae_weylScaleOn_eq_internal hD P hRL.2.1, ae_weylScaleOn_eq_internal hD P hGlim]
    with ω hω hx hxG hxL hxGlim
  refine ⟨?_, hω.2⟩
  have e1 : ∀ n, confined (ξ : ℝ) (D (h₀ n ω)) hKK' (resC hK'V (k n ω) + f n ω) =
      confined (ξ : ℝ) (D (G n ω)) hKK' (f n ω) := fun n =>
    confined_cut_eq (k n ω) m c hR hKK' hK'V hm (hx n) (hxG n) (f n ω)
  have e2 : confined (ξ : ℝ) (D (h₀L ω)) hKK' (resC hK'V (kL ω) + fL ω) =
      confined (ξ : ℝ) (D (Glim ω)) hKK' (fL ω) :=
    confined_cut_eq (kL ω) m c hR hKK' hK'V hm hxL hxGlim (fL ω)
  simp only [e1, e2]
  exact hω.1

end SupercriticalConformalCovariance.Lemma31
