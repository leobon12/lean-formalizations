import SupercriticalConformalCovariance.BiLip.L51.Scale
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.JointCompactPort

/-!
# Lemma 5.1: the field-measurable replacement of `e`

With `Y = cl A_{r/2,2r}(z) ⊆ U`, `K_T = φ(Y)` and any field `G`:

  `ehat D Y φ G (u, v) = D_G(φ u, φ v; K_T)` for `u, v ∈ Y` (`⊤` otherwise).

* `measurable_ehat`: jointly Borel in `(G, u, v)` (compact internal metrics are jointly lsc, SLU
  `internal_compact_joint_lsc`).
* `confT_eq_intExt`: for `G = g₀ + F` with `F = k` on `K_T` and the Weyl identity, `e(·,·; Y)` is
  `D_G(φ ·, φ ·; K_T)` (the domain-metric layer's domain Weyl/internal identities).
* `transportedE_eq_ehat`: at every (G5)-antecedent pair the shield gives
  `e(u, v) = e(u, v; Y) = ehat (u, v)` (`target_shield`).
* `good_congr_ehat`: hence the literal good event of `(D_h, e)` equals that of `(D_h, ehat)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip.L51

open SupercriticalLQGUniqueness (LSCMetric EuclideanAnnulus aroundDist weylScale Disconnects)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events (eventCarrier eventMiddle eventBoundary)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36 (intExt sphere_subset_middle)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated (aroundRat)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)
open SupercriticalConformalCovariance (IsConformalBijection weylScaleOn domainMetric)
open LQGMetric (DistC addFun)
open SupercriticalConformalCovariance.Domain (dV SV resC)
open HigherDimLQGMetric (internalWith)
open SupercriticalConformalCovariance.BiLip (eT confT pathInf)

/-! ## The replacement -/

open Classical in
/-- `ehat D Y φ G (u, v) = D_G(φ u, φ v; φ(Y))` on `Y × Y`, `⊤` elsewhere -/
def ehat (D : DistC → LSCMetric) (Y : Set ℂ) (φ : ℂ → ℂ) (G : DistC) (p : ℂ × ℂ) : ℝ≥0∞ :=
  if p.1 ∈ Y ∧ p.2 ∈ Y then intExt (D G) (φ '' Y) (φ p.1) (φ p.2) else ⊤

theorem ehat_of_mem {D : DistC → LSCMetric} {Y : Set ℂ} {φ : ℂ → ℂ} {G : DistC} {u v : ℂ}
    (hu : u ∈ Y) (hv : v ∈ Y) : ehat D Y φ G (u, v) = intExt (D G) (φ '' Y) (φ u) (φ v) := by
  unfold ehat; rw [if_pos ⟨hu, hv⟩]

theorem intExt_compact_measurable {K : Set ℂ} (hK : IsCompact K) :
    Measurable fun p : LSCMetric × (ℂ × ℂ) => intExt p.1 K p.2.1 p.2.2 := by
  set S : Set (LSCMetric × (ℂ × ℂ)) := {p | p.2.1 ∈ K ∧ p.2.2 ∈ K} with hSdef
  have hS : MeasurableSet S :=
    ((measurable_fst.comp measurable_snd) hK.isClosed.measurableSet).inter
      ((measurable_snd.comp measurable_snd) hK.isClosed.measurableSet)
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · let ψ : S → LSCMetric × (K × K) := fun p => (p.1.1, (⟨p.1.2.1, p.2.1⟩, ⟨p.1.2.2, p.2.2⟩))
    have hψ : Measurable ψ := by
      have hb : Measurable fun p : S => p.1 := measurable_subtype_coe
      refine (measurable_fst.comp hb).prodMk (Measurable.prodMk ?_ ?_)
      · exact ((measurable_fst.comp measurable_snd).comp hb).subtype_mk
      · exact ((measurable_snd.comp measurable_snd).comp hb).subtype_mk
    have hint := (SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.internal_compact_joint_lsc
      hK).measurable
    have heq : S.domRestrict (fun p : LSCMetric × (ℂ × ℂ) => intExt p.1 K p.2.1 p.2.2) =
        (fun q : LSCMetric × (K × K) => q.1.internal K (q.2.1, q.2.2)) ∘ ψ := by
      funext p; rfl
    rw [heq]
    exact hint.comp hψ
  · have heq : Sᶜ.domRestrict (fun p : LSCMetric × (ℂ × ℂ) => intExt p.1 K p.2.1 p.2.2) =
        fun _ => ⊤ := by
      funext p
      have hp : ¬ (p.1.2.1 ∈ K ∧ p.1.2.2 ∈ K) := p.2
      by_cases h0 : p.1.2.1 ∈ K
      · exact SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_right _
          (fun h1 => hp ⟨h0, h1⟩)
      · exact SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.intExt_eq_top_of_not_mem_left _ h0
    rw [heq]
    exact measurable_const

/-- `ehat` is jointly Borel in the field and the pair -/
theorem measurable_ehat {D : DistC → LSCMetric} (hD : Measurable D) {Y : Set ℂ} (hY : IsCompact Y)
    {φ : ℂ → ℂ} (hφ : ContinuousOn φ Y) :
    Measurable fun x : DistC × (ℂ × ℂ) => ehat D Y φ x.1 x.2 := by
  have hK : IsCompact (φ '' Y) := hY.image_of_continuousOn hφ
  set S : Set (DistC × (ℂ × ℂ)) := {x | x.2.1 ∈ Y ∧ x.2.2 ∈ Y} with hSdef
  have hS : MeasurableSet S :=
    ((measurable_fst.comp measurable_snd) hY.isClosed.measurableSet).inter
      ((measurable_snd.comp measurable_snd) hY.isClosed.measurableSet)
  refine measurable_of_restrict_of_restrict_compl hS ?_ ?_
  · have hφY : Continuous fun y : Y => φ y := hφ.domRestrict
    have hm : Measurable fun x : S => ((D x.1.1, (φ x.1.2.1, φ x.1.2.2)) : LSCMetric × (ℂ × ℂ)) := by
      have hb : Measurable fun x : S => x.1 := measurable_subtype_coe
      refine (hD.comp (measurable_fst.comp hb)).prodMk (Measurable.prodMk ?_ ?_)
      · have h1 : Measurable fun x : S => (⟨x.1.2.1, x.2.1⟩ : Y) :=
          ((measurable_fst.comp measurable_snd).comp hb).subtype_mk
        exact hφY.measurable.comp h1
      · have h1 : Measurable fun x : S => (⟨x.1.2.2, x.2.2⟩ : Y) :=
          ((measurable_snd.comp measurable_snd).comp hb).subtype_mk
        exact hφY.measurable.comp h1
    have heq : S.domRestrict (fun x : DistC × (ℂ × ℂ) => ehat D Y φ x.1 x.2) =
        (fun p : LSCMetric × (ℂ × ℂ) => intExt p.1 (φ '' Y) p.2.1 p.2.2) ∘
          fun x : S => ((D x.1.1, (φ x.1.2.1, φ x.1.2.2)) : LSCMetric × (ℂ × ℂ)) := by
      funext x
      simp only [Set.domRestrict_apply, Function.comp_apply]
      exact ehat_of_mem x.2.1 x.2.2
    rw [heq]
    exact (intExt_compact_measurable hK).comp hm
  · have heq : Sᶜ.domRestrict (fun x : DistC × (ℂ × ℂ) => ehat D Y φ x.1 x.2) = fun _ => ⊤ := by
      funext x
      have hx : ¬ (x.1.2.1 ∈ Y ∧ x.1.2.2 ∈ Y) := x.2
      simp only [Set.domRestrict_apply, ehat, if_neg hx]
    rw [heq]
    exact measurable_const

/-! ## The loop of (9) -/

theorem exists_loop_of_aroundDist_lt {D : LSCMetric} {A : EuclideanAnnulus} {M : ℝ≥0∞}
    (h : aroundDist D A < M) :
    ∃ (L : ℝ → ℂ) (σ₀ σ₁ : ℝ), D.IsCurve L σ₀ σ₁ ∧ (∀ t ∈ Icc σ₀ σ₁, L t ∈ A.toSet) ∧
      Disconnects (L '' Icc σ₀ σ₁) A.innerBoundary A.outerBoundary ∧ D.len L σ₀ σ₁ < M := by
  unfold aroundDist at h
  simp only [iInf_lt_iff] at h
  obtain ⟨L, σ₀, σ₁, hL, htr, hd, hlen⟩ := h
  exact ⟨L, σ₀, σ₁, hL, htr, hd, hlen⟩

/-! ## The internal target metric of the carrier -/

/-- `e(·,·; C) = D_G(φ ·, φ ·; φ(C))` for `G = g₀ + F` with `F = k` on `φ(C)` -/
theorem confT_eq_intExt {D₀ : LSCMetric} {ξ : ℝ} {U V : Set ℂ} (k : C(V, ℝ)) {φ : ℂ → ℂ}
    (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hL : D₀.IsLengthSpace) (hV : IsOpen V)
    (hφU : MapsTo φ U V) {C : Set ℂ} (hCU : C ⊆ U) (F : C(ℂ, ℝ))
    (hFk : ∀ y (hy : y ∈ V), y ∈ φ '' C → F y = k ⟨y, hy⟩) (E : LSCMetric)
    (hE : ∀ q, E q = weylScale ξ F D₀ q) {x y : ℂ} (hx : x ∈ C) (hy : y ∈ C) :
    confT D₀ ξ k φ C x y = intExt E (φ '' C) (φ x) (φ y) := by
  have hKV : φ '' C ⊆ V := by rintro _ ⟨w, hw, rfl⟩; exact hφU (hCU hw)
  have hx' : φ x ∈ φ '' C := mem_image_of_mem φ hx
  have hy' : φ y ∈ φ '' C := mem_image_of_mem φ hy
  have h1 := SupercriticalConformalCovariance.Domain.weylScaleOn_resC_eq_internalWith (ξ := ξ) hf hV hKV k
    (⟨φ x, hx'⟩, ⟨φ y, hy'⟩)
  have h2 := SupercriticalConformalCovariance.Domain.weylScaleOn_eq_internal_of_extension hξ hf hL (resC hKV k) F
    (fun w hw => by rw [hFk w (hKV hw) hw]; rfl) E hE (⟨φ x, hx'⟩, ⟨φ y, hy'⟩)
  rw [confT, ← h1, h2]
  rfl

/-! ## The shield at the antecedent pairs -/

/-- the domain metric at `(φ u, φ v)` is `e(u, v)` -/
theorem domainMetric_eq_eT (ξ : ℝ) (D : DistC → LSCMetric) {V : Opens ℂ} (g₀ : DistC)
    (k : C(V, ℝ)) (hf : Continuous (forget (D g₀))) {φ : ℂ → ℂ} {u v : ℂ} (hu : φ u ∈ V)
    (hv : φ v ∈ V) :
    domainMetric ξ D V g₀ k (⟨φ u, hu⟩, ⟨φ v, hv⟩) = eT (D g₀) ξ k φ u v :=
  SupercriticalConformalCovariance.Domain.weylScaleOn_eq_dV hf k _

/-- **The shield at a (G5)-antecedent pair**: `e(u, v) = ehat(u, v)`. -/
theorem transportedE_eq_ehat (ξ : ℝ) (hξ : 0 ≤ ξ) (D : DistC → LSCMetric) {U V : Opens ℂ}
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) (h g₀ : DistC) (k : C(V, ℝ))
    (hf₀ : Continuous (forget (D g₀))) (hL₀ : (D g₀).IsLengthSpace)
    (hWeyl : ∀ f : C(ℂ, ℝ), weylScale ξ f (D g₀) = (D (addFun g₀ f)).1)
    (hBh : SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier (D h))
    (hLh : (D h).IsLengthSpace)
    {C : ℝ} (hC : 1 ≤ C)
    (hcmp : ∀ u v : U,
      ENNReal.ofReal C⁻¹ * (D h).internal U (u, v) ≤
          domainMetric ξ D V g₀ k (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
        domainMetric ξ D V g₀ k (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
          ENNReal.ofReal C * (D h).internal U (u, v))
    {z : ℂ} {r : Ioi (0 : ℝ)} (hYU : eventCarrier z r ⊆ U) (F : C(ℂ, ℝ))
    (hFk : ∀ y (hy : y ∈ (V : Set ℂ)), y ∈ φ '' eventCarrier z r → F y = k ⟨y, hy⟩)
    (hSt : setDist (D h) (eventMiddle z r) (eventBoundary z r) < ⊤)
    {q : Ioo (0 : ℝ) (1 / 100)} {u v : ℂ} (hu : u ∈ eventMiddle z r) (hv : v ∈ sphere z r)
    (huv : dist u v ≤ (q : ℝ) * r)
    (h9 : aroundRat (D h, (v, (q : ℝ) * r, Real.sqrt q * r)) ≤
      ENNReal.ofReal (SupercriticalConformalCovariance.Good.shieldK C) * SupercriticalConformalCovariance.GoodAnnulus.barrier (D h) z r) :
    SupercriticalConformalCovariance.Good.transportedE ξ D hφ g₀ k (u, v) =
      ehat D (eventCarrier z r) φ (addFun g₀ F) (u, v) := by
  have hr : (0 : ℝ) < r := r.2
  have hq0 : (0 : ℝ) < q := q.2.1
  have hq1 : (q : ℝ) < 1 / 100 := q.2.2
  have hC0 : 0 < C := by linarith
  set Y := eventCarrier z r with hYdef
  set ψ := Function.invFunOn φ U with hψdef
  have hψ := SupercriticalConformalCovariance.BiLip.PortRev.inverse_conformal hφ
  have hφψ : ∀ y ∈ (V : Set ℂ), φ (ψ y) = y := fun y hy => hφ.2.invOn_invFunOn.2 hy
  have hψφ : ∀ x ∈ (U : Set ℂ), ψ (φ x) = x := fun x hx => hφ.2.injOn.leftInvOn_invFunOn hx
  have hφc : ContinuousOn φ U := hφ.1.continuousOn
  have hvM : v ∈ eventMiddle z r := sphere_subset_middle (s := (r : ℝ)) hr (by linarith) (by linarith) hv
  have huY : u ∈ Y := middle_subset_carrier hu
  have hvY : v ∈ Y := middle_subset_carrier hvM
  have huU : u ∈ (U : Set ℂ) := hYU huY
  have hvU : v ∈ (U : Set ℂ) := hYU hvY
  -- the comparison in `eT`/`pathInf` form
  have hup : ∀ x ∈ (U : Set ℂ), ∀ y ∈ (U : Set ℂ),
      eT (D g₀) ξ k φ x y ≤ ENNReal.ofReal C * pathInf (D h) U x y := by
    intro x hx y hy
    have := (hcmp ⟨x, hx⟩ ⟨y, hy⟩).2
    rwa [domainMetric_eq_eT ξ D g₀ k hf₀] at this
  have hlo : ∀ x ∈ (U : Set ℂ), ∀ y ∈ (U : Set ℂ),
      pathInf (D h) U x y ≤ ENNReal.ofReal C * eT (D g₀) ξ k φ x y := by
    intro x hx y hy
    have h1 := (hcmp ⟨x, hx⟩ ⟨y, hy⟩).1
    rw [domainMetric_eq_eT ξ D g₀ k hf₀] at h1
    calc pathInf (D h) U x y = ENNReal.ofReal C * (ENNReal.ofReal C⁻¹ * pathInf (D h) U x y) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC0.le, mul_inv_cancel₀ hC0.ne', ENNReal.ofReal_one,
            one_mul]
      _ ≤ ENNReal.ofReal C * eT (D g₀) ξ k φ x y := by gcongr; exact h1
  -- the loop of (9)
  have hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), (D h).IsCurve γ a b → ContinuousOn γ (Icc a b) :=
    fun γ a b hγ =>
      SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.continuousOn_of_barrier_of_length _
        hBh hLh hγ
  have hbe := barrier_eq_ambient (D h) hcont hLh z r
  set S := setDist (D h) (eventMiddle z r) (eventBoundary z r) with hSdef
  have hS0 : 0 < S := SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.setDist_middle_pos (D h) z hr
  have hq1' : (q : ℝ) < 1 := by linarith
  have hvalid := SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.loop_annulus_valid
    hr hq0 hq1'
  have hlt : aroundDist (D h) (annAt v ((q : ℝ) * r) (Real.sqrt q * r) hvalid) <
      ENNReal.ofReal (1 / (2 * C ^ 2)) * S := by
    rw [← aroundRat_eq_annAt]
    refine h9.trans_lt ?_
    rw [hbe]
    refine (ENNReal.mul_lt_mul_iff_left hS0.ne' hSt.ne).2 ?_
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    unfold SupercriticalConformalCovariance.Good.shieldK
    have : 0 < C ^ 2 := by positivity
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨L, σ₀, σ₁, hL, hLtr, hLd, hLlen⟩ := exists_loop_of_aroundDist_lt hlt
  have hLA : ∀ t ∈ Icc σ₀ σ₁, L t ∈ ball v (Real.sqrt q * r) := fun t ht => (hLtr t ht).1
  -- the shield and the internal identity
  have hE : ∀ (F' : C(ℂ, ℝ)) (q' : ℂ × ℂ), (D (addFun g₀ F')) q' = weylScale ξ F' (D g₀) q' :=
    fun F' q' => (congrFun (hWeyl F') q').symm
  have hsh := target_shield k hξ hf₀ hL₀ V.isOpen (fun F' => D (addFun g₀ F')) hE hφc
    hφ.2.mapsTo hψ.2.mapsTo hψ.1.continuousOn hφψ hψφ hC hup hlo hr hq0 hq1 hYU hv huv hL hLA
    hLd hLlen hSt
  have hconf := confT_eq_intExt k hξ hf₀ hL₀ V.isOpen hφ.2.mapsTo hYU F hFk (D (addFun g₀ F))
    (hE F) huY hvY
  rw [SupercriticalConformalCovariance.Good.transportedE, dif_pos ⟨huU, hvU⟩, domainMetric_eq_eT ξ D g₀ k hf₀, hsh, hconf,
    ehat_of_mem huY hvY]

theorem mem_middle_of_sphere_a {z u : ℂ} {r : Ioi (0 : ℝ)} {q : Ioo (0 : ℝ) (1 / 100)}
    {a : Ioo (1 - (q : ℝ)) 1} (hu : u ∈ sphere z ((a : ℝ) * r)) : u ∈ eventMiddle z r := by
  have hr0 : (0 : ℝ) < r := r.2
  have ha1 : (a : ℝ) < 1 := a.2.2
  have haq : 1 - (q : ℝ) < a := a.2.1
  have hq1 : (q : ℝ) < 1 / 100 := q.2.2
  have h1 : 3 * (r : ℝ) / 4 < (a : ℝ) * r := by nlinarith
  have h2 : (a : ℝ) * r < 3 * (r : ℝ) / 2 := by nlinarith
  exact sphere_subset_middle hr0 h1 h2 hu

/-- **The good event of `(D_h, e)` is that of `(D_h, ehat)`** on the sample. -/
theorem good_congr_ehat (ξ : ℝ) (hξ : 0 ≤ ξ) (D : DistC → LSCMetric) {U V : Opens ℂ}
    {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V) (h g₀ : DistC) (k : C(V, ℝ))
    (hf₀ : Continuous (forget (D g₀))) (hL₀ : (D g₀).IsLengthSpace)
    (hWeyl : ∀ f : C(ℂ, ℝ), weylScale ξ f (D g₀) = (D (addFun g₀ f)).1)
    (hBh : SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Barrier (D h))
    (hLh : (D h).IsLengthSpace)
    {C : ℝ} (hC : 1 ≤ C)
    (hcmp : ∀ u v : U,
      ENNReal.ofReal C⁻¹ * (D h).internal U (u, v) ≤
          domainMetric ξ D V g₀ k (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ∧
        domainMetric ξ D V g₀ k (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) ≤
          ENNReal.ofReal C * (D h).internal U (u, v))
    {z : ℂ} {r : Ioi (0 : ℝ)} (hYU : eventCarrier z r ⊆ U) (F : C(ℂ, ℝ))
    (hFk : ∀ y (hy : y ∈ (V : Set ℂ)), y ∈ φ '' eventCarrier z r → F y = k ⟨y, hy⟩)
    (hSt : setDist (D h) (eventMiddle z r) (eventBoundary z r) < ⊤)
    (Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (θ : Ioi (0 : ℝ)) (c η : ℝ) :
    SupercriticalConformalCovariance.Improve.Good (D h) (SupercriticalConformalCovariance.Good.transportedE ξ D hφ g₀ k) ξ Q z r q a K θ
        (SupercriticalConformalCovariance.Good.shieldK C) c η ↔
      SupercriticalConformalCovariance.Improve.Good (D h) (ehat D (eventCarrier z r) φ (addFun g₀ F)) ξ Q z r q a K θ
        (SupercriticalConformalCovariance.Good.shieldK C) c η := by
  refine and_congr Iff.rfl ?_
  unfold SupercriticalConformalCovariance.Improve.G5
  refine forall₂_congr fun u v => ?_
  constructor
  · intro H hreg huv h9
    have hu : u ∈ eventMiddle z r := mem_middle_of_sphere_a hreg.2.1
    rw [← transportedE_eq_ehat ξ hξ D hφ h g₀ k hf₀ hL₀ hWeyl hBh hLh hC hcmp hYU F hFk hSt hu
      hreg.2.2.1 huv h9]
    exact H hreg huv h9
  · intro H hreg huv h9
    have hu : u ∈ eventMiddle z r := mem_middle_of_sphere_a hreg.2.1
    rw [transportedE_eq_ehat ξ hξ D hφ h g₀ k hf₀ hL₀ hWeyl hBh hLh hC hcmp hYU F hFk hSt hu
      hreg.2.2.1 huv h9]
    exact H hreg huv h9

end SupercriticalConformalCovariance.BiLip.L51
