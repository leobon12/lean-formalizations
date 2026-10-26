import SupercriticalConformalCovariance.BiLip.Source
import SupercriticalConformalCovariance.Domain.Geometry

/-!
# Lemma 2.1: the pulled-back metric `e` as source and as target of the deterministic core

Paper l. 34–37 (forward convention): `e(u, v) = D_{h^φ}(φ(u), φ(v); V)`. For one sample of a realization
`h^φ = g₀|_V + k` of the target field (`IsDomainRealization`), `D₀ = D_{g₀}` and the domain metric is
`D_{h^φ}(·,·;V) = weylScaleOn ξ k D₀ = dV D₀ ξ k` (`weylScaleOn_eq_dV`). Everything here is
deterministic, for an `LSCMetric` `D₀` with `(ℂ, D₀) → ℂ` continuous, and a homeomorphism `φ : U → V` with
inverse `ψ` (explicit hypotheses; for a conformal bijection see `Lemma21.lean`).

* `eT x y = dV(φ x, φ y)`: the metric `e`;
* `lenT P a b`: the `e`-length of `P`, i.e. the `dV`-length of `φ ∘ P` (`curveLengthWith`), on the
  admissible paths `AdmT` (Euclidean-continuous paths in `U` with `φ ∘ P` a `D₀`-continuous curve);
* `confT C x y`: the internal metric of `e` on `C` (paths in `φ(C)` measured with `dV`), which is the domain
  metric of `k|_{φ(C)}` on `φ(C)` (`weylScaleOn_resC_eq_internalWith`), hence, for compact `C`, the
  internal metric of a WHOLE-PLANE metric `e^{ξ F}·D₀` on `φ(C)` for any continuous extension `F` of
  `k|_{φ(C)}` (`weylScaleOn_eq_internal_of_extension`; Tietze). This is Lemma 1.2's object;
* `acrT z r = e(across A_{r/2,r}(z))` (distance between the two boundary circles), and
  `aroundT U z r = e(around A_{r,2r}(z))` (infimum of `e`-lengths of admissible loops in `A_{r,2r}(z)`
  separating its boundary circles).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale Disconnects)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalConformalCovariance (weylScaleOn)
open SupercriticalConformalCovariance.Domain (dV SV wV resC)
open HigherDimLQGMetric (curveLengthWith internalWith partitionSup)

section Defs

variable (D₀ : LSCMetric) (ξ : ℝ) {V : Set ℂ} (k : C(V, ℝ)) (φ : ℂ → ℂ)

/-- the metric `e(x, y) = D_{h^φ}(φ x, φ y; V)` -/
def eT (x y : ℂ) : ℝ≥0∞ := dV D₀ ξ k (D₀.pt (φ x)) (D₀.pt (φ y))

/-- the `e`-length of a path: the `dV`-length of `φ ∘ P` -/
def lenT (P : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ := curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ φ ∘ P) a b

/-- admissible paths for `e`: Euclidean-continuous paths in `U` whose image `φ ∘ P` is a `D₀`-curve -/
def AdmT (U : Set ℂ) (P : ℝ → ℂ) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn P (Icc a b) ∧ ContinuousOn (D₀.pt ∘ φ ∘ P) (Icc a b) ∧
    ∀ t ∈ Icc a b, P t ∈ U

/-- the internal metric of `e` on `C`: `e(x, y; C)` -/
def confT (C : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  internalWith (dV D₀ ξ k) (SV D₀ (φ '' C)) (D₀.pt (φ x)) (D₀.pt (φ y))

/-- `e(across A_{r/2,r}(z))`: the `e`-distance between `∂B_{r/2}(z)` and `∂B_r(z)` -/
def acrT (z : ℂ) (r : ℝ) : ℝ≥0∞ := ⨅ x ∈ sphere z (r / 2), ⨅ y ∈ sphere z r, eT D₀ ξ k φ x y

/-- `e(around A_{r,2r}(z))`: the infimum of the `e`-lengths of admissible loops in `A_{r,2r}(z)` which
separate `∂B_r(z)` from `∂B_{2r}(z)` -/
def aroundT (U : Set ℂ) (z : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → ℂ) (s₀ : ℝ) (s₁ : ℝ) (_ : AdmT D₀ φ U γ s₀ s₁)
    (_ : ∀ t ∈ Icc s₀ s₁, γ t ∈ ball z (2 * r) \ closedBall z r)
    (_ : Disconnects (γ '' Icc s₀ s₁) (sphere z r) (sphere z (2 * r))), lenT D₀ ξ k φ γ s₀ s₁

end Defs

/-! ## Lengths -/

/-- affine reparametrization of `[0, 1]` onto `[a, b]` -/
theorem curveLengthWith_affine {X : Type*} (δ : X → X → ℝ≥0∞) (Q : ℝ → X) {a b : ℝ}
    (hab : a ≤ b) :
    curveLengthWith δ (fun s => Q (a + s * (b - a))) 0 1 = curveLengthWith δ Q a b := by
  unfold curveLengthWith
  have h := HigherDimLQGMetric.partitionSup_comp (φ := fun s : ℝ => a + s * (b - a))
    (c := 0) (d := 1) zero_le_one (by fun_prop)
    (fun x _ y _ hxy => by nlinarith) (fun u v => δ (Q u) (Q v))
  simpa using h

/-- a continuous path in `S` on `[a, b]` bounds the induced internal distance of its endpoints -/
theorem internalWith_le_curveLengthWith {X : Type*} [TopologicalSpace X] (δ : X → X → ℝ≥0∞)
    {S : Set X} {Q : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn Q (Icc a b))
    (hS : MapsTo Q (Icc a b) S) : internalWith δ S (Q a) (Q b) ≤ curveLengthWith δ Q a b := by
  have hmaps : MapsTo (fun s : ℝ => a + s * (b - a)) (Icc 0 1) (Icc a b) := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2]
  have hc' : ContinuousOn (fun s => Q (a + s * (b - a))) (Icc 0 1) :=
    hc.comp (by fun_prop) hmaps
  have h := HigherDimLQGMetric.internalWith_le (δ := δ) (x := Q a) (y := Q b) hc'
    (by simp) (by simp) (hS.comp hmaps)
  rwa [curveLengthWith_affine δ Q hab] at h

/-- reversal of a path for a symmetric distance function -/
theorem curveLengthWith_reverse {X : Type*} (δ : X → X → ℝ≥0∞) (hδ : ∀ x y, δ x y = δ y x)
    (Q : ℝ → X) (a b : ℝ) :
    curveLengthWith δ (fun u => Q (a + b - u)) a b = curveLengthWith δ Q a b := by
  unfold curveLengthWith
  rw [← HigherDimLQGMetric.partitionSup_reflect (fun u v => δ (Q u) (Q v)) a b]
  exact HigherDimLQGMetric.partitionSup_congr fun u v _ _ _ => hδ _ _

/-- the reversed form of `internalWith_le_curveLengthWith` -/
theorem internalWith_le_curveLengthWith_rev {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞) (hδ : ∀ x y, δ x y = δ y x)
    {S : Set X} {Q : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn Q (Icc a b))
    (hS : MapsTo Q (Icc a b) S) : internalWith δ S (Q b) (Q a) ≤ curveLengthWith δ Q a b := by
  have hmaps : MapsTo (fun u : ℝ => a + b - u) (Icc a b) (Icc a b) := by
    intro u hu; constructor <;> linarith [hu.1, hu.2]
  have h := internalWith_le_curveLengthWith δ (Q := fun u => Q (a + b - u)) hab
    (hc.comp (by fun_prop) hmaps) (hS.comp hmaps)
  simp only [add_sub_cancel_left, add_sub_cancel_right] at h
  rwa [curveLengthWith_reverse δ hδ Q a b] at h

section Props

variable {D₀ : LSCMetric} {ξ : ℝ} {V : Set ℂ} (k : C(V, ℝ)) {φ ψ : ℂ → ℂ} {U : Set ℂ}

theorem eT_triangle (x y z : ℂ) : eT D₀ ξ k φ x z ≤ eT D₀ ξ k φ x y + eT D₀ ξ k φ y z :=
  HigherDimLQGMetric.weylDistOn_triangle _ _ _

theorem eT_comm (x y : ℂ) : eT D₀ ξ k φ x y = eT D₀ ξ k φ y x :=
  HigherDimLQGMetric.weylDistOn_comm _ _

/-- the `e`-length is additive -/
theorem lenT_add (P : ℝ → ℂ) (s t u : ℝ) (hst : s ≤ t) (htu : t ≤ u) :
    lenT D₀ ξ k φ P s u = lenT D₀ ξ k φ P s t + lenT D₀ ξ k φ P t u :=
  (HigherDimLQGMetric.curveLengthWith_add (fun _ _ _ _ _ _ _ =>
    HigherDimLQGMetric.weylDistOn_triangle _ _ _) hst htu).symm

theorem eT_le_lenT (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    eT D₀ ξ k φ (P a) (P b) ≤ lenT D₀ ξ k φ P a b :=
  HigherDimLQGMetric.le_curveLengthWith (P := D₀.pt ∘ φ ∘ P) hab

/-- **The crossing charge for `e`** (the reverse direction, l. 147): an admissible path running from
`B̄_{r/2}(w)` to `ℂ ∖ B_r(w)` has `e`-length at least `e(across A_{r/2,r}(w))`. -/
theorem acrT_le_lenT (P : ℝ → ℂ) (w : ℂ) (r τ t : ℝ) (hτt : τ ≤ t)
    (hPc : ContinuousOn P (Icc τ t)) (h1 : dist (P τ) w ≤ r / 2) (h2 : r ≤ dist (P t) w) :
    acrT D₀ ξ k φ w r ≤ lenT D₀ ξ k φ P τ t := by
  have hf : ContinuousOn (fun u => dist (P u) w) (Icc τ t) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  have hr0 : 0 ≤ r := by have := dist_nonneg (x := P τ) (y := w); linarith
  obtain ⟨s', hs', hs'r⟩ := intermediate_value_Icc hτt hf ⟨by linarith, h2⟩
  have hf' : ContinuousOn (fun u => dist (P u) w) (Icc τ s') := hf.mono (Icc_subset_Icc le_rfl hs'.2)
  obtain ⟨s, hs, hsr⟩ := intermediate_value_Icc hs'.1 hf' ⟨h1, by simp only at hs'r; linarith⟩
  have hx : P s ∈ sphere w (r / 2) := mem_sphere.2 hsr
  have hy : P s' ∈ sphere w r := mem_sphere.2 hs'r
  calc acrT D₀ ξ k φ w r ≤ eT D₀ ξ k φ (P s) (P s') :=
        iInf₂_le_of_le (P s) hx (iInf₂_le (P s') hy)
    _ ≤ lenT D₀ ξ k φ P s s' := eT_le_lenT k P hs.2
    _ ≤ lenT D₀ ξ k φ P τ t :=
        HigherDimLQGMetric.curveLengthWith_mono_interval hs.1 hs.2 hs'.2

/-- admissible paths approximate `e` from above (`dV` is a length metric on `V`,
`internalWith_dV`) -/
theorem exists_admT_le (hf : Continuous (forget D₀)) (hV : IsOpen V)
    (hψV : MapsTo ψ V U) (hψc : ContinuousOn ψ V) (hφψ : ∀ y ∈ V, φ (ψ y) = y)
    (hψφ : ∀ x ∈ U, ψ (φ x) = x)
    (u : ℂ) (hu : u ∈ U) (v : ℂ) (hv : v ∈ U) (hfin : eT D₀ ξ k φ u v < ∞) (δ : ℝ≥0∞)
    (hδ : 0 < δ) :
    ∃ P a b, AdmT D₀ φ U P a b ∧ (∀ t ∈ Icc a b, P t ∈ U) ∧ P a = u ∧ P b = v ∧
      lenT D₀ ξ k φ P a b ≤ eT D₀ ξ k φ u v + δ := by
  have hint := SupercriticalConformalCovariance.Domain.internalWith_dV (ξ := ξ) hf hV k (D₀.pt (φ u)) (D₀.pt (φ v))
  have hlt : eT D₀ ξ k φ u v < eT D₀ ξ k φ u v + δ := ENNReal.lt_add_right hfin.ne hδ.ne'
  conv_lhs at hlt => rw [eT, ← hint]
  unfold internalWith at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨Q, hQc, hQ0, hQ1, hQS, hQlen⟩ := hlt
  have hQV : ∀ t ∈ Icc (0 : ℝ) 1, forget D₀ (Q t) ∈ V := fun t ht => hQS ht
  set P : ℝ → ℂ := fun t => ψ (forget D₀ (Q t)) with hPdef
  have hPQ : EqOn (D₀.pt ∘ φ ∘ P) Q (Icc 0 1) := by
    intro t ht
    simp only [Function.comp_apply, hPdef]
    exact hφψ _ (hQV t ht)
  have hPc : ContinuousOn P (Icc 0 1) :=
    hψc.comp (hf.comp_continuousOn hQc) (fun t ht => hQV t ht)
  have hPU : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ U := fun t ht => hψV (hQV t ht)
  refine ⟨P, 0, 1, ⟨zero_le_one, hPc, hQc.congr hPQ, hPU⟩, hPU, ?_, ?_, ?_⟩
  · simp only [hPdef, hQ0]; exact hψφ u hu
  · simp only [hPdef, hQ1]; exact hψφ v hv
  · have hlenEq : lenT D₀ ξ k φ P 0 1 = curveLengthWith (dV D₀ ξ k) Q 0 1 := by
      unfold lenT curveLengthWith
      exact HigherDimLQGMetric.partitionSup_congr fun u' v' hu' huv hv' => by
        show dV D₀ ξ k ((D₀.pt ∘ φ ∘ P) u') ((D₀.pt ∘ φ ∘ P) v') = dV D₀ ξ k (Q u') (Q v')
        rw [hPQ ⟨hu', huv.trans hv'⟩, hPQ ⟨hu'.trans huv, hv'⟩]
    rw [hlenEq]; exact hQlen.le

/-- `e ≤ e(·,·;C)` -/
theorem eT_le_confT (hf : Continuous (forget D₀)) (hV : IsOpen V) {C : Set ℂ}
    (hCU : C ⊆ U) (hφU : MapsTo φ U V) (x y : ℂ) :
    eT D₀ ξ k φ x y ≤ confT D₀ ξ k φ C x y := by
  rw [eT, ← SupercriticalConformalCovariance.Domain.internalWith_dV (ξ := ξ) hf hV k]
  refine HigherDimLQGMetric.internalWith_anti ?_
  rintro z ⟨w, hw, hwz⟩
  change forget D₀ z ∈ V
  rw [show forget D₀ z = φ w from hwz.symm]
  exact hφU (hCU hw)

/-- `e(·,·;C)` is antitone in `C` -/
theorem confT_anti {C C' : Set ℂ} (hCC : C ⊆ C') (x y : ℂ) :
    confT D₀ ξ k φ C' x y ≤ confT D₀ ξ k φ C x y :=
  HigherDimLQGMetric.internalWith_anti (preimage_mono (image_mono hCC))

/-- **Lemma 1.2 for `e`, representation**: on a compact `C ⊆ U`, `e(·,·;C)` is the internal metric on `φ(C)`
of the whole-plane metric `E = e^{ξ F} · D₀` for a continuous extension `F` of `k|_{φ(C)}`. -/
theorem exists_confT_eq_pathInf (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hL : D₀.IsLengthSpace)
    (hV : IsOpen V) (E : C(ℂ, ℝ) → LSCMetric) (hE : ∀ F q, E F q = weylScale ξ F D₀ q)
    (hφc : ContinuousOn φ U) (hφU : MapsTo φ U V) {C : Set ℂ} (hC : IsCompact C)
    (hCU : C ⊆ U) :
    ∃ F : C(ℂ, ℝ), ∀ x ∈ C, ∀ y ∈ C,
      confT D₀ ξ k φ C x y = pathInf (E F) (φ '' C) (φ x) (φ y) := by
  have hK : IsCompact (φ '' C) := hC.image_of_continuousOn (hφc.mono hCU)
  have hKV : φ '' C ⊆ V := by rintro _ ⟨w, hw, rfl⟩; exact hφU (hCU hw)
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq hK.isClosed (resC hKV k)
  refine ⟨F, fun x hx y hy => ?_⟩
  have hx' : φ x ∈ φ '' C := mem_image_of_mem φ hx
  have hy' : φ y ∈ φ '' C := mem_image_of_mem φ hy
  have h1 := SupercriticalConformalCovariance.Domain.weylScaleOn_resC_eq_internalWith (ξ := ξ) hf hV hKV k
    (⟨φ x, hx'⟩, ⟨φ y, hy'⟩)
  have h2 := SupercriticalConformalCovariance.Domain.weylScaleOn_eq_internal_of_extension hξ hf hL (resC hKV k) F
    (fun z hz => by rw [← hF]; rfl) (E F) (hE F) (⟨φ x, hx'⟩, ⟨φ y, hy'⟩)
  rw [confT, ← h1, h2, internal_eq_pathInf]

/-- `e(·,·;C)` is an extended pseudometric on a compact `C ⊆ U` -/
theorem isPMetricOn_confT (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hL : D₀.IsLengthSpace)
    (hV : IsOpen V) (E : C(ℂ, ℝ) → LSCMetric) (hE : ∀ F q, E F q = weylScale ξ F D₀ q)
    (hφc : ContinuousOn φ U) (hφU : MapsTo φ U V) {C : Set ℂ} (hC : IsCompact C)
    (hCU : C ⊆ U) : IsPMetricOn (confT D₀ ξ k φ C) C := by
  obtain ⟨F, hF⟩ := exists_confT_eq_pathInf k hξ hf hL hV E hE hφc hφU hC hCU
  obtain ⟨h0, hs, ht⟩ := isPMetricOn_pathInf (E F) (φ '' C)
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_, fun x hx y hy z hz => ?_⟩
  · rw [hF x hx x hx]; exact h0 _ (mem_image_of_mem φ hx)
  · rw [hF x hx y hy, hF y hy x hx]; exact hs _ (mem_image_of_mem φ hx) _ (mem_image_of_mem φ hy)
  · rw [hF x hx z hz, hF x hx y hy, hF y hy z hz]
    exact ht _ (mem_image_of_mem φ hx) _ (mem_image_of_mem φ hy) _ (mem_image_of_mem φ hz)

/-- **Lemma 1.2 for `e`**: `e(·,·;C)` is lower semicontinuous on `C × C` (sequential form) -/
theorem confT_lsc_seq (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hL : D₀.IsLengthSpace)
    (hV : IsOpen V) (E : C(ℂ, ℝ) → LSCMetric) (hE : ∀ F q, E F q = weylScale ξ F D₀ q)
    (hφc : ContinuousOn φ U) (hφU : MapsTo φ U V) {C : Set ℂ} (hC : IsCompact C)
    (hCU : C ⊆ U) (x : ℂ) (hx : x ∈ C) (y : ℂ) (hy : y ∈ C) (xs ys : ℕ → ℂ)
    (hxs : ∀ j, xs j ∈ C) (hys : ∀ j, ys j ∈ C) (hxt : Tendsto xs atTop (𝓝 x))
    (hyt : Tendsto ys atTop (𝓝 y)) (M : ℝ≥0∞) (hM : ∀ j, confT D₀ ξ k φ C (xs j) (ys j) ≤ M) :
    confT D₀ ξ k φ C x y ≤ M := by
  obtain ⟨F, hF⟩ := exists_confT_eq_pathInf k hξ hf hL hV E hE hφc hφU hC hCU
  have hK : IsCompact (φ '' C) := hC.image_of_continuousOn (hφc.mono hCU)
  have hcx : ContinuousWithinAt φ C x := (hφc.mono hCU) x hx
  have hcy : ContinuousWithinAt φ C y := (hφc.mono hCU) y hy
  rw [hF x hx y hy]
  refine pathInf_lsc_seq (E F) hK (φ x) (mem_image_of_mem φ hx) (φ y) (mem_image_of_mem φ hy)
    (fun j => φ (xs j)) (fun j => φ (ys j)) (fun j => mem_image_of_mem φ (hxs j))
    (fun j => mem_image_of_mem φ (hys j)) ?_ ?_ M (fun j => by rw [← hF _ (hxs j) _ (hys j)]; exact hM j)
  · exact hcx.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxt, Eventually.of_forall hxs⟩)
  · exact hcy.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hyt, Eventually.of_forall hys⟩)

/-- an `e`-around loop of `A_{r,2r}(z)` of `e`-length `< M` is a good loop for `e(·,·;B̄_{2r}(z))` -/
theorem isGoodLoop_of_aroundT_lt (z : ℂ) {r : ℝ} {M : ℝ≥0∞} (hM : aroundT D₀ ξ k φ U z r < M) :
    IsGoodLoop (confT D₀ ξ k φ (closedBall z (2 * r))) (closedBall z (2 * r)) z r M := by
  unfold aroundT at hM
  simp only [iInf_lt_iff] at hM
  obtain ⟨γ, s₀, s₁, ⟨hle, hγc, hγc', -⟩, hγA, hdisc, hlen⟩ := hM
  have hsub : ∀ t ∈ Icc s₀ s₁, γ t ∈ closedBall z (2 * r) := fun t ht =>
    ball_subset_closedBall (hγA t ht).1
  have hdiam : ∀ s ∈ Icc s₀ s₁, ∀ t ∈ Icc s₀ s₁, s ≤ t →
      confT D₀ ξ k φ (closedBall z (2 * r)) (γ s) (γ t) ≤ lenT D₀ ξ k φ γ s₀ s₁ := by
    intro s hs t ht hst
    have h := internalWith_le_curveLengthWith (dV D₀ ξ k) (S := SV D₀ (φ '' closedBall z (2 * r)))
      (Q := D₀.pt ∘ φ ∘ γ) hst (hγc'.mono (Icc_subset_Icc hs.1 ht.2))
      (fun u hu => ⟨γ u, hsub u ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩, rfl⟩)
    exact h.trans (HigherDimLQGMetric.curveLengthWith_mono_interval hs.1 hst ht.2)
  refine ⟨γ '' Icc s₀ s₁, ⟨γ s₀, s₀, ⟨le_rfl, hle⟩, rfl⟩, isPreconnected_Icc.image _ hγc, ?_, ?_,
    ?_, SupercriticalLQGUniqueness.B2.PfeLocal.l4_closedBall_subset_fill hdisc,
    lenT D₀ ξ k φ γ s₀ s₁, hlen, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩; exact hsub t ht
  · rintro _ ⟨t, ht, rfl⟩; exact hsub t ht
  · rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ hb
    exact (hγA t ht).2 (ball_subset_closedBall hb)
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rcases le_total s t with hst | hts
    · exact hdiam s hs t ht hst
    · have h := internalWith_le_curveLengthWith_rev (dV D₀ ξ k)
        (fun x y => HigherDimLQGMetric.weylDistOn_comm x y)
        (S := SV D₀ (φ '' closedBall z (2 * r))) (Q := D₀.pt ∘ φ ∘ γ) hts
        (hγc'.mono (Icc_subset_Icc ht.1 hs.2))
        (fun u hu => ⟨γ u, hsub u ⟨ht.1.trans hu.1, hu.2.trans hs.2⟩, rfl⟩)
      exact h.trans (HigherDimLQGMetric.curveLengthWith_mono_interval ht.1 hts hs.2)

end Props

end SupercriticalConformalCovariance.BiLip
