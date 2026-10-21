import SmallGammaGeodesics.CC.Zoom26
import LQGMetric.Metric.InternalC
import LQGMetric.Meas.Internal

/-!
# [3] Prop 2.1: deterministic tools (track CC, packet CC6b; CC0 Details D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10** (Gwynne–Miller,
arXiv:1905.00384, Prop 2.1), the "localization" step of CC6a's recipe
(`planning/handoffs/CC6a.md`, Details §2).

* `ContMetric.internal_eq_of_le_frontier` (**internal localization**): for `A` open with
  `closure A ⊆ B ⊆ U` and `y ∈ A`, if `X(y, y'; B) ≤ X(y, w; B)` for every `w ∈ ∂A`, then
  `X(y, y'; U) = X(y, y'; B)`. A path from `y` to `y'` in `U` either stays in `A ⊆ B`, or its
  initial segment up to the first exit from `A` is a path in `closure A ⊆ B` ending on `∂A`. The
  condition only involves the internal metric on `B`, which is what can be transferred between
  probability spaces (it is a local functional of the field).
* `exists_mem_of_continuousOn_of_dense`: a continuous map takes a value in an open set at a point
  of a dense subset as soon as it does so at some point.
* `LocBad` / `LocBadQ`: the **localized bad event** of D10 in zoomed coordinates, as a predicate on
  three functions (the global metric `dg`, an internal metric `dl`, the transported metric `n`),
  and its version on countable dense sets of witnesses (`locBadQ_of_locBad`,
  `locBad_of_locBadQ`). The negation `not_locBad_iff` is the conjunction used in the assembly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.MetricGeometry

/-! ## 1. Internal localization -/

/-- **Internal localization** (deterministic): let `A` be open with `closure A ⊆ B ⊆ U` and
`y ∈ A`. If `X(y, y'; B) ≤ X(y, w; B)` for every `w ∈ ∂A`, then `X(y, y'; U) = X(y, y'; B)`. -/
theorem ContMetric.internal_eq_of_le_frontier (X : ContMetric) {U B A : Set ℂ} (hBU : B ⊆ U)
    (hA : IsOpen A) (hAB : closure A ⊆ B) {y y' : ℂ} (hy : y ∈ A)
    (hle : ∀ w ∈ frontier A, X.internal B y y' ≤ X.internal B y w) :
    X.internal U y y' = X.internal B y y' := by
  refine le_antisymm (internalEDist_anti (image_mono hBU) _ _) ?_
  show X.internal B y y' ≤ internalEDist (X.pt '' U) (X.pt y) (X.pt y')
  refine le_iInf fun γ => ?_
  have hAB' : A ⊆ B := subset_closure.trans hAB
  by_cases hall : ∀ t, γ.1 t ∈ X.pt '' A
  · exact internalEDist_le_pathLength γ.1 fun t => image_mono hAB' (hall t)
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  set P : ℝ → X.Space := ⇑γ.1.extend with hPdef
  have hPc : Continuous P := γ.1.continuous_extend
  have hAc : IsClosed (X.pt '' A)ᶜ := (X.isOpen_image_pt hA).isClosed_compl
  obtain ⟨s, hs, hsA, hbefore⟩ := exists_first_hit hPc.continuousOn hAc
    ⟨t, t.2, by rw [hPdef, Path.extend_extends']; exact ht⟩
  have hP0 : P 0 = X.pt y := Path.extend_zero γ.1
  have hs0 : 0 < s := by
    rcases hs.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hP0] at hsA
      exact hsA ⟨y, hy, rfl⟩
    · exact h
  have hin : ∀ r ∈ Ico 0 s, P r ∈ X.pt '' A := fun r hr => not_not.1 (hbefore r hr)
  have hne : (𝓝[Ico 0 s] s).NeBot := right_nhdsWithin_Ico_neBot hs0
  -- the exit point lies on `∂A` and the initial segment in `closure A`
  have hcl : X.unpt (P s) ∈ closure A := mem_closure_of_tendsto
    (((X.continuous_unpt.comp hPc).tendsto s).mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun r hr => X.mem_image_pt.1 (by
      simpa only [Function.comp_apply, ContMetric.pt_unpt] using hin r hr))
  have hfr : X.unpt (P s) ∈ frontier A := by
    refine ⟨hcl, ?_⟩
    rw [hA.interior_eq]
    intro h
    exact hsA (by simpa only [ContMetric.pt_unpt] using X.mem_image_pt.2 h)
  have hmaps : MapsTo P (Icc 0 s) (X.pt '' B) := fun r hr => by
    rcases hr.2.lt_or_eq with h | h
    · exact image_mono hAB' (hin r ⟨hr.1, h⟩)
    · rw [h]
      exact ⟨X.unpt (P s), hAB hcl, ContMetric.pt_unpt X _⟩
  have h1 := internalEDist_le_curveLength hs.1 hPc.continuousOn hmaps
  rw [hP0] at h1
  calc X.internal B y y' ≤ X.internal B y (X.unpt (P s)) := hle _ hfr
    _ = internalEDist (X.pt '' B) (X.pt y) (P s) := by
        unfold ContMetric.internal
        rw [ContMetric.pt_unpt]
    _ ≤ curveLength P 0 s := h1
    _ ≤ pathLength γ.1 := curveLength_mono P le_rfl hs.2

/-! ## 2. Dense witnesses -/

/-- If `F` is continuous on `S`, `Q ⊆ S` is dense in `S` and `F x ∈ O` (open) for some `x ∈ S`,
then `F q ∈ O` for some `q ∈ Q`. -/
theorem exists_mem_of_continuousOn_of_dense {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {S Q : Set α} {F : α → β} {O : Set β} (hF : ContinuousOn F S)
    (hO : IsOpen O) (hQS : Q ⊆ S) (hSQ : S ⊆ closure Q) {x : α} (hx : x ∈ S) (hFx : F x ∈ O) :
    ∃ q ∈ Q, F q ∈ O := by
  obtain ⟨U, hU, hUeq⟩ := continuousOn_iff'.1 hF O hO
  have hxU : x ∈ U := by
    have : x ∈ F ⁻¹' O ∩ S := ⟨hFx, hx⟩
    rw [hUeq] at this
    exact this.1
  obtain ⟨q, hqU, hqQ⟩ := mem_closure_iff.1 (hSQ hx) U hU hxU
  have hq : q ∈ U ∩ S := ⟨hqU, hQS hqQ⟩
  rw [← hUeq] at hq
  exact ⟨q, hqQ, hq.1⟩

/-- A set in `ℂ` has a countable dense subset. -/
theorem exists_countable_dense_subset_complex (S : Set ℂ) :
    ∃ Q : Set ℂ, Q ⊆ S ∧ Q.Countable ∧ S ⊆ closure Q :=
  ((TopologicalSpace.isSeparable_univ_iff.2 inferInstance).mono
    (subset_univ S)).exists_countable_dense_subset

/-! ## 3. The localized bad event -/

/-- **The localized bad event of D10** in zoomed coordinates, for the global metric `dg`, an
internal metric `dl` and the transported metric `n`: for some `u, v` in the unit disc, either the
global metric is not realized by `dl` (`dg < dl`), or the transported distance `n(u, v)` exceeds
the distance from `u` to some point of `T`, or `n` and `dl` differ by more than `δ`. -/
def LocBad (δ : ℝ) (T : Set ℂ) (dg dl n : ℂ → ℂ → ℝ≥0∞) : Prop :=
  ∃ u ∈ ball (0 : ℂ) 1, ∃ v ∈ ball (0 : ℂ) 1, dg u v < dl u v ∨ (∃ w ∈ T, n u w < n u v) ∨
    dl u v + ENNReal.ofReal δ < n u v ∨ n u v + ENNReal.ofReal δ < dl u v

/-- The same event with witnesses `u, v ∈ Q₁` and `w ∈ Q₂`. -/
def LocBadQ (δ : ℝ) (Q₁ Q₂ : Set ℂ) (dg dl n : ℂ → ℂ → ℝ≥0∞) : Prop :=
  ∃ u ∈ Q₁, ∃ v ∈ Q₁, dg u v < dl u v ∨ (∃ w ∈ Q₂, n u w < n u v) ∨
    dl u v + ENNReal.ofReal δ < n u v ∨ n u v + ENNReal.ofReal δ < dl u v

/-- The negation of the localized bad event. -/
theorem not_locBad_iff {δ : ℝ} {T : Set ℂ} {dg dl n : ℂ → ℂ → ℝ≥0∞} :
    ¬ LocBad δ T dg dl n ↔ ∀ u ∈ ball (0 : ℂ) 1, ∀ v ∈ ball (0 : ℂ) 1, dl u v ≤ dg u v ∧
      (∀ w ∈ T, n u v ≤ n u w) ∧ n u v ≤ dl u v + ENNReal.ofReal δ ∧
        dl u v ≤ n u v + ENNReal.ofReal δ := by
  unfold LocBad
  push Not
  rfl

/-- Dense witnesses suffice for continuous data. -/
theorem locBad_of_locBadQ {δ : ℝ} {T Q₁ Q₂ : Set ℂ} {dg dl n : ℂ → ℂ → ℝ≥0∞}
    (hQ₁ : Q₁ ⊆ ball (0 : ℂ) 1) (hQ₂ : Q₂ ⊆ T) (h : LocBadQ δ Q₁ Q₂ dg dl n) :
    LocBad δ T dg dl n := by
  obtain ⟨u, hu, v, hv, h⟩ := h
  refine ⟨u, hQ₁ hu, v, hQ₁ hv, ?_⟩
  rcases h with h | ⟨w, hw, h⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨w, hQ₂ hw, h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The witnesses of `LocBad` can be taken in countable dense subsets, if `dg`, `dl` are
continuous on the unit bidisc and `n` is continuous on `S × S` with `B_1 ∪ T ⊆ S`. -/
theorem locBadQ_of_locBad {δ : ℝ} {T Q₁ Q₂ S : Set ℂ} {dg dl n : ℂ → ℂ → ℝ≥0∞}
    (hQ₁ : Q₁ ⊆ ball (0 : ℂ) 1) (hQ₁d : ball (0 : ℂ) 1 ⊆ closure Q₁) (hQ₂ : Q₂ ⊆ T)
    (hQ₂d : T ⊆ closure Q₂) (hBS : ball (0 : ℂ) 1 ⊆ S) (hTS : T ⊆ S)
    (hdg : ContinuousOn (fun p : ℂ × ℂ => dg p.1 p.2) (ball 0 1 ×ˢ ball 0 1))
    (hdl : ContinuousOn (fun p : ℂ × ℂ => dl p.1 p.2) (ball 0 1 ×ˢ ball 0 1))
    (hn : ContinuousOn (fun p : ℂ × ℂ => n p.1 p.2) (S ×ˢ S)) (h : LocBad δ T dg dl n) :
    LocBadQ δ Q₁ Q₂ dg dl n := by
  obtain ⟨u, hu, v, hv, h⟩ := h
  have hB2 : ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1 ⊆ closure (Q₁ ×ˢ Q₁) := by
    rw [closure_prod_eq]
    exact prod_mono hQ₁d hQ₁d
  have hQQ : Q₁ ×ˢ Q₁ ⊆ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1 := prod_mono hQ₁ hQ₁
  have huv : (u, v) ∈ ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1 := ⟨hu, hv⟩
  have hnB : ContinuousOn (fun p : ℂ × ℂ => n p.1 p.2) (ball 0 1 ×ˢ ball 0 1) :=
    hn.mono (prod_mono hBS hBS)
  have hlt : IsOpen {q : ℝ≥0∞ × ℝ≥0∞ | q.1 < q.2} := isOpen_lt continuous_fst continuous_snd
  rcases h with h | ⟨w, hw, h⟩ | h | h
  · obtain ⟨q, hq, hq'⟩ := exists_mem_of_continuousOn_of_dense (hdg.prodMk hdl) hlt hQQ hB2 huv h
    exact ⟨q.1, hq.1, q.2, hq.2, Or.inl hq'⟩
  · -- the map `(u, v, w) ↦ (n u w, n u v)` on `B_1 × B_1 × T`
    set S3 : Set (ℂ × ℂ × ℂ) := ball (0 : ℂ) 1 ×ˢ ball (0 : ℂ) 1 ×ˢ T with hS3
    have hF : ContinuousOn (fun p : ℂ × ℂ × ℂ => (n p.1 p.2.2, n p.1 p.2.1)) S3 := by
      refine ContinuousOn.prodMk ?_ ?_
      · exact hn.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
          fun p hp => ⟨hBS hp.1, hTS hp.2.2⟩
      · exact hn.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
          fun p hp => ⟨hBS hp.1, hBS hp.2.1⟩
    have hd3 : S3 ⊆ closure (Q₁ ×ˢ Q₁ ×ˢ Q₂) := by
      rw [closure_prod_eq, closure_prod_eq]
      exact prod_mono hQ₁d (prod_mono hQ₁d hQ₂d)
    obtain ⟨q, hq, hq'⟩ := exists_mem_of_continuousOn_of_dense hF hlt
      (prod_mono hQ₁ (prod_mono hQ₁ hQ₂)) hd3 (⟨hu, hv, hw⟩ : (u, v, w) ∈ S3) h
    exact ⟨q.1, hq.1, q.2.1, hq.2.1, Or.inr (Or.inl ⟨q.2.2, hq.2.2, hq'⟩)⟩
  · have hF : ContinuousOn (fun p : ℂ × ℂ => (dl p.1 p.2 + ENNReal.ofReal δ, n p.1 p.2))
        (ball 0 1 ×ˢ ball 0 1) := (hdl.add continuousOn_const).prodMk hnB
    obtain ⟨q, hq, hq'⟩ := exists_mem_of_continuousOn_of_dense hF hlt hQQ hB2 huv h
    exact ⟨q.1, hq.1, q.2, hq.2, Or.inr (Or.inr (Or.inl hq'))⟩
  · have hF : ContinuousOn (fun p : ℂ × ℂ => (n p.1 p.2 + ENNReal.ofReal δ, dl p.1 p.2))
        (ball 0 1 ×ˢ ball 0 1) := (hnB.add continuousOn_const).prodMk hdl
    obtain ⟨q, hq, hq'⟩ := exists_mem_of_continuousOn_of_dense hF hlt hQQ hB2 huv h
    exact ⟨q.1, hq.1, q.2, hq.2, Or.inr (Or.inr (Or.inr hq'))⟩

/-- `LocBadQ` only reads the functions at the witnesses. -/
theorem LocBadQ.congr {δ : ℝ} {Q₁ Q₂ : Set ℂ} {dg dl n dg' dl' n' : ℂ → ℂ → ℝ≥0∞}
    (h : LocBadQ δ Q₁ Q₂ dg dl n) (hg : ∀ u ∈ Q₁, ∀ v ∈ Q₁, dg u v = dg' u v)
    (hl : ∀ u ∈ Q₁, ∀ v ∈ Q₁, dl u v = dl' u v)
    (hn : ∀ u ∈ Q₁, ∀ v ∈ Q₁ ∪ Q₂, n u v = n' u v) : LocBadQ δ Q₁ Q₂ dg' dl' n' := by
  obtain ⟨u, hu, v, hv, h⟩ := h
  refine ⟨u, hu, v, hv, ?_⟩
  rw [← hg u hu v hv, ← hl u hu v hv, ← hn u hu v (Or.inl hv)]
  rcases h with h | ⟨w, hw, h⟩ | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨w, hw, by rw [← hn u hu w (Or.inr hw)]; exact h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end SmallGammaGeodesics.CC
