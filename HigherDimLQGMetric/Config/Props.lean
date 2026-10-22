import HigherDimLQGMetric.Config.Coordinate
import HigherDimLQGMetric.Coord.LimitTopology
import HigherDimLQGMetric.Metric.WeylBridge

/-!
# Coordinate properties of compact configuration families

The original configurations retain a uniform lower modulus inside `B(β)`.
For a limit configuration, MA1 Lemma 2.2′ transfers the coordinate topology
and the same modulus to the limit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Filter Topology BoundedContinuousFunction unitInterval
open scoped ENNReal
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem configCompactFamily_exists_seq (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) :
    ∃ F : ℕ → ConfigC d,
      (∀ n, F n ∈ configOriginal hd c C ∩ configBoundSet β) ∧
      Tendsto F atTop (𝓝 q) := by
  exact mem_closure_iff_seq_limit.mp hq

theorem configCompactFamily_outer_P1 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) :
    IsCoordinate q.1 ∧
      ∀ L : Set (configOuter d), IsCompact L → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ u ∈ L, ∀ v ∈ L, q.1 (u, v) < δ → dist u v < ε := by
  obtain ⟨F, hF, hlim⟩ := configCompactFamily_exists_seq hd c C β hq
  have hlen (n : ℕ) : IsLengthCoordinate (F n).1 :=
    configOriginal_outer_length hd c C (hF n).1
  have hconv : TendstoLocallyUniformly (fun n => ⇑(F n).1) (⇑q.1) atTop := by
    apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
    exact (continuous_fst.tendsto q).comp hlim
  have hmod : ∀ L : Set (configOuter d), IsCompact L → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
        (F n).1 (u, v) < δ → dist u v < ε := by
    exact configBoundOne_uniformLower (configOuterExhaust d) β.outer
      (fun n => (F n).1) (fun n => (hF n).2.1)
  have h := lemma22i (fun n => ⇑(F n).1) (⇑q.1) hlen hconv hmod
  refine ⟨h.1, fun L hL ε hε => ?_⟩
  obtain ⟨δ, hδ, -, hlimmod⟩ := h.2 L hL ε hε
  exact ⟨δ, hδ, hlimmod⟩

/-- Generic projection form of (P1); its inputs are checked below for each of
the four coordinate projections. -/
theorem configCompactFamily_project_P1 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (K : CompactExhaustion X) (βX : ConfigBoundDatum X)
    (π : ConfigC d → C(X × X, ℝ)) (hπ : Continuous π)
    (hOrig : ∀ q ∈ configOriginal hd c C, IsLengthCoordinate (π q))
    (hBound : ∀ q ∈ configBoundSet β, π q ∈ configBoundOne K βX)
    {q : ConfigC d} (hq : q ∈ configCompactFamily hd c C β) :
    IsCoordinate (π q) ∧
      ∀ L : Set X, IsCompact L → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ u ∈ L, ∀ v ∈ L, π q (u, v) < δ → dist u v < ε := by
  obtain ⟨F, hF, hlim⟩ := configCompactFamily_exists_seq hd c C β hq
  have hlen (n : ℕ) : IsLengthCoordinate (π (F n)) := hOrig (F n) (hF n).1
  have hconv : TendstoLocallyUniformly (fun n => ⇑(π (F n))) (⇑(π q)) atTop := by
    apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
    exact (hπ.tendsto q).comp hlim
  have hmod : ∀ L : Set X, IsCompact L → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
        π (F n) (u, v) < δ → dist u v < ε :=
    configBoundOne_uniformLower K βX (fun n => π (F n))
      (fun n => hBound (F n) (hF n).2)
  have h := lemma22i (fun n => ⇑(π (F n))) (⇑(π q)) hlen hconv hmod
  refine ⟨h.1, fun L hL ε hε => ?_⟩
  obtain ⟨δ, hδ, -, hlimmod⟩ := h.2 L hL ε hε
  exact ⟨δ, hδ, hlimmod⟩

theorem configCompactFamily_outer_tilde_P1 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) :
    IsCoordinate q.2.1 ∧
      ∀ L : Set (configOuter d), IsCompact L → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ u ∈ L, ∀ v ∈ L, q.2.1 (u, v) < δ → dist u v < ε := by
  exact configCompactFamily_project_P1 hd c C β (configOuterExhaust d) β.outer
    (fun p => p.2.1) (continuous_fst.comp continuous_snd)
    (fun p hp => configOriginal_outer_tilde_length hd c C hp)
    (fun p hp => hp.2.1) hq

theorem configCompactFamily_inner_P1 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) :
    IsCoordinate q.2.2.1 ∧
      ∀ L : Set (configInner d), IsCompact L → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ u ∈ L, ∀ v ∈ L, q.2.2.1 (u, v) < δ → dist u v < ε := by
  exact configCompactFamily_project_P1 hd c C β (configInnerExhaust d) β.inner
    (fun p => p.2.2.1) (continuous_fst.comp (continuous_snd.comp continuous_snd))
    (fun p hp => configOriginal_inner_length hd c C hp)
    (fun p hp => hp.2.2.1) hq

theorem configCompactFamily_inner_tilde_P1 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {q : ConfigC d}
    (hq : q ∈ configCompactFamily hd c C β) :
    IsCoordinate q.2.2.2 ∧
      ∀ L : Set (configInner d), IsCompact L → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ u ∈ L, ∀ v ∈ L, q.2.2.2 (u, v) < δ → dist u v < ε := by
  exact configCompactFamily_project_P1 hd c C β (configInnerExhaust d) β.inner
    (fun p => p.2.2.2) (continuous_snd.comp (continuous_snd.comp continuous_snd))
    (fun p hp => configOriginal_inner_tilde_length hd c C hp)
    (fun p hp => hp.2.2.2) hq

/-- (P2), uniformly over the whole compact family. The separation premise is
the concrete collar condition used by M2a's Lemma 2.3′. -/
theorem configCompactFamily_project_P2 (hd : 2 ≤ d) (c C : ℝ)
    (β : ConfigBounds d) {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    (E : CompactExhaustion X) (βX : ConfigBoundDatum X)
    (π : ConfigC d → C(X × X, ℝ)) (hπ : Continuous π)
    (hOrig : ∀ q ∈ configOriginal hd c C, IsLengthCoordinate (π q))
    (hBound : ∀ q ∈ configBoundSet β, π q ∈ configBoundOne E βX)
    {K O : Set X} (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (η : ℝ) (hη : 0 < η)
    (hsep : ∀ x ∈ K, ∀ z ∈ frontier O, η ≤ dist x z) :
    ∃ a : ℝ, 0 < a ∧ ∀ q ∈ configCompactFamily hd c C β,
      ∀ x ∈ K, ∀ y ∈ K, π q (x, y) < a / 4 →
        ∃ Q : unitInterval →ᵇ X, (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (π q (u, v)))
            (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (π q (x, y)) := by
  obtain ⟨m, hm⟩ := E.exists_superset_of_isCompact hOc
  refine ⟨βX.lower m η, βX.lower_pos m η hη, ?_⟩
  intro q hq x hx y hy hxy
  obtain ⟨F, hF, hlim⟩ := configCompactFamily_exists_seq hd c C β hq
  have hlen (n : ℕ) : IsLengthCoordinate (π (F n)) := hOrig (F n) (hF n).1
  have hconv : TendstoLocallyUniformly (fun n => ⇑(π (F n))) (⇑(π q)) atTop := by
    apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp
    exact (hπ.tendsto q).comp hlim
  have hmod : ∀ L : Set X, IsCompact L → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∀ u ∈ L, ∀ v ∈ L,
        π (F n) (u, v) < δ → dist u v < ε :=
    configBoundOne_uniformLower E βX (fun n => π (F n))
      (fun n => hBound (F n) (hF n).2)
  have hlower : ∀ n, ∀ u ∈ closure O, ∀ v ∈ closure O,
      βX.lower m (dist u v) ≤ π (F n) (u, v) := by
    intro n u hu v hv
    exact (hBound (F n) (hF n).2).1 m (u, v) (hm hu) (hm hv) |>.1
  exact (lemma23 (fun n => ⇑(π (F n))) (⇑(π q)) hlen hconv hmod
    hKO hO hOc (βX.lower m) (βX.lower_mono m) (βX.lower_pos m)
    hlower η hη hsep).2 x hx y hy hxy

theorem configCompactFamily_outer_P2 (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d)
    {K O : Set (configOuter d)} (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (η : ℝ) (hη : 0 < η)
    (hsep : ∀ x ∈ K, ∀ z ∈ frontier O, η ≤ dist x z) :
    ∃ a : ℝ, 0 < a ∧ ∀ q ∈ configCompactFamily hd c C β,
      ∀ x ∈ K, ∀ y ∈ K, q.1 (x, y) < a / 4 →
        ∃ Q : unitInterval →ᵇ configOuter d,
          (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (q.1 (u, v)))
            (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (q.1 (x, y)) :=
  configCompactFamily_project_P2 hd c C β (configOuterExhaust d) β.outer
    (fun q => q.1) continuous_fst
    (fun _ hq => configOriginal_outer_length hd c C hq)
    (fun _ hq => hq.1) hKO hO hOc η hη hsep

theorem configCompactFamily_outer_tilde_P2 (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d)
    {K O : Set (configOuter d)} (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (η : ℝ) (hη : 0 < η)
    (hsep : ∀ x ∈ K, ∀ z ∈ frontier O, η ≤ dist x z) :
    ∃ a : ℝ, 0 < a ∧ ∀ q ∈ configCompactFamily hd c C β,
      ∀ x ∈ K, ∀ y ∈ K, q.2.1 (x, y) < a / 4 →
        ∃ Q : unitInterval →ᵇ configOuter d,
          (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (q.2.1 (u, v)))
            (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (q.2.1 (x, y)) :=
  configCompactFamily_project_P2 hd c C β (configOuterExhaust d) β.outer
    (fun q => q.2.1) (continuous_fst.comp continuous_snd)
    (fun _ hq => configOriginal_outer_tilde_length hd c C hq)
    (fun _ hq => hq.2.1) hKO hO hOc η hη hsep

theorem configCompactFamily_inner_P2 (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d)
    {K O : Set (configInner d)} (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (η : ℝ) (hη : 0 < η)
    (hsep : ∀ x ∈ K, ∀ z ∈ frontier O, η ≤ dist x z) :
    ∃ a : ℝ, 0 < a ∧ ∀ q ∈ configCompactFamily hd c C β,
      ∀ x ∈ K, ∀ y ∈ K, q.2.2.1 (x, y) < a / 4 →
        ∃ Q : unitInterval →ᵇ configInner d,
          (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (q.2.2.1 (u, v)))
            (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (q.2.2.1 (x, y)) :=
  configCompactFamily_project_P2 hd c C β (configInnerExhaust d) β.inner
    (fun q => q.2.2.1) (continuous_fst.comp (continuous_snd.comp continuous_snd))
    (fun _ hq => configOriginal_inner_length hd c C hq)
    (fun _ hq => hq.2.2.1) hKO hO hOc η hη hsep

theorem configCompactFamily_inner_tilde_P2 (hd : 2 ≤ d) (c C : ℝ) (β : ConfigBounds d)
    {K O : Set (configInner d)} (hKO : K ⊆ O) (hO : IsOpen O)
    (hOc : IsCompact (closure O)) (η : ℝ) (hη : 0 < η)
    (hsep : ∀ x ∈ K, ∀ z ∈ frontier O, η ≤ dist x z) :
    ∃ a : ℝ, 0 < a ∧ ∀ q ∈ configCompactFamily hd c C β,
      ∀ x ∈ K, ∀ y ∈ K, q.2.2.2 (x, y) < a / 4 →
        ∃ Q : unitInterval →ᵇ configInner d,
          (∀ t, Q t ∈ closure O) ∧ Q 0 = x ∧ Q 1 = y ∧
          curveLengthWith (fun u v => ENNReal.ofReal (q.2.2.2 (u, v)))
            (Set.IccExtend zero_le_one Q) 0 1 = ENNReal.ofReal (q.2.2.2 (x, y)) :=
  configCompactFamily_project_P2 hd c C β (configInnerExhaust d) β.inner
    (fun q => q.2.2.2) (continuous_snd.comp (continuous_snd.comp continuous_snd))
    (fun _ hq => configOriginal_inner_tilde_length hd c C hq)
    (fun _ hq => hq.2.2.2) hKO hO hOc η hη hsep

/-- Pointwise comparison passes from ambient metrics to finite annular
internal coordinates. -/
theorem config_internalC_compare (D Dt : ContMetric d) (hD : D.IsLength)
    (hDt : Dt.IsLength) {U : Set (Rd d)} (hU : IsOpen U)
    (hUc : IsPreconnected U) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hcmp : ∀ x y : Rd d, c * D.1 (x, y) ≤ Dt.1 (x, y) ∧
      Dt.1 (x, y) ≤ C * D.1 (x, y)) (u v : U) :
    c * internalC D hD hU hUc (u, v) ≤ internalC Dt hDt hU hUc (u, v) ∧
      internalC Dt hDt hU hUc (u, v) ≤ C * internalC D hD hU hUc (u, v) := by
  have hDfin := D.internal_ne_top_of_isPreconnected hD hU hUc u.2 v.2
  have hDtfin := Dt.internal_ne_top_of_isPreconnected hDt hU hUc u.2 v.2
  have hlo := D.mul_internal_le_of_le (fun x y => (hcmp x y).1) U u.1 v.1
  have hhi := ContMetric.internal_le_mul_of_le (D := D) (E := Dt)
    hC (fun x y => (hcmp x y).2) U u.1 v.1
  constructor
  · have h := ENNReal.toReal_mono hDtfin hlo
    change c * (D.internal U u.1 v.1).toReal ≤ (Dt.internal U u.1 v.1).toReal
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using h
  · have htop : ENNReal.ofReal C * D.internal U u.1 v.1 ≠ ∞ := by finiteness
    have h := ENNReal.toReal_mono htop hhi
    change (Dt.internal U u.1 v.1).toReal ≤ C * (D.internal U u.1 v.1).toReal
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le] using h

theorem configOriginal_P3 (hd : 2 ≤ d) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    {q : ConfigC d} (hq : q ∈ configOriginal hd c C) :
    (∀ u v : configOuter d,
      c * q.1 (u, v) ≤ q.2.1 (u, v) ∧
      q.2.1 (u, v) ≤ C * q.1 (u, v)) ∧
    (∀ u v : configInner d,
      c * q.2.2.1 (u, v) ≤ q.2.2.2 (u, v) ∧
      q.2.2.2 (u, v) ≤ C * q.2.2.1 (u, v)) := by
  obtain ⟨D, Dt, hD, hDt, hcmp, rfl⟩ := hq
  constructor
  · intro u v
    simpa only [configC, configScaledMetric_one] using
      (config_internalC_compare D Dt hD hDt configOuter_isOpen
        (configOuter_isPreconnected hd) hc hC hcmp u v)
  · intro u v
    simpa only [configC, configScaledMetric_one] using
      (config_internalC_compare D Dt hD hDt configInner_isOpen
        (configInner_isPreconnected hd) hc hC hcmp u v)

theorem configCompactFamily_P3 (hd : 2 ≤ d) {c C : ℝ}
    (hc : 0 < c) (hC : 0 < C) (β : ConfigBounds d)
    {q : ConfigC d} (hq : q ∈ configCompactFamily hd c C β) :
    (∀ u v : configOuter d,
      c * q.1 (u, v) ≤ q.2.1 (u, v) ∧
      q.2.1 (u, v) ≤ C * q.1 (u, v)) ∧
    (∀ u v : configInner d,
      c * q.2.2.1 (u, v) ≤ q.2.2.2 (u, v) ∧
      q.2.2.2 (u, v) ≤ C * q.2.2.1 (u, v)) := by
  obtain ⟨F, hF, hlim⟩ := configCompactFamily_exists_seq hd c C β hq
  have hPn (n : ℕ) := configOriginal_P3 hd hc hC (hF n).1
  constructor
  · intro u v
    have hDval : Continuous (fun p : ConfigC d => p.1 (u, v)) :=
      (continuous_eval_const (u, v)).comp continuous_fst
    have hTval : Continuous (fun p : ConfigC d => p.2.1 (u, v)) :=
      (continuous_eval_const (u, v)).comp (continuous_fst.comp continuous_snd)
    have hDt := (hDval.tendsto q).comp hlim
    have hTt := (hTval.tendsto q).comp hlim
    constructor
    · exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.mul hDt) hTt
        (fun n => (hPn n).1 u v |>.1)
    · exact le_of_tendsto_of_tendsto' hTt (tendsto_const_nhds.mul hDt)
        (fun n => (hPn n).1 u v |>.2)
  · intro u v
    have hDval : Continuous (fun p : ConfigC d => p.2.2.1 (u, v)) :=
      (continuous_eval_const (u, v)).comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))
    have hTval : Continuous (fun p : ConfigC d => p.2.2.2 (u, v)) :=
      (continuous_eval_const (u, v)).comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))
    have hDt := (hDval.tendsto q).comp hlim
    have hTt := (hTval.tendsto q).comp hlim
    constructor
    · exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.mul hDt) hTt
        (fun n => (hPn n).2 u v |>.1)
    · exact le_of_tendsto_of_tendsto' hTt (tendsto_const_nhds.mul hDt)
        (fun n => (hPn n).2 u v |>.2)

end HigherDimLQGMetric
