import SupercriticalLFPPAS.Local.OneWay
import SupercriticalLFPPAS.Local.Collar

/-!
# Lemma 3.2, deterministic implication (packet P32)

Planning audit `planning/audits/SB1-sections-1-3.md` A12, steps 4 and 6. Fix a realization:
`D` the LQG metric of `h`, `Df = D(h + f)` with `f = collarFn B` (Weyl scaling,
`Df = weylScale ξ f D`), `Y = 𝔞⁻¹ D_φ` the normalized LFPP metric of a continuous field `φ`
and `Yf = 𝔞⁻¹ D_{φ + g}` with `g = f*_δ`. On the collar events (`ofReal (M + 2)` below `e^{ξB}`
times the across distances of `D` and `e^{ξ(B−1)}` times those of `Y`) and the event of Lemma 3.1
for `(Yf, Df)`, both (3.1) and (3.2) hold (`lemma32Event_of_collars`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS.Local

local notation "Barrier.forget" => Uniqueness.BiLipschitz.Barrier.forget

theorem norm_mem_of_mem_srcV {z : ℂ} (hz : z ∈ srcV) : 1 / 2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 := hz

/-- On `V` the collar function vanishes, so Weyl scaling by it does not increase internal
distances in `V`. -/
theorem weyl_le_internal_srcV {ξ B : ℝ} {D Df : LSCMetric}
    (hforget : Continuous (Barrier.forget D))
    (hDf : ∀ p, Df p = weylScale ξ (collarFn B) D p) (u v : srcV) :
    Df ((u : ℂ), (v : ℂ)) ≤ D.internal srcV (u, v) := by
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hY => le_iInf fun ha => le_iInf fun hb => ?_
  have hzero : ∀ s ∈ Icc a b, collarFn B (P s) = 0 := by
    intro s hs
    have h := hY s hs
    exact collarFn_eq_zero B (by linarith [h.1]) (by linarith [h.2])
  rw [← ha, ← hb, ← len_weyl_eq_of_zero_on hDf hforget hP hzero]
  exact LSCMetric.apply_le_len Df P hP.1

/-- On the open neighbourhood `W` of `V` where `|g| ≤ β`, the penalized LFPP internal distances
in `V` are at most `e^{ξβ}` times the unpenalized ones. -/
theorem lfpp_penalized_le_internal_srcV {ξ β : ℝ} (hξ : 0 < ξ) (a : Set.Ioi (0 : ℝ))
    {φ g : C(ℂ, ℝ)} (hgW : ∀ z : ℂ, 9 / 20 < ‖z‖ → ‖z‖ < 7 / 2 → |g z| ≤ β) (u v : srcV) :
    B2.Median.lfppMetric ξ a (φ + g) ((u : ℂ), (v : ℂ)) ≤
      ENNReal.ofReal (Real.exp (ξ * β)) * (B2.Median.lfppMetric ξ a φ).internal srcV (u, v) := by
  set W : Set ℂ := {z | 9 / 20 < ‖z‖ ∧ ‖z‖ < 7 / 2} with hW
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hK : ∀ x ∈ W, |(φ + g) x - φ x| ≤ β := by
    intro x hx
    rw [ContinuousMap.add_apply, add_sub_cancel_left]
    exact hgW x hx.1 hx.2
  have h0 : ENNReal.ofReal (Real.exp (ξ * β)) ≠ 0 := by
    simpa using Real.exp_pos (ξ * β)
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
    le_iInf fun hY => le_iInf fun hs => le_iInf fun ht => ?_
  have hPc : ContinuousOn P (Icc s t) := ((B2.Polylog.lfppMetric_isCurve_iff ξ a φ).1 hP).2
  have hPW : ∀ r ∈ Icc s t, P r ∈ W := by
    intro r hr
    have h := hY r hr
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hlen := B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a hWo hK hPc hPW
  rw [abs_of_pos hξ] at hlen
  rw [← hs, ← ht]
  exact (LSCMetric.apply_le_len _ P hP.1).trans hlen

/-- **LFPP collar confinement**: on the LFPP collar event, curves of the penalized LFPP metric
from `{1/3 ≤ |z| ≤ 6}` of length below `M + 2` stay in `U`. -/
theorem lfpp_penalized_confined {ξ B M : ℝ} (hξ : 0 < ξ) (a : Set.Ioi (0 : ℝ)) {φ g : C(ℂ, ℝ)}
    (hgN : ∀ z : ℂ, ‖z‖ < 3 / 8 ∨ (5 < ‖z‖ ∧ ‖z‖ < 8) → B - 1 ≤ g z)
    (hcol : ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
        acrossDist (B2.Median.lfppMetric ξ a φ) collarIn ∧
      ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
        acrossDist (B2.Median.lfppMetric ξ a φ) collarOut)
    (P : ℝ → ℂ) (s t : ℝ) (hP : (B2.Median.lfppMetric ξ a (φ + g)).IsCurve P s t)
    (hs1 : 1 / 3 ≤ ‖P s‖) (hs2 : ‖P s‖ ≤ 6)
    (hlen : (B2.Median.lfppMetric ξ a (φ + g)).len P s t < ENNReal.ofReal (M + 2)) :
    ∀ r ∈ Icc s t, P r ∈ tgtU := by
  have hPc : ContinuousOn P (Icc s t) := ((B2.Polylog.lfppMetric_isCurve_iff ξ a _).1 hP).2
  have hcmp : ∀ (N : Set ℂ), IsOpen N → (∀ z ∈ N, B - 1 ≤ g z) → ∀ s' t', s ≤ s' → t' ≤ t →
      (∀ r ∈ Icc s' t', P r ∈ N) →
      ENNReal.ofReal (Real.exp (ξ * (B - 1))) * (B2.Median.lfppMetric ξ a φ).len P s' t' ≤
        (B2.Median.lfppMetric ξ a (φ + g)).len P s' t' := by
    intro N hN hgN' s' t' hs' ht' hPN
    refine lfppMetric_len_ge_of_ge_on hξ.le a hN (fun z hz => ?_)
      (hPc.mono (Icc_subset_Icc hs' ht')) hPN
    rw [ContinuousMap.add_apply]
    linarith [hgN' z hz]
  refine mem_tgtU_of_collars _ hPc ⟨hs1, hs2⟩ (ENNReal.ofReal (M + 2)) ?_ ?_ hlen
  · intro s' t' hs' hst' ht' hmem h1 h2
    have hN : IsOpen (ball (0 : ℂ) (3 / 8)) := isOpen_ball
    have hPN : ∀ r ∈ Icc s' t', P r ∈ ball (0 : ℂ) (3 / 8) := by
      intro r hr
      rw [mem_ball, dist_zero_right]
      linarith [(hmem r hr).2]
    have hc := hcmp _ hN (fun z hz => hgN z (Or.inl (by
      rwa [mem_ball, dist_zero_right] at hz))) s' t' hs' ht' hPN
    have hacr := acrossDist_collarIn_le_len (B2.Median.lfppMetric ξ a φ) hst'
      (hPc.mono (Icc_subset_Icc hs' ht')) h1 h2
    calc ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
          acrossDist (B2.Median.lfppMetric ξ a φ) collarIn := hcol.1
      _ ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
          (B2.Median.lfppMetric ξ a φ).len P s' t' := by gcongr
      _ ≤ _ := hc
  · intro s' t' hs' hst' ht' hmem h1 h2
    have hN : IsOpen {z : ℂ | 5 < ‖z‖ ∧ ‖z‖ < 8} :=
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)
    have hPN : ∀ r ∈ Icc s' t', P r ∈ {z : ℂ | 5 < ‖z‖ ∧ ‖z‖ < 8} := by
      intro r hr
      exact ⟨by linarith [(hmem r hr).1], by linarith [(hmem r hr).2]⟩
    have hc := hcmp _ hN (fun z hz => hgN z (Or.inr hz)) s' t' hs' ht' hPN
    have hacr := acrossDist_collarOut_le_len (B2.Median.lfppMetric ξ a φ) hst'
      (hPc.mono (Icc_subset_Icc hs' ht')) h1 h2
    calc ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
          acrossDist (B2.Median.lfppMetric ξ a φ) collarOut := hcol.2
      _ ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
          (B2.Median.lfppMetric ξ a φ).len P s' t' := by gcongr
      _ ≤ _ := hc

/-- **LQG collar confinement**: on the LQG collar event, curves of the Weyl-scaled metric
`D(h + f)` from `{1/3 ≤ |z| ≤ 6}` of length below `M + 2` stay in `U`. -/
theorem weyl_confined {ξ B M : ℝ} (hξ : 0 < ξ) (hB : 0 ≤ B) {D Df : LSCMetric}
    (hforget : Continuous (Barrier.forget D))
    (hDf : ∀ p, Df p = weylScale ξ (collarFn B) D p)
    (hcol : ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * B)) * acrossDist D collarIn ∧
      ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * B)) * acrossDist D collarOut)
    (P : ℝ → ℂ) (s t : ℝ) (hP : Df.IsCurve P s t) (hs1 : 1 / 3 ≤ ‖P s‖) (hs2 : ‖P s‖ ≤ 6)
    (hlen : Df.len P s t < ENNReal.ofReal (M + 2)) :
    ∀ r ∈ Icc s t, P r ∈ tgtU := by
  have hDle : ∀ p, D p ≤ Df p := fun p =>
    (le_weylScale_of_nonneg D hξ.le (collarFn_nonneg hB) p).trans (hDf p).ge
  have hPD : D.IsCurve P s t := isCurve_of_le hDle hP
  have hPc : ContinuousOn P (Icc s t) := hforget.comp_continuousOn hPD.2
  have hsub : ∀ s' t', s ≤ s' → s' ≤ t' → t' ≤ t → D.IsCurve P s' t' := fun s' t' h1 h2 h3 =>
    ⟨h2, hPD.2.mono (Icc_subset_Icc h1 h3)⟩
  refine mem_tgtU_of_collars Df hPc ⟨hs1, hs2⟩ (ENNReal.ofReal (M + 2)) ?_ ?_ hlen
  · intro s' t' hs' hst' ht' hmem h1 h2
    have hc := le_len_weyl_of_eq_on hξ.le hDf hforget (hsub s' t' hs' hst' ht') (B := B)
      (fun r hr => (collarFn_eq_of_le B (by linarith [(hmem r hr).2])).ge)
    have hacr := acrossDist_collarIn_le_len D hst' (hPc.mono (Icc_subset_Icc hs' ht')) h1 h2
    calc ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * B)) * acrossDist D collarIn :=
          hcol.1
      _ ≤ ENNReal.ofReal (Real.exp (ξ * B)) * D.len P s' t' := by gcongr
      _ ≤ _ := hc
  · intro s' t' hs' hst' ht' hmem h1 h2
    have hc := le_len_weyl_of_eq_on hξ.le hDf hforget (hsub s' t' hs' hst' ht') (B := B)
      (fun r hr => (collarFn_eq_of_ge B (by linarith [(hmem r hr).1])).ge)
    have hacr := acrossDist_collarOut_le_len D hst' (hPc.mono (Icc_subset_Icc hs' ht')) h1 h2
    calc ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * B)) * acrossDist D collarOut :=
          hcol.2
      _ ≤ ENNReal.ofReal (Real.exp (ξ * B)) * D.len P s' t' := by gcongr
      _ ≤ _ := hc

/-- **Lemma 3.2, deterministic implication.** For one realization: if `Df = D(h + f)` is the Weyl
scaling of `D` by the collar function, a length space, `D` has Euclidean-continuous curves, the
mollified collar `g = f*_δ` satisfies the heat facts, both collar events hold, and the event of
Lemma 3.1 holds for `(Yf, Df)` with height `M + 1`, radius `η` and error `ν/4`, then the event of
Lemma 3.2 holds for `(D, Y)`. -/
theorem lemma32Event_of_collars {ξ : ℝ} (hξ : 0 < ξ) {D Df : LSCMetric} (a : Set.Ioi (0 : ℝ))
    {φ g : C(ℂ, ℝ)} {B η ν M β : ℝ} (hB : 0 ≤ B) (hη1 : η ≤ 1 / 10) (hν : 0 < ν)
    (hν1 : ν ≤ 1) (hM : 0 ≤ M)
    (hforget : Continuous (Barrier.forget D))
    (hDf : ∀ p, Df p = weylScale ξ (collarFn B) D p) (hDflen : Df.IsLengthSpace)
    (hg0 : ∀ z, 0 ≤ g z)
    (hgN : ∀ z : ℂ, ‖z‖ < 3 / 8 ∨ (5 < ‖z‖ ∧ ‖z‖ < 8) → B - 1 ≤ g z)
    (hgW : ∀ z : ℂ, 9 / 20 < ‖z‖ → ‖z‖ < 7 / 2 → |g z| ≤ β)
    (hβ : (Real.exp (ξ * β) - 1) * M ≤ ν / 8)
    (hcolD : ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * B)) * acrossDist D collarIn ∧
      ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * B)) * acrossDist D collarOut)
    (hcolY : ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
        acrossDist (B2.Median.lfppMetric ξ a φ) collarIn ∧
      ENNReal.ofReal (M + 2) ≤ ENNReal.ofReal (Real.exp (ξ * (B - 1))) *
        acrossDist (B2.Median.lfppMetric ξ a φ) collarOut)
    (hnear1 : NearCompare (B2.Median.lfppMetric ξ a (φ + g)) Df endpointPairs (M + 1) η (ν / 4))
    (hnear2 : NearCompare Df (B2.Median.lfppMetric ξ a (φ + g)) endpointPairs (M + 1) η (ν / 4)) :
    Lemma32Event D (B2.Median.lfppMetric ξ a φ) η ν M := by
  have hDle : ∀ p, D p ≤ Df p := fun p =>
    (le_weylScale_of_nonneg D hξ.le (collarFn_nonneg hB) p).trans (hDf p).ge
  have hYle : ∀ p, B2.Median.lfppMetric ξ a φ p ≤ B2.Median.lfppMetric ξ a (φ + g) p :=
    fun p => lfppMetric_le_of_le hξ.le a (fun z => by
      rw [ContinuousMap.add_apply]
      linarith [hg0 z]) p
  refine ⟨?_, ?_⟩
  · -- (3.1): source `D`, target `Y`
    refine oneWayCompare_of_penalized (Sf := Df) (Tf := B2.Median.lfppMetric ξ a (φ + g))
      hη1 hν hν1 hM ?_ hnear1 (lfppMetric_isLengthSpace ξ a _) ?_ hYle
    · intro u v _ _ _
      exact (weyl_le_internal_srcV hforget hDf u v).trans le_self_add
    · intro P s t hP hs1 hs2 hlen
      exact lfpp_penalized_confined hξ a hgN hcolY P s t hP hs1 hs2 hlen
  · -- (3.2): source `Y`, target `D`
    refine oneWayCompare_of_penalized (Sf := B2.Median.lfppMetric ξ a (φ + g)) (Tf := Df)
      hη1 hν hν1 hM ?_ hnear2 hDflen ?_ hDle
    · intro u v _ _ hSM
      set s := (B2.Median.lfppMetric ξ a φ).internal srcV (u, v)
      have h1 := lfpp_penalized_le_internal_srcV (φ := φ) hξ a hgW u v
      have he : 1 ≤ Real.exp (ξ * β) := by
        have hβ0 : 0 ≤ β := le_trans (abs_nonneg _) (hgW 1 (by norm_num) (by norm_num))
        exact Real.one_le_exp (mul_nonneg hξ.le hβ0)
      have hsplit : ENNReal.ofReal (Real.exp (ξ * β)) =
          1 + ENNReal.ofReal (Real.exp (ξ * β) - 1) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
        congr 1
        ring
      calc B2.Median.lfppMetric ξ a (φ + g) ((u : ℂ), (v : ℂ))
          ≤ ENNReal.ofReal (Real.exp (ξ * β)) * s := h1
        _ = s + ENNReal.ofReal (Real.exp (ξ * β) - 1) * s := by
            rw [hsplit, add_mul, one_mul]
        _ ≤ s + ENNReal.ofReal (Real.exp (ξ * β) - 1) * ENNReal.ofReal M := by gcongr
        _ = s + ENNReal.ofReal ((Real.exp (ξ * β) - 1) * M) := by
            rw [ENNReal.ofReal_mul (by linarith)]
        _ ≤ s + ENNReal.ofReal (ν / 8) := by gcongr
    · intro P s t hP hs1 hs2 hlen
      exact weyl_confined hξ hB hforget hDf hcolD P s t hP hs1 hs2 hlen

end SupercriticalLFPPAS.Local
