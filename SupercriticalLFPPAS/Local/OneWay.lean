import SupercriticalLFPPAS.Local.NearCompare
import SupercriticalLFPPAS.Local.MetricTools

/-!
# The deterministic core of Lemma 3.2: one direction (packet P32)

Planning audit `planning/audits/SB1-sections-1-3.md` A12, step 6. Both (3.1) and (3.2) are
instances of `oneWayCompare_of_penalized`: a source metric `S` and a target metric `T`, their
penalized versions `Sf`, `Tf` (the metrics of the field plus the collar function), such that

* the penalization does not increase source internal distances in `V` by more than `ν/8`;
* Lemma 3.1's inequality holds for `(Tf, Sf)` on the endpoint pairs with height `M + 1`, radius
  `η` and error `ν/4`;
* `Tf` is a length space, its short curves from `{1/3 ≤ |z| ≤ 6}` stay in `U` (collars), and
  `T ≤ Tf`.

Then `T(B_η(u), B_η(v); U) ≤ S(u, v; V) + ν` whenever `S(u, v; V) ≤ M`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints (movingOpenSetDist)

namespace SupercriticalLFPPAS.Local

/-- The endpoint pairs of Lemma 3.2: `|u| = 1`, `|v| = 2`. -/
def endpointPairs : Set (ℂ × ℂ) := {p | ‖p.1‖ = 1 ∧ ‖p.2‖ = 2}

theorem isCompact_endpointPairs : IsCompact endpointPairs := by
  have h : endpointPairs = sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 2 := by
    ext p
    simp [endpointPairs]
  rw [h]
  exact (isCompact_sphere 0 1).prod (isCompact_sphere 0 2)

/-- A point within `η ≤ 1/10` of a point of modulus `1` or `2` lies in `{1/3 ≤ |z| ≤ 6}`. -/
theorem norm_mem_of_dist_lt {x u : ℂ} {η : ℝ} (hη1 : η ≤ 1 / 10) (hx : dist x u < η)
    (hu : ‖u‖ = 1 ∨ ‖u‖ = 2) : 1 / 3 ≤ ‖x‖ ∧ ‖x‖ ≤ 6 := by
  have h1 : ‖x - u‖ < η := by rwa [dist_eq_norm] at hx
  have h2 := norm_sub_norm_le x u
  have h3 := norm_sub_norm_le u x
  rw [norm_sub_rev] at h3
  rcases hu with hu | hu <;> constructor <;> linarith

/-- **One direction of Lemma 3.2, deterministic form.** -/
theorem oneWayCompare_of_penalized {S T Sf Tf : LSCMetric} {η ν M : ℝ}
    (hη1 : η ≤ 1 / 10) (hν : 0 < ν) (hν1 : ν ≤ 1) (hM : 0 ≤ M)
    (hsrc : ∀ u v : srcV, ‖(u : ℂ)‖ = 1 → ‖(v : ℂ)‖ = 2 →
      S.internal srcV (u, v) ≤ ENNReal.ofReal M →
      Sf ((u : ℂ), (v : ℂ)) ≤ S.internal srcV (u, v) + ENNReal.ofReal (ν / 8))
    (hnear : NearCompare Tf Sf endpointPairs (M + 1) η (ν / 4))
    (hlen : Tf.IsLengthSpace)
    (hconf : ∀ (P : ℝ → ℂ) (a b : ℝ), Tf.IsCurve P a b → 1 / 3 ≤ ‖P a‖ → ‖P a‖ ≤ 6 →
      Tf.len P a b < ENNReal.ofReal (M + 2) → ∀ t ∈ Icc a b, P t ∈ tgtU)
    (hTle : ∀ p, T p ≤ Tf p) :
    OneWayCompare S T η ν M := by
  intro u v hu hv hSM
  set s := S.internal srcV (u, v) with hs_def
  have hsfin : s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSM
  have hν8 : 0 ≤ ν / 8 := by positivity
  have hν4 : 0 ≤ ν / 4 := by positivity
  -- the penalized source distance is below the height cutoff
  have h1 := hsrc u v hu hv hSM
  have h2 : Sf ((u : ℂ), (v : ℂ)) ≤ ENNReal.ofReal (M + 1) := by
    calc Sf ((u : ℂ), (v : ℂ)) ≤ s + ENNReal.ofReal (ν / 8) := h1
      _ ≤ ENNReal.ofReal M + ENNReal.ofReal (ν / 8) := by gcongr
      _ = ENNReal.ofReal (M + ν / 8) := (ENNReal.ofReal_add hM hν8).symm
      _ ≤ ENNReal.ofReal (M + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  -- Lemma 3.1 at `(u, v)`
  have h3 : movingOpenSetDist Tf η (u : ℂ) (v : ℂ) ≤
      Sf ((u : ℂ), (v : ℂ)) + ENNReal.ofReal (ν / 4) :=
    hnear ((u : ℂ), (v : ℂ)) ⟨hu, hv⟩ h2
  have h4 : movingOpenSetDist Tf η (u : ℂ) (v : ℂ) < s + ENNReal.ofReal (ν / 2) := by
    calc movingOpenSetDist Tf η (u : ℂ) (v : ℂ)
        ≤ s + ENNReal.ofReal (ν / 8) + ENNReal.ofReal (ν / 4) := h3.trans (by gcongr)
      _ = s + ENNReal.ofReal (3 * ν / 8) := by
          rw [add_assoc, ← ENNReal.ofReal_add hν8 hν4]
          congr 2
          ring
      _ < s + ENNReal.ofReal (ν / 2) := by
          refine ENNReal.add_lt_add_left hsfin ?_
          exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  -- a nearly optimal pair of endpoints
  obtain ⟨q, hq, hqlt⟩ : ∃ q ∈ ball (u : ℂ) η ×ˢ ball (v : ℂ) η,
      Tf q < s + ENNReal.ofReal (ν / 2) := by
    unfold movingOpenSetDist at h4
    rw [iInf_lt_iff] at h4
    obtain ⟨q, hq⟩ := h4
    rw [iInf_lt_iff] at hq
    obtain ⟨hqmem, hqlt⟩ := hq
    exact ⟨q, hqmem, hqlt⟩
  -- a nearly optimal `Tf`-curve
  have hqtop : Tf (q.1, q.2) < ⊤ := lt_of_lt_of_le hqlt le_top
  obtain ⟨P, a, b, hP, hPa, hPb, hPlen⟩ := hlen q.1 q.2 hqtop (ν / 8) (by positivity)
  have hlenlt : Tf.len P a b < s + ENNReal.ofReal (5 * ν / 8) := by
    calc Tf.len P a b ≤ Tf (q.1, q.2) + ENNReal.ofReal (ν / 8) := hPlen
      _ < s + ENNReal.ofReal (ν / 2) + ENNReal.ofReal (ν / 8) := by
          refine ENNReal.add_lt_add_right ENNReal.ofReal_ne_top ?_
          exact hqlt
      _ = s + ENNReal.ofReal (5 * ν / 8) := by
          rw [add_assoc, ← ENNReal.ofReal_add (by positivity) hν8]
          congr 2
          ring
  have hlenM : Tf.len P a b < ENNReal.ofReal (M + 2) := by
    refine lt_of_lt_of_le hlenlt ?_
    calc s + ENNReal.ofReal (5 * ν / 8) ≤ ENNReal.ofReal M + ENNReal.ofReal (5 * ν / 8) := by
          gcongr
      _ = ENNReal.ofReal (M + 5 * ν / 8) := (ENNReal.ofReal_add hM (by positivity)).symm
      _ ≤ ENNReal.ofReal (M + 2) := ENNReal.ofReal_le_ofReal (by linarith)
  -- confinement
  have hstart : 1 / 3 ≤ ‖P a‖ ∧ ‖P a‖ ≤ 6 := by
    rw [hPa]
    exact norm_mem_of_dist_lt hη1 (mem_ball.1 hq.1) (Or.inl hu)
  have hU := hconf P a b hP hstart.1 hstart.2 hlenM
  -- the `T`-internal distance in `U`
  have hPT : T.IsCurve P a b := isCurve_of_le hTle hP
  have hTlen : T.len P a b ≤ Tf.len P a b := len_le_len_of_le hTle P a b
  let x : tgtU := ⟨P a, hU a ⟨le_rfl, hP.1⟩⟩
  let y : tgtU := ⟨P b, hU b ⟨hP.1, le_rfl⟩⟩
  have hint : T.internal tgtU (x, y) < s + ENNReal.ofReal (5 * ν / 8) :=
    internal_lt_of_curve hPT hU rfl rfl (lt_of_le_of_lt hTlen hlenlt)
  have hxmem : (x : ℂ) ∈ ball (u : ℂ) η := by
    change P a ∈ ball (u : ℂ) η
    rw [hPa]
    exact hq.1
  have hymem : (y : ℂ) ∈ ball (v : ℂ) η := by
    change P b ∈ ball (v : ℂ) η
    rw [hPb]
    exact hq.2
  calc T.internalSetDist tgtU {x | (x : ℂ) ∈ ball (u : ℂ) η} {x | (x : ℂ) ∈ ball (v : ℂ) η}
      ≤ T.internal tgtU (x, y) := by
        unfold LSCMetric.internalSetDist
        exact iInf₂_le_of_le x hxmem (iInf₂_le y hymem)
    _ ≤ s + ENNReal.ofReal (5 * ν / 8) := hint.le
    _ ≤ s + ENNReal.ofReal ν := by
        gcongr
        linarith

end SupercriticalLFPPAS.Local
