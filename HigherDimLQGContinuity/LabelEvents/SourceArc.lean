import HigherDimLQGContinuity.LabelEvents.Source
import HigherDimLQGContinuity.Witness.FirstExit

/-!
# Consequences of source validity for the arc of an edge (packet Q5; remark after `b:def-source`)

Source: blueprint Part B, the remark after `b:def-source`: "(V2)(a) says that `γ` is an intrinsic `E`-geodesic of the
seed inspection with own length `λ` in primary site units, so `len_E(γ|[s,t]) ≤ λ|t - s|` …; (V2)(d) gives
`D(γ(0), γ(1)) = D(γ(0), γ(1); A) = D(γ(0), γ(1); A_{e,j})`: a path from `γ(0)` to `γ(1)` either stays in `A_{e,j}`, or
leaves `B̄_{s_{e,j}/8}(γ(0)) ⊆ A_{e,j}` and, up to its first hit `w` of the sphere, is a path in `A_{e,j}` of length
`≥ D(γ(0), w; A_{e,j})` (Lemma `a:lem-212`)"; used by the certificate `b:thm-sitecert`(iv), (C10)(a),(d),(e), for a
**length** primary metric (IA1 MAJOR-2). Inputs: `witness_exists_first_sphere_hit` (packet P5a), the curve form of
length metrics `ContMetric.isLength_iff_curves`, and `ContMetric.curveLengthWith_internal` (BBI Prop. 2.3.12).

* `q5_internal_eq_of_first_exit`: (2.12) with a non-strict first-exit barrier at the endpoint itself.
* `edgeArc_internal_eq_global`: for a length metric `D` and an arc of the arc space of the seed shell with the
  first-exit clause (V2)(d), `D(γ 0, γ 1; W) = D(γ 0, γ 1)` for every `W ⊇ A_seed` (in particular `W = A_seed`, `A`).
* `edgeArc_len_eq`: (V2)(a) gives `len_E(γ|[s,t]) = λ (t - s)` for any continuous metric `E`.
* `EdgeSource.exists_arc_spec`: everything the certificate reads from one edge's validity, unpacked.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- **(2.12) with a non-strict first-exit barrier.** Let `D` be a length metric, `δ₁ > 0` with `B̄_{δ₁}(u) ⊆ U`, and
`D(u, v; U) ≤ D(u, w; U)` for every `w` with `|w - u| = δ₁`. Then `D(u, v; U) = D(u, v)`. -/
theorem q5_internal_eq_of_first_exit (D : ContMetric d) (hD : D.IsLength) {U : Set (Rd d)} {u v : Rd d}
    {δ₁ : ℝ} (hδ₁ : 0 < δ₁) (hbuf : closedBall u δ₁ ⊆ U)
    (hexit : ∀ w : Rd d, ‖w - u‖ = δ₁ → D.internal U u v ≤ D.internal U u w) :
    D.internal U u v = ENNReal.ofReal (D.1 (u, v)) := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    (D.ofReal_le_internal U u v)
  obtain ⟨P, hPc, hP0, hP1, hPlen⟩ :=
    (D.isLength_iff_curves.1 hD) u v (ε : ℝ) (by exact_mod_cast hε)
  rw [ENNReal.ofReal_coe_nnreal] at hPlen
  by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ closedBall u δ₁
  · calc D.internal U u v = D.internal U (P 0) (P 1) := by rw [hP0, hP1]
      _ ≤ D.len P 0 1 := D.internal_le_len zero_le_one hPc fun t ht => hbuf (hstay t ht)
      _ ≤ _ := hPlen
  · push Not at hstay
    obtain ⟨s, hs, hsu, hmaps⟩ := witness_exists_first_sphere_hit hδ₁ hPc hP0 hstay
    calc D.internal U u v ≤ D.internal U u (P s) := hexit _ hsu
      _ = D.internal U (P 0) (P s) := by rw [hP0]
      _ ≤ D.len P 0 s :=
          D.internal_le_len hs.1 (hPc.mono (Icc_subset_Icc le_rfl hs.2)) (hmaps.mono_right hbuf)
      _ ≤ D.len P 0 1 := D.len_mono P le_rfl hs.2
      _ ≤ _ := hPlen

/-- The closed first-exit ball about a point of the seed shell lies in the seed inspection. -/
theorem closedBall_eighth_subset_srcSeedA {c u : Rd d} {r : ℝ} (hr : 0 < r) (hu : u ∈ srcSeedK c r) :
    closedBall u (r / 8) ⊆ srcSeedA c r := by
  rw [srcSeedK_eq c hr] at hu
  rw [srcSeedA_eq c hr]
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  obtain ⟨hu1, hu2⟩ := hu
  have h1 : ‖w - c‖ ≤ ‖w - u‖ + ‖u - c‖ := by
    calc ‖w - c‖ = ‖(w - u) + (u - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖w - u‖ + ‖u - c‖ := norm_add_le _ _
  have h2 : ‖u - c‖ ≤ ‖u - w‖ + ‖w - c‖ := by
    calc ‖u - c‖ = ‖(u - w) + (w - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖u - w‖ + ‖w - c‖ := norm_add_le _ _
  rw [norm_sub_rev u w] at h2
  constructor <;> linarith

/-- **Global distance of the arc endpoints** (remark after `b:def-source`): for a length metric `D`, an arc of the
arc space of the seed shell with the first-exit clause (V2)(d) has `D(γ 0, γ 1; W) = D(γ 0, γ 1)` for every
`W ⊇ A_seed`. -/
theorem edgeArc_internal_eq_global {D : ContMetric d} (hD : D.IsLength) {c : Rd d} {r A α β : ℝ}
    (hr : 0 < r) {γ : C(unitInterval, Rd d)} (hγ : γ ∈ ArcSpace (srcSeedK c r) A α β)
    (hexit : ∀ w : Rd d, ‖w - γ 0‖ = r / 8 →
      D.internal (srcSeedA c r) (γ 0) (γ 1) ≤ D.internal (srcSeedA c r) (γ 0) w)
    {W : Set (Rd d)} (hW : srcSeedA c r ⊆ W) :
    D.internal W (γ 0) (γ 1) = ENNReal.ofReal (D.1 (γ 0, γ 1)) := by
  have hA : D.internal (srcSeedA c r) (γ 0) (γ 1) = ENNReal.ofReal (D.1 (γ 0, γ 1)) :=
    q5_internal_eq_of_first_exit D hD (by positivity) (closedBall_eighth_subset_srcSeedA hr (hγ.1 0)) hexit
  refine le_antisymm ?_ (D.ofReal_le_internal W _ _)
  rw [← hA]
  exact D.internal_anti hW _ _

/-- **The `E`-length of the arc** (remark after `b:def-source`): if `E(γ s, γ t; A_seed) = λ|s - t|` along an arc of
the seed shell, then `len_E(γ|[s,t]) = λ (t - s)` for `0 ≤ s ≤ t ≤ 1` (any continuous metric `E`). -/
theorem edgeArc_len_eq {E : ContMetric d} {c : Rd d} {r A α β lam : ℝ} (hr : 0 < r)
    {γ : C(unitInterval, Rd d)} (hγ : γ ∈ ArcSpace (srcSeedK c r) A α β)
    (ha : ∀ s t : unitInterval, E.internal (srcSeedA c r) (γ s) (γ t) = ENNReal.ofReal (lam * |(s : ℝ) - t|))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    E.len (witExt γ) s t = ENNReal.ofReal (lam * (t - s)) := by
  have hc : ContinuousOn (witExt γ) (Icc s t) := (continuous_witExt γ).continuousOn
  have hK : MapsTo (witExt γ) (Icc s t) (srcSeedA c r) :=
    fun u _ => srcSeedK_subset_srcSeedA c hr (witExt_mem hγ.1 u)
  rw [← E.curveLengthWith_internal hc hK]
  have hlam : ∀ u v, s ≤ u → u ≤ v → v ≤ t →
      E.internal (srcSeedA c r) (witExt γ u) (witExt γ v) = ENNReal.ofReal (v - u) * ENNReal.ofReal lam := by
    intro u v hu huv hv
    have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hu, (huv.trans hv).trans ht⟩
    have hv' : v ∈ Icc (0 : ℝ) 1 := ⟨(hs.trans hu).trans huv, hv.trans ht⟩
    rw [witExt_of_mem γ hu', witExt_of_mem γ hv', ha, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 huv),
      mul_comm, ENNReal.ofReal_mul (sub_nonneg.2 huv)]
  rw [witness_curveLengthWith_eq hst hlam, ← ENNReal.ofReal_mul (sub_nonneg.2 hst), mul_comm]

/-- **Unpacking one edge's validity** for the certificate (`b:thm-sitecert`(iv), (C10)): for a length primary metric,
the arc `γ` of (V2) lies in the seed shell, has the moduli of the arc space, own length `λ ∈ [ℓ₀, ℓ₁]` with
`len_E(γ|[s,t]) = λ (t - s)`, the unit-pair bound and the ratio bound for the **global** distance
`D(γ 0, γ 1) = D(γ 0, γ 1; W)` (`W ⊇ A_seed`), and the geometric predicate. -/
theorem EdgeSource.exists_arc_spec {HE sE A α β ℓ₀ ℓ₁ d₀ v : ℝ} {c : Rd d} {r : ℝ}
    {Geo : C(unitInterval, Rd d) → Prop} {D E : ContMetric d} (hD : D.IsLength) (hr : 0 < r) (hv : 0 ≤ v)
    (h : EdgeSource HE sE A α β ℓ₀ ℓ₁ d₀ v c r Geo D E) :
    DUpper E (srcSeedA c r) HE sE ∧ ∃ γ ∈ ArcSpace (srcSeedK c r) A α β, ∃ lam ∈ Icc ℓ₀ ℓ₁,
      (∀ s t : unitInterval,
        E.internal (srcSeedA c r) (γ s) (γ t) = ENNReal.ofReal (lam * |(s : ℝ) - t|)) ∧
      (∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → E.len (witExt γ) s t = ENNReal.ofReal (lam * (t - s))) ∧
      (∀ W : Set (Rd d), srcSeedA c r ⊆ W → D.internal W (γ 0) (γ 1) = ENNReal.ofReal (D.1 (γ 0, γ 1))) ∧
      d₀ ≤ D.1 (γ 0, γ 1) ∧ lam ≤ (1 + 4 * v) * D.1 (γ 0, γ 1) ∧ Geo γ := by
  obtain ⟨hup, γ, hγ, lam, hlam, ha, hb, hc, hd, he⟩ := h
  have hglob : ∀ W : Set (Rd d), srcSeedA c r ⊆ W →
      D.internal W (γ 0) (γ 1) = ENNReal.ofReal (D.1 (γ 0, γ 1)) :=
    fun W hW => edgeArc_internal_eq_global hD hr hγ hd hW
  have hA := hglob (srcSeedA c r) subset_rfl
  have hDnn : 0 ≤ D.1 (γ 0, γ 1) := D.nonneg _ _
  refine ⟨hup, γ, hγ, lam, hlam, ha, fun s t hs hst ht => edgeArc_len_eq hr hγ ha hs hst ht, hglob, ?_, ?_, he⟩
  · rw [hA] at hb
    exact (ENNReal.ofReal_le_ofReal_iff hDnn).1 hb
  · rw [hA, ← ENNReal.ofReal_mul (by linarith)] at hc
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by linarith) hDnn)).1 hc

end HigherDimLQGContinuity
