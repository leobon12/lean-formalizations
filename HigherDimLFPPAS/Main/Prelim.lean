import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Bridge.Weyl
import HigherDimLQGMetric.Sharp.ScaledMetric

/-!
# Proof of Theorem 1.2: preliminaries (packet THM)

Generic tools for the assembly of Theorem 1.2 (MA2 §§2.21–2.25 and Details D-E; paper l. 729–771):

* the intervals `I_n = [(n+1)^{-a}, n^{-a}]`: every `ε`-eventual property holds on all of `I_n` for large `n`
  (`thm_eventually_tiles_of_nhdsGT`), and conversely, since the `I_n` tile `(0, 1]`, a property holding on `I_n` for
  all large `n` holds for all small `ε > 0` (`thm_eventually_of_tiles`);
* Borel–Cantelli along `ε_n = n^{-a}` for events of outer probability `≤ K ε^β` with `aβ > 1`
  (`thm_ae_eventually_of_rate`; `MeasureTheory.ae_eventually_notMem`, `Real.summable_nat_rpow_inv`);
* the comparison step behind (6.8)–(6.9): a unit-speed `G`-geodesic in `B_R`, the property
  `𝒞^{G→G'}_{ε,R}(C, q)` (`Core.Comp`) and endpoint moduli `σ` give `G'(x, y) ≤ C G(x, y) + 2σ` (`thm_le_of_comp`);
* the density comparisons (MA2 D-D1, D5's `fieldLfppMetric_internal_density_compare`) between `M_ε` and `M_{ε'}`
  (`thm_meps_internal_le`) and between `N_ε` and `M_ε` (`thm_neps_internal_le_meps`, `thm_meps_internal_le_neps`),
  and their real-valued form under global = internal (`thm_le_of_internal_le`);
* `N_ε = 𝔞_ε⁻¹ D^ε_h` as functions (`thm_neps_apply`);
* unit-speed geodesics of a proper length metric between points of `B̄_r` stay in a fixed ball
  (`thm_exists_geodesic_confined`), and a uniform modulus of continuity (`thm_exists_modulus`);
* the two real-arithmetic combinations of (6.11) and of the transfer to `N_ε` (`thm_real_combine`,
  `thm_real_transfer`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Main

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### The sequences `ε_n = n^{-a}` and the intervals `I_n` -/

/-- `n^{-a} → 0⁺` for `a > 0`. -/
theorem thm_tendsto_seq {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝[>] (0 : ℝ)) := by
  refine tendsto_nhdsWithin_iff.2
    ⟨(tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

/-- The endpoint radii `ρ_n = 8 ε_n^q` of (6.8)–(6.9) tend to `0` (`q > 0`). -/
theorem thm_tendsto_radius {a q : ℝ} (ha : 0 < a) (hq : 0 < q) :
    Tendsto (fun n : ℕ => 8 * ((n : ℝ) ^ (-a)) ^ q) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => 8 * x ^ q) (𝓝 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto).const_mul 8
    simpa only [Real.zero_rpow hq.ne', mul_zero] using this
  exact h1.comp ((thm_tendsto_seq ha).mono_right nhdsWithin_le_nhds)

/-- An `ε`-eventual property holds on the whole interval `I_n = [(n+1)^{-a}, n^{-a}]` for all large `n`. -/
theorem thm_eventually_tiles_of_nhdsGT {a : ℝ} (ha : 0 < a) {p : ℝ → Prop}
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), p ε) :
    ∀ᶠ n : ℕ in atTop, ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)), p ε := by
  obtain ⟨ε₁, hε₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
    (thm_tendsto_seq ha).mono_right nhdsWithin_le_nhds
  filter_upwards [ht.eventually (gt_mem_nhds hε₁)] with n hn ε hε
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact hsub ⟨(Real.rpow_pos_of_pos hpos _).trans_le hε.1, hε.2.trans_lt hn⟩

/-- **The intervals `I_n` tile `(0, 1]`** (MA2 §1.1 item 25): a property holding on `I_n = [(n+1)^{-a}, n^{-a}]` for
all large `n` holds for all small `ε > 0` (`ε ∈ I_n` for `n = ⌊ε^{-1/a}⌋`). -/
theorem thm_eventually_of_tiles {a : ℝ} (ha : 0 < a) {p : ℝ → Prop}
    (h : ∀ᶠ n : ℕ in atTop, ∀ ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)), p ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), p ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have hN1 : (1 : ℝ) ≤ ((max N 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right N 1
  have hNpos : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) := zero_lt_one.trans_le hN1
  filter_upwards [Ioo_mem_nhdsGT (Real.rpow_pos_of_pos hNpos (-a))] with ε hε
  obtain ⟨hε0, hεN⟩ := hε
  have hinv : (-a⁻¹) * (-a) = 1 := by rw [neg_mul_neg, inv_mul_cancel₀ ha.ne']
  have hinv' : (-a) * (-a⁻¹) = 1 := by rw [neg_mul_neg, mul_inv_cancel₀ ha.ne']
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = ε ^ (-a⁻¹) := ⟨_, rfl⟩
  have hypos : 0 < y := hy ▸ Real.rpow_pos_of_pos hε0 _
  have hyε : y ^ (-a) = ε := by
    rw [hy, ← Real.rpow_mul hε0.le, hinv, Real.rpow_one]
  have hNy : ((max N 1 : ℕ) : ℝ) ≤ y := by
    have h1 := Real.rpow_le_rpow_of_nonpos hε0 hεN.le (neg_nonpos.2 (inv_pos.2 ha).le)
    rwa [← Real.rpow_mul hNpos.le, hinv', Real.rpow_one, ← hy] at h1
  have hn : max N 1 ≤ ⌊y⌋₊ := Nat.le_floor hNy
  have hnpos : (0 : ℝ) < (⌊y⌋₊ : ℝ) := hNpos.trans_le (by exact_mod_cast hn)
  refine hN ⌊y⌋₊ ((le_max_left N 1).trans hn) ε ⟨?_, ?_⟩
  · rw [← hyε]
    exact Real.rpow_le_rpow_of_nonpos hypos (Nat.lt_floor_add_one y).le (neg_nonpos.2 ha.le)
  · rw [← hyε]
    exact Real.rpow_le_rpow_of_nonpos hnpos (Nat.floor_le hypos.le) (neg_nonpos.2 ha.le)

/-- `n^{-a}` lies in its own interval `I_n` (`n ≥ 1`). -/
theorem thm_seq_mem_tile {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (-a) ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  exact ⟨Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (neg_nonpos.2 ha.le), le_rfl⟩

/-- Points of `I_n` are positive. -/
theorem thm_pos_of_mem_tile {a ε : ℝ} {n : ℕ}
    (hε : ε ∈ Icc (((n : ℝ) + 1) ^ (-a)) ((n : ℝ) ^ (-a))) : 0 < ε :=
  (Real.rpow_pos_of_pos (by positivity) _).trans_le hε.1

/-! ### Borel–Cantelli along `ε_n = n^{-a}` -/

/-- **Borel–Cantelli along `ε_n = n^{-a}`** (outer measure; no measurability needed): if the events `bad ε` have
outer probability `≤ K ε^β` for `ε < ε₀` and `aβ > 1`, then almost surely `bad ε_n` eventually fails. -/
theorem thm_ae_eventually_of_rate {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {bad : ℝ → Set Ω}
    {a β K ε₀ : ℝ} (ha : 0 < a) (haβ : 1 < a * β) (hε₀ : 0 < ε₀)
    (hbound : ∀ ε ∈ Ioo (0 : ℝ) ε₀, P (bad ε) ≤ ENNReal.ofReal (K * ε ^ β)) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, ω ∉ bad ((n : ℝ) ^ (-a)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((thm_tendsto_seq ha).eventually (Ioo_mem_nhdsGT hε₀))
  let s : ℕ → Set Ω := fun n => {ω | N ≤ n ∧ ω ∈ bad ((n : ℝ) ^ (-a))}
  have hs : ∀ n : ℕ, P (s n) ≤ ENNReal.ofReal (|K| * ((n : ℝ) ^ (a * β))⁻¹) := by
    intro n
    by_cases hn : N ≤ n
    · have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc P (s n) ≤ P (bad ((n : ℝ) ^ (-a))) := measure_mono fun ω hω => hω.2
        _ ≤ ENNReal.ofReal (K * ((n : ℝ) ^ (-a)) ^ β) := hbound _ (hN n hn)
        _ ≤ ENNReal.ofReal (|K| * ((n : ℝ) ^ (a * β))⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Real.rpow_mul hn0, ← Real.rpow_neg hn0, neg_mul]
          exact mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hn0 _)
    · have hempty : s n = ∅ := by
        ext ω
        exact ⟨fun h => absurd h.1 hn, fun h => h.elim⟩
      rw [hempty, measure_empty]
      exact zero_le
  have hsum : Summable (fun n : ℕ => |K| * ((n : ℝ) ^ (a * β))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 haβ).mul_left _
  have htsum : ∑' n, P (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hs)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem htsum] with ω hω
  filter_upwards [hω, eventually_ge_atTop N] with n hn hNn hb
  exact hn ⟨hNn, hb⟩

/-! ### The comparison step of (6.8)–(6.9) -/

/-- Lower bounds through a set distance: if `a ≤ c + G(u, v; V)` for all `u ∈ A`, `v ∈ B`, then
`a ≤ c + G(A, B; V)`. -/
theorem thm_le_add_setDistIn (G : ContMetric d) {V A B : Set (Rd d)} {a c : ℝ≥0∞}
    (h : ∀ u ∈ A, ∀ v ∈ B, a ≤ c + G.internal V u v) : a ≤ c + setDistIn G V A B := by
  unfold setDistIn
  simp only [ENNReal.add_iInf]
  exact le_iInf₂ fun u hu => le_iInf₂ fun v hv => h u hu v hv

/-- **The comparison step of (6.8)–(6.9)** (MA2 §2.21): a unit-speed `G`-geodesic from `x` to `y` inside `B_R`
(admissible for `Core.Comp` through `Core.UnitSpeedAdmissible`), the property `𝒞^{G→G'}_{ε,R}(C, q)` and
`G'`-moduli `σ` at the two endpoints on the scale `8ε^q` give `G'(x, y) ≤ C G(x, y) + 2σ`. -/
theorem thm_le_of_comp (hus : Core.UnitSpeedAdmissible d) (G G' : ContMetric d) {R ε q C σ : ℝ}
    {x y : Rd d} (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hgeo : ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
      MapsTo γ (Icc 0 T) (ball 0 R) ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, G.1 (γ s, γ t) = |t - s|)
    (hcomp : Core.Comp G G' R ε q C)
    (hx : ∀ x' ∈ ball x (8 * ε ^ q), G'.1 (x, x') ≤ σ)
    (hy : ∀ y' ∈ ball y (8 * ε ^ q), G'.1 (y', y) ≤ σ) :
    G'.1 (x, y) ≤ C * G.1 (x, y) + 2 * σ := by
  obtain ⟨γ, T, hT, h0, h1, hc, hmaps, hu⟩ := hgeo
  have hgeoI := hus G R γ T hT hc hmaps hu
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hTT : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hlen : G.len γ 0 T = ENNReal.ofReal T := by
    simpa only [sub_zero] using hgeoI.2.2.2.2 0 hT0 T hTT hT
  have hGxy : G.1 (x, y) = T := by
    rw [← h0, ← h1, hu 0 hT0 T hTT, sub_zero, abs_of_nonneg hT]
  have hc' := hcomp γ T hgeoI hmaps
  rw [h0, h1, hlen, ← ENNReal.ofReal_mul hC] at hc'
  have key : ENNReal.ofReal (G'.1 (x, y)) ≤ ENNReal.ofReal (2 * σ) + ENNReal.ofReal (C * T) := by
    refine le_trans ?_ (add_le_add le_rfl hc')
    refine thm_le_add_setDistIn G' fun u hu v hv => ?_
    have htri : G'.1 (x, y) ≤ G'.1 (x, u) + G'.1 (u, v) + G'.1 (v, y) :=
      (G'.apply_triangle x v y).trans (add_le_add (G'.apply_triangle x u v) le_rfl)
    calc ENNReal.ofReal (G'.1 (x, y))
        ≤ ENNReal.ofReal (2 * σ + G'.1 (u, v)) := by
          apply ENNReal.ofReal_le_ofReal
          linarith [hx u hu, hy v hv]
      _ = ENNReal.ofReal (2 * σ) + ENNReal.ofReal (G'.1 (u, v)) :=
          ENNReal.ofReal_add (by positivity) (G'.nonneg u v)
      _ ≤ ENNReal.ofReal (2 * σ) + G'.internal (ball 0 (R + 2)) u v :=
          add_le_add le_rfl (G'.ofReal_le_internal _ u v)
  rw [← ENNReal.ofReal_add (by positivity) (mul_nonneg hC hT)] at key
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key
  rw [hGxy]
  linarith

/-! ### `M_ε`, `N_ε` and the density comparisons -/

/-- Unfolding `Core.Meps` where `𝔞_ε > 0` (always, for admissible seeds: `SeedFacts.aEps_pos`). -/
theorem thm_meps_eq (κ : Rd d → ℝ) {ξ ε : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ ε) :
    Core.Meps κ ξ ε g =
      (fieldLfppMetric ξ (Core.locFieldC κ ε g)).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha) :=
  dite_eq_left ha

/-- Unfolding `Core.Neps` where `𝔞_ε > 0`. -/
theorem thm_neps_eq (κ : Rd d → ℝ) {ξ ε : ℝ} (g : DistRd d) (ha : 0 < aEps κ ξ ε) :
    Core.Neps κ ξ ε g =
      (fieldLfppMetric ξ (Core.convFieldC κ ε g)).smul (aEps κ ξ ε)⁻¹ (inv_pos.2 ha) :=
  dite_eq_left ha

/-- `Core.locFieldC` is `ĥ*_ε` where the latter is continuous. -/
theorem thm_locFieldC_eq (κ : Rd d → ℝ) {ε : ℝ} {g : DistRd d} (hc : Continuous (locField κ ε g)) :
    Core.locFieldC κ ε g = ⟨locField κ ε g, hc⟩ :=
  dite_eq_left hc

/-- `Core.convFieldC` is `h*_ε` where the latter is continuous. -/
theorem thm_convFieldC_eq (κ : Rd d → ℝ) {ε : ℝ} {g : DistRd d}
    (hc : Continuous (convMollify κ ε g)) :
    Core.convFieldC κ ε g = ⟨convMollify κ ε g, hc⟩ :=
  dite_eq_left hc

/-- `N_ε = 𝔞_ε⁻¹ D^ε_g` as functions on `ℝ^d × ℝ^d` where `h*_ε` is continuous (`fieldLfpp_eq_lfppDistOn`). -/
theorem thm_neps_apply (κ : Rd d → ℝ) {ξ ε : ℝ} {g : DistRd d} (ha : 0 < aEps κ ξ ε)
    (hc : Continuous (convMollify κ ε g)) (p : Rd d × Rd d) :
    (Core.Neps κ ξ ε g).1 p = ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε g) p := by
  rw [thm_neps_eq κ g ha, ContMetric.smul_apply, fieldLfppMetric_apply,
    fieldLfpp_eq_lfppDistOn (Core.convFieldC κ ε g).continuous, thm_convFieldC_eq κ hc]
  rfl

/-- Density comparison for scaled LFPP metrics (MA2 D-D1): if `|log(α/β) + ξ(φ − ψ)| ≤ s` on the open set `V`,
then `(α D^φ)(·,·;V) ≤ e^s (β D^ψ)(·,·;V)`. -/
theorem thm_smul_internal_le {ξ s α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (φ ψ : C(Rd d, ℝ))
    {V : Set (Rd d)} (hV : IsOpen V)
    (hb : ∀ z ∈ V, |Real.log (α / β) + ξ * (φ z - ψ z)| ≤ s) (x y : Rd d) :
    ((fieldLfppMetric ξ φ).smul α hα).internal V x y ≤
      ENNReal.ofReal (Real.exp s) * ((fieldLfppMetric ξ ψ).smul β hβ).internal V x y := by
  rw [ContMetric.internal_smul, ContMetric.internal_smul, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos s).le]
  exact Bridge.fieldLfppMetric_internal_density_compare ξ s α β hα hβ φ ψ V hV hb x y

/-- `M_ε(·,·;V) ≤ e^s M_{ε'}(·,·;V)` when `|log(𝔞_{ε'}/𝔞_ε) + ξ(ĥ*_ε − ĥ*_{ε'})| ≤ s` on `V` (the comparison of (6.10)). -/
theorem thm_meps_internal_le (κ : Rd d → ℝ) {ξ ε ε' s : ℝ} {g : DistRd d} {V : Set (Rd d)}
    (hV : IsOpen V) (ha : 0 < aEps κ ξ ε) (ha' : 0 < aEps κ ξ ε')
    (hc : Continuous (locField κ ε g)) (hc' : Continuous (locField κ ε' g))
    (hb : ∀ z ∈ V, |Real.log (aEps κ ξ ε' / aEps κ ξ ε) +
      ξ * (locField κ ε g z - locField κ ε' g z)| ≤ s) (x y : Rd d) :
    (Core.Meps κ ξ ε g).internal V x y ≤
      ENNReal.ofReal (Real.exp s) * (Core.Meps κ ξ ε' g).internal V x y := by
  rw [thm_meps_eq κ g ha, thm_meps_eq κ g ha']
  refine thm_smul_internal_le _ _ _ _ hV (fun z hz => ?_) x y
  rw [inv_div_inv, thm_locFieldC_eq κ hc, thm_locFieldC_eq κ hc']
  exact hb z hz

/-- `N_ε(·,·;V) ≤ e^s M_ε(·,·;V)` when `ξ |h*_ε − ĥ*_ε| ≤ s` on `V` (the transfer, MA2 §2.24). -/
theorem thm_neps_internal_le_meps (κ : Rd d → ℝ) {ξ ε s : ℝ} {g : DistRd d} {V : Set (Rd d)}
    (hV : IsOpen V) (ha : 0 < aEps κ ξ ε)
    (hc : Continuous (convMollify κ ε g)) (hc' : Continuous (locField κ ε g))
    (hb : ∀ z ∈ V, |ξ * (convMollify κ ε g z - locField κ ε g z)| ≤ s) (x y : Rd d) :
    (Core.Neps κ ξ ε g).internal V x y ≤
      ENNReal.ofReal (Real.exp s) * (Core.Meps κ ξ ε g).internal V x y := by
  rw [thm_neps_eq κ g ha, thm_meps_eq κ g ha]
  refine thm_smul_internal_le _ _ _ _ hV (fun z hz => ?_) x y
  rw [div_self (inv_pos.2 ha).ne', Real.log_one, zero_add, thm_convFieldC_eq κ hc,
    thm_locFieldC_eq κ hc']
  exact hb z hz

/-- `M_ε(·,·;V) ≤ e^s N_ε(·,·;V)` when `ξ |ĥ*_ε − h*_ε| ≤ s` on `V` (the transfer, MA2 §2.24). -/
theorem thm_meps_internal_le_neps (κ : Rd d → ℝ) {ξ ε s : ℝ} {g : DistRd d} {V : Set (Rd d)}
    (hV : IsOpen V) (ha : 0 < aEps κ ξ ε)
    (hc : Continuous (convMollify κ ε g)) (hc' : Continuous (locField κ ε g))
    (hb : ∀ z ∈ V, |ξ * (locField κ ε g z - convMollify κ ε g z)| ≤ s) (x y : Rd d) :
    (Core.Meps κ ξ ε g).internal V x y ≤
      ENNReal.ofReal (Real.exp s) * (Core.Neps κ ξ ε g).internal V x y := by
  rw [thm_neps_eq κ g ha, thm_meps_eq κ g ha]
  refine thm_smul_internal_le _ _ _ _ hV (fun z hz => ?_) x y
  rw [div_self (inv_pos.2 ha).ne', Real.log_one, zero_add, thm_convFieldC_eq κ hc,
    thm_locFieldC_eq κ hc']
  exact hb z hz

/-- Real form of an internal comparison when both global distances equal the internal ones on `V`. -/
theorem thm_le_of_internal_le {G G' : ContMetric d} {V : Set (Rd d)} {x y : Rd d} {c : ℝ}
    (hc : 0 ≤ c) (hG : ENNReal.ofReal (G.1 (x, y)) = G.internal V x y)
    (hG' : ENNReal.ofReal (G'.1 (x, y)) = G'.internal V x y)
    (h : G.internal V x y ≤ ENNReal.ofReal c * G'.internal V x y) :
    G.1 (x, y) ≤ c * G'.1 (x, y) := by
  rw [← hG, ← hG', ← ENNReal.ofReal_mul hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc (G'.nonneg x y))).1 h

/-! ### Deterministic facts about a fixed continuous metric -/

/-- A continuous metric is bounded on `B̄_r × B̄_r`. -/
theorem thm_exists_bound (G : ContMetric d) (r : ℝ) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ ∀ x ∈ closedBall (0 : Rd d) r, ∀ y ∈ closedBall (0 : Rd d) r, G.1 (x, y) ≤ Δ := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Rd d) r).prod
    (isCompact_closedBall (0 : Rd d) r)).exists_bound_of_continuousOn G.continuous_apply.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx y hy =>
    (Real.le_norm_self _).trans ((hC (x, y) ⟨hx, hy⟩).trans (le_max_left _ _))⟩

/-- Uniform continuity of a continuous metric on `B̄_r`: nearby points are `G`-close. -/
theorem thm_exists_modulus (G : ContMetric d) (r : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    ∃ ρ₀ > 0, ∀ p ∈ closedBall (0 : Rd d) r, ∀ p' ∈ closedBall (0 : Rd d) r,
      ‖p - p'‖ < ρ₀ → G.1 (p, p') < σ := by
  have hU := ((isCompact_closedBall (0 : Rd d) r).prod
    (isCompact_closedBall (0 : Rd d) r)).uniformContinuousOn_of_continuous
      G.continuous_apply.continuousOn
  obtain ⟨ρ₀, hρ₀, h⟩ := Metric.uniformContinuousOn_iff.1 hU σ hσ
  refine ⟨ρ₀, hρ₀, fun p hp p' hp' hpp' => ?_⟩
  have hd : dist (p, p) (p, p') < ρ₀ := by
    rw [Prod.dist_eq, dist_self, dist_eq_norm, max_eq_right (norm_nonneg _)]
    exact hpp'
  have := h (p, p) ⟨hp, hp⟩ (p, p') ⟨hp, hp'⟩ hd
  rwa [Real.dist_eq, G.apply_self, zero_sub, abs_neg, abs_of_nonneg (G.nonneg p p')] at this

/-- **Confinement of geodesics** (MA2 §2.21): for a proper length metric `G` whose distances escape to infinity
uniformly from compact sets (Lemma 2.2, D2's `lemma22_ae_proper_and_geodesic`), all unit-speed `G`-geodesics
between points of `B̄_r` lie in one ball `B_R`. -/
theorem thm_exists_geodesic_confined (G : ContMetric d) (hG : G.IsLength) [ProperSpace G.Space]
    (hesc : ∀ K : Set (Rd d), IsCompact K → ∀ M : ℝ, ∃ R : ℝ, ∀ x ∈ K, ∀ y : Rd d,
      R ≤ ‖y‖ → M < G.1 (x, y))
    (r : ℝ) :
    ∃ R : ℕ, ∀ x ∈ closedBall (0 : Rd d) r, ∀ y ∈ closedBall (0 : Rd d) r,
      ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = x ∧ γ T = y ∧ ContinuousOn γ (Icc 0 T) ∧
        MapsTo γ (Icc 0 T) (ball 0 R) ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, G.1 (γ s, γ t) = |t - s| := by
  obtain ⟨Δ, -, hΔ⟩ := thm_exists_bound G r
  obtain ⟨R₁, hR₁⟩ := hesc _ (isCompact_closedBall 0 r) Δ
  refine ⟨⌈R₁⌉₊, fun x hx y hy => ?_⟩
  obtain ⟨P, h0, h1, -, -, hu⟩ := G.exists_geodesic hG x y
  have hT : 0 ≤ G.1 (x, y) := G.nonneg x y
  refine ⟨P, G.1 (x, y), hT, h0, h1, ?_, ?_, hu⟩
  · rw [← G.continuousOn_pt_comp_iff]
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun s hs t ht => ?_).continuousOn
    rw [Function.comp_apply, Function.comp_apply, ContMetric.dist_pt, hu s hs t ht, NNReal.coe_one,
      one_mul, Real.dist_eq, abs_sub_comm]
  · intro s hs
    rw [mem_ball_zero_iff]
    by_contra hcon
    have h1' := hR₁ x hx (P s) ((Nat.le_ceil R₁).trans (not_lt.1 hcon))
    have h2 : G.1 (x, P s) ≤ Δ := by
      have hxs : G.1 (x, P s) = s := by
        rw [← h0, hu 0 ⟨le_rfl, hT⟩ s hs, sub_zero, abs_of_nonneg hs.1]
      rw [hxs]
      exact hs.2.trans (hΔ x hx y hy)
    linarith

/-! ### Real arithmetic -/

/-- `|log r| ≤ 2η` for `|r − 1| ≤ η ≤ 1/2`. -/
theorem thm_abs_log_le {r η : ℝ} (hr : 0 < r) (hη : η ≤ 1 / 2) (h : |r - 1| ≤ η) :
    |Real.log r| ≤ 2 * η := by
  have h' := abs_le.1 h
  have hη0 : 0 ≤ η := (abs_nonneg _).trans h
  rw [abs_le]
  refine ⟨?_, by linarith [Real.log_le_sub_one_of_pos hr]⟩
  have hinv := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
  rw [Real.log_inv] at hinv
  have hrr : r * (r⁻¹ - 1) = 1 - r := by rw [mul_sub, mul_inv_cancel₀ hr.ne', mul_one]
  have : r⁻¹ - 1 ≤ 2 * η := by
    by_contra hcon
    have h2 := mul_lt_mul_of_pos_left (not_le.1 hcon) hr
    nlinarith [mul_nonneg hη0 (by linarith : (0 : ℝ) ≤ 2 * r - 1)]
  linarith

/-- The arithmetic of (6.11): from (6.8) `m_n ≤ (1+δ)g + 2σ`, (6.9) `g ≤ (1+δ)m_n + 2σ` and (6.10)
`m ≤ (1+t)m_n`, `m_n ≤ (1+t)m`, with `δ ≤ t ≤ 1`, `σ ≤ 1` and `0 ≤ g ≤ Δ`: `|m − g| ≤ 12t(Δ + 1) + 4σ`. -/
theorem thm_real_combine {m mn g δ t σ Δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδ0 : 0 ≤ δ)
    (hδt : δ ≤ t) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hg0 : 0 ≤ g) (hgΔ : g ≤ Δ) (hmn0 : 0 ≤ mn)
    (hA : mn ≤ (1 + δ) * g + 2 * σ) (hB : g ≤ (1 + δ) * mn + 2 * σ)
    (hC1 : m ≤ (1 + t) * mn) (hC2 : mn ≤ (1 + t) * m) :
    |m - g| ≤ 12 * t * (Δ + 1) + 4 * σ := by
  have hδ1 : δ ≤ 1 := hδt.trans ht1
  have hΔ0 : 0 ≤ Δ := hg0.trans hgΔ
  have htδ : t * δ ≤ t := mul_le_of_le_one_right ht0 hδ1
  have hL : (1 + t) * (1 + δ) - 1 ≤ 3 * t := by nlinarith
  have hm0 : 0 ≤ m := by nlinarith
  have hup : m - g ≤ ((1 + t) * (1 + δ) - 1) * g + 2 * (1 + t) * σ := by
    have := hC1.trans (mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ 1 + t))
    nlinarith
  have hlow : g - m ≤ ((1 + t) * (1 + δ) - 1) * m + 2 * σ := by
    have := hB.trans (add_le_add
      (mul_le_mul_of_nonneg_left hC2 (by linarith : (0 : ℝ) ≤ 1 + δ)) le_rfl)
    nlinarith
  have hmn : mn ≤ 2 * Δ + 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hδ1) hg0]
  have hm : m ≤ 4 * Δ + 4 := by nlinarith [mul_nonneg (sub_nonneg.2 ht1) hmn0]
  have e1 : ((1 + t) * (1 + δ) - 1) * g ≤ 3 * t * Δ := mul_le_mul hL hgΔ hg0 (by linarith)
  have e2 : ((1 + t) * (1 + δ) - 1) * m ≤ 3 * t * (4 * Δ + 4) := mul_le_mul hL hm hm0 (by linarith)
  have e3 : 2 * (1 + t) * σ ≤ 4 * σ := by nlinarith
  have e4 : 0 ≤ t * Δ := mul_nonneg ht0 hΔ0
  rw [abs_le]
  constructor <;> nlinarith

/-- The arithmetic of the transfer to `N_ε` (MA2 §2.24): from `n ≤ (1+t)m`, `m ≤ (1+t)n`, `|m − g| ≤ η/2`, `g ≤ Δ`
and `2t(Δ + η) ≤ η/2` (`0 ≤ t ≤ 1`): `|n − g| ≤ η`. -/
theorem thm_real_transfer {nε m g t η Δ : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hm0 : 0 ≤ m)
    (h1 : nε ≤ (1 + t) * m) (h2 : m ≤ (1 + t) * nε) (hmg : |m - g| ≤ η / 2)
    (hgΔ : g ≤ Δ) (htη : 2 * t * (Δ + η) ≤ η / 2) : |nε - g| ≤ η := by
  have hη0 : 0 ≤ η := by linarith [abs_nonneg (m - g)]
  have hmg' := abs_le.1 hmg
  have hmΔ : m ≤ Δ + η := by linarith
  have e1 : nε - m ≤ t * m := by linarith
  have e2 : m - nε ≤ 2 * t * m := by
    nlinarith [mul_le_mul_of_nonneg_left h1 ht0, mul_nonneg (mul_nonneg ht0 (sub_nonneg.2 ht1)) hm0]
  have e3 : t * m ≤ t * (Δ + η) := mul_le_mul_of_nonneg_left hmΔ ht0
  rw [abs_le]
  constructor <;> nlinarith

end HigherDimLFPPAS.Main
