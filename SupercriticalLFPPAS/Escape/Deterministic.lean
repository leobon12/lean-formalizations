import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Main.Transfer
import SupercriticalLFPPAS.Local.Confinement

/-!
# Lemma 6.2: the deterministic steps (packet L62)

Paper `source/almost-sure-supercritical-lfpp.txt`, Lemma 6.2 (l. 605–622); binding proof: planning audit
`planning/audits/SB2-sections-3-7.md` §2.7 and Details **D10** (with M10), SB3 §2 "Lemma 6.2".

At one sample `g = h(ω)` with heat versions `Y ε = X ε ω`:

* `exists_lt_setDist_thickening` (lower semicontinuity and compactness): `c < D(K, T)` for compact `K, T` gives
  `c < D(K^ρ, T^ρ)` for all small `ρ`.
* `lt_setDist_of_compare` (the mesh bound (6.2), D10 steps 2–3): on the event of (2.8) for `U = B_{R+1}(0)` at radius
  `ρ`, `C₀(M + 1/2) < D(K^ρ, (∂B_R)^ρ)` gives `M < X̂(K, ∂B_R)` (paths stopped at their first hit of `∂B_R`).
* `lt_setDist_of_close` (interpolation, D10 step 4): a near-minimizing curve for the cutoff `ε`, stopped at its first
  hit of `∂B_R`, lies in `B̄_R ⊆ B_{R+1}`, where the field changes by at most `κ` and the normalizer ratio is controlled.
* `escape_core` (D10 steps 2–5): the conclusion of Lemma 6.2 at one sample from the mesh comparisons (2.8) on every
  `B_{R+1}(0)`, (2.1), (2.2) for every mesh exponent, (6.1) and (1.4).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Escape

open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.Median (lfppMetric)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)

/-- `setDist` is antitone in both sets. -/
theorem setDist_anti_sets (d : LSCMetric) {A A' B B' : Set ℂ} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    setDist d A B ≤ setDist d A' B' :=
  iInf₂_mono' fun z hz => ⟨z, hA hz, iInf₂_mono' fun w hw => ⟨w, hB hw, le_rfl⟩⟩

/-- **Lower semicontinuity and compactness.** If `c < d(K, T)` for compact `K, T`, then `c < d(K^ρ, T^ρ)` for every
`ρ ≤ 1/(N+1)`, for some `N`. -/
theorem exists_lt_setDist_thickening (d : LSCMetric) {K T : Set ℂ} (hK : IsCompact K) (hT : IsCompact T)
    {c : ℝ≥0∞} (hc : c < setDist d K T) :
    ∃ N : ℕ, ∀ ρ : ℝ, ρ ≤ 1 / ((N : ℝ) + 1) → c < setDist d (thickening ρ K) (thickening ρ T) := by
  by_contra hcon
  push Not at hcon
  have h : ∀ n : ℕ, B2.Iface.setDistance d.1 (thickening (1 / ((n : ℝ) + 1)) K)
      (thickening (1 / ((n : ℝ) + 1)) T) ≤ c := by
    intro n
    obtain ⟨ρ, hρ, hle⟩ := hcon n
    rw [iface_setDistance_eq_setDist]
    exact (setDist_anti_sets d (thickening_mono hρ K) (thickening_mono hρ T)).trans hle
  have hle := Local.setDistance_le_of_thickening d hK hT h
  rw [iface_setDistance_eq_setDist] at hle
  exact absurd hle (not_le.2 hc)

/-- **The mesh bound** (paper (6.2); SB2 D10 steps 2–3). On the event of (2.8) for `U = B_{R+1}(0)` at radius `ρ`, if
`C₀(M + 1/2) < D(K^ρ, (∂B_R)^ρ)` then `M < a⁻¹D^φ(K, ∂B_R)`: a near-minimizing path stopped at its first hit of
`∂B_R` lies in `B̄_R ⊆ U` (`Local.setDistance_thickening_le_of_compare`). -/
theorem lt_setDist_of_compare (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) {Dg : LSCMetric} {ρ C₀ M R : ℝ}
    {K : Set ℂ} (hKR : ∀ z ∈ K, ‖z‖ < R) (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M)
    (hcomp : B2.Polylog.compareHolds (lfppMetric ξ a φ) Dg ρ (ball (0 : ℂ) (R + 1)) C₀)
    (hD : ENNReal.ofReal (C₀ * (M + 1 / 2)) <
      setDist Dg (thickening ρ K) (thickening ρ (sphere (0 : ℂ) R))) :
    ENNReal.ofReal M < setDist (lfppMetric ξ a φ) K (sphere (0 : ℂ) R) := by
  by_contra hle
  rw [not_lt, ← iface_setDistance_eq_setDist] at hle
  have h := Local.setDistance_thickening_le_of_compare (Local.lfppMetric_isLengthSpace ξ a φ)
    (fun P s t hP => ((B2.Polylog.lfppMetric_isCurve_iff ξ a φ).1 hP).2) hKR hC₀ hM hcomp hle
  rw [iface_setDistance_eq_setDist] at h
  exact absurd h (not_le.2 hD)

/-- **Interpolation between cutoffs** (SB2 D10 step 4). If `|φ − ψ| ≤ κ` on `B_{R+1}(0)` and `(a'/a) e^{|ξ|κ} ≤ 2`,
then `2M + 1 < a⁻¹D^φ(K, ∂B_R)` implies `M < a'⁻¹D^ψ(K, ∂B_R)`: a near-minimizing `ψ`-curve from `K` to `∂B_R`,
stopped at its first hit of `∂B_R`, stays in `B̄_R ⊆ B_{R+1}`, where its `φ`-length is at most twice its `ψ`-length.
No confinement is assumed. -/
theorem lt_setDist_of_close (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ ψ : C(ℂ, ℝ)} {κ M R : ℝ} {K : Set ℂ}
    (hKR : ∀ z ∈ K, ‖z‖ < R) (hM : 0 ≤ M) (hfac : (a' : ℝ) / a * Real.exp (|ξ| * κ) ≤ 2)
    (hκ : ∀ z ∈ ball (0 : ℂ) (R + 1), |φ z - ψ z| ≤ κ)
    (hφ : ENNReal.ofReal (2 * M + 1) < setDist (lfppMetric ξ a φ) K (sphere (0 : ℂ) R)) :
    ENNReal.ofReal M < setDist (lfppMetric ξ a' ψ) K (sphere (0 : ℂ) R) := by
  by_contra hle
  rw [not_lt] at hle
  have hMlt : ENNReal.ofReal M < ENNReal.ofReal (M + 1 / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
  have hlt := lt_of_le_of_lt hle hMlt
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ K, ∃ y ∈ sphere (0 : ℂ) R,
      lfppMetric ξ a' ψ (x, y) < ENNReal.ofReal (M + 1 / 2) := by
    unfold setDist at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨x, hx, y, hy, h⟩ := hlt
    exact ⟨x, hx, y, hy, h⟩
  obtain ⟨γ, hγ, h0, h1, hlen⟩ := Main.exists_curve_len_lt ξ a' ψ hxy
  obtain ⟨t, ht, hγt, hin⟩ := Local.exists_stopped_curve zero_le_one hγ
    (by rw [h0]; exact hKR x hx) (by rw [h1]; simpa using hy)
  have hV : ∀ u ∈ Icc (0 : ℝ) t, γ u ∈ ball (0 : ℂ) (R + 1) := fun u hu => by
    rw [mem_ball, dist_zero_right]
    linarith [hin u hu]
  have htr := Main.len_lfppMetric_le_mul ξ a' a isOpen_ball hκ
    (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hV
  have hpt : lfppMetric ξ a φ (x, γ t) ≤ ENNReal.ofReal (2 * M + 1) := by
    calc lfppMetric ξ a φ (x, γ t) ≤ (lfppMetric ξ a φ).len γ 0 t := by
          rw [← h0]
          exact Main.apply_le_len _ γ (left_mem_Icc.2 ht.1) (right_mem_Icc.2 ht.1)
      _ ≤ ENNReal.ofReal ((a' : ℝ) / a * Real.exp (|ξ| * κ)) * (lfppMetric ξ a' ψ).len γ 0 t := htr
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (M + 1 / 2) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hfac)
            ((B2.PfeWeyl.len_mono_Icc _ γ le_rfl ht.2).trans hlen.le)
      _ = ENNReal.ofReal (2 * M + 1) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  have hle' : setDist (lfppMetric ξ a φ) K (sphere (0 : ℂ) R) ≤ ENNReal.ofReal (2 * M + 1) :=
    (Main.setDist_le_apply _ hx (by simpa using hγt)).trans hpt
  exact absurd hle' (not_le.2 hφ)

/-- The normalizer and field factor of the interpolation: `|log x| ≤ η` and `(1 + 3|ξ|)η ≤ log 2` give
`x e^{|ξ| · 3η} ≤ 2`. -/
theorem mul_exp_le_two_of_abs_log_le {ξ η x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ η)
    (hη : (1 + 3 * |ξ|) * η ≤ Real.log 2) : x * Real.exp (|ξ| * (3 * η)) ≤ 2 := by
  have hx' : x ≤ Real.exp η := by
    rw [← Real.exp_log hx]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans hlog)
  calc x * Real.exp (|ξ| * (3 * η)) ≤ Real.exp η * Real.exp (|ξ| * (3 * η)) :=
        mul_le_mul_of_nonneg_right hx' (Real.exp_pos _).le
    _ = Real.exp ((1 + 3 * |ξ|) * η) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hη
    _ = 2 := Real.exp_log two_pos

/-- `ĥ_ε` as the coercion of the continuous field `plMollifyC`. -/
theorem plMollifyC_apply (q ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (g : DistC) (z : ℂ) :
    B2.Polylog.plMollifyC q ε hε g z = B2.Polylog.plMollify q ε hε g z := rfl

/-- **Lemma 6.2 at one sample** (SB2 D10 steps 2–5). Data at the sample `g = h(ω)` with heat versions `Y`: for every
integer `R`, the comparison (2.8) at `ζ` on `B_{R+1}(0)` eventually on the mesh `n^{-a(R)}` (constant `C₀` independent
of `R`); (2.1); (2.2) for every mesh exponent `a(R)`; (6.1) (`hW`, deterministic); (1.4). Conclusion: the escape form of
Lemma 6.2. -/
theorem escape_core (S : Core.Setup) (hW : Core.NormalizerWindowStmt S) {ζ C₀ : ℝ} (hζ1 : ζ < 1) (hC₀ : 0 < C₀)
    {a : ℕ → ℝ} (ha : ∀ R, 0 < a R) {g : DistC} {Y : Set.Ioi (0 : ℝ) → C(ℂ, ℝ)}
    (hcomp : ∀ R : ℕ, ∀ᶠ n : ℕ in atTop, ∀ hδ : (n : ℝ) ^ (-a R) ∈ Ioo (0 : ℝ) 1,
      B2.Polylog.compareHolds (Core.locMetric S _ hδ g) (S.D g) (((n : ℝ) ^ (-a R)) ^ (1 - ζ))
        (ball (0 : ℂ) ((R : ℝ) + 1)) C₀)
    (hloc : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1, ∀ z ∈ K,
        |Y ⟨ε, hε.1⟩ z - B2.Polylog.plMollify 1 ε hε g z| ≤ η)
    (hosc : ∀ R : ℕ, ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      ∀ ε δ : Set.Ioi (0 : ℝ), ((n : ℝ) + 1) ^ (-a R) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a R) →
        ((n : ℝ) + 1) ^ (-a R) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a R) → ∀ z ∈ K, |Y ε z - Y δ z| ≤ η)
    (hesc : ∀ k : ℕ, Tendsto (fun R : ℝ => setDist (S.D g) (closedBall (0 : ℂ) k) (sphere (0 : ℂ) R))
      atTop (𝓝 ⊤)) :
    ∀ K : Set ℂ, IsCompact K → ∀ M : ℝ, ∃ R : ℝ, K ⊆ ball 0 R ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1), ε < ε₀ →
        ENNReal.ofReal M < setDist (Core.locMetric S ε hε g) K (sphere 0 R) ∧
        ENNReal.ofReal M < setDist (Core.lfppM S ⟨ε, hε.1⟩ (Y ⟨ε, hε.1⟩)) K (sphere 0 R) := by
  intro K hK M
  obtain ⟨M', hM'0, hMM'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ M ≤ M' := ⟨max M 0, le_max_right _ _, le_max_left _ _⟩
  have hM₁ : 0 ≤ 2 * M' + 1 := by linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, K ⊆ closedBall (0 : ℂ) k := by
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    obtain ⟨k, hk⟩ := exists_nat_ge r
    exact ⟨k, hr.trans (closedBall_subset_closedBall hk)⟩
  -- the radius: `C₀(2M' + 1 + 1/2) < D(B̄_k, ∂B_R)` by (1.4)
  obtain ⟨R, hRk, hRc⟩ : ∃ R : ℕ, (k : ℝ) + 1 ≤ R ∧ ENNReal.ofReal (C₀ * (2 * M' + 1 + 1 / 2)) <
      setDist (S.D g) (closedBall (0 : ℂ) k) (sphere (0 : ℂ) R) := by
    have h1 := (hesc k).eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := C₀ * (2 * M' + 1 + 1 / 2))))
    have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h1
    obtain ⟨R, hR1, hR2⟩ := (h2.and (eventually_ge_atTop (k + 1))).exists
    exact ⟨R, by exact_mod_cast hR2, hR1⟩
  have hKR : ∀ z ∈ K, ‖z‖ < R := fun z hz => by
    have := hk hz
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  refine ⟨R, fun z hz => mem_ball_zero_iff.2 (hKR z hz), ?_⟩
  have hDK : ENNReal.ofReal (C₀ * (2 * M' + 1 + 1 / 2)) < setDist (S.D g) K (sphere (0 : ℂ) R) :=
    hRc.trans_le (setDist_anti_sets _ hk subset_rfl)
  obtain ⟨N, hN⟩ := exists_lt_setDist_thickening (S.D g) hK (isCompact_sphere 0 R) hDK
  have hA := ha R
  -- the mesh radii `ρ_n = (n^{-a})^{1-ζ}` tend to `0`
  have hρ : Tendsto (fun n : ℕ => ((n : ℝ) ^ (-a R)) ^ (1 - ζ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x ^ (1 - ζ)) (𝓝 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 (1 - ζ) (Or.inr (by linarith))).tendsto
      rwa [Real.zero_rpow (by linarith)] at this
    exact h0.comp ((Main.tendsto_mesh_pow hA).mono_right nhdsWithin_le_nhds)
  -- (6.2) on the mesh: `2M' + 1 < X̂_{δ_n}(K, ∂B_R)` eventually
  have hmesh : ∀ᶠ n : ℕ in atTop, ∀ hδ : (n : ℝ) ^ (-a R) ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (2 * M' + 1) < setDist (Core.locMetric S _ hδ g) K (sphere (0 : ℂ) R) := by
    filter_upwards [hcomp R, hρ.eventually (eventually_le_nhds
      (show (0 : ℝ) < 1 / ((N : ℝ) + 1) by positivity))] with n hn hρn hδ
    exact lt_setDist_of_compare (S.ξ : ℝ) (S.m ⟨_, hδ.1⟩) (B2.Polylog.plMollifyC 1 _ hδ g) hKR hC₀.le hM₁
      (hn hδ) (hN _ hρn)
  -- the interpolation tolerance
  set η : ℝ := Real.log 2 / (1 + 3 * |(S.ξ : ℝ)|) with hη_def
  have hden : 0 < 1 + 3 * |(S.ξ : ℝ)| := by positivity
  have hη : 0 < η := div_pos (Real.log_pos one_lt_two) hden
  have hηb : (1 + 3 * |(S.ξ : ℝ)|) * η ≤ Real.log 2 := by
    rw [hη_def, mul_div_cancel₀ _ hden.ne']
  have hVc : IsCompact (closedBall (0 : ℂ) ((R : ℝ) + 1)) := isCompact_closedBall _ _
  have hlocV := hloc _ hVc η hη
  have hgood : ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      (∀ hδ : (n : ℝ) ^ (-a R) ∈ Ioo (0 : ℝ) 1,
        ENNReal.ofReal (2 * M' + 1) < setDist (Core.locMetric S _ hδ g) K (sphere (0 : ℂ) R)) ∧
      (∀ ε δ : Set.Ioi (0 : ℝ), ((n : ℝ) + 1) ^ (-a R) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a R) →
        ((n : ℝ) + 1) ^ (-a R) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a R) →
          ∀ z ∈ closedBall (0 : ℂ) ((R : ℝ) + 1), |Y ε z - Y δ z| ≤ η) ∧
      (∀ ε δ : Set.Ioi (0 : ℝ), ((n : ℝ) + 1) ^ (-a R) ≤ (ε : ℝ) → (ε : ℝ) ≤ (n : ℝ) ^ (-a R) →
        ((n : ℝ) + 1) ^ (-a R) ≤ (δ : ℝ) → (δ : ℝ) ≤ (n : ℝ) ^ (-a R) →
          |Real.log ((S.m ε : ℝ) / (S.m δ : ℝ))| ≤ η) ∧
      (∀ hδ : (n : ℝ) ^ (-a R) ∈ Ioo (0 : ℝ) 1, ∀ z ∈ closedBall (0 : ℂ) ((R : ℝ) + 1),
        |Y ⟨_, hδ.1⟩ z - B2.Polylog.plMollify 1 _ hδ g z| ≤ η) := by
    filter_upwards [eventually_ge_atTop 2, hmesh, hosc R _ hVc η hη, hW (a R) hA η hη,
      (Main.tendsto_mesh_pow hA).eventually hlocV] with n h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  -- every small real cutoff lies in a good mesh window
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal M < setDist (Core.locMetric S ε hε g) K (sphere 0 R) ∧
      ENNReal.ofReal M < setDist (Core.lfppM S ⟨ε, hε.1⟩ (Y ⟨ε, hε.1⟩)) K (sphere 0 R) := by
    filter_upwards [hlocV, (Main.tendsto_meshIdx hA).eventually hgood] with ε hlocε hgε hε
    obtain ⟨hn2, hmeshn, hoscn, hWn, hlocn⟩ := hgε
    obtain ⟨-, hw1, hw2⟩ := Main.meshIdx_window hA hε.1 hε.2.le
    have hδ := Main.mesh_pow_mem_Ioo hA hn2
    have hw3 := hw1.trans hw2
    have hYY := hoscn ⟨ε, hε.1⟩ ⟨_, hδ.1⟩ hw1 hw2 hw3 le_rfl
    have hfac := mul_exp_le_two_of_abs_log_le (div_pos (S.m ⟨ε, hε.1⟩).2 (S.m ⟨_, hδ.1⟩).2)
      (hWn ⟨ε, hε.1⟩ ⟨_, hδ.1⟩ hw1 hw2 hw3 le_rfl) hηb
    have hMle : ENNReal.ofReal M ≤ ENNReal.ofReal M' := ENNReal.ofReal_le_ofReal hMM'
    constructor
    · refine hMle.trans_lt (lt_setDist_of_close (S.ξ : ℝ) (S.m ⟨_, hδ.1⟩) (S.m ⟨ε, hε.1⟩) hKR hM'0 hfac
        (fun z hz => ?_) (hmeshn hδ))
      have hzV : z ∈ closedBall (0 : ℂ) ((R : ℝ) + 1) := ball_subset_closedBall hz
      rw [plMollifyC_apply, plMollifyC_apply]
      have e1 := abs_le.1 (hlocε hε z hzV)
      have e2 := abs_le.1 (hYY z hzV)
      have e3 := abs_le.1 (hlocn hδ z hzV)
      exact abs_le.2 ⟨by linarith, by linarith⟩
    · refine hMle.trans_lt (lt_setDist_of_close (S.ξ : ℝ) (S.m ⟨_, hδ.1⟩) (S.m ⟨ε, hε.1⟩) hKR hM'0 hfac
        (fun z hz => ?_) (hmeshn hδ))
      have hzV : z ∈ closedBall (0 : ℂ) ((R : ℝ) + 1) := ball_subset_closedBall hz
      rw [plMollifyC_apply]
      have e2 := abs_le.1 (hYY z hzV)
      have e3 := abs_le.1 (hlocn hδ z hzV)
      exact abs_le.2 ⟨by linarith, by linarith⟩
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  exact ⟨ε₀, hε₀, fun ε hε hεε₀ => hsub ⟨hε.1, hεε₀⟩ hε⟩

end SupercriticalLFPPAS.Escape
