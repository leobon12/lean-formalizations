import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLQGUniqueness.B2.Polylog.P7Bridge
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MetricLemmas

/-!
# §7: deterministic comparisons between cutoffs (packet T7)

The deterministic tools of the proof of Theorem 1.1 (paper §7, l. 625–662; SB2 §2.8, D11; the corrected
interpolation bridge of SB3 §5(a)):

* normalizer changes `a⁻¹ D^φ = (b/a) · b⁻¹ D^φ` for distances, lengths and internal metrics;
* the transfer of LFPP lengths and internal distances between two continuous fields whose difference is bounded on an
  open set (`len_lfppMetric_le_mul`, `internal_lfppMetric_le_mul`, `lfppMetric_le_internal_mul`);
* confinement: a Euclidean-continuous curve starting in `K ⊆ B_R(0)` whose `d`-length is below `d(K, ∂B_R(0))` stays in
  `B_R(0)` (`mem_ball_of_len_lt_setDist`, IVT on `t ↦ ‖P t‖`);
* near-minimizing curves of LFPP metrics and the transfer of an ordinary near-minimizer confined by the escape distance
  (`lfppMetric_le_of_confined`);
* the length `T` of a unit-speed geodesic on `[0, T]` (`ofReal_eq_of_unitSpeed_geodesic`);
* the mesh index `k(ε) = ⌊ε^{-1/a}⌋₊` with `ε ∈ [(k+1)^{-a}, k^{-a}]` (`meshIdx_window`), `k(ε) → ∞` as `ε ↓ 0`, and
  `k^{-a} ↓ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLFPPAS.Main

open SupercriticalLQGUniqueness (LSCMetric)
open SupercriticalLQGUniqueness.B2.Median (lfppMetric lfppMetric_apply)
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios (setDist)

/-! ### Normalizer changes -/

/-- `a⁻¹ D^φ = (b/a) · b⁻¹ D^φ`. -/
theorem lfppMetric_apply_eq_mul (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppMetric ξ a φ p = ENNReal.ofReal ((b : ℝ) / a) * lfppMetric ξ b φ p := by
  have ha : (0 : ℝ) < a := a.2
  have hb : (0 : ℝ) < b := b.2
  rw [lfppMetric_apply, lfppMetric_apply, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp

/-- Lengths scale with the normalizer: `len_{a⁻¹D^φ} = (b/a) · len_{b⁻¹D^φ}`. -/
theorem len_lfppMetric_eq_mul (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (γ : ℝ → ℂ) (s t : ℝ) :
    (lfppMetric ξ a φ).len γ s t = ENNReal.ofReal ((b : ℝ) / a) * (lfppMetric ξ b φ).len γ s t :=
  LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
    (F := (lfppMetric ξ a φ).pt ∘ γ) (G := (lfppMetric ξ b φ).pt ∘ γ)
    (fun u v => lfppMetric_apply_eq_mul ξ a b φ (γ u, γ v)) (Icc s t)

/-! ### Transfer between two fields -/

/-- **Length transfer.** If `|φ' − φ| ≤ κ` on an open `V`, a Euclidean-continuous curve in `V` has
`a'⁻¹D^{φ'}`-length at most `(a/a') e^{|ξ|κ}` times its `a⁻¹D^φ`-length. -/
theorem len_lfppMetric_le_mul (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {V : Set ℂ}
    (hV : IsOpen V) {κ : ℝ} (hκ : ∀ x ∈ V, |φ' x - φ x| ≤ κ) {γ : ℝ → ℂ} {s t : ℝ}
    (hγ : ContinuousOn γ (Icc s t)) (hγV : ∀ u ∈ Icc s t, γ u ∈ V) :
    (lfppMetric ξ a' φ').len γ s t ≤
      ENNReal.ofReal ((a : ℝ) / a' * Real.exp (|ξ| * κ)) * (lfppMetric ξ a φ).len γ s t := by
  have ha : (0 : ℝ) < a := a.2
  have ha' : (0 : ℝ) < a' := a'.2
  rw [len_lfppMetric_eq_mul ξ a' a φ' γ s t, ENNReal.ofReal_mul (by positivity), mul_assoc]
  exact mul_le_mul_right
    (SupercriticalLQGUniqueness.B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a hV hκ hγ hγV) _

/-- **Internal-distance transfer** with a change of normalizer. -/
theorem internal_lfppMetric_le_mul (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {V : Set ℂ}
    (hV : IsOpen V) {κ : ℝ} (hκ : ∀ x ∈ V, |φ' x - φ x| ≤ κ) (p : V × V) :
    (lfppMetric ξ a' φ').internal V p ≤
      ENNReal.ofReal ((a : ℝ) / a' * Real.exp (|ξ| * κ)) * (lfppMetric ξ a φ).internal V p := by
  have ha : (0 : ℝ) < a := a.2
  have ha' : (0 : ℝ) < a' := a'.2
  have h0 : ENNReal.ofReal ((a : ℝ) / a' * Real.exp (|ξ| * κ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
    le_iInf fun hPV => le_iInf fun hs => le_iInf fun ht => ?_
  have hE := (SupercriticalLQGUniqueness.B2.Polylog.lfppMetric_isCurve_iff ξ a φ).1 hP
  have hP' : (lfppMetric ξ a' φ').IsCurve P s t :=
    (SupercriticalLQGUniqueness.B2.Polylog.lfppMetric_isCurve_iff ξ a' φ').2 hE
  exact iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hP'
    (iInf_le_of_le hPV (iInf_le_of_le hs (iInf_le_of_le ht
      (len_lfppMetric_le_mul ξ a a' hV hκ hE.2 hPV)))))))

/-- Whole-plane distance of the new metric below the transferred internal distance of the old one. -/
theorem lfppMetric_le_internal_mul (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {V : Set ℂ}
    (hV : IsOpen V) {κ : ℝ} (hκ : ∀ x ∈ V, |φ' x - φ x| ≤ κ) (p : V × V) :
    lfppMetric ξ a' φ' ((p.1 : ℂ), (p.2 : ℂ)) ≤
      ENNReal.ofReal ((a : ℝ) / a' * Real.exp (|ξ| * κ)) * (lfppMetric ξ a φ).internal V p :=
  (LSCMetric.edist_le_internal _ V p).trans (internal_lfppMetric_le_mul ξ a a' hV hκ p)

/-! ### Confinement and near-minimizers -/

/-- `d(K, B) ≤ d(x, y)` for `x ∈ K`, `y ∈ B`. -/
theorem setDist_le_apply (d : LSCMetric) {A B : Set ℂ} {x y : ℂ} (hx : x ∈ A) (hy : y ∈ B) :
    setDist d A B ≤ d (x, y) :=
  iInf₂_le_of_le x hx (iInf₂_le y hy)

/-- `d(x, y) ≤ len_d(γ; [s, t])` for parameters `u, v ∈ [s, t]`. -/
theorem apply_le_len (d : LSCMetric) (γ : ℝ → ℂ) {s t u v : ℝ} (hu : u ∈ Icc s t) (hv : v ∈ Icc s t) :
    d (γ u, γ v) ≤ d.len γ s t :=
  eVariationOn.edist_le (d.pt ∘ γ) hu hv

/-- **Confinement.** A Euclidean-continuous curve on `[s, t]` starting in `K ⊆ B_R(0)` whose `d`-length is below the
escape distance `d(K, ∂B_R(0))` stays in `B_R(0)` (IVT on `u ↦ ‖γ u‖`). -/
theorem mem_ball_of_len_lt_setDist (d : LSCMetric) {K : Set ℂ} {R : ℝ} (hK : K ⊆ ball (0 : ℂ) R)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContinuousOn γ (Icc s t)) (hs : γ s ∈ K)
    (hlen : d.len γ s t < setDist d K (sphere 0 R)) : ∀ u ∈ Icc s t, γ u ∈ ball (0 : ℂ) R := by
  intro u hu
  by_contra hout
  have hsR : ‖γ s‖ < R := mem_ball_zero_iff.1 (hK hs)
  have huR : R ≤ ‖γ u‖ := by
    rw [mem_ball_zero_iff, not_lt] at hout; exact hout
  have hsub : Icc s u ⊆ Icc s t := Icc_subset_Icc le_rfl hu.2
  have hcont : ContinuousOn (fun v => ‖γ v‖) (Icc s u) := (hγ.mono hsub).norm
  obtain ⟨v, hv, hvR⟩ := intermediate_value_Icc hu.1 hcont ⟨hsR.le, huR⟩
  have hvs : γ v ∈ sphere (0 : ℂ) R := mem_sphere_zero_iff_norm.2 hvR
  have h1 : setDist d K (sphere 0 R) ≤ d (γ s, γ v) := setDist_le_apply d hs hvs
  have h2 : d (γ s, γ v) ≤ d.len γ s t :=
    apply_le_len d γ (left_mem_Icc.2 (hu.1.trans hu.2)) (hsub hv)
  exact absurd (h1.trans h2) (not_le.2 hlen)

/-- **Near-minimizers of LFPP metrics.** Below any value above `a⁻¹D^φ(x, y)` there is a Euclidean-continuous curve on
`[0, 1]` from `x` to `y` (a piecewise `C¹` path) of smaller length. -/
theorem exists_curve_len_lt (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) {x y : ℂ} {c : ℝ≥0∞}
    (hc : lfppMetric ξ a φ (x, y) < c) :
    ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ 0 = x ∧ γ 1 = y ∧ (lfppMetric ξ a φ).len γ 0 1 < c := by
  have ha : (0 : ℝ) < a := a.2
  have h0 : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [lfppMetric_apply] at hc
  unfold SupercriticalLQGUniqueness.lfppDistance at hc
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top, iInf_lt_iff] at hc
  obtain ⟨P, hP, hPc⟩ := hc
  exact ⟨P, hP.continuousOn, hP.source, hP.target,
    (SupercriticalLQGUniqueness.B2.Median.lfppMetric_len_le_lfppLen ξ a φ hP).trans_lt hPc⟩

/-- **Ordinary-to-localized transfer of a confined near-minimizer** (SB2 §2.8 step 2, SB3 §5(a) bridge): if
`a⁻¹D^φ(x, y) < L ≤ a⁻¹D^φ(K, ∂B_R(0))` with `x ∈ K ⊆ B_R(0)` and `|φ' − φ| ≤ κ` on `B_R(0)`, then
`a'⁻¹D^{φ'}(x, y) ≤ (a/a') e^{|ξ|κ} L`. -/
theorem lfppMetric_le_of_confined (ξ : ℝ) (a a' : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {R κ : ℝ}
    {K : Set ℂ} (hK : K ⊆ ball (0 : ℂ) R) (hκ : ∀ x ∈ ball (0 : ℂ) R, |φ' x - φ x| ≤ κ) {x y : ℂ}
    (hx : x ∈ K) {L : ℝ≥0∞} (hxy : lfppMetric ξ a φ (x, y) < L)
    (hL : L ≤ setDist (lfppMetric ξ a φ) K (sphere 0 R)) :
    lfppMetric ξ a' φ' (x, y) ≤ ENNReal.ofReal ((a : ℝ) / a' * Real.exp (|ξ| * κ)) * L := by
  obtain ⟨γ, hγ, h0, h1, hlen⟩ := exists_curve_len_lt ξ a φ hxy
  have hin : ∀ u ∈ Icc (0 : ℝ) 1, γ u ∈ ball (0 : ℂ) R :=
    mem_ball_of_len_lt_setDist _ hK hγ (h0 ▸ hx) (hlen.trans_le hL)
  have hle : lfppMetric ξ a' φ' (x, y) ≤ (lfppMetric ξ a' φ').len γ 0 1 := by
    rw [← h0, ← h1]
    exact apply_le_len _ γ (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
  calc lfppMetric ξ a' φ' (x, y) ≤ (lfppMetric ξ a' φ').len γ 0 1 := hle
    _ ≤ ENNReal.ofReal ((a : ℝ) / a' * Real.exp (|ξ| * κ)) * (lfppMetric ξ a φ).len γ 0 1 :=
        len_lfppMetric_le_mul ξ a a' isOpen_ball hκ hγ hin
    _ ≤ ENNReal.ofReal ((a : ℝ) / a' * Real.exp (|ξ| * κ)) * L := mul_le_mul_right hlen.le _

/-! ### Unit-speed geodesics -/

/-- A unit-speed geodesic on `[0, T]` has `d(P 0, P T) = T`. -/
theorem ofReal_eq_of_unitSpeed_geodesic (d : LSCMetric) {P : ℝ → ℂ} {T : ℝ}
    (hg : LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 T)) : ENNReal.ofReal T = d (P 0, P T) := by
  have h1 := hu (left_mem_Icc.2 hg.1) (right_mem_Icc.2 hg.1)
  rw [inter_self, NNReal.coe_one, one_mul, sub_zero] at h1
  rw [← h1]
  exact hg.2.2

/-- `IsGeodIn` is monotone in the radius. -/
theorem isGeodIn_mono {d : LSCMetric} {P : ℝ → ℂ} {T R R' : ℝ} (h : Core.IsGeodIn d P T R) (hR : R ≤ R') :
    Core.IsGeodIn d P T R' :=
  ⟨h.1, h.2.1, h.2.2.1, fun t ht => ball_subset_ball hR (h.2.2.2 t ht)⟩

/-! ### The mesh index -/

/-- The mesh index `k(ε) = ⌊ε^{-1/a}⌋₊`: the window `[(k+1)^{-a}, k^{-a}]` of the mesh `n^{-a}` containing `ε`. -/
def meshIdx (a ε : ℝ) : ℕ := ⌊ε ^ (-a⁻¹)⌋₊

/-- For `0 < ε ≤ 1`: `k(ε) ≥ 1` and `(k(ε)+1)^{-a} ≤ ε ≤ k(ε)^{-a}`. -/
theorem meshIdx_window {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ meshIdx a ε ∧ ((meshIdx a ε : ℝ) + 1) ^ (-a) ≤ ε ∧ ε ≤ (meshIdx a ε : ℝ) ^ (-a) := by
  set t := ε ^ (-a⁻¹) with ht
  have hneg : -a⁻¹ ≤ 0 := by have := inv_pos.2 ha; linarith
  have ht1 : 1 ≤ t := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 hneg
  have hk1 : 1 ≤ meshIdx a ε := Nat.le_floor (by exact_mod_cast ht1)
  have hkpos : (0 : ℝ) < meshIdx a ε := by exact_mod_cast hk1
  have hkt : (meshIdx a ε : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htk : t < (meshIdx a ε : ℝ) + 1 := Nat.lt_floor_add_one t
  have htε : t ^ (-a) = ε := by
    rw [ht, ← Real.rpow_mul hε.le]
    have : -a⁻¹ * -a = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hna : -a ≤ 0 := by linarith
  refine ⟨hk1, ?_, ?_⟩
  · have := Real.rpow_le_rpow_of_nonpos (by linarith) htk.le hna
    rwa [htε] at this
  · have := Real.rpow_le_rpow_of_nonpos hkpos hkt hna
    rwa [htε] at this

/-- `k(ε) → ∞` as `ε ↓ 0`. -/
theorem tendsto_meshIdx {a : ℝ} (ha : 0 < a) : Tendsto (meshIdx a) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun ε : ℝ => (ε⁻¹) ^ (a⁻¹)) (𝓝[>] 0) atTop :=
    (tendsto_rpow_atTop (inv_pos.2 ha)).comp tendsto_inv_nhdsGT_zero
  have h2 : (fun ε : ℝ => (ε⁻¹) ^ (a⁻¹)) =ᶠ[𝓝[>] 0] fun ε => ε ^ (-a⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.inv_rpow (le_of_lt hε), Real.rpow_neg (le_of_lt hε)]
  exact tendsto_nat_floor_atTop.comp (h1.congr' h2)

/-- The mesh points `k^{-a}` tend to `0` from above. -/
theorem tendsto_mesh_pow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ (-a)) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_rpow_neg_atTop ha).comp tendsto_natCast_atTop_atTop, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact Real.rpow_pos_of_pos (by exact_mod_cast hk) _

/-- For `k ≥ 2`, the mesh point `k^{-a}` lies in `(0, 1)`. -/
theorem mesh_pow_mem_Ioo {a : ℝ} (ha : 0 < a) {k : ℕ} (hk : 2 ≤ k) : (k : ℝ) ^ (-a) ∈ Ioo (0 : ℝ) 1 := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast hk
  exact ⟨Real.rpow_pos_of_pos (by linarith) _, Real.rpow_lt_one_of_one_lt_of_neg hk1 (by linarith)⟩

/-- The mesh endpoint radii `513 (k^{-a})^σ` tend to `0`. -/
theorem tendsto_mesh_rad {a σ : ℝ} (ha : 0 < a) (hσ : 0 < σ) :
    Tendsto (fun k : ℕ => 513 * ((k : ℝ) ^ (-a)) ^ σ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) ^ (-(a * σ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (mul_pos ha hσ)).comp tendsto_natCast_atTop_atTop
  have h2 : (fun k : ℕ => (k : ℝ) ^ (-(a * σ))) = fun k : ℕ => ((k : ℝ) ^ (-a)) ^ σ := by
    funext k
    rw [← Real.rpow_mul (Nat.cast_nonneg k), neg_mul]
  rw [h2] at h1
  simpa only [mul_zero] using h1.const_mul 513

end SupercriticalLFPPAS.Main
