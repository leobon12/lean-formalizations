import HigherDimLQGMetric.DGZ.TightBasics
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# DGZ Lemma 6.2, deterministic part: chains of boxes (packet L5a)

Source: Ding–Gwynne–Zhuang, arXiv:2310.03996v5 ([2]), Lemma 6.2 (TeX l. 2879–2907, pp. 56–57);
blueprint Part C, Lemma `r2:lem:62` ("choose `k` and a finite family of boxes `B_{2^{-k}}(x_i)`
covering `V̄`, with `B_{2^{1-k}}(x_i) ⊆ U`, whose union is connected … other pairs are joined
through the chain of boxes, at most `C(k)` links").

* `exists_box_cover`: a compact `T` inside an open `U` is covered by finitely many boxes
  `B_{2^{-k}}(c)`, `c ∈ T`, whose doubles `B_{2^{1-k}}(c)` lie in `U`.
* `boxGraph_reachable`: if `T` is preconnected, the intersection graph of such a cover is
  connected (a clopen argument on `T`).
* `chain_holder_bound`: Hölder bounds `D(u, v; B_{2r}(c)) ≤ K ‖u - v‖^β` on all doubled boxes give
  `D(x, y; U) ≤ K (1 + #F (2√d)^β) ‖x - y‖^β` for all `x, y ∈ T` (close pairs lie in a common
  doubled box; far pairs are joined along a path of the box graph, of length `< #F`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

namespace DGZ

open HigherDimLFPP
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

/-! ### Box covers of compact sets -/

/-- Every point of `obox c s` is within Euclidean distance `√d s` of `c`. -/
lemma tc_norm_sub_le_of_mem_obox {c z : Rd d} {s : ℝ} (hz : z ∈ obox c s) :
    ‖z - c‖ ≤ Real.sqrt d * s :=
  norm_sub_le_of_forall_abs_le fun i => (hz i).le

/-- **Box covers**: a compact `T` inside an open `U` is covered by finitely many boxes
`B_{2^{-k}}(c)` with centres `c ∈ T` and `k ≥ 1`, whose doubles `B_{2·2^{-k}}(c)` lie in `U`. -/
theorem exists_box_cover {T U : Set (Rd d)} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ F : Finset (Rd d), (∀ c ∈ F, c ∈ T) ∧
      T ⊆ ⋃ c ∈ F, obox c ((2 : ℝ)⁻¹ ^ k) ∧ ∀ c ∈ F, obox c (2 * (2 : ℝ)⁻¹ ^ k) ⊆ U := by
  obtain ⟨δ, hδ, hthick⟩ := hT.exists_thickening_subset_open hU hTU
  have hD : 0 < 2 * Real.sqrt d + 1 := by positivity
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (div_pos hδ hD) (by norm_num : (2 : ℝ)⁻¹ < 1)
  set k := k₀ + 1 with hk
  have hkk : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ k₀ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ k₀)
  obtain ⟨F, hFT, hcov⟩ := hT.elim_nhds_subcover (fun c => obox c ((2 : ℝ)⁻¹ ^ k))
    fun c _ => (HigherDimLFPP.DGZ.isOpen_obox c _).mem_nhds fun i => by
      rw [sub_self, abs_zero]; positivity
  refine ⟨k, Nat.le_add_left 1 k₀, F, hFT, hcov, fun c hc z hz => hthick ?_⟩
  refine Metric.ball_subset_thickening (hFT c hc) δ ?_
  rw [Metric.mem_ball, dist_eq_norm]
  have h1 := tc_norm_sub_le_of_mem_obox hz
  have h2 : Real.sqrt d * (2 * (2 : ℝ)⁻¹ ^ k) < δ := by
    have h3 : (2 * Real.sqrt d + 1) * (2 : ℝ)⁻¹ ^ k < δ := by
      calc (2 * Real.sqrt d + 1) * (2 : ℝ)⁻¹ ^ k ≤ (2 * Real.sqrt d + 1) * (2 : ℝ)⁻¹ ^ k₀ :=
            mul_le_mul_of_nonneg_left hkk hD.le
        _ < (2 * Real.sqrt d + 1) * (δ / (2 * Real.sqrt d + 1)) :=
            mul_lt_mul_of_pos_left hk₀ hD
        _ = δ := by field_simp
    have h4 : 0 < (2 : ℝ)⁻¹ ^ k := by positivity
    nlinarith
  linarith

/-! ### The box graph -/

/-- The intersection graph of the boxes `B_r(c)`, `c ∈ F`. -/
def boxGraph (F : Finset (Rd d)) (r : ℝ) : SimpleGraph F where
  Adj u v := u ≠ v ∧ (obox (u : Rd d) r ∩ obox (v : Rd d) r).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The box graph of a cover of a preconnected set is connected.** -/
theorem boxGraph_reachable {T : Set (Rd d)} (hT : IsPreconnected T) {F : Finset (Rd d)}
    (hFT : ∀ c ∈ F, c ∈ T) {r : ℝ} (hr : 0 < r) (hcov : T ⊆ ⋃ c ∈ F, obox c r) (u v : F) :
    (boxGraph F r).Reachable u v := by
  classical
  set S : Set F := {w | (boxGraph F r).Reachable u w} with hS
  set A : Set (Rd d) := ⋃ w ∈ S, obox (w : Rd d) r with hA
  set B : Set (Rd d) := ⋃ w ∈ Sᶜ, obox (w : Rd d) r with hB
  have hcen : ∀ w : F, (w : Rd d) ∈ obox (w : Rd d) r := fun w i => by
    rw [sub_self, abs_zero]; exact hr
  by_contra hv
  have hvS : v ∈ Sᶜ := hv
  have hAo : IsOpen A := isOpen_biUnion fun w _ => HigherDimLFPP.DGZ.isOpen_obox _ _
  have hBo : IsOpen B := isOpen_biUnion fun w _ => HigherDimLFPP.DGZ.isOpen_obox _ _
  have hTAB : T ⊆ A ∪ B := by
    intro t ht
    obtain ⟨c, hc, htc⟩ := mem_iUnion₂.1 (hcov ht)
    by_cases hcS : (⟨c, hc⟩ : F) ∈ S
    · exact Or.inl (mem_iUnion₂.2 ⟨⟨c, hc⟩, hcS, htc⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨⟨c, hc⟩, hcS, htc⟩)
  have hTA : (T ∩ A).Nonempty :=
    ⟨u, hFT u u.2, mem_iUnion₂.2 ⟨u, SimpleGraph.Reachable.refl u, hcen u⟩⟩
  have hTB : (T ∩ B).Nonempty := ⟨v, hFT v v.2, mem_iUnion₂.2 ⟨v, hvS, hcen v⟩⟩
  obtain ⟨z, -, hzA, hzB⟩ := hT A B hAo hBo hTAB hTA hTB
  obtain ⟨w₁, hw₁, hz₁⟩ := mem_iUnion₂.1 hzA
  obtain ⟨w₂, hw₂, hz₂⟩ := mem_iUnion₂.1 hzB
  have hne : w₁ ≠ w₂ := fun h => hw₂ (h ▸ hw₁)
  have hadj : (boxGraph F r).Adj w₁ w₂ := ⟨hne, z, hz₁, hz₂⟩
  exact hw₂ (SimpleGraph.Reachable.trans hw₁ hadj.reachable)

/-! ### The chain bound -/

/-- **Chains of boxes** (D-6.1–6.3, Lemma 6.2): let `T` be preconnected and covered by the boxes
`B_r(c)`, `c ∈ F ⊆ T`, whose doubles `B_{2r}(c)` lie in `V`, and suppose the Hölder bounds
`D(u, v; B_{2r}(c)) ≤ K ‖u - v‖^β` hold on every doubled box. Then
`D(x, y; V) ≤ K (1 + #F (2√d)^β) ‖x - y‖^β` for all `x, y ∈ T`. -/
theorem chain_holder_bound {φ : Rd d → ℝ} (hφ : Continuous φ) (ξ : ℝ) {V T : Set (Rd d)}
    (hT : IsPreconnected T) {F : Finset (Rd d)} (hFT : ∀ c ∈ F, c ∈ T) {r : ℝ} (hr : 0 < r)
    (hcov : T ⊆ ⋃ c ∈ F, obox c r) (hsub : ∀ c ∈ F, obox c (2 * r) ⊆ V) {K β : ℝ} (hK : 0 ≤ K)
    (hβ : 0 < β)
    (hbox : ∀ c ∈ F, ∀ u ∈ obox c (2 * r), ∀ v ∈ obox c (2 * r),
      lfppDistOn ξ φ (obox c (2 * r)) u v ≤ K * ‖u - v‖ ^ β) :
    ∀ x ∈ T, ∀ y ∈ T,
      lfppDistOn ξ φ V x y ≤ K * (1 + F.card * (2 * Real.sqrt d) ^ β) * ‖x - y‖ ^ β := by
  classical
  -- points of one box are joined inside its double, at cost `≤ b`
  have hmem2 : ∀ c : Rd d, ∀ z ∈ obox c r, z ∈ obox c (2 * r) := fun c z hz i =>
    (hz i).trans (by linarith)
  set b : ℝ := K * (Real.sqrt d * (2 * r)) ^ β with hb
  have hb0 : 0 ≤ b := by positivity
  have hone : ∀ c ∈ F, ∀ x ∈ obox c r, ∀ z ∈ obox c r,
      PcwJoined V x z ∧ lfppDistOn ξ φ V x z ≤ b := by
    intro c hc x hx z hz
    have hj : PcwJoined (obox c (2 * r)) x z :=
      PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox c _) (hmem2 c x hx) (hmem2 c z hz)
    refine ⟨hj.mono (hsub c hc), ?_⟩
    have hxz : ‖x - z‖ ≤ Real.sqrt d * (2 * r) :=
      norm_sub_le_of_forall_abs_le fun i => by
        have h1 := hx i
        have h2 := hz i
        rw [abs_lt] at h1 h2
        rw [abs_le]; constructor <;> linarith
    calc lfppDistOn ξ φ V x z ≤ lfppDistOn ξ φ (obox c (2 * r)) x z :=
          lfppDistOn_mono (hsub c hc) hj
      _ ≤ K * ‖x - z‖ ^ β := hbox c hc x (hmem2 c x hx) z (hmem2 c z hz)
      _ ≤ b := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hxz hβ.le) hK
  -- walks in the box graph
  have hwalk : ∀ (u v : F) (p : (boxGraph F r).Walk u v), ∀ x ∈ obox (u : Rd d) r,
      ∀ y ∈ obox (v : Rd d) r, PcwJoined V x y ∧ lfppDistOn ξ φ V x y ≤ (p.length + 1) * b := by
    intro u v p
    induction p with
    | nil =>
      intro x hx y hy
      obtain ⟨h1, h2⟩ := hone _ (Subtype.prop _) x hx y hy
      refine ⟨h1, ?_⟩
      simpa only [SimpleGraph.Walk.length_nil, CharP.cast_eq_zero, zero_add, one_mul] using h2
    | cons hadj p ih =>
      intro x hx y hy
      obtain ⟨z, hz₁, hz₂⟩ := hadj.2
      obtain ⟨hj₁, hd₁⟩ := hone _ (Subtype.prop _) x hx z hz₁
      obtain ⟨hj₂, hd₂⟩ := ih z hz₂ y hy
      refine ⟨hj₁.trans hj₂, ?_⟩
      calc lfppDistOn ξ φ V x y ≤ lfppDistOn ξ φ V x z + lfppDistOn ξ φ V z y :=
            lfppDistOn_triangle hφ hj₁ hj₂
        _ ≤ b + (p.length + 1) * b := add_le_add hd₁ hd₂
        _ = ((SimpleGraph.Walk.cons hadj p).length + 1) * b := by
            rw [SimpleGraph.Walk.length_cons]; push_cast; ring
  intro x hx y hy
  obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hcov hx)
  have hsβ : 0 ≤ ‖x - y‖ ^ β := Real.rpow_nonneg (norm_nonneg _) β
  have hKc : 0 ≤ K * (F.card * (2 * Real.sqrt d) ^ β) := by positivity
  by_cases hclose : ‖x - y‖ < r
  · -- close pairs: a common doubled box
    have hyc : y ∈ obox c (2 * r) := fun i => by
      have h1 := hxc i
      have h2 : |x i - y i| < r := by
        have := HigherDimLFPP.DGZ.abs_apply_le_norm (x - y) i
        rw [PiLp.sub_apply] at this
        exact lt_of_le_of_lt this hclose
      calc |y i - c i| ≤ |y i - x i| + |x i - c i| := abs_sub_le _ _ _
        _ < r + r := by rw [abs_sub_comm] at h2; exact add_lt_add h2 h1
        _ = 2 * r := by ring
    have hj : PcwJoined (obox c (2 * r)) x y :=
      PcwJoined.of_convex (HigherDimLFPP.DGZ.convex_obox c _) (hmem2 c x hxc) hyc
    calc lfppDistOn ξ φ V x y ≤ lfppDistOn ξ φ (obox c (2 * r)) x y :=
          lfppDistOn_mono (hsub c hc) hj
      _ ≤ K * ‖x - y‖ ^ β := hbox c hc x (hmem2 c x hxc) y hyc
      _ ≤ K * (1 + F.card * (2 * Real.sqrt d) ^ β) * ‖x - y‖ ^ β := by
          rw [mul_add, mul_one, add_mul]
          linarith [mul_nonneg hKc hsβ]
  · -- far pairs: a path of the box graph
    push Not at hclose
    obtain ⟨c', hc', hyc'⟩ := mem_iUnion₂.1 (hcov hy)
    obtain ⟨p⟩ := boxGraph_reachable hT hFT hr hcov ⟨c, hc⟩ ⟨c', hc'⟩
    set q := p.bypass with hq
    have hlen : q.length < F.card := by
      have := p.bypass_isPath.length_lt
      rwa [Fintype.card_coe] at this
    obtain ⟨-, hD⟩ := hwalk _ _ q x hxc y hyc'
    have hbr : b ≤ K * (2 * Real.sqrt d) ^ β * ‖x - y‖ ^ β := by
      rw [hb, show Real.sqrt d * (2 * r) = (2 * Real.sqrt d) * r by ring,
        Real.mul_rpow (by positivity) hr.le, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hclose hβ.le) (by positivity)
    have hlen' : ((q.length : ℝ) + 1) ≤ F.card := by exact_mod_cast hlen
    calc lfppDistOn ξ φ V x y ≤ (q.length + 1) * b := hD
      _ ≤ F.card * b := mul_le_mul_of_nonneg_right hlen' hb0
      _ ≤ F.card * (K * (2 * Real.sqrt d) ^ β * ‖x - y‖ ^ β) :=
          mul_le_mul_of_nonneg_left hbr (Nat.cast_nonneg _)
      _ ≤ K * (1 + F.card * (2 * Real.sqrt d) ^ β) * ‖x - y‖ ^ β := by
          have : 0 ≤ K * ‖x - y‖ ^ β := mul_nonneg hK hsβ
          nlinarith

end DGZ

end HigherDimLQGMetric
