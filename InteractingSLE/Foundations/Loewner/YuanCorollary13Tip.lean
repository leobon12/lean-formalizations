import InteractingSLE.Foundations.Loewner.YuanShift
import InteractingSLE.Foundations.Loewner.ConformalImageReflect
import QuantumZipper.Proofs.Loewner.CoreArc1

/-!
# The tip of a Loewner chain lies in the closure of its hull

Packet PROVE-YUAN-M1 (input to Y. Yuan, *Topological characterisations of Loewner traces*,
Indiana Univ. Math. J. 71 (2022), arXiv:2003.05535v4, [Yua22], Corollary 1.3; the "basic inverse-map
fact" of `source/external/AstraIG1` §5, interface 1: "at positive time a tip belongs to its
canonical hull").

Let `U` be a continuous driver with `U 0 = 0`, `r > 0`, and suppose the inverse map `F_r` of the
chain has a limit `p` at the driving point `0`. Then `p ∈ closure K_r`
(`mem_closure_fwdHull_of_tendsto`).

## Proof

If `p ∈ ℍ`, then `p ∈ K_r`: otherwise `g_r` is continuous at `p` and `g_r(F_r(w)) = w → 0`.
Let `p` be real with `B(p, κ) ∩ K_r = ∅`. For `s ∈ [0, r]` the centred map `G_s = f_s` reflects
across `(p − κ/2, p + κ/2)` to a holomorphic `Ĝ_s` on `B(p, κ/2)` (Schwarz reflection,
`IsMapOut.exists_reflection`).

* `Ĝ_r(p) = 0`, and `Ĝ_r` has no other zero in `B(p, κ/2)` (a real zero `z` would give
  `F_r(Ĝ_r(ζ)) = ζ → z` and `→ p` at once). Let `m₀ > 0` be the minimum of `‖Ĝ_r‖` on the circle
  `|z − p| = κ/8`.
* `‖Ĝ_s − Ĝ_r‖ ≤ 24 M + 8 √(r − s)` on `B(p, κ/2)` (`G_r = Φ ∘ G_s` with `Φ` the map of the chain
  shifted by `s`, which moves points by at most this amount), so for `s < r` close to `r` it is
  `< m₀/4`.
* Maximum modulus applied to `1/(Ĝ_s − w)`: every `w ∈ B(0, m₀/4)` is a value of `Ĝ_s` on
  `B̄(p, κ/8)`; for `w ∈ ℍ` the preimage lies in `ℍ`.
* Local growth (`CoreArc.norm_fwdMap_le_of_mem_diff`) and strict growth after `s` produce a point
  of `K_r \ K_s` whose `G_s`-image lies in `B(0, m₀/4) ∩ ℍ`; by injectivity of `G_s` this point
  lies in `B(p, κ/2)`, a contradiction.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanCorollary13

variable {U : ℝ → ℝ}

/-! ### The centred reflection near a real point off the hull -/

/-- **Centred Schwarz reflection.** If `B(y, κ)` (`y ∈ ℝ`) avoids `K_s`, the centred map
`G_s = fwdMap U s` extends to a holomorphic `K` on `B(y, κ/2)` with `K(z̄) = conj K(z)`, real on the
real diameter, and `G_s → K(z)` at every real point `z` of the ball. -/
theorem exists_centred_reflection (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {y κ : ℝ} (hd : Disjoint (ball (y : ℂ) κ) (fwdHull U s)) :
    ∃ K : ℂ → ℂ, DifferentiableOn ℂ K (ball (y : ℂ) (κ / 2)) ∧
      EqOn K (fwdMap U s) (ball (y : ℂ) (κ / 2) ∩ H) ∧
      (∀ z ∈ ball (y : ℂ) (κ / 2), K (conj z) = conj (K z)) ∧
      (∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 → (K z).im = 0) ∧
      (∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 →
        Tendsto (fwdMap U s) (𝓝[ball (y : ℂ) (κ / 2) ∩ H] z) (𝓝 (K z))) := by
  obtain ⟨G, hGd, hGeq, hGc, hGr, -, hGt⟩ :=
    (isMapOut_fwdMap hU hU0 hs).exists_reflection (isHPHull_fwdHull hU hs) hd
  refine ⟨fun z => G z - U s, hGd.sub_const _, fun z hz => ?_, fun z hz => ?_, fun z hz h0 => ?_,
    fun z hz h0 => ?_⟩
  · simp only [hGeq hz, add_sub_cancel_right]
  · simp only [hGc z hz, map_sub, Complex.conj_ofReal]
  · simp only [sub_im, ofReal_im, sub_zero]
    exact hGr z hz h0
  · have h := (hGt z hz h0).sub_const (U s : ℂ)
    simpa only [add_sub_cancel_right] using h

/-- Values of the centred reflection: in `ℍ` on the upper half-ball, in the lower half-plane on
the lower half-ball. -/
theorem im_pos_of_centred_reflection (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s) {y κ : ℝ}
    (hd : Disjoint (ball (y : ℂ) κ) (fwdHull U s)) {K : ℂ → ℂ}
    (hKeq : EqOn K (fwdMap U s) (ball (y : ℂ) (κ / 2) ∩ H))
    (hKc : ∀ z ∈ ball (y : ℂ) (κ / 2), K (conj z) = conj (K z))
    {z : ℂ} (hz : z ∈ ball (y : ℂ) (κ / 2)) (hz0 : z.im ≠ 0) :
    (0 < z.im ↔ 0 < (K z).im) ∧ (z.im < 0 ↔ (K z).im < 0) := by
  have hsub : ball (y : ℂ) (κ / 2) ∩ H ⊆ H \ fwdHull U s := fun w hw =>
    ⟨hw.2, fun h => Set.disjoint_left.1 hd (ball_subset_ball (by
      have : 0 ≤ κ := by
        by_contra hneg
        have := (mem_ball.1 hw.1)
        have := dist_nonneg (x := w) (y := (y : ℂ))
        linarith
      linarith) hw.1) h⟩
  have hup : ∀ w ∈ ball (y : ℂ) (κ / 2), 0 < w.im → 0 < (K w).im := fun w hw hw0 => by
    rw [hKeq ⟨hw, hw0⟩]
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hU hs (hsub ⟨hw, hw0⟩)
  have hlow : ∀ w ∈ ball (y : ℂ) (κ / 2), w.im < 0 → (K w).im < 0 := fun w hw hw0 => by
    have hcw : conj w ∈ ball (y : ℂ) (κ / 2) := by
      rw [mem_ball, dist_eq_norm, ← Complex.conj_ofReal, ← map_sub, Complex.norm_conj,
        ← dist_eq_norm]
      exact hw
    have h1 := hup (conj w) hcw (by simpa using hw0)
    have h2 := hKc (conj w) hcw
    rw [Complex.conj_conj] at h2
    rw [h2, Complex.conj_im]
    linarith
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · have := hlow z hz hneg
    exact ⟨⟨fun h => absurd h (not_lt.2 hneg.le), fun h => absurd h (not_lt.2 this.le)⟩,
      ⟨fun _ => this, fun _ => hneg⟩⟩
  · have := hup z hz hpos
    exact ⟨⟨fun _ => this, fun _ => hpos⟩,
      ⟨fun h => absurd h (not_lt.2 hpos.le), fun h => absurd h (not_lt.2 this.le)⟩⟩

/-! ### Uniform displacement between two times -/

/-- `‖G_s(z) − G_r(z)‖ ≤ 24 M + 8 √(r − s)` for `z ∈ ℍ \ K_r`, `0 ≤ s < r`, if
`|U(s + x) − U(s)| ≤ M` on `[0, r − s]`. -/
theorem norm_fwdMap_sub_fwdMap_le (hU : Continuous U) {s r M : ℝ} (hs : 0 ≤ s) (hsr : s < r)
    (hM : ∀ x ∈ Icc (0 : ℝ) (r - s), |shiftDrive U s x| ≤ M) {z : ℂ}
    (hz : z ∈ H \ fwdHull U r) :
    ‖fwdMap U s z - fwdMap U r z‖ ≤ 24 * M + 8 * Real.sqrt (r - s) := by
  have hrs : 0 < r - s := sub_pos.2 hsr
  have hr : r = s + (r - s) := by ring
  have hsol : ∃ u, QuantumZipper.IsForwardSol U z (s + (r - s)) u := by
    rw [← hr]
    exact QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull (hs.trans hsr.le) hz.1 hz.2
  have hadd := QuantumZipper.fwdMap_add hU hz.1 hs hrs.le hsol
  rw [← hr] at hadd
  have hzs : z ∉ fwdHull U s := fun h => hz.2 ((QuantumZipper.fwdHull_mono (W := U)).1 hsr.le h)
  have hGs : fwdMap U s z ∈ H \ fwdHull (shiftDrive U s) (r - s) := by
    refine ⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hU hs ⟨hz.1, hzs⟩, fun h => hz.2 ?_⟩
    have hdiff := QuantumZipper.fwdHull_add_diff hU hs hrs.le (W := U)
    have hmem : z ∈ fwdHull U (s + (r - s)) \ fwdHull U s := by
      rw [hdiff]
      exact ⟨⟨hz.1, hzs⟩, h⟩
    rw [← hr] at hmem
    exact hmem.1
  have hb := QuantumZipper.CoreArc.norm_fwdMap_sub_le_uniform
    (QuantumZipper.RS.continuous_shiftDrive hU s) (shiftDrive_zero U s) hrs hM hGs
  rw [hadd, norm_sub_rev]
  exact hb

/-- **Displacement of reflections.** If two reflected maps agree with `g₁`, `g₂` on the upper
half-ball, are conjugation-symmetric and are the boundary limits of `g₁`, `g₂` at real points, a
bound `‖g₁ − g₂‖ ≤ D` on the upper half-ball holds on the whole ball. -/
theorem norm_sub_le_of_reflections {y κ D : ℝ} {K₁ K₂ g₁ g₂ : ℂ → ℂ}
    (h₁eq : EqOn K₁ g₁ (ball (y : ℂ) (κ / 2) ∩ H)) (h₂eq : EqOn K₂ g₂ (ball (y : ℂ) (κ / 2) ∩ H))
    (h₁c : ∀ z ∈ ball (y : ℂ) (κ / 2), K₁ (conj z) = conj (K₁ z))
    (h₂c : ∀ z ∈ ball (y : ℂ) (κ / 2), K₂ (conj z) = conj (K₂ z))
    (h₁t : ∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 →
      Tendsto g₁ (𝓝[ball (y : ℂ) (κ / 2) ∩ H] z) (𝓝 (K₁ z)))
    (h₂t : ∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 →
      Tendsto g₂ (𝓝[ball (y : ℂ) (κ / 2) ∩ H] z) (𝓝 (K₂ z)))
    (hD : ∀ z ∈ ball (y : ℂ) (κ / 2) ∩ H, ‖g₁ z - g₂ z‖ ≤ D) :
    ∀ z ∈ ball (y : ℂ) (κ / 2), ‖K₁ z - K₂ z‖ ≤ D := by
  have hup : ∀ z ∈ ball (y : ℂ) (κ / 2), 0 < z.im → ‖K₁ z - K₂ z‖ ≤ D := fun z hz hz0 => by
    rw [h₁eq ⟨hz, hz0⟩, h₂eq ⟨hz, hz0⟩]
    exact hD z ⟨hz, hz0⟩
  intro z hz
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have hcz : conj z ∈ ball (y : ℂ) (κ / 2) := by
      rw [mem_ball, dist_eq_norm, ← Complex.conj_ofReal, ← map_sub, Complex.norm_conj,
        ← dist_eq_norm]
      exact hz
    have h1 := h₁c (conj z) hcz
    have h2 := h₂c (conj z) hcz
    rw [Complex.conj_conj] at h1 h2
    rw [h1, h2, ← map_sub, Complex.norm_conj]
    exact hup (conj z) hcz (by simpa using hneg)
  · have hcl : z ∈ closure (ball (y : ℂ) (κ / 2) ∩ H) :=
      subset_closure_ball_inter_H _ _ ⟨hz, show 0 ≤ z.im from hzero.ge⟩
    have : (𝓝[ball (y : ℂ) (κ / 2) ∩ H] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
    have ht := ((h₁t z hz hzero).sub (h₂t z hz hzero)).norm
    refine le_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hD w hw
  · exact hup z hz hpos

/-! ### The tip and the zeros of the reflection at the final time -/

/-- If `F_r(w) → y` (`y ∈ ℝ`) as `w → 0` and `B(y, κ)` avoids `K_r`, the centred reflection of
`G_r` at `y` vanishes at `y` and nowhere else in `B(y, κ/2)`. -/
theorem centred_reflection_eq_zero_iff (hU : Continuous U) (hU0 : U 0 = 0) {r : ℝ} (hr : 0 ≤ r)
    {y κ : ℝ} (hd : Disjoint (ball (y : ℂ) κ) (fwdHull U r))
    (hp : Tendsto (fwdMapInv U r) (𝓝[H] 0) (𝓝 (y : ℂ))) {K : ℂ → ℂ}
    (hKeq : EqOn K (fwdMap U r) (ball (y : ℂ) (κ / 2) ∩ H))
    (hKc : ∀ z ∈ ball (y : ℂ) (κ / 2), K (conj z) = conj (K z))
    (hKt : ∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 →
      Tendsto (fwdMap U r) (𝓝[ball (y : ℂ) (κ / 2) ∩ H] z) (𝓝 (K z)))
    {z : ℂ} (hz : z ∈ ball (y : ℂ) (κ / 2)) : K z = 0 ↔ z = y := by
  set S := ball (y : ℂ) (κ / 2) ∩ H with hS
  have hκ : 0 < κ := by
    by_contra hneg
    have := mem_ball.1 hz
    have := dist_nonneg (x := z) (y := (y : ℂ))
    linarith
  have hyb : (y : ℂ) ∈ ball (y : ℂ) (κ / 2) := mem_ball_self (by positivity)
  have hSsub : S ⊆ H \ fwdHull U r := fun w hw =>
    ⟨hw.2, fun h => Set.disjoint_left.1 hd (ball_subset_ball (by linarith) hw.1) h⟩
  have hH0 : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact zero_mem_Hbar
  have hFS : Tendsto (fwdMapInv U r) (𝓝[H] 0) (𝓝[S] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hp, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hp (isOpen_ball.mem_nhds hyb)] with w hw hwb
    exact ⟨hwb, QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hr hw⟩
  have hKy : K y = 0 := by
    have h1 := (hKt y hyb (by simp)).comp hFS
    have h2 : Tendsto (fun w : ℂ => w) (𝓝[H] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (h1.congr' ?_) h2
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hr hw
  constructor
  · intro hKz
    by_contra hne
    by_cases hz0 : z.im = 0
    · have hcl : z ∈ closure S := subset_closure_ball_inter_H _ _ ⟨hz, show 0 ≤ z.im from hz0.ge⟩
      have : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
      have hG : Tendsto (fwdMap U r) (𝓝[S] z) (𝓝[H] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hKz ▸ hKt z hz hz0, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact QuantumZipper.FwdHolo.mapsTo_fwdMap hU hr (hSsub hw)
      have h1 := hp.comp hG
      have h2 : Tendsto (fun w : ℂ => w) (𝓝[S] z) (𝓝 z) := tendsto_id.mono_left nhdsWithin_le_nhds
      refine hne (tendsto_nhds_unique (h2.congr' ?_) h1)
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hr (hSsub hw)).symm
    · have h := im_pos_of_centred_reflection hU hr (hd.mono_right
        (subset_refl _)) hKeq hKc hz hz0
      rcases lt_or_gt_of_ne hz0 with hneg | hpos
      · have := h.2.1 hneg
        rw [hKz, zero_im] at this
        exact lt_irrefl 0 this
      · have := h.1.1 hpos
        rw [hKz, zero_im] at this
        exact lt_irrefl 0 this
  · rintro rfl
    exact hKy

/-! ### Maximum modulus: values near the centre are attained -/

/-- If `f` is holomorphic on `B(c, R)`, `0 < ρ < R`, `‖f‖ > m` on the circle `|z − c| = ρ` and
`‖f(c)‖ < m`, then `f` vanishes somewhere in `B̄(c, ρ)` (maximum modulus for `1/f`). -/
theorem exists_eq_zero_of_norm_lt {f : ℂ → ℂ} {c : ℂ} {ρ R m : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (hd : DifferentiableOn ℂ f (ball c R)) (hsph : ∀ z ∈ sphere c ρ, m < ‖f z‖)
    (hc : ‖f c‖ < m) : ∃ z ∈ closedBall c ρ, f z = 0 := by
  by_contra hne
  push Not at hne
  have hm : 0 < m := lt_of_le_of_lt (norm_nonneg _) hc
  have hcl : closure (ball c ρ) = closedBall c ρ := closure_ball c hρ.ne'
  have hdg : DifferentiableOn ℂ (fun z => (f z)⁻¹) (closure (ball c ρ)) := by
    rw [hcl]
    exact (hd.mono (closedBall_subset_ball hρR)).inv fun z hz => hne z hz
  have hfr : frontier (ball c ρ) = sphere c ρ := frontier_ball c hρ.ne'
  have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdg.diffContOnCl
    (C := m⁻¹) (fun z hz => by
      rw [hfr] at hz
      rw [norm_inv]
      exact inv_anti₀ hm (hsph z hz).le)
    (subset_closure (mem_ball_self hρ))
  have hfc : 0 < ‖f c‖ := norm_pos_iff.2 (hne c (mem_closedBall_self hρ.le))
  rw [norm_inv] at hle
  have := (inv_le_inv₀ hfc hm).1 hle
  linarith

/-! ### Local growth near the tip -/

/-- If every point of `B(0, μ) ∩ ℍ` is the `G_s`-image of a point of `B(y, κ) ∩ ℍ` (`s < r`), then
`B(y, κ)` meets `K_r`: by local and strict growth, `K_{s+h} \ K_s` is nonempty and is mapped by
`G_s` into `B(0, μ)` for small `h`. -/
theorem not_disjoint_of_ball_subset_image (hU : Continuous U) (hU0 : U 0 = 0) {s r μ κ : ℝ}
    {y : ℂ} (hs : 0 ≤ s) (hsr : s < r) (hμ : 0 < μ)
    (himg : ∀ w ∈ ball (0 : ℂ) μ ∩ H, ∃ z ∈ ball y κ ∩ H, fwdMap U s z = w) :
    ¬ Disjoint (ball y κ) (fwdHull U r) := by
  intro hd
  obtain ⟨δ, hδ, hδU⟩ := Metric.continuous_iff.1 hU s (μ / 16) (by positivity)
  set h := min (r - s) (min (δ / 2) ((μ / 16) ^ 2)) with hh
  have hh0 : 0 < h := lt_min (sub_pos.2 hsr) (lt_min (by positivity) (by positivity))
  have hhr : h ≤ r - s := min_le_left _ _
  have hhδ : h ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hhμ : h ≤ (μ / 16) ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hne := fwdHull_ne_of_lt hU hU0 hs (show s < s + h by linarith)
  have hsub : fwdHull U s ⊆ fwdHull U (s + h) := fwdHull_mono' (by linarith)
  obtain ⟨z', hz', hz's⟩ : ∃ z' ∈ fwdHull U (s + h), z' ∉ fwdHull U s := by
    by_contra hcon
    push Not at hcon
    exact hne (Set.Subset.antisymm hsub hcon)
  have hM : ∀ x ∈ Icc (0 : ℝ) h, |U (s + x) - U s| ≤ μ / 16 := fun x hx => by
    have := hδU (s + x) (by
      rw [Real.dist_eq, show s + x - s = x by ring, abs_of_nonneg hx.1]
      linarith [hx.2])
    rw [Real.dist_eq] at this
    exact this.le
  have hgrow := QuantumZipper.CoreArc.norm_fwdMap_le_of_mem_diff hU hs hh0.le hM hz' hz's
  have hsq : Real.sqrt h ≤ μ / 16 := by
    calc Real.sqrt h ≤ Real.sqrt ((μ / 16) ^ 2) := Real.sqrt_le_sqrt hhμ
      _ = μ / 16 := Real.sqrt_sq (by positivity)
  have hz'H : z' ∈ H \ fwdHull U s := ⟨hz'.1, hz's⟩
  have hGH : fwdMap U s z' ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hs hz'H
  obtain ⟨z, hz, hGz⟩ := himg (fwdMap U s z') ⟨by
    rw [mem_ball, dist_zero_right]
    linarith, hGH⟩
  have hzs : z ∈ H \ fwdHull U s := ⟨hz.2, fun h' => Set.disjoint_left.1 hd hz.1
    ((QuantumZipper.fwdHull_mono (W := U)).1 hsr.le h')⟩
  have hzz : z = z' := QuantumZipper.FwdHolo.injOn_fwdMap hU hs hzs hz'H hGz
  exact Set.disjoint_left.1 hd (hzz ▸ hz.1)
    ((QuantumZipper.fwdHull_mono (W := U)).1 (by linarith) hz')

/-! ### The tip lies in the closure of the hull -/

/-- A limit of `F_r` at `0` lies in `ℍ̄`. -/
theorem mem_Hbar_of_tendsto (hU : Continuous U) (hU0 : U 0 = 0) {r : ℝ} (hr : 0 ≤ r) {p : ℂ}
    (hp : Tendsto (fwdMapInv U r) (𝓝[H] 0) (𝓝 p)) : p ∈ Hbar := by
  have hH0 : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact zero_mem_Hbar
  rw [← closure_H]
  refine mem_closure_of_tendsto hp ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hr hw

/-- **The tip lies in the closure of the hull.** If `r > 0` and the inverse map `F_r` of the chain
driven by `U` has a limit `p` at the driving point `0`, then `p ∈ closure K_r`. -/
theorem mem_closure_fwdHull_of_tendsto (hU : Continuous U) (hU0 : U 0 = 0) {r : ℝ} (hr : 0 < r)
    {p : ℂ} (hp : Tendsto (fwdMapInv U r) (𝓝[H] 0) (𝓝 p)) : p ∈ closure (fwdHull U r) := by
  have hH0 : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact zero_mem_Hbar
  have hpH : p ∈ Hbar := mem_Hbar_of_tendsto hU hU0 hr.le hp
  by_contra hpc
  by_cases hpH' : p ∈ H
  · -- an interior limit would be a point of `ℍ \ K_r` mapped to `0`
    have hpD : p ∈ H \ fwdHull U r := ⟨hpH', fun h => hpc (subset_closure h)⟩
    have hopen : IsOpen (H \ fwdHull U r) := (isHPHull_fwdHull hU hr.le).isOpen
    have hcont : ContinuousAt (fwdMap U r) p :=
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hU hr.le).differentiableAt
        (hopen.mem_nhds hpD)).continuousAt
    have h1 := hcont.tendsto.comp hp
    have h2 : Tendsto (fun w : ℂ => w) (𝓝[H] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have heq : fwdMap U r p = 0 := by
      refine tendsto_nhds_unique h1 (h2.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact (QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hr.le hw).symm
    have := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hr.le hpD
    rw [heq] at this
    exact lt_irrefl 0 (show (0 : ℝ) < (0 : ℂ).im from this)
  -- a real limit with a hull-free neighbourhood
  have hp0 : p.im = 0 := le_antisymm (not_lt.1 hpH') hpH
  set y := p.re with hy
  have hpy : p = (y : ℂ) := eq_ofReal_re_of_im_eq_zero hp0
  obtain ⟨κ, hκ, hκsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpc
  have hdr : Disjoint (ball (y : ℂ) κ) (fwdHull U r) := by
    rw [← hpy]
    exact Set.disjoint_left.2 fun z hz hzK => hκsub hz (subset_closure hzK)
  rw [hpy] at hp
  -- the reflection at the final time and its minimum on a small circle
  obtain ⟨Kr, hKrd, hKreq, hKrc, -, hKrt⟩ := exists_centred_reflection hU hU0 hr.le hdr
  have hzero := fun z (hz : z ∈ ball (y : ℂ) (κ / 2)) =>
    centred_reflection_eq_zero_iff hU hU0 hr.le hdr hp hKreq hKrc hKrt hz
  have hyb : (y : ℂ) ∈ ball (y : ℂ) (κ / 2) := mem_ball_self (by positivity)
  have hKry : Kr y = 0 := (hzero y hyb).2 rfl
  have hsph_sub : sphere (y : ℂ) (κ / 8) ⊆ ball (y : ℂ) (κ / 2) := fun z hz => by
    rw [mem_sphere] at hz
    rw [mem_ball, hz]
    linarith
  have hsph_ne : (sphere (y : ℂ) (κ / 8)).Nonempty :=
    NormedSpace.sphere_nonempty.2 (by positivity)
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (y : ℂ) (κ / 8)).exists_isMinOn hsph_ne
    ((hKrd.mono hsph_sub).continuousOn.norm)
  set m₀ := ‖Kr z₀‖ with hm₀
  have hm₀pos : 0 < m₀ := by
    refine norm_pos_iff.2 fun h => ?_
    have := (hzero z₀ (hsph_sub hz₀)).1 h
    rw [this, mem_sphere, dist_self] at hz₀
    linarith
  have hmin' : ∀ z ∈ sphere (y : ℂ) (κ / 8), m₀ ≤ ‖Kr z‖ := fun z hz => hmin hz
  -- a time `s < r` at which the reflections are uniformly close
  obtain ⟨δ, hδ, hδU⟩ := Metric.continuous_iff.1 hU r (m₀ / 400) (by positivity)
  set ε := min (r / 2) (min (δ / 2) ((m₀ / 100) ^ 2)) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hεr : ε ≤ r / 2 := min_le_left _ _
  have hεδ : ε ≤ δ / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεm : ε ≤ (m₀ / 100) ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  set s := r - ε with hs
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsr : s < r := by rw [hs]; linarith
  have hrs : r - s = ε := by rw [hs]; ring
  have hM : ∀ x ∈ Icc (0 : ℝ) (r - s), |shiftDrive U s x| ≤ m₀ / 200 := by
    intro x hx
    rw [hrs] at hx
    have h1 := hδU (s + x) (by
      rw [Real.dist_eq, hs, abs_lt]
      constructor <;> linarith [hx.1, hx.2])
    have h2 := hδU s (by
      rw [Real.dist_eq, hs, abs_lt]
      constructor <;> linarith)
    rw [Real.dist_eq] at h1 h2
    show |U (s + x) - U s| ≤ m₀ / 200
    calc |U (s + x) - U s| = |(U (s + x) - U r) - (U s - U r)| := by ring_nf
      _ ≤ |U (s + x) - U r| + |U s - U r| := abs_sub _ _
      _ ≤ m₀ / 200 := by linarith
  have hsq : Real.sqrt (r - s) ≤ m₀ / 100 := by
    rw [hrs]
    calc Real.sqrt ε ≤ Real.sqrt ((m₀ / 100) ^ 2) := Real.sqrt_le_sqrt hεm
      _ = m₀ / 100 := Real.sqrt_sq (by positivity)
  have hds : Disjoint (ball (y : ℂ) κ) (fwdHull U s) :=
    hdr.mono_right ((QuantumZipper.fwdHull_mono (W := U)).1 hsr.le)
  obtain ⟨Ks, hKsd, hKseq, hKsc, hKsr, hKst⟩ := exists_centred_reflection hU hU0 hs0 hds
  have hclose : ∀ z ∈ ball (y : ℂ) (κ / 2), ‖Ks z - Kr z‖ ≤ m₀ / 5 := by
    have hb := norm_sub_le_of_reflections hKseq hKreq hKsc hKrc hKst hKrt (D := 24 * (m₀ / 200) +
      8 * Real.sqrt (r - s)) fun z hz => norm_fwdMap_sub_fwdMap_le hU hs0 hsr hM
        ⟨hz.2, fun h => Set.disjoint_left.1 hdr (ball_subset_ball (by linarith) hz.1) h⟩
    intro z hz
    refine (hb z hz).trans ?_
    linarith
  -- every small value in `ℍ` is a `G_s`-value on the upper half-ball
  have himg : ∀ w ∈ ball (0 : ℂ) (m₀ / 4) ∩ H, ∃ z ∈ ball (y : ℂ) κ ∩ H, fwdMap U s z = w := by
    rintro w ⟨hw, hwH⟩
    rw [mem_ball, dist_zero_right] at hw
    obtain ⟨z, hz, hKz⟩ := exists_eq_zero_of_norm_lt (f := fun z => Ks z - w) (c := (y : ℂ))
      (ρ := κ / 8) (R := κ / 2) (m := m₀ / 2) (by positivity) (by linarith)
      (hKsd.sub_const w) (fun z hz => by
        have h1 := hmin' z hz
        have h2 := hclose z (hsph_sub hz)
        have h3 : ‖Kr z‖ ≤ ‖Ks z - w‖ + ‖Ks z - Kr z‖ + ‖w‖ := by
          calc ‖Kr z‖ = ‖(Ks z - w) - (Ks z - Kr z) + w‖ := by ring_nf
            _ ≤ ‖(Ks z - w) - (Ks z - Kr z)‖ + ‖w‖ := norm_add_le _ _
            _ ≤ ‖Ks z - w‖ + ‖Ks z - Kr z‖ + ‖w‖ := by gcongr; exact norm_sub_le _ _
        show m₀ / 2 < ‖Ks z - w‖
        linarith)
      (by
        have h2 := hclose y hyb
        show ‖Ks y - w‖ < m₀ / 2
        calc ‖Ks y - w‖ = ‖(Ks y - Kr y) - w‖ := by rw [hKry, sub_zero]
          _ ≤ ‖Ks y - Kr y‖ + ‖w‖ := norm_sub_le _ _
          _ < m₀ / 2 := by linarith)
    have hKzw : Ks z = w := sub_eq_zero.1 hKz
    have hzb : z ∈ ball (y : ℂ) (κ / 2) := by
      rw [mem_closedBall] at hz
      rw [mem_ball]
      linarith
    have hz0 : z.im ≠ 0 := fun h0 => by
      have := hKsr z hzb h0
      rw [hKzw] at this
      have hw0 : (0 : ℝ) < w.im := hwH
      linarith
    have hzH : 0 < z.im :=
      ((im_pos_of_centred_reflection hU hs0 hds hKseq hKsc hzb hz0).1).2 (hKzw ▸ hwH)
    exact ⟨z, ⟨ball_subset_ball (by linarith) hzb, hzH⟩, (hKseq ⟨hzb, hzH⟩).symm.trans hKzw⟩
  exact not_disjoint_of_ball_subset_image hU hU0 hs0 hsr (by positivity) himg hdr

end YuanCorollary13

end InteractingSLE
