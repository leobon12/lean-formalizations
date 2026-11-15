import InteractingSLE.Foundations.Loewner.YuanCorollary13Tip

/-!
# Mapping out an initial segment of a continuous Loewner trace ([Yua22] Corollary 1.3)

Packet PROVE-YUAN-M1. Y. Yuan, *Topological characterisations of Loewner traces*, Indiana Univ.
Math. J. 71 (2022), arXiv:2003.05535v4 ([Yua22]), Corollary 1.3: if `η` is a continuous Loewner
trace of `W` and `a ≥ 0`, the shifted driver `W(a + ·) − W(a)` generates the continuous trace
`γ_a = loewnerTip (shiftDrive W a)`, with `F̄_a(γ_a(u)) = η(a + u)`.

`YuanShift.lean` (PROVE-GEO-YUAN) proved everything except left-continuity of `γ_a`. Here it is
proved (`IsLoewnerTrace.continuousWithinAt_shift_Iic`), giving Corollary 1.3 unconditionally
(`IsLoewnerTrace.isLoewnerTrace_shift`).

## Proof of left-continuity (a shorter route than [Yua22] §3)

Write `τ = γ_a`, `ψ(u) = η(a + u) = F̄_a(τ(u))`.

1. **A clean jump across a ray.** If `τ` is not left-continuous at `t₀ > 0`, it has a left cluster
   value `x ≠ τ(t₀)`. Both lie in the fibre of `ψ(t₀)` under `F̄_a`, hence are real (otherwise the
   fibre is a point and `τ` is continuous at `t₀`). Pick `m` strictly between them with
   `F̄_a(m) ≠ ψ(t₀)` (no fibre contains an interval). `F̄_a` keeps the vertical ray `R_m` above `m`
   at a positive distance from `ψ(t₀)`, so near `t₀` no value of `τ`, nor any of its cluster values,
   lies on `R_m`. With the side function `ℓ(w) = (Re w − m)(Re τ(t₀) − m)` and right-continuity, the
   first time `t₁` after a left-side time `q` at which `τ` is on the right side satisfies:
   `ℓ < 0` on the closure of `τ([q, t₁))`, `ℓ(τ(t₁)) > 0`, and `τ(t₁)` is real.
2. **The chart at time `q`.** Let `F'` be the inverse map of the chain shifted by `q`, at time
   `r = t₁ − q`, with hull `A = fill(σ[0, r])` (`σ` the shifted tips, `F̄_q ∘ σ = τ(q + ·)`). Take a
   small half-disc `D` about `0` in the chart at time `t₁`, so `ℓ > 0` on `F_{t₁}(D) = F_q(F'(D))`.
   * `A` does not meet `closure F'(D)`: a point there lies on `closure σ[0, r]` (it is in `A` and
     adherent to `ℍ \ A`), so `F_q` maps it into `closure τ([q, t₁]) ∩ ℍ ⊆ {ℓ < 0}`; but it
     also lies in `closure F_{t₁}(D) ⊆ {ℓ > 0}`.
   * The tip `p = σ(r) = F̄'(0)` lies in `closure F'(D)` and, by
     `mem_closure_fwdHull_of_tendsto`, in `closure A`. Choosing the ends of `D` with `F̄' ≠ p`
     there, a small half-disc about `p` misses the crosscut `F'(∂D ∩ ℍ)`; it meets both `F'(D)`
     and `A`, so it contains a frontier point of `F'(D)` in `ℍ`, which is neither in `A` nor on
     the crosscut. Contradiction.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace YuanCorollary13

/-! ### Shifts of shifts -/

theorem shiftDrive_shiftDrive (W : ℝ → ℝ) (a q : ℝ) :
    shiftDrive (shiftDrive W a) q = shiftDrive W (a + q) := by
  funext r
  simp only [shiftDrive]
  rw [add_assoc]
  ring

/-! ### Fillings: points of the hull adherent to the domain lie on the closure of the set -/

/-- A point of `fill P` adherent to `ℍ \ fill P` lies in `closure P`. -/
theorem mem_closure_of_mem_fillH_of_mem_closure {P : Set ℂ} {v : ℂ} (hv : v ∈ fillH P)
    (hvc : v ∈ closure (H \ fillH P)) : v ∈ closure P := by
  by_contra hvP
  have hvH : v ∈ H := hv.1
  have hbdd : Bornology.IsBounded (connectedComponentIn (H \ closure P) v) :=
    hv.2.resolve_left hvP
  have hopen : IsOpen (H \ closure P) := QuantumZipper.isOpen_H.sdiff isClosed_closure
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hopen v ⟨hvH, hvP⟩
  have hball : ball v ε ⊆ fillH P := by
    intro z hz
    have hzc : z ∈ connectedComponentIn (H \ closure P) v :=
      (isPreconnected_ball.subset_connectedComponentIn (mem_ball_self hε) hεsub) hz
    refine ⟨(hεsub hz).1, Or.inr ?_⟩
    rw [connectedComponentIn_eq hzc] at hbdd
    exact hbdd
  obtain ⟨w, hw, hwb⟩ := Metric.mem_closure_iff.1 hvc ε hε
  exact hw.2 (hball (by rw [mem_ball, dist_comm]; exact hwb))

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-! ### The shifted chains of a Loewner trace -/

/-- **Composition at the boundary.** `F̄^{(a)}_q(γ_{a+q}(u)) = γ_a(q + u)`: the tips of the chain
shifted by `a + q` lie over the tips of the chain shifted by `a`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.extendFrom_shift_shift_tip (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a q u : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hu : 0 ≤ u) :
    extendFrom H (fwdMapInv (shiftDrive W a) q)
        (loewnerTip (shiftDrive (shiftDrive W a) q) u) =
      loewnerTip (shiftDrive W a) (q + u) := by
  set V := shiftDrive W a with hVdef
  have hV : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : V 0 = 0 := shiftDrive_zero W a
  have hVV : shiftDrive V q = shiftDrive W (a + q) := shiftDrive_shiftDrive W a q
  obtain ⟨hσH, -, hσt⟩ := hη.extendFrom_shift_tip hW hW0 (add_nonneg ha hq) hu
  rw [hVV]
  have hFqc : ContinuousOn (extendFrom H (fwdMapInv V q)) Hbar :=
    (hη.hasBdryLimits_shift hW hW0 ha hq).continuousOn
  have hVq : Continuous (shiftDrive W (a + q)) :=
    QuantumZipper.RS.continuous_shiftDrive hW (a + q)
  have hVq0 : shiftDrive W (a + q) 0 = 0 := shiftDrive_zero W (a + q)
  have hin : Tendsto (fwdMapInv (shiftDrive W (a + q)) u) (𝓝[H] 0)
      (𝓝[Hbar] (loewnerTip (shiftDrive W (a + q)) u)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hσt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact H_subset_Hbar (QuantumZipper.RS.fwdMapInv_mem_H hVq hVq0 hu hw)
  have h1 := (hFqc _ hσH).tendsto.comp hin
  have h2 := (hη.extendFrom_shift_tip hW hW0 ha (add_nonneg hq hu)).2.2
  have hH0 : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact zero_mem_Hbar
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hGw := QuantumZipper.RS.fwdMapInv_mem_H hVq hVq0 hu hw
  simp only [Function.comp]
  rw [extendFrom_H_eq (continuousOn_fwdMapInv hV hV0 hq) hGw,
    QuantumZipper.RS.fwdMapInv_add_shift hV hV0 hq hu hw, hVV]

/-- The hulls of the chain shifted by `a + q`, seen from the chain shifted by `a`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.fwdHull_shift_shift_eq (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a q r : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    fwdHull (shiftDrive (shiftDrive W a) q) r =
      fillH (loewnerTip (shiftDrive (shiftDrive W a) q) '' Icc 0 r) := by
  rw [shiftDrive_shiftDrive]
  exact hη.fwdHull_shift_eq hW hW0 (add_nonneg ha hq) hr

/-- The boundary extension `F̄_a` moves points of `ℍ̄` by a bounded amount. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.exists_norm_extendFrom_sub_le
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C, ∀ w ∈ Hbar, ‖extendFrom H (fwdMapInv W a) w - w‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 ha
  refine ⟨C, fun w hw => ?_⟩
  have hcl : w ∈ closure H := by rw [closure_H]; exact hw
  have : (𝓝[H] w).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have ht := (((hη.hasBdryLimits hW hW0 ha).tendsto hw).sub
    (tendsto_id.mono_left nhdsWithin_le_nhds)).norm
  refine le_of_tendsto ht ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  exact hC v hv

/-- **The ray lemma.** If `z` is not a value of `F̄_a` on `ℍ` and `F̄_a(m) ≠ z`, the vertical ray
`{Re = m} ∩ ℍ̄` is mapped by `F̄_a` at a positive distance from `z`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.exists_pos_lt_dist_ray (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a) {m : ℝ} {z : ℂ}
    (hzH : ∀ w ∈ H, extendFrom H (fwdMapInv W a) w ≠ z)
    (hm : extendFrom H (fwdMapInv W a) (m : ℂ) ≠ z) :
    ∃ r₀ > 0, ∀ w ∈ Hbar, w.re = m → r₀ < dist (extendFrom H (fwdMapInv W a) w) z := by
  set F := extendFrom H (fwdMapInv W a) with hF
  have hFc : ContinuousOn F Hbar := (hη.hasBdryLimits hW hW0 ha).continuousOn
  obtain ⟨C, hC⟩ := hη.exists_norm_extendFrom_sub_le hW hW0 ha
  have hne : ∀ w ∈ Hbar, w.re = m → F w ≠ z := by
    intro w hw hwm
    rcases (show 0 ≤ w.im from hw).lt_or_eq with hpos | hzero
    · exact hzH w hpos
    · have : w = (m : ℂ) := Complex.ext (by simp [hwm]) (by simp [← hzero])
      rw [this]; exact hm
  set R := ‖z‖ + C + 2 with hR
  have hfar : ∀ w ∈ Hbar, R < ‖w‖ → 1 < dist (F w) z := by
    intro w hw hwR
    have h1 := hC w hw
    have h2 : ‖w‖ ≤ ‖F w - w‖ + ‖F w - z‖ + ‖z‖ := by
      calc ‖w‖ = ‖(F w - z) - (F w - w) + z‖ := by ring_nf
        _ ≤ ‖(F w - z) - (F w - w)‖ + ‖z‖ := norm_add_le _ _
        _ ≤ ‖F w - z‖ + ‖F w - w‖ + ‖z‖ := by gcongr; exact norm_sub_le _ _
        _ = ‖F w - w‖ + ‖F w - z‖ + ‖z‖ := by ring
    rw [dist_eq_norm]
    linarith
  set K := {w : ℂ | w.re = m} ∩ Hbar ∩ closedBall 0 R with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 R).inter_left
    ((isClosed_eq continuous_re continuous_const).inter isClosed_Hbar)
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun w hw hwm => hfar w hw ?_⟩
    by_contra hle
    have : w ∈ K := ⟨⟨hwm, hw⟩, mem_closedBall_zero_iff.2 (not_lt.1 hle)⟩
    rw [hKe] at this
    exact this
  have hKsub : K ⊆ Hbar := fun w hw => hw.1.2
  have hcont : ContinuousOn (fun w => dist (F w) z) K :=
    (continuous_id.dist continuous_const).comp_continuousOn (hFc.mono hKsub)
  obtain ⟨w₁, hw₁, hmin⟩ := hKc.exists_isMinOn hKne hcont
  have hd₁ : 0 < dist (F w₁) z := dist_pos.2 (hne w₁ hw₁.1.2 hw₁.1.1)
  refine ⟨min 1 (dist (F w₁) z / 2), lt_min one_pos (by positivity), fun w hw hwm => ?_⟩
  by_cases hwR : ‖w‖ ≤ R
  · have h1 : dist (F w₁) z ≤ dist (F w) z :=
      hmin (show w ∈ K from ⟨⟨hwm, hw⟩, mem_closedBall_zero_iff.2 hwR⟩)
    have h2 := min_le_right 1 (dist (F w₁) z / 2)
    linarith
  · have h1 := hfar w hw (not_le.1 hwR)
    have h2 := min_le_left 1 (dist (F w₁) z / 2)
    linarith

/-! ### The chart at an earlier time: no clean jump -/

/-- **No clean jump.** Let `τ = γ_a`, `0 ≤ q < t`, and `ℓ` continuous with `ℓ < 0` on the closure of
`τ([q, t))`, `ℓ(τ(t)) > 0` and `τ(t) ∉ ℍ`. This is impossible (see the module docstring, step 2). -/
theorem _root_.InteractingSLE.IsLoewnerTrace.false_of_jump (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a q t : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q) (hqt : q < t)
    {ℓ : ℂ → ℝ} (hℓ : Continuous ℓ) (hpos : 0 < ℓ (loewnerTip (shiftDrive W a) t))
    (hreal : loewnerTip (shiftDrive W a) t ∉ H)
    (hneg : ∀ w ∈ closure (loewnerTip (shiftDrive W a) '' Ico q t), ℓ w < 0) : False := by
  set V := shiftDrive W a with hVdef
  have hV : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW a
  have hV0 : V 0 = 0 := shiftDrive_zero W a
  set τ := loewnerTip V with hτ
  have ht : 0 ≤ t := hq.trans hqt.le
  -- the chart at time `t`: `ℓ > ℓ(τ t)/2` on the image of a half-disc about `0`
  set Ft := extendFrom H (fwdMapInv V t) with hFt
  have hFtc : ContinuousOn Ft Hbar := (hη.hasBdryLimits_shift hW hW0 ha ht).continuousOn
  obtain ⟨δ, hδ, hδFt⟩ : ∃ δ > 0, ∀ w ∈ Hbar, dist w 0 < δ → ℓ (τ t) / 2 < ℓ (Ft w) := by
    have hcw : ContinuousWithinAt (fun w => ℓ (Ft w)) Hbar 0 :=
      hℓ.continuousAt.comp_continuousWithinAt (hFtc 0 zero_mem_Hbar)
    obtain ⟨δ, hδ, h⟩ := Metric.continuousWithinAt_iff.1 hcw (ℓ (τ t) / 2) (by positivity)
    refine ⟨δ, hδ, fun w hw hwd => ?_⟩
    have h1 := h hw hwd
    have h2 : Ft 0 = τ t := rfl
    rw [Real.dist_eq, h2] at h1
    have := (abs_lt.1 h1).1
    linarith
  -- the chart at time `q`
  set r := t - q with hr
  have hr0 : 0 < r := sub_pos.2 hqt
  have hqr : q + r = t := by rw [hr]; ring
  have hUW : shiftDrive V q = shiftDrive W (a + q) := shiftDrive_shiftDrive W a q
  set U := shiftDrive V q with hU
  have hUc : Continuous U := QuantumZipper.RS.continuous_shiftDrive hV q
  have hU0 : U 0 = 0 := shiftDrive_zero V q
  set F' := fwdMapInv U r with hF'
  set Fq := extendFrom H (fwdMapInv V q) with hFq
  have hFqc : ContinuousOn Fq Hbar := (hη.hasBdryLimits_shift hW hW0 ha hq).continuousOn
  set σ := loewnerTip U with hσ
  set A := fwdHull U r with hA
  have hAfill : A = fillH (σ '' Icc 0 r) := hη.fwdHull_shift_shift_eq hW hW0 ha hq hr0.le
  have hσtip : Tendsto F' (𝓝[H] 0) (𝓝 (σ r)) := by
    have := (hη.extendFrom_shift_tip hW hW0 (add_nonneg ha hq) hr0.le).2.2
    rw [← hUW] at this
    exact this
  have hσH : ∀ u, 0 ≤ u → σ u ∈ Hbar := fun u hu => by
    have := (hη.extendFrom_shift_tip hW hW0 (add_nonneg ha hq) hu).1
    rw [← hUW] at this
    exact this
  have hFqσ : ∀ u, 0 ≤ u → Fq (σ u) = τ (q + u) := fun u hu =>
    hη.extendFrom_shift_shift_tip hW hW0 ha hq hu
  have hpH : σ r ∉ H := by
    intro h
    have h1 := hFqσ r hr0.le
    rw [hqr, hFq, extendFrom_H_eq (continuousOn_fwdMapInv hV hV0 hq) h] at h1
    exact hreal (h1 ▸ QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hq h)
  have hpA : σ r ∈ closure A := YuanCorollary13.mem_closure_fwdHull_of_tendsto hUc hU0 hr0 hσtip
  -- the boundary extension of `F'` and the ends of the half-disc
  set F'' := extendFrom H F' with hF''
  have hF''c : ContinuousOn F'' Hbar := by
    have := (hη.hasBdryLimits_shift hW hW0 (add_nonneg ha hq) hr0.le).continuousOn
    rw [← hUW] at this
    exact this
  have hcb := isConformalBijection_fwdMapInv hUc hU0 hr0.le
  have hF''eq : EqOn F'' F' H := fun x hx => extendFrom_H_eq hcb.1.continuousOn hx
  have hF''d : DifferentiableOn ℂ F'' H := hcb.1.congr hF''eq
  have hF''inj : InjOn F'' H := hcb.2.injOn.congr hF''eq.symm
  obtain ⟨δ₁, hδ₁, hδ₁p⟩ := exists_ne_of_injOn hF''d hF''c hF''inj hδ (σ r)
  obtain ⟨δ₂', hδ₂', hδ₂p⟩ := exists_ne_of_injOn hF''d hF''c hF''inj (neg_lt_zero.2 hδ) (σ r)
  set δ₂ := -δ₂' with hδ₂
  have hδ₂0 : 0 < δ₂ := by rw [hδ₂]; linarith [hδ₂'.2]
  have hδ₂δ : δ₂ < δ := by rw [hδ₂]; linarith [hδ₂'.1]
  have hδ₁0 : 0 < δ₁ := hδ₁.1
  have hδ₁δ : δ₁ < δ := hδ₁.2
  set c₀ : ℝ := (δ₁ - δ₂) / 2 with hc₀
  set ρ₀ : ℝ := (δ₁ + δ₂) / 2 with hρ₀
  set D := ball (c₀ : ℂ) ρ₀ ∩ H with hD
  set S := sphere (c₀ : ℂ) ρ₀ ∩ H with hS
  have hc₀abs : ‖(c₀ : ℂ)‖ = |c₀| := Complex.norm_real c₀
  have hDδ : ∀ w ∈ D, dist w 0 < δ := by
    intro w hw
    have h1 := mem_ball.1 hw.1
    rw [dist_eq_norm] at h1
    have h2 : |c₀| < δ - ρ₀ := by
      rw [hc₀, hρ₀, abs_lt]; constructor <;> linarith
    rw [dist_zero_right]
    calc ‖w‖ ≤ ‖w - c₀‖ + ‖(c₀ : ℂ)‖ := norm_le_norm_sub_add w c₀
      _ < δ := by rw [hc₀abs]; linarith
  have hsmall : ∀ w ∈ H, ‖w‖ < min δ₁ δ₂ → w ∈ D := by
    intro w hw hwn
    refine ⟨?_, hw⟩
    rw [mem_ball, dist_eq_norm]
    have h2 : |c₀| ≤ ρ₀ - min δ₁ δ₂ := by
      rw [hc₀, hρ₀, abs_le]
      constructor <;> [skip; skip] <;>
        rcases le_total δ₁ δ₂ with h | h <;> simp only [min_eq_left, min_eq_right, h] <;> linarith
    calc ‖w - c₀‖ ≤ ‖w‖ + ‖(c₀ : ℂ)‖ := norm_sub_le w c₀
      _ < ρ₀ := by rw [hc₀abs]; linarith
  -- `O = F'(D)` is open, and characterised through `G_r = fwdMap U r`
  set O := F' '' D with hO
  have hOchar : O = (H \ A) ∩ fwdMap U r ⁻¹' D := by
    ext v
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact ⟨QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hUc hU0 hr0.le hd.2, by
        show fwdMap U r (F' d) ∈ D
        rw [hF', QuantumZipper.RS.fwdMap_fwdMapInv hUc hU0 hr0.le hd.2]
        exact hd⟩
    · rintro ⟨hv, hvD⟩
      exact ⟨fwdMap U r v, hvD, QuantumZipper.RS.fwdMapInv_fwdMap hUc hU0 hr0.le hv⟩
  have hAopen : IsOpen (H \ A) := (isHPHull_fwdHull hUc hr0.le).isOpen
  have hGc : ContinuousOn (fwdMap U r) (H \ A) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hUc hr0.le).continuousOn
  have hOopen : IsOpen O := by
    rw [hOchar]
    exact hGc.isOpen_inter_preimage hAopen (isOpen_ball.inter QuantumZipper.isOpen_H)
  have hOsub : O ⊆ H \ A := by rw [hOchar]; exact inter_subset_left
  -- `ℓ ≥ ℓ(τ t)/2` on `F_q(closure O ∩ ℍ)`
  have hcomp : ∀ w ∈ H, fwdMapInv V q (F' w) = fwdMapInv V t w := by
    intro w hw
    rw [← hqr, QuantumZipper.RS.fwdMapInv_add_shift hV hV0 hq hr0.le hw]
  have hOℓ : ∀ v ∈ closure O, v ∈ H → ℓ (τ t) / 2 ≤ ℓ (fwdMapInv V q v) := by
    intro v hv hvH
    have hca : ContinuousAt (fwdMapInv V q) v :=
      (continuousOn_fwdMapInv hV hV0 hq).continuousAt (QuantumZipper.isOpen_H.mem_nhds hvH)
    have h1 := mem_closure_image hca hv
    have hsub : fwdMapInv V q '' O ⊆ {w | ℓ (τ t) / 2 ≤ ℓ w} := by
      rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      rw [hcomp d hd.2]
      have := hδFt d (H_subset_Hbar hd.2) (hDδ d hd)
      rw [hFt, extendFrom_H_eq (continuousOn_fwdMapInv hV hV0 ht) hd.2] at this
      exact this.le
    exact (isClosed_le continuous_const hℓ).closure_subset_iff.2 hsub h1
  -- Claim 1: the hull does not meet `closure O`
  have hclaim1 : ∀ v ∈ A, v ∉ closure O := by
    intro v hvA hvO
    have hvH : v ∈ H := hvA.1
    have hvc : v ∈ closure (H \ A) := closure_mono hOsub hvO
    rw [hAfill] at hvA hvc
    have hvP := mem_closure_of_mem_fillH_of_mem_closure hvA hvc
    have hPH : σ '' Icc 0 r ⊆ Hbar := by
      rintro _ ⟨u, hu, rfl⟩
      exact hσH u hu.1
    have hclH : closure (σ '' Icc 0 r) ⊆ Hbar := isClosed_Hbar.closure_subset_iff.2 hPH
    have h1 := (hFqc.mono hclH).image_closure ⟨v, hvP, rfl⟩
    have himg : Fq '' (σ '' Icc 0 r) ⊆ insert (τ t) (τ '' Ico q t) := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [hFqσ u hu.1]
      rcases hu.2.eq_or_lt with heq | hlt
      · left; rw [heq, hqr]
      · right; exact ⟨q + u, ⟨by linarith [hu.1], by linarith⟩, rfl⟩
    have h2 := closure_mono himg h1
    rw [Set.insert_eq, closure_union, closure_singleton] at h2
    have hFv : Fq v = fwdMapInv V q v := extendFrom_H_eq (continuousOn_fwdMapInv hV hV0 hq) hvH
    have hFvH : Fq v ∈ H := hFv ▸ QuantumZipper.RS.fwdMapInv_mem_H hV hV0 hq hvH
    rcases h2 with h2 | h2
    · exact hreal ((mem_singleton_iff.1 h2) ▸ hFvH)
    · have h3 := hneg _ h2
      have h4 := hOℓ v hvO hvH
      rw [← hFv] at h4
      linarith
  -- Claim 2: the tip `σ r` lies in `closure O`
  have hH0 : (𝓝[H] (0 : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact zero_mem_Hbar
  have hpO : σ r ∈ closure O := by
    refine mem_closure_of_tendsto hσtip ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds
      (ball_mem_nhds (0 : ℂ) (lt_min hδ₁0 hδ₂0))] with w hw hwb
    exact ⟨w, hsmall w hw (by rw [mem_ball, dist_zero_right] at hwb; exact hwb), rfl⟩
  -- Claim 3: a ball about `σ r` misses the crosscut `F'(S)`
  obtain ⟨κ, hκ, hκS⟩ : ∃ κ > 0, ∀ v ∈ ball (σ r) κ, v ∉ F' '' S := by
    set Kc := sphere (c₀ : ℂ) ρ₀ ∩ Hbar with hKc
    have hKcc : IsCompact Kc := (isCompact_sphere _ _).inter_right isClosed_Hbar
    have hclosed : IsClosed (F'' '' Kc) :=
      (hKcc.image_of_continuousOn (hF''c.mono inter_subset_right)).isClosed
    have hsub : F' '' S ⊆ F'' '' Kc := by
      rintro _ ⟨d, hd, rfl⟩
      exact ⟨d, ⟨hd.1, H_subset_Hbar hd.2⟩, hF''eq hd.2⟩
    have hnot : σ r ∉ F'' '' Kc := by
      rintro ⟨k, hk, hkp⟩
      rcases (show 0 ≤ k.im from hk.2).lt_or_eq with hkpos | hk0
      · rw [hF''eq hkpos] at hkp
        exact hpH (hkp ▸ QuantumZipper.RS.fwdMapInv_mem_H hUc hU0 hr0.le hkpos)
      · have hkr : k = (k.re : ℂ) := eq_ofReal_re_of_im_eq_zero hk0.symm
        have hks := hk.1
        rw [mem_sphere, hkr, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs] at hks
        rcases (abs_eq (by positivity)).1 hks with h | h
        · have : k.re = δ₁ := by rw [hc₀, hρ₀] at h; linarith
          rw [hkr, this] at hkp
          exact hδ₁p hkp
        · have : k.re = δ₂' := by rw [hc₀, hρ₀, hδ₂] at h; linarith
          rw [hkr, this] at hkp
          exact hδ₂p hkp
    obtain ⟨κ, hκ, hκsub⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl (σ r) hnot
    exact ⟨κ, hκ, fun v hv hvS => hκsub hv (hsub hvS)⟩
  -- Claim 4: the half-disc about `σ r` crosses the frontier of `O` inside `ℍ`
  have hpre : IsPreconnected (ball (σ r) κ ∩ H) := (convex_ball_inter_H _ _).isPreconnected
  obtain ⟨v₁, hv₁O, hv₁b⟩ := Metric.mem_closure_iff.1 hpO κ hκ
  obtain ⟨v₂, hv₂A, hv₂b⟩ := Metric.mem_closure_iff.1 hpA κ hκ
  obtain ⟨v, hv, hvO, hvcl⟩ : ∃ v ∈ ball (σ r) κ ∩ H, v ∉ O ∧ v ∈ closure O := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw, hwO, hwc⟩ := hpre O (closure O)ᶜ hOopen isClosed_closure.isOpen_compl
      (fun w hw => by
        by_cases hwO : w ∈ O
        · exact Or.inl hwO
        · exact Or.inr (hcon w hw hwO))
      ⟨v₁, ⟨by rw [mem_ball, dist_comm]; exact hv₁b, (hOsub hv₁O).1⟩, hv₁O⟩
      ⟨v₂, ⟨by rw [mem_ball, dist_comm]; exact hv₂b, hv₂A.1⟩, hclaim1 v₂ hv₂A⟩
    exact hwc (subset_closure hwO)
  have hvH : v ∈ H := hv.2
  by_cases hvA : v ∈ A
  · exact hclaim1 v hvA hvcl
  have hvD : v ∈ H \ A := ⟨hvH, hvA⟩
  set d := fwdMap U r v with hd
  have hdH : d ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hUc hr0.le hvD
  have hvd : F' d = v := QuantumZipper.RS.fwdMapInv_fwdMap hUc hU0 hr0.le hvD
  have hdcl : d ∈ closure D := by
    have hca : ContinuousAt (fwdMap U r) v := hGc.continuousAt (hAopen.mem_nhds hvD)
    have h1 := mem_closure_image hca hvcl
    refine closure_mono ?_ h1
    rintro _ ⟨w, hw, rfl⟩
    rw [hOchar] at hw
    exact hw.2
  have hdS : d ∈ S := by
    have h1 : d ∈ closedBall (c₀ : ℂ) ρ₀ := closure_minimal (inter_subset_left.trans
      ball_subset_closedBall) isClosed_closedBall hdcl
    have h2 : d ∉ ball (c₀ : ℂ) ρ₀ := fun h => hvO ⟨d, ⟨h, hdH⟩, hvd⟩
    refine ⟨?_, hdH⟩
    rw [mem_sphere]
    rw [mem_closedBall] at h1
    rw [mem_ball, not_lt] at h2
    exact le_antisymm h1 h2
  exact hκS v hv.1 ⟨d, hdS, hvd⟩

/-! ### Left-continuity of the shifted trace -/

/-- Continuity on `[0, ∞)` at a positive time gives left-continuity. -/
theorem continuousWithinAt_Iic_of_Ici {f : ℝ → ℂ} {s : ℝ} (hs : 0 < s)
    (h : ContinuousWithinAt f (Ici 0) s) : ContinuousWithinAt f (Iic s) s :=
  h.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hs))

/-- **Left-continuity of the shifted trace** (the missing step M1 of `YuanShift.lean`): for a
continuous Loewner trace `η` of `W` and `a ≥ 0`, the tips `γ_a = loewnerTip (shiftDrive W a)` of the
chain shifted by `a` are left-continuous at every positive time. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.continuousWithinAt_shift_Iic
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {a t₀ : ℝ} (ha : 0 ≤ a)
    (ht₀ : 0 < t₀) : ContinuousWithinAt (loewnerTip (shiftDrive W a)) (Iic t₀) t₀ := by
  set V := shiftDrive W a with hVdef
  have hV : Continuous V := QuantumZipper.RS.continuous_shiftDrive hW a
  set τ := loewnerTip V with hτ
  set Fa := extendFrom H (fwdMapInv W a) with hFa
  obtain ⟨hFad, hFac, hFainj, -⟩ := hη.fiber_hyps hW hW0 ha
  have hτH : ∀ u, 0 ≤ u → τ u ∈ Hbar := fun u hu => (hη.extendFrom_shift_tip hW hW0 ha hu).1
  have hFaτ : ∀ u, 0 ≤ u → Fa (τ u) = η (a + u) := fun u hu =>
    (hη.extendFrom_shift_tip hW hW0 ha hu).2.1
  have hFaH : ∀ w ∈ H, Fa w ∈ H \ fwdHull W a := fun w hw => by
    rw [hFa, extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ha) hw]
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ha hw
  -- `ψ = η(a + ·)` is continuous at every time
  have hψ : ∀ u, 0 ≤ u → ContinuousWithinAt (fun v => η (a + v)) (Ici 0) u := by
    intro u hu
    have h1 := hη.2.1 (a + u) (add_nonneg ha hu)
    have h2 : Tendsto (fun v : ℝ => a + v) (𝓝[Ici 0] u) (𝓝[Ici 0] (a + u)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_const.add continuous_id).tendsto u).mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact add_nonneg ha hv
    exact h1.tendsto.comp h2
  by_contra hnc
  -- if `ψ(t₀)` is an interior point, `τ` is continuous at `t₀`
  have hint : η (a + t₀) ∉ H \ fwdHull W a := fun h =>
    hnc (continuousWithinAt_Iic_of_Ici ht₀
      (hη.continuousWithinAt_shift_of_mem hW hW0 ha ht₀.le h))
  have hreal : ∀ w ∈ Hbar, Fa w = η (a + t₀) → w.im = 0 := by
    intro w hw hFw
    rcases (show 0 ≤ w.im from hw).lt_or_eq with hpos | hzero
    · exact absurd (hFw ▸ hFaH w hpos) hint
    · exact hzero.symm
  -- a left cluster value `x ≠ τ(t₀)`
  have hnc' := hnc
  rw [← continuousWithinAt_Iio_iff_Iic, ContinuousWithinAt, Metric.tendsto_nhds] at hnc'
  push Not at hnc'
  obtain ⟨ε₀, hε₀, hfreq⟩ := hnc'
  set y₀ := τ t₀ with hy₀
  set L := 𝓝[<] t₀ ⊓ 𝓟 {v | ε₀ ≤ dist (τ v) y₀} with hL
  have hLne : L.NeBot := frequently_iff_neBot.1 hfreq
  have hLle : L ≤ 𝓝[<] t₀ := inf_le_left
  have hLev : ∀ᶠ v in L, v ∈ Ioo 0 t₀ := hLle (Ioo_mem_nhdsLT ht₀)
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_continuous hV t₀
  set R := 24 * M + 8 * Real.sqrt t₀ with hR
  set Kc := closedBall (0 : ℂ) R ∩ Hbar ∩ {w | ε₀ ≤ dist w y₀} with hKc
  have hKcc : IsCompact Kc := ((isCompact_closedBall _ _).inter_right isClosed_Hbar).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hmapK : Filter.map τ L ≤ 𝓟 Kc := by
    rw [Filter.map_le_iff_le_comap, Filter.comap_principal, Filter.le_principal_iff]
    filter_upwards [hLev, inf_le_right (a := 𝓝[<] t₀) (mem_principal_self _)] with v hv hvε
    refine ⟨⟨mem_closedBall_zero_iff.2 ?_, hτH v hv.1.le⟩, hvε⟩
    refine (hη.norm_shift_tip_le hW hW0 ha hv.1.le fun r hr => hM r ⟨hr.1, ?_⟩).trans ?_
    · exact hr.2.trans hv.2.le
    · rw [hR]; gcongr; exact hv.2.le
  obtain ⟨x, hxK, hxcl⟩ := hKcc.exists_mapClusterPt hmapK
  have hxH : x ∈ Hbar := hxK.1.2
  have hLIci : Tendsto (fun v : ℝ => v) L (𝓝[Ici 0] t₀) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_id.mono_left (hLle.trans nhdsWithin_le_nhds),
      hLev.mono fun v hv => show (0 : ℝ) ≤ v from hv.1.le⟩
  have hFx : Fa x = η (a + t₀) := by
    refine eq_of_mapClusterPt hFac (hLev.mono fun v hv => hτH v hv.1.le) ?_ hxH hxcl
    refine ((hψ t₀ ht₀.le).tendsto.comp hLIci).congr' ?_
    filter_upwards [hLev] with v hv
    exact (hFaτ v hv.1.le).symm
  have hx0 : x.im = 0 := hreal x hxH hFx
  have hy₀0 : y₀.im = 0 := hreal y₀ (hτH t₀ ht₀.le) (hFaτ t₀ ht₀.le)
  have hxy : x.re ≠ y₀.re := by
    intro h
    have hxy' : x = y₀ := Complex.ext h (by rw [hx0, hy₀0])
    have h2 : ε₀ ≤ dist x y₀ := hxK.2
    rw [hxy', dist_self] at h2
    linarith
  -- the ray `Re = m` between them
  obtain ⟨m, hm, hFm⟩ := exists_ne_of_injOn hFad hFac hFainj (min_lt_max.2 hxy) (η (a + t₀))
  set ℓ : ℂ → ℝ := fun w => (w.re - m) * (y₀.re - m) with hℓ
  have hℓc : Continuous ℓ := by rw [hℓ]; fun_prop
  have hym : y₀.re ≠ m := by
    intro h
    rcases le_total x.re y₀.re with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hm; linarith [hm.2]
    · rw [min_eq_right hle, max_eq_left hle] at hm; linarith [hm.1]
  have hℓy : 0 < ℓ y₀ := mul_self_pos.2 (sub_ne_zero.2 hym)
  have hℓx : ℓ x < 0 := by
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hm
      exact mul_neg_of_neg_of_pos (by linarith [hm.1]) (by linarith [hm.2])
    · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hm
      exact mul_neg_of_pos_of_neg (by linarith [hm.2]) (by linarith [hm.1])
  have hℓ0 : ∀ w, ℓ w = 0 → w.re = m := fun w hw => by
    rcases mul_eq_zero.1 hw with h | h
    · linarith
    · exact absurd (sub_eq_zero.1 h) hym
  obtain ⟨r₀, hr₀, hray⟩ := hη.exists_pos_lt_dist_ray hW hW0 ha
    (fun w hw h => hint (by rw [← h]; exact hFaH w hw)) hFm
  -- a left neighbourhood on which `ψ` stays near `ψ(t₀)`
  obtain ⟨q₀, hq₀0, hq₀t, hq₀ψ⟩ : ∃ q₀, 0 ≤ q₀ ∧ q₀ < t₀ ∧
      ∀ u ∈ Icc q₀ t₀, dist (η (a + u)) (η (a + t₀)) < r₀ / 2 := by
    obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 (hψ t₀ ht₀.le) (r₀ / 2) (by positivity)
    refine ⟨max 0 (t₀ - δ / 2), le_max_left _ _, max_lt ht₀ (by linarith), fun u hu => ?_⟩
    refine hδψ ((le_max_left _ _).trans hu.1) ?_
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [le_max_right 0 (t₀ - δ / 2), hu.1, hu.2]
  have hRay : ∀ w ∈ closure (τ '' Icc q₀ t₀), w ∈ Hbar ∧ w.re ≠ m := by
    have hsub : τ '' Icc q₀ t₀ ⊆ Hbar := by
      rintro _ ⟨u, hu, rfl⟩; exact hτH u (hq₀0.trans hu.1)
    have hclH : closure (τ '' Icc q₀ t₀) ⊆ Hbar := isClosed_Hbar.closure_subset_iff.2 hsub
    intro w hw
    refine ⟨hclH hw, fun hwm => ?_⟩
    have h1 := (hFac.mono hclH).image_closure ⟨w, hw, rfl⟩
    have hball : Fa '' (τ '' Icc q₀ t₀) ⊆ closedBall (η (a + t₀)) (r₀ / 2) := by
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [hFaτ u (hq₀0.trans hu.1), mem_closedBall]
      exact (hq₀ψ u hu).le
    have h2 := isClosed_closedBall.closure_subset_iff.2 hball h1
    rw [mem_closedBall] at h2
    have h3 := hray w (hclH hw) hwm
    linarith
  -- a time `q₁ ∈ [q₀, t₀)` on the left side
  obtain ⟨q₁, hq₁, hℓq₁⟩ : ∃ q₁ ∈ Ico q₀ t₀, ℓ (τ q₁) < 0 := by
    have hfr := hxcl.frequently ((isOpen_lt hℓc continuous_const).mem_nhds hℓx)
    obtain ⟨v, hv1, hv2⟩ := (hfr.and_eventually (hLle (Ioo_mem_nhdsLT hq₀t))).exists
    exact ⟨v, ⟨hv2.1.le, hv2.2⟩, hv1⟩
  -- the first time `t₁ ≥ q₁` on the right side
  set T := {u | u ∈ Icc q₁ t₀ ∧ 0 < ℓ (τ u)} with hT
  have hT0 : t₀ ∈ T := ⟨⟨hq₁.2.le, le_rfl⟩, hℓy⟩
  have hTbdd : BddBelow T := ⟨q₁, fun u hu => hu.1.1⟩
  set t₁ := sInf T with ht₁
  have ht₁le : t₁ ≤ t₀ := csInf_le hTbdd hT0
  have hq₁t₁ : q₁ ≤ t₁ := le_csInf ⟨t₀, hT0⟩ fun u hu => hu.1.1
  have hside : ∀ u ∈ Icc q₁ t₀, ℓ (τ u) ≠ 0 := fun u hu h0 =>
    (hRay (τ u) (subset_closure ⟨u, ⟨hq₁.1.trans hu.1, hu.2⟩, rfl⟩)).2 (hℓ0 _ h0)
  have hbelow : ∀ u ∈ Ico q₁ t₁, ℓ (τ u) < 0 := by
    intro u hu
    have hu' : u ∈ Icc q₁ t₀ := ⟨hu.1, hu.2.le.trans ht₁le⟩
    have hnT : u ∉ T := notMem_of_lt_csInf hu.2 hTbdd
    have hle : ℓ (τ u) ≤ 0 := not_lt.1 fun h => hnT ⟨hu', h⟩
    exact lt_of_le_of_ne hle (hside u hu')
  have hq₁0 : 0 ≤ q₁ := hq₀0.trans hq₁.1
  have ht₁T : t₁ ∈ T := by
    by_contra hn
    have ht₁I : t₁ ∈ Icc q₁ t₀ := ⟨hq₁t₁, ht₁le⟩
    have hlt : ℓ (τ t₁) < 0 :=
      lt_of_le_of_ne (not_lt.1 fun h => hn ⟨ht₁I, h⟩) (hside t₁ ht₁I)
    have hrc := hη.continuousWithinAt_shift_Ici hW hW0 ha (hq₁0.trans hq₁t₁)
    have hev : ∀ᶠ u in 𝓝[≥] t₁, ℓ (τ u) < 0 :=
      (hℓc.continuousAt.comp_continuousWithinAt hrc).eventually_lt continuousWithinAt_const hlt
    obtain ⟨u', hu', hu'sub⟩ := (mem_nhdsGE_iff_exists_Ico_subset' (lt_add_one t₁)).1 hev
    obtain ⟨u, huT, huu'⟩ := exists_lt_of_csInf_lt ⟨t₀, hT0⟩ (show sInf T < u' from hu')
    have := hu'sub ⟨csInf_le hTbdd huT, huu'⟩
    exact absurd huT.2 (not_lt.2 this.le)
  have hq₁lt : q₁ < t₁ := lt_of_le_of_ne hq₁t₁ fun h => by
    have := ht₁T.2
    rw [← h] at this
    linarith
  have ht₁0 : 0 < t₁ := lt_of_le_of_lt hq₁0 hq₁lt
  have hneg : ∀ w ∈ closure (τ '' Ico q₁ t₁), ℓ w < 0 := by
    intro w hw
    have hsub : Ico q₁ t₁ ⊆ Icc q₀ t₀ := fun u hu => ⟨hq₁.1.trans hu.1, hu.2.le.trans ht₁le⟩
    have hw' : w ∈ closure (τ '' Icc q₀ t₀) := closure_mono (image_mono hsub) hw
    have hle : ℓ w ≤ 0 := by
      refine (isClosed_le hℓc continuous_const).closure_subset_iff.2 ?_ hw
      rintro _ ⟨u, hu, rfl⟩
      exact (hbelow u hu).le
    exact lt_of_le_of_ne hle fun h0 => (hRay w hw').2 (hℓ0 w h0)
  have hrealt₁ : τ t₁ ∉ H := by
    intro hH
    have h1 : η (a + t₁) ∈ H \ fwdHull W a := hFaτ t₁ ht₁0.le ▸ hFaH _ hH
    have hc := continuousWithinAt_Iic_of_Ici ht₁0
      (hη.continuousWithinAt_shift_of_mem hW hW0 ha ht₁0.le h1)
    have hev : ∀ᶠ u in 𝓝[≤] t₁, 0 < ℓ (τ u) :=
      ((hℓc.continuousAt.comp_continuousWithinAt hc).eventually_const_lt ht₁T.2).mono
        fun u hu => hu
    have hev' : ∀ᶠ u in 𝓝[<] t₁, 0 < ℓ (τ u) ∧ u ∈ Ioo q₁ t₁ :=
      Filter.Eventually.and (nhdsWithin_mono _ Iio_subset_Iic_self hev) (Ioo_mem_nhdsLT hq₁lt)
    obtain ⟨u, hu1, hu2⟩ := hev'.exists
    exact absurd hu1 (not_lt.2 (hbelow u ⟨hu2.1.le, hu2.2⟩).le)
  exact hη.false_of_jump hW hW0 ha hq₁0 hq₁lt hℓc ht₁T.2 hrealt₁ hneg

/-! ### Corollary 1.3 -/

/-- **[Yua22] Corollary 1.3.** If `η` is a continuous Loewner trace of the continuous driver `W`
(`W 0 = 0`) and `a ≥ 0`, the shifted driver `W(a + ·) − W(a)` generates the continuous trace
`γ_a = loewnerTip (shiftDrive W a)`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.isLoewnerTrace_shift (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a) :
    IsLoewnerTrace (shiftDrive W a) (loewnerTip (shiftDrive W a)) :=
  hη.isLoewnerTrace_shift_of_left hW hW0 ha fun _ hs =>
    hη.continuousWithinAt_shift_Iic hW hW0 ha hs

/-- **[Yua22] Corollary 1.3 with the fibre identity**: `γ_a` is a continuous Loewner trace of the
shifted driver and lies over the future of `η`: `F̄_a(γ_a(u)) = η(a + u)` for `u ≥ 0`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.isLoewnerTrace_shift_and_extendFrom
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a) :
    IsLoewnerTrace (shiftDrive W a) (loewnerTip (shiftDrive W a)) ∧
      ∀ u, 0 ≤ u → extendFrom H (fwdMapInv W a) (loewnerTip (shiftDrive W a) u) = η (a + u) :=
  ⟨hη.isLoewnerTrace_shift hW hW0 ha, fun _ hu => (hη.extendFrom_shift_tip hW hW0 ha hu).2.1⟩

end YuanCorollary13

end InteractingSLE
