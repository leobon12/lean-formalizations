/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4RelSpace
import InteractingSLE.Spec.Supplement.GB11ChartBdry
import InteractingSLE.Spec.ZhanGT4.A2TipSepGeom
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Theorem GW4: the relative clock of the component counterflow (deterministic)

Packet PROVE-GW4-RELLAW. Two deterministic steps of Theorem GW4's proof (p. 639: "The relative endpoint is the
designated `x_C`, hence is infinity in the reversed chart. … At a proposed finite relative lifetime, integrated
nonexplosion and bounded-coordinate localization would bound the whole relative hull, contradicting that endpoint.
The relative lifetime is infinite."):

* **`exists_far_relHullFam`** (the relative endpoint is infinity): for the walks' barrier and pocket shape, the
  bounded relative hulls `A(t) = Φ(K'_t ∩ R⁻¹(C))` of the ambient counterflow are not uniformly bounded. Trace points
  in open `C` accumulate at the exit `x_C` before the exit time (GB11's density of open-`C` visits; continuity at the
  exit time, or transience when `x_C = 0` is never visited), and the component chart tends to `0` at `x_C` (the
  pocket coordinate of `GB11Chart`, continuous at `x_C`), so `Φ = −1/c(−1/·)` of these points is unbounded; `A(t)` is
  bounded before the exit time (`GW4Reg.isBounded_relHull`).
* **`exists_clock_of_versions`** (integrated nonexplosion): if a driver `W_C` continuous on `[0, ∞)` agrees with
  drivers `R m` before stops `V m`, every hull of `R m` before `V m` is some `A(t)`, every bounded `A(t)` is reached
  before some `V m`, and the bounded `A(t)` are not uniformly bounded, then the stops exhaust `[0, ∞)` (otherwise all
  bounded `A(t)` would lie in the bounded hull of `W_C` at time `sup V m`), and every hull of `W_C` is some `A(T s)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE

namespace Theorem14

namespace GW4Rel

open GW4Traverse GW4Reg

/-! ### Integrated nonexplosion: the clock of the component counterflow -/

/-- Drivers agreeing before a stop have the same hulls at every earlier time. -/
theorem fwdHull_eq_of_eq_before {f g : ℝ≥0 → ℝ} {V : ℝ≥0∞} (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < V → f t = g t)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < V) :
    fwdHull (fun r : ℝ => f r.toNNReal) s = fwdHull (fun r : ℝ => g r.toNNReal) s := by
  obtain ⟨q, hsq, hqV⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hsq' : (s : ℝ) < q := by exact_mod_cast ENNReal.coe_lt_coe.1 hsq
  refine fwdHull_eq_of_eqOn (NNReal.coe_nonneg s) hsq' fun r hr => h _ ?_
  refine lt_of_le_of_lt ?_ hqV
  exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)

/-- **The clock of the component counterflow from exhausting versions** (integrated nonexplosion). Let `W_C` be a
continuous driver, and `R m`, `V m` drivers and stops with: `W_C = R m` before `V m`; every hull of `R m` before
`V m` is a member of a family `A`; every bounded member of `A` is the hull of some `R m` before `V m`; the bounded
members of `A` are not uniformly bounded. Then every hull of `W_C` is a member of `A`. -/
theorem exists_clock_of_versions {cf : ℝ≥0 → ℝ} (hcf : Continuous cf) {A : ℝ≥0 → Set ℂ}
    {R : ℕ → ℝ≥0 → ℝ} {V : ℕ → ℝ≥0∞} (heq : ∀ m (t : ℝ≥0), (t : ℝ≥0∞) < V m → cf t = R m t)
    (hver : ∀ m (s : ℝ≥0), (s : ℝ≥0∞) < V m → ∃ t, fwdHull (fun r : ℝ => R m r.toNNReal) s = A t)
    (hex : ∀ t, Bornology.IsBounded (A t) → ∃ m, ∃ s : ℝ≥0, (s : ℝ≥0∞) < V m ∧
      fwdHull (fun r : ℝ => R m r.toNNReal) s = A t)
    (hfar : ∀ M : ℝ, ∃ t, Bornology.IsBounded (A t) ∧ ¬ A t ⊆ closedBall 0 M) :
    ∃ T : ℝ≥0 → ℝ≥0, ∀ s : ℝ≥0, fwdHull (fun r : ℝ => cf r.toNNReal) s = A (T s) := by
  have hsame : ∀ m (s : ℝ≥0), (s : ℝ≥0∞) < V m →
      fwdHull (fun r : ℝ => cf r.toNNReal) s = fwdHull (fun r : ℝ => R m r.toNNReal) s :=
    fun m s hs => fwdHull_eq_of_eq_before (heq m) hs
  -- the stops exhaust `[0, ∞)`
  have hall : ∀ s : ℝ≥0, ∃ m, (s : ℝ≥0∞) < V m := by
    intro s₀
    by_contra hcon
    push Not at hcon
    have hcfr : Continuous fun r : ℝ => cf r.toNNReal := hcf.comp continuous_real_toNNReal
    -- the hull of `W_C` at `s₀ + 1` is bounded
    obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := (s₀ : ℝ) + 1)).exists_bound_of_continuousOn
      hcfr.continuousOn
    have hpos : (0 : ℝ) < (s₀ : ℝ) + 1 := by positivity
    have hball := QuantumZipper.CaraR.fwdHull_subset_closedBall hcfr hpos (M := M₀) fun r hr => by
      have := hM₀ r hr
      rwa [Real.norm_eq_abs] at this
    obtain ⟨t, htb, htfar⟩ := hfar (M₀ + 3 * Real.sqrt ((s₀ : ℝ) + 1))
    obtain ⟨m, s, hs, hAs⟩ := hex t htb
    refine htfar ?_
    rw [← hAs, ← hsame m s hs]
    refine (QuantumZipper.fwdHull_mono.1 ?_).trans hball
    have h1 : (s : ℝ≥0∞) < s₀ := lt_of_lt_of_le hs (hcon m)
    have h2 : (s : ℝ) < s₀ := by exact_mod_cast ENNReal.coe_lt_coe.1 h1
    linarith
  choose mOf hmOf using hall
  choose T hT using fun s => hver (mOf s) s (hmOf s)
  exact ⟨T, fun s => (hsame (mOf s) s (hmOf s)).trans (hT s)⟩

/-! ### The relative endpoint is infinity -/

section Far

variable {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {s₁ t₁ : ℝ≥0} {E : Set ℂ} {ψ G : ℂ → ℂ} {k : ℝ}

/-- On the pocket, the component chart is the pocket coordinate up to the factor `k`: `c(z) = ψ(z)/k`. -/
theorem chart_eq_of_isPocketCoord (hc : IsComponentChart (range αR) (range αL) C c)
    (hpc : GB11Chart.IsPocketCoord αR αL C c s₁ t₁ E ψ G k) {z : ℂ} (hz : z ∈ C) :
    ψ z = (k : ℂ) * c.1 z := by
  have hcz : c.1 z ∈ H := hc.2.1 hz
  have hinv : c.2.1 (c.1 z) = z := hc.2.2.2.1.1 hz
  have hG : G ((k : ℂ) * c.1 z) = z := by rw [← hpc.inv_eq _ hcz, hinv]
  have hbar : (k : ℂ) * c.1 z ∈ Hbar := by
    show 0 ≤ ((k : ℂ) * c.1 z).im
    have hk : 0 < k := hpc.pos
    have him : 0 < (c.1 z).im := hcz
    rw [Complex.im_ofReal_mul]
    exact mul_nonneg hk.le him.le
  calc ψ z = ψ (G ((k : ℂ) * c.1 z)) := by rw [hG]
    _ = (k : ℂ) * c.1 z := hpc.left_inv _ hbar

/-- **The component chart tends to `0` at the exit**: for a pocket coordinate continuous at the exit `α_R(s₁)`
(outside the excluded entry set `E`), points of `C` close to the exit have small chart values. -/
theorem exists_norm_chart_lt (hc : IsComponentChart (range αR) (range αL) C c)
    (hpc : GB11Chart.IsPocketCoord αR αL C c s₁ t₁ E ψ G k) (hx : αR s₁ ∈ closure C \ E)
    (hCE : ∀ z ∈ C, z ∉ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ C, ‖z - αR s₁‖ < δ → ‖c.1 z‖ < ε := by
  have hk : 0 < k := hpc.pos
  have hψ0 : ψ (αR s₁) = 0 := by
    have h0 : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
    rw [← hpc.G_zero, hpc.left_inv 0 h0]
  obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousWithinAt_iff.1 (hpc.continuousOn_ψ _ hx) (k * ε) (by positivity)
  refine ⟨δ, hδ, fun z hz hzd => ?_⟩
  have hz' : z ∈ closure C \ E := ⟨subset_closure hz, hCE z hz⟩
  have h1 := hδψ hz' (by rwa [dist_eq_norm])
  rw [dist_eq_norm, hψ0, sub_zero, chart_eq_of_isPocketCoord hc hpc hz, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hk] at h1
  exact lt_of_mul_lt_mul_left h1 hk.le

/-- **The relative endpoint is infinity** (Theorem GW4, p. 639): for the walks' barrier and pocket shape, the bounded
relative hulls `A(t) = Φ(K'_t ∩ R⁻¹(C))` of the ambient counterflow are not uniformly bounded. -/
theorem exists_far_relHullFam {W' : ℝ≥0 → ℝ} (hW' : Continuous W') (hW'0 : W' 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W' ⊤ γ) (hγt : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (hno : GB10.NoSimpleArcInterval γ ⊤) (hB : GB11.IsGB11Barrier αR αL γ) (hP : WalkPocketShape αR αL)
    (hC : C ∈ betweenComponents (range αR) (range αL)) (hc : IsComponentChart (range αR) (range αL) C c)
    (M : ℝ) :
    ∃ t : ℝ≥0, Bornology.IsBounded (relHullFam c C W' t) ∧ ¬ relHullFam c C W' t ⊆ closedBall 0 M := by
  obtain ⟨s₁', t₁', s₂, t₂, hs⟩ := hP.1 C hC
  obtain ⟨xC, hxC, -, -⟩ := hc.2.2.2.2.1 0
  have hxC' : Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) := by simpa only [Complex.ofReal_zero] using hxC
  have hx : xC = αR s₁' := hP.2.1 C hC s₁' t₁' s₂ t₂ hs c hc xC hxC'
  subst hx
  obtain ⟨hfR, hfL, hord, -, -, -, -⟩ := id hB
  have hγc := GW4Reg.continuous_of_isGeneratingTrace_top hγ
  have hCsub : C ⊆ H \ (range αR ∪ range αL) := by
    obtain ⟨z, -, -, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  -- the chart near the exit
  have hnear : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ C, ‖z - αR s₁'‖ < δ → ‖c.1 z‖ < ε := by
    intro ε hε
    by_cases hs₂ : s₂ = ⊤
    · obtain ⟨ψ, G, k, hpc, -, -⟩ :=
        GB11Chart.exists_isPocketCoord_of_unbounded hfR hfL hord hC hs hs₂ hc hxC'
      exact exists_norm_chart_lt hc hpc ⟨hs.mem_closure_exit, notMem_empty _⟩ (fun z _ => notMem_empty z) hε
    · obtain ⟨ψ, G, k, hpc, -, -⟩ :=
        GB11Chart.exists_isPocketCoord_of_bounded hfR hfL hord hC hs hs₂ hc hxC'
      refine exists_norm_chart_lt hc hpc ⟨hs.mem_closure_exit, fun hmem => ?_⟩ (fun z hz hzE => ?_) hε
      · have heq : αR s₁' = αR s₂.toNNReal := hmem
        have hlt' : (s₁' : ℝ≥0∞) < (s₂.toNNReal : ℝ≥0∞) := by
          rw [ENNReal.coe_toNNReal hs₂]
          exact hs.lt
        exact (ENNReal.coe_lt_coe.1 hlt').ne (hfR.2.1 heq)
      · have hzE' : z = αR s₂.toNNReal := hzE
        exact (hCsub hz).2 (Or.inl ⟨_, hzE'.symm⟩)
  -- trace points of open `C` close to the exit, before the exit time
  have hclose : ∀ δ > 0, ∃ t : ℝ≥0, (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁') ∧ γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C ∧
      ‖-(γ t)⁻¹ - αR s₁'‖ < δ := by
    intro δ hδ
    have hτσ := entryTime_lt_firstVisit hγ.1 hγc hB hs
    rcases eq_or_ne (GB11.firstVisit γ (αR s₁')) ⊤ with hσ | hσ
    · -- the exit is never visited: it is the target `0`, and the trace is transient
      have hs0 : s₁' = 0 := by
        by_contra h0
        exact (hB.firstVisit_lt_top_R (pos_iff_ne_zero.2 h0)).ne hσ
      have hx0 : αR s₁' = 0 := by rw [hs0]; exact hfR.2.2.1
      obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hγt.eventually (eventually_gt_atTop (1 / δ)))
      set a : ℝ≥0 := max (entryTime γ αR s₂) T₀ with ha
      obtain ⟨t, ⟨hat, -⟩, hγt0, htC⟩ := exists_mem_of_traversal hW' hW'0 hγ hno hB hP hC hs a (a + 1)
        (le_max_left _ _) (lt_add_one a) (by rw [hσ]; exact ENNReal.coe_lt_top)
      refine ⟨t, by rw [hσ]; exact ENNReal.coe_lt_top, hγt0, htC, ?_⟩
      rw [hx0, sub_zero, norm_neg, norm_inv]
      have h1 := hT₀ t (le_trans (le_max_right _ _) hat.le)
      rw [inv_lt_comm₀ (norm_pos_iff.2 hγt0) hδ]
      simpa only [one_div] using h1
    · obtain ⟨tσ, htσ, hγσ, hzσ⟩ := exists_eq_firstVisit hγc (lt_top_iff_ne_top.2 hσ)
      have hcont : ContinuousAt (fun t => -(γ t)⁻¹) tσ := (hγc.continuousAt.inv₀ hγσ).neg
      have hτσ' : entryTime γ αR s₂ < tσ := by
        rw [← htσ] at hτσ
        exact_mod_cast hτσ
      have hev : (fun t => -(γ t)⁻¹) ⁻¹' ball (αR s₁') δ ∈ 𝓝[<] tσ := by
        have h1 := hcont.tendsto
        rw [hzσ] at h1
        exact nhdsWithin_le_nhds (h1 (ball_mem_nhds _ hδ))
      obtain ⟨l, hl, hlsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hτσ').1 hev
      have ha : max (entryTime γ αR s₂) l < tσ := max_lt hτσ' hl
      obtain ⟨b, hab, hbσ⟩ := exists_between ha
      obtain ⟨t, ⟨hat, htb⟩, hγt0, htC⟩ := exists_mem_of_traversal hW' hW'0 hγ hno hB hP hC hs _ b
        (le_max_left _ _) hab (by rw [← htσ]; exact_mod_cast hbσ)
      refine ⟨t, by rw [← htσ]; exact_mod_cast htb.trans hbσ, hγt0, htC, ?_⟩
      have h2 := hlsub ⟨lt_of_le_of_lt (le_max_right _ _) hat, htb.trans hbσ⟩
      rw [mem_preimage, mem_ball, dist_eq_norm] at h2
      exact h2
  -- a far relative hull before the exit time
  obtain ⟨δ, hδ, hδc⟩ := hnear (1 / (|M| + 1)) (by positivity)
  obtain ⟨t, htσ, hγt0, hzC, hzd⟩ := hclose δ hδ
  refine ⟨t, isBounded_relHull hW' hW'0 hγ hB hc hxC' htσ, fun hsub => ?_⟩
  have hzH : -(γ t)⁻¹ ∈ H := (hCsub hzC).1
  have hγH : γ t ∈ H := by
    have h1 := negInv_mem_H' hzH
    rwa [negInv_negInv'] at h1
  have hhull : γ t ∈ fwdHull (fun r : ℝ => W' r.toNNReal) t :=
    ZhanGT4.A2TipSep.trace_mem_fwdHull hγ ENNReal.coe_lt_top hγH
  have hmem : relMapC c (γ t) ∈ relHullFam c C W' t := ⟨γ t, ⟨hhull, hzC⟩, rfl⟩
  have h1 := hsub hmem
  rw [mem_closedBall, dist_zero_right] at h1
  have h2 : ‖c.1 (-(γ t)⁻¹)‖ < 1 / (|M| + 1) := hδc _ hzC hzd
  have hc0 : c.1 (-(γ t)⁻¹) ≠ 0 := ne_zero_of_mem_H' (hc.2.1 hzC)
  have h3 : ‖relMapC c (γ t)‖ = ‖c.1 (-(γ t)⁻¹)‖⁻¹ := by
    simp only [relMapC, norm_neg, norm_inv]
  have h4 : |M| + 1 < ‖c.1 (-(γ t)⁻¹)‖⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) (norm_pos_iff.2 hc0)]
    simpa only [one_div] using h2
  rw [h3] at h1
  linarith [le_abs_self M]

end Far

end GW4Rel

end Theorem14

end InteractingSLE
