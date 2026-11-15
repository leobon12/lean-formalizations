/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanShift

/-!
# Singleton active tip fibres: the deterministic geometry of Aux. lemmas 135–136

Packet PROVE-SEC7-E (specification §7.5, `source/spec/p433-480.md` L121–L201, pp. 439–442).

Let `η` be a continuous Loewner trace of the driver `W` (`IsLoewnerTrace W η`), `f_t = g_t⁻¹` the
inverse Loewner map and `F_t(z) = f_t(W_t + z)` its centred form (`fwdMapInv W t`), with boundary
extension `F̄_t = extendFrom ℍ F_t` (continuous on `ℍ̄` along a continuous trace). The tip is
`η(t) = F̄_t(0)` (`loewnerTip`). The specification's fibre identities

  (TS1)/(SF1)  `f_t⁻¹({η(t)}) = {W_t}` on `∂ℍ`

read, in centred coordinates `v = x − W_t`, "`F̄_t(v) = η(t)` for a real `v` only when `v = 0`"
(the point `∞` is never a preimage of a finite point: the hydrodynamic map fixes `∞`). This is
`IsSingletonTipFiber W t`; `isSingletonTipFiber_iff` gives the set form `{v | F̄_t(v) = η(t)} = {0}`.

## Main results

* `extendFrom_fwdMapInv_congr`, `isSingletonTipFiber_congr`: the boundary map `F̄_t`, the tip and the
  fibre property at time `t` depend only on the driver on `[0, t]`.
* `IsLoewnerTrace.mem_activeDomain_of_not_mem_image` (Aux. 135 proof, p. 441: "The point `p` belongs
  to the active domain `D_a`"): if `p = η(T) ∈ ℍ`, `a ≤ T` and `p ∉ η([0, a])`, then
  `p ∈ ℍ \ K_a`, and the mapped point `g_a(p) − W_a` is the shifted tip `γ_a(T − a) ∈ ℍ`.
* `IsLoewnerTrace.isSingletonTipFiber_of_shift` (Aux. 135 proof, last paragraph): if moreover the
  chain of the future driver `W(a + ·) − W(a)` has a singleton tip fibre at time `T − a`, then the
  original chain has a singleton tip fibre at time `T`.
* `IsLoewnerTrace.exists_rat_not_mem_image` (Aux. 135 proof, p. 441: "Choose a positive rational `a`
  before this first visit"): an interior tip `η(T)` is first visited at a positive time.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology

open QuantumZipper (H Hbar fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace Sec7

/-! ### The singleton tip fibre -/

/-- **Singleton active tip fibre** at time `t` ((TS1) of Aux. lemma 135, (SF1) of Aux. lemma 136),
in centred coordinates: the only real point `v` with `F̄_t(v) = F̄_t(0)` is `v = 0`. Here
`F̄_t = extendFrom ℍ (fwdMapInv W t)` is the boundary extension of the centred inverse map
`F_t(z) = g_t⁻¹(W_t + z)`, and `F̄_t(0) = loewnerTip W t` is the tip. It depends on `W` only, and only
on `W` restricted to `[0, t]` (`isSingletonTipFiber_congr`). -/
def IsSingletonTipFiber (W : ℝ → ℝ) (t : ℝ) : Prop :=
  ∀ v : ℝ, extendFrom H (fwdMapInv W t) (v : ℂ) = loewnerTip W t → v = 0

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- For a continuous Loewner trace, the singleton tip fibre is the identity
`{v ∈ ℝ | F̄_t(v) = η(t)} = {0}`, i.e. `f_t⁻¹({η(t)}) ∩ ℝ = {W_t}` ((TS1), (SF1)). -/
theorem _root_.InteractingSLE.IsLoewnerTrace.isSingletonTipFiber_iff (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsSingletonTipFiber W t ↔ {v : ℝ | extendFrom H (fwdMapInv W t) (v : ℂ) = η t} = {0} := by
  have htip : loewnerTip W t = η t := hη.loewnerTip_eq hW hW0 ht
  constructor
  · intro h
    ext v
    simp only [Set.mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun hv => h v (by rw [hv, htip]), ?_⟩
    rintro rfl
    rw [← htip]
    simp [loewnerTip]
  · intro h v hv
    have : v ∈ {v : ℝ | extendFrom H (fwdMapInv W t) (v : ℂ) = η t} := by
      rw [Set.mem_ofPred_eq, hv, htip]
    rw [h] at this
    exact this

/-! ### Dependence on the driver -/

/-- The inverse map `F_t` on `ℍ` only depends on the driver on `[0, t]`. -/
theorem fwdMapInv_eqOn_of_eqOn {W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn W W' (Icc 0 t)) :
    EqOn (fwdMapInv W t) (fwdMapInv W' t) H := by
  intro u hu
  rw [QuantumZipper.UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hW hW0 ht hu,
    QuantumZipper.UnzipInvariance.fwdMapInv_eq_revMap_timeRev W' hW' hW'0 ht hu]
  refine QuantumZipper.ReverseFlow.revMap_congr_drive u fun q hq => ?_
  show W (t - q) - W t = W' (t - q) - W' t
  rw [h ⟨by linarith [hq.2], by linarith [hq.1]⟩, h ⟨ht, le_rfl⟩]

/-- `extendFrom ℍ` only sees the values on `ℍ`. -/
theorem extendFrom_H_congr {f g : ℂ → ℂ} (h : EqOn f g H) : extendFrom H f = extendFrom H g := by
  funext x
  unfold extendFrom limUnder
  congr 1
  exact Filter.map_congr (eventuallyEq_nhdsWithin_of_eqOn h)

/-- The boundary map `F̄_t` only depends on the driver on `[0, t]`. -/
theorem extendFrom_fwdMapInv_congr {W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn W W' (Icc 0 t)) :
    extendFrom H (fwdMapInv W t) = extendFrom H (fwdMapInv W' t) :=
  extendFrom_H_congr (fwdMapInv_eqOn_of_eqOn hW hW0 hW' hW'0 ht h)

/-- The tip at time `t` only depends on the driver on `[0, t]`. -/
theorem loewnerTip_congr {W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn W W' (Icc 0 t)) :
    loewnerTip W t = loewnerTip W' t := by
  unfold loewnerTip
  rw [extendFrom_fwdMapInv_congr hW hW0 hW' hW'0 ht h]

/-- The singleton tip fibre at time `t` only depends on the driver on `[0, t]`. -/
theorem isSingletonTipFiber_congr {W' : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {t : ℝ} (ht : 0 ≤ t) (h : EqOn W W' (Icc 0 t)) :
    IsSingletonTipFiber W t ↔ IsSingletonTipFiber W' t := by
  unfold IsSingletonTipFiber
  rw [loewnerTip_congr hW hW0 hW' hW'0 ht h, extendFrom_fwdMapInv_congr hW hW0 hW' hW'0 ht h]

/-! ### The tip of the mapped future is interior (Aux. 135 proof, p. 441) -/

/-- **A real boundary value of `F̄_a` lies on `ℝ ∪ η([0, a])`** ("the boundary of a hull generated by a
continuous trace is contained in the earlier trace together with the original boundary"). -/
theorem _root_.InteractingSLE.IsLoewnerTrace.extendFrom_ofReal_mem (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a : ℝ} (ha : 0 ≤ a) {x : ℂ} (hx : x.im = 0) :
    (extendFrom H (fwdMapInv W a) x).im = 0 ∨ extendFrom H (fwdMapInv W a) x ∈ η '' Icc 0 a := by
  obtain ⟨-, hc, -, -⟩ := hη.fiber_hyps hW hW0 ha
  have hcb := isConformalBijection_fwdMapInv hW hW0 ha
  have heq : EqOn (extendFrom H (fwdMapInv W a)) (fwdMapInv W a) H := fun z hz =>
    extendFrom_H_eq hcb.1.continuousOn hz
  have himg : extendFrom H (fwdMapInv W a) '' H = H \ fwdHull W a := by
    rw [heq.image_eq]; exact hcb.2.image_eq
  have hxc : x ∈ closure H := by rw [closure_H]; exact mem_Hbar_of_im_eq_zero hx
  have hc' : ContinuousOn (extendFrom H (fwdMapInv W a)) (closure H) := by rw [closure_H]; exact hc
  have h1 : extendFrom H (fwdMapInv W a) x ∈ closure (H \ fwdHull W a) := by
    rw [← himg]; exact hc'.image_closure (mem_image_of_mem _ hxc)
  have h2 := hη.extendFrom_not_mem hW hW0 ha hx
  have hfr : extendFrom H (fwdMapInv W a) x ∈ frontier (H \ fwdHull W a) := by
    rw [(isHPHull_fwdHull hW ha).2.2.1.frontier_eq]; exact ⟨h1, h2⟩
  rw [hη.2.2 a ha] at hfr
  rcases frontier_H_diff_fillH_subset (hη.isCompact_image a).isBounded hfr with h | h
  · exact Or.inl h
  · exact Or.inr (by rwa [(hη.isCompact_image a).isClosed.closure_eq] at h)

/-- **The point `p = η(a + u)` lies in the active domain `D_a`, and the mapped future tip
`γ_a(u) = g_a(p) − W_a` lies in `ℍ`** (Aux. 135 proof, p. 441: "The point `p` belongs to the active
domain `D_a` … Thus `g_a(p) ∈ ℍ`"), provided `p ∈ ℍ` was not visited during `[0, a]`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.shift_tip_mem_H (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u) (hpH : η (a + u) ∈ H)
    (hpa : η (a + u) ∉ η '' Icc 0 a) :
    loewnerTip (shiftDrive W a) u ∈ H ∧ η (a + u) ∈ H \ fwdHull W a := by
  obtain ⟨hξ, hFξ, -⟩ := hη.extendFrom_shift_tip hW hW0 ha hu
  have hcb := isConformalBijection_fwdMapInv hW hW0 ha
  by_cases hξH : loewnerTip (shiftDrive W a) u ∈ H
  · refine ⟨hξH, ?_⟩
    rw [← hFξ, extendFrom_H_eq hcb.1.continuousOn hξH, ← hcb.2.image_eq]
    exact mem_image_of_mem _ hξH
  · exfalso
    have him : (loewnerTip (shiftDrive W a) u).im = 0 := le_antisymm (not_lt.1 hξH) hξ
    rcases hη.extendFrom_ofReal_mem hW hW0 ha him with h | h
    · rw [hFξ] at h
      have : 0 < (η (a + u)).im := hpH
      rw [h] at this
      exact lt_irrefl 0 this
    · rw [hFξ] at h
      exact hpa h

/-! ### Transfer of a singleton fibre through the composition `f_T = f_a ∘ f^{(a)}_{T−a}` -/

/-- **Aux. 135, the composition step** (p. 441: "The preceding conditional argument says that the
inverse map of the mapped future hull has a single boundary preimage of `g_a(p)`. Composing it with
`f_a` gives `f_T` … There is exactly one such preimage, namely the current driver."). If the interior
tip `p = η(a + u)` was not visited during `[0, a]` and the chain of the future driver
`W(a + ·) − W(a)` has a singleton tip fibre at time `u`, then the chain of `W` has a singleton tip
fibre at time `a + u`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.isSingletonTipFiber_of_shift (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {a u : ℝ} (ha : 0 ≤ a) (hu : 0 ≤ u)
    (hpH : η (a + u) ∈ H) (hpa : η (a + u) ∉ η '' Icc 0 a)
    (hshift : IsSingletonTipFiber (shiftDrive W a) u) : IsSingletonTipFiber W (a + u) := by
  intro v hv
  rw [hη.loewnerTip_eq hW hW0 (add_nonneg ha hu)] at hv
  obtain ⟨hξH, hpD⟩ := hη.shift_tip_mem_H hW hW0 ha hu hpH hpa
  have hvH : (v : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  obtain ⟨ζ, hζ, hFζ, hlim⟩ := hη.exists_tendsto_shift hW hW0 ha hu hvH
  rw [hv] at hFζ
  have hζH : ζ ∈ H := by
    by_contra h
    have him : ζ.im = 0 := le_antisymm (not_lt.1 h) hζ
    exact hη.extendFrom_not_mem hW hW0 ha him (hFζ ▸ hpD)
  obtain ⟨-, -, hinj, -⟩ := hη.fiber_hyps hW hW0 ha
  obtain ⟨-, hFξ, -⟩ := hη.extendFrom_shift_tip hW hW0 ha hu
  have hζξ : ζ = loewnerTip (shiftDrive W a) u := hinj hζH hξH (by rw [hFζ, hFξ])
  have hext : extendFrom H (fwdMapInv (shiftDrive W a) u) (v : ℂ) = ζ :=
    extendFrom_eq (by rw [closure_H]; exact hvH) hlim
  exact hshift v (by rw [hext, hζξ])

/-! ### The first visit of an interior tip is at a positive time -/

/-- **An interior tip is first visited at a positive time** (Aux. 135 proof, p. 441: "Its first visit
occurs at a strictly positive time: the trace is continuous and starts on the real boundary. Choose a
positive rational `a` before this first visit."). -/
theorem _root_.InteractingSLE.IsLoewnerTrace.exists_rat_not_mem_image (hη : IsLoewnerTrace W η) {T : ℝ} (hT : 0 < T)
    (hpH : η T ∈ H) : ∃ a : ℚ, 0 < (a : ℝ) ∧ (a : ℝ) < T ∧ η T ∉ η '' Icc 0 (a : ℝ) := by
  have him : 0 < (η T).im := hpH
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.1 (hη.2.1 0 (Set.mem_Ici.2 le_rfl)) _ him
  obtain ⟨a, ha0, haT⟩ := exists_rat_btwn (lt_min hδ hT)
  refine ⟨a, ha0, haT.trans_le (min_le_right _ _), ?_⟩
  rintro ⟨s, hs, hsT⟩
  have hsδ : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt (haT.trans_le (min_le_left _ _))
  have h1 := hcont hs.1 hsδ
  rw [hsT, hη.1, dist_zero_right] at h1
  exact absurd (h1.trans_le' (abs_im_le_norm _)) (by rw [abs_of_pos him]; exact lt_irrefl _)

/-- **Aux. 135, the deterministic reduction.** Let `T > 0` with interior tip `η(T)`. If for every
positive rational `a < T` such that `η(T) ∉ η([0, a])` the chain of the future driver
`W(a + ·) − W(a)` has a singleton tip fibre at time `T − a`, then the chain of `W` has a singleton
tip fibre at time `T`. -/
theorem _root_.InteractingSLE.IsLoewnerTrace.isSingletonTipFiber_of_forall_rat (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) (hpH : η T ∈ H)
    (hshift : ∀ a : ℚ, 0 < (a : ℝ) → (a : ℝ) < T → η T ∉ η '' Icc 0 (a : ℝ) →
      IsSingletonTipFiber (shiftDrive W a) (T - a)) :
    IsSingletonTipFiber W T := by
  obtain ⟨a, ha0, haT, hpa⟩ := hη.exists_rat_not_mem_image hT hpH
  have hTa : (a : ℝ) + (T - a) = T := by ring
  have h := hη.isSingletonTipFiber_of_shift hW hW0 ha0.le (sub_nonneg.2 haT.le)
    (by rw [hTa]; exact hpH) (by rw [hTa]; exact hpa) (hshift a ha0 haT hpa)
  rwa [hTa] at h

end Sec7

end InteractingSLE
