/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux37SideBand

/-!
# Aux. lemma 37's side germ: the traversal side (PFI3)

Packet PROVE-STRIPSYS42. Specification §6.2, Aux. lemma 37's proof (`source/spec/p193-240.md` L126–L129, p. 199:
"use the accessible `C`-side collar of the whole incoming segment from `αᵢ(v)` through `J`. The active inverse map is
continuous, and the singleton tip-fiber assertion makes the real endpoint of that collar at `αᵢ(v)` equal to the
driver. The real boundary orientation in a conformal half-plane chart then puts the remainder of this collar to the
left of the driver when it is the incoming right side, and to the right when it is the incoming left side"), with
ruling R41's replacement of the singleton tip fibre (`ig1_ztip_elimination.txt` L185–L196: "`T_v` … is explicitly the
first counterflow visit to the interior point `αᵢ(v)`. On the witness event (PFI1), `r < T_v < s`, so this is a positive
fresh interior tip. The deterministic fresh-tip lemma makes the incident endpoint of the incoming collar equal to
`W_{T_v}`").

* `IsArcChart`: the pathwise setting of one arc of a reverse-contained pocket read through a chart of the pocket with
  a landing map, a reading and strictly monotone arc values (`ε = 1`: increasing, `ε = −1`: decreasing);
* **`exists_side_limit`** ((PFI3) at the deterministic witness times): at a rational witness `(r₀, s₀, v, v₁, v₂)`, the
  counterflow chart `g_{s₀} ∘ m` has a real limit `y` along the chart approach at the arc value `f(v₁)`, with
  `ε y > 0` and `f̄_{s₀}(y) = A(v₁)`. Proof: the first visit `T` of `A(v)` lies in `(r₀, s₀]` and is a fresh
  interior tip; on the band rectangle over `f([v, x₂])` the boundary values `k(u) = g_T(A(u))` are continuous and
  injective, `k(v) = 0`
  by the fresh-tip fibre (`Sec6.fresh_tip_fibre`), and `ε k` increases (Schwarz reflection); so `ε k(v₁) > 0`. A
  half-disc around `k(v₁)` maps into `D_{s₀}` (open mapping), so `k(v₁)` is alive for the increment chain from `T` to
  `s₀`, whose real flow keeps the sign and is the limit at `s₀` (`fwdMap_add_shift`).

No Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, `*_of_param` (R43, R48).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Function Complex
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open QuantumZipper.RS (shiftDrive)
open InteractingSLE.WangWu (negInv)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal Real

namespace InteractingSLE.Sec7.Aux37Side

open WangWu Lemma71I PocketCoord PocketJordan Aux119Bdry Lemma71O Aux37Frame

/-! ### The setting -/

/-- **One arc of a pocket read through a chart** (the chart part of the side germ's setting; the visit data are
`IsArcVisit`): `C = m(P)`, the arc `A` is read through the wall `X` (`m(A u) = X(arcTime(lo + u(hi − lo)))` on
`(0, 1)`); `c` is a conformal chart of `P` whose landing map `land c` (continuous on `ℍ̄`, `c⁻¹` on `ℍ`, off `0` away
from the chart value `0`) is inverted by the reading `κ`, and whose inverse lands at the wall points at the arc values
`f u`, with `ε f` positive and strictly increasing (`ε = ±1`). -/
structure IsArcChart (C : Set ℂ) (A : ℝ → ℂ) (P : Set ℂ) (X : ℝ≥0 → ℂ) (Wu : Set ℂ) (lo hi : ℝ) (c : Chart)
    (κ : ℂ → ℂ) (f : ℝ → ℝ) (ε : ℝ) : Prop where
  hCP : C = negInv '' P
  hPH : P ⊆ H
  hPW : Disjoint P Wu
  hAX : ∀ u ∈ Ioo (0 : ℝ) 1, negInv (A u) = X (arcTime (lo + u * (hi - lo))).toNNReal
  conf : c.IsConformal
  mapsTo : MapsTo c.2.1 H P
  landC : ContinuousOn (land c) Hbar
  landH : ∀ w ∈ H, land c w = c.2.1 w
  read : ∀ q ∈ Hbar, κ (land c q) = q
  readC : ∀ q ∈ Hbar, ContinuousWithinAt κ (land c '' Hbar) (land c q)
  land0 : ∀ q ∈ Hbar, q ≠ 0 → land c q ≠ 0
  fc : ContinuousOn f (Ioo 0 1)
  ne_zero : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < ε * f u
  mono : StrictMonoOn (fun u => ε * f u) (Ioo 0 1)
  sign : ε = 1 ∨ ε = -1
  lim : ∀ u ∈ Ioo (0 : ℝ) 1, Tendsto c.2.1 (𝓝[H] (f u : ℂ)) (𝓝 (X (arcTime (lo + u * (hi - lo))).toNNReal))

namespace IsArcChart

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β A : ℝ → ℂ} {τ σ : ℝ} {P : Set ℂ} {X : ℝ≥0 → ℂ}
  {Wu : Set ℂ} {lo hi : ℝ} {c : Chart} {κ : ℂ → ℂ} {f : ℝ → ℝ} {ε : ℝ}

theorem ofReal_mem_Hbar (q : ℝ) : (q : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (q : ℂ).im by simp

/-- The landing point at an arc value is `m` of the arc point. -/
theorem negInv_land (hS : IsArcChart C A P X Wu lo hi c κ f ε) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    negInv (land c (f u)) = A u := by
  have hl : land c (f u) = X (arcTime (lo + u * (hi - lo))).toNNReal := by
    rw [land, extendFrom_eq (by rw [closure_H]; exact ofReal_mem_Hbar _) (hS.lim u hu)]
  rw [hl, ← hS.hAX u hu, WangWu.negInv_negInv]

theorem eps_ne_zero (hS : IsArcChart C A P X Wu lo hi c κ f ε) : ε ≠ 0 := by
  rcases hS.sign with h | h <;> rw [h] <;> norm_num

/-- `f` is injective on `(0, 1)`. -/
theorem injOn_f (hS : IsArcChart C A P X Wu lo hi c κ f ε) : InjOn f (Ioo 0 1) := fun u hu u' hu' h =>
  hS.mono.injOn hu hu' (by simp only [h])

end IsArcChart

namespace IsArcChart

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β A : ℝ → ℂ} {τ σ : ℝ} {P : Set ℂ} {X : ℝ≥0 → ℂ}
  {Wu : Set ℂ} {lo hi : ℝ} {c : Chart} {κ : ℂ → ℂ} {f : ℝ → ℝ} {ε : ℝ}

/-- The arc values between two arc parameters lie between their values. -/
theorem mem_uIcc (hS : IsArcChart C A P X Wu lo hi c κ f ε) {p q u : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hpu : p ≤ u) (huq : u ≤ q) : f u ∈ uIcc (f p) (f q) := by
  have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨hp.1.trans_le hpu, huq.trans_lt hq.2⟩
  have h1 : ε * f p ≤ ε * f u := hS.mono.monotoneOn hp hu hpu
  have h2 : ε * f u ≤ ε * f q := hS.mono.monotoneOn hu hq huq
  rcases hS.sign with he | he <;> rw [he] at h1 h2
  · exact Set.mem_uIcc_of_le (by linarith) (by linarith)
  · exact Set.mem_uIcc_of_ge (by linarith) (by linarith)

/-- Two distinct arc parameters have distinct values, with the strict order along `ε`. -/
theorem lt_of_lt (hS : IsArcChart C A P X Wu lo hi c κ f ε) {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) (hpq : p < q) : ε * f p < ε * f q := hS.mono hp hq hpq

/-- The base of a rectangle between two arc values avoids `0`. -/
theorem rect_base (hS : IsArcChart C A P X Wu lo hi c κ f ε) {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1) : 0 < f p ⊓ f q ∨ f p ⊔ f q < 0 := by
  have h1 := hS.ne_zero p hp
  have h2 := hS.ne_zero q hq
  rcases hS.sign with he | he <;> rw [he] at h1 h2
  · exact Or.inl (lt_inf_iff.2 ⟨by linarith, by linarith⟩)
  · exact Or.inr (sup_lt_iff.2 ⟨by linarith, by linarith⟩)

end IsArcChart

/-! ### Elementary facts -/

section Elem

/-- A continuous injective function on `[p, q]` with one increasing pair is strictly increasing. -/
theorem strictMonoOn_of_pair {g : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q) (hgc : ContinuousOn g (Icc p q))
    (hgi : InjOn g (Icc p q)) {u₁ u₂ : ℝ} (hu₁ : u₁ ∈ Icc p q) (hu₂ : u₂ ∈ Icc p q) (h12 : u₁ < u₂)
    (hg : g u₁ < g u₂) : StrictMonoOn g (Icc p q) := by
  rcases hgc.strictMonoOn_of_injOn_Icc' hpq hgi with h | h
  · exact h
  · exact absurd (h hu₁ hu₂ h12) (not_lt.2 hg.le)

/-- A solution of the centred flow from a nonzero real point (driver from `0`) is real and keeps its sign. -/
theorem mul_re_pos_of_isForwardSol_real {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {y T : ℝ} (hy : y ≠ 0)
    (hT : 0 ≤ T) {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W (y : ℂ) T u) :
    (u T).im = 0 ∧ 0 < y * (u T).re := by
  have him : ∀ t ∈ Icc (0 : ℝ) T, (u t).im = 0 := fun t ht => im_eq_zero_of_isForwardSol_real hW hu ht
  refine ⟨him T ⟨hT, le_rfl⟩, ?_⟩
  have hu0 : u 0 = (y : ℂ) := by
    have h := (hu.2 0 ⟨le_rfl, hT⟩).2
    rw [h, hW0, intervalIntegral.integral_same]
    simp
  have hc : ContinuousOn (fun t => y * (u t).re) (Icc 0 T) :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn hu.1)
  by_contra hle
  push Not at hle
  have hy2 : 0 ≤ y * (u 0).re := by rw [hu0, ofReal_re]; exact mul_self_nonneg y
  obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' hT hc (show (0 : ℝ) ∈ Icc (y * (u T).re) (y * (u 0).re) from
    ⟨hle, hy2⟩)
  have hre : (u t).re = 0 := by
    rcases mul_eq_zero.1 ht0 with h | h
    · exact absurd h hy
    · exact h
  exact (hu.2 t ht).1 (Complex.ext (by simpa using hre) (by simpa using him t ht))

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **A point of `ℍ` whose image under `f̄_T` lies in `D_s` is off the increment hull** from `T` to `s`. -/
theorem notMem_fwdHull_shift (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {T s : ℝ}
    (hT : 0 ≤ T) (hTs : T ≤ s) {w : ℂ} (hw : w ∈ H) (hD : trMap W 0 T w ∈ H \ fwdHull W s) :
    w ∉ fwdHull (shiftDrive W T) (s - T) := by
  rw [← Sec6.trMap_zero_image_H hW hW0 (hT.trans hTs)] at hD
  obtain ⟨w', hw', he⟩ := hD
  rw [← YuanSimpleApprox.trMap_trMap hη hW hW0 le_rfl hT hTs (QuantumZipper.H_subset_Hbar hw')] at he
  have hm := YuanSimpleApprox.trMap_image_subset hW hTs ⟨w', hw', rfl⟩
  have heq := YuanSimpleApprox.trMap_injOn hη hW hW0 le_rfl hT hm.1 hw he
  rw [← heq]
  exact hm.2

end Elem

/-! ### (PFI3): the traversal side at the witness times -/

section Side

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β A : ℝ → ℂ} {τ σ : ℝ} {P : Set ℂ} {X : ℝ≥0 → ℂ}
  {Wu : Set ℂ} {lo hi : ℝ} {c : Chart} {κ : ℂ → ℂ} {f : ℝ → ℝ} {ε : ℝ}

/-- **The sign at the first visit `T` of `A(v)`** (the first half of `exists_side_limit`): a time `T ≤ s₀`, the
counterflow map `G = ḡ_T` on a band rectangle, conformal with real boundary values on an upper half-disc around the
arc value `f(v₁)`, whose points land in `D_{s₀}`, and the real boundary value `y_T = G(A(v₁))` with `ε y_T > 0`. -/
theorem exists_sign_first_visit (hS : IsArcChart C A P X Wu lo hi c κ f ε)
    {r₀ s₀ a₀ v v₁ v₂ : ℝ} (hV : IsArcVisit W η C A r₀ s₀ a₀ v v₂) (hvv₁ : v < v₁) (hv₁v₂ : v₁ < v₂) :
    ∃ (T : ℝ) (G : ℂ → ℂ) (ρ yT : ℝ), 0 ≤ T ∧ T ≤ s₀ ∧ 0 < ρ ∧
      R16.IsRealBoundaryConformal (fun w => G (negInv (land c w))) (f v₁) ρ ∧
      (∀ w ∈ H ∩ ball (f v₁ : ℂ) ρ, negInv (land c w) ∈ H \ fwdHull W s₀ ∧
        G (negInv (land c w)) = fwdMap W T (negInv (land c w)) ∧
        trMap W 0 T (G (negInv (land c w))) = negInv (land c w)) ∧
      G (negInv (land c (f v₁))) = (yT : ℂ) ∧ 0 < ε * yT := by
  have hη := hV.trace
  have hW := hV.continuous_W
  have hW0 := hV.W_zero
  have hr₀ : 0 ≤ r₀ := hV.nonneg
  have hs₀ : 0 ≤ s₀ := hr₀.trans hV.lt.le
  -- the band at `s₀`
  obtain ⟨δ, hδ, hband⟩ := exists_band_cf hV hS.hCP hS.hPH hS.hPW hS.hAX hS.conf hS.mapsTo hS.fc hS.lim
  -- the arc parameters
  set x₂ : ℝ := (v₁ + v₂) / 2 with hx₂
  have ha₀v := hV.a₀_lt
  have ha₀ := hV.pos
  have hv₂1 := hV.lt_one
  have hI : ∀ u, a₀ ≤ u → u ≤ v₂ → u ∈ Ioo (0 : ℝ) 1 := fun u h1 h2 => ⟨by linarith, by linarith⟩
  have hvI := hI v (by linarith) (by linarith)
  have hv₁I := hI v₁ (by linarith) (by linarith)
  have hx₂I := hI x₂ (by linarith) (by linarith)
  have hσ₁I := hI a₀ le_rfl (by linarith)
  have hv₂I := hI v₂ (by linarith) le_rfl
  set a' : ℝ := f v ⊓ f x₂ with ha'
  set b' : ℝ := f v ⊔ f x₂ with hb'
  have hfv₁ : f v₁ ∈ Ioo a' b' := by
    have h1 := hS.lt_of_lt hvI hv₁I hvv₁
    have h2 := hS.lt_of_lt hv₁I hx₂I (by linarith)
    rcases hS.sign with he | he <;> rw [he] at h1 h2
    · exact ⟨inf_lt_of_left_lt (by linarith), lt_sup_of_lt_right (by linarith)⟩
    · exact ⟨inf_lt_of_right_lt (by linarith), lt_sup_of_lt_left (by linarith)⟩
  have hab' : a' < b' := hfv₁.1.trans hfv₁.2
  have hsub : Icc a' b' ⊆ uIcc (f a₀) (f v₂) :=
    Set.uIcc_subset_uIcc (hS.mem_uIcc hσ₁I hv₂I (by linarith) (by linarith))
      (hS.mem_uIcc hσ₁I hv₂I (by linarith) (by linarith))
  have hbot : ∀ q ∈ Icc a' b', ∃ u ∈ Icc v x₂, f u = q := by
    intro q hq
    have hvx : v ≤ x₂ := by linarith
    have := intermediate_value_uIcc (a := v) (b := x₂) (f := f)
      (hS.fc.mono (by rw [uIcc_of_le hvx]; exact fun u hu => hI u (by linarith [hu.1]) (by linarith [hu.2])))
    obtain ⟨u, hu, hfu⟩ := this hq
    rw [uIcc_of_le hvx] at hu
    exact ⟨u, hu, hfu⟩
  have hIvx : ∀ u ∈ Icc v x₂, u ∈ Ioo (0 : ℝ) 1 := fun u hu => hI u (by linarith [hu.1]) (by linarith [hu.2])
  -- the first visit `T` of `A v`
  have hAvs : A v ∈ η '' Icc 0 s₀ := hV.vis_s v ⟨le_rfl, hV.v_lt.le⟩
  obtain ⟨hT0, hηT, hfresh⟩ := firstHit_spec hη.2.1 ⟨s₀, hAvs⟩
  set T := firstHit η (A v) with hTdef
  have hTs : T ≤ s₀ := Sec6.le_of_fresh hfresh hAvs
  have hrT : r₀ < T := by
    by_contra hle
    push Not at hle
    exact Sec6.notMem_domain_of_mem_trace hη hr₀ ⟨T, ⟨hT0, hle⟩, hηT⟩ (hV.unvis_r v ⟨ha₀v.le, hV.v_lt.le⟩)
  have hTpos : 0 < T := hr₀.trans_lt hrT
  have hvisT : ∀ u ∈ Icc v v₂, A u ∈ η '' Icc 0 T := fun u hu =>
    hV.rev T v ⟨ha₀v.le, hV.v_lt.le⟩ u ⟨ha₀v.le.trans hu.1, hu.2⟩ hu.1 ⟨T, ⟨hT0, le_rfl⟩, hηT⟩
  -- the counterflow map at `T` on the rectangle
  have hband' : ∀ w ∈ H, w.re ∈ Icc (f a₀ ⊓ f v₂) (f a₀ ⊔ f v₂) → w.im < δ →
      c.2.1 w ∈ H \ (negInv '' fwdHull W s₀ ∪ Wu) := hband
  have hvisq : ∀ t, T ≤ t → ∀ q : ℝ, q ∈ Icc a' b' → negInv (land c q) ∉ H \ fwdHull W t := by
    intro t hTt q hq
    obtain ⟨u, hu, rfl⟩ := hbot q hq
    rw [hS.negInv_land (hIvx u hu)]
    exact Sec6.notMem_domain_of_mem_trace hη (hT0.trans hTt)
      (image_mono (Icc_subset_Icc_right hTt) (hvisT u ⟨hu.1, by linarith [hu.2]⟩))
  have hrect0 : 0 < a' ∨ b' < 0 := hS.rect_base hvI hx₂I
  obtain ⟨G, hGc, hGi, -, hGF, hGD, hGR, hDs, hRBC⟩ := exists_ext_rect (δ' := δ / 2) hη hW hW0 hT0 hTs hS.conf
    hS.landC hS.landH hS.read hS.readC
    (fun q hq => hS.land0 q (closure_rect_subset.trans crect_subset_Hbar hq) (ne_zero_of_mem_closure_rect hrect0 hq))
    hband' (hsub ⟨le_rfl, hab'.le⟩).1 (hsub ⟨hab'.le, le_rfl⟩).2 (by linarith) (hvisq T le_rfl)
  set S := rect a' b' (δ / 2) with hSdef
  have hfuS : ∀ u ∈ Icc v x₂, ((f u : ℝ) : ℂ) ∈ closure S := fun u hu =>
    ofReal_mem_closure_rect hab' (by linarith) (hS.mem_uIcc hvI hx₂I hu.1 hu.2)
  have hmem : ∀ u ∈ Icc v x₂, A u ∈ negInv '' (land c '' closure S) := fun u hu =>
    ⟨land c (f u), ⟨f u, hfuS u hu, rfl⟩, hS.negInv_land (hIvx u hu)⟩
  have hAnD : ∀ u ∈ Icc v x₂, A u ∉ H \ fwdHull W T := fun u hu =>
    Sec6.notMem_domain_of_mem_trace hη hT0 (hvisT u ⟨hu.1, by linarith [hu.2]⟩)
  set k : ℝ → ℝ := fun u => (G (A u)).re with hkdef
  have hkreal : ∀ u ∈ Icc v x₂, G (A u) = ((k u : ℝ) : ℂ) := fun u hu =>
    Complex.ext (by simp [hkdef]) (by simp [hkdef, hGR _ (hmem u hu) (hAnD u hu)])
  -- `k v = 0`: the fresh-tip fibre
  have hkv : k v = 0 := by
    have hvv : v ∈ Icc v x₂ := ⟨le_rfl, by linarith⟩
    have h1 : trMap W 0 T (k v) = η T := by rw [← hkreal v hvv, hGF _ (hmem v hvv), hηT]
    exact Sec6.fresh_tip_fibre hη hW hW0 hTpos (by rw [hηT]; exact (hV.unvis_r v ⟨ha₀v.le, hV.v_lt.le⟩).1)
      (by rw [hηT]; exact hfresh) h1
  -- continuity and injectivity of `k`
  have hland0 : ∀ q ∈ closure S, ContinuousWithinAt (fun w => G (negInv (land c w))) (closure S) q := by
    intro q hq
    have hKH : closure S ⊆ Hbar := closure_rect_subset.trans crect_subset_Hbar
    have h1 : ContinuousWithinAt (fun w => negInv (land c w)) (closure S) q :=
      (WangWu.continuousAt_negInv (hS.land0 q (hKH hq) (ne_zero_of_mem_closure_rect hrect0 hq))).comp_continuousWithinAt
        (hS.landC.mono hKH q hq)
    exact ContinuousWithinAt.comp (f := fun w => negInv (land c w)) (hGc _ ⟨land c q, ⟨q, hq, rfl⟩, rfl⟩) h1
      fun w hw => ⟨land c w, ⟨w, hw, rfl⟩, rfl⟩
  have hkeq : ∀ u ∈ Icc v x₂, k u = (G (negInv (land c (f u)))).re := fun u hu => by
    simp only [hkdef, hS.negInv_land (hIvx u hu)]
  have hkc : ContinuousOn k (Icc v x₂) := by
    have hφc : ContinuousOn (fun w => G (negInv (land c w))) (closure S) := fun q hq => hland0 q hq
    have hfc' : ContinuousOn (fun u => ((f u : ℝ) : ℂ)) (Icc v x₂) :=
      Complex.continuous_ofReal.comp_continuousOn (hS.fc.mono fun u hu => hIvx u hu)
    exact ContinuousOn.congr (Complex.continuous_re.comp_continuousOn (hφc.comp hfc' hfuS)) hkeq
  have hki : InjOn k (Icc v x₂) := by
    intro u hu u' hu' he
    have h1 : G (A u) = G (A u') := by rw [hkreal u hu, hkreal u' hu', he]
    have h2 := hGi (hmem u hu) (hmem u' hu') h1
    rw [← hS.negInv_land (hIvx u hu), ← hS.negInv_land (hIvx u' hu')] at h2
    have h3 : land c (f u) = land c (f u') := by
      rw [← WangWu.negInv_negInv (land c (f u)), h2, WangWu.negInv_negInv]
    have h4 : (f u : ℂ) = f u' := by
      rw [← hS.read _ (IsArcChart.ofReal_mem_Hbar (f u)), h3, hS.read _ (IsArcChart.ofReal_mem_Hbar _)]
    exact hS.injOn_f (hIvx u hu) (hIvx u' hu') (Complex.ofReal_injective h4)
  -- `ε k` increases near `v₁`
  set ρ : ℝ := min (min (f v₁ - a') (b' - f v₁)) (δ / 2) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min (by linarith [hfv₁.1]) (by linarith [hfv₁.2])) (by linarith)
  have hρa : ρ ≤ f v₁ - a' := (min_le_left _ _).trans (min_le_left _ _)
  have hρb : ρ ≤ b' - f v₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hρδ : ρ ≤ δ / 2 := min_le_right _ _
  have hR := hRBC (f v₁) ρ hρa hρb hρδ
  have hmonoR := strictMonoOn_re hR
  obtain ⟨η₀, hη₀, hη₀f⟩ := Metric.continuousAt_iff.1
    ((hS.fc.continuousAt (isOpen_Ioo.mem_nhds hv₁I))) ρ hρ
  set u₂ : ℝ := v₁ + min (η₀ / 2) ((x₂ - v₁) / 2) with hu₂
  have hm1 : 0 < min (η₀ / 2) ((x₂ - v₁) / 2) := lt_min (by linarith) (by linarith)
  have hm2 := min_le_left (η₀ / 2) ((x₂ - v₁) / 2)
  have hm3 := min_le_right (η₀ / 2) ((x₂ - v₁) / 2)
  have hu₂I : u₂ ∈ Icc v x₂ := ⟨by linarith, by linarith⟩
  have hv₁m : v₁ ∈ Icc v x₂ := ⟨hvv₁.le, by linarith⟩
  have hfu₂ : f u₂ ∈ Ioo (f v₁ - ρ) (f v₁ + ρ) := by
    have h := hη₀f (show dist u₂ v₁ < η₀ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hfv₁m : f v₁ ∈ Ioo (f v₁ - ρ) (f v₁ + ρ) := ⟨by linarith, by linarith⟩
  have hpair : ε * k v₁ < ε * k u₂ := by
    rw [hkeq v₁ hv₁m, hkeq u₂ hu₂I]
    have hlt := hS.lt_of_lt hv₁I (hIvx u₂ hu₂I) (by linarith)
    rcases hS.sign with he | he <;> rw [he] at hlt ⊢
    · simp only [one_mul] at hlt ⊢
      exact hmonoR hfv₁m hfu₂ hlt
    · have hlt' : f u₂ < f v₁ := by linarith
      have := hmonoR hfu₂ hfv₁m hlt'
      simp only at this
      linarith
  have hmono : StrictMonoOn (fun u => ε * k u) (Icc v x₂) :=
    strictMonoOn_of_pair (by linarith) (continuousOn_const.mul hkc)
      (fun u hu u' hu' he => hki hu hu' (mul_left_cancel₀ hS.eps_ne_zero he)) hv₁m hu₂I (by linarith) hpair
  have hyT : 0 < ε * k v₁ := by
    have := hmono ⟨le_rfl, by linarith⟩ hv₁m hvv₁
    simp only [hkv, mul_zero] at this
    exact this
  set yT := k v₁ with hyTdef
  have hφv₁ : G (negInv (land c (f v₁))) = (yT : ℂ) := by rw [hS.negInv_land hv₁I]; exact hkreal v₁ hv₁m
  have hHρ : H ∩ ball (f v₁ : ℂ) ρ ⊆ S := (ball_subset_rect hρa hρb hρδ).1
  refine ⟨T, G, ρ, yT, hT0, hTs, hρ, hR, fun w hw => ?_, hφv₁, hyT⟩
  have hwS : w ∈ closure S := subset_closure (hHρ hw)
  have hmem' : negInv (land c w) ∈ negInv '' (land c '' closure S) := ⟨land c w, ⟨w, hwS, rfl⟩, rfl⟩
  have hzD := hDs w hwS hw.1
  have hzT : negInv (land c w) ∈ H \ fwdHull W T := ⟨hzD.1, fun h => hzD.2 (WangWu.fwdHull_mono hTs h)⟩
  exact ⟨hzD, hGD _ hmem' hzT, hGF _ hmem'⟩

/-- **The transport from the first visit to `s₀`** (the second half of `exists_side_limit`): if a half-disc around
the real boundary value `y_T` of `G = ḡ_T` maps into `D_{s₀}`, then `y_T` is alive for the increment chain from `T` to
`s₀`; its real flow keeps the sign and is the limit of `g_{s₀}` along the chart approach. -/
theorem exists_side_transport {W : ℝ → ℝ} {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {c : Chart} (hlandC : ContinuousOn (land c) Hbar) (hlandH : ∀ w ∈ H, land c w = c.2.1 w)
    {ξ : ℝ} (hland0 : land c ξ ≠ 0) {T s₀ : ℝ} (hT0 : 0 ≤ T) (hTs : T ≤ s₀) {G : ℂ → ℂ} {ρ yT ε : ℝ}
    (hρ : 0 < ρ) (hR : R16.IsRealBoundaryConformal (fun w => G (negInv (land c w))) ξ ρ)
    (hD : ∀ w ∈ H ∩ ball (ξ : ℂ) ρ, negInv (land c w) ∈ H \ fwdHull W s₀ ∧
      G (negInv (land c w)) = fwdMap W T (negInv (land c w)) ∧
      trMap W 0 T (G (negInv (land c w))) = negInv (land c w))
    (hφv₁ : G (negInv (land c ξ)) = (yT : ℂ)) (hε : ε = 1 ∨ ε = -1) (hyT : 0 < ε * yT) :
    ∃ y : ℝ, Tendsto (fun w => fwdMap W s₀ (negInv (c.2.1 w))) (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) ∧ 0 < ε * y ∧
      trMap W 0 s₀ y = negInv (land c ξ) := by
  have hs₀ : 0 ≤ s₀ := hT0.trans hTs
  have hyT0 : yT ≠ 0 := fun h => by rw [h, mul_zero] at hyT; exact lt_irrefl _ hyT
  obtain ⟨ε₁, hε₁, himg⟩ := exists_ball_image hR (mem_ball_self hρ)
  rw [hφv₁] at himg
  have hV := QuantumZipper.RS.continuous_shiftDrive hW T
  have hV0 := QuantumZipper.RS.shiftDrive_zero W T
  have hsT : 0 ≤ s₀ - T := sub_nonneg.2 hTs
  set ρ' : ℝ := min ε₁ |yT| / 2 with hρ'def
  have hρ' : 0 < ρ' := by have := lt_min hε₁ (abs_pos.2 hyT0); simp only [hρ'def]; linarith
  have hρ'1 : ρ' < ε₁ := by have := min_le_left ε₁ |yT|; simp only [hρ'def]; linarith
  have hρ'2 : ρ' < |yT| := by have := min_le_right ε₁ |yT|; simp only [hρ'def]; linarith
  have hK : ∀ z ∈ ball (yT : ℂ) ρ', 0 < z.im → z ∉ fwdHull (shiftDrive W T) (s₀ - T) := by
    intro z hz hzH
    have hz' : z ∈ ball (yT : ℂ) ε₁ := ball_subset_ball hρ'1.le hz
    obtain ⟨u, hu, -, hφu, hpos, -⟩ := himg z hz' hzH.le
    have huH : u ∈ H := hpos hzH
    obtain ⟨h1, -, h3⟩ := hD u ⟨huH, hu⟩
    refine notMem_fwdHull_shift hη hW hW0 hT0 hTs (show z ∈ H from hzH) ?_
    rw [← hφu, h3]
    exact h1
  obtain ⟨u, hu⟩ := Supp8.GB8.alive_of_ball hV hV0 hsT hρ' hρ'2 hK (yT : ℂ) (mem_ball_self (by linarith))
  have hsgn := mul_re_pos_of_isForwardSol_real hV hV0 hyT0 hsT hu
  set y : ℝ := (u (s₀ - T)).re with hydef
  have huy : u (s₀ - T) = (y : ℂ) := Complex.ext (by simp [hydef]) (by simp [hsgn.1])
  have hεy : 0 < ε * y := by
    have h2 : 0 < yT * y := hsgn.2
    rcases hε with he | he <;> rw [he] at hyT ⊢
    · have : 0 < yT := by linarith
      nlinarith
    · have : yT < 0 := by linarith
      nlinarith
  -- the limit at `s₀`
  set N := 𝓝[H] (ξ : ℂ) with hN
  have hHB : H ∩ ball (ξ : ℂ) ρ ∈ N := inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hρ))
  have hφt : Tendsto (fun w => G (negInv (land c w))) N (𝓝[H] (yT : ℂ)) := by
    have h1 := (hR.2.1 _ ⟨IsArcChart.ofReal_mem_Hbar _, mem_ball_self hρ⟩).tendsto
    rw [hφv₁] at h1
    refine tendsto_nhdsWithin_iff.2 ⟨h1.mono_left (nhdsWithin_le_of_mem ?_), ?_⟩
    · exact mem_of_superset hHB fun w hw => ⟨QuantumZipper.H_subset_Hbar hw.1, hw.2⟩
    · filter_upwards [hHB] with w hw using hR.2.2.2.1 hw
  have hDsN : ∀ w ∈ H ∩ ball (ξ : ℂ) ρ, negInv (c.2.1 w) ∈ H \ fwdHull W s₀ := fun w hw => by
    rw [← hlandH w hw.1]; exact (hD w hw).1
  have hshift : ∀ᶠ w in N, fwdMap (shiftDrive W T) (s₀ - T) (G (negInv (land c w))) =
      fwdMap W s₀ (negInv (c.2.1 w)) := by
    filter_upwards [hHB] with w hw
    have hzD := hDsN w hw
    rw [(hD w hw).2.1, hlandH w hw.1]
    have hz' : negInv (c.2.1 w) ∈ H \ fwdHull W (T + (s₀ - T)) := by rw [add_sub_cancel]; exact hzD
    have := (fwdMap_add_shift hW hW0 hT0 hsT hz').2
    rw [add_sub_cancel] at this
    exact this
  have hlim : Tendsto (fun w => fwdMap W s₀ (negInv (c.2.1 w))) N (𝓝 (y : ℂ)) := by
    have h := (tendsto_fwdMap_of_isForwardSol hV hsT hu).comp hφt
    rw [huy] at h
    exact h.congr' hshift
  refine ⟨y, hlim, hεy, ?_⟩
  -- `f̄_{s₀}(y)` is the arc point
  have hzlim : Tendsto (fun w => negInv (c.2.1 w)) N (𝓝 (negInv (land c ξ))) := by
    have h1 : Tendsto (land c) N (𝓝 (land c ξ)) :=
      ((hlandC _ (IsArcChart.ofReal_mem_Hbar _)).tendsto).mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)
    have h2 : Tendsto (fun w => negInv (land c w)) N (𝓝 (negInv (land c ξ))) :=
      (WangWu.continuousAt_negInv hland0).tendsto.comp h1
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [hlandH w hw]
  have hinv : ∀ᶠ w in N, trMap W 0 s₀ (fwdMap W s₀ (negInv (c.2.1 w))) = negInv (c.2.1 w) := by
    filter_upwards [hHB] with w hw
    have hzD := hDsN w hw
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hs₀ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs₀ hzD),
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero, QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs₀ hzD]
  have hlimH : Tendsto (fun w => fwdMap W s₀ (negInv (c.2.1 w))) N (𝓝[Hbar] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
    filter_upwards [hHB] with w hw
    exact QuantumZipper.H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs₀ (hDsN w hw))
  have hNe : N.NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact IsArcChart.ofReal_mem_Hbar _)
  have hc := ((YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs₀) _
    (IsArcChart.ofReal_mem_Hbar y)).tendsto.comp hlimH
  exact tendsto_nhds_unique hc (hzlim.congr' (hinv.mono fun w hw => hw.symm))

/-- **The traversal side (PFI3) at a rational witness** (see the module docstring). -/
theorem exists_side_limit {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {A : ℝ → ℂ} {P : Set ℂ}
    {X : ℝ≥0 → ℂ} {Wu : Set ℂ} {lo hi : ℝ} {c : Chart} {κ : ℂ → ℂ} {f : ℝ → ℝ} {ε : ℝ}
    (hS : IsArcChart C A P X Wu lo hi c κ f ε) {r₀ s₀ a₀ v v₁ v₂ : ℝ} (hV : IsArcVisit W η C A r₀ s₀ a₀ v v₂)
    (hvv₁ : v < v₁) (hv₁v₂ : v₁ < v₂) :
    ∃ y : ℝ, Tendsto (fun w => fwdMap W s₀ (negInv (c.2.1 w))) (𝓝[H] (f v₁ : ℂ)) (𝓝 (y : ℂ)) ∧ 0 < ε * y ∧
      trMap W 0 s₀ y = A v₁ := by
  obtain ⟨T, G, ρ, yT, hT0, hTs, hρ, hR, hD, hφ, hyT⟩ := exists_sign_first_visit hS hV hvv₁ hv₁v₂
  have hv₁I : v₁ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hV.pos, hV.a₀_lt], by linarith [hV.lt_one]⟩
  have hl0 : land c (f v₁) ≠ 0 := hS.land0 _ (IsArcChart.ofReal_mem_Hbar _)
    (by have := hS.ne_zero v₁ hv₁I; intro h; rw [Complex.ofReal_eq_zero.1 h, mul_zero] at this; exact lt_irrefl _ this)
  obtain ⟨y, h1, h2, h3⟩ := exists_side_transport hV.trace hV.continuous_W hV.W_zero hS.landC hS.landH hl0
    hT0 hTs hρ hR hD hφ hS.sign hyT
  exact ⟨y, h1, h2, by rw [h3, hS.negInv_land hv₁I]⟩

end Side

end InteractingSLE.Sec7.Aux37Side
