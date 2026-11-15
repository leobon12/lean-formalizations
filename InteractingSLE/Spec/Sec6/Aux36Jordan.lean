/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Topology.Schoenflies.Disc
import InteractingSLE.Foundations.Complex.RiemannMap
import LQGMetric.Papers.GM.S4.P412cLC

/-!
# Jordan coordinates and boundary extensions onto `ℍ` (Aux. lemmas 40–41, (RG4)–(RG5))

Specification §6.2, **Aux.** lemma 41 (`source/spec/p193-240.md` L214–L265, pp. 204–206): "Let
`ψ : C → ℍ` be the Jordan coordinate with `ψ(y₀) = 0` and `ψ(x₀) = ∞`", and (RG4)–(RG5): "The domain
`F_s` is Jordan in the sphere, so `Φ_s` extends to a boundary homeomorphism. Its pole is the
boundary point over `x₀`". Ruling R41's note (`ig1_ztip_elimination.txt` L313–L316): "The conformal
map from
`F_s` to the half-plane of the relative erased hull extends homeomorphically to its boundary. Its
pole is the pocket target".

Both are proved here from the closed-disc Schoenflies theorem
(`Foundations.Schoenflies.schoenflies_disc`), the Cayley transform and the classification of the
automorphisms of the unit disc (`exists_eqOn_mul_diskMobius_of_isConformalBijection`).

## Main results

* `exists_discChart`: the Schoenflies chart `φ : 𝔻̄ → D̄` of a bounded Jordan domain `D` together
  with its continuous inverse `χ : D̄ → 𝔻̄`, holomorphic on `D`;
* `exists_bdryExt_of_isConformalBijection`: **a conformal bijection `Φ : D → ℍ` of a bounded Jordan
  domain extends continuously to `D̄ \ {x₀}`** for one boundary point `x₀` (its pole), with values
  in `ℍ̄` and `Φ → ∞` at `x₀`;
* `exists_jordanCoord`: **the Jordan coordinate** of a bounded Jordan domain `C` with distinct
  boundary points `x₀, y₀`: a homeomorphism `ψ : C̄ \ {x₀} → ℍ̄`, conformal from `C` onto `ℍ`, real
  on
  `∂C \ {x₀}`, with `ψ(y₀) = 0` and `ψ → ∞` at `x₀`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function Bornology
open scoped ComplexConjugate

open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA (cayley cayleyInv diskMobius)
open LQGMetric.JordanMap (IsJordanCurve)

namespace InteractingSLE.Sec6

/-! ### The Schoenflies chart and its inverse -/

/-- The closure of the image of the open disc under a map continuous on the closed disc. -/
theorem closure_image_ball_eq {φ : ℂ → ℂ} (hφc : ContinuousOn φ (closedBall 0 1)) :
    closure (φ '' ball 0 1) = φ '' closedBall 0 1 := by
  refine Subset.antisymm (closure_minimal (image_mono ball_subset_closedBall)
    ((isCompact_closedBall 0 1).image_of_continuousOn hφc).isClosed) ?_
  have h := closure_ball (0 : ℂ) (one_ne_zero (α := ℝ))
  rw [← h] at hφc ⊢
  exact hφc.image_closure

/-- **The Schoenflies chart of a bounded Jordan domain with its inverse.** For a Jordan curve `Γ`
and the bounded component `D` of `Γᶜ` through `p`, there are `φ` (continuous on `𝔻̄`, holomorphic on
`𝔻`) and `χ` (continuous on `D̄`, holomorphic on `D`), mutually inverse between `𝔻̄` and `D̄`, with
`φ(𝔻) = D`, `φ(∂𝔻) = Γ`, `D̄ = φ(𝔻̄)`. -/
theorem exists_discChart {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) :
    ∃ φ χ : ℂ → ℂ, ContinuousOn φ (closedBall 0 1) ∧
      ContinuousOn χ (closure (connectedComponentIn Γᶜ p)) ∧
      (∀ w ∈ closedBall (0 : ℂ) 1, χ (φ w) = w) ∧
      (∀ z ∈ closure (connectedComponentIn Γᶜ p), φ (χ z) = z) ∧
      MapsTo χ (closure (connectedComponentIn Γᶜ p)) (closedBall 0 1) ∧
      MapsTo χ (connectedComponentIn Γᶜ p) (ball 0 1) ∧ MapsTo χ Γ (sphere 0 1) ∧
      φ '' ball 0 1 = connectedComponentIn Γᶜ p ∧ φ '' sphere 0 1 = Γ ∧
      closure (connectedComponentIn Γᶜ p) = φ '' closedBall 0 1 ∧
      DifferentiableOn ℂ φ (ball 0 1) ∧ DifferentiableOn ℂ χ (connectedComponentIn Γᶜ p) := by
  set D := connectedComponentIn Γᶜ p with hDdef
  obtain ⟨φ, hφc, hφi, hφd, -, hφball, hφsph⟩ := Foundations.Schoenflies.schoenflies_disc hΓ hp hb
  rw [← hDdef] at hφball
  set χ := invFunOn φ (closedBall 0 1) with hχdef
  have hcl : closure D = φ '' closedBall 0 1 := by rw [← hφball]; exact closure_image_ball_eq hφc
  have hχφ : ∀ w ∈ closedBall (0 : ℂ) 1, χ (φ w) = w := fun w hw => hφi.leftInvOn_invFunOn hw
  have hφχ : ∀ z ∈ closure D, φ (χ z) = z := by
    intro z hz
    rw [hcl] at hz
    exact (surjOn_image φ (closedBall 0 1)).rightInvOn_invFunOn hz
  have hχmaps : MapsTo χ (closure D) (closedBall 0 1) := by
    intro z hz
    rw [hcl] at hz
    exact (surjOn_image φ (closedBall 0 1)).mapsTo_invFunOn hz
  have hχD : MapsTo χ D (ball 0 1) := by
    intro z hz
    rw [← hφball] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hχφ w (ball_subset_closedBall hw)]; exact hw
  have hχΓ : MapsTo χ Γ (sphere 0 1) := by
    intro z hz
    rw [← hφsph] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [hχφ w (sphere_subset_closedBall hw)]; exact hw
  have hχc : ContinuousOn χ (closure D) := by
    rw [hcl]; exact LQGMetric.GM.p412c_invFun_contOn (isCompact_closedBall 0 1) hφc hφi
  -- holomorphy of `χ` on `D`: it agrees there with the holomorphic inverse of `φ|𝔻`
  have hφi' : InjOn φ (ball 0 1) := hφi.mono ball_subset_closedBall
  have hχd : DifferentiableOn ℂ χ D := by
    have hs := QuantumZipper.CA.differentiableOn_univalentOPH_symm isOpen_ball hφd hφi'
    rw [hφball] at hs
    refine hs.congr fun z hz => ?_
    have hz' : z ∈ φ '' ball 0 1 := by rw [hφball]; exact hz
    obtain ⟨w, hw, rfl⟩ := hz'
    rw [hχφ w (ball_subset_closedBall hw),
      QuantumZipper.CA.univalentOPH_symm_apply_apply isOpen_ball hφd hφi' hw]
  exact ⟨φ, χ, hφc, hχc, hχφ, hφχ, hχmaps, hχD, hχΓ, hφball, hφsph, hcl, hφd, hχd⟩

/-! ### Disc Möbius maps on the closed disc -/

theorem norm_diskMobius_le_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖diskMobius a z‖ ≤ 1 := by
  have h := QuantumZipper.CA.one_sub_sq_norm_diskMobius ha hz
  have h0 : 0 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / normSq (1 - conj a * z) :=
    div_nonneg (mul_nonneg (by nlinarith [norm_nonneg a]) (by nlinarith [norm_nonneg z]))
      (normSq_nonneg _)
  nlinarith [norm_nonneg (diskMobius a z)]

theorem norm_diskMobius_eq_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    ‖diskMobius a z‖ = 1 := by
  have h := QuantumZipper.CA.one_sub_sq_norm_diskMobius ha hz.le
  rw [hz, one_pow, sub_self, mul_zero, zero_div] at h
  have h1 : ‖diskMobius a z‖ ^ 2 = 1 := by linarith
  nlinarith [norm_nonneg (diskMobius a z)]

theorem diskMobius_diskMobius_neg {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    diskMobius a (diskMobius (-a) z) = z := by
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  have := QuantumZipper.CA.diskMobius_neg_diskMobius hna hz
  rwa [neg_neg] at this

/-- The imaginary part of `cayleyInv` vanishes on the unit circle. -/
theorem im_cayleyInv_eq_zero {w : ℂ} (hw : ‖w‖ = 1) : (cayleyInv w).im = 0 := by
  rw [QuantumZipper.CA.im_cayleyInv, hw, one_pow, sub_self, zero_div]

/-- `ψ(z) → ∞` survives subtracting a constant. -/
theorem tendsto_sub_const_cobounded {l : Filter ℂ} {f : ℂ → ℂ} (hf : Tendsto f l (cobounded ℂ))
    (c : ℂ) : Tendsto (fun z => f z - c) l (cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded] at hf ⊢
  refine tendsto_atTop_mono (fun z => ?_) (tendsto_atTop_add_const_right _ (-‖c‖) hf)
  have := norm_sub_norm_le (f z) c
  linarith

/-! ### Boundary extension of a conformal bijection onto `ℍ` -/

/-- **A conformal bijection of a bounded Jordan domain onto `ℍ` extends to the boundary** (the
Jordan-face step of (RG4)–(RG5), Specification p. 206: "The domain `F_s` is Jordan in the sphere, so
`Φ_s` extends to a boundary homeomorphism. Its pole is the boundary point over `x₀`"). If `D` is the
bounded component of `Γᶜ` through `p` (`Γ` a Jordan curve) and `Φ : D → ℍ` is a conformal bijection,
there are a boundary point `x₀ ∈ Γ` (the pole) and `Φ'` agreeing with `Φ` on `D`, continuous on
`D̄ \ {x₀}` with values in `ℍ̄`, and `Φ → ∞` at `x₀` within `D`.

*Proof.* With the Schoenflies chart `φ : 𝔻̄ → D̄`, `cayley ∘ Φ ∘ φ` is a conformal automorphism of
`𝔻`, hence `w ↦ u (w − a)/(1 − ā w)`; this Möbius map `m` is continuous and injective on `𝔻̄`,
maps `∂𝔻` to `∂𝔻`, and takes the value `1` at exactly one point `w₀ ∈ ∂𝔻`. Put `x₀ = φ(w₀)` and
`Φ' = cayleyInv ∘ m ∘ φ⁻¹`. -/
theorem exists_bdryExt_of_isConformalBijection {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ}
    (hp : p ∈ Γᶜ) (hb : IsBounded (connectedComponentIn Γᶜ p)) {Φ : ℂ → ℂ}
    (hΦ : IsConformalBijection Φ (connectedComponentIn Γᶜ p) H) :
    ∃ x₀ ∈ Γ, ∃ Φ' : ℂ → ℂ, EqOn Φ' Φ (connectedComponentIn Γᶜ p) ∧
      ContinuousOn Φ' (closure (connectedComponentIn Γᶜ p) \ {x₀}) ∧
      MapsTo Φ' (closure (connectedComponentIn Γᶜ p) \ {x₀}) Hbar ∧
      Tendsto Φ (𝓝[connectedComponentIn Γᶜ p] x₀) (cobounded ℂ) := by
  obtain ⟨φ, χ, hφc, hχc, hχφ, hφχ, hχcl, hχD, -, hφball, hφsph, hcl, hφd, -⟩ :=
    exists_discChart hΓ hp hb
  set D := connectedComponentIn Γᶜ p with hDdef
  have hφbij : IsConformalBijection φ (ball 0 1) D := by
    refine ⟨hφd, fun w hw => hφball ▸ mem_image_of_mem φ hw, fun w hw w' hw' h => ?_,
      fun z hz => by rw [← hφball] at hz; exact hz⟩
    rw [← hχφ w (ball_subset_closedBall hw), ← hχφ w' (ball_subset_closedBall hw'), h]
  have hcay : IsConformalBijection cayley H (ball 0 1) :=
    ⟨QuantumZipper.CA.differentiableOn_cayley_Hbar.mono QuantumZipper.H_subset_Hbar,
      QuantumZipper.CA.bijOn_cayley_H⟩
  have hh := isConformalBijection_comp hcay (isConformalBijection_comp hΦ hφbij)
  obtain ⟨u, a, hu, ha, hEq⟩ := exists_eqOn_mul_diskMobius_of_isConformalBijection hh
  have ha' : ‖a‖ < 1 := mem_ball_zero_iff.1 ha
  have hna : ‖-a‖ < 1 := by rwa [norm_neg]
  set m : ℂ → ℂ := fun w => u * diskMobius a w with hmdef
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; exact zero_ne_one hu
  have hm_cont : ContinuousOn m (closedBall 0 1) :=
    continuousOn_const.mul (QuantumZipper.CA.differentiableOn_diskMobius ha').continuousOn
  have hm_le : ∀ w ∈ closedBall (0 : ℂ) 1, ‖m w‖ ≤ 1 := fun w hw => by
    simp only [hmdef, norm_mul, hu, one_mul]
    exact norm_diskMobius_le_one ha' (mem_closedBall_zero_iff.1 hw)
  have hm_ball : ∀ w ∈ ball (0 : ℂ) 1, m w ≠ 1 := fun w hw h => by
    have h1 := mem_ball_zero_iff.1 (QuantumZipper.CA.diskMobius_mem_ball ha' hw)
    have h2 : ‖m w‖ = ‖diskMobius a w‖ := by simp only [hmdef, norm_mul, hu, one_mul]
    rw [h, norm_one] at h2
    linarith
  -- the pole `w₀`
  set w₀ := diskMobius (-a) (conj u) with hw₀def
  have hcu : ‖conj u‖ = 1 := by rw [Complex.norm_conj, hu]
  have hw₀s : ‖w₀‖ = 1 := norm_diskMobius_eq_one hna hcu
  have hw₀cb : w₀ ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.2 hw₀s.le
  have hmw₀ : m w₀ = 1 := by
    simp only [hmdef, hw₀def, diskMobius_diskMobius_neg ha' hcu.le]
    rw [Complex.mul_conj', hu]; norm_num
  have hm_one : ∀ w ∈ closedBall (0 : ℂ) 1, m w = 1 → w = w₀ := by
    intro w hw h
    have h1 : diskMobius a w = diskMobius a w₀ := by
      have := h.trans hmw₀.symm
      exact mul_left_cancel₀ hu0 this
    have h2 := congrArg (diskMobius (-a)) h1
    rwa [QuantumZipper.CA.diskMobius_neg_diskMobius ha' (mem_closedBall_zero_iff.1 hw),
      QuantumZipper.CA.diskMobius_neg_diskMobius ha' hw₀s.le] at h2
  set x₀ := φ w₀ with hx₀def
  have hx₀Γ : x₀ ∈ Γ := hφsph ▸ mem_image_of_mem φ (mem_sphere_zero_iff_norm.2 hw₀s)
  have hx₀cl : x₀ ∈ closure D := by rw [hcl]; exact mem_image_of_mem φ hw₀cb
  have hχx₀ : χ x₀ = w₀ := hχφ w₀ hw₀cb
  refine ⟨x₀, hx₀Γ, fun z => cayleyInv (m (χ z)), ?_, ?_, ?_, ?_⟩
  · -- agreement with `Φ` on `D`
    intro z hz
    have hzb := hχD hz
    have h1 := hEq hzb
    simp only [comp_apply, hφχ z (subset_closure hz)] at h1
    show cayleyInv (m (χ z)) = Φ z
    rw [← h1, QuantumZipper.CA.cayleyInv_cayley
      (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt (hΦ.2.mapsTo hz)))]
  · -- continuity off the pole
    have hne : MapsTo (fun z => m (χ z)) (closure D \ {x₀}) {w | w ≠ 1} := by
      intro z hz h
      have := hm_one _ (hχcl hz.1) h
      apply hz.2
      rw [← hφχ z hz.1, this]
      exact mem_singleton_iff.2 rfl
    exact QuantumZipper.CA.continuousOn_cayleyInv.comp
      (hm_cont.comp (hχc.mono sdiff_subset) (hχcl.mono_left sdiff_subset)) hne
  · intro z hz
    exact QuantumZipper.CA.cayleyInv_mem_Hbar (mem_closedBall_zero_iff.2 (hm_le _ (hχcl hz.1)))
  · -- `Φ → ∞` at the pole
    have hχt : Tendsto χ (𝓝[D] x₀) (𝓝[closedBall 0 1] w₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
        ball_subset_closedBall (hχD hz)⟩
      have := ((hχc x₀ hx₀cl).mono subset_closure).tendsto
      rwa [hχx₀] at this
    have hmt : Tendsto (fun z => m (χ z)) (𝓝[D] x₀) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
        hm_ball _ (hχD hz)⟩
      have := (hm_cont w₀ hw₀cb).tendsto.comp hχt
      rwa [hmw₀] at this
    refine (QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.comp hmt).congr'
      (eventually_nhdsWithin_of_forall fun z hz => ?_)
    have hzb := hχD hz
    have h1 := hEq hzb
    simp only [comp_apply, hφχ z (subset_closure hz)] at h1
    show cayleyInv (m (χ z)) = Φ z
    rw [← h1, QuantumZipper.CA.cayleyInv_cayley
      (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (le_of_lt (hΦ.2.mapsTo hz)))]

/-! ### The Jordan coordinate -/

/-- **The Jordan coordinate of a bounded Jordan domain** (Aux. lemma 41: "Let `ψ : C → ℍ` be the
Jordan coordinate with `ψ(y₀) = 0` and `ψ(x₀) = ∞`"; Aux. lemma 40: "a Jordan coordinate of `C`
with `x₀` at infinity"). Let `D` be the bounded component of `Γᶜ` through `p` (`Γ` a Jordan curve)
and `x₀, y₀` points of `Γ` (distinct in every application). There are `ψ` and `ψinv`, mutually
inverse homeomorphisms between
`D̄ \ {x₀}` and `ℍ̄`, with `ψ` a conformal bijection `D → ℍ`, real on `Γ \ {x₀}`, `ψ(y₀) = 0`, and
`ψ → ∞` at `x₀`.

*Proof.* With the Schoenflies chart `φ`, `χ = φ⁻¹`, `w_x = χ(x₀)`, put
`ψ(z) = cayleyInv(w̄_x χ(z)) − c`, `c = cayleyInv(w̄_x χ(y₀))` (real, as `|w̄_x χ(y₀)| = 1`), and
`ψinv(w) = φ(w_x cayley(w + c))`. -/
theorem exists_jordanCoord {Γ : Set ℂ} (hΓ : IsJordanCurve Γ) {p : ℂ} (hp : p ∈ Γᶜ)
    (hb : IsBounded (connectedComponentIn Γᶜ p)) {x₀ y₀ : ℂ} (hx₀ : x₀ ∈ Γ) (hy₀ : y₀ ∈ Γ) :
    ∃ ψ ψinv : ℂ → ℂ, ContinuousOn ψ (closure (connectedComponentIn Γᶜ p) \ {x₀}) ∧
      MapsTo ψ (closure (connectedComponentIn Γᶜ p) \ {x₀}) Hbar ∧
      ContinuousOn ψinv Hbar ∧ MapsTo ψinv Hbar (closure (connectedComponentIn Γᶜ p) \ {x₀}) ∧
      (∀ z ∈ closure (connectedComponentIn Γᶜ p) \ {x₀}, ψinv (ψ z) = z) ∧
      (∀ w ∈ Hbar, ψ (ψinv w) = w) ∧
      IsConformalBijection ψ (connectedComponentIn Γᶜ p) H ∧
      (∀ z ∈ Γ \ {x₀}, (ψ z).im = 0) ∧ ψ y₀ = 0 ∧
      Tendsto ψ (𝓝[closure (connectedComponentIn Γᶜ p) \ {x₀}] x₀) (cobounded ℂ) := by
  obtain ⟨φ, χ, hφc, hχc, hχφ, hφχ, hχcl, hχD, hχΓ, hφball, hφsph, hcl, hφd, hχd⟩ :=
    exists_discChart hΓ hp hb
  set D := connectedComponentIn Γᶜ p with hDdef
  have hΓcl : Γ ⊆ closure D := by
    rw [hcl, ← hφsph]; exact image_mono sphere_subset_closedBall
  have hDΓ : ∀ z ∈ D, z ∉ Γ := fun z hz hzΓ => (connectedComponentIn_subset _ _ hz) hzΓ
  set wx := χ x₀ with hwxdef
  have hwx : ‖wx‖ = 1 := mem_sphere_zero_iff_norm.1 (hχΓ hx₀)
  have hwy : ‖χ y₀‖ = 1 := mem_sphere_zero_iff_norm.1 (hχΓ hy₀)
  have hcw : conj wx * wx = 1 := by rw [Complex.conj_mul', hwx]; norm_num
  have hwc : wx * conj wx = 1 := by rw [mul_comm]; exact hcw
  set m : ℂ → ℂ := fun w => conj wx * w with hmdef
  have hm_norm : ∀ w, ‖m w‖ = ‖w‖ := fun w => by
    simp only [hmdef, norm_mul, Complex.norm_conj, hwx, one_mul]
  have hm_one : ∀ w, m w = 1 → w = wx := fun w h => by
    have := congrArg (fun v => wx * v) h
    simp only [hmdef, ← mul_assoc, hwc, one_mul, mul_one] at this
    exact this
  have hmx : m wx = 1 := hcw
  set c : ℝ := (cayleyInv (m (χ y₀))).re with hcdef
  have hcre : cayleyInv (m (χ y₀)) = (c : ℂ) := by
    apply Complex.ext
    · simp [hcdef]
    · rw [im_cayleyInv_eq_zero (by rw [hm_norm, hwy]), ofReal_im]
  set ψ : ℂ → ℂ := fun z => cayleyInv (m (χ z)) - c with hψdef
  set ψinv : ℂ → ℂ := fun w => φ (wx * cayley (w + c)) with hψinvdef
  -- elementary facts
  have hne1 : ∀ z ∈ closure D \ {x₀}, m (χ z) ≠ 1 := by
    intro z hz h
    apply hz.2
    rw [← hφχ z hz.1, hm_one _ h, hwxdef, hφχ x₀ (hΓcl hx₀)]
    exact mem_singleton_iff.2 rfl
  have hmcb : ∀ z ∈ closure D, m (χ z) ∈ closedBall (0 : ℂ) 1 := fun z hz => by
    rw [mem_closedBall_zero_iff, hm_norm]; exact mem_closedBall_zero_iff.1 (hχcl hz)
  have him : ∀ w : ℂ, (w - (c : ℂ)).im = w.im := fun w => by simp
  have hcHbar : ∀ w ∈ Hbar, w + (c : ℂ) ∈ Hbar := fun w hw => by
    have hw' : 0 ≤ w.im := hw
    show 0 ≤ (w + (c : ℂ)).im
    simpa using hw'
  have hcay_mem : ∀ w ∈ Hbar, wx * cayley (w + c) ∈ closedBall (0 : ℂ) 1 := fun w hw => by
    rw [mem_closedBall_zero_iff, norm_mul, hwx, one_mul]
    exact mem_closedBall_zero_iff.1 (QuantumZipper.CA.cayley_mem_closedBall (hcHbar w hw))
  have hcay_ne : ∀ w ∈ Hbar, cayley (w + c) ≠ 1 := fun w hw =>
    QuantumZipper.CA.cayley_ne_one (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (hcHbar w hw))
  have hψψinv : ∀ w ∈ Hbar, ψ (ψinv w) = w := by
    intro w hw
    simp only [hψdef, hψinvdef]
    rw [hχφ _ (hcay_mem w hw)]
    simp only [hmdef, ← mul_assoc, hcw, one_mul]
    rw [QuantumZipper.CA.cayleyInv_cayley
      (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (hcHbar w hw)), add_sub_cancel_right]
  have hψinvψ : ∀ z ∈ closure D \ {x₀}, ψinv (ψ z) = z := by
    intro z hz
    simp only [hψdef, hψinvdef, sub_add_cancel]
    rw [QuantumZipper.CA.cayley_cayleyInv (hne1 z hz)]
    simp only [hmdef, ← mul_assoc, hwc, one_mul]
    exact hφχ z hz.1
  have hψHbar : MapsTo ψ (closure D \ {x₀}) Hbar := by
    intro z hz
    show 0 ≤ (ψ z).im
    simp only [hψdef, him]
    exact QuantumZipper.CA.cayleyInv_mem_Hbar (hmcb z hz.1)
  have hψinvmaps : MapsTo ψinv Hbar (closure D \ {x₀}) := by
    intro w hw
    refine ⟨by rw [hcl]; exact mem_image_of_mem φ (hcay_mem w hw), fun h => ?_⟩
    have h1 : φ (wx * cayley (w + c)) = φ wx := by
      rw [show φ wx = x₀ from hφχ x₀ (hΓcl hx₀)]; exact h
    have h2 := congrArg χ h1
    rw [hχφ _ (hcay_mem w hw), hχφ _ (hχcl (hΓcl hx₀))] at h2
    have h3 : cayley (w + c) = 1 := by
      have := congrArg (fun v => conj wx * v) h2
      simp only [← mul_assoc, hcw, one_mul] at this
      rw [this, ← hwxdef, hcw]
    exact hcay_ne w hw h3
  have hmcont : ContinuousOn (fun z => m (χ z)) (closure D) :=
    continuousOn_const.mul hχc
  refine ⟨ψ, ψinv, ?_, hψHbar, ?_, hψinvmaps, hψinvψ, hψψinv, ?_, ?_, ?_, ?_⟩
  · -- continuity of `ψ`
    exact (QuantumZipper.CA.continuousOn_cayleyInv.comp (hmcont.mono sdiff_subset)
      (fun z hz => hne1 z hz)).sub continuousOn_const
  · -- continuity of `ψinv`
    have h1 : ContinuousOn (fun w : ℂ => w + (c : ℂ)) Hbar := continuousOn_id.add continuousOn_const
    have h2 : ContinuousOn (fun w : ℂ => cayley (w + c)) Hbar :=
      QuantumZipper.CA.continuousOn_cayley.comp h1 fun w hw =>
        QuantumZipper.CA.ne_neg_I_iff.2 (QuantumZipper.CA.add_I_ne_zero_of_im_nonneg (hcHbar w hw))
    exact hφc.comp (continuousOn_const.mul h2) hcay_mem
  · -- conformal bijection `D → ℍ`
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      have hb1 : m (χ z) ≠ 1 := hne1 z ⟨subset_closure hz, fun h => hDΓ z hz (h ▸ hx₀)⟩
      have hd : DifferentiableWithinAt ℂ (fun z => m (χ z)) D z :=
        (differentiableWithinAt_const _).mul (hχd z hz)
      exact ((QuantumZipper.CA.differentiableAt_cayleyInv hb1).comp_differentiableWithinAt z
        hd).sub (differentiableWithinAt_const _)
    · intro z hz
      show 0 < (ψ z).im
      simp only [hψdef, him]
      refine QuantumZipper.CA.cayleyInv_mem_H ?_
      rw [mem_ball_zero_iff, hm_norm]; exact mem_ball_zero_iff.1 (hχD hz)
    · intro z hz z' hz' h
      have hzx : z ∈ closure D \ {x₀} := ⟨subset_closure hz, fun h' => hDΓ z hz (h' ▸ hx₀)⟩
      have hzx' : z' ∈ closure D \ {x₀} := ⟨subset_closure hz', fun h' => hDΓ z' hz' (h' ▸ hx₀)⟩
      rw [← hψinvψ z hzx, ← hψinvψ z' hzx', h]
    · intro w hw
      refine ⟨ψinv w, ?_, hψψinv w (QuantumZipper.H_subset_Hbar hw)⟩
      have hwc : w + (c : ℂ) ∈ H := by
        have hw' : 0 < w.im := hw
        show 0 < (w + (c : ℂ)).im
        simpa using hw'
      have hb1 : wx * cayley (w + c) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, norm_mul, hwx, one_mul]
        exact mem_ball_zero_iff.1 (QuantumZipper.CA.cayley_mem_ball hwc)
      rw [← hφball]
      exact mem_image_of_mem φ hb1
  · -- real on the boundary
    intro z hz
    simp only [hψdef, him]
    exact im_cayleyInv_eq_zero (by rw [hm_norm]; exact mem_sphere_zero_iff_norm.1 (hχΓ hz.1))
  · simp only [hψdef, hcre, sub_self]
  · -- `ψ → ∞` at `x₀`
    have hx₀cl : x₀ ∈ closure D := hΓcl hx₀
    have hmt : Tendsto (fun z => m (χ z)) (𝓝[closure D \ {x₀}] x₀) (𝓝[≠] 1) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz =>
        hne1 z hz⟩
      have := ((hmcont x₀ hx₀cl).mono (sdiff_subset (t := {x₀}))).tendsto
      have hmx' : m (χ x₀) = 1 := hmx
      rwa [hmx'] at this
    exact tendsto_sub_const_cobounded
      (QuantumZipper.CA.tendsto_cayleyInv_nhdsNE_one.comp hmt) _

end InteractingSLE.Sec6
