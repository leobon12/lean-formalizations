/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTildeMart
import InteractingSLE.Spec.Ito.Measurability

/-!
# The stopped martingale of `M̃` for ordinary `SLE_κ` with the other curve frozen

Packet PROVE-ZHAN-GT4-A8. Source: Astra, *Follow-up proofs*, §A.1.2–A.1.3 (`ig1_followup_proofs.txt` L268–L341, R38):
"First suppose `W_j` has zero drift. Using (D3)–(D5), the coefficient of `dW_j` in `d_j M̃/M̃` is `q_j` … Hence the drift
is zero", and (D9): `M̃` is bounded above and below on the protected rectangle.

For ordinary chordal `SLE_κ` (driver `W = √κ B`), the frozen hull `A` of the other curve with mapping-out function `φ`,
per-path image chains `(W' ω, a ω)` (`OwnData` up to `T ω ≥ S ω`), marks `ζ₀`, `ζ_m` of the `φ`-chart alive up to
`a(T)`, and the (D9) constants (`D9Const`, with a deterministic scale `L`), the logarithm `ℓ = log M̃` of A7's `FrzData`
is a log-field along the driver up to the stopping time `S` (`isDriverLogField_frozen`): the local regularity is A7's
`FrzData.isLogField_of_D9`, the vanishing generator is A7's `FrzData.cutField_gen_eq_zero_of_D9` at the centre, and the
measurability is `FrozenMeas`. Hence (`integral_mul_MTilde_stopped_sub_eq_zero`)

  `E[ξ (M̃_{t∧S} − M̃_{s∧S})] = 0` for bounded `𝓕_s`-measurable `ξ`.

## Main results

* `frzDataOf`, `frzMeas_of_adapted` (the measurability inputs of `FrozenMeas` from an adapted continuous `B`);
* `FrzMartHyp` (the hypotheses), `isDriverLogField_frozen`, **`integral_mul_MTilde_stopped_sub_eq_zero`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap drive)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The frozen data of `M̃` along the path `ω`: the driver `√κ B`, the image chain `(W' ω, a ω)`. -/
def frzDataOf {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (φ : ℂ → ℂ) (r : Fin n → ℝ) (ζ₀ : ℝ)
    (ζ : Fin n → ℝ) (ω : Ω) : FrzData n :=
  ⟨drive κ B ω, W' ω, a ω, φ, κ, r, ζ₀, ζ⟩

/-! ### The measurability inputs from an adapted driver -/

/-- **`FrzMeas` from an adapted continuous Brownian path.** For `W = √κ B`, on an `𝓕_r`-event `G` on which `OwnData`
holds up to `T ω ≥ u` (`0 ≤ u ≤ r`), the measurability inputs of `FrozenMeas` hold at time `u` for the σ-algebra
`𝓕_r` (`Ito.measurableSet_aliveSet`, `Ito.measurable_fwdMap_alive`). -/
theorem frzMeas_of_adapted {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
    (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω)) {W' a : Ω → ℝ → ℝ} {A : Set ℂ}
    {φ : ℂ → ℂ} {T : Ω → ℝ} {G : Set Ω} {r : ℝ≥0} (hG : MeasurableSet[𝓕 r] G)
    (hown : ∀ ω ∈ G, OwnData (drive κ B ω) A φ (T ω) (a ω) (W' ω)) {u : ℝ} (hu : u ∈ Icc 0 (r : ℝ))
    (hmem : ∀ ω ∈ G, u ∈ Icc 0 (T ω)) :
    @FrzMeas Ω (𝓕 r) (fun ω => drive κ B ω) W' a A φ T G u := by
  classical
  set W₀ : ℝ≥0 → Ω → ℝ := fun t ω => Real.sqrt κ * B t ω with hW₀
  have hsq : Continuous fun x : ℝ => Real.sqrt κ * x := continuous_const.mul continuous_id
  have hW₀m : ∀ t, Measurable[𝓕 t] (W₀ t) := fun t => hsq.measurable.comp (hBm t)
  have hAd : AdaptedBefore 𝓕 (fun _ => (⊤ : ℝ≥0∞)) W₀ := fun t A hA => by
    have : {ω | ((t : ℝ≥0∞) < ⊤) ∧ W₀ t ω ∈ A} = W₀ t ⁻¹' A := by
      ext ω; simp [ENNReal.coe_lt_top]
    rw [this]; exact hW₀m t hA
  have hGc : ∀ ω ∈ (univ : Set Ω), ContinuousOn (fun t => W₀ t ω) {t | (t : ℝ≥0∞) < ⊤} := fun ω _ =>
    (hsq.comp (hBc ω)).continuousOn
  set s := u.toNNReal with hs
  have hsr : s ≤ r := Real.toNNReal_le_iff_le_coe.2 hu.2
  have hus : ((s : ℝ≥0) : ℝ) = u := Real.coe_toNNReal _ hu.1
  have hrp : ∀ ω, Ito.rpath (fun x => W₀ x ω) = drive κ B ω := fun ω => rfl
  have hal : ∀ z, {ω | ω ∈ G ∧ ∃ v, IsForwardSol (drive κ B ω) z u v} =
      G ∩ Ito.aliveSet W₀ (fun _ => ⊤) univ z s := fun z => by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, Ito.aliveSet, mem_univ, true_and, ENNReal.coe_lt_top, hrp, hus]
  have hdrv : Measurable[𝓕 r] fun ω => drive κ B ω u := by
    have : (fun ω => drive κ B ω u) = W₀ s := by funext ω; rfl
    rw [this]; exact (hW₀m s).mono (𝓕.mono hsr) le_rfl
  have hals : ∀ z ∈ H, MeasurableSet[𝓕 r] {ω | ω ∈ G ∧ ∃ v, IsForwardSol (drive κ B ω) z u v} := fun z hz => by
    rw [hal]
    exact hG.inter (𝓕.mono hsr _ (Ito.measurableSet_aliveSet hAd hGc MeasurableSet.univ hz s))
  have hfwd : ∀ z ∈ H, Measurable[𝓕 r] ({ω | ω ∈ G ∧ ∃ v, IsForwardSol (drive κ B ω) z u v}.indicator
      fun ω => fwdMap (drive κ B ω) u z) := fun z hz => by
    have heq : ({ω | ω ∈ G ∧ ∃ v, IsForwardSol (drive κ B ω) z u v}.indicator fun ω => fwdMap (drive κ B ω) u z) =
        G.indicator fun ω => if ω ∈ Ito.aliveSet W₀ (fun _ => ⊤) univ z s then
          fwdMap (Ito.rpath fun x => W₀ x ω) (s : ℝ) z else 0 := by
      funext ω
      rw [hal]
      by_cases hω : ω ∈ G
      · by_cases ha : ω ∈ Ito.aliveSet W₀ (fun _ => ⊤) univ z s
        · rw [indicator_of_mem (show ω ∈ G ∩ Ito.aliveSet W₀ (fun _ => ⊤) univ z s from ⟨hω, ha⟩),
            indicator_of_mem hω, hrp, hus]
          simp only [ha, ↓reduceIte]
        · rw [indicator_of_notMem (show ω ∉ G ∩ Ito.aliveSet W₀ (fun _ => ⊤) univ z s from fun h => ha h.2),
            indicator_of_mem hω]
          simp only [ha, ↓reduceIte]
      · rw [indicator_of_notMem (fun h => hω h.1), indicator_of_notMem hω]
    rw [heq]
    exact ((Ito.measurable_fwdMap_alive hAd hGc MeasurableSet.univ hz s).mono (𝓕.mono hsr) le_rfl).indicator hG
  exact @FrzMeas.mk Ω (𝓕 r) _ _ _ _ _ _ _ _ hG hown hmem hdrv hals hfwd

/-! ### The hypotheses of the frozen-curve martingale -/

/-- **The hypotheses of the frozen-curve martingale** (§A.1.3): for every path, `OwnData` up to `T ω`, with
`S ω ≤ T ω ≤ Tmax`; the marks `ζ₀`, `ζ_m` of the `φ`-chart alive for the image chain up to `a(T)`, distinct; the (D9)
constants on `[0, T ω]`; a deterministic scale `L`. -/
structure FrzMartHyp {n : ℕ} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (W' a : Ω → ℝ → ℝ) (A : Set ℂ) (φ : ℂ → ℂ)
    (rr : Fin n → ℝ) (ζ₀ : ℝ) (ζ : Fin n → ℝ) (S : Ω → ℝ≥0) (T : Ω → ℝ) (r a₀ γ Γ lam L Tmax : ℝ) : Prop where
  own : ∀ ω, OwnData (drive κ B ω) A φ (T ω) (a ω) (W' ω)
  le : ∀ ω, (S ω : ℝ) ≤ T ω
  leMax : ∀ ω, T ω ≤ Tmax
  alive₀ : ∀ ω, ∃ v, IsForwardSol (W' ω) ζ₀ (a ω (T ω)) v
  alive : ∀ ω m, ∃ v, IsForwardSol (W' ω) (ζ m) (a ω (T ω)) v
  ne : ∀ m, ζ m ≠ ζ₀
  inj : Function.Injective ζ
  d9 : ∀ ω, (frzDataOf κ B W' a φ rr ζ₀ ζ ω).D9Const A (T ω) r a₀ γ Γ lam
  scale : ScaleOK r a₀ γ Γ lam Tmax L

namespace FrzMartHyp

variable {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {rr : Fin n → ℝ}
  {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}
  (hH : FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax)
include hH

/-- The scale conditions hold on every `[0, T ω]` (`T ω ≤ Tmax`). -/
theorem scaleOK (ω : Ω) : ScaleOK r a₀ γ Γ lam (T ω) L := by
  have hr := (hH.d9 ω).r0
  have ha := (hH.d9 ω).a0
  have hrate : 0 ≤ rateBound r a₀ := by unfold rateBound; positivity
  exact { hH.scale with logF := (mul_le_mul_of_nonneg_right (hH.leMax ω) hrate).trans hH.scale.logF }

theorem cutRad_pos (ω : Ω) : 0 < cutRad r a₀ γ :=
  InteractingSLE.ZhanGT4.cutRad_pos (hH.d9 ω).r0 (hH.d9 ω).a0 (hH.d9 ω).g0

/-- The local regularity of `log M̃` on driver pieces. -/
theorem isLogField (ω : Ω) {b c y : ℝ} (hb : 0 ≤ b) (hcS : c ≤ S ω)
    (hWy : ∀ t ∈ Icc b c, |Real.sqrt κ * B t.toNNReal ω - y| < cutRad r a₀ γ) :
    IsLogField (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX
      (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXX (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXXX
      (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ellT b c y (cutRad r a₀ γ) (2 * coefTot κ rr * scaleBound L) :=
  (frzDataOf κ B W' a φ rr ζ₀ ζ ω).isLogField_of_D9 (hH.own ω) (hH.alive₀ ω).choose_spec
    (v := fun m => (hH.alive ω m).choose) (fun m => (hH.alive ω m).choose_spec) hH.ne hH.inj
    (fun _ hx => ⟨hb.trans hx.1, hx.2.trans (hcS.trans (hH.le ω))⟩) (hH.d9 ω) (hH.scaleOK ω) hWy

/-- The generator identity of `log M̃` along the driver. -/
theorem gen (hκ : 0 < κ) (ω : Ω) {u : ℝ} (hu0 : 0 ≤ u) (huS : u ≤ S ω) :
    (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ellT u (Real.sqrt κ * B u.toNNReal ω) +
      Real.sqrt κ ^ 2 / 2 * ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXX u (Real.sqrt κ * B u.toNNReal ω) +
        (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX u (Real.sqrt κ * B u.toNNReal ω) ^ 2) = 0 := by
  set d := frzDataOf κ B W' a φ rr ζ₀ ζ ω
  have hρ := hH.cutRad_pos ω
  have hx : |d.W u - d.W u| < cutRad r a₀ γ := by rw [sub_self, abs_zero]; exact hρ
  have h := d.cutField_gen_eq_zero_of_D9 (hH.own ω) (hH.alive₀ ω).choose_spec
    (v := fun m => (hH.alive ω m).choose) (fun m => (hH.alive ω m).choose_spec) hH.ne hH.inj
    (b := u) (c := u) (y := d.W u) (fun _ hx => ⟨hu0.trans hx.1, hx.2.trans (huS.trans (hH.le ω))⟩) hκ.ne'
    (hH.d9 ω) (hH.scaleOK ω) (fun t ht => by rw [show t = u from le_antisymm ht.2 ht.1]; exact hx)
    (t := u) ⟨le_rfl, le_rfl⟩
  have e0 := cutChi_zero_eq_one hρ hx
  have e1 := cutChi_succ_eq_zero hρ hx (k := 1) one_pos
  have e2 := cutChi_succ_eq_zero hρ hx (k := 2) two_pos
  simp only [cutFieldT, cutField2, cutExp2, e0, e1, e2] at h
  rw [Real.sq_sqrt hκ.le]
  have hk : d.κ = κ := rfl
  rw [hk] at h
  have : Real.exp (d.ell u (d.W u)) * (d.ellT u (d.W u) + κ / 2 * (d.LSXX u (d.W u) + d.LSX u (d.W u) ^ 2)) = 0 := by
    linear_combination h
  exact (mul_eq_zero.1 this).resolve_left (Real.exp_pos _).ne'

variable {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The frozen factors at a time `rT` are `𝓕_rT`-measurable on `{rT ≤ S}`.** -/
theorem measurable_parts (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (rT : ℝ≥0) :
    (∀ k, Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ k rT)) ∧
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω => frzImg (W' ω) (a ω) ζ₀ rT) ∧
    (∀ m, Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω => frzImg (W' ω) (a ω) (ζ m) rT)) ∧
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω => frzImgD (W' ω) (a ω) ζ₀ rT) ∧
    (∀ m, Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω => frzImgD (W' ω) (a ω) (ζ m) rT)) ∧
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω => frzLogF (drive κ B ω) (W' ω) (a ω) φ rT) := by
  have hG : MeasurableSet[𝓕 rT] {ω | rT ≤ S ω} := measurableSet_ge_of_isStoppingTime hS rT
  have hFM : ∀ u ∈ Icc (0 : ℝ) rT, @FrzMeas Ω (𝓕 rT) (fun ω => drive κ B ω) W' a A φ T {ω | rT ≤ S ω} u :=
    fun u hu => frzMeas_of_adapted hBm hBc hG (fun ω _ => hH.own ω) hu fun ω hω =>
      ⟨hu.1, hu.2.trans ((NNReal.coe_le_coe.2 hω).trans (hH.le ω))⟩
  have hM := hFM rT ⟨rT.coe_nonneg, le_rfl⟩
  exact ⟨fun k => @FrzMeas.measurable_frzA Ω (𝓕 rT) _ _ _ _ _ _ _ _ hM k,
    @FrzMeas.measurable_frzImg Ω (𝓕 rT) _ _ _ _ _ _ _ _ hM ζ₀ fun ω _ => hH.alive₀ ω,
    fun m => @FrzMeas.measurable_frzImg Ω (𝓕 rT) _ _ _ _ _ _ _ _ hM (ζ m) fun ω _ => hH.alive ω m,
    @FrzMeas.measurable_frzImgD Ω (𝓕 rT) _ _ _ _ _ _ _ _ hM ζ₀ fun ω _ => hH.alive₀ ω,
    fun m => @FrzMeas.measurable_frzImgD Ω (𝓕 rT) _ _ _ _ _ _ _ _ hM (ζ m) fun ω _ => hH.alive ω m,
    @measurable_frzLogF Ω (𝓕 rT) _ _ _ _ _ _ _ _ rT.coe_nonneg hFM⟩

omit hH in
/-- The point `√κ B_r` is the driver of the frozen data at time `r`. -/
theorem frzDataOf_W (ω : Ω) (rT : ℝ≥0) :
    (frzDataOf κ B W' a φ rr ζ₀ ζ ω).W rT = Real.sqrt κ * B rT ω := by
  simp [frzDataOf, drive]

/-- `log M̃` along the driver is adapted on `{r ≤ S}`. -/
theorem measurable_ell (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (rT : ℝ≥0) :
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω =>
      (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell rT (Real.sqrt κ * B rT ω)) := by
  obtain ⟨hA, hI0, hIm, hD0, hDm, hF⟩ := hH.measurable_parts hBm hBc hS rT
  have hG : MeasurableSet[𝓕 rT] {ω | rT ≤ S ω} := measurableSet_ge_of_isStoppingTime hS rT
  set G := {ω | rT ≤ S ω} with hGdef
  have hA0 := hA 0
  have hA1 := hA 1
  set f0 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 0 rT with hf0
  set f1 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 1 rT with hf1
  set i0 := G.indicator fun ω => frzImg (W' ω) (a ω) ζ₀ rT with hi0
  set im := fun m => G.indicator fun ω => frzImg (W' ω) (a ω) (ζ m) rT with him
  set d0 := G.indicator fun ω => frzImgD (W' ω) (a ω) ζ₀ rT with hd0
  set dm := fun m => G.indicator fun ω => frzImgD (W' ω) (a ω) (ζ m) rT with hdm
  set lf := G.indicator fun ω => frzLogF (drive κ B ω) (W' ω) (a ω) φ rT with hlf
  have hmeas : Measurable[𝓕 rT] fun ω => dualLogTime κ rr (d0 ω) (lf ω) (i0 ω) (fun m => im m ω)
      (fun m => dm m ω) + dualLogSpace κ rr (f0 ω) (f1 ω) (i0 ω) (fun m => im m ω) := by
    unfold dualLogTime dualLogSpace pairSum; fun_prop
  convert hmeas.indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · rw [indicator_of_mem hω, indicator_of_mem hω]
    simp only [hf0, hf1, hi0, him, hd0, hdm, hlf, indicator_of_mem hω]
    rw [← frzDataOf_W (W' := W') (a := a) (φ := φ) (rr := rr) (ζ₀ := ζ₀) (ζ := ζ)]
    rfl
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]

/-- `∂_x log M̃` along the driver is adapted on `{r ≤ S}`. -/
theorem measurable_LSX (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (rT : ℝ≥0) :
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω =>
      (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX rT (Real.sqrt κ * B rT ω)) := by
  obtain ⟨hA, hI0, hIm, -, -, -⟩ := hH.measurable_parts hBm hBc hS rT
  have hG : MeasurableSet[𝓕 rT] {ω | rT ≤ S ω} := measurableSet_ge_of_isStoppingTime hS rT
  set G := {ω | rT ≤ S ω} with hGdef
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  set f0 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 0 rT with hf0
  set f1 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 1 rT with hf1
  set f2 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 2 rT with hf2
  set i0 := G.indicator fun ω => frzImg (W' ω) (a ω) ζ₀ rT with hi0
  set im := fun m => G.indicator fun ω => frzImg (W' ω) (a ω) (ζ m) rT with him
  have hmeas : Measurable[𝓕 rT] fun ω => dualLogSpaceX κ rr (f0 ω) (f1 ω) (f2 ω) (i0 ω) (fun m => im m ω) := by
    unfold dualLogSpaceX; fun_prop
  convert hmeas.indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · rw [indicator_of_mem hω, indicator_of_mem hω]
    simp only [hf0, hf1, hf2, hi0, him, indicator_of_mem hω]
    rw [← frzDataOf_W (W' := W') (a := a) (φ := φ) (rr := rr) (ζ₀ := ζ₀) (ζ := ζ)]
    rfl
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]

/-- `∂²_x log M̃` along the driver is adapted on `{r ≤ S}`. -/
theorem measurable_LSXX (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (rT : ℝ≥0) :
    Measurable[𝓕 rT] ({ω | rT ≤ S ω}.indicator fun ω =>
      (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXX rT (Real.sqrt κ * B rT ω)) := by
  obtain ⟨hA, hI0, hIm, -, -, -⟩ := hH.measurable_parts hBm hBc hS rT
  have hG : MeasurableSet[𝓕 rT] {ω | rT ≤ S ω} := measurableSet_ge_of_isStoppingTime hS rT
  set G := {ω | rT ≤ S ω} with hGdef
  have hA0 := hA 0
  have hA1 := hA 1
  have hA2 := hA 2
  have hA3 := hA 3
  set f0 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 0 rT with hf0
  set f1 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 1 rT with hf1
  set f2 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 2 rT with hf2
  set f3 := G.indicator fun ω => frzA (drive κ B ω) (W' ω) (a ω) φ 3 rT with hf3
  set i0 := G.indicator fun ω => frzImg (W' ω) (a ω) ζ₀ rT with hi0
  set im := fun m => G.indicator fun ω => frzImg (W' ω) (a ω) (ζ m) rT with him
  have hmeas : Measurable[𝓕 rT] fun ω =>
      dualLogSpaceXX κ rr (f0 ω) (f1 ω) (f2 ω) (f3 ω) (i0 ω) (fun m => im m ω) := by
    unfold dualLogSpaceXX; fun_prop
  convert hmeas.indicator hG using 1
  funext ω
  by_cases hω : ω ∈ G
  · rw [indicator_of_mem hω, indicator_of_mem hω]
    simp only [hf0, hf1, hf2, hf3, hi0, him, indicator_of_mem hω]
    rw [← frzDataOf_W (W' := W') (a := a) (φ := φ) (rr := rr) (ζ₀ := ζ₀) (ζ := ζ)]
    rfl
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]

end FrzMartHyp

/-! ### `log M̃` is a log-field along the driver; the martingale -/

section Mart

variable {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ} {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {W' a : Ω → ℝ → ℝ} {A : Set ℂ}
  {φ : ℂ → ℂ} {rr : Fin n → ℝ} {ζ₀ : ℝ} {ζ : Fin n → ℝ} {S : Ω → ℝ≥0} {T : Ω → ℝ} {r a₀ γ Γ lam L Tmax : ℝ}

/-- **`log M̃` is a log-field along the driver `√κ B` up to `S`.** -/
theorem isDriverLogField_frozen (hκ : 0 < κ) (hBm : ∀ u, Measurable[𝓕 u] (B u)) (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hH : FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax) :
    IsDriverLogField 𝓕 (Real.sqrt κ) (cutRad r a₀ γ) (2 * coefTot κ rr * scaleBound L) B S
      (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell) (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSX)
      (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXX) (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).LSXXX)
      (fun ω => (frzDataOf κ B W' a φ rr ζ₀ ζ ω).ellT) :=
  ⟨fun ω _ _ _ hb _ hcS hWy => hH.isLogField ω hb hcS hWy, fun ω _ hu0 huS => hH.gen hκ ω hu0 huS,
    hH.measurable_ell hBm hBc hS, hH.measurable_LSX hBm hBc hS, hH.measurable_LSXX hBm hBc hS⟩

/-- **The stopped martingale of `M̃` for ordinary `SLE_κ` with the other curve frozen** (§A.1.2–A.1.3): with
`M̃_r = exp ℓ(r, W_r)`, `ℓ = log M̃` of the frozen data (A7's `FrzData.ell`), and `S` the stopping time up to which
the (D9) hypotheses hold, `E[ξ (M̃_{t∧S} − M̃_{s∧S})] = 0` for every bounded `𝓕_s`-measurable `ξ`. -/
theorem integral_mul_MTilde_stopped_sub_eq_zero {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hH : FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax) {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (Real.exp ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell ((min t (S ω) : ℝ≥0) : ℝ)
        ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).W ((min t (S ω) : ℝ≥0) : ℝ))) -
      Real.exp ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell ((min s (S ω) : ℝ≥0) : ℝ)
        ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).W ((min s (S ω) : ℝ≥0) : ℝ)))) ∂P = 0 := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have h := (isDriverLogField_frozen hκ hBm hBc hS hH).integral_mul_logField_stopped_sub_eq_zero hB hBc
    (Real.sqrt_nonneg κ) (hH.cutRad_pos ω₀) hS hst hξ hξb
  have hW : ∀ ω (τ : ℝ≥0), (frzDataOf κ B W' a φ rr ζ₀ ζ ω).W τ = Real.sqrt κ * B τ ω :=
    FrzMartHyp.frzDataOf_W
  simp only [logFieldExp] at h
  simp only [hW]
  exact h

/-- **`M̃_{·∧S}` is a martingale** (Mathlib form) for ordinary `SLE_κ` with the other curve frozen (§A.1.2–A.1.3). -/
theorem martingale_MTilde_stopped {P : Measure Ω} (hκ : 0 < κ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hH : FrzMartHyp κ B W' a A φ rr ζ₀ ζ S T r a₀ γ Γ lam L Tmax) :
    Martingale (fun t ω => Real.exp ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).ell ((min t (S ω) : ℝ≥0) : ℝ)
      ((frzDataOf κ B W' a φ rr ζ₀ ζ ω).W ((min t (S ω) : ℝ≥0) : ℝ)))) 𝓕 P := by
  have hBm : ∀ u, Measurable[𝓕 u] (B u) := fun u => hB.2.1 u
  have hP := hB.isProbabilityMeasure'
  obtain ⟨ω₀⟩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hP.measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
    exact zero_ne_one this
  have h := (isDriverLogField_frozen hκ hBm hBc hS hH).martingale_logFieldExp_stopped hB hBc
    (Real.sqrt_nonneg κ) (hH.cutRad_pos ω₀) hS
  have hW : ∀ ω (τ : ℝ≥0), (frzDataOf κ B W' a φ rr ζ₀ ζ ω).W τ = Real.sqrt κ * B τ ω :=
    FrzMartHyp.frzDataOf_W
  simp only [hW]
  exact h

end Mart

end InteractingSLE.ZhanGT4
