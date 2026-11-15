/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MixtureA33ChordalDriver
import InteractingSLE.Spec.ZhanGT4.MixtureA32Strip
import InteractingSLE.Spec.Zhan.UpperPoint

/-!
# (G3) in chordal coordinates: the forced strip law is chordal `SLE_κ(κ − 4, −4)`

Packet PROVE-ZHAN-A33. Astra, *Follow-up proofs* §A.3.2 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L686–L705): "Mapping back gives the original killed chordal law as a mixture of `SLE_κ(−4, κ − 4)` from `(0; y, x)`,
`y = Ψ⁻¹(u + iπ)`". In the chart of ruling R36 (`x = −1`, `Ψ(z) = log(1 + z)`), the upper strip point `u + iπ` is the
chordal point `y = −1 − e^u`. For the chordal integrated evolution with left marks `(−1, −1 − e^u)` and weights
`(κ − 4, −4)` (no right marks; target charge `κ − 6 − (κ − 8) = 2`), whose strip clock is unbounded on the strip life:

* **`exists_stripDriver_eq_forcedDrv`**: there is a Brownian motion `B̃` (continuous paths, `B̃₀ = 0`) such that almost
  surely the strip driver `ξ_t` is, at every strip time, PROVE-ZHAN-A32's forced driver `forcedDrv κ σ u B̃`,
  `σ = 3 − κ/2` (strip SLE with charge `−4` at `u + iπ`, `2` at the right end, `κ − 4` at the left end);
* **`map_stripDriver_eq_forcedLaw`**: the law of the strip driver path is the forced law
  `Law(forcedPath κ σ u (β))` of any Brownian motion `β` (the component of A32's mixture `mixLaw`).

## Proof

`exists_upStripBrownian` gives `ξ = √κ B̃ + 2(p − u) − σ t` with `p` the strip coordinate of the upper mark, and
(3.15) (`Strip.IsSepMark.stripPoint_eq_add_integral_of_gt`) gives `p_t = u + ∫₀ᵗ tanh((p − ξ)/2)`. Hence `Y = p − ξ`
solves `Y = u − √κ B̃ + σ t − ∫₀ᵗ tanh(Y/2)`, the equation of the forced upper point `forcedY`; the solution is unique
(`OneForce.eqOn_lipSol`), so `ξ = √κ B̃ − σ t + 2∫ tanh(Y/2) = forcedDrv`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan Mix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The chordal weights of A.3.2's component law: `κ − 4` at the end mark `−1`, `−4` at the upper mark. -/
def a33RhoL (κ : ℝ) : Fin 2 → ℝ := ![κ - 4, -4]

/-- **The strip coordinate of the upper mark starts at `u`.** -/
theorem stripPoint_zero_of_isSepMark {w v y : ℝ → ℝ} {S : ℝ} (h : Strip.IsSepMark w v S) :
    Strip.stripPoint w v y 0 = Real.log |y 0 - v 0| := by
  have hc0 : Strip.stripClock w v 0 = 0 := by simp [Strip.stripClock]
  have h0 := h.chordalTime_stripClock (s := 0) ⟨le_rfl, h.nonneg⟩
  rw [hc0] at h0
  simp only [Strip.stripPoint, h0, zero_add]

/-- **Pathwise identification.** For one path of the evolution: if the strip clock is unbounded on the strip life and
the strip driver satisfies the upper-mark driving equation with a continuous `β`, then it is the forced driver of `β`
at every strip time. -/
theorem stripDriver_eq_forcedDrv_path {κ u : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 2 → ℝ≥0 → ℝ}
    {vR : Fin 0 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath κ (upWordXL ![u]) ![] (a33RhoL κ) ![] w vL vR b ζ)
    (hcl : HasUnboundedStripClock w (vL 0) ζ) {β : ℝ≥0 → Ω → ℝ} {ω : Ω} (hβ : Continuous (β · ω))
    (hdrv : ∀ t : ℝ≥0, Strip.stripDriver (Strip.extPath w) (Strip.extPath (vL 0)) t =
      Real.sqrt κ * β t ω + 2 * (Strip.stripPoint (Strip.extPath w) (Strip.extPath (vL 0))
        (Strip.extPath (vL 1)) t - u) - (3 - κ / 2) * t) (t₀ : ℝ≥0) :
    Strip.stripDriver (Strip.extPath w) (Strip.extPath (vL 0)) t₀ =
      forcedDrv κ (3 - κ / 2) (fun _ => u) β t₀ ω := by
  set σ : ℝ := 3 - κ / 2 with hσ
  set ξ : ℝ → ℝ := Strip.stripDriver (Strip.extPath w) (Strip.extPath (vL 0)) with hξ
  set p : ℝ → ℝ := Strip.stripPoint (Strip.extPath w) (Strip.extPath (vL 0)) (Strip.extPath (vL 1)) with hpdef
  -- a strip-life time beyond `t₀`
  obtain ⟨S, hS, hTS⟩ := hcl ((t₀ : ℝ) + 1)
  have hsep := isSepMark_of_up hp (upWordXL_zero ![u]) hS
  have hF := hp.isForcePath
  have hT0 : (0 : ℝ) ≤ t₀ := t₀.coe_nonneg
  have hTS' : (t₀ : ℝ) ≤ Strip.stripClock (Strip.extPath w) (Strip.extPath (vL 0)) S := by linarith
  -- the upper mark as a real path on `[0, S]`
  have hsubS : ∀ s ∈ Icc (0 : ℝ) S, (s.toNNReal : ℝ≥0∞) < ζ := fun s hs => Sec2.toNNReal_lt_of_mem_Icc hS.1 hs
  have hy : ContinuousOn (Strip.extPath (vL 1)) (Icc 0 (S : ℝ)) := Strip.continuousOn_extPath (hF.continuousOn_vL 1) hS.1
  have hint : IntervalIntegrable (fun s => 2 / (Strip.extPath (vL 1) s - Strip.extPath w s)) volume 0 S :=
    hF.intervalIntegrable_forceL hS.1 1
  have hy0 : Strip.extPath (vL 1) 0 = -1 - Real.exp u := by
    simp only [Strip.extPath, Real.toNNReal_zero, hF.vL_zero]
    simp [upWordXL]
  have heq : ∀ s ∈ Icc (0 : ℝ) S, Strip.extPath (vL 1) s =
      Strip.extPath (vL 1) 0 + ∫ r in (0 : ℝ)..s, 2 / (Strip.extPath (vL 1) r - Strip.extPath w r) := by
    intro s hs
    have h := hF.vL_eq (hsubS s hs) 1
    rw [Real.coe_toNNReal _ hs.1] at h
    rw [hy0]
    simp only [Strip.extPath]
    rw [h]
    simp [upWordXL]
  have hyv : ∀ s ∈ Icc (0 : ℝ) S, Strip.extPath (vL 1) s < Strip.extPath (vL 0) s := fun s hs =>
    vL_succ_lt_vL_zero hp (hS.mono (Sec2.toNNReal_le_of_mem_Icc hs)) (upWordXL_succ_lt ![u]) 0
  -- (3.15) for the upper mark
  have hp0 : p 0 = u := by
    rw [hpdef, stripPoint_zero_of_isSepMark hsep, hy0]
    simp only [Strip.extPath, Real.toNNReal_zero, hF.vL_zero, upWordXL_zero]
    rw [show -1 - Real.exp u - -1 = -Real.exp u by ring, abs_neg, abs_of_pos (Real.exp_pos u), Real.log_exp]
  have hpint : ∀ s ∈ Icc (0 : ℝ) t₀, p s = u + ∫ r in (0 : ℝ)..s, Real.tanh ((p r - ξ r) / 2) := by
    intro s hs
    rw [← hp0]
    exact hsep.stripPoint_eq_add_integral_of_gt hy hint heq hyv ⟨hs.1, hs.2.trans hTS'⟩
  -- the gap `Y = p − ξ` solves the forced equation
  set Y : ℝ → ℝ := fun s => p s - ξ s with hYdef
  have hpc : ContinuousOn p (Icc 0 (t₀ : ℝ)) :=
    (hsep.continuousOn_stripPoint hy fun s hs => (hyv s hs).ne).mono (Icc_subset_Icc le_rfl hTS')
  have hξc : ContinuousOn ξ (Icc 0 (t₀ : ℝ)) := hsep.continuousOn_stripDriver.mono (Icc_subset_Icc le_rfl hTS')
  have hYc : ContinuousOn Y (Icc 0 (t₀ : ℝ)) := hpc.sub hξc
  set wf : ℝ → ℝ := fun s => -(Real.sqrt κ * β s.toNNReal ω) + σ * s with hwf
  have hwfc : Continuous wf :=
    ((continuous_const.mul (hβ.comp continuous_real_toNNReal)).neg).add (continuous_const.mul continuous_id)
  have hLD : OneForce.LipData (fun z => -Real.tanh (z / 2)) wf :=
    ⟨⟨_, lipschitzWith_neg_tanh_half⟩, ⟨1, fun x => by rw [abs_neg]; exact (Real.abs_tanh_lt_one _).le⟩, hwfc⟩
  have hdrv' : ∀ s ∈ Icc (0 : ℝ) t₀, ξ s = Real.sqrt κ * β s.toNNReal ω + 2 * (p s - u) - σ * s := by
    intro s hs
    have h := hdrv s.toNNReal
    rw [Real.coe_toNNReal _ hs.1] at h
    exact h
  have hYeq : ∀ s ∈ Icc (0 : ℝ) t₀, Y s = u + wf s + ∫ r in (0 : ℝ)..s, -Real.tanh (Y r / 2) := by
    intro s hs
    have h1 := hpint s hs
    have h2 := hdrv' s hs
    simp only [hYdef, hwf, intervalIntegral.integral_neg]
    rw [h2]
    have : p s - u = ∫ r in (0 : ℝ)..s, Real.tanh ((p r - ξ r) / 2) := by linarith
    linarith
  -- the forced upper point solves it too
  set Z : ℝ → ℝ := fun s => forcedY κ σ (fun _ => u) β s.toNNReal ω with hZ
  have hZc : Continuous Z :=
    (continuous_forcedY (κ := κ) (σ := σ) (U := fun _ => u) hβ).comp continuous_real_toNNReal
  have hZeq : ∀ s ∈ Icc (0 : ℝ) t₀, Z s = u + wf s + ∫ r in (0 : ℝ)..s, -Real.tanh (Z r / 2) := by
    intro s hs
    simp only [hZ, hwf]
    rw [forcedY_eq hβ s.toNNReal, Real.coe_toNNReal _ hs.1]
    ring
  have e1 := OneForce.eqOn_lipSol hLD hT0 hYc hYeq
  have e2 := OneForce.eqOn_lipSol hLD hT0 hZc.continuousOn hZeq
  have hYZ : ∀ s ∈ Icc (0 : ℝ) t₀, Y s = Z s := fun s hs => by rw [← e1 hs, e2 hs]
  -- conclude
  have hpt := hpint t₀ ⟨hT0, le_rfl⟩
  rw [forcedDrv_eq hβ t₀]
  have hξt := hdrv t₀
  rw [hξt]
  have hint_eq : ∫ r in (0 : ℝ)..t₀, Real.tanh ((p r - ξ r) / 2) =
      ∫ r in (0 : ℝ)..t₀, Real.tanh (forcedY κ σ (fun _ => u) β r.toNNReal ω / 2) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hT0] at hr
    have := hYZ r hr
    simp only [hYdef, hZ] at this
    simp only [this]
  have : p t₀ - u = ∫ r in (0 : ℝ)..t₀, Real.tanh ((p r - ξ r) / 2) := by linarith
  rw [this, hint_eq]
  ring

/-- **(G3), chordal form, pathwise**: for the chordal integrated `SLE_κ(κ − 4, −4)` evolution from `(0; −1, −1 − e^u)`
whose strip clock is almost surely unbounded on the strip life, there is a Brownian motion `B̃` (every path continuous,
`B̃₀ = 0`) such that almost surely the strip driver is PROVE-ZHAN-A32's forced driver `forcedDrv κ σ u B̃`,
`σ = 3 − κ/2`, at every strip time. -/
theorem exists_stripDriver_eq_forcedDrv {κ u : ℝ} (hκ : 0 < κ) {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ (upWordXL ![u]) ![] (a33RhoL κ) ![] P 𝓕 W VL VR B ζ)
    (hclock : ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL 0 · ω) (ζ ω)) :
    ∃ (𝓗 : Filtration ℝ≥0 mΩ) (B' : ℝ≥0 → Ω → ℝ), IsFilteredBrownianReal 𝓗 B' P ∧
      (∀ ω, Continuous (B' · ω)) ∧ (∀ ω, B' 0 ω = 0) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) t =
        forcedDrv κ (3 - κ / 2) (fun _ => u) B' t ω := by
  obtain ⟨𝓗, B', hB', hB'c, hB'0, hae⟩ :=
    exists_upStripBrownian (nL := 1) (nR := 0) hκ (q := ![u]) (xR := ![]) (fun j => j.elim0) hE hclock
  refine ⟨𝓗, B', hB', hB'c, hB'0, ?_⟩
  filter_upwards [hae, hE.2.2.2.2, show ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL 0 · ω) (ζ ω) from hclock]
    with ω hω hp hcl t
  refine stripDriver_eq_forcedDrv_path (vL := fun i t => VL i t ω) (w := (W · ω)) hp hcl (hB'c ω)
    (fun t => ?_) t
  rw [(hω t).2]
  simp only [Fin.sum_univ_one, Finset.univ_eq_empty, Finset.sum_empty, a33RhoL, Fin.succ_zero_eq_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- **(G3), chordal form, in law**: for the chordal integrated `SLE_κ(κ − 4, −4)` evolution from `(0; −1, −1 − e^u)`
with an almost surely unbounded strip clock, the law of the strip driver path `t ↦ ξ_t` is the forced law
`Law(forcedPath κ σ u β)`, `σ = 3 − κ/2`, of any Brownian motion `β` — the `u`-component of PROVE-ZHAN-A32's mixture
`mixLaw` (`mixLaw_eq_map_prod`). -/
theorem map_stripDriver_eq_forcedLaw {κ u : ℝ} (hκ : 0 < κ) {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ (upWordXL ![u]) ![] (a33RhoL κ) ![] P 𝓕 W VL VR B ζ)
    (hclock : ∀ᵐ ω ∂P, HasUnboundedStripClock (W · ω) (VL 0 · ω) (ζ ω))
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Q : Measure Ω'} {β : ℝ≥0 → Ω' → ℝ} (hβ : IsPreBrownianReal β Q)
    (hβm : ∀ t, Measurable (β t)) :
    P.map (fun ω (t : ℝ≥0) => Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) t) =
      Q.map fun ω' => forcedPath κ (3 - κ / 2) u (pathOf β ω') := by
  obtain ⟨𝓗, B', hB', -, -, hae⟩ := exists_stripDriver_eq_forcedDrv hκ hE hclock
  have hB'm : ∀ t, Measurable (B' t) := fun t => (hB'.2.1 t).mono (𝓗.le t) le_rfl
  have hpath : (fun ω (t : ℝ≥0) => Strip.stripDriver (Strip.extPath (W · ω)) (Strip.extPath (VL 0 · ω)) t)
      =ᵐ[P] fun ω => forcedPath κ (3 - κ / 2) u (pathOf B' ω) := by
    filter_upwards [hae] with ω hω
    rw [forcedPath_eq]
    funext t
    exact hω t
  rw [Measure.map_congr hpath]
  have h1 : (fun ω => forcedPath κ (3 - κ / 2) u (pathOf B' ω)) = forcedPath κ (3 - κ / 2) u ∘ pathOf B' := rfl
  have h2 : (fun ω' => forcedPath κ (3 - κ / 2) u (pathOf β ω')) = forcedPath κ (3 - κ / 2) u ∘ pathOf β := rfl
  rw [h1, h2, ← Measure.map_map (measurable_forcedPath u) (measurable_pathOf hB'm),
    ← Measure.map_map (measurable_forcedPath u) (measurable_pathOf hβm),
    map_pathOf_eq_of_isPreBrownianReal hB'.1.toIsPreBrownianReal hβ hB'm hβm]

end InteractingSLE.ZhanGT4.UpMark
