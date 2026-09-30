import QuantumZipper.Proofs.RS.Generation
import QuantumZipper.Proofs.RS.HullBasics
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.RS.TraceShift

/-!
# EXT-RS node TIP, deterministic core

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **TIP** (task RS-TIP-SIM). Deterministic
statements behind "the tip never returns to `0`":

* `RadialGood W`: `W` continuous, `W 0 = 0`, `η = trace W` starts at `0`, is continuous on
  `[0,∞)`, and `‖f̂_t(iy) − η t‖ ≤ C_N y^δ` on `[0,N] × (0,1]` (the conclusion of TR4).
* `tendstoUniformlyOn_trace`: the uniform radial convergence required by `gen_no_path`.
* `trace_eq_zero_of_shift`: if `η s = 0`, `u ∈ (0,s)`, the shifted trace `ηᵘ` has radial
  limits and no real values except `0` (NR), and `f̂_u(w) → η u` as `w → 0` in `ℍ` (boundary
  continuity at `0`), then `η u = 0`.
* `trace_ne_zero_of_dense`: if this holds for a dense set of `u`, then `η s ≠ 0` for `s > 0`:
  otherwise `η ≡ 0` on `[0,s]`, and `gen_no_path` forbids a segment in `ℍ` from a point of
  `K_s ≠ ∅` (D6) to a point of `ℍ \ K_s`.

Sources: Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 6.1 and its
proof (p. 23: "if `γ(t) = 0` for some `t > 0` ... `g_s` extends continuously ..."); Kemppainen,
*Schramm–Loewner Evolution* (2017), p. 80 (5.5). RS derive the boundary continuity at `0` from
Thm 4.1 (continuous extension of `g_s⁻¹`); here it is an explicit hypothesis, discharged by the
fixed-time Hölder estimate RS Thm 5.2 for `κ < 4` (`TipA.lean`, blueprint TIP-a) and by
Carathéodory's theorem for `κ = 4` (TIP-b). The final step uses GEN (`gen_no_path`) in place of
RS's "the hull at time `s` would be empty".
-/

noncomputable section

open Set Filter Topology Metric Complex

namespace QuantumZipper
namespace RS

variable {W : ℝ → ℝ}

/-- The conclusion of TR4 for a fixed driver. -/
def RadialGood (W : ℝ → ℝ) : Prop :=
  Continuous W ∧ W 0 = 0 ∧ trace W 0 = 0 ∧ ContinuousOn (trace W) (Ici 0) ∧
    ∃ δ > (0 : ℝ), ∀ N : ℕ, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) N, ∀ y ∈ Ioc (0 : ℝ) 1,
      ‖fwdMapInv W t (y * I) - trace W t‖ ≤ C * y ^ δ

/-- No real values of the trace at positive times, except `0` (the conclusion of NR). -/
def NoRealHitDet (W : ℝ → ℝ) : Prop :=
  ∀ t > (0 : ℝ), (trace W t).im = 0 → trace W t = 0

theorem RadialGood.tendsto (hW : RadialGood W) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun y : ℝ => fwdMapInv W t (y * I)) (𝓝[>] (0 : ℝ)) (𝓝 (trace W t)) := by
  obtain ⟨-, -, -, -, δ, hδ, h⟩ := hW
  obtain ⟨C, hC⟩ := h ⌈t⌉₊
  exact tendsto_fwdMapInv_of_rpow_bound hδ fun y hy => hC t ⟨ht, Nat.le_ceil t⟩ y hy

/-- TR4 gives the uniform radial convergence on `[0,t]` used by GEN. -/
theorem tendstoUniformlyOn_trace (hW : RadialGood W) (t : ℝ) :
    TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) (trace W)
      (𝓝[>] 0) (Icc 0 t) := by
  obtain ⟨-, -, -, -, δ, hδ, h⟩ := hW
  obtain ⟨C, hC⟩ := h ⌈t⌉₊
  have hlim : Tendsto (fun y : ℝ => C * y ^ δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun y : ℝ => y ^ δ) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ δ)) :=
      (Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto
    rw [Real.zero_rpow hδ.ne'] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε), Ioc_mem_nhdsGT (zero_lt_one' ℝ)]
    with y hy hy1 s hs
  rw [dist_comm, dist_eq_norm]
  exact (hC s ⟨hs.1, hs.2.trans (Nat.le_ceil t)⟩ y hy1).trans_lt hy

/-- **Key step.** If `η s = 0` and `u ∈ (0,s)` is a good time (the shifted trace `ηᵘ` has radial
limits and no nonzero real values, and `f̂_u` is continuous at `0` from `ℍ` with value `η u`),
then `η u = 0`. RS Thm 6.1 proof (p. 23). -/
theorem trace_eq_zero_of_shift (hW : RadialGood W) {u s : ℝ} (hu : 0 < u) (hus : u < s)
    (hV : RadialGood (shiftDrive W u)) (hVnr : NoRealHitDet (shiftDrive W u))
    (hbd : Tendsto (fwdMapInv W u) (𝓝[H] 0) (𝓝 (trace W u))) (hs : trace W s = 0) :
    trace W u = 0 := by
  obtain ⟨hWc, hW0, -⟩ := hW
  have hsu : 0 < s - u := sub_pos.2 hus
  have hVc := continuous_shiftDrive hWc u
  have hV0 : shiftDrive W u 0 = 0 := shiftDrive_zero W u
  set p := trace (shiftDrive W u) (s - u) with hpdef
  have hp := hV.tendsto hsu.le
  have hmemH : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), fwdMapInv (shiftDrive W u) (s - u) ((y : ℂ) * I) ∈ H :=
    eventually_mem_nhdsWithin.mono fun y hy => fwdMapInv_mem_H hVc hV0 hsu.le (mul_I_mem_H hy)
  have hpim : 0 ≤ p.im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto p).comp hp)
      (hmemH.mono fun y hy => le_of_lt hy)
  have hsum : u + (s - u) = s := by ring
  rcases hpim.lt_or_eq with hpos | hzero
  · exfalso
    have h3 := (trace_add_of_tendsto_shift hWc hW0 hu.le hsu.le hpos hp).2.2
    rw [hsum, hs] at h3
    have := fwdMapInv_mem_H hWc hW0 hu.le hpos
    rw [← h3] at this
    exact lt_irrefl _ (show (0 : ℂ).im > 0 from this)
  · have hp0 : p = 0 := hVnr _ hsu hzero.symm
    have hg : Tendsto (fun y : ℝ => fwdMapInv (shiftDrive W u) (s - u) (y * I)) (𝓝[>] (0 : ℝ))
        (𝓝[H] 0) := tendsto_nhdsWithin_iff.2 ⟨hp0 ▸ hp, hmemH⟩
    have h1 := hbd.comp hg
    have h2 : Tendsto (fun y : ℝ => fwdMapInv W s (y * I)) (𝓝[>] (0 : ℝ)) (𝓝 (trace W u)) := by
      refine h1.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
      show fwdMapInv W u (fwdMapInv (shiftDrive W u) (s - u) (y * I)) = _
      rw [← fwdMapInv_add_shift hWc hW0 hu.le hsu.le (mul_I_mem_H hy), hsum]
    rw [← hs]
    unfold trace
    exact h2.limUnder_eq.symm

/-- If a trace vanishes on `[0,s]` with `s > 0`, GEN is violated. -/
theorem false_of_trace_eqOn_zero (hW : RadialGood W) {s : ℝ} (hs : 0 < s)
    (h0 : ∀ t ∈ Icc (0 : ℝ) s, trace W t = 0) : False := by
  have hWc := hW.1
  have hW0 := hW.2.1
  have hcont : ContinuousOn (trace W) (Icc 0 s) := hW.2.2.2.1.mono Icc_subset_Ici_self
  obtain ⟨p, hp⟩ := fwdHull_nonempty_of_pos hWc hW0 hs
  have hq := fwdMapInv_mem_compl_fwdHull hWc hW0 hs.le (w := I) (by simp [H])
  have hconv : Convex ℝ H :=
    convex_halfSpace_gt (f := Complex.im) Complex.imLm.isLinear (0 : ℝ)
  have hpH : p ∈ H := (fwdHull_mono.2 s) hp
  have hj : JoinedIn H p (fwdMapInv W s I) :=
    hconv.isPathConnected ⟨p, hpH⟩ |>.joinedIn p hpH _ hq.1
  refine gen_no_path hWc hW0 hs.le (tendstoUniformlyOn_trace hW s) hcont hp hq hj.somePath
    fun v => ⟨hj.somePath_mem v, ?_⟩
  rintro ⟨t, ht, hteq⟩
  have := hj.somePath_mem v
  rw [← hteq, h0 t ht] at this
  exact lt_irrefl _ (show (0 : ℂ).im > 0 from this)

/-- **TIP, deterministic form.** If the key step's hypotheses hold at every `u > 0` of a dense
set `D`, the trace never returns to `0` at positive times. -/
theorem trace_ne_zero_of_dense (hW : RadialGood W) {D : Set ℝ} (hD : Dense D)
    (hgood : ∀ u ∈ D, 0 < u → RadialGood (shiftDrive W u) ∧ NoRealHitDet (shiftDrive W u) ∧
      Tendsto (fwdMapInv W u) (𝓝[H] 0) (𝓝 (trace W u)))
    {s : ℝ} (hs : 0 < s) : trace W s ≠ 0 := by
  intro hs0
  have hzeroD : EqOn (trace W) (fun _ => 0) (Ioo 0 s ∩ D) := fun u hu =>
    let h := hgood u hu.2 hu.1.1
    trace_eq_zero_of_shift hW hu.1.1 hu.1.2 h.1 h.2.1 h.2.2 hs0
  have hsub : Icc 0 s ⊆ closure (Ioo 0 s ∩ D) := by
    rw [← closure_Ioo hs.ne]
    exact closure_mono (hD.open_subset_closure_inter isOpen_Ioo) |>.trans (by rw [closure_closure])
  have hEq := hzeroD.of_subset_closure (hW.2.2.2.1.mono Icc_subset_Ici_self) continuousOn_const
    (inter_subset_left.trans Ioo_subset_Icc_self) hsub
  exact false_of_trace_eqOn_zero hW hs fun t ht => hEq ht

end RS
end QuantumZipper
