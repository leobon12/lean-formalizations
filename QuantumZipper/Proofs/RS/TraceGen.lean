import QuantumZipper.Proofs.RS.GenerationCor
import QuantumZipper.Proofs.RS.TraceMain
import QuantumZipper.Blueprint.External3

/-!
# EXT-RS node AD1-0: `Blueprint.RohdeSchrammTraceGen` for `κ < 8`

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §5, node AD1-0 (DECISIONS D4, DEVIATIONS L-AD1).

Sources: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 5.1
(p. 20) and Thm 4.1 (pp. 19–20); A. Kemppainen, *Schramm–Loewner Evolution* (2017), Thm 5.2 and
Def. 5.3 (p. 76); G. Lawler, *Conformally Invariant Processes in the Plane* (2005), Thm 7.4
(p. 157).

Proof: TR4 (`ae_sleTrace_good`: the trace exists, is continuous, with a uniform radial bound)
feeds the bridge `tendstoUniformlyOn_fwdMapInv_mul_I_of_bound` and GEN-a
(`exists_compl_fwdHull_eq_connectedComponentIn_mul_I`), which gives `H_t` as the component of
`H \ η[0,t]` containing `M' i` for all large `M'`. The Blueprint statement allows any `M` with
`‖η(s)‖ < M` on `[0,t]`; the vertical segment `[M i, M' i]` misses `η[0,t]` (own elementary
step), so the components of `M i` and `M' i` agree.

The argument works for all `0 < κ < 8`; the κ-range `(4,8)` of AD1-0 is a special case.
-/

noncomputable section

open Set Filter Topology Metric Complex MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.RS

/-- Deterministic core: if the trace is continuous on `[0,t]` with a uniform radial bound, then
for every `M` bounding `‖trace W‖` on `[0,t]` strictly, `H \ K_t` is the component of
`H \ trace W '' [0,t]` containing `M i`. -/
theorem compl_fwdHull_eq_connectedComponentIn_of_norm_lt {W : ℝ → ℝ} {t : ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hunif : TendstoUniformlyOn (fun (y : ℝ) (s : ℝ) => fwdMapInv W s (y * I)) (trace W)
      (𝓝[>] 0) (Icc 0 t))
    (hcont : ContinuousOn (trace W) (Icc 0 t)) {M : ℝ}
    (hM : ∀ s ∈ Icc 0 t, ‖trace W s‖ < M) :
    H \ fwdHull W t = connectedComponentIn (H \ trace W '' Icc 0 t) ((M : ℂ) * I) := by
  obtain ⟨M₀, hM₀⟩ := exists_compl_fwdHull_eq_connectedComponentIn_mul_I hW hW0 ht hunif hcont
  have hM0 : 0 < M := lt_of_le_of_lt (norm_nonneg _) (hM 0 ⟨le_rfl, ht⟩)
  set M' := max M M₀ with hM'
  obtain ⟨_, hEq⟩ := hM₀ M' (le_max_right _ _)
  rw [hEq]
  -- the vertical segment from `M i` to `M' i` misses the trace
  set S : Set ℂ := (fun y : ℝ => (y : ℂ) * I) '' Icc M M' with hS
  have hSpre : IsPreconnected S :=
    isPreconnected_Icc.image _ (by fun_prop : Continuous fun y : ℝ => (y : ℂ) * I).continuousOn
  have hSsub : S ⊆ H \ trace W '' Icc 0 t := by
    rintro _ ⟨y, hy, rfl⟩
    have hy0 : 0 < y := lt_of_lt_of_le hM0 hy.1
    refine ⟨show 0 < ((y : ℂ) * I).im by simpa using hy0, ?_⟩
    rintro ⟨s, hs, hsy⟩
    have h1 := hM s hs
    rw [hsy, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos hy0] at h1
    linarith [hy.1]
  have hMS : (M : ℂ) * I ∈ S := ⟨M, ⟨le_rfl, le_max_left _ _⟩, rfl⟩
  have hM'S : (M' : ℂ) * I ∈ S := ⟨M', ⟨le_max_left _ _, le_rfl⟩, rfl⟩
  exact (connectedComponentIn_eq (hSpre.subset_connectedComponentIn hMS hSsub hM'S)).symm

/-- **AD1-0 for `0 < κ < 8`.** The SLE trace exists, is continuous, and generates the hulls
(RS Thm 5.1, p. 20; Kemppainen Thm 5.2, Def. 5.3, p. 76). -/
theorem rohdeSchrammTraceGen_of_lt_eight {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) :
    Blueprint.RohdeSchrammTraceGen κ := by
  intro Ω _ P _ B hB
  obtain ⟨δ, hδ, h⟩ := ae_sleTrace_good hB hκ hκ8
  filter_upwards [h, hB.cont, hB.eval_zero_ae_eq_zero] with ω hω hc h0
  obtain ⟨h0', hcont, hbd⟩ := hω
  refine ⟨h0', hcont, fun t ht M hM => ?_⟩
  have hW : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  obtain ⟨C, hC⟩ := hbd ⌈t⌉₊
  have hunif := tendstoUniformlyOn_fwdMapInv_mul_I_of_bound (W := drive κ B ω) (t := t) hδ
    (C := C) fun s hs y hy => hC s ⟨hs.1, hs.2.trans (Nat.le_ceil t)⟩ y hy
  exact compl_fwdHull_eq_connectedComponentIn_of_norm_lt hW hW0 ht hunif
    (hcont.mono Icc_subset_Ici_self) hM

/-- **AD1-0** (`EXT_RS_BLUEPRINT.md` §5, DECISIONS D4): `RohdeSchrammTraceGen κ` for
`κ ∈ (4,8)`. -/
theorem rohdeSchrammTraceGen {κ : ℝ} (hκ : 4 < κ) (hκ8 : κ < 8) :
    Blueprint.RohdeSchrammTraceGen κ :=
  rohdeSchrammTraceGen_of_lt_eight (by linarith) hκ8

end QuantumZipper.RS
