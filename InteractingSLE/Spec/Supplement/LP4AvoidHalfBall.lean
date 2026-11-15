import InteractingSLE.Spec.Supplement.LP4Terminal
import QuantumZipper.Proofs.RS.HullBasics

/-!
# LP4's positive-probability step: reduction to a half-ball in a finite-time hull

Packet PROVE-LP16. Specification p. 483 (end of the first half of LP4's proof): "Every later relative trace lies in
the closure of the remaining component and avoids an open neighborhood of `F`. By compactness and continuity of
`f_T` on the spherical closure, its physical image is bounded away from `0`."

The deterministic end of that step is proved here in the form: **if some finite-time hull contains a half-ball
`ℍ ∩ B(0, ε)`, every generating trace stays at distance `≥ ε` from `0` afterwards, so `0` is not in its terminal
cluster set** (`le_norm_of_halfBall_subset`, `zero_notMem_terminalClusterSet_of_halfBall`). The proof uses only the
strict growth of Loewner hulls (QuantumZipper's `RS.fwdHull_ssubset`): while the trace stays in the hull `K_s`, the
filled hull does not grow (`eq_of_isFilling_of_subset`).

Consequently `LP4AvoidStatement` follows from the named input **`LP4HalfBallStatement`** (same hypotheses; conclusion:
with positive probability some finite-time hull contains a half-ball around `0`) — `lp4AvoidStatement_of_halfBall`.
This is a conditional helper; it replaces no source theorem. The half-ball statement is what the source's
construction produces before its last sentence (the collar `[Zha10, Corollary 6.1]` at the capped time `τ_m` gives
a neighbourhood of the compact fiber `F` in the future hull, and continuity of `f_T` turns it into a relative
neighbourhood of `0` in the physical hull).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LP

open QuantumZipper

/-! ### Filled hulls do not grow while the trace stays inside -/

/-- If the points of `A₂ \ A₁` in `ℍ` lie in `K₁` and `K₁ ⊆ K₂ ⊆ ℍ`, then the filled hulls agree. -/
theorem eq_of_isFilling_of_subset {K₁ K₂ A₁ A₂ : Set ℂ} (h1 : IsFilling K₁ A₁) (h2 : IsFilling K₂ A₂)
    (hnew : ∀ z ∈ A₂, z ∈ H → z ∉ A₁ → z ∈ K₁) (hK : K₁ ⊆ K₂) (hK₂ : K₂ ⊆ H) :
    K₁ = K₂ := by
  obtain ⟨⟨z₁, -, hc₁⟩, -⟩ := h1
  obtain ⟨⟨z₂, hz₂, hc₂⟩, -⟩ := h2
  -- `ℍ \ K₁` avoids `A₂`
  have hsub : H \ K₁ ⊆ H \ A₂ := by
    intro z hz
    refine ⟨hz.1, fun hzA => ?_⟩
    by_cases hz1 : z ∈ A₁
    · have : z ∈ H \ A₁ := by rw [← hc₁] at hz; exact connectedComponentIn_subset _ _ hz
      exact this.2 hz1
    · exact hz.2 (hnew z hzA hz.1 hz1)
  have hz₂1 : z₂ ∈ H \ K₁ := ⟨hz₂.1, fun h => hz₂.2 (hK h)⟩
  have hpre : IsPreconnected (H \ K₁) := by
    rw [← hc₁]; exact isPreconnected_connectedComponentIn
  have hle : H \ K₁ ⊆ H \ K₂ := by
    rw [← hc₂]; exact hpre.subset_connectedComponentIn hz₂1 hsub
  refine hK.antisymm fun z hz => ?_
  by_contra hz1
  exact (hle ⟨hK₂ hz, hz1⟩).2 hz

variable {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}

/-- **After a half-ball is swallowed, the trace stays away from `0`.** If `K_T ⊇ ℍ ∩ B(0, ε)`, every generating
trace on `[0, ∞)` satisfies `‖η t‖ ≥ ε` for `t > T`. -/
theorem le_norm_of_halfBall_subset (hw : Continuous w) (hw0 : w 0 = 0) (hη : IsGeneratingTrace w ⊤ η)
    {T : ℝ≥0} {ε : ℝ} (hball : ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull (fun s : ℝ => w s.toNNReal) T)
    {t : ℝ≥0} (hTt : T < t) : ε ≤ ‖η t‖ := by
  by_contra hlt
  push Not at hlt
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hηc : Continuous η := continuousOn_univ.1 (by simpa using hη.2.1)
  have hev : ∀ᶠ s in 𝓝[<] t, ‖η s‖ < ε :=
    nhdsWithin_le_nhds ((hηc.norm.continuousAt).eventually (gt_mem_nhds hlt))
  obtain ⟨l, hlt', hIoo⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hTt).1 hev
  obtain ⟨s₁, hs₁, hs₁t⟩ := exists_between (max_lt hlt' hTt)
  have hl : l < s₁ := (le_max_left _ _).trans_lt hs₁
  have hT1 : T < s₁ := (le_max_right _ _).trans_lt hs₁
  have hF1 := hη.2.2 s₁ ENNReal.coe_lt_top
  have hF2 := hη.2.2 t ENNReal.coe_lt_top
  have hmono : fwdHull W s₁ ⊆ fwdHull W t := fwdHull_mono.1 (by exact_mod_cast hs₁t.le)
  have hTs : fwdHull W T ⊆ fwdHull W s₁ := fwdHull_mono.1 (by exact_mod_cast hT1.le)
  have heq := eq_of_isFilling_of_subset hF1 hF2
    (fun z hz hzH hz1 => by
      obtain ⟨r, hr, rfl⟩ := hz
      have hrs : s₁ < r := by
        by_contra h; push Not at h; exact hz1 ⟨r, ⟨hr.1, h⟩, rfl⟩
      have hnorm : ‖η r‖ < ε := by
        rcases hr.2.lt_or_eq with h | h
        · exact hIoo ⟨hl.trans hrs, h⟩
        · rw [h]; exact hlt
      exact hTs (hball _ hzH hnorm))
    hmono (fwdHull_mono.2 _)
  exact (RS.fwdHull_ssubset hW hW0 s₁.coe_nonneg (by exact_mod_cast hs₁t)).ne heq

/-- **`0` is not in the terminal cluster set** once a finite-time hull contains a half-ball around `0`. -/
theorem zero_notMem_terminalClusterSet_of_halfBall (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsGeneratingTrace w ⊤ η) {T : ℝ≥0} {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull (fun s : ℝ => w s.toNNReal) T) :
    (0 : ℂ) ∉ terminalClusterSet η := by
  obtain ⟨n, hn⟩ := exists_nat_gt (T : ℝ)
  intro h0
  have hsub : closure (η '' Ici (n : ℝ≥0)) ⊆ {p : ℂ | ε ≤ ‖p‖} := by
    refine closure_minimal ?_ (isClosed_le continuous_const continuous_norm)
    rintro _ ⟨t, ht, rfl⟩
    have hTt : T < t := lt_of_lt_of_le (by exact_mod_cast hn) ht
    exact le_norm_of_halfBall_subset hw hw0 hη hball hTt
  have := hsub (mem_iInter.1 h0 n)
  simp only [mem_ofPred_eq, norm_zero] at this
  linarith

/-! ### The reduction -/

/-- **Named input: a half-ball in a finite-time hull with positive probability** (the output of the first half of
LP4's proof before its last sentence, specification pp. 482–483). Hypotheses as in `LP4AvoidStatement`. Conclusion:
for every two-seed evolution, with positive probability some hull `K_T`, `T < ∞`, contains `ℍ ∩ B(0, ε)` for some
`ε > 0`. -/
def LP4HalfBallStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 2 → -2 < rR → rR < κ / 2 - 2 →
    (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∃ᵐ ω ∂P, ∃ T : ℝ≥0, ∃ ε > (0 : ℝ),
          ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull (fun s : ℝ => W s.toNNReal ω) T

/-- **`LP4AvoidStatement` from the half-ball input.** The infinite lifetime (`Sec7.ae_lifetime_eq_top_twoSeed`)
and the finite-continuity premise give a generating trace on `[0, ∞)` almost surely; on the positive-probability
half-ball event, `0` is not in its terminal cluster set. -/
theorem lp4AvoidStatement_of_halfBall (h : LP4HalfBallStatement.{u}) : LP4AvoidStatement.{u} := by
  intro κ hκ rL rR hL hLc hR hRc hcont Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hhb := h κ hκ rL rR hL hLc hR hRc hcont P 𝓕 W VL VR B ζ hE
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    Sec7.ae_lifetime_eq_top_twoSeed (ρL := fun _ => rL) (ρR := fun _ => rR) (by linarith) hL hR
      Sec7.jacobiDiffusionExistsStatement hE
  refine hhb.mp ?_
  filter_upwards [hζ, hcont P 𝓕 W VL VR B ζ hE, hE.2.2.2.2] with ω hζω htr hp
  rintro ⟨T, ε, hε, hball⟩
  rw [hζω] at htr hp
  obtain ⟨η, hη⟩ := htr
  obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
  exact ⟨η, hη, zero_notMem_terminalClusterSet_of_halfBall hwc hw0 hη hε hball⟩

end InteractingSLE.LP
