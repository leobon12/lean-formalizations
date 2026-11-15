import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Impl.ForceBoundaryData

/-!
# The bounded harmonic extension of finite piecewise-constant boundary data

Packet PROVE-T15-COMP. Implementation proof of the companion theorem of Theorem 1.5
(Specification p. 5, the convention on p. 2 "their harmonic extension means the bounded harmonic
extension", and p. 457, §3.1): if `b : ℝ → ℝ` is locally constant off the finite set `jumps`
(`IsPiecewiseConstantBoundaryData b jumps`, frozen and sealed), then `b` has a bounded harmonic
extension in `ℍ` with boundary values `b` off `jumps`, unique on `ℍ`.

## Proof
Count the jumps to the left: `jumpCount jumps t = #{y ∈ jumps | y ≤ t}`. If `s ≤ t` are off `jumps`
and have the same count, no jump lies in `[s, t]`, so `b` is locally constant on the preconnected
set `[s, t]` and `b s = b t`. Hence off `jumps` the value `b t` depends only on `jumpCount jumps t`.
List the jumps increasingly (`Finset.orderEmbOfFin`) as the breakpoints of a `StepData` whose
`k`-th value is `b r` for any `r ∉ jumps` with `jumpCount jumps r = k` (and `0` if there is none);
its boundary function is `b` off `jumps`, and its explicit extension
`InteractingSLE.StepData.harmonicExtH` is harmonic, bounded and has these boundary values
(`StepData.tendsto_harmonicExtH`). Uniqueness is the landed Lindelöf argument with a finite
exceptional set, `InteractingSLE.Impl.eqOn_of_isBoundedHarmonicExtension`.

## Main statements
* `InteractingSLE.PiecewiseConstant.eq_of_jumpCount_eq`: `b` depends only on the jump count;
* `InteractingSLE.PiecewiseConstant.isBoundedHarmonicExtension_harmonicExtH_stepData`: existence;
* `InteractingSLE.PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension`: uniqueness on `ℍ`;
* `InteractingSLE.PiecewiseConstant.existsUnique_isBoundedHarmonicExtension`: the frozen
  companion statement, with the hypothesis explicit.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology

namespace InteractingSLE

namespace PiecewiseConstant

/-- The number of points of `jumps` at or to the left of `t`. -/
def jumpCount (jumps : Finset ℝ) (t : ℝ) : ℕ :=
  (jumps.filter fun y => y ≤ t).card

/-- If `s ≤ t`, `s ∉ jumps`, and `s`, `t` have the same jump count, no jump lies in `[s, t]`. -/
theorem notMem_of_jumpCount_eq {jumps : Finset ℝ} {s t y : ℝ} (hs : s ∉ jumps) (hst : s ≤ t)
    (h : jumpCount jumps s = jumpCount jumps t) (hy : y ∈ jumps) : y ∉ Icc s t := by
  rintro ⟨hsy, hyt⟩
  have hsub : (jumps.filter fun r => r ≤ s) ⊆ jumps.filter fun r => r ≤ t := fun r hr =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hr).1, (Finset.mem_filter.1 hr).2.trans hst⟩
  have hss : (jumps.filter fun r => r ≤ s) ⊂ jumps.filter fun r => r ≤ t := by
    refine (Finset.ssubset_iff_of_subset hsub).2 ⟨y, Finset.mem_filter.2 ⟨hy, hyt⟩, fun hy' => ?_⟩
    exact hs (le_antisymm hsy (Finset.mem_filter.1 hy').2 ▸ hy)
  have := Finset.card_lt_card hss
  unfold jumpCount at h
  omega

/-- Piecewise-constant data take the same value at two points `s ≤ t` off the jumps with the
same jump count. -/
theorem eq_of_jumpCount_eq_of_le {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {s t : ℝ} (hs : s ∉ jumps) (hst : s ≤ t)
    (h : jumpCount jumps s = jumpCount jumps t) : b s = b t := by
  have hoff : ∀ r ∈ Icc s t, r ∉ jumps := fun r hr hrj =>
    notMem_of_jumpCount_eq hs hst h hrj hr
  have : PreconnectedSpace (Icc s t) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlc : IsLocallyConstant fun r : Icc s t => b r := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun r => ?_
    exact (continuous_subtype_val.tendsto r).eventually (hb r.1 (hoff r.1 r.2))
  exact hlc.apply_eq_of_preconnectedSpace ⟨s, left_mem_Icc.2 hst⟩ ⟨t, right_mem_Icc.2 hst⟩

/-- **Piecewise-constant data depend only on the jump count** off the jumps. -/
theorem eq_of_jumpCount_eq {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {s t : ℝ} (hs : s ∉ jumps) (ht : t ∉ jumps)
    (h : jumpCount jumps s = jumpCount jumps t) : b s = b t := by
  rcases le_total s t with hst | hts
  · exact eq_of_jumpCount_eq_of_le hb hs hst h
  · exact (eq_of_jumpCount_eq_of_le hb ht hts h.symm).symm

/-- The number of breakpoints `jumps.orderEmbOfFin rfl j ≤ t` is the jump count of `t`. -/
theorem card_filter_orderEmbOfFin_le (jumps : Finset ℝ) (t : ℝ) :
    (Finset.univ.filter fun j => jumps.orderEmbOfFin rfl j ≤ t).card = jumpCount jumps t := by
  refine Finset.card_bij (fun j _ => jumps.orderEmbOfFin rfl j) (fun j hj => ?_)
    (fun _ _ _ _ e => (jumps.orderEmbOfFin rfl).injective e) (fun y hy => ?_)
  · exact Finset.mem_filter.2
      ⟨jumps.orderEmbOfFin_mem rfl j, (Finset.mem_filter.1 hj).2⟩
  · obtain ⟨hyj, hyt⟩ := Finset.mem_filter.1 hy
    have : y ∈ Set.range (jumps.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hyj
    obtain ⟨j, rfl⟩ := this
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, hyt⟩, rfl⟩

open scoped Classical in
/-- The step data of `b` with breakpoints the jumps (listed increasingly): the `k`-th value is the
value of `b` at some point off the jumps with jump count `k` (`0` if there is none). -/
def stepData (b : ℝ → ℝ) (jumps : Finset ℝ) : StepData where
  n := jumps.card
  x := jumps.orderEmbOfFin rfl
  monotone_x := (jumps.orderEmbOfFin rfl).monotone
  v := fun k => if h : ∃ r, r ∉ jumps ∧ jumpCount jumps r = k then b h.choose else 0

theorem stepData_x_mem (b : ℝ → ℝ) (jumps : Finset ℝ) (j : Fin (stepData b jumps).n) :
    (stepData b jumps).x j ∈ jumps :=
  jumps.orderEmbOfFin_mem rfl j

/-- Off the jumps, the boundary function of `stepData b jumps` is `b`. -/
theorem bdry_stepData {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {t : ℝ} (ht : t ∉ jumps) :
    (stepData b jumps).bdry t = b t := by
  have hc := card_filter_orderEmbOfFin_le jumps t
  unfold StepData.bdry
  simp only [stepData]
  split_ifs with h
  · obtain ⟨hr, hrc⟩ := h.choose_spec
    exact eq_of_jumpCount_eq hb hr ht (hrc.trans hc)
  · exact absurd ⟨t, ht, hc.symm⟩ h

/-- **Existence**: the explicit extension of `stepData b jumps` is a bounded harmonic extension
of `b` off `jumps`. -/
theorem isBoundedHarmonicExtension_harmonicExtH_stepData {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) :
    IsBoundedHarmonicExtension b jumps (stepData b jumps).harmonicExtH := by
  refine ⟨(stepData b jumps).harmonicOnNhd_harmonicExtH,
    ⟨max |⨅ k, (stepData b jumps).v k| |⨆ k, (stepData b jumps).v k|, fun z hz => ?_⟩,
    fun x hx => ?_⟩
  · obtain ⟨h1, h2⟩ := (stepData b jumps).harmonicExtH_mem_Icc hz
    exact abs_le_max_abs_abs h1 h2
  · have hx' : x ∉ jumps := hx
    rw [← bdry_stepData hb hx']
    exact (stepData b jumps).tendsto_harmonicExtH fun j hj =>
      hx' (hj ▸ stepData_x_mem b jumps j)

/-- **Uniqueness**: two bounded harmonic extensions of the same data off a finite set agree on
`ℍ` (the landed `Impl` theorem, whose predicate is definitionally the frozen one). -/
theorem eqOn_of_isBoundedHarmonicExtension {g : ℝ → ℝ} {S : Set ℝ} (hS : S.Finite)
    {u v : ℂ → ℝ} (hu : IsBoundedHarmonicExtension g S u)
    (hv : IsBoundedHarmonicExtension g S v) : EqOn v u QuantumZipper.H :=
  Impl.eqOn_of_isBoundedHarmonicExtension hS hu hv

/-- **Well-definedness of the bounded harmonic extension of finite piecewise-constant boundary
data**: the statement of the frozen companion of Theorem 1.5
`InteractingSLE.IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension`. -/
theorem existsUnique_isBoundedHarmonicExtension {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u ∧
      ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension b jumps v → EqOn v u QuantumZipper.H :=
  ⟨(stepData b jumps).harmonicExtH, isBoundedHarmonicExtension_harmonicExtH_stepData hb,
    fun _ hv => eqOn_of_isBoundedHarmonicExtension jumps.finite_toSet
      (isBoundedHarmonicExtension_harmonicExtH_stepData hb) hv⟩

end PiecewiseConstant

end InteractingSLE
