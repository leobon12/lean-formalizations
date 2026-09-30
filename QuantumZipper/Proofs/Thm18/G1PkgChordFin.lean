import QuantumZipper.Proofs.Thm18.G1PkgChordU

/-!
# G1 package: assembly of the chord part and of `G1PsiSelStmt`

Continuation of G1PkgChord.lean / G1PkgChordU.lean. The map
`U η w = if w ∈ ℍ then (if Good η then V η w else w) else c₀` (with `c₀` the junk value of
`invFunOn` off its range), its measurability, its derivative (Weierstrass on `ℍ`; `0` off `ℍ`,
where `U η` is constant on the closed lower half-plane), and:

* `G1Chord.exists_U` (generic side);
* **`G1Chord.g1ChordUnifSelStmt_of`** : `ChordSepStmt → SideUnifExistStmt → G1ChordUnifSelStmt`;
* **`G1Chord.g1PsiSelStmt_of_sep`** : `ChordSepStmt → SideUnifExistStmt → G1PsiSelStmt`.

Own argument (see G1PkgChord.lean).
-/

noncomputable section

open MeasureTheory Filter Set Function Topology Metric
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Chord

open CA.Kernel

/-- The junk value of `invFunOn` (and of `U`) off `ℍ`. -/
def c₀ : ℂ := Classical.choice (⟨0⟩ : Nonempty ℂ)

theorem invFunOn_eq_c₀ {φ : ℂ → ℂ} {D : Set ℂ} (hmaps : MapsTo φ D H) {w : ℂ} (hw : w ∉ H) :
    invFunOn φ D w = c₀ := by
  unfold invFunOn
  rw [dif_neg]
  · rfl
  · rintro ⟨a, ha, rfl⟩; exact hw (hmaps ha)

/-- A function constant on the closed lower half-plane has derivative `0` there. -/
theorem deriv_eq_zero_of_const_lower {f : ℂ → ℂ} {c : ℂ} (hf : ∀ z : ℂ, z.im ≤ 0 → f z = c)
    {w : ℂ} (hw : w.im ≤ 0) : deriv f w = 0 := by
  by_cases hd : DifferentiableAt ℂ f w
  · have hs := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
    have hmap : Tendsto (fun t : ℝ => w - (t : ℂ) * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝[≠] w) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : Continuous fun t : ℝ => w - (t : ℂ) * Complex.I := by fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with t ht
        show w - (t : ℂ) * Complex.I ≠ w
        intro h
        have : (t : ℂ) * Complex.I = 0 := by linear_combination -h
        rcases mul_eq_zero.1 this with h1 | h1
        · exact (ne_of_gt (show (0 : ℝ) < t from ht)) (by exact_mod_cast h1)
        · exact Complex.I_ne_zero h1
    have h2 := hs.comp hmap
    have h0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (slope f w ∘ fun t : ℝ => w - (t : ℂ) * Complex.I) t = 0 := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      have him : (w - (t : ℂ) * Complex.I).im ≤ 0 := by simp; linarith
      simp only [Function.comp, slope_def_field, hf _ him, hf _ hw, sub_self, zero_div]
    exact tendsto_nhds_unique h2 (tendsto_const_nhds.congr' (h0.mono fun t ht => ht.symm))
  · exact deriv_zero_of_not_differentiableAt hd

section U

variable (ηk : ℕ → ℝ → ℂ) (ψk : ℕ → ℂ → ℂ)

open Classical in
/-- The selected inverse uniformizer. -/
def U (η : ℝ → ℂ) (w : ℂ) : ℂ :=
  if w ∈ H then (if Good ηk ψk η then V ηk ψk η w else w) else c₀

variable {ηk ψk}

theorem measurable_sel_apply {g : ℕ → ℂ → ℂ} (hg : ∀ k, Measurable (g k)) (n : ℕ) :
    Measurable fun p : (ℝ → ℂ) × ℂ => g (sel ηk n p.1) p.2 := by
  have hG : Measurable fun p : ℂ × ℕ => g p.2 p.1 := measurable_from_prod_countable_left hg
  exact hG.comp (measurable_snd.prodMk ((measurable_sel ηk n).comp measurable_fst))

theorem measurable_U (hψm : ∀ k, Measurable (ψk k)) :
    Measurable fun p : (ℝ → ℂ) × ℂ => U ηk ψk p.1 p.2 := by
  classical
  have hV : Measurable fun p : (ℝ → ℂ) × ℂ => V ηk ψk p.1 p.2 :=
    (StronglyMeasurable.limUnder fun n =>
      (measurable_sel_apply hψm n).stronglyMeasurable).measurable
  unfold U
  refine Measurable.ite (measurable_snd isOpen_H.measurableSet) (Measurable.ite
    ((measurableSet_good ηk ψk).preimage measurable_fst) hV measurable_snd) measurable_const

theorem deriv_U_of_good (hψd : ∀ k, DifferentiableOn ℂ (ψk k) H) {η : ℝ → ℂ}
    (hg : Good ηk ψk η) {w : ℂ} (hw : w ∈ H) :
    deriv (U ηk ψk η) w = limUnder atTop fun n => deriv (ψk (sel ηk n η)) w := by
  classical
  have he : U ηk ψk η =ᶠ[𝓝 w] V ηk ψk η := by
    filter_upwards [isOpen_H.mem_nhds hw] with z hz
    simp only [U, if_pos hz, if_pos hg]
  rw [he.deriv_eq]
  have h := (hg.tendstoLocallyUniformlyOn hψd).deriv (Eventually.of_forall fun n => hψd _)
    isOpen_H
  exact (h.tendsto_at hw).limUnder_eq.symm

theorem deriv_U_of_not_good {η : ℝ → ℂ} (hg : ¬ Good ηk ψk η) {w : ℂ} (hw : w ∈ H) :
    deriv (U ηk ψk η) w = 1 := by
  classical
  have he : U ηk ψk η =ᶠ[𝓝 w] id := by
    filter_upwards [isOpen_H.mem_nhds hw] with z hz
    simp only [U, if_pos hz, if_neg hg, id]
  rw [he.deriv_eq, deriv_id]

theorem deriv_U_of_not_mem {η : ℝ → ℂ} {w : ℂ} (hw : w ∉ H) : deriv (U ηk ψk η) w = 0 := by
  classical
  refine deriv_eq_zero_of_const_lower (c := c₀) (fun z hz => ?_) (not_lt.1 hw)
  have : z ∉ H := fun h => absurd (show 0 < z.im from h) (not_lt.2 hz)
  simp only [U, if_neg this]

theorem measurable_log_deriv_U (hψd : ∀ k, DifferentiableOn ℂ (ψk k) H) :
    Measurable fun p : (ℝ → ℂ) × ℂ => Real.log ‖deriv (U ηk ψk p.1) p.2‖ := by
  classical
  have hD : Measurable fun p : (ℝ → ℂ) × ℂ =>
      limUnder atTop fun n => deriv (ψk (sel ηk n p.1)) p.2 :=
    (StronglyMeasurable.limUnder fun n =>
      (measurable_sel_apply (fun k => measurable_deriv (ψk k)) n).stronglyMeasurable).measurable
  have e : (fun p : (ℝ → ℂ) × ℂ => Real.log ‖deriv (U ηk ψk p.1) p.2‖) =
      fun p => if p.2 ∈ H then (if Good ηk ψk p.1 then
        Real.log ‖limUnder atTop fun n => deriv (ψk (sel ηk n p.1)) p.2‖ else 0) else 0 := by
    funext p
    by_cases hw : p.2 ∈ H
    · by_cases hg : Good ηk ψk p.1
      · rw [if_pos hw, if_pos hg, deriv_U_of_good hψd hg hw]
      · rw [if_pos hw, if_neg hg, deriv_U_of_not_good hg hw, norm_one, Real.log_one]
    · rw [if_neg hw, deriv_U_of_not_mem hw, norm_zero, Real.log_zero]
  rw [e]
  exact Measurable.ite (measurable_snd isOpen_H.measurableSet) (Measurable.ite
    ((measurableSet_good ηk ψk).preimage measurable_fst)
    (Real.measurable_log.comp hD.norm) measurable_const) measurable_const

end U

/-- **Generic chord-measurable selection** for one side. -/
theorem exists_U {dom : (ℝ → ℂ) → Set ℂ} {Nrm : (ℝ → ℂ) → (ℂ → ℂ) → Prop}
    (hS : SideData dom Nrm) (hsep : ChordSepStmt) :
    ∃ U : (ℝ → ℂ) → ℂ → ℂ, (Measurable fun p : (ℝ → ℂ) × ℂ => U p.1 p.2) ∧
      (Measurable fun p : (ℝ → ℂ) × ℂ => Real.log ‖deriv (U p.1) p.2‖) ∧
      ∀ η, IsSimpleChord η → ∃ φ, IsNormalizedUniformizer (dom η) φ ∧ U η = invFunOn φ (dom η) := by
  obtain ⟨ηk, hk, hden⟩ := hsep
  choose φk hφk using fun k => hS.exists_nrm (ηk k) (hk k)
  set ψk : ℕ → ℂ → ℂ := fun k => invFunOn (φk k) (dom (ηk k)) with hψk
  have hprops := fun k => G1.invFunOn_props (hS.isOpen _ (hk k)) (hS.normalized _ _ (hk k) (hφk k))
  have hψd : ∀ k, DifferentiableOn ℂ (ψk k) H := fun k => (hprops k).1
  have hψm : ∀ k, Measurable (ψk k) := fun k => (hprops k).2.2.1
  refine ⟨U ηk ψk, measurable_U hψm, measurable_log_deriv_U hψd, fun η hη => ?_⟩
  obtain ⟨φ, hφ⟩ := hS.exists_nrm η hη
  have hφn := hS.normalized η φ hη hφ
  have hT : TendstoLocallyUniformlyOn (fun n => ψk (sel ηk n η)) (invFunOn φ (dom η)) atTop H :=
    hS.kernel (fun n => ηk (sel ηk n η)) η (fun n => φk (sel ηk n η)) φ (fun n => hk _) hη
      (sphereUniformConv_sel ηk hk hden hη) (fun n => hφk _) hφ
  have hg : Good ηk ψk η := good_of_tendsto hT
  refine ⟨φ, hφn, funext fun w => ?_⟩
  classical
  by_cases hw : w ∈ H
  · simp only [U, if_pos hw, if_pos hg]
    exact (hT.tendsto_at hw).limUnder_eq
  · simp only [U, if_neg hw]
    exact (invFunOn_eq_c₀ hφn.1.mapsTo hw).symm

/-- **(C2) Existence of the side-normalized uniformizers** (`φ(∓1) = ∓1`). -/
def SideUnifExistStmt : Prop :=
  ∀ η, IsSimpleChord η → (∃ φ, IsLeftUniformizer η φ) ∧ ∃ φ, IsRightUniformizer η φ

theorem sideData_left (hex : SideUnifExistStmt) :
    SideData (fun η => sideDom η true) IsLeftUniformizer where
  isOpen _η hη := G1.isOpen_component hη true
  normalized _η _φ _ hφ := hφ.1
  exists_nrm η hη := (hex η hη).1
  kernel η ηi φ φi hη hηi hc hφ hφi := (chordKernelTheoremLeft η ηi φ φi hη hηi hc hφ hφi).1

theorem sideData_right (hex : SideUnifExistStmt) :
    SideData (fun η => sideDom η false) IsRightUniformizer where
  isOpen _η hη := G1.isOpen_component hη false
  normalized _η _φ _ hφ := hφ.1
  exists_nrm η hη := (hex η hη).2
  kernel η ηi φ φi hη hηi hc hφ hφi := (chordKernelTheoremRight η ηi φ φi hη hηi hc hφ hφi).1

/-- **The chord part from separability and normalized existence.** -/
theorem g1ChordUnifSelStmt_of (hsep : ChordSepStmt) (hex : SideUnifExistStmt) :
    G1ChordUnifSelStmt := by
  obtain ⟨UL, hLm, hLd, hLe⟩ := exists_U (sideData_left hex) hsep
  obtain ⟨UR, hRm, hRd, hRe⟩ := exists_U (sideData_right hex) hsep
  refine ⟨fun left => if left then UL else UR, fun left => ?_, fun left => ?_,
    fun η hη left => ?_⟩
  · cases left
    · exact hRm
    · exact hLm
  · cases left
    · exact hRd
    · exact hLd
  · cases left
    · exact hRe η hη
    · exact hLe η hη

/-- **`G1PsiSelStmt` from separability and normalized existence** (trace part proved). -/
theorem g1PsiSelStmt_of_sep (hsep : ChordSepStmt) (hex : SideUnifExistStmt) : G1PsiSelStmt :=
  g1PsiSelStmt_of_chordUnifSel (g1ChordUnifSelStmt_of hsep hex)

end G1Chord
end Thm18Asm
end QuantumZipper
