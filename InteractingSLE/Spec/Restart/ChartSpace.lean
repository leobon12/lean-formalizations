/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.Carrier
import InteractingSLE.Spec.Sec2.AssemblyCode
import LQGMetric.Field.StandardBorelRange

/-!
# The canonical restart space

Packet PROVE-RESTART-CPL2, step (2) of the PROVE-RESTART-CPL handoff ("a standard Borel `S` carrying the field and,
for each continuation, the lifetime, path …"). The restart carrier `FirstContactRestartStatement` needs a canonical
space `S : Type` with coordinates `(H, γ₁, γ₂, U₁, U₂)` satisfying `IsRestartCoordinates`: measurable coordinates and
**every** path `γᵢ s` continuous on its closed available interval `[0, Uᵢ s]`. Mathlib (`a4c8ef0a`) has no Polish
structure on `C(ℝ≥0, ℂ)`, so paths are coded by their values at the dyadic times (the codes `Sec2.Assembly.PCode` of
Theorem 2.2's assembly, one real code for each of the real and imaginary parts), and a code is decoded only when it
is uniformly continuous on the dyadic times of every compact part of `[0, U]` (`GoodPath`, a measurable condition);
otherwise the path coordinate is `0`.

* `RestartSpace = 𝒟'(ℍ) × ((PCode × PCode) × ℝ≥0∞) × ((PCode × PCode) × ℝ≥0∞)`: a standard Borel space;
* `RestartSpace.field`, `path₁`, `path₂`, `life₁`, `life₂`: the coordinates;
  **`isRestartCoordinates_restartSpace`**: they satisfy `IsRestartCoordinates` (at every point);
* `RestartSpace.mk'`: the code of a field and two paths with lifetimes; **`measurable_mk'`** (measurable when the
  field, every time coordinate of the paths and the lifetimes are); **`path₁_mk'`**, `path₂_mk'`, `field_mk'`,
  `life₁_mk'`, `life₂_mk'`: decoding returns the field, the lifetimes, and each path on its closed available interval
  as soon as the path is continuous there.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

open Sec2.Assembly

/-! ### Decoding a complex path with a lifetime -/

/-- A real code is good for the lifetime `U` if it is uniformly continuous on the dyadic times of every `[0, T]`,
`T ≤ U` finite. -/
def GoodCode (a : PCode) (U : ℝ≥0∞) : Prop := ∀ T : ℝ≥0, (T : ℝ≥0∞) ≤ U → UC a T

theorem goodCode_iff (a : PCode) (U : ℝ≥0∞) :
    GoodCode a U ↔ (U = ⊤ ∧ ∀ N : ℕ, UC a N) ∨ (U ≠ ⊤ ∧ UC a U.toNNReal) := by
  constructor
  · intro h
    by_cases hU : U = ⊤
    · exact Or.inl ⟨hU, fun N => h N (by simp [hU])⟩
    · exact Or.inr ⟨hU, h _ (ENNReal.coe_toNNReal_le_self)⟩
  · rintro (⟨hU, h⟩ | ⟨hU, h⟩) T hT
    · obtain ⟨N, hN⟩ := exists_nat_ge T
      exact (h N).mono hN
    · exact h.mono ((ENNReal.toNNReal_le_toNNReal ENNReal.coe_ne_top hU).2 hT)

/-- `UC` is jointly measurable in the code and the horizon. -/
theorem measurableSet_UC_prod : MeasurableSet {p : PCode × ℝ≥0 | UC p.1 p.2} := by
  have hset : {p : PCode × ℝ≥0 | UC p.1 p.2} = ⋂ m : ℕ, ⋃ N : ℕ, ⋂ n : ℕ, ⋂ k : ℕ, ⋂ n' : ℕ, ⋂ k' : ℕ,
      ({p : PCode × ℝ≥0 | p.2 < dyad n k} ∪ {p : PCode × ℝ≥0 | p.2 < dyad n' k'}) ∪
        ({p : PCode × ℝ≥0 | |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1) →
          |p.1 n k - p.1 n' k'| ≤ 1 / (m + 1)}) := by
    ext p
    simp only [UC, mem_ofPred_eq, mem_iInter, mem_iUnion, mem_union, not_le.symm]
    refine forall_congr' fun m => exists_congr fun N => forall_congr' fun n => forall_congr' fun k =>
      forall_congr' fun n' => forall_congr' fun k' => ?_
    tauto
  rw [hset]
  refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun N => MeasurableSet.iInter
    fun n => MeasurableSet.iInter fun k => MeasurableSet.iInter fun n' => MeasurableSet.iInter
    fun k' => ?_
  refine ((measurableSet_lt measurable_snd measurable_const).union
    (measurableSet_lt measurable_snd measurable_const)).union ?_
  by_cases hp : |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1)
  · have e : {p : PCode × ℝ≥0 | |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1) →
        |p.1 n k - p.1 n' k'| ≤ 1 / (m + 1)} = {p : PCode × ℝ≥0 | |p.1 n k - p.1 n' k'| ≤ 1 / (m + 1)} := by
      ext p
      exact ⟨fun h => h hp, fun h _ => h⟩
    rw [e]
    exact measurableSet_le (continuous_abs.measurable.comp
      (((measurable_code n k).comp measurable_fst).sub ((measurable_code n' k').comp measurable_fst)))
      measurable_const
  · have e : {p : PCode × ℝ≥0 | |(dyad n k : ℝ) - dyad n' k'| < 1 / (N + 1) →
        |p.1 n k - p.1 n' k'| ≤ 1 / (m + 1)} = univ := by
      ext p
      exact ⟨fun _ => trivial, fun _ h => absurd h hp⟩
    rw [e]
    exact MeasurableSet.univ

theorem measurableSet_goodCode : MeasurableSet {p : PCode × ℝ≥0∞ | GoodCode p.1 p.2} := by
  have hset : {p : PCode × ℝ≥0∞ | GoodCode p.1 p.2} =
      ({p : PCode × ℝ≥0∞ | p.2 = ⊤} ∩ ⋂ N : ℕ, {p : PCode × ℝ≥0∞ | UC p.1 N}) ∪
        ({p : PCode × ℝ≥0∞ | p.2 ≠ ⊤} ∩ (fun p : PCode × ℝ≥0∞ => (p.1, p.2.toNNReal)) ⁻¹'
          {q : PCode × ℝ≥0 | UC q.1 q.2}) := by
    ext p
    simp only [mem_ofPred_eq, goodCode_iff, mem_union, mem_inter_iff, mem_iInter, mem_preimage]
  rw [hset]
  refine ((measurableSet_eq_fun measurable_snd measurable_const).inter (MeasurableSet.iInter fun N : ℕ =>
    measurable_fst (measurableSet_UC (N : ℝ≥0)))).union
    (((measurableSet_eq_fun measurable_snd measurable_const).compl).inter ?_)
  exact (measurable_fst.prodMk (ENNReal.measurable_toNNReal.comp measurable_snd)) measurableSet_UC_prod

theorem GoodCode.continuousOn {a : PCode} {U : ℝ≥0∞} (h : GoodCode a U) :
    ContinuousOn (dec a) {t | (t : ℝ≥0∞) ≤ U} := by
  intro t ht
  by_cases hU : U = ⊤
  · have hc := (h (t + 1) (by simp [hU])).continuousOn
    have hnhds : Iic (t + 1) ∈ 𝓝 t := Iic_mem_nhds (lt_add_one t)
    exact ((hc.continuousAt hnhds)).continuousWithinAt
  · have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ U} = Iic U.toNNReal := by
      ext t
      simp only [mem_ofPred_eq, mem_Iic]
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hU]
    rw [hset] at ht ⊢
    exact (h _ ENNReal.coe_toNNReal_le_self).continuousOn t ht

/-- A real path continuous on `[0, U]` has a good code. -/
theorem goodCode_enc {f : ℝ≥0 → ℝ} {U : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) ≤ U}) :
    GoodCode (enc f) U := fun T hT =>
  uc_enc (hf.mono fun t (ht : t ≤ T) => (ENNReal.coe_le_coe.2 ht).trans hT)

theorem dec_enc_of_continuousOn {f : ℝ≥0 → ℝ} {U : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) ≤ U})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ U) : dec (enc f) t = f t :=
  dec_enc ((hf t ht).mono fun s (hs : s ≤ t) => (ENNReal.coe_le_coe.2 hs).trans ht)

/-- The complex path of a pair of real codes with a lifetime: the decoded path when both codes are good, `0`
otherwise. -/
def decPath (p : (PCode × PCode) × ℝ≥0∞) (t : ℝ≥0) : ℂ :=
  open Classical in
  if GoodCode p.1.1 p.2 ∧ GoodCode p.1.2 p.2 then (dec p.1.1 t : ℂ) + (dec p.1.2 t : ℂ) * Complex.I else 0

theorem measurable_decPath (t : ℝ≥0) : Measurable fun p : (PCode × PCode) × ℝ≥0∞ => decPath p t := by
  have hG : MeasurableSet {p : (PCode × PCode) × ℝ≥0∞ | GoodCode p.1.1 p.2 ∧ GoodCode p.1.2 p.2} :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd measurableSet_goodCode).inter
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd measurableSet_goodCode)
  have hd : ∀ (g : (PCode × PCode) × ℝ≥0∞ → PCode), Measurable g →
      Measurable fun p => dec (g p) t := fun g hg =>
    measurable_dec.comp (hg.prodMk measurable_const)
  unfold decPath
  refine Measurable.ite hG ?_ measurable_const
  exact (Complex.measurable_ofReal.comp (hd _ (measurable_fst.comp measurable_fst))).add
    ((Complex.measurable_ofReal.comp (hd _ (measurable_snd.comp measurable_fst))).mul_const _)

theorem continuousOn_decPath (p : (PCode × PCode) × ℝ≥0∞) :
    ContinuousOn (decPath p) {t | (t : ℝ≥0∞) ≤ p.2} := by
  unfold decPath
  split_ifs with h
  · exact (Complex.continuous_ofReal.comp_continuousOn h.1.continuousOn).add
      ((Complex.continuous_ofReal.comp_continuousOn h.2.continuousOn).mul continuousOn_const)
  · exact continuousOn_const

/-- The code of a complex path with a lifetime. -/
def encPath (f : ℝ≥0 → ℂ) (U : ℝ≥0∞) : (PCode × PCode) × ℝ≥0∞ :=
  ((enc fun t => (f t).re, enc fun t => (f t).im), U)

theorem decPath_encPath {f : ℝ≥0 → ℂ} {U : ℝ≥0∞} (hf : ContinuousOn f {t | (t : ℝ≥0∞) ≤ U})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ U) : decPath (encPath f U) t = f t := by
  have hre : ContinuousOn (fun t => (f t).re) {t | (t : ℝ≥0∞) ≤ U} :=
    Complex.continuous_re.comp_continuousOn hf
  have him : ContinuousOn (fun t => (f t).im) {t | (t : ℝ≥0∞) ≤ U} :=
    Complex.continuous_im.comp_continuousOn hf
  simp only [decPath, encPath, goodCode_enc hre, goodCode_enc him, and_self, ↓reduceIte,
    dec_enc_of_continuousOn hre ht, dec_enc_of_continuousOn him ht]
  exact Complex.re_add_im (f t)

theorem measurable_encPath {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ≥0 → ℂ}
    (hf : ∀ t, Measurable fun ω => f ω t) {U : Ω → ℝ≥0∞} (hU : Measurable U) :
    Measurable fun ω => encPath (f ω) (U ω) := by
  have hc : ∀ g : ℂ → ℝ, Measurable g → Measurable fun ω => enc (fun t => g (f ω t)) :=
    fun g hg => measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => hg.comp (hf (dyad n k))
  exact ((hc _ Complex.measurable_re).prodMk (hc _ Complex.measurable_im)).prodMk hU

/-! ### The restart space -/

/-- **The canonical restart space**: the chart field and, for each continuation, a coded path with its lifetime. -/
abbrev RestartSpace : Type :=
  LQGMetric.DistOn upperHalfPlaneOpens × ((PCode × PCode) × ℝ≥0∞) × ((PCode × PCode) × ℝ≥0∞)

instance : StandardBorelSpace ((PCode × PCode) × ℝ≥0∞) := StandardBorelSpace.prod

instance : StandardBorelSpace (((PCode × PCode) × ℝ≥0∞) × ((PCode × PCode) × ℝ≥0∞)) :=
  StandardBorelSpace.prod

/-- The restart space is standard Borel (a finite product of standard Borel spaces), as the regular conditional
law of the restart variable needs. -/
instance : StandardBorelSpace RestartSpace := StandardBorelSpace.prod

namespace RestartSpace

/-- The chart field coordinate. -/
def field (s : RestartSpace) : LQGMetric.DistOn upperHalfPlaneOpens := s.1

/-- The first continuation (decoded). -/
def path₁ (s : RestartSpace) : ℝ≥0 → ℂ := decPath s.2.1

/-- The second continuation (decoded). -/
def path₂ (s : RestartSpace) : ℝ≥0 → ℂ := decPath s.2.2

/-- The lifetime of the first continuation. -/
def life₁ (s : RestartSpace) : ℝ≥0∞ := s.2.1.2

/-- The lifetime of the second continuation. -/
def life₂ (s : RestartSpace) : ℝ≥0∞ := s.2.2.2

/-- The code of a field and two paths with lifetimes. -/
def mk' (h : LQGMetric.DistOn upperHalfPlaneOpens) (f₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞) (f₂ : ℝ≥0 → ℂ)
    (U₂ : ℝ≥0∞) : RestartSpace :=
  (h, encPath f₁ U₁, encPath f₂ U₂)

theorem field_mk' (h : LQGMetric.DistOn upperHalfPlaneOpens) (f₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞)
    (f₂ : ℝ≥0 → ℂ) (U₂ : ℝ≥0∞) : (mk' h f₁ U₁ f₂ U₂).field = h := rfl

theorem life₁_mk' (h : LQGMetric.DistOn upperHalfPlaneOpens) (f₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞)
    (f₂ : ℝ≥0 → ℂ) (U₂ : ℝ≥0∞) : (mk' h f₁ U₁ f₂ U₂).life₁ = U₁ := rfl

theorem life₂_mk' (h : LQGMetric.DistOn upperHalfPlaneOpens) (f₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞)
    (f₂ : ℝ≥0 → ℂ) (U₂ : ℝ≥0∞) : (mk' h f₁ U₁ f₂ U₂).life₂ = U₂ := rfl

theorem path₁_mk' (h : LQGMetric.DistOn upperHalfPlaneOpens) {f₁ : ℝ≥0 → ℂ} {U₁ : ℝ≥0∞}
    (hf₁ : ContinuousOn f₁ {t | (t : ℝ≥0∞) ≤ U₁}) (f₂ : ℝ≥0 → ℂ) (U₂ : ℝ≥0∞) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ U₁) : (mk' h f₁ U₁ f₂ U₂).path₁ t = f₁ t :=
  decPath_encPath hf₁ ht

theorem path₂_mk' (h : LQGMetric.DistOn upperHalfPlaneOpens) (f₁ : ℝ≥0 → ℂ) (U₁ : ℝ≥0∞)
    {f₂ : ℝ≥0 → ℂ} {U₂ : ℝ≥0∞} (hf₂ : ContinuousOn f₂ {t | (t : ℝ≥0∞) ≤ U₂}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ U₂) : (mk' h f₁ U₁ f₂ U₂).path₂ t = f₂ t :=
  decPath_encPath hf₂ ht

/-- The code map is measurable. -/
theorem measurable_mk' {Ω : Type*} [MeasurableSpace Ω] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : Measurable h) {f₁ f₂ : Ω → ℝ≥0 → ℂ} (hf₁ : ∀ t, Measurable fun ω => f₁ ω t)
    (hf₂ : ∀ t, Measurable fun ω => f₂ ω t) {U₁ U₂ : Ω → ℝ≥0∞} (hU₁ : Measurable U₁)
    (hU₂ : Measurable U₂) : Measurable fun ω => mk' (h ω) (f₁ ω) (U₁ ω) (f₂ ω) (U₂ ω) :=
  hh.prodMk ((measurable_encPath hf₁ hU₁).prodMk (measurable_encPath hf₂ hU₂))

end RestartSpace

/-- **The coordinates of the canonical restart space are restart coordinates** (at every point). -/
theorem isRestartCoordinates_restartSpace :
    IsRestartCoordinates RestartSpace.field RestartSpace.path₁ RestartSpace.path₂ RestartSpace.life₁
      RestartSpace.life₂ :=
  ⟨measurable_fst, measurable_snd.fst.snd, measurable_snd.snd.snd,
    fun t => (measurable_decPath t).comp measurable_snd.fst,
    fun t => (measurable_decPath t).comp measurable_snd.snd,
    fun s => continuousOn_decPath s.2.1, fun s => continuousOn_decPath s.2.2⟩

end Restart

end InteractingSLE
