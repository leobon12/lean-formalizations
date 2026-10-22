import HigherDimLQGMetric.Topology.NonSepHandshake

/-!
# Codimension-two nonseparation (D-NS), part 2: Mayer–Vietoris for path components (NS-3) and
bisection

Packet M4 (ruling M9). Source: planning audit `planning/audits/MA1-sections-1-4.md`, Details (a)
**A15**, steps NS-3 and NS-5 (bisection).

* `LoopsContractibleIn W`: every loop in `W` is freely null-homotopic in `W`, in the cylinder form
  used by NS-1 (a map `H : [0,1]² → W` with `H (s, 0) = ℓ s`, `H (0, t) = H (1, t)` and `H (·, 1)`
  constant).
* `joinedIn_inter_of_joinedIn` (**NS-3**): if `G₁, G₂` are open, every loop in `G₁ ∪ G₂` is
  contractible there, and `x, y ∈ G₁ ∩ G₂` are joined in `G₁` and in `G₂`, then they are joined in
  `G₁ ∩ G₂`. Proof: run a path in `G₁` from `x` to `y` on `[0, 1/2]` and a path in `G₂` back on
  `[1/2, 1]`; NS-1 (`joinedIn_inter_of_cylinder`) applied to a null-homotopy of this loop, with the
  top colour given by the constant top value.
* `bisection_false`: the nested-interval principle used in NS-5: a property `P a b` of intervals
  that holds on `[a, b]`, is inherited by one of the two halves, and fails on all short intervals
  around each point, cannot exist.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric.Topology

open Set unitInterval

/-- Every loop in `W` is freely null-homotopic in `W`, in the cylinder form used by NS-1: there is
`H : [0,1]² → W` with `H (s, 0) = ℓ s`, `H (0, t) = H (1, t)` and `H (·, 1)` constant. -/
def LoopsContractibleIn {Y : Type*} [TopologicalSpace Y] (W : Set Y) : Prop :=
  ∀ ℓ : C(I, Y), (∀ t, ℓ t ∈ W) → ℓ 0 = ℓ 1 →
    ∃ H : C(I × I, Y), (∀ q, H q ∈ W) ∧ (∀ s, H (s, 0) = ℓ s) ∧ (∀ t, H (0, t) = H (1, t)) ∧
      ∃ c : Y, ∀ s, H (s, 1) = c

lemma LoopsContractibleIn.congr {Y : Type*} [TopologicalSpace Y] {W W' : Set Y}
    (h : LoopsContractibleIn W) (hW : W = W') : LoopsContractibleIn W' := hW ▸ h

/-- **NS-3 (Mayer–Vietoris for path components).** If `G₁, G₂` are open, every loop in `G₁ ∪ G₂`
is null-homotopic there, and `x, y ∈ G₁ ∩ G₂` are joined by a path in `G₁` and by a path in `G₂`,
then they are joined by a path in `G₁ ∩ G₂`. -/
theorem joinedIn_inter_of_joinedIn {Y : Type*} [TopologicalSpace Y] {G₁ G₂ : Set Y}
    (h₁ : IsOpen G₁) (h₂ : IsOpen G₂) (hW : LoopsContractibleIn (G₁ ∪ G₂)) {x y : Y}
    (hy : y ∈ G₁ ∩ G₂) (hxy₁ : JoinedIn G₁ x y) (hxy₂ : JoinedIn G₂ x y) :
    JoinedIn (G₁ ∩ G₂) x y := by
  obtain ⟨γ₁, hγ₁⟩ := hxy₁
  obtain ⟨γ₂, hγ₂⟩ := hxy₂
  set γ : Path x x := γ₁.trans γ₂.symm with hγ
  -- the loop runs in `G₁` on `[0, 1/2]` and in `G₂` on `[1/2, 1]`
  have hleft : ∀ s : I, (s : ℝ) ≤ 1 / 2 → γ s ∈ G₁ := by
    intro s hs
    rw [hγ, Path.trans_apply]
    simp only [hs, ↓reduceDIte]
    exact hγ₁ _
  have hright : ∀ s : I, 1 / 2 ≤ (s : ℝ) → γ s ∈ G₂ := by
    intro s hs
    rw [hγ, Path.trans_apply]
    split_ifs with h
    · have hs' : (s : ℝ) = 1 / 2 := le_antisymm h hs
      have h1 : (⟨2 * (s : ℝ), by rw [hs']; norm_num, by rw [hs']; norm_num⟩ : I) = 1 := by
        apply Subtype.ext
        simp only [hs', Set.Icc.coe_one]
        norm_num
      simp only [h1, Path.target]
      exact hy.2
    · rw [Path.symm_apply]
      exact hγ₂ _
  have hmid : γ halfI = y := by
    have hh : ((halfI : I) : ℝ) ≤ 1 / 2 := by simp [halfI]
    rw [hγ, Path.trans_apply]
    simp only [hh, ↓reduceDIte]
    have h1 : (⟨2 * ((halfI : I) : ℝ), by simp [halfI], by simp [halfI]⟩ : I) = 1 := by
      apply Subtype.ext
      simp [halfI]
    rw [h1, Path.target]
  have hℓ : ∀ t, γ.toContinuousMap t ∈ G₁ ∪ G₂ := by
    intro t
    rcases le_total (t : ℝ) (1 / 2) with h | h
    · exact Or.inl (hleft t h)
    · exact Or.inr (hright t h)
  obtain ⟨H, hHW, hH0, hside, c, hc⟩ :=
    hW γ.toContinuousMap hℓ (by simp only [Path.coe_toContinuousMap, Path.source, Path.target])
  have hL : ∀ s : I, (s : ℝ) ≤ 1 / 2 → H (s, 0) ∈ G₁ := fun s hs => by
    rw [hH0]; exact hleft s hs
  have hR : ∀ s : I, 1 / 2 ≤ (s : ℝ) → H (s, 0) ∈ G₂ := fun s hs => by
    rw [hH0]; exact hright s hs
  have hcW : c ∈ G₁ ∪ G₂ := by rw [← hc 0]; exact hHW _
  have key : JoinedIn (G₁ ∩ G₂) (H (halfI, 0)) (H (0, 0)) := by
    rcases hcW with hc1 | hc2
    · exact joinedIn_inter_of_cylinder h₁ h₂ H hHW hside true
        (fun s => by rw [hc s]; exact hc1) hL hR
    · exact joinedIn_inter_of_cylinder h₁ h₂ H hHW hside false
        (fun s => by rw [hc s]; exact hc2) hL hR
  rw [hH0, hH0] at key
  simp only [Path.coe_toContinuousMap, hmid, Path.source] at key
  exact key.symm

/-- **Bisection.** Let `P a' b'` be a property of subintervals of `[a, b]` that holds for
`[a, b]`, passes to one of the two halves of any subinterval where it holds, and fails for all
sufficiently short subintervals containing any given point of `[a, b]`. Then `False`. -/
theorem bisection_false (P : ℝ → ℝ → Prop) {a b : ℝ} (hab : a ≤ b) (hP : P a b)
    (hsplit : ∀ a' b', a ≤ a' → a' ≤ b' → b' ≤ b → P a' b' →
      P a' ((a' + b') / 2) ∨ P ((a' + b') / 2) b')
    (hloc : ∀ t ∈ Icc a b, ∃ η > 0, ∀ a' b', a' ≤ t → t ≤ b' → b' - a' < η → ¬ P a' b') :
    False := by
  classical
  -- the nested intervals
  let step : ℝ × ℝ → ℝ × ℝ := fun q =>
    if P q.1 ((q.1 + q.2) / 2) then (q.1, (q.1 + q.2) / 2) else ((q.1 + q.2) / 2, q.2)
  let seq : ℕ → ℝ × ℝ := fun n => step^[n] (a, b)
  have hseq_succ : ∀ n, seq (n + 1) = step (seq n) := fun n =>
    Function.iterate_succ_apply' step n (a, b)
  have inv : ∀ n, a ≤ (seq n).1 ∧ (seq n).1 ≤ (seq n).2 ∧ (seq n).2 ≤ b ∧
      (seq n).2 - (seq n).1 = (b - a) / 2 ^ n ∧ P (seq n).1 (seq n).2 := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, hab, le_rfl, by simp [seq], hP⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih
      rw [hseq_succ]
      simp only [step]
      split_ifs with h
      · refine ⟨h1, by linarith, by linarith, ?_, h⟩
        rw [pow_succ, ← div_div, ← h4]; ring
      · refine ⟨by linarith, by linarith, h3, ?_, ?_⟩
        · rw [pow_succ, ← div_div, ← h4]; ring
        · exact (hsplit _ _ h1 h2 h3 h5).resolve_left h
  have hmono : ∀ n, (seq n).1 ≤ (seq (n + 1)).1 ∧ (seq (n + 1)).2 ≤ (seq n).2 := by
    intro n
    obtain ⟨-, h2, -, -, -⟩ := inv n
    rw [hseq_succ]
    simp only [step]
    split_ifs
    · exact ⟨le_rfl, by linarith⟩
    · exact ⟨by linarith, le_rfl⟩
  have hlow : Monotone fun n => (seq n).1 := monotone_nat_of_le_succ fun n => (hmono n).1
  have hupp : Antitone fun n => (seq n).2 := antitone_nat_of_succ_le fun n => (hmono n).2
  have hle : ∀ m n, (seq m).1 ≤ (seq n).2 := by
    intro m n
    calc (seq m).1 ≤ (seq (max m n)).1 := hlow (le_max_left m n)
      _ ≤ (seq (max m n)).2 := (inv _).2.1
      _ ≤ (seq n).2 := hupp (le_max_right m n)
  have hbdd : BddAbove (range fun n => (seq n).1) := ⟨b, by
    rintro _ ⟨n, rfl⟩
    exact (inv n).2.1.trans (inv n).2.2.1⟩
  set t := ⨆ n, (seq n).1 with ht
  have htlow : ∀ n, (seq n).1 ≤ t := fun n => le_ciSup hbdd n
  have htupp : ∀ n, t ≤ (seq n).2 := fun n => ciSup_le fun m => hle m n
  have htab : t ∈ Icc a b := ⟨(inv 0).1.trans (htlow 0), (htupp 0).trans (inv 0).2.2.1⟩
  obtain ⟨η, hη, hηP⟩ := hloc t htab
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / η)
  have hlen : (seq n).2 - (seq n).1 < η := by
    rw [(inv n).2.2.2.1, div_lt_iff₀ (by positivity)]
    have h1 : b - a < η * n := by rwa [div_lt_iff₀ hη, mul_comm] at hn
    have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    nlinarith
  exact hηP _ _ (htlow n) (htupp n) hlen (inv n).2.2.2.2

end HigherDimLQGMetric.Topology

end
