import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- Sums of a mapped list split additively. -/
theorem list_sum_add_aux {α : Type*} (S : List α) (X Y : α → ℝ) :
    (S.map (fun s => X s + Y s)).sum = (S.map X).sum + (S.map Y).sum := by
  induction S with
  | nil => simp
  | cons s S ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- Differentiability of the list sum of products of spatial-word fields. -/
theorem tjLeib_diff_aux (f g : ℝ × (ℝ × ℝ) → ℝ) (S : List (List (Fin 3) × List (Fin 3)))
    (hS : ∀ s ∈ S, ContDiffOn ℝ ∞ (tjW s.1 f) tjU ∧ ContDiffOn ℝ ∞ (tjW s.2 g) tjU)
    (p : ℝ × (ℝ × ℝ)) (hp : p ∈ tjU) :
    DifferentiableWithinAt ℝ (fun q => (S.map (fun s => tjW s.1 f q * tjW s.2 g q)).sum) tjU p := by
  induction S with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact differentiableWithinAt_const 0
  | cons s S ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : DifferentiableWithinAt ℝ (fun q => tjW s.1 f q * tjW s.2 g q) tjU p :=
      ((hS s (by simp)).1.differentiableOn (by simp) p hp).mul
        ((hS s (by simp)).2.differentiableOn (by simp) p hp)
    have h2 := ih (fun s' hs' => hS s' (List.mem_cons_of_mem _ hs'))
    exact h1.add h2

/-- The derivative of a list sum of products of spatial-word fields, along a direction. -/
theorem tjLeib_sum_aux (f g : ℝ × (ℝ × ℝ) → ℝ) (S : List (List (Fin 3) × List (Fin 3)))
    (hS : ∀ s ∈ S, ContDiffOn ℝ ∞ (tjW s.1 f) tjU ∧ ContDiffOn ℝ ∞ (tjW s.2 g) tjU)
    (p : ℝ × (ℝ × ℝ)) (hp : p ∈ tjU) (v : ℝ × (ℝ × ℝ)) :
    fderivWithin ℝ (fun q => (S.map (fun s => tjW s.1 f q * tjW s.2 g q)).sum) tjU p v =
      (S.map (fun s => tjW s.1 f p * fderivWithin ℝ (tjW s.2 g) tjU p v +
        tjW s.2 g p * fderivWithin ℝ (tjW s.1 f) tjU p v)).sum := by
  induction S with
  | nil =>
    simp [fderivWithin_const_apply]
  | cons s S ih =>
    have hs := hS s (by simp)
    have hpr : DifferentiableWithinAt ℝ (fun q => tjW s.1 f q * tjW s.2 g q) tjU p :=
      (hs.1.differentiableOn (by simp) p hp).mul (hs.2.differentiableOn (by simp) p hp)
    have htail := tjLeib_diff_aux f g S (fun s' hs' => hS s' (List.mem_cons_of_mem _ hs')) p hp
    have hadd : fderivWithin ℝ
        (fun q => tjW s.1 f q * tjW s.2 g q +
          (S.map (fun s => tjW s.1 f q * tjW s.2 g q)).sum) tjU p =
        fderivWithin ℝ (fun q => tjW s.1 f q * tjW s.2 g q) tjU p +
        fderivWithin ℝ (fun q => (S.map (fun s => tjW s.1 f q * tjW s.2 g q)).sum) tjU p :=
      fderivWithin_add (uniqueDiffOn_tjU p hp) hpr htail
    have hmul := fderivWithin_fun_mul (uniqueDiffOn_tjU p hp)
      ((hs.1.differentiableOn (by simp)) p hp) ((hs.2.differentiableOn (by simp)) p hp)
    have ih' := ih (fun s' hs' => hS s' (List.mem_cons_of_mem _ hs'))
    simp only [List.map_cons, List.sum_cons]
    rw [hadd, add_apply, hmul, ih']
    simp only [add_apply, smul_apply, smul_eq_mul]

/-- **The Leibniz rule for words** (calculus): `∂_L(fg) = Σ_{splittings (L₁, L₂) of L} ∂_{L₁}f ∂_{L₂}g`
on `tjU`, for `f, g` `C^∞` on `tjU`. (Induction on `L`: `fderivWithin_mul`, `fderivWithin_sum` /
induction on the list sum, `fderivWithin_congr` with the inductive identity on `tjU`.) -/
theorem tjWLeibniz : TjWLeibniz := by
  intro f g hf hg L
  induction L with
  | nil =>
    intro p _
    simp [tjSplits]
  | cons a L ih =>
    intro p hp
    have e : fderivWithin ℝ (tjW L (fun q => f q * g q)) tjU p =
        fderivWithin ℝ (fun q => ((tjSplits L).map (fun s => tjW s.1 f q * tjW s.2 g q)).sum)
          tjU p :=
      fderivWithin_congr (fun q hq => ih q hq) (ih p hp)
    have hS : ∀ s ∈ tjSplits L, ContDiffOn ℝ ∞ (tjW s.1 f) tjU ∧
        ContDiffOn ℝ ∞ (tjW s.2 g) tjU :=
      fun s _ => ⟨tjW_contDiffOn hf _, tjW_contDiffOn hg _⟩
    have hD : ∀ (L' : List (Fin 3)) (h : ℝ × (ℝ × ℝ) → ℝ),
        fderivWithin ℝ (tjW L' h) tjU p (stDir a) = tjW (a :: L') h p := fun _ _ => rfl
    simp only [tjW_cons]
    rw [e, tjLeib_sum_aux f g (tjSplits L) hS p hp (stDir a)]
    simp only [hD, tjSplits, List.map_append, List.sum_append, List.map_map]
    rw [← list_sum_add_aux]
    congr 1
    apply List.map_congr_left
    intro s _
    simp only [Function.comp_apply]
    ring

end UnforcedLeray.Short.IIIa
