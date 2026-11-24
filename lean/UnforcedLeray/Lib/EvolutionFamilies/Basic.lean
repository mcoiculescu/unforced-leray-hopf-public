import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Evolution families on a compact time interval and block composition (INF08 T8.1)


§5, Layer 3, target T8.1; frozen interface of decision D17 (`scoping/README.md` §3).

* `EvolutionFamily X a b`: a two-parameter family `U t s` of bounded operators on a complex
  normed space, defined for `a ≤ s ≤ t ≤ b`, with `U t t = 1`, the evolution law
  `U t r ∘ U r s = U t s`, joint strong continuity on the triangle `a ≤ s ≤ t ≤ b`, and a uniform
  bound there. Values of `U t s` off the triangle carry no meaning.
* `BoundedPert X a b`: a strongly measurable, uniformly bounded interaction `A r`
  (`paper/main.tex`, line 1594: "strongly measurable, uniformly bounded interactions";
  blueprint B0104, B0106). Strong measurability is the manuscript's hypothesis and is weaker
  than the operator-norm measurability proposed in bypass BP6; `BoundedPert.ofAEStronglyMeasurable`
  builds a `BoundedPert` from operator-norm measurability.
* `EvolutionFamily.norm_le_of_blocks`: the block composition lemma (`paper/main.tex`,
  lines 6224-6233, blueprint B0322, used for B0110, B0323, B0348): if every full block has norm
  at most `1/2` and short blocks are bounded by `M`, then
  `‖U t s‖ ≤ 2 M e^{-(log 2)(t-s)/B}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Evolution

/-- The closed time triangle `{(s,t) : a ≤ s ≤ t ≤ b}`; a point is `p = (s, t)`. -/
def triangle (a b : ℝ) : Set (ℝ × ℝ) := {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}

theorem mem_triangle {a b : ℝ} {p : ℝ × ℝ} : p ∈ triangle a b ↔ a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b :=
  Iff.rfl

theorem isClosed_triangle (a b : ℝ) : IsClosed (triangle a b) := by
  have h1 : IsClosed {p : ℝ × ℝ | a ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} := isClosed_le continuous_fst continuous_snd
  have h3 : IsClosed {p : ℝ × ℝ | p.2 ≤ b} := isClosed_le continuous_snd continuous_const
  exact h1.inter (h2.inter h3)

/-- **Evolution family on `[a,b]`** (INF08 T8.1; `paper/main.tex`, lines 1586-1601 and
6224-6233; blueprint B0104, B0110, B0322). `U t s` is the evolution from time `s` to time `t`
for `a ≤ s ≤ t ≤ b`. -/
structure EvolutionFamily (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] (a b : ℝ) where
  /-- The evolution operator `U(t,s)`, from time `s` to time `t`. -/
  U : ℝ → ℝ → X →L[ℂ] X
  /-- `U(t,t) = 1`. -/
  U_diag : ∀ t ∈ Set.Icc a b, U t t = 1
  /-- Evolution law `U(t,r) U(r,s) = U(t,s)` for `a ≤ s ≤ r ≤ t ≤ b`. -/
  U_comp : ∀ ⦃s r t⦄, a ≤ s → s ≤ r → r ≤ t → t ≤ b → U t r ∘L U r s = U t s
  /-- Joint strong continuity on the triangle `a ≤ s ≤ t ≤ b` (the point is `p = (s,t)`). -/
  U_cont : ∀ x, ContinuousOn (fun p : ℝ × ℝ => U p.2 p.1 x) {p | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}
  /-- Uniform bound on the triangle. -/
  U_bdd : ∃ M, ∀ s t, a ≤ s → s ≤ t → t ≤ b → ‖U t s‖ ≤ M

/-- **Bounded interaction on `[a,b]`** (INF08 T8.2; `paper/main.tex`, line 1594, "strongly
measurable, uniformly bounded interactions"; blueprint B0104, B0106). -/
structure BoundedPert (X : Type*) [NormedAddCommGroup X] [NormedSpace ℂ X] (a b : ℝ) where
  /-- The interaction `A(r)`. -/
  A : ℝ → X →L[ℂ] X
  /-- Strong measurability on `[a,b]`: `r ↦ A r x` is a.e. strongly measurable for every `x`. -/
  meas : ∀ x, AEStronglyMeasurable (fun r => A r x) (volume.restrict (Set.Icc a b))
  /-- Uniform bound on `[a,b]`. -/
  bdd : ∃ C, ∀ r ∈ Set.Icc a b, ‖A r‖ ≤ C

namespace BoundedPert

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ}

/-- A `BoundedPert` from operator-norm measurability (bypass BP6 of the scoping note). -/
def ofAEStronglyMeasurable (A : ℝ → X →L[ℂ] X)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hb : ∃ C, ∀ r ∈ Set.Icc a b, ‖A r‖ ≤ C) : BoundedPert X a b where
  A := A
  meas x := (ContinuousLinearMap.apply ℂ X x).continuous.comp_aestronglyMeasurable hA
  bdd := hb

/-- A bound for the interaction, `C = max C₀ 0`. -/
def C (A : BoundedPert X a b) : ℝ := max (Classical.choose A.bdd) 0

theorem C_nonneg (A : BoundedPert X a b) : 0 ≤ A.C := le_max_right _ _

theorem norm_le (A : BoundedPert X a b) {r : ℝ} (hr : r ∈ Set.Icc a b) : ‖A.A r‖ ≤ A.C :=
  (Classical.choose_spec A.bdd r hr).trans (le_max_left _ _)

/-- The zero interaction. -/
def zero : BoundedPert X a b where
  A := fun _ => 0
  meas _ := aestronglyMeasurable_const
  bdd := ⟨0, fun _ _ => by simp⟩

end BoundedPert

namespace EvolutionFamily

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ}
  (E : EvolutionFamily X a b)

/-- A bound for the family on the triangle, `M = max M₀ 0`. -/
def M : ℝ := max (Classical.choose E.U_bdd) 0

theorem M_nonneg : 0 ≤ E.M := le_max_right _ _

theorem norm_le {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) : ‖E.U t s‖ ≤ E.M :=
  (Classical.choose_spec E.U_bdd s t hs hst ht).trans (le_max_left _ _)

theorem norm_apply_le {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : X) :
    ‖E.U t s x‖ ≤ E.M * ‖x‖ :=
  ((E.U t s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (E.norm_le hs hst ht) (norm_nonneg _))

theorem continuousOn_triangle (x : X) :
    ContinuousOn (fun p : ℝ × ℝ => E.U p.2 p.1 x) (triangle a b) :=
  E.U_cont x

theorem apply_diag {t : ℝ} (ht : t ∈ Set.Icc a b) (x : X) : E.U t t x = x := by
  simp [E.U_diag t ht]

theorem apply_comp {s r t : ℝ} (hs : a ≤ s) (hsr : s ≤ r) (hrt : r ≤ t) (ht : t ≤ b) (x : X) :
    E.U t r (E.U r s x) = E.U t s x := by
  rw [← ContinuousLinearMap.comp_apply, E.U_comp hs hsr hrt ht]

/-- Strong continuity in the final time: `t ↦ U(t,s) x` is continuous on `[s,b]`. -/
theorem continuousOn_fst {s : ℝ} (hs : a ≤ s) (x : X) :
    ContinuousOn (fun t => E.U t s x) (Set.Icc s b) := by
  have h := (E.U_cont x).comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
    (fun t (ht : t ∈ Set.Icc s b) => (⟨hs, ht.1, ht.2⟩ : a ≤ s ∧ s ≤ t ∧ t ≤ b))
  exact h

/-- Strong continuity in the initial time: `s ↦ U(t,s) x` is continuous on `[a,t]`. -/
theorem continuousOn_snd {t : ℝ} (ht : t ≤ b) (x : X) :
    ContinuousOn (fun s => E.U t s x) (Set.Icc a t) := by
  have h := (E.U_cont x).comp (Continuous.continuousOn (continuous_id.prodMk continuous_const))
    (fun s (hs : s ∈ Set.Icc a t) => (⟨hs.1, hs.2, ht⟩ : a ≤ s ∧ s ≤ t ∧ t ≤ b))
  exact h

/-- **Block composition lemma** (INF08 T8.1; `paper/main.tex`, lines 6224-6233; blueprint
B0322, used in B0110, B0323, B0348). If every full block of length `B > 0` has
`‖U(s+B,s)‖ ≤ 1/2` and every block of length at most `B` has `‖U(t,s)‖ ≤ M`, then
`‖U(t,s)‖ ≤ 2 M e^{-(log 2)(t-s)/B}` for all `a ≤ s ≤ t ≤ b`. -/
theorem norm_le_of_blocks {B M : ℝ} (hB : 0 < B)
    (hfull : ∀ s, a ≤ s → s + B ≤ b → ‖E.U (s + B) s‖ ≤ 1 / 2)
    (hshort : ∀ s t, a ≤ s → s ≤ t → t ≤ min b (s + B) → ‖E.U t s‖ ≤ M) :
    ∀ s t, a ≤ s → s ≤ t → t ≤ b →
      ‖E.U t s‖ ≤ 2 * M * Real.exp (-(Real.log 2) * (t - s) / B) := by
  -- the bound on `n` full blocks plus a short one
  have key : ∀ n : ℕ, ∀ s t, a ≤ s → s + n * B ≤ t → t ≤ b → t ≤ s + (n + 1) * B →
      ‖E.U t s‖ ≤ M * (1 / 2) ^ n := by
    intro n
    induction n with
    | zero =>
      intro s t hs h1 h2 h3
      simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul, pow_zero, mul_one] at h1 h3 ⊢
      exact hshort s t hs h1 (le_min h2 h3)
    | succ n ih =>
      intro s t hs h1 h2 h3
      push_cast at h1 h3
      have hB' : s + B ≤ t := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hsB : s + B ≤ b := hB'.trans h2
      have h := ih (s + B) t (by linarith) (by linarith) h2 (by linarith)
      rw [← E.U_comp hs (by linarith) hB' h2]
      calc ‖(E.U t (s + B)).comp (E.U (s + B) s)‖
          ≤ ‖E.U t (s + B)‖ * ‖E.U (s + B) s‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (M * (1 / 2) ^ n) * (1 / 2) :=
          mul_le_mul h (hfull s hs hsB) (norm_nonneg _) ((norm_nonneg _).trans h)
        _ = M * (1 / 2) ^ (n + 1) := by ring
  intro s t hs hst ht
  have hM : 0 ≤ M := (norm_nonneg _).trans
    (hshort s s hs le_rfl (le_min (hst.trans ht) (by linarith)))
  set n := ⌊(t - s) / B⌋₊ with hn
  have hq : 0 ≤ (t - s) / B := div_nonneg (by linarith) hB.le
  have hn1 : (n : ℝ) ≤ (t - s) / B := Nat.floor_le hq
  have hn2 : (t - s) / B < n + 1 := Nat.lt_floor_add_one _
  have h := key n s t hs (by rw [le_div_iff₀ hB] at hn1; linarith) ht
    (by rw [div_lt_iff₀ hB] at hn2; linarith)
  refine h.trans ?_
  have hpow : (1 / 2 : ℝ) ^ n = Real.exp (-(Real.log 2) * n) := by
    rw [one_div, inv_pow, ← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
      ← Real.exp_neg, Real.log_exp]
    ring_nf
  rw [hpow, mul_comm 2 M, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hM
  have h2 : 2 * Real.exp (-(Real.log 2) * (t - s) / B) =
      Real.exp (Real.log 2 + -(Real.log 2) * (t - s) / B) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  rw [h2, Real.exp_le_exp]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : -(Real.log 2) * (t - s) / B = -(Real.log 2) * ((t - s) / B) := by ring
  rw [this]
  nlinarith

end EvolutionFamily

end UnforcedLeray.Evolution
