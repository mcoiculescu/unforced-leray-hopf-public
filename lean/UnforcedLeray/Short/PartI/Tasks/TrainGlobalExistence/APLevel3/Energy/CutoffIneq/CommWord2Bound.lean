import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1_2_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel3.Energy.CutoffIneq.CommWord2Expand
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord

/-!
# Part I, `PartI:T04/10/1/2/1/13`, target `commWord2Bound_proof`: the commutator bound

Source of record: `the November 2 reference manuscript`, lines 285-288
(`[∂², u·∇]ω = ∂²u·∇ω + 2∂u·∇∂ω`). The Prop is `CommWord2Bound` in `Sub/PartI_T04_10_1_2_1.lean`.

Proof. `CommWord2Expand` writes each commutator `∂_{[a,a']}(b·∇h) - b·∇∂_{[a,a']}h` as six
products `wordComp w b k z * ∂_{w'} h z` (two of length 2 and four of length 1 on `b`, and
the matching derivatives of `h`). Coordinate word derivatives are bounded by operator norms of
the jets (`CylJetWord`), so each commutator is at most `2‖D²b‖‖Dh‖ + 4‖Db‖‖D²h‖` and
`|∂_{[a,a']}h| ≤ ‖D²h‖`. Each of the four words contributes at most
`4‖D²h‖(‖D²b‖‖Dh‖ + 2‖Db‖‖D²h‖)`, and `#wordsOfLength 2 = 4`.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Coordinate word derivatives are bounded by the jet norm (`CylJetWord`). -/
theorem cbw_word_le {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (w : List Bool) (z : Plane) :
    |B0151.derivWord w f z| ≤ ‖iteratedFDeriv ℝ w.length f z‖ :=
  (cylJetWord_proof f hf w.length z).1 w rfl

/-- The word derivative of a component is bounded by the jet norm of the vector field. -/
theorem cbw_comp_le {b : Plane → Vec} (hb : ContDiff ℝ ∞ b) (k : Fin 2) (w : List Bool)
    (z : Plane) :
    |wordComp w b k z| ≤ ‖iteratedFDeriv ℝ w.length b z‖ := by
  have hproj : ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
      simpa using PiLp.norm_apply_le x k)
  have hj : ((w.length : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hg : ContDiff ℝ ∞ (fun x => b x k) :=
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hb
  have hw := cbw_word_le hg w z
  have hcomp : ‖iteratedFDeriv ℝ w.length (fun x => b x k) z‖ ≤
      ‖iteratedFDeriv ℝ w.length b z‖ := by
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
      (f := b) (x := z) (n := w.length) hb.contDiffAt hj
    calc ‖iteratedFDeriv ℝ w.length (fun x => b x k) z‖
        = ‖iteratedFDeriv ℝ w.length
            ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ b) z‖ := rfl
      _ ≤ ‖(EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ *
            ‖iteratedFDeriv ℝ w.length b z‖ := h
      _ ≤ 1 * ‖iteratedFDeriv ℝ w.length b z‖ :=
            mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ w.length b z‖ := one_mul _
  exact hw.trans hcomp

theorem cbw_abs_mul_le {x y α β : ℝ} (hx : |x| ≤ α) (hy : |y| ≤ β) : |x * y| ≤ α * β := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

/-- Six products bounded in two groups: `B` for the three `wordComp` products of the
length-two word and `C` for the others. -/
theorem cbw_six_le {p1 p2 p3 p4 p5 p6 B C : ℝ}
    (h1 : |p1| ≤ B) (h2 : |p2| ≤ C) (h3 : |p3| ≤ C)
    (h4 : |p4| ≤ B) (h5 : |p5| ≤ C) (h6 : |p6| ≤ C) :
    |p1 + p2 + p3 + (p4 + p5 + p6)| ≤ 2 * B + 4 * C := by
  obtain ⟨h1l, h1u⟩ := abs_le.1 h1
  obtain ⟨h2l, h2u⟩ := abs_le.1 h2
  obtain ⟨h3l, h3u⟩ := abs_le.1 h3
  obtain ⟨h4l, h4u⟩ := abs_le.1 h4
  obtain ⟨h5l, h5u⟩ := abs_le.1 h5
  obtain ⟨h6l, h6u⟩ := abs_le.1 h6
  rw [abs_le]
  constructor <;> linarith

theorem cbw_mul_bound {X S a b c : ℝ} (hX : |X| ≤ a) (hS : |S| ≤ 2 * b + 4 * c) (ha : 0 ≤ a) :
    |2 * X * S| ≤ 4 * (a * (b + 2 * c)) := by
  rw [abs_mul, abs_mul, abs_two]
  have h2 : 2 * |X| ≤ 2 * a := by linarith
  have hb2 : 0 ≤ 2 * a := by linarith
  calc 2 * |X| * |S| ≤ (2 * a) * (2 * b + 4 * c) :=
        mul_le_mul h2 hS (abs_nonneg _) hb2
    _ = 4 * (a * (b + 2 * c)) := by ring

theorem cbw_mem_two {u : List Bool} (hu : u ∈ wordsOfLength 2) : ∃ a a' : Bool, u = [a, a'] := by
  unfold wordsOfLength at hu
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hu
  exact ⟨x 0, x 1, by simp [List.ofFn_succ]⟩

/-- One word `[a, a']` of the commutator sum, bounded by `4 ‖D²h‖ (‖D²b‖‖Dh‖ + 2‖Db‖‖D²h‖)`. -/
theorem cbw_word_term (b : Plane → Vec) (h : Plane → ℝ) (hb : ContDiff ℝ ∞ b)
    (hh : ContDiff ℝ ∞ h) (a a' : Bool) (z : Plane) :
    |2 * B0151.derivWord [a, a'] h z *
        (B0151.derivWord [a, a'] (scalarAdv b h) z - scalarAdv b (B0151.derivWord [a, a'] h) z)| ≤
      4 * (‖iteratedFDeriv ℝ 2 h z‖ * (‖iteratedFDeriv ℝ 2 b z‖ * ‖iteratedFDeriv ℝ 1 h z‖ +
        2 * (‖iteratedFDeriv ℝ 1 b z‖ * ‖iteratedFDeriv ℝ 2 h z‖))) := by
  have hE := commWord2Expand_proof b h hb hh a a' z
  rw [hE]
  have hX : |B0151.derivWord [a, a'] h z| ≤ ‖iteratedFDeriv ℝ 2 h z‖ :=
    cbw_word_le hh [a, a'] z
  have c0 : |wordComp [a, a'] b 0 z| ≤ ‖iteratedFDeriv ℝ 2 b z‖ := cbw_comp_le hb 0 [a, a'] z
  have c1 : |wordComp [a, a'] b 1 z| ≤ ‖iteratedFDeriv ℝ 2 b z‖ := cbw_comp_le hb 1 [a, a'] z
  have d0 : |wordComp [a] b 0 z| ≤ ‖iteratedFDeriv ℝ 1 b z‖ := cbw_comp_le hb 0 [a] z
  have d1 : |wordComp [a] b 1 z| ≤ ‖iteratedFDeriv ℝ 1 b z‖ := cbw_comp_le hb 1 [a] z
  have e0 : |wordComp [a'] b 0 z| ≤ ‖iteratedFDeriv ℝ 1 b z‖ := cbw_comp_le hb 0 [a'] z
  have e1 : |wordComp [a'] b 1 z| ≤ ‖iteratedFDeriv ℝ 1 b z‖ := cbw_comp_le hb 1 [a'] z
  have h1t : |B0151.derivWord [true] h z| ≤ ‖iteratedFDeriv ℝ 1 h z‖ := cbw_word_le hh [true] z
  have h1f : |B0151.derivWord [false] h z| ≤ ‖iteratedFDeriv ℝ 1 h z‖ := cbw_word_le hh [false] z
  have h2a : |B0151.derivWord [a', true] h z| ≤ ‖iteratedFDeriv ℝ 2 h z‖ :=
    cbw_word_le hh [a', true] z
  have h2b : |B0151.derivWord [a, true] h z| ≤ ‖iteratedFDeriv ℝ 2 h z‖ :=
    cbw_word_le hh [a, true] z
  have h2c : |B0151.derivWord [a', false] h z| ≤ ‖iteratedFDeriv ℝ 2 h z‖ :=
    cbw_word_le hh [a', false] z
  have h2d : |B0151.derivWord [a, false] h z| ≤ ‖iteratedFDeriv ℝ 2 h z‖ :=
    cbw_word_le hh [a, false] z
  exact cbw_mul_bound hX
    (cbw_six_le (cbw_abs_mul_le c0 h1t) (cbw_abs_mul_le d0 h2a) (cbw_abs_mul_le e0 h2b)
      (cbw_abs_mul_le c1 h1f) (cbw_abs_mul_le d1 h2c) (cbw_abs_mul_le e1 h2d))
    (norm_nonneg _)

/-- **Target** `commWord2Bound_proof`: the pointwise commutator bound (`CommWord2Bound`,
`Sub/PartI_T04_10_1_2_1.lean`, lines 285-288). -/
theorem commWord2Bound_proof : CommWord2Bound := by
  intro b h hb hh z
  have hterm : ∀ u ∈ wordsOfLength 2,
      |2 * B0151.derivWord u h z *
          (B0151.derivWord u (scalarAdv b h) z - scalarAdv b (B0151.derivWord u h) z)| ≤
        4 * (‖iteratedFDeriv ℝ 2 h z‖ * (‖iteratedFDeriv ℝ 2 b z‖ * ‖iteratedFDeriv ℝ 1 h z‖ +
          2 * (‖iteratedFDeriv ℝ 1 b z‖ * ‖iteratedFDeriv ℝ 2 h z‖))) := by
    intro u hu
    obtain ⟨a, a', rfl⟩ := cbw_mem_two hu
    exact cbw_word_term b h hb hh a a' z
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans_eq ?_)
  rw [Finset.sum_const, card_wordsOfLength, nsmul_eq_mul]
  push_cast
  ring

end UnforcedLeray.Short.PartI
