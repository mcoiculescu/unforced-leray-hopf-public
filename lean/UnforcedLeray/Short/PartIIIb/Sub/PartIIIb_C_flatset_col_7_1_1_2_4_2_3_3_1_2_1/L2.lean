import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_3_3_1_2_1
import UnforcedLeray.Lib.TrainB.P0W1

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

local instance : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Cyl (Vec2 Plane)

/-- Splitting a derivative word: `∂_v (∂_w u) = ∂_{v ++ w} u`. -/
theorem iterD_append_aux {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (v w : List E) (u : E → F) :
    UnforcedLeray.Sob.iterD (v ++ w) u = UnforcedLeray.Sob.iterD v (UnforcedLeray.Sob.iterD w u) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
      rw [List.cons_append, UnforcedLeray.Sob.iterD_cons, UnforcedLeray.Sob.iterD_cons, ih]

/-- A coordinate Plane-word of length `≤ n` is the direction list of a multi-index of order `n`. -/
theorem coordWord_idx_aux (c : ℝ) : ∀ (n : ℕ) (L : List Plane), IsCoordWord L → L.length ≤ n →
    ∃ α : UnforcedLeray.Sob.Idx 2 n, (UnforcedLeray.Sob.cylinder c).word α = L := by
  intro n
  induction n with
  | zero =>
      intro L hL hlen
      cases L with
      | nil => exact ⟨UnforcedLeray.Sob.Idx.zero, by simp⟩
      | cons a L' => simp at hlen
  | succ n ih =>
      intro L hL hlen
      cases L with
      | nil => exact ⟨UnforcedLeray.Sob.Idx.zero, by simp⟩
      | cons a L' =>
          have hL' : IsCoordWord L' := fun b hb => hL b (List.mem_cons_of_mem a hb)
          have hlen' : L'.length ≤ n := by
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨α, hα⟩ := ih L' hL' hlen'
          rcases hL a (List.mem_cons_self) with rfl | rfl
          · refine ⟨UnforcedLeray.Sob.Idx.cons 0 α, ?_⟩
            rw [UnforcedLeray.Sob.TestDomain.word_cons, hα]
            rfl
          · refine ⟨UnforcedLeray.Sob.Idx.cons 1 α, ?_⟩
            rw [UnforcedLeray.Sob.TestDomain.word_cons, hα]
            rfl

/-- Each word component of an element of `W` is at most its norm. -/
theorem csb_deriv_le_aux {c : ℝ} {m : ℕ} (ρ : UnforcedLeray.Sob.Weight (ℝ × ℝ))
    (x : UnforcedLeray.Sob.W (UnforcedLeray.Sob.cylinder c) ρ ℝ Vec2 m 2)
    (α : UnforcedLeray.Sob.Idx 2 m) :
    ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c) ρ ℝ Vec2 m 2 α x‖ ≤ ‖x‖ := by
  have hsq : ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c) ρ ℝ Vec2 m 2 α x‖ ^ 2
      ≤ ‖x‖ ^ 2 := by
    rw [UnforcedLeray.Sob.W.norm_sq x]
    exact Finset.single_le_sum (f := fun β : UnforcedLeray.Sob.Idx 2 m =>
      ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c) ρ ℝ Vec2 m 2 β x‖ ^ 2)
      (fun β _ => sq_nonneg _) (Finset.mem_univ α)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

theorem cellL2ByNorm_proof : CellL2ByNorm := by
  intro c hc m
  refine ⟨m + 2, 1, zero_le_one, fun u hu w v hw hwl hv hvl => ?_⟩
  have hL : IsCoordWord (v ++ w) := by
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hv a h
    · exact hw a h
  have hLlen : (v ++ w).length ≤ m + 2 := by
    simp only [List.length_append]
    omega
  obtain ⟨α, hα⟩ := coordWord_idx_aux c (m + 2) (v ++ w) hL hLlen
  have hμ : UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = UnforcedLeray.Cyl.cellμ c :=
    UnforcedLeray.TrainB.vecH1_measure_eq_cell c
  set x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := Vec2) (k := m + 2) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc u hu with hx
  set y := UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
    (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 (m + 2) 2 α x with hy
  have hnorm : ‖y‖ ≤ ‖x‖ := csb_deriv_le_aux _ x α
  have hae : UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) u
      =ᵐ[UnforcedLeray.Cyl.cellμ c] ⇑y := by
    have h1 := UnforcedLeray.Sob.W.deriv_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2) (k := m + 2) (p := 2)
      hc u hu α
    have key : ∀ ν : Measure (ℝ × ℝ),
        UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) = ν →
          UnforcedLeray.Sob.iterD ((UnforcedLeray.Sob.cylinder c).word α) u =ᵐ[ν] ⇑y := by
      rintro ν rfl
      exact h1.symm
    exact key _ hμ
  rw [← iterD_append_aux v w u, one_mul, hα] at *
  rw [eLpNorm_congr_ae hae, ← hμ, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hnorm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
