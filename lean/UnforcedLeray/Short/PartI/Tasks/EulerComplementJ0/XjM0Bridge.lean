import UnforcedLeray.Short.PartI.Sub.PartI_S15

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Real
open scoped ENNReal ComplexConjugate ContDiff Topology

namespace UnforcedLeray.Short.PartI

/-- For `j = 0` the only multi-index is `0`, so the norm of `H^0_M` is the `L²_M` norm of the value. -/
theorem xjM0_norm_eq_value {M : ℝ} (F : B0008.HjM 0 M) : ‖F‖ = ‖F.value‖ := by
  have hall : ∀ α : B0008.Idx 0, α = B0008.idx0 0 := by
    rintro ⟨⟨a, b⟩, hα⟩
    have h := (PlanarBS.Sob.mem_multiIdx).1 hα
    dsimp only at h
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha
    subst hb
    rfl
  have hsum : ∑ α : B0008.Idx 0, ‖F.der α‖ ^ 2 = ‖F.der (B0008.idx0 0)‖ ^ 2 := by
    apply Fintype.sum_eq_single
    intro α hα
    exact absurd (hall α) hα
  have h := B0008.HjM.norm_sq F
  rw [hsum, B0008.HjM.der_idx0] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

theorem xjM0Bridge : XjM0Bridge := by
  intro M hM
  constructor
  · intro f
    let v : Planar.L2w M := (f : B0008.HjM 0 M).value
    have hint : ∫ y, v y = 0 := (B0008.mem_XjM_iff hM _).1 f.2
    have hmem : v ∈ Planar.X0 hM := (Planar.mem_X0_iff hM _).2 hint
    refine ⟨⟨v, hmem⟩, ?_, ?_⟩
    · exact Filter.EventuallyEq.rfl
    · calc ‖(⟨v, hmem⟩ : Planar.X0 hM)‖ = ‖v‖ := rfl
        _ = ‖(f : B0008.HjM 0 M).value‖ := rfl
        _ = ‖(f : B0008.HjM 0 M)‖ := (xjM0_norm_eq_value _).symm
        _ = ‖f‖ := rfl
  · intro g'
    let T : B0008.Tuple 0 M := WithLp.toLp 2 (fun _ : B0008.Idx 0 => (g' : Planar.L2w M))
    have hT : T ∈ B0008.HSub 0 M := by
      rw [B0008.mem_HSub_iff]
      intro α
      have hα : α = B0008.idx0 0 := by
        rcases α with ⟨⟨a, b⟩, hα⟩
        have h := (PlanarBS.Sob.mem_multiIdx).1 hα
        dsimp only at h
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha
        subst hb
        rfl
      subst hα
      intro φ _
      have hp : NonUniqueEuler.Sob.pdList ((B0008.idx0 0 : B0008.Idx 0) : ℕ × ℕ) = [] := rfl
      rw [hp, List.length_nil, pow_zero, one_mul]
      rfl
    let G : B0008.HjM 0 M := ⟨T, hT⟩
    have hmem : G ∈ B0008.XjM 0 M :=
      (B0008.mem_XjM_iff hM G).2 ((Planar.mem_X0_iff hM _).1 g'.2)
    refine ⟨⟨G, hmem⟩, Filter.EventuallyEq.rfl, ?_⟩
    calc ‖((⟨G, hmem⟩ : B0008.XjM 0 M) : B0008.HjM 0 M)‖
        = ‖G‖ := rfl
      _ = ‖G.value‖ := xjM0_norm_eq_value G
      _ = ‖(g' : Planar.L2w M)‖ := rfl
      _ = ‖g'‖ := rfl

end UnforcedLeray.Short.PartI
