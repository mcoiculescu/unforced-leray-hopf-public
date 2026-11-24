import UnforcedLeray.Short.PartIIb.StatementsMixed
import UnforcedLeray.Short.PartIIb.Tasks.InvAddComp

/-!
# Part II-b, task `PartII-b:T06`: the graph-transform lemma

Source of record: `the November 2 reference manuscript`, lines 2172-2188
(`short-bg:graphs` at line 2177). The statement is `GraphTransformLemma` in `StatementsMixed.lean`
and is not changed here.

Target: `graphTransformLemma_proof : UnforcedLeray.Short.IIb.GraphTransformLemma`.

Proof. The inverse `M = (a + b ∘ ξ)⁻¹` comes from `exists_inverse_add_comp` (task `T05`,
`Tasks/InvAddComp.lean`). Two-sided inverses are unique, so every two-sided inverse obeys the same
norm bound. Ball preservation is `‖(c + d ∘ ξ) ∘ M‖ ≤ (η + D r) A / (1 - A η r) ≤ r`, which is the
hypothesis `A η (1 + r²) ≤ r (1 - A D)`. The Lipschitz bound uses the identity
`(ξ'₁ - ξ'₂) ∘ (a + b ∘ ξ₁) = (d - ξ'₂ ∘ b) ∘ (ξ₁ - ξ₂)`, where `ξ'ᵢ = (c + d ∘ ξᵢ) ∘ Mᵢ`.
The backward map is the same argument with the roles of `b` and `c` exchanged.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

/-- Two-sided inverses are unique. -/
theorem gt_inv_unique {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T M M' : E →L[ℝ] E) (h1 : M * T = 1) (h2 : T * M' = 1) : M = M' := by
  calc M = M * (T * M') := by rw [h2, mul_one]
    _ = (M * T) * M' := (mul_assoc M T M').symm
    _ = M' := by rw [h1, one_mul]

/-- The forward difference identity: `(ξ'₁ - ξ'₂) ∘ (a + b ∘ ξ₁) = (d - ξ'₂ ∘ b) ∘ (ξ₁ - ξ₂)`
with `ξ'ᵢ = (c + d ∘ ξᵢ) ∘ Mᵢ`, followed by `Mᵢ` (SP 2172-2188). -/
theorem gt_fwd_identity {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : E →L[ℝ] E) (b : F →L[ℝ] E) (c : E →L[ℝ] F) (d : F →L[ℝ] F)
    (ξ₁ ξ₂ : E →L[ℝ] F) (M₁ M₂ : E →L[ℝ] E)
    (h₁a : M₁ * (a + b.comp ξ₁) = 1) (h₁b : (a + b.comp ξ₁) * M₁ = 1)
    (h₂a : M₂ * (a + b.comp ξ₂) = 1) :
    (c + d.comp ξ₁).comp M₁ - (c + d.comp ξ₂).comp M₂ =
      ((d - ((c + d.comp ξ₂).comp M₂).comp b).comp (ξ₁ - ξ₂)).comp M₁ := by
  have hA1 : ∀ y : E, M₁ ((a + b.comp ξ₁) y) = y := by
    intro y
    have h : (M₁ * (a + b.comp ξ₁)) y = (1 : E →L[ℝ] E) y := by rw [h₁a]
    exact h
  have hB1 : ∀ x : E, (a + b.comp ξ₁) (M₁ x) = x := by
    intro x
    have h : ((a + b.comp ξ₁) * M₁) x = (1 : E →L[ℝ] E) x := by rw [h₁b]
    exact h
  have hA2 : ∀ y : E, M₂ ((a + b.comp ξ₂) y) = y := by
    intro y
    have h : (M₂ * (a + b.comp ξ₂)) y = (1 : E →L[ℝ] E) y := by rw [h₂a]
    exact h
  have e1 : ∀ y : E, (a + b.comp ξ₁) y = (a + b.comp ξ₂) y + b ((ξ₁ - ξ₂) y) := by
    intro y
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      sub_apply, map_sub]
    abel
  have key : ∀ y : E,
      ((c + d.comp ξ₁).comp M₁ - (c + d.comp ξ₂).comp M₂) ((a + b.comp ξ₁) y) =
        (d - ((c + d.comp ξ₂).comp M₂).comp b) ((ξ₁ - ξ₂) y) := by
    intro y
    have hz : M₂ ((a + b.comp ξ₁) y) = y + M₂ (b ((ξ₁ - ξ₂) y)) := by
      rw [e1 y, map_add, hA2 y]
    show (c + d.comp ξ₁) (M₁ ((a + b.comp ξ₁) y)) - (c + d.comp ξ₂) (M₂ ((a + b.comp ξ₁) y))
      = d ((ξ₁ - ξ₂) y) - (c + d.comp ξ₂) (M₂ (b ((ξ₁ - ξ₂) y)))
    rw [hA1 y, hz]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      sub_apply, map_add, map_sub]
    abel
  ext x
  have hk := key (M₁ x)
  rw [hB1 x] at hk
  exact hk

/-- The backward difference identity: `Z₁ - Z₂ = M₁ ∘ (ζ₁ - ζ₂) ∘ (d + c ∘ Z₂)` with
`Zᵢ = Mᵢ ∘ (ζᵢ d - b)` (SP 2172-2188). -/
theorem gt_bwd_identity {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : E →L[ℝ] E) (b : F →L[ℝ] E) (c : E →L[ℝ] F) (d : F →L[ℝ] F)
    (ζ₁ ζ₂ : F →L[ℝ] E) (M₁ M₂ : E →L[ℝ] E)
    (h₁a : M₁ * (a - ζ₁.comp c) = 1) (h₁b : (a - ζ₁.comp c) * M₁ = 1)
    (h₂b : (a - ζ₂.comp c) * M₂ = 1) :
    M₁.comp (ζ₁.comp d - b) - M₂.comp (ζ₂.comp d - b) =
      M₁.comp ((ζ₁ - ζ₂).comp (d + c.comp (M₂.comp (ζ₂.comp d - b)))) := by
  have hA1 : ∀ x : E, M₁ ((a - ζ₁.comp c) x) = x := by
    intro x
    have h : (M₁ * (a - ζ₁.comp c)) x = (1 : E →L[ℝ] E) x := by rw [h₁a]
    exact h
  have hB1 : ∀ z : E, (a - ζ₁.comp c) (M₁ z) = z := by
    intro z
    have h : ((a - ζ₁.comp c) * M₁) z = (1 : E →L[ℝ] E) z := by rw [h₁b]
    exact h
  have hB2 : ∀ z : E, (a - ζ₂.comp c) (M₂ z) = z := by
    intro z
    have h : ((a - ζ₂.comp c) * M₂) z = (1 : E →L[ℝ] E) z := by rw [h₂b]
    exact h
  have e2 : ∀ z : E, (a - ζ₁.comp c) z = (a - ζ₂.comp c) z - (ζ₁ - ζ₂) (c z) := by
    intro z
    simp only [sub_apply, ContinuousLinearMap.comp_apply]
    abel
  ext v
  have hinner : (a - ζ₁.comp c) (M₁ (ζ₁ (d v) - b v) - M₂ (ζ₂ (d v) - b v)) =
      (ζ₁ - ζ₂) (d v + c (M₂ (ζ₂ (d v) - b v))) := by
    rw [map_sub (a - ζ₁.comp c), hB1, e2 (M₂ (ζ₂ (d v) - b v)), hB2]
    simp only [map_add, sub_apply]
    abel
  have h := congrArg M₁ hinner
  rw [hA1] at h
  exact h

/-- **The graph-transform lemma** (SP 2172-2188). -/
theorem graphTransformLemma_proof : UnforcedLeray.Short.IIb.GraphTransformLemma := by
  intro E F _ _ _ _ _ _ a b c d ainv A D η r h1 h2 hA hD hb hc hη hr hArη hball
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) hA
  have hD0 : 0 ≤ D := le_trans (norm_nonneg _) hD
  have hq : 0 < 1 - A * η * r := by linarith
  have hkey : (η + D * r) * (A / (1 - A * η * r)) ≤ r := by
    have hk2 : (η + D * r) * A ≤ r * (1 - A * η * r) := by nlinarith [hball]
    calc (η + D * r) * (A / (1 - A * η * r)) = ((η + D * r) * A) / (1 - A * η * r) := by ring
      _ ≤ r := by rw [div_le_iff₀ hq]; exact hk2
  -- Norm bound for any two-sided inverse of `a + b ∘ ξ`.
  have hfinv : ∀ ξ : E →L[ℝ] F, ‖ξ‖ ≤ r → ∀ M : E →L[ℝ] E,
      M * (a + b.comp ξ) = 1 → (a + b.comp ξ) * M = 1 → ‖M‖ ≤ A / (1 - A * η * r) := by
    intro ξ hξ M hMa hMb
    obtain ⟨M0, h0a, h0b, h0n⟩ := exists_inverse_add_comp a ainv b ξ h1 h2 hA hb hξ hη hr hArη
    have hMM : M = M0 := gt_inv_unique _ M M0 hMa h0b
    rw [hMM]
    exact h0n
  have hC : ∀ ξ : E →L[ℝ] F, ‖ξ‖ ≤ r → ‖c + d.comp ξ‖ ≤ η + D * r := by
    intro ξ hξ
    calc ‖c + d.comp ξ‖ ≤ ‖c‖ + ‖d.comp ξ‖ := norm_add_le _ _
      _ ≤ η + D * r :=
          add_le_add hc ((d.opNorm_comp_le ξ).trans (mul_le_mul hD hξ (norm_nonneg _) hD0))
  -- Ball preservation for any two-sided inverse.
  have hfball : ∀ ξ : E →L[ℝ] F, ‖ξ‖ ≤ r → ∀ M : E →L[ℝ] E,
      M * (a + b.comp ξ) = 1 → (a + b.comp ξ) * M = 1 → ‖(c + d.comp ξ).comp M‖ ≤ r := by
    intro ξ hξ M hMa hMb
    have hM := hfinv ξ hξ M hMa hMb
    calc ‖(c + d.comp ξ).comp M‖ ≤ ‖c + d.comp ξ‖ * ‖M‖ := (c + d.comp ξ).opNorm_comp_le M
      _ ≤ (η + D * r) * (A / (1 - A * η * r)) :=
          mul_le_mul (hC ξ hξ) hM (norm_nonneg _) (add_nonneg hη (mul_nonneg hD0 hr))
      _ ≤ r := hkey
  -- An inverse of `a - ζ ∘ c`, from `T05` applied to `b := -ζ`, `ξ := c` with `η, r` swapped.
  have hBinv : ∀ ζ : F →L[ℝ] E, ‖ζ‖ ≤ r → ∃ M0 : E →L[ℝ] E,
      M0 * (a - ζ.comp c) = 1 ∧ (a - ζ.comp c) * M0 = 1 ∧ ‖M0‖ ≤ A / (1 - A * η * r) := by
    intro ζ hζ
    have hsub : a - ζ.comp c = a + (-ζ).comp c := by
      rw [ContinuousLinearMap.neg_comp, sub_eq_add_neg]
    have hnζ : ‖-ζ‖ ≤ r := by rw [norm_neg]; exact hζ
    have hArη' : A * r * η < 1 := by
      have e : A * r * η = A * η * r := by ring
      rw [e]; exact hArη
    obtain ⟨M0, h0a, h0b, h0n⟩ :=
      exists_inverse_add_comp a ainv (-ζ) c h1 h2 hA hnζ hc hr hη hArη'
    refine ⟨M0, ?_, ?_, ?_⟩
    · rw [hsub]; exact h0a
    · rw [hsub]; exact h0b
    · have e : A * r * η = A * η * r := by ring
      rw [e] at h0n; exact h0n
  have hbinv : ∀ ζ : F →L[ℝ] E, ‖ζ‖ ≤ r → ∀ M : E →L[ℝ] E,
      M * (a - ζ.comp c) = 1 → (a - ζ.comp c) * M = 1 → ‖M‖ ≤ A / (1 - A * η * r) := by
    intro ζ hζ M hMa hMb
    obtain ⟨M0, h0a, h0b, h0n⟩ := hBinv ζ hζ
    have hMM : M = M0 := gt_inv_unique _ M M0 hMa h0b
    rw [hMM]
    exact h0n
  have hZ : ∀ ζ : F →L[ℝ] E, ‖ζ‖ ≤ r → ‖ζ.comp d - b‖ ≤ η + D * r := by
    intro ζ hζ
    have hzd : ‖ζ.comp d‖ ≤ r * D :=
      (ζ.opNorm_comp_le d).trans (mul_le_mul hζ hD (norm_nonneg _) hr)
    rw [mul_comm r D] at hzd
    calc ‖ζ.comp d - b‖ ≤ ‖ζ.comp d‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ η + D * r := by linarith
  have hbball : ∀ ζ : F →L[ℝ] E, ‖ζ‖ ≤ r → ∀ M : E →L[ℝ] E,
      M * (a - ζ.comp c) = 1 → (a - ζ.comp c) * M = 1 → ‖M.comp (ζ.comp d - b)‖ ≤ r := by
    intro ζ hζ M hMa hMb
    have hM := hbinv ζ hζ M hMa hMb
    calc ‖M.comp (ζ.comp d - b)‖ ≤ ‖M‖ * ‖ζ.comp d - b‖ := M.opNorm_comp_le _
      _ ≤ (A / (1 - A * η * r)) * (η + D * r) :=
          mul_le_mul hM (hZ ζ hζ) (norm_nonneg _) (div_nonneg hA0 hq.le)
      _ = (η + D * r) * (A / (1 - A * η * r)) := by ring
      _ ≤ r := hkey
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- forward ball preservation
    intro ξ hξ
    obtain ⟨M0, h0a, h0b, h0n⟩ := exists_inverse_add_comp a ainv b ξ h1 h2 hA hb hξ hη hr hArη
    exact ⟨M0, h0a, h0b, h0n, hfball ξ hξ M0 h0a h0b⟩
  · -- forward Lipschitz bound
    intro ξ₁ ξ₂ M₁ M₂ hξ₁ hξ₂ h₁a h₁b h₂a h₂b
    have hPb : ‖(c + d.comp ξ₂).comp M₂‖ ≤ r := hfball ξ₂ hξ₂ M₂ h₂a h₂b
    have hid := gt_fwd_identity a b c d ξ₁ ξ₂ M₁ M₂ h₁a h₁b h₂a
    have hdb : ‖d - ((c + d.comp ξ₂).comp M₂).comp b‖ ≤ D + r * η := by
      calc ‖d - ((c + d.comp ξ₂).comp M₂).comp b‖
            ≤ ‖d‖ + ‖((c + d.comp ξ₂).comp M₂).comp b‖ := norm_sub_le _ _
        _ ≤ D + r * η :=
            add_le_add hD ((((c + d.comp ξ₂).comp M₂).opNorm_comp_le b).trans
              (mul_le_mul hPb hb (norm_nonneg _) hr))
    have hQ : ‖(d - ((c + d.comp ξ₂).comp M₂).comp b).comp (ξ₁ - ξ₂)‖ ≤
        (D + r * η) * ‖ξ₁ - ξ₂‖ :=
      ((d - ((c + d.comp ξ₂).comp M₂).comp b).opNorm_comp_le (ξ₁ - ξ₂)).trans
        (mul_le_mul hdb le_rfl (norm_nonneg _) (add_nonneg hD0 (mul_nonneg hr hη)))
    have hM1 := hfinv ξ₁ hξ₁ M₁ h₁a h₁b
    rw [hid]
    calc ‖((d - ((c + d.comp ξ₂).comp M₂).comp b).comp (ξ₁ - ξ₂)).comp M₁‖
        ≤ ‖(d - ((c + d.comp ξ₂).comp M₂).comp b).comp (ξ₁ - ξ₂)‖ * ‖M₁‖ :=
          ((d - ((c + d.comp ξ₂).comp M₂).comp b).comp (ξ₁ - ξ₂)).opNorm_comp_le M₁
      _ ≤ ((D + r * η) * ‖ξ₁ - ξ₂‖) * (A / (1 - A * η * r)) :=
          mul_le_mul hQ hM1 (norm_nonneg _)
            (mul_nonneg (add_nonneg hD0 (mul_nonneg hr hη)) (norm_nonneg _))
      _ = A * (D + η * r) / (1 - A * η * r) * ‖ξ₁ - ξ₂‖ := by ring
  · -- backward ball preservation
    intro ζ hζ
    obtain ⟨M0, h0a, h0b, h0n⟩ := hBinv ζ hζ
    exact ⟨M0, h0a, h0b, h0n, hbball ζ hζ M0 h0a h0b⟩
  · -- backward Lipschitz bound
    intro ζ₁ ζ₂ M₁ M₂ hζ₁ hζ₂ h₁a h₁b h₂a h₂b
    have hZ2 : ‖M₂.comp (ζ₂.comp d - b)‖ ≤ r := hbball ζ₂ hζ₂ M₂ h₂a h₂b
    have hid := gt_bwd_identity a b c d ζ₁ ζ₂ M₁ M₂ h₁a h₁b h₂b
    have hcZ : ‖c.comp (M₂.comp (ζ₂.comp d - b))‖ ≤ η * r :=
      (c.opNorm_comp_le (M₂.comp (ζ₂.comp d - b))).trans
        (mul_le_mul hc hZ2 (norm_nonneg _) hη)
    have hdc : ‖d + c.comp (M₂.comp (ζ₂.comp d - b))‖ ≤ D + η * r := by
      calc ‖d + c.comp (M₂.comp (ζ₂.comp d - b))‖
            ≤ ‖d‖ + ‖c.comp (M₂.comp (ζ₂.comp d - b))‖ := norm_add_le _ _
        _ ≤ D + η * r := add_le_add hD hcZ
    have hQ : ‖(ζ₁ - ζ₂).comp (d + c.comp (M₂.comp (ζ₂.comp d - b)))‖ ≤
        ‖ζ₁ - ζ₂‖ * (D + η * r) :=
      ((ζ₁ - ζ₂).opNorm_comp_le (d + c.comp (M₂.comp (ζ₂.comp d - b)))).trans
        (mul_le_mul_of_nonneg_left hdc (norm_nonneg _))
    have hM1 := hbinv ζ₁ hζ₁ M₁ h₁a h₁b
    rw [hid]
    calc ‖M₁.comp ((ζ₁ - ζ₂).comp (d + c.comp (M₂.comp (ζ₂.comp d - b))))‖
        ≤ ‖M₁‖ * ‖(ζ₁ - ζ₂).comp (d + c.comp (M₂.comp (ζ₂.comp d - b)))‖ :=
          M₁.opNorm_comp_le _
      _ ≤ (A / (1 - A * η * r)) * (‖ζ₁ - ζ₂‖ * (D + η * r)) :=
          mul_le_mul hM1 hQ (norm_nonneg _) (div_nonneg hA0 hq.le)
      _ = A * (D + η * r) / (1 - A * η * r) * ‖ζ₁ - ζ₂‖ := by ring

end UnforcedLeray.Short.IIb
