import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.FullKerReg.SPart1

/-!
# Smallness as `h ↓ 0`: the factor `1 - λ²` in `xKer`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

/-- `xKer` carries the factor `1 - λ²`: a bound uniform in the kernel scale. -/
theorem xKer_small : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (ν μ h : ℝ), 0 < ν → -(1 / 4) < μ → μ ≤ 1 → 0 < h →
    ∀ (M : Matrix (Fin 3) (Fin 3) ℝ) (x : Space), x ≠ 0 →
      ‖xKer ν μ h x M‖ ≤ ((1 - pdLam h ^ 2) * (C0 * IIIa.tensorNorm M)) * (‖x‖ ^ 4)⁻¹ := by
  obtain ⟨C0, hC0⟩ := IIIa.sepKernelBounds 0
  have hK0 : ∀ x : Space, x ≠ 0 → ∀ i k : Fin 3, ∀ s : ℝ, 0 < s →
      ‖iteratedFDeriv ℝ (0 + 1) (fun y => IIIa.heatLerayK s i k y) x‖ ≤
        C0 * ‖x‖ ^ (-4 - ((0 : ℕ) : ℝ)) :=
    fun x hx i k s hs => (hC0 x hx i k).1 s hs
  refine ⟨27 * max C0 0, by positivity, fun ν μ h hν hμ0 hμ1 hh M x hx => ?_⟩
  have hT := kb_hT ν h hν hh
  have hG := kb_grad0 hT M hK0 hx
  obtain ⟨hA, hB, hBA, hA1⟩ := kb_coef_bounds μ h hμ0 hμ1 hh
  have hl := pdLam_pos h
  have hB' : pdLam h ^ (2 * μ + 5) = pdLam h ^ (2 * μ + 3) * pdLam h ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hl]; norm_num; ring_nf
  have hc : |-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))| ≤ 1 - pdLam h ^ 2 := by
    rw [abs_neg, abs_of_nonneg (sub_nonneg.mpr hBA), hB']
    have hl2 : pdLam h ^ 2 ≤ 1 := by
      have := pdLam_lt_one hh; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hA1 (sub_nonneg.mpr hl2)]
  unfold xKer
  rw [norm_smul, Real.norm_eq_abs]
  have hnn : 0 ≤ 1 - pdLam h ^ 2 := by
    have := pdLam_lt_one hh; nlinarith
  calc |-(pdLam h ^ (2 * μ + 3) - pdLam h ^ (2 * μ + 5))| * ‖gradKCon (ν * (1 - pdLam h ^ 2)) x M‖
      ≤ (1 - pdLam h ^ 2) * (27 * (max C0 0 * (‖x‖ ^ 4)⁻¹) * IIIa.tensorNorm M) :=
        mul_le_mul hc hG (norm_nonneg _) hnn
    _ = _ := by ring

theorem small_tendsto : Tendsto (fun h : ℝ => 1 - pdLam h ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun h : ℝ => 1 - pdLam h ^ 2) := by
    unfold pdLam; fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  simpa [pdLam] using this

/-- The primitive is bounded using only the size of `A`. -/
theorem primInt_abs_le {A : Space → ℝ} {w : Space} {K ρ₀ δ : ℝ} (hK : 0 ≤ K) (hρ₀ : 0 ≤ ρ₀)
    (hδ : 0 < δ) (hw : w 0 ≤ ρ₀) (b0 : ∀ x : Space, x ≠ 0 → |A x| ≤ K * (‖x‖ ^ 4)⁻¹)
    (q : Space) (hq : ρ₀ + δ < q 0) :
    |primInt A w q| ≤ primCp ρ₀ δ * K * (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - w 2) ^ 2))) := by
  have ha : 0 < q 0 - ρ₀ := by linarith
  obtain ⟨hJi, hJv⟩ := primJ2 ha (q 2 - w 2)
  have hI : ∫ u in Ioi (0 : ℝ), primCp ρ₀ δ * K *
      ((q 0 - ρ₀ + u) * ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - w 2) ^ 2) ^ 2)⁻¹))
      = primCp ρ₀ δ * K * (1 / (2 * ((q 0 - ρ₀) ^ 2 + (q 2 - w 2) ^ 2))) := by
    rw [integral_const_mul, hJv]
  have hIi : Integrable (fun u : ℝ => primCp ρ₀ δ * K *
      ((q 0 - ρ₀ + u) * ((((q 0 - ρ₀ + u) ^ 2 + (q 2 - w 2) ^ 2) ^ 2)⁻¹)))
      (volume.restrict (Ioi (0 : ℝ))) := hJi.const_mul _
  have hae : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))), 0 < u :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => hu)
  have := norm_integral_le_of_norm_le hIi (hae.mono fun u hu => by
    have hv : δ ≤ q 0 + u - ρ₀ := by linarith
    have hlow := prim_shift_lower q w u ρ₀ hw (by linarith)
    have ht : (q 0 + u - ρ₀) ^ 2 + (q 2 - w 2) ^ 2 ≤ ‖q + (u • primE0 - w)‖ ^ 2 := hlow
    have hx : q + (u • primE0 - w) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at ht
      have : 0 < (q 0 + u - ρ₀) ^ 2 := by have := lt_of_lt_of_le hδ hv; positivity
      nlinarith [sq_nonneg (q 2 - w 2)]
    have hp := (primPt (K := K) (ρ₀ := ρ₀) (δ := δ) (v := q 0 + u - ρ₀) (b := q 2 - w 2)
      (t := ‖q + (u • primE0 - w)‖) (α₀ := |A (q + (u • primE0 - w))|) (α₁ := 0) (α₂ := 0) hK hρ₀ hδ hv
      ht (norm_nonneg _) (abs_nonneg _) le_rfl le_rfl (b0 _ hx) (by positivity) (by positivity)).1
    have hqu : |q 0 + u| = ρ₀ + (q 0 + u - ρ₀) := by
      rw [abs_of_nonneg (by linarith)]; ring
    have e : q 0 + u - ρ₀ = q 0 - ρ₀ + u := by ring
    rw [e] at hp
    rw [Real.norm_eq_abs]
    show |(q 0 + u) * A (q + (u • primE0 - w))| ≤ _
    rw [abs_mul, show |q 0 + u| = ρ₀ + (q 0 - ρ₀ + u) by rw [abs_of_nonneg (by linarith)]; ring]
    exact hp)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_of_eq hI)

end UnforcedLeray.Short.PartIIIb.Concrete

end
