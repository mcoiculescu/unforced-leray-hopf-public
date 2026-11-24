import UnforcedLeray.Short.PartIIb.Tasks.BlockFactorization.CompactDuhamelNorm.Helpers

/-!
# Pointwise window estimates for `PartII-b:F2/4/3` (`CompactDuhamelNorm/WindowSide.lean`)

Isolates the three pointwise operator estimates on a single shifted block `[t', t' + Lmax]`
used to verify `hFb`, `hF`, and `hFadj` in `RCDuhamel.real_compact_duhamel_window`:
1. `norm_Jc_comp_Rc_le`: `‖Jc ∘ B ∘ Rc‖ ≤ ‖B‖` (bounded by `M` when `‖B‖ ≤ M`);
2. `lifted_free_apply_sub_lt`: strong free difference bound via `T_pl (ν s) L x` and the group law;
3. `lifted_free_adjoint_sub_lt`: strong adjoint free difference bound via `W = F ∘ T_pl (ν s) (-L)`
   and `PartIIbF24Sub.norm_adjoint_apply_sub_sq_le`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Real Metric

namespace UnforcedLeray.Short.IIb.CompactDuhamelNormHelp

open UnforcedLeray.Cons.C03.Concrete

/-- Lifting `B : Xmc c m →L[ℝ] Xmc c m` via `Jc c m` and `Rc c m` does not increase the operator norm. -/
theorem norm_Jc_comp_Rc_le (c m : ℝ) (B : Xmc c m →L[ℝ] Xmc c m) {M : ℝ}
    (hM : 0 ≤ M) (hB : ‖B‖ ≤ M) :
    ‖(Jc c m).comp (B.comp (Rc c m))‖ ≤ M := by
  calc ‖(Jc c m).comp (B.comp (Rc c m))‖
      ≤ ‖Jc c m‖ * (‖B‖ * ‖Rc c m‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (M * 1) :=
        mul_le_mul (norm_Jc_le c m)
          (mul_le_mul hB (norm_Rc_le c m) (norm_nonneg _) hM)
          (by positivity) zero_le_one
    _ = M := by ring

/-- Pointwise strong comparison on a shifted block: combines `FreeTransportConverges` on
`f = T_pl σ (τ - ρ) x` with slow-age continuity `‖T_pl σ (τ - ρ) x - T_pl σstar (τ - ρ) x‖ < ε / 2`. -/
theorem lifted_free_apply_sub_lt {c m Sig : ℝ}
    {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)} (hT : IsFrozenRadialTransport m Sig T_pl)
    (Sc : ℝ → ℝ → (Xmc c m →L[ℝ] Xmc c m))
    {t' τ ρ σ σstar ε : ℝ} (hσ : σ ∈ Icc 0 Sig) (x : Xm m)
    (hfr : ‖Jc c m (Sc (t' + ρ + (τ - ρ)) (t' + ρ)
        (Rc c m (T_pl σ (-(τ - ρ)) (T_pl σ (τ - ρ) x)))) - T_pl σ (τ - ρ) x‖ ≤ ε / 2)
    (hcont : ‖T_pl σ (τ - ρ) x - T_pl σstar (τ - ρ) x‖ < ε / 2) :
    ‖((Jc c m).comp ((Sc (t' + τ) (t' + ρ)).comp (Rc c m))) x - T_pl σstar (τ - ρ) x‖ < ε := by
  have hsL : t' + ρ + (τ - ρ) = t' + τ := by ring
  have hTf : T_pl σ (-(τ - ρ)) (T_pl σ (τ - ρ) x) = x := T_pl_neg_apply hT hσ (τ - ρ) x
  rw [hsL, hTf] at hfr
  set f : Xm m := T_pl σ (τ - ρ) x
  calc ‖((Jc c m).comp ((Sc (t' + τ) (t' + ρ)).comp (Rc c m))) x - T_pl σstar (τ - ρ) x‖
      = ‖(Jc c m (Sc (t' + τ) (t' + ρ) (Rc c m x)) - f) + (f - T_pl σstar (τ - ρ) x)‖ := by
        simp only [ContinuousLinearMap.comp_apply, sub_add_sub_cancel]
    _ ≤ ‖Jc c m (Sc (t' + τ) (t' + ρ) (Rc c m x)) - f‖ + ‖f - T_pl σstar (τ - ρ) x‖ :=
        norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hfr hcont
    _ = ε := add_halves ε

/-- Pointwise strong adjoint comparison on a shifted block via `W = F ∘ T_pl σ (-L)` and
`PartIIbF24Sub.norm_adjoint_apply_sub_sq_le`. -/
theorem lifted_free_adjoint_sub_lt {c m Sig : ℝ}
    {T_pl : ℝ → ℝ → (Xm m →L[ℝ] Xm m)} (hT : IsFrozenRadialTransport m Sig T_pl)
    (Sc : ℝ → ℝ → (Xmc c m →L[ℝ] Xmc c m))
    {t' τ ρ σ σstar ε ε₁ : ℝ} (hσ : σ ∈ Icc 0 Sig) (hσstar : σstar ∈ Icc 0 Sig)
    (x : Xm m) (hε₁_pos : 0 < ε₁) (hε₁_le1 : ε₁ ≤ 1)
    (hDε₁ : (3 * ‖x‖ ^ 2 + 2 * ‖x‖ + 1) * ε₁ ≤ (ε / 3) ^ 2)
    (hSc_bd : ‖Sc (t' + ρ + (τ - ρ)) (t' + ρ)‖ ≤ 1 + ε₁)
    (hWx_raw : ‖Jc c m (Sc (t' + ρ + (τ - ρ)) (t' + ρ) (Rc c m (T_pl σ (-(τ - ρ)) x))) - x‖ ≤ ε₁)
    (hcont : ‖T_pl σ (-(τ - ρ)) x - T_pl σstar (-(τ - ρ)) x‖ < ε / 3) :
    ‖ContinuousLinearMap.adjoint ((Jc c m).comp ((Sc (t' + τ) (t' + ρ)).comp (Rc c m))) x -
        ContinuousLinearMap.adjoint (T_pl σstar (τ - ρ)) x‖ < ε := by
  set L : ℝ := τ - ρ
  have hsL : t' + ρ + L = t' + τ := by dsimp [L]; ring
  rw [hsL] at hSc_bd hWx_raw
  let Fop : Xm m →L[ℝ] Xm m := (Jc c m).comp ((Sc (t' + τ) (t' + ρ)).comp (Rc c m))
  let W : Xm m →L[ℝ] Xm m := Fop.comp (T_pl σ (-L))
  have hWT : W.comp (T_pl σ L) = Fop :=
    ContinuousLinearMap.ext fun y => by
      simp only [W, ContinuousLinearMap.comp_apply, T_pl_neg_apply hT hσ L y]
  have hW_norm : ‖W‖ ≤ 1 + ε₁ := by
    have hF_norm : ‖Fop‖ ≤ 1 + ε₁ :=
      norm_Jc_comp_Rc_le c m (Sc (t' + τ) (t' + ρ)) (by positivity) hSc_bd
    calc ‖W‖ ≤ ‖Fop‖ * ‖T_pl σ (-L)‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1 + ε₁) * 1 :=
          mul_le_mul hF_norm (norm_T_pl_le_one hT hσ (-L)) (norm_nonneg _) (by positivity)
      _ = 1 + ε₁ := mul_one _
  have hWx : ‖W x - x‖ ≤ ε₁ := hWx_raw
  have hWadj : ‖ContinuousLinearMap.adjoint W x - x‖ ≤ ε / 3 := by
    have hsq := PartIIbF24Sub.norm_adjoint_apply_sub_sq_le W x
    have hWsq : ‖W‖ ^ 2 - 1 ≤ 3 * ε₁ := by
      nlinarith [norm_nonneg W, mul_le_mul hW_norm hW_norm (norm_nonneg W) (by positivity),
        mul_le_mul_of_nonneg_left hε₁_le1 hε₁_pos.le]
    have h1 : (‖W‖ ^ 2 - 1) * ‖x‖ ^ 2 ≤ 3 * ε₁ * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hWsq (sq_nonneg _)
    have h2 : 2 * ‖x‖ * ‖W x - x‖ ≤ 2 * ‖x‖ * ε₁ :=
      mul_le_mul_of_nonneg_left hWx (by positivity)
    have h3 : ‖ContinuousLinearMap.adjoint W x - x‖ ^ 2 ≤ (ε / 3) ^ 2 := by
      nlinarith [hsq, h1, h2, hDε₁, hε₁_pos]
    have hε_pos : 0 ≤ ε / 3 := (norm_nonneg _).trans hcont.le
    nlinarith [norm_nonneg (ContinuousLinearMap.adjoint W x - x), h3, hε_pos]
  have hadj_F : ContinuousLinearMap.adjoint Fop x =
      T_pl σ (-L) (ContinuousLinearMap.adjoint W x) := by
    rw [← hWT, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
      adjoint_T_pl hT hσ L]
  have hadj_F0 : ContinuousLinearMap.adjoint (T_pl σstar L) x = T_pl σstar (-L) x :=
    congrArg (fun B : Xm m →L[ℝ] Xm m => B x) (adjoint_T_pl hT hσstar L)
  change ‖ContinuousLinearMap.adjoint Fop x - ContinuousLinearMap.adjoint (T_pl σstar L) x‖ < ε
  rw [hadj_F, hadj_F0]
  have hsplit : T_pl σ (-L) (ContinuousLinearMap.adjoint W x) - T_pl σstar (-L) x =
      T_pl σ (-L) (ContinuousLinearMap.adjoint W x - x) + (T_pl σ (-L) x - T_pl σstar (-L) x) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [hsplit]
  calc ‖T_pl σ (-L) (ContinuousLinearMap.adjoint W x - x) + (T_pl σ (-L) x - T_pl σstar (-L) x)‖
      ≤ ‖T_pl σ (-L) (ContinuousLinearMap.adjoint W x - x)‖ +
          ‖T_pl σ (-L) x - T_pl σstar (-L) x‖ := norm_add_le _ _
    _ = ‖ContinuousLinearMap.adjoint W x - x‖ + ‖T_pl σ (-L) x - T_pl σstar (-L) x‖ := by
        rw [hT.isometry σ hσ (-L)]
    _ < ε / 3 + ε / 3 := add_lt_add_of_le_of_lt hWadj hcont
    _ < ε := by
        have hε_pos : 0 < ε := by linarith [norm_nonneg (T_pl σ (-L) x - T_pl σstar (-L) x), hcont]
        linarith

end UnforcedLeray.Short.IIb.CompactDuhamelNormHelp
