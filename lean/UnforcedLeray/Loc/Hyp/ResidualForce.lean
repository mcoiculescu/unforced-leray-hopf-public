import UnforcedLeray.Loc.Hyp.ResidualForce.Bounds

/-!
# Hypothesis `H-Residual`: the physical residual `G_res` (proof of `L10.ResidualForce`)

`paper/main.tex` lines 474–491 (the proof of `loc:eq:force-bound`), blueprint unit B0722
(ingredient (2)), infrastructure INF04, INF22, INF27. The statement is
`UnforcedLeray.Blueprint.L10.ResidualForce` (`Loc/L10Nonlinear.lean`, line 94): for every
unstable background `D` and every datum `u₀` with `IsCompactDatum D u₀`, with
`H = H_h[u_dss]` (line 160) and `K = K_loc` (line 446), there are `G_res : ℝ → X` and `C` with
`G_res` continuous on `τ ≤ 0`, `G_res(τ) = -𝔓 div(H ⊗ K + K ⊗ H + K ⊗ K)(τ)` in the literal weak
sense `IsMinusLerayDiv`, and `‖G_res(τ)‖_{H¹} ≤ C e^{τ/2}` for `τ ≤ 0`.

## Proof

Write `δ = e^{τ/4}` (so `δ² = e^{τ/2}`, `δ⁴ = t`), `W = H + ½K`. Column `j` of
`H ⊗ K + K ⊗ H + K ⊗ K` is `B_j(W, K)`, `B_j(u,v) = v_j u + u_j v` (`colT_eq`).

1. *Decay* (`Bounds.lean`). `|D^a H| ≤ C(1+|y|)^{-1-a}` (B0710, the compiled
   `Heat.simHeat_decay`); `|D^b K| ≤ Cδ^{2b+2}(1+δ²|y|)^{-1-b}` from the smoothed defect
   (`tail_decayK`); hence `W` has the decay of `H`.
2. *Products* (`Product.lean`, `Weights.lean`). By Leibniz, `B_j(W,K)` is `≤ C(1+|y|)^{-2}` and
   all its first and second derivatives are `≤ Cψ_δ`, `ψ_δ = 2δ²(1+|y|)^{-2} + δ⁵(1+δ²|y|)^{-3}`,
   whose `L²` norm is `≤ cδ²`. In physical variables these are the bounds `C⟨x⟩^{-3}`,
   `C⟨x⟩^{-4}` of lines 482–484 together with the inner-ball smallness of lines 479–481; the
   similarity rescaling of line 486 is built into the weight.
3. *Projection*. The columns are smooth `H²` fields (`colH2`), so the compiled construction
   `minusLerayDivX` (the `H¹`-bounded Leray projection of `∑ⱼ ∂ⱼ 𝕋_{·j}`, line 485) gives
   `G_res(τ) ∈ X` with `IsMinusLerayDiv`; its norm is at most the `L²` norms of the first and
   second derivatives of the columns (`norm_minusLerayDivX_le'`), hence `≤ Cδ² = Ce^{τ/2}`.
   The undifferentiated columns are in `L²` but enter no bound: only the divergence is
   estimated, as in the manuscript.
4. *Continuity* (`Continuity.lean`; implicit in the manuscript). The columns and their
   derivatives are pointwise continuous in `τ` (the heat profiles are kernel convolutions
   with the fixed kernel `G_h` of the data `e^{τ/2}v(e^{τ/2}·)`), and dominated by
   `C(1+|y|)^{-2}` for `τ ≤ 0`; dominated convergence gives `H²`-continuity, and `G_res` is
   built at the phase `min τ 0`, so it is even continuous on all of `ℝ`.

The manuscript's statement is stronger in the exponents (`Ct^{3/4}`, `Ct^{5/4}` for the `L²` and
gradient norms, `t = e^τ`); the hypothesis asks for `Ce^{τ/2}` only, which is what is proved.

Main declarations: `residualForce : ResidualForce` (namespace `UnforcedLeray.Blueprint.L10`),
`norm_minusLerayDivX_le'`, `minusLerayDivX_sub`, `colT`, `colT_eq`, `colH2`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.ResidualForceHyp

open UnforcedLeray.Blueprint UnforcedLeray.Blueprint.L10 SobolevGraph

/-! ## `-𝔓 div` of `H²` columns: the bound by the derivatives only, and linearity -/

theorem norm_h2PartialH1_le' (P : H2) (j : Fin 3) :
    ‖h2PartialH1 P j‖ ≤ ‖P.first j‖ + ∑ i : Fin 3, ‖P.second j i‖ := by
  have ha := norm_nonneg (P.first j)
  have h0 := norm_nonneg (P.second j 0)
  have h1 := norm_nonneg (P.second j 1)
  have h2 := norm_nonneg (P.second j 2)
  refine (sq_le_sq₀ (norm_nonneg _) (by rw [Fin.sum_univ_three]; positivity)).mp ?_
  rw [H1.norm_sq]
  simp only [h2PartialH1, H1.value_ofWeakDerivatives, H1.derivative_ofWeakDerivatives,
    Fin.sum_univ_three]
  nlinarith [mul_nonneg ha h0, mul_nonneg ha h1, mul_nonneg ha h2, mul_nonneg h0 h1,
    mul_nonneg h0 h2, mul_nonneg h1 h2]

/-- `‖-𝔓 div 𝕋‖_{H¹} ≤ ∑ⱼ (‖∂ⱼ𝕋_{·j}‖_{L²} + ∑ᵢ ‖∂ᵢ∂ⱼ𝕋_{·j}‖_{L²})` for `H²` columns. -/
theorem norm_minusLerayDivX_le' (P : Fin 3 → H2) :
    ‖minusLerayDivX P‖ ≤ ∑ j : Fin 3, (‖(P j).first j‖ + ∑ i : Fin 3, ‖(P j).second j i‖) := by
  rw [minusLerayDivX, norm_neg, norm_mk_X]
  refine (Leray.norm_h1Project_le _).trans ?_
  unfold h2DivH1
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_h2PartialH1_le' (P j) j)

theorem minusLerayDivX_sub (P Q : Fin 3 → H2) :
    minusLerayDivX P - minusLerayDivX Q = minusLerayDivX (P - Q) := by
  apply Xclass_injective
  rw [Xclass_sub, Xclass_minusLerayDivX, Xclass_minusLerayDivX, Xclass_minusLerayDivX]
  have e2 : ∀ j, (P - Q) j = P j - Q j := fun j => rfl
  have e3 : ∀ j, (P j - Q j).first j = (P j).first j - (Q j).first j := fun j => by
    rw [← H2.firstCLM_apply, map_sub]
    rfl
  simp only [e2, e3, Finset.sum_sub_distrib, map_sub]
  abel

theorem norm_minusLerayDivX_sub_le (P Q : Fin 3 → H2) :
    ‖minusLerayDivX P - minusLerayDivX Q‖ ≤ ∑ j : Fin 3, ‖P j - Q j‖ := by
  rw [minusLerayDivX_sub]
  exact norm_minusLerayDivX_le (P - Q)

/-! ## A smooth `H²` column -/

/-- A smooth field whose value and first and second coordinate derivatives are in `L²`, as an
element of the compiled `H²` (classical derivatives are weak derivatives). -/
def colH2 {f : SpatialField} (hf : ContDiff ℝ ∞ f) (h0 : MemLp f 2 volume)
    (h1 : ∀ i, MemLp (dpart f i) 2 volume) (h2 : ∀ i l, MemLp (dpart (dpart f i) l) 2 volume) :
    H2 :=
  H2.ofFields f (fun i => dpart f i) (fun i l => dpart (dpart f i) l) h0 h1 h2
    (fun i => hasWeakSpatialDerivative_of_contDiff (hf.of_le (by simp)) i)
    (fun i l => hasWeakSpatialDerivative_of_contDiff ((contDiff_dpart hf i).of_le (by simp)) l)

/-! ## The columns of `H ⊗ K + K ⊗ H + K ⊗ K` -/

/-- `W = H + ½ K`. -/
def Wf (D : BackgroundData) (u₀ : SpatialField) (τ : ℝ) : SpatialField :=
  heatProfile D.h D.udss τ + (1 / 2 : ℝ) • heatTail D u₀ τ

/-- Column `j` of `H ⊗ K + K ⊗ H + K ⊗ K`, written `B_j(W, K)`. -/
def colT (D : BackgroundData) (u₀ : SpatialField) (j : Fin 3) (τ : ℝ) : SpatialField :=
  bcol (symBilin j) (Wf D u₀ τ) (heatTail D u₀ τ)

theorem colT_eq (D : BackgroundData) (u₀ : SpatialField) (τ : ℝ) (j : Fin 3) :
    addColumns (symTensorColumns (heatProfile D.h D.udss τ) (heatTail D u₀ τ))
      (tensorColumns (heatTail D u₀ τ) (heatTail D u₀ τ)) j = colT D u₀ j τ := by
  funext y
  simp only [addColumns, symTensorColumns, tensorColumns, colT, bcol, symBilin_apply, Wf,
    Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  module

section Main

variable {D : BackgroundData} {u₀ : SpatialField}

theorem Wf_contDiff (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) (τ : ℝ) :
    ContDiff ℝ ∞ (Wf D u₀ τ) :=
  (heatProfile_contDiff hD.background τ).add
    (show ContDiff ℝ ∞ ((1 / 2 : ℝ) • heatTail D u₀ τ) from (hu.tail_smooth τ).const_smul (1 / 2 : ℝ))

theorem colT_contDiff (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) (j : Fin 3)
    (τ : ℝ) : ContDiff ℝ ∞ (colT D u₀ j τ) :=
  contDiff_bcol _ (Wf_contDiff hD hu τ) (hu.tail_smooth τ)

/-- Pointwise continuity in the phase of a family and its first two coordinate derivatives. -/
def PhaseCont (F : ℝ → SpatialField) : Prop :=
  ∀ (y : Space) (i l : Fin 3), Continuous (fun τ => F τ y) ∧
    Continuous (fun τ => dpart (F τ) i y) ∧ Continuous (fun τ => dpart (dpart (F τ) i) l y)

theorem phaseCont_H (hD : IsUnstableBackground D) : PhaseCont (heatProfile D.h D.udss) := by
  obtain ⟨C, hC⟩ := udss_invBound hD.background
  exact fun y i l => heatProfile_continuity hD.background.h_pos hC y i l

theorem phaseCont_K (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) :
    PhaseCont (heatTail D u₀) := by
  obtain ⟨r, hr, hd0⟩ := defect_vanishes hu
  obtain ⟨C, hC⟩ := defect_invBound hD hu hr hd0
  have e : heatTail D u₀ = heatProfile D.h (L09.smoothDefect r (u₀ - D.udss)) :=
    funext (heatTail_eq hd0)
  rw [e]
  exact fun y i l => heatProfile_continuity hD.background.h_pos hC y i l

theorem phaseCont_W (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) :
    PhaseCont (Wf D u₀) := by
  intro y i l
  obtain ⟨a0, a1, a2⟩ := phaseCont_H hD y i l
  obtain ⟨b0, b1, b2⟩ := phaseCont_K hD hu y i l
  have hH := heatProfile_contDiff hD.background
  have hK := hu.tail_smooth
  refine ⟨a0.add (b0.fun_const_smul (1 / 2 : ℝ)), ?_, ?_⟩
  · have e : (fun τ => dpart (Wf D u₀ τ) i y) = fun τ =>
        dpart (heatProfile D.h D.udss τ) i y + (1 / 2 : ℝ) • dpart (heatTail D u₀ τ) i y := by
      funext τ
      unfold Wf
      rw [dpart_add_smul ((hH τ).differentiable (by simp)) ((hK τ).differentiable (by simp))]
    rw [e]
    exact a1.add (b1.fun_const_smul (1 / 2 : ℝ))
  · have e : (fun τ => dpart (dpart (Wf D u₀ τ) i) l y) = fun τ =>
        dpart (dpart (heatProfile D.h D.udss τ) i) l y +
          (1 / 2 : ℝ) • dpart (dpart (heatTail D u₀ τ) i) l y := by
      funext τ
      unfold Wf
      rw [dpart_dpart_add_smul (hH τ) (hK τ)]
    rw [e]
    exact a2.add (b2.fun_const_smul (1 / 2 : ℝ))

theorem phaseCont_colT (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) (j : Fin 3) :
    PhaseCont (colT D u₀ j) := by
  intro y i l
  obtain ⟨w0, wi, wil⟩ := phaseCont_W hD hu y i l
  obtain ⟨-, wl, -⟩ := phaseCont_W hD hu y l l
  obtain ⟨k0, ki, kil⟩ := phaseCont_K hD hu y i l
  obtain ⟨-, kl, -⟩ := phaseCont_K hD hu y l l
  have hW := Wf_contDiff hD hu
  have hK := hu.tail_smooth
  have hB : Continuous (symBilin j) := (symBilin j).continuous
  refine ⟨(hB.comp w0).clm_apply k0, ?_, ?_⟩
  · have e : (fun τ => dpart (colT D u₀ j τ) i y) = fun τ =>
        symBilin j (dpart (Wf D u₀ τ) i y) (heatTail D u₀ τ y) +
          symBilin j (Wf D u₀ τ y) (dpart (heatTail D u₀ τ) i y) := by
      funext τ
      unfold colT
      rw [dpart_bcol _ ((hW τ).differentiable (by simp)) ((hK τ).differentiable (by simp))]
    rw [e]
    exact ((hB.comp wi).clm_apply k0).add ((hB.comp w0).clm_apply ki)
  · have e : (fun τ => dpart (dpart (colT D u₀ j τ) i) l y) = fun τ =>
        symBilin j (dpart (dpart (Wf D u₀ τ) i) l y) (heatTail D u₀ τ y) +
          symBilin j (dpart (Wf D u₀ τ) i y) (dpart (heatTail D u₀ τ) l y) +
        (symBilin j (dpart (Wf D u₀ τ) l y) (dpart (heatTail D u₀ τ) i y) +
          symBilin j (Wf D u₀ τ y) (dpart (dpart (heatTail D u₀ τ) i) l y)) := by
      funext τ
      unfold colT
      rw [dpart_dpart_bcol _ (hW τ) (hK τ)]
    rw [e]
    exact (((hB.comp wil).clm_apply k0).add ((hB.comp wi).clm_apply kl)).add
      (((hB.comp wl).clm_apply ki).add ((hB.comp w0).clm_apply kil))

/-- **The pointwise estimates** for `τ ≤ 0`, with `δ = e^{τ/4}`. -/
theorem colT_estimates (hD : IsUnstableBackground D) (hu : IsCompactDatum D u₀) :
    ∃ A : Fin 3 → ℝ, (∀ j, 0 ≤ A j) ∧ ∀ j τ, τ ≤ 0 →
      (∀ y, ‖colT D u₀ j τ y‖ ≤ A j / (1 + ‖y‖) ^ 2) ∧
      (∀ i y, ‖dpart (colT D u₀ j τ) i y‖ ≤ A j * psi (Real.exp (τ / 4)) y) ∧
      (∀ i l y, ‖dpart (dpart (colT D u₀ j τ) i) l y‖ ≤ A j * psi (Real.exp (τ / 4)) y) := by
  obtain ⟨CH, hCH0, hCH⟩ := heatProfile_decayW hD.background
  obtain ⟨CK, hCK0, hCK⟩ := tail_decayK hD hu
  refine ⟨fun j => 2 * ‖symBilin j‖ * (CH + CK) * CK, fun j => by positivity,
    fun j τ hτ => ?_⟩
  have hδ : 0 < Real.exp (τ / 4) := Real.exp_pos _
  have hδ1 : Real.exp (τ / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hKd := hCK τ hτ
  have hWd : DecayW (Wf D u₀ τ) (CH + CK) :=
    DecayW.add_smul (heatProfile_contDiff hD.background τ) (hu.tail_smooth τ)
      (by rw [abs_of_pos (by norm_num)]; norm_num) hCK0 (hCH τ) (hKd.decayW hCK0 hδ hδ1)
  obtain ⟨e0, e1, e2⟩ := bcol_estimates (symBilin j) (Wf_contDiff hD hu τ) (hu.tail_smooth τ)
    (by positivity) hCK0 hδ hδ1 hWd hKd
  refine ⟨fun y => (e0 y).trans ?_, fun i y => (e1 i y).trans le_rfl,
    fun i l y => (e2 i l y).trans le_rfl⟩
  have hB := norm_nonneg (symBilin j)
  have : 0 ≤ ‖symBilin j‖ * (CH + CK) * CK / (1 + ‖y‖) ^ 2 := by positivity
  have e : 2 * ‖symBilin j‖ * (CH + CK) * CK / (1 + ‖y‖) ^ 2 =
      2 * (‖symBilin j‖ * (CH + CK) * CK / (1 + ‖y‖) ^ 2) := by ring
  rw [e]
  linarith

end Main

end UnforcedLeray.ResidualForceHyp

namespace UnforcedLeray.Blueprint.L10

open UnforcedLeray.ResidualForceHyp SobolevGraph

/-- **`H-Residual` proved** (`paper/main.tex` lines 474–491, blueprint B0722 ingredient (2);
INF04, INF22, INF27): the physical residual `G_res(τ) = -𝔓 div(H ⊗ K + K ⊗ H + K ⊗ K)(τ)`
exists in `X = H¹_div` for `τ ≤ 0`, is continuous on `τ ≤ 0`, and `‖G_res(τ)‖_{H¹} ≤ Ce^{τ/2}`.
See the module docstring for the proof. -/
theorem residualForce : ResidualForce := by
  intro D hD u₀ hu
  obtain ⟨A, hA0, hA⟩ := colT_estimates hD hu
  have hsm : ∀ j τ, ContDiff ℝ ∞ (colT D u₀ j τ) := colT_contDiff hD hu
  have hmeas0 : ∀ j τ, AEStronglyMeasurable (colT D u₀ j τ) volume :=
    fun j τ => (hsm j τ).continuous.aestronglyMeasurable
  have hmeas1 : ∀ j τ i, AEStronglyMeasurable (dpart (colT D u₀ j τ) i) volume :=
    fun j τ i => (contDiff_dpart (hsm j τ) i).continuous.aestronglyMeasurable
  have hmeas2 : ∀ j τ i l, AEStronglyMeasurable (dpart (dpart (colT D u₀ j τ) i) l) volume :=
    fun j τ i l => (contDiff_dpart (contDiff_dpart (hsm j τ) i) l).continuous.aestronglyMeasurable
  have hm0 : ∀ j τ, τ ≤ 0 → MemLp (colT D u₀ j τ) 2 volume :=
    fun j τ hτ => memLp_of_bound (hmeas0 j τ) (hA j τ hτ).1
  have hL1 : ∀ j τ, τ ≤ 0 → ∀ i, MemLp (dpart (colT D u₀ j τ) i) 2 volume ∧
      l2Norm (dpart (colT D u₀ j τ) i) ≤ A j * cPsi * Real.exp (τ / 4) ^ 2 :=
    fun j τ hτ i => psi_L2 (hmeas1 j τ i) (hA0 j) (Real.exp_pos _) ((hA j τ hτ).2.1 i)
  have hL2 : ∀ j τ, τ ≤ 0 → ∀ i l, MemLp (dpart (dpart (colT D u₀ j τ) i) l) 2 volume ∧
      l2Norm (dpart (dpart (colT D u₀ j τ) i) l) ≤ A j * cPsi * Real.exp (τ / 4) ^ 2 :=
    fun j τ hτ i l => psi_L2 (hmeas2 j τ i l) (hA0 j) (Real.exp_pos _) ((hA j τ hτ).2.2 i l)
  -- the `H²` columns, built at the phase `min τ 0`
  set P : Fin 3 → ℝ → H2 := fun j τ =>
    colH2 (hsm j (min τ 0)) (hm0 j _ (min_le_right τ 0)) (fun i => (hL1 j _ (min_le_right τ 0) i).1)
      (fun i l => (hL2 j _ (min_le_right τ 0) i l).1) with hP
  -- domination for the continuity
  have hdom1 : ∀ j τ, τ ≤ 0 → ∀ i y, ‖dpart (colT D u₀ j τ) i y‖ ≤ (3 * A j) / (1 + ‖y‖) ^ 2 := by
    intro j τ hτ i y
    refine ((hA j τ hτ).2.1 i y).trans ?_
    have h := psi_le (Real.exp_pos (τ / 4)) (Real.exp_le_one_iff.mpr (by linarith)) y
    calc A j * psi (Real.exp (τ / 4)) y ≤ A j * (3 / (1 + ‖y‖) ^ 2) :=
          mul_le_mul_of_nonneg_left h (hA0 j)
      _ = 3 * A j / (1 + ‖y‖) ^ 2 := by ring
  have hdom2 : ∀ j τ, τ ≤ 0 → ∀ i l y,
      ‖dpart (dpart (colT D u₀ j τ) i) l y‖ ≤ (3 * A j) / (1 + ‖y‖) ^ 2 := by
    intro j τ hτ i l y
    refine ((hA j τ hτ).2.2 i l y).trans ?_
    have h := psi_le (Real.exp_pos (τ / 4)) (Real.exp_le_one_iff.mpr (by linarith)) y
    calc A j * psi (Real.exp (τ / 4)) y ≤ A j * (3 / (1 + ‖y‖) ^ 2) :=
          mul_le_mul_of_nonneg_left h (hA0 j)
      _ = 3 * A j / (1 + ‖y‖) ^ 2 := by ring
  have hmin : Continuous fun τ : ℝ => min τ 0 := continuous_id.min continuous_const
  have hminle : ∀ τ : ℝ, min τ 0 ∈ Iic (0 : ℝ) := fun τ => min_le_right τ 0
  have hPc : ∀ j, Continuous (P j) := by
    intro j
    rw [← continuousOn_univ, H2.continuousOn_iff_components]
    refine ⟨?_, fun i => ?_, fun i l => ?_⟩
    · have hv : ContinuousOn (fun σ => toL2 (colT D u₀ j σ)) (Iic 0) :=
        continuousOn_toL2 (A := A j) (fun σ _ => hmeas0 j σ) (fun σ hσ => (hA j σ hσ).1)
          (fun y => (phaseCont_colT hD hu j y 0 0).1.continuousOn)
      exact (hv.comp_continuous hmin hminle).continuousOn
    · have hv : ContinuousOn (fun σ => toL2 (dpart (colT D u₀ j σ) i)) (Iic 0) :=
        continuousOn_toL2 (A := 3 * A j) (fun σ _ => hmeas1 j σ i)
          (fun σ hσ => hdom1 j σ hσ i) (fun y => (phaseCont_colT hD hu j y i 0).2.1.continuousOn)
      exact (hv.comp_continuous hmin hminle).continuousOn
    · have hv : ContinuousOn (fun σ => toL2 (dpart (dpart (colT D u₀ j σ) i) l)) (Iic 0) :=
        continuousOn_toL2 (A := 3 * A j) (fun σ _ => hmeas2 j σ i l)
          (fun σ hσ => hdom2 j σ hσ i l)
          (fun y => (phaseCont_colT hD hu j y i l).2.2.continuousOn)
      exact (hv.comp_continuous hmin hminle).continuousOn
  have hGc : Continuous fun τ => minusLerayDivX (fun j => P j τ) := by
    rw [continuous_iff_continuousAt]
    intro τ₀
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hsum : Tendsto (fun τ => ∑ j : Fin 3, ‖P j τ - P j τ₀‖) (𝓝 τ₀) (𝓝 0) := by
      have h := tendsto_finset_sum (Finset.univ : Finset (Fin 3))
        (fun j _ => (tendsto_iff_norm_sub_tendsto_zero.mp ((hPc j).tendsto τ₀)))
      simpa using h
    refine squeeze_zero (fun τ => norm_nonneg _) (fun τ => ?_) hsum
    exact norm_minusLerayDivX_sub_le (fun j => P j τ) (fun j => P j τ₀)
  refine ⟨fun τ => minusLerayDivX (fun j => P j τ), ∑ j : Fin 3, 4 * A j * cPsi,
    hGc.continuousOn, fun τ hτ => ⟨?_, ?_⟩⟩
  · -- the weak identity `G_res(τ) = -𝔓 div(H ⊗ K + K ⊗ H + K ⊗ K)(τ)`
    have hmin0 : min τ 0 = τ := min_eq_left hτ
    refine isMinusLerayDiv_minusLerayDivX (fun j => P j τ) _ (fun j => ?_)
    rw [colT_eq]
    show (toL2 (colT D u₀ j (min τ 0)) : SpatialField) =ᵐ[volume] colT D u₀ j τ
    rw [hmin0]
    exact coeFn_toL2 (hm0 j τ hτ)
  · -- the bound `‖G_res(τ)‖_{H¹} ≤ C e^{τ/2}`
    have hmin0 : min τ 0 = τ := min_eq_left hτ
    have hδ2 : Real.exp (τ / 4) ^ 2 = Real.exp ((1 / 2) * τ) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    refine (norm_minusLerayDivX_le' _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    have b1 : ‖(P j τ).first j‖ ≤ A j * cPsi * Real.exp ((1 / 2) * τ) := by
      show ‖toL2 (dpart (colT D u₀ j (min τ 0)) j)‖ ≤ _
      rw [hmin0, norm_toL2 (hL1 j τ hτ j).1, ← hδ2]
      exact (hL1 j τ hτ j).2
    have b2 : ∀ i, ‖(P j τ).second j i‖ ≤ A j * cPsi * Real.exp ((1 / 2) * τ) := by
      intro i
      show ‖toL2 (dpart (dpart (colT D u₀ j (min τ 0)) j) i)‖ ≤ _
      rw [hmin0, norm_toL2 (hL2 j τ hτ j i).1, ← hδ2]
      exact (hL2 j τ hτ j i).2
    calc ‖(P j τ).first j‖ + ∑ i : Fin 3, ‖(P j τ).second j i‖
        ≤ A j * cPsi * Real.exp ((1 / 2) * τ) +
          ∑ _i : Fin 3, A j * cPsi * Real.exp ((1 / 2) * τ) :=
          add_le_add b1 (Finset.sum_le_sum fun i _ => b2 i)
      _ = 4 * A j * cPsi * Real.exp ((1 / 2) * τ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring

/-! Axiom audit (expected `[propext, Classical.choice, Quot.sound]`). -/
#print axioms residualForce

end UnforcedLeray.Blueprint.L10
