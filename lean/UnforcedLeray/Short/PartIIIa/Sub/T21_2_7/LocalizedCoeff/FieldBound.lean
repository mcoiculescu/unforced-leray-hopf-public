import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_1_7
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_1.LocalizedSourceBounds
import UnforcedLeray.Units.B0238.Partials

/-!
# `PartIII-a:T21/2/7/1/7/2`: field bounds `F_j = w ∂_jE(r)` (`locFieldBound`)

For `w ∈ X_{-m,c}` and `r ∈ [0, T]`, `|∂_jE(r)| ≤ C jb^{-(m+2)/2}` on the cell (`LadTrainBdd`),
so `|F_j| ≤ C |w| jb^{-m/2} · jb^{-1}`. The `L²` bound is the weighted norm of `w` times `C`
(since `jb^{-1} ≤ 1`); the `L¹` bound is Hölder against the `L²(cell)` factor `jb^{-1}`, which is
square integrable because `jb^{-2}` is integrable on `ℝ²`. The vorticity `E_c(r)` is `C¹`
(`contDiff_Vc`, `curl_eq_fderiv`), so its classical partials are continuous.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace FieldBoundAux

open UnforcedLeray.B0579

theorem one_le_jb (x : ℝ × ℝ) : 1 ≤ jb x := by
  have h1 := sq_nonneg x.1
  have h2 := sq_nonneg x.2
  unfold jb
  linarith

theorem jb_inv_le_one (x : ℝ × ℝ) : jb x ^ (-1 : ℝ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_jb x) (by norm_num)

/-- The weight `jb^{-1}` is square integrable on the cell. -/
theorem memLp_jb_inv (c : ℝ) :
    MemLp (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 (volume.restrict (cell c)) := by
  have hreal : MemLp (fun x : ℝ × ℝ => jb x ^ (-1 : ℝ)) 2 (volume.restrict (cell c)) := by
    refine (memLp_two_iff_integrable_sq_norm ?_).2 ?_
    · exact (continuous_jb_rpow (-1)).aestronglyMeasurable
    · have hfun : (fun x : ℝ × ℝ => ‖jb x ^ (-1 : ℝ)‖ ^ 2) = fun x => jb x ^ (-(2 : ℝ)) := by
        funext x
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (jb_pos x).le _), ← Real.rpow_natCast,
          ← Real.rpow_mul (jb_pos x).le]
        norm_num
      rw [hfun]
      exact integrable_jb_rpow_neg_two'.restrict
  exact hreal.ofReal

/-- Pointwise algebra: `|P| (B J) ≤ |C|` gives `|P| ≤ |C| B⁻¹ J⁻¹`. -/
theorem pt_bound {J B P C : ℝ} (hB : 0 < B) (hJ : 0 < J) (h : |P| * (B * J) ≤ |C|) :
    |P| ≤ |C| * (B⁻¹ * J⁻¹) := by
  have hBJ : 0 < B * J := mul_pos hB hJ
  have h' : |P| ≤ |C| / (B * J) := (le_div_iff₀ hBJ).2 h
  calc |P| ≤ |C| / (B * J) := h'
    _ = |C| * (B⁻¹ * J⁻¹) := by rw [div_eq_mul_inv, mul_inv]

/-- The core estimate for `F = w P` where `|P| ≤ K (jb^{-m/2} jb^{-1})` on the cell. -/
theorem core {c m : ℝ} {P : ℝ × ℝ → ℝ} (hPc : Continuous P) {K : ℝ} (hK : 0 ≤ K)
    (hP : ∀ x ∈ cell c, |P x| ≤ K * (jb x ^ (-m / 2) * jb x ^ (-1 : ℝ)))
    (w : Lp ℂ 2 (cellMeasure c (-m))) :
    IntegrableOn (fun x => w x * (P x : ℂ)) (cell c) ∧
      MemLp (fun x => w x * (P x : ℂ)) 2 (volume.restrict (cell c)) ∧
      eLpNorm (fun x => w x * (P x : ℂ)) 1 (volume.restrict (cell c)) +
        eLpNorm (fun x => w x * (P x : ℂ)) 2 (volume.restrict (cell c)) ≤
      ENNReal.ofReal K * (eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2
        (volume.restrict (cell c)) + 1) * ‖w‖ₑ := by
  set μ := volume.restrict (cell c) with hμ
  have hg1 : MemLp (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x) 2 μ :=
    PairContAux.memLp_scaled (Lp.memLp w)
  have hw1 : eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x) 2 μ = ‖w‖ₑ := by
    rw [Lp.enorm_def]
    exact (PairContAux.eLpNorm_cellMeasure_cx c (-m) (⇑w)).symm
  have hg2 : MemLp (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ := memLp_jb_inv c
  have hG2top : eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ ≠ ⊤ :=
    hg2.eLpNorm_lt_top.ne
  have hwtop : ‖w‖ₑ ≠ ⊤ := by
    rw [← hw1]; exact hg1.eLpNorm_lt_top.ne
  have hFm : AEStronglyMeasurable (fun x => w x * (P x : ℂ)) μ :=
    ((Lp.aestronglyMeasurable w).mono_ac (ac_cellMeasure c (-m))).mul
      (Complex.continuous_ofReal.comp hPc).aestronglyMeasurable
  -- pointwise bounds on the cell
  have hpt : ∀ᵐ x ∂μ, ‖w x * (P x : ℂ)‖ ≤
      ‖K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x * ((jb x ^ (-1 : ℝ) : ℝ) : ℂ))‖ := by
    refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
    have ht : 0 < jb x ^ (-m / 2) := Real.rpow_pos_of_pos (jb_pos x) _
    have hs : 0 < jb x ^ (-1 : ℝ) := Real.rpow_pos_of_pos (jb_pos x) _
    have hPx := hP x hx
    have e1 : ‖w x * (P x : ℂ)‖ = ‖w x‖ * |P x| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x * ((jb x ^ (-1 : ℝ) : ℝ) : ℂ))‖ =
        K * ((jb x ^ (-m / 2)) * ‖w x‖ * (jb x ^ (-1 : ℝ))) := by
      rw [norm_smul, Real.norm_of_nonneg hK, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_of_nonneg ht.le, Real.norm_of_nonneg hs.le]
    rw [e1, e2]
    calc ‖w x‖ * |P x| ≤ ‖w x‖ * (K * (jb x ^ (-m / 2) * jb x ^ (-1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hPx (norm_nonneg _)
      _ = K * ((jb x ^ (-m / 2)) * ‖w x‖ * (jb x ^ (-1 : ℝ))) := by ring
  -- the `L²` pointwise bound
  have hpt2 : ∀ᵐ x ∂μ, ‖w x * (P x : ℂ)‖ ≤ ‖K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x)‖ := by
    refine (ae_restrict_iff' (measurableSet_cell c)).2 (Eventually.of_forall fun x hx => ?_)
    have ht : 0 < jb x ^ (-m / 2) := Real.rpow_pos_of_pos (jb_pos x) _
    have hPx := hP x hx
    have hs1 : jb x ^ (-1 : ℝ) ≤ 1 := jb_inv_le_one x
    have e1 : ‖w x * (P x : ℂ)‖ = ‖w x‖ * |P x| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x)‖ = K * ((jb x ^ (-m / 2)) * ‖w x‖) := by
      rw [norm_smul, Real.norm_of_nonneg hK, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ht.le]
    rw [e1, e2]
    calc ‖w x‖ * |P x| ≤ ‖w x‖ * (K * (jb x ^ (-m / 2) * jb x ^ (-1 : ℝ))) :=
          mul_le_mul_of_nonneg_left hPx (norm_nonneg _)
      _ ≤ ‖w x‖ * (K * (jb x ^ (-m / 2) * 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hs1 ht.le) hK) (norm_nonneg _)
      _ = K * ((jb x ^ (-m / 2)) * ‖w x‖) := by ring
  -- Hölder for the `L¹` norm of `g₁ g₂`
  have hH : eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x *
      ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 1 μ ≤
      eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x) 2 μ *
        eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := μ) (p := 2) (q := 2) (r := 1)
      hg1.aestronglyMeasurable hg2.aestronglyMeasurable (fun a z : ℂ => a * z) 1
      (Eventually.of_forall fun x => by simp [nnnorm_mul])
    simpa only [ENNReal.coe_one, one_mul] using h
  have hL1 : eLpNorm (fun x => w x * (P x : ℂ)) 1 μ ≤
      eLpNorm (fun x => K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x * ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)))
        1 μ :=
    eLpNorm_mono_ae hpt
  have hL1' : eLpNorm (fun x => K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x *
      ((jb x ^ (-1 : ℝ) : ℝ) : ℂ))) 1 μ =
      ENNReal.ofReal K * eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x *
        ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 1 μ := by
    have := eLpNorm_const_smul K (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x *
      ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 1 μ
    simpa [Real.enorm_eq_ofReal hK, Pi.smul_def, smul_eq_mul] using this
  have hL2 : eLpNorm (fun x => w x * (P x : ℂ)) 2 μ ≤
      eLpNorm (fun x => K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x)) 2 μ :=
    eLpNorm_mono_ae hpt2
  have hL2' : eLpNorm (fun x => K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x)) 2 μ =
      ENNReal.ofReal K * eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x) 2 μ := by
    have := eLpNorm_const_smul K (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x) 2 μ
    simpa [Real.enorm_eq_ofReal hK, Pi.smul_def, smul_eq_mul] using this
  have hF1 : eLpNorm (fun x => w x * (P x : ℂ)) 1 μ ≤
      ENNReal.ofReal K * (‖w‖ₑ * eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ) := by
    calc eLpNorm (fun x => w x * (P x : ℂ)) 1 μ
        ≤ eLpNorm (fun x => K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x *
            ((jb x ^ (-1 : ℝ) : ℝ) : ℂ))) 1 μ := hL1
      _ = ENNReal.ofReal K * eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x *
            ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 1 μ := hL1'
      _ ≤ ENNReal.ofReal K * (eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x) 2 μ *
            eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ) :=
          mul_le_mul_of_nonneg_left hH zero_le
      _ = ENNReal.ofReal K * (‖w‖ₑ * eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ) := by
          rw [hw1]
  have hF2 : eLpNorm (fun x => w x * (P x : ℂ)) 2 μ ≤ ENNReal.ofReal K * ‖w‖ₑ := by
    calc eLpNorm (fun x => w x * (P x : ℂ)) 2 μ ≤
          eLpNorm (fun x => K • (((jb x ^ (-m / 2) : ℝ) : ℂ) * w x)) 2 μ := hL2
      _ = ENNReal.ofReal K * eLpNorm (fun x => ((jb x ^ (-m / 2) : ℝ) : ℂ) * w x) 2 μ := hL2'
      _ = ENNReal.ofReal K * ‖w‖ₑ := by rw [hw1]
  have hF1top : eLpNorm (fun x => w x * (P x : ℂ)) 1 μ < ⊤ :=
    lt_of_le_of_lt hF1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hwtop) (lt_top_iff_ne_top.2 hG2top)))
  have hF2top : eLpNorm (fun x => w x * (P x : ℂ)) 2 μ < ⊤ :=
    lt_of_le_of_lt hF2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hwtop))
  refine ⟨?_, ⟨hFm, hF2top⟩, ?_⟩
  · exact memLp_one_iff_integrable.1 ⟨hFm, hF1top⟩
  · calc eLpNorm (fun x => w x * (P x : ℂ)) 1 μ + eLpNorm (fun x => w x * (P x : ℂ)) 2 μ
        ≤ ENNReal.ofReal K * (‖w‖ₑ * eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ)
            + ENNReal.ofReal K * ‖w‖ₑ := add_le_add hF1 hF2
      _ = ENNReal.ofReal K * (eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2 μ + 1)
            * ‖w‖ₑ := by ring

end FieldBoundAux

open FieldBoundAux in
open UnforcedLeray.B0579 in
/-- **(L1) Field bounds** (SP 3052-3058): `F_j = w ∂_jE(r)` is in `L¹ ∩ L²(cell)` with a uniform
bound in terms of `‖w‖_{X_{-m,c}}`. -/
theorem locFieldBound (m : ℝ) (hm : 8 < m) : LocFieldBound m := by
  intro ν hν hν1 tr T C hT hb
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  have hG2top : eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2
      (volume.restrict (cell (ν ^ (-2 : ℝ)))) ≠ ⊤ :=
    (memLp_jb_inv (ν ^ (-2 : ℝ))).eLpNorm_lt_top.ne
  refine ⟨|C| * ((eLpNorm (fun x : ℝ × ℝ => ((jb x ^ (-1 : ℝ) : ℝ) : ℂ)) 2
      (volume.restrict (cell (ν ^ (-2 : ℝ))))).toReal + 1),
    mul_nonneg (abs_nonneg _) (add_nonneg ENNReal.toReal_nonneg zero_le_one), ?_⟩
  intro r hr w j
  have hv : ContDiff ℝ ∞ (tr.v r) := UnforcedLeray.B0238.contDiff_Vc tr hr.1
  have hv1 : ContDiff ℝ 1 (tr.v r) := hv.of_le (by exact_mod_cast le_top)
  have hEq : UnforcedLeray.B0238.Ec tr r = fun z =>
      fderiv ℝ (fun w => tr.v r w 1) z (1, 0) - fderiv ℝ (fun w => tr.v r w 0) z (0, 1) :=
    funext fun z => UnforcedLeray.B0238.curl_eq_fderiv hv1 z
  have hEc1 : ContDiff ℝ 1 (UnforcedLeray.B0238.Ec tr r) := by
    rw [hEq]
    exact (((UnforcedLeray.B0238.contDiff_comp_apply hv 1).fderiv_right
        (m := 1) (by norm_num)).clm_apply contDiff_const).sub
      (((UnforcedLeray.B0238.contDiff_comp_apply hv 0).fderiv_right
        (m := 1) (by norm_num)).clm_apply contDiff_const)
  have hPc : Continuous (pd j (UnforcedLeray.B0238.Ec tr r)) :=
    UnforcedLeray.B0238.continuous_fderiv_apply hEc1 (dir j)
  have hP : ∀ x ∈ cell (ν ^ (-2 : ℝ)),
      |pd j (UnforcedLeray.B0238.Ec tr r) x| ≤
        |C| * (jb x ^ (-m / 2) * jb x ^ (-1 : ℝ)) := by
    intro x hx
    have h1 := (hb r hr x hx).2 j
    have hJ : 0 < jb x := jb_pos x
    have hA : jb x ^ ((m + 2) / 2) = jb x ^ (m / 2) * jb x := by
      rw [show (m + 2) / 2 = m / 2 + 1 by ring, Real.rpow_add hJ, Real.rpow_one]
    have hneg : jb x ^ (-m / 2) = (jb x ^ (m / 2))⁻¹ := by
      rw [show -m / 2 = -(m / 2) by ring, Real.rpow_neg hJ.le]
    rw [hneg, Real.rpow_neg_one]
    apply pt_bound (Real.rpow_pos_of_pos hJ _) hJ
    have e : |pd j (UnforcedLeray.B0238.Ec tr r) x| * (jb x ^ (m / 2) * jb x) =
        jb x ^ ((m + 2) / 2) * |pd j (UnforcedLeray.B0238.Ec tr r) x| := by
      rw [hA]; ring
    rw [e]
    exact h1.trans (le_abs_self C)
  obtain ⟨h1, h2, h3⟩ := core hPc (abs_nonneg C) hP w
  refine ⟨h1, h2, ?_⟩
  rw [ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
    ENNReal.ofReal_toReal hG2top, ENNReal.ofReal_one]
  exact h3

end UnforcedLeray.Short.IIIa
