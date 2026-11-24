import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_2_1_2_3
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3

/-!
# `PartIII-a:T21/2/7/2/2/1/2/3/5`: the transport term `|I₃| ≤ (ν/4) ∑_k G_k^R + K`

Source: `the November 2 reference manuscript`
(SP) lines 3060-3067 (cutoff energy identity), 3044-3049 (weights), 3052-3058 (`|v| ≤ C`).

Pointwise, with `Φ = φ ρ`, `a_k = |∂_kΦ|`, `p = |Φ|`, `|v_j| ≤ C` on the cell (`LadTrainBdd`):
`|Re(Φ̄ v·∇Φ)| ≤ p C (a_0 + a_1)` and `C p a_k ≤ (ν/8) a_k² + (2C²/ν) p²`, so the integrand of
`I₃` is dominated by `(ν/8) ∑_k χ_R² jb^{-m} a_k² + (4C²/ν) χ_R² jb^{-m} p²`.
The first part is `(ν/8) ∑_k G_k^R`; the second is bounded by `(4C²/ν) E_0 ≤ (4C²/ν) max M 0`
since `χ_R ≤ 1` and `∫ jb^{-m} p² = ∫ |Φ|² dX_{-m,c} ≤ M`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace CutLowerTransportAux

lemma ladCut_nonneg' (R : ℝ) (x : ℝ × ℝ) : 0 ≤ ladCut R x :=
  Real.smoothTransition.nonneg _

lemma ladCut_le_one' (R : ℝ) (x : ℝ × ℝ) : ladCut R x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma ladCut_continuous' (R : ℝ) : Continuous (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.continuous.comp (by fun_prop)

/-- The transverse cutoff vanishes on the band `2R² ≤ η²`. -/
lemma ladCut_zero_of_band {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R ^ 2 ≤ x.2 ^ 2) :
    ladCut R x = 0 := by
  unfold ladCut
  apply Real.smoothTransition.zero_of_nonpos
  have h : 2 ≤ x.2 ^ 2 / R ^ 2 := (le_div_iff₀ (by positivity)).2 hx
  linarith

lemma pdCx_continuous' {Φ : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : Fin 2) :
    Continuous (pdCx k Φ) := by
  unfold pdCx
  exact (hΦ.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The slice `x ↦ φ ρ x` is smooth for `ρ ∈ [t, s)`. -/
lemma slice_contDiff {t s ρ : ℝ} {φ : ℝ → ℝ × ℝ → ℂ}
    (hφ : ContDiffOn ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) (Ico t s ×ˢ univ))
    (hρ : ρ ∈ Ico t s) : ContDiff ℝ ∞ (φ ρ) := by
  have h1 : ContDiffOn ℝ ∞ ((fun p : ℝ × (ℝ × ℝ) => φ p.1 p.2) ∘
      (fun x : ℝ × ℝ => ((ρ, x) : ℝ × (ℝ × ℝ)))) univ :=
    hφ.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨hρ, mem_univ x⟩)
  rw [contDiffOn_univ] at h1
  exact h1

lemma enorm_sq_eq' (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.ofReal_pow (norm_nonneg z), ofReal_norm_eq_enorm, ENNReal.rpow_two]

/-- A continuous function vanishing outside the band `2R² ≤ η²` is integrable on the cell. -/
lemma integrableOn_band {c R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (hv : ∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 → g x = 0) :
    IntegrableOn g (B0579.cell c) := by
  refine B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c (2 * R)) ?_
  intro x hx hK
  have hband : 2 * R ^ 2 ≤ x.2 ^ 2 := by
    by_contra h
    push Not at h
    apply hK
    apply B0579.mem_box_of_mem_cell hx
    nlinarith [sq_abs x.2, abs_nonneg x.2]
  exact hv x hband

/-- The energy at one age: `∫_{C_c} χ_R² jb^{-m}|ψ|² ≤ max M 0`, from `∫⁻ |ψ|² dX_{-m,c} ≤ M`. -/
lemma cutE0_le {c m R M : ℝ} {ψ : ℝ × ℝ → ℂ} (hmem : MemLp ψ 2 (B0579.cellMeasure c (-m)))
    (hl : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m)) ≤ ENNReal.ofReal M) :
    ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ x‖ ^ 2) ≤ max M 0 := by
  have hint : Integrable (fun x => ‖ψ x‖ ^ 2) (B0579.cellMeasure c (-m)) := by
    have h := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [Real.rpow_two] using h
  have hbound : ∫ x, ‖ψ x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) ≤ max M 0 := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg (‖ψ x‖))
      (hmem.aestronglyMeasurable.norm.pow 2)]
    apply ENNReal.toReal_le_of_le_ofReal (le_max_right M 0)
    calc ∫⁻ x, ENNReal.ofReal (‖ψ x‖ ^ 2) ∂(B0579.cellMeasure c (-m))
        = ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) ∂(B0579.cellMeasure c (-m)) :=
          lintegral_congr fun x => enorm_sq_eq' _
      _ ≤ ENNReal.ofReal M := hl
      _ ≤ ENNReal.ofReal (max M 0) := ENNReal.ofReal_le_ofReal (le_max_left M 0)
  have heq : ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖ψ x‖ ^ 2)
      = ∫ x, ladCut R x ^ 2 * ‖ψ x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) := by
    rw [integral_cellMeasure_eq]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    ring
  rw [heq]
  calc ∫ x, ladCut R x ^ 2 * ‖ψ x‖ ^ 2 ∂(B0579.cellMeasure c (-m))
      ≤ ∫ x, ‖ψ x‖ ^ 2 ∂(B0579.cellMeasure c (-m)) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hint
          (ae_of_all _ fun x => mul_le_of_le_one_left (sq_nonneg _)
            (pow_le_one₀ (ladCut_nonneg' R x) (ladCut_le_one' R x)))
    _ ≤ max M 0 := hbound

/-- Young's inequality with the constants used below: `C p a ≤ (ν/8) a² + (2C²/ν) p²`. -/
lemma amgm_aux {ν C p a : ℝ} (hν : 0 < ν) :
    C * p * a ≤ ν / 8 * a ^ 2 + 2 * C ^ 2 / ν * p ^ 2 := by
  have hν0 : ν ≠ 0 := hν.ne'
  have key : ν / 8 * a ^ 2 + 2 * C ^ 2 / ν * p ^ 2 - C * p * a
      = (ν * a - 4 * C * p) ^ 2 / (8 * ν) := by
    field_simp
    ring
  have hnn : 0 ≤ (ν * a - 4 * C * p) ^ 2 / (8 * ν) :=
    div_nonneg (sq_nonneg _) (by linarith)
  linarith

end CutLowerTransportAux

open CutLowerTransportAux in
/-- **(v) The transport term** (SP 3060-3067, `|v| ≤ C` on `[0, s]` by `LadTrainBdd`; Cauchy-Schwarz
and Young with `E_0 ≤ M`): `|I₃| ≤ (ν/4) ∑_k G_k^R + K`, `K` independent of `R ≥ 1` and `ρ`. -/
theorem cutLowerTransport (m : ℝ) : CutLowerTransport m := by
  intro ν tr t s G φ M hL
  obtain ⟨hctx, hm, hM⟩ := hL
  obtain ⟨hν, hν1, hb, ht, hts, hG, hφw, hφs⟩ := id hctx
  have hs0 : 0 ≤ s := by linarith
  obtain ⟨C, hC⟩ := hb s hs0
  refine ⟨4 * C ^ 2 / ν * max M 0, fun R hR ρ hρ => ?_⟩
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  have hρI : ρ ∈ Icc t s := ⟨hρ.1.le, hρ.2.le⟩
  have hρC : ρ ∈ Icc (0 : ℝ) s := ⟨le_trans ht hρ.1.le, hρ.2.le⟩
  have hρD : ρ ∈ Ico t s := ⟨hρ.1.le, hρ.2⟩
  have hΦ : ContDiff ℝ ∞ (φ ρ) := slice_contDiff hφs hρD
  have hmem : MemLp (φ ρ) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) (-m)) := hφw.memX ρ hρI
  have hE : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2) ≤ max M 0 :=
    cutE0_le (R := R) hmem (hM ρ hρI)
  -- pointwise domination of the integrand of `I₃`
  have hpt : ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)), ‖lowF3 tr m R φ ρ x‖ ≤
      ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)) +
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)) := by
    intro x hx
    have hv := (hC ρ hρC x hx).1
    have hT : ‖ladTransport tr ρ (φ ρ) x‖ ≤
        C * ‖pdCx 0 (φ ρ) x‖ + C * ‖pdCx 1 (φ ρ) x‖ := by
      unfold ladTransport
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_right (hv 0) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hv 1) (norm_nonneg _))
    have hRe : |((starRingEnd ℂ) (φ ρ x) * ladTransport tr ρ (φ ρ) x).re| ≤
        ‖φ ρ x‖ * (C * ‖pdCx 0 (φ ρ) x‖ + C * ‖pdCx 1 (φ ρ) x‖) := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left hT (norm_nonneg _)
    have hkey : ‖φ ρ x‖ * (C * ‖pdCx 0 (φ ρ) x‖ + C * ‖pdCx 1 (φ ρ) x‖) ≤
        ν / 8 * (‖pdCx 0 (φ ρ) x‖ ^ 2 + ‖pdCx 1 (φ ρ) x‖ ^ 2) + 4 * C ^ 2 / ν * ‖φ ρ x‖ ^ 2 := by
      have h0 := amgm_aux (C := C) (p := ‖φ ρ x‖) (a := ‖pdCx 0 (φ ρ) x‖) hν
      have h1 := amgm_aux (C := C) (p := ‖φ ρ x‖) (a := ‖pdCx 1 (φ ρ) x‖) hν
      calc ‖φ ρ x‖ * (C * ‖pdCx 0 (φ ρ) x‖ + C * ‖pdCx 1 (φ ρ) x‖)
          = C * ‖φ ρ x‖ * ‖pdCx 0 (φ ρ) x‖ + C * ‖φ ρ x‖ * ‖pdCx 1 (φ ρ) x‖ := by ring
        _ ≤ (ν / 8 * ‖pdCx 0 (φ ρ) x‖ ^ 2 + 2 * C ^ 2 / ν * ‖φ ρ x‖ ^ 2) +
            (ν / 8 * ‖pdCx 1 (φ ρ) x‖ ^ 2 + 2 * C ^ 2 / ν * ‖φ ρ x‖ ^ 2) := add_le_add h0 h1
        _ = ν / 8 * (‖pdCx 0 (φ ρ) x‖ ^ 2 + ‖pdCx 1 (φ ρ) x‖ ^ 2) +
            4 * C ^ 2 / ν * ‖φ ρ x‖ ^ 2 := by ring
    have hmain := hRe.trans hkey
    have hW : 0 ≤ ladCut R x ^ 2 * B0579.jb x ^ (-m) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (B0579.jb_pos x).le _)
    have hf : ‖lowF3 tr m R φ ρ x‖ = ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        |((starRingEnd ℂ) (φ ρ x) * ladTransport tr ρ (φ ρ) x).re|) := by
      unfold lowF3
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _)]
    rw [hf]
    calc ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
          |((starRingEnd ℂ) (φ ρ x) * ladTransport tr ρ (φ ρ) x).re|)
        = (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
            |((starRingEnd ℂ) (φ ρ x) * ladTransport tr ρ (φ ρ) x).re| := by ring
      _ ≤ (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
            (ν / 8 * (‖pdCx 0 (φ ρ) x‖ ^ 2 + ‖pdCx 1 (φ ρ) x‖ ^ 2) +
              4 * C ^ 2 / ν * ‖φ ρ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hmain hW
      _ = ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
            ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)) +
          4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)) := by ring
  -- integrability of the dominating pieces
  have hcont : ∀ k : Fin 2, Continuous (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (φ ρ) x‖ ^ 2)) := fun k =>
    ((ladCut_continuous' R).pow 2).mul
      ((B0579.continuous_jb_rpow (-m)).mul ((pdCx_continuous' hΦ k).norm.pow 2))
  have hcontE : Continuous (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)) :=
    ((ladCut_continuous' R).pow 2).mul
      ((B0579.continuous_jb_rpow (-m)).mul (hΦ.continuous.norm.pow 2))
  have hband : ∀ k : Fin 2, ∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 →
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx k (φ ρ) x‖ ^ 2) = 0 := by
    intro k x hx
    rw [ladCut_zero_of_band hR0 hx]
    simp
  have hbandE : ∀ x : ℝ × ℝ, 2 * R ^ 2 ≤ x.2 ^ 2 →
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2) = 0 := by
    intro x hx
    rw [ladCut_zero_of_band hR0 hx]
    simp
  have hI0 : IntegrableOn (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    integrableOn_band hR0 (hcont 0) (hband 0)
  have hI1 : IntegrableOn (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    integrableOn_band hR0 (hcont 1) (hband 1)
  have hIE : IntegrableOn (fun x : ℝ × ℝ =>
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2))
      (B0579.cell (ν ^ (-2 : ℝ))) :=
    integrableOn_band hR0 hcontE hbandE
  have hA : Integrable (fun x : ℝ × ℝ =>
      ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)))
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    (Integrable.add hI0 hI1).const_mul _
  have hB : Integrable (fun x : ℝ × ℝ =>
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)))
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    hIE.const_mul _
  have hgI : Integrable (fun x : ℝ × ℝ =>
      ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)) +
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)))
      (volume.restrict (B0579.cell (ν ^ (-2 : ℝ)))) :=
    hA.add hB
  have hsplit : ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      (ν / 8 * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 0 (φ ρ) x‖ ^ 2) +
        ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖pdCx 1 (φ ρ) x‖ ^ 2)) +
      4 * C ^ 2 / ν * (ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)))
      = ν / 8 * (cutGReal (ν ^ (-2 : ℝ)) m R φ 0 ρ + cutGReal (ν ^ (-2 : ℝ)) m R φ 1 ρ) +
        4 * C ^ 2 / ν * (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)) := by
    unfold cutGReal
    rw [integral_add hA hB, integral_const_mul, integral_const_mul, integral_add hI0 hI1]
  have hG0 : 0 ≤ cutGReal (ν ^ (-2 : ℝ)) m R φ 0 ρ := by
    unfold cutGReal
    refine setIntegral_nonneg (B0579.measurableSet_cell _) (fun x _ => ?_)
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
  have hG1 : 0 ≤ cutGReal (ν ^ (-2 : ℝ)) m R φ 1 ρ := by
    unfold cutGReal
    refine setIntegral_nonneg (B0579.measurableSet_cell _) (fun x _ => ?_)
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg (Real.rpow_nonneg (B0579.jb_pos x).le _) (sq_nonneg _))
  have hnorm := norm_integral_le_of_norm_le hgI
    ((ae_restrict_mem (B0579.measurableSet_cell _)).mono fun x hx => hpt x hx)
  have hpos : 0 ≤ ν * (cutGReal (ν ^ (-2 : ℝ)) m R φ 0 ρ + cutGReal (ν ^ (-2 : ℝ)) m R φ 1 ρ) :=
    mul_nonneg hν.le (add_nonneg hG0 hG1)
  have hK : 4 * C ^ 2 / ν * (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
      ladCut R x ^ 2 * (B0579.jb x ^ (-m) * ‖φ ρ x‖ ^ 2)) ≤ 4 * C ^ 2 / ν * max M 0 :=
    mul_le_mul_of_nonneg_left hE (div_nonneg (by positivity) hν.le)
  rw [← Real.norm_eq_abs, Fin.sum_univ_two]
  rw [hsplit] at hnorm
  nlinarith [hnorm, hpos, hK]

end UnforcedLeray.Short.IIIa
