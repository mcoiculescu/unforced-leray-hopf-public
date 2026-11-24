import UnforcedLeray.Short.PartIIa.Sub.N02_4_5.Gen

/-!
# Part II-a, task `PartII-a:N02/4/5` (`NzConvGenHyp`): the domination hypotheses of the Green family

Source of record: `the November 2 reference manuscript`, lines 1713-1722 (the one-mode
potentials are convolutions with the Green kernel `G_k(t) = -e^{-|k||t|}/(2|k|)`).

Proof. `x ↦ G_k(t) h(x.1, x.2 - t)` equals `G_k(t) • h(· - (0, t))`. Its `x`-derivatives are
`G_k(t) • (iteratedFDeriv ℝ j h)(p - (0, t))`, which is continuous in `t` and bounded by
`‖G_k(t)‖ * M_j`, where `M_j` bounds `iteratedFDeriv ℝ j h` (continuous with compact support).
`G_k` is integrable on `ℝ` (two half-lines, `integrableOn_exp_mul_Ioi` and `integrableOn_exp_mul_Iic`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-- The order `j` lies below `∞`, where `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` (written out to avoid the
clash with the `ENNReal` notation `∞` opened in this file). -/
theorem nzgh_le (j : ℕ) : (j : WithTop ENat) ≤ ((⊤ : ENat) : WithTop ENat) := by
  exact_mod_cast le_top

/-- Shifting the second coordinate: `(x.1, x.2 - t) = x - (0, t)`. -/
theorem nzgh_shift (t : ℝ) (x : ℝ × ℝ) : (x.1, x.2 - t) = x - ((0 : ℝ), t) := by
  ext <;> simp

/-- Key identity: the `j`-th derivative of the family `x ↦ G_k(t) h(x.1, x.2 - t)` at `p`
is `G_k(t) • (iteratedFDeriv ℝ j h)(p - (0, t))`. -/
theorem nzgh_iter (k : ℝ) (h : ℝ × ℝ → ℂ) (hh : ContDiff ℝ ∞ h) (j : ℕ) (t : ℝ) (p : ℝ × ℝ) :
    iteratedFDeriv ℝ j (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t)) p
      = (nzGreen k t : ℂ) • iteratedFDeriv ℝ j h (p - ((0 : ℝ), t)) := by
  have hfun : (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t))
      = fun x : ℝ × ℝ => (nzGreen k t : ℂ) • h (x - ((0 : ℝ), t)) := by
    funext x
    rw [nzgh_shift t x, smul_eq_mul]
  have hsub : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z - ((0 : ℝ), t)) :=
    contDiff_id.sub contDiff_const
  have hcd : ContDiffAt ℝ j (fun z : ℝ × ℝ => h (z - ((0 : ℝ), t))) p :=
    ((hh.comp hsub).of_le (nzgh_le j)).contDiffAt
  rw [hfun, iteratedFDeriv_const_smul_apply' hcd, iteratedFDeriv_comp_sub]

/-- The Green constant `t ↦ G_k(t)`, as a complex scalar, is continuous. -/
theorem nzgh_green_cont (k : ℝ) : Continuous fun t : ℝ => (nzGreen k t : ℂ) := by
  have hreal : Continuous fun t : ℝ => nzGreen k t := by
    unfold nzGreen
    fun_prop
  exact Complex.continuous_ofReal.comp hreal

/-- The Green kernel `G_k` is integrable on `ℝ` for `k ≠ 0`. -/
theorem nzgh_green_integrable (k : ℝ) (hk : k ≠ 0) :
    Integrable (fun t : ℝ => nzGreen k t) volume := by
  have ha : 0 < |k| := abs_pos.mpr hk
  have hI1 : IntegrableOn (fun t : ℝ => Real.exp (-|k| * |t|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic ha 0).congr_fun ?_ measurableSet_Iic
    intro t ht
    have ht' : t ≤ 0 := Set.mem_Iic.mp ht
    simp only [abs_of_nonpos ht']
    congr 1
    ring
  have hI2 : IntegrableOn (fun t : ℝ => Real.exp (-|k| * |t|)) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht' : 0 < t := Set.mem_Ioi.mp ht
    simp only [abs_of_pos ht']
  have hE : Integrable (fun t : ℝ => Real.exp (-|k| * |t|)) volume := by
    have h12 := hI1.union hI2
    rwa [Set.Iic_union_Ioi, integrableOn_univ] at h12
  unfold nzGreen
  exact (hE.neg).div_const (2 * |k|)

/-- **`NzConvGenHyp`: domination hypotheses for the Green family.** -/
theorem nzConvGenHyp_proof : NzConvGenHyp := by
  intro k hk h hh hcs
  have hcont : ∀ j : ℕ, Continuous fun x : ℝ × ℝ => iteratedFDeriv ℝ j h x :=
    fun j => (hh.of_le (nzgh_le j)).continuous_iteratedFDeriv'
  refine ⟨?_, ?_, ?_⟩
  · -- (1) each `G t` is smooth
    refine ae_of_all _ (fun t => ?_)
    show ContDiff ℝ ∞ (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t))
    have hsub : ContDiff ℝ ∞ (fun z : ℝ × ℝ => z - ((0 : ℝ), t)) :=
      contDiff_id.sub contDiff_const
    have e : (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t))
        = fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x - ((0 : ℝ), t)) := by
      funext x
      rw [nzgh_shift t x]
    rw [e]
    exact contDiff_const.mul (hh.comp hsub)
  · -- (2) `t ↦ iteratedFDeriv ℝ j (G t) p` is a.e.-strongly measurable (it is continuous)
    intro j p
    show AEStronglyMeasurable (fun t : ℝ => iteratedFDeriv ℝ j
      (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t)) p) volume
    have hfun : (fun t : ℝ => iteratedFDeriv ℝ j
        (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t)) p)
        = fun t : ℝ => (nzGreen k t : ℂ) • iteratedFDeriv ℝ j h (p - ((0 : ℝ), t)) := by
      funext t
      exact nzgh_iter k h hh j t p
    rw [hfun]
    have hpt : Continuous fun t : ℝ => p - ((0 : ℝ), t) := by fun_prop
    exact Continuous.aestronglyMeasurable
      ((nzgh_green_cont k).smul ((hcont j).comp hpt))
  · -- (3) integrable domination bound `‖G_k(t)‖ * C` for each order `j`
    intro j
    obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support (hcont j)
      (hcs.iteratedFDeriv j)
    refine ⟨fun t : ℝ => ‖nzGreen k t‖ * C, ?_, ?_⟩
    · exact (nzgh_green_integrable k hk).norm.mul_const C
    · refine ae_of_all _ (fun t => fun p => ?_)
      show ‖iteratedFDeriv ℝ j (fun x : ℝ × ℝ => (nzGreen k t : ℂ) * h (x.1, x.2 - t)) p‖
        ≤ ‖nzGreen k t‖ * C
      rw [nzgh_iter k h hh j t p, norm_smul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

end UnforcedLeray.Short.PartIIa
