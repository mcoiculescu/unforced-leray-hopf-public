import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.PhasePrimitive.FarLeafOrg.Point.Kern

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg

open UnforcedLeray.Short.IIIa

/-- the path `l ↦ (ν(1-l²), y₀ - l z)` -/
def pth (ν : ℝ) (z y0 : Space) (l : ℝ) : ℝ × Space := (ν * (1 - l ^ 2), y0 - l • z)

/-- the coefficient `ω` -/
def om (a : ℂ) (ν : ℝ) (z y0 : Space) (i j k : Fin 3) (w : Space) (l : ℝ) : ℂ :=
  (l : ℂ) ^ a * ((Hk i j k w (pth ν z y0 l) : ℝ) : ℂ)

lemma pth_hasDeriv (ν : ℝ) (z y0 : Space) (l : ℝ) :
    HasDerivAt (pth ν z y0) (-(2 * ν * l), -z) l := by
  have h1 : HasDerivAt (fun l : ℝ => ν * (1 - l ^ 2)) (-(2 * ν * l)) l := by
    have := ((hasDerivAt_pow 2 l).const_sub 1).const_mul ν
    refine this.congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun l : ℝ => y0 - l • z) (-z) l := by
    have := (hasDerivAt_const l y0).sub ((hasDerivAt_id l).smul_const z)
    exact this.congr_deriv (by simp)
  exact h1.prodMk h2

lemma pth_pos {ν : ℝ} (hν : 0 < ν) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) : 0 < (pth ν 0 0 l).1 := by
  simp only [pth]
  have : l ^ 2 < 1 := by nlinarith [hl.1, hl.2]
  exact mul_pos hν (by linarith)

lemma pth_pos' {ν : ℝ} (hν : 0 < ν) (z y0 : Space) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    0 < (pth ν z y0 l).1 := pth_pos hν hl

lemma hdiff_at (i j k : Fin 3) (w : Space) {p : ℝ × Space} (hp : 0 < p.1) :
    DifferentiableAt ℝ (Hk i j k w) p :=
  ((Hk_cd i j k w).contDiffAt (isOpen_U.mem_nhds (show p ∈ {p : ℝ × Space | 0 < p.1} from hp))).differentiableAt
    (by norm_num)

lemma h_hasDeriv {ν : ℝ} (hν : 0 < ν) (z y0 : Space) (i j k : Fin 3) (w : Space) {l : ℝ}
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun l => Hk i j k w (pth ν z y0 l))
      (fderiv ℝ (Hk i j k w) (pth ν z y0 l) (-(2 * ν * l), -z)) l :=
  (hdiff_at i j k w (pth_pos' hν z y0 hl)).hasFDerivAt.comp_hasDerivAt l (pth_hasDeriv ν z y0 l)

lemma cpow_cd (a : ℂ) : ContDiffOn ℝ 1 (fun l : ℝ => (l : ℂ) ^ a) (Ioo 0 1) := by
  have heq : EqOn (fun l : ℝ => (l : ℂ) ^ a) (fun l : ℝ => Complex.exp (((Real.log l : ℝ) : ℂ) * a))
      (Ioo 0 1) := by
    intro l hl
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.1.ne'
    simp only
    rw [Complex.cpow_def_of_ne_zero hl0, Complex.ofReal_log hl.1.le, mul_comm]
  refine ContDiffOn.congr ?_ heq
  have h1 : ContDiffOn ℝ 1 (fun l : ℝ => Real.log l) (Ioo 0 1) :=
    (Real.contDiffOn_log (n := 1)).mono (fun l hl => by simpa using hl.1.ne')
  have h2 : ContDiffOn ℝ 1 (fun l : ℝ => ((Real.log l : ℝ) : ℂ)) (Ioo 0 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h1
  exact Complex.contDiff_exp.comp_contDiffOn (h2.mul contDiffOn_const)

lemma om_cd {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3) (w : Space) :
    ContDiffOn ℝ 1 (om a ν z y0 i j k w) (Ioo 0 1) := by
  have hpath : ContDiff ℝ 1 (pth ν z y0) := by
    unfold pth
    exact (contDiff_const.mul (contDiff_const.sub (contDiff_id.pow 2))).prodMk
      (contDiff_const.sub (contDiff_id.smul contDiff_const))
  have h1 : ContDiffOn ℝ 1 (fun l => Hk i j k w (pth ν z y0 l)) (Ioo 0 1) :=
    (Hk_cd i j k w).comp hpath.contDiffOn (fun l hl => pth_pos' hν z y0 hl)
  have h2 : ContDiffOn ℝ 1 (fun l => ((Hk i j k w (pth ν z y0 l) : ℝ) : ℂ)) (Ioo 0 1) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn h1
  exact (cpow_cd a).mul h2

lemma om_form {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3) (w : Space) {l : ℝ}
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    om a ν z y0 i j k w l + (l : ℂ) * deriv (om a ν z y0 i j k w) l =
      ((1 + a) * (l : ℂ) ^ a) * ((Hk i j k w (pth ν z y0 l) : ℝ) : ℂ) +
      ((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (Hk i j k w) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.1.ne'
  have hslit : (l : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simpa using hl.1
  have hc : HasDerivAt (fun l : ℝ => (l : ℂ) ^ a) (a * (l : ℂ) ^ (a - 1)) l :=
    ((Complex.hasStrictDerivAt_cpow_const hslit).hasDerivAt).comp_ofReal
  have hh := (h_hasDeriv hν z y0 i j k w hl).ofReal_comp
  have hm := hc.mul hh
  have : deriv (om a ν z y0 i j k w) l = _ := hm.deriv
  rw [this]
  have e : (l : ℂ) ^ (a - 1) = (l : ℂ) ^ a / l := by
    rw [Complex.cpow_sub _ _ hl0, Complex.cpow_one]
  rw [e]
  unfold om
  field_simp
  ring

lemma om_norm {ν : ℝ} (hν : 0 < ν) (a : ℂ) (z y0 : Space) (i j k : Fin 3) (w : Space) {l : ℝ}
    (hl : l ∈ Ioo (0 : ℝ) 1) :
    ‖om a ν z y0 i j k w l‖ = l ^ a.re * |Hk i j k w (pth ν z y0 l)| := by
  unfold om
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real, Real.norm_eq_abs]


lemma om_bounds (C : ℝ) (hC0 : 0 ≤ C)
    (hpk : ∀ (i j k : Fin 3) (s : ℝ), 0 < s → ∀ x : Space, x ≠ 0 → ∀ w v : Space,
      ‖Hk i j k w (s, x)‖ ≤ C * ‖w‖ * ‖x‖ ^ (-5 : ℝ) ∧
      ‖fderiv ℝ (Hk i j k w) (s, x) ((1 : ℝ), (0 : Space))‖ ≤ C * ‖w‖ * ‖x‖ ^ (-7 : ℝ) ∧
      ‖fderiv ℝ (Hk i j k w) (s, x) ((0 : ℝ), v)‖ ≤ C * ‖w‖ * ‖v‖ * ‖x‖ ^ (-6 : ℝ))
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) (a : ℂ) (z y0 : Space) (i j k : Fin 3) (w : Space)
    (hw : ‖w‖ ≤ 1) {g Z : ℝ} (hg : 0 < g) (hZ : ‖z‖ ≤ Z)
    (hgap : ∀ l ∈ Ioo (0 : ℝ) 1, g ≤ ‖y0 - l • z‖) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    ‖om a ν z y0 i j k w l‖ ≤ l ^ a.re * (C * g ^ (-5 : ℝ)) ∧
    ‖om a ν z y0 i j k w l + (l : ℂ) * deriv (om a ν z y0 i j k w) l‖ ≤
      l ^ a.re * (‖1 + a‖ * (C * g ^ (-5 : ℝ)) + 2 * C * g ^ (-7 : ℝ) + C * Z * g ^ (-6 : ℝ)) := by
  have hx : y0 - l • z ≠ 0 := by
    intro h0
    have := hgap l hl
    rw [h0, norm_zero] at this
    linarith
  have hs : 0 < ν * (1 - l ^ 2) := pth_pos' hν z y0 hl
  obtain ⟨b1, b2, b3⟩ := hpk i j k _ hs _ hx w (-z)
  have hxg : g ≤ ‖y0 - l • z‖ := hgap l hl
  have r5 : ‖y0 - l • z‖ ^ (-5 : ℝ) ≤ g ^ (-5 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have r6 : ‖y0 - l • z‖ ^ (-6 : ℝ) ≤ g ^ (-6 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have r7 : ‖y0 - l • z‖ ^ (-7 : ℝ) ≤ g ^ (-7 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hg hxg (by norm_num)
  have g5 : 0 ≤ g ^ (-5 : ℝ) := Real.rpow_nonneg hg.le _
  have g6 : 0 ≤ g ^ (-6 : ℝ) := Real.rpow_nonneg hg.le _
  have g7 : 0 ≤ g ^ (-7 : ℝ) := Real.rpow_nonneg hg.le _
  have hh : |Hk i j k w (pth ν z y0 l)| ≤ C * g ^ (-5 : ℝ) := by
    rw [← Real.norm_eq_abs]
    refine b1.trans ?_
    calc C * ‖w‖ * ‖y0 - l • z‖ ^ (-5 : ℝ) ≤ C * 1 * g ^ (-5 : ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hC0) r5 (Real.rpow_nonneg (norm_nonneg _) _)
            (by positivity)
      _ = _ := by ring
  have hp : pth ν z y0 l = (ν * (1 - l ^ 2), y0 - l • z) := rfl
  have hdec : (-(2 * ν * l), -z) = (-(2 * ν * l)) • ((1 : ℝ), (0 : Space)) + ((0 : ℝ), -z) := by
    ext <;> simp
  have hh' : |fderiv ℝ (Hk i j k w) (pth ν z y0 l) (-(2 * ν * l), -z)| ≤
      2 * C * g ^ (-7 : ℝ) + C * Z * g ^ (-6 : ℝ) := by
    rw [← Real.norm_eq_abs, hdec, map_add, map_smul, hp]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [smul_eq_mul, norm_mul]
      have e1 : ‖-(2 * ν * l)‖ ≤ 2 := by
        rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by have := hl.1; positivity)]
        nlinarith [hl.1, hl.2]
      calc _ ≤ 2 * (C * ‖w‖ * ‖y0 - l • z‖ ^ (-7 : ℝ)) :=
            mul_le_mul e1 b2 (norm_nonneg _) (by norm_num)
        _ ≤ 2 * (C * 1 * g ^ (-7 : ℝ)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hw hC0) r7
              (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)) (by norm_num)
        _ = _ := by ring
    · refine b3.trans ?_
      rw [norm_neg]
      calc C * ‖w‖ * ‖z‖ * ‖y0 - l • z‖ ^ (-6 : ℝ) ≤ C * 1 * Z * g ^ (-6 : ℝ) :=
            mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hw hC0) hZ (norm_nonneg _)
              (by positivity)) r6 (Real.rpow_nonneg (norm_nonneg _) _) (by
                have := (norm_nonneg z).trans hZ; positivity)
        _ = _ := by ring
  have hn := om_norm hν a z y0 i j k w hl
  have hlr : 0 ≤ l ^ a.re := Real.rpow_nonneg hl.1.le _
  refine ⟨?_, ?_⟩
  · rw [hn]; exact mul_le_mul_of_nonneg_left hh hlr
  · rw [om_form hν a z y0 i j k w hl]
    refine (norm_add_le _ _).trans ?_
    have n1 : ‖((1 + a) * (l : ℂ) ^ a) * ((Hk i j k w (pth ν z y0 l) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (‖1 + a‖ * (C * g ^ (-5 : ℝ))) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs]
      calc ‖1 + a‖ * l ^ a.re * |Hk i j k w (pth ν z y0 l)| ≤ ‖1 + a‖ * l ^ a.re * (C * g ^ (-5 : ℝ)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring
    have n2 : ‖((l : ℂ) * (l : ℂ) ^ a) *
        ((fderiv ℝ (Hk i j k w) (pth ν z y0 l) (-(2 * ν * l), -z) : ℝ) : ℂ)‖ ≤
        l ^ a.re * (2 * C * g ^ (-7 : ℝ) + C * Z * g ^ (-6 : ℝ)) := by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl.1, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl.1]
      calc l * l ^ a.re * |fderiv ℝ (Hk i j k w) (pth ν z y0 l) (-(2 * ν * l), -z)| ≤
            1 * l ^ a.re * (2 * C * g ^ (-7 : ℝ) + C * Z * g ^ (-6 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hl.2.le hlr) hh' (abs_nonneg _) (by positivity)
        _ = _ := by ring
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete.FarLeafOrg
end
