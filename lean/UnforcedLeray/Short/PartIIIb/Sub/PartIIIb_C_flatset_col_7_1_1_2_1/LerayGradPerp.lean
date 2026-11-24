import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayGradPerp.Integ
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember

/-!
# `∇u ∈ (solenoidalHC 0 c)ᗮ`: gradients of the chart potential (`SmoothGradPerp`)

Source `the November 2 reference manuscript` 1676-1677 (the orthogonal complement of
the solenoidal fields is the closure of the gradients). `(solenoidalHC 0 c)ᗮ` is the orthogonal
complement of the span of the gradients of profile tests, so `(solenoidalHC 0 c)ᗮ` is closed and
contains every `cgrad 0 Φ` (`gen_mem_orth`). It therefore suffices to approximate `∇u` in
`L²(measureH c)` by such gradients: the approximants are `Φ_n = chi(η/(n+1)) u`, which agree with
`u` near each point for `n` large, and whose gradients are dominated by `2|∇u| + errFn`
(`hnorm_le`, `errFn` of `Bounds.lean`), so dominated convergence applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open GradPerpCut

theorem cvec_flatGrad_eq_cgrad (u : Chart → ℝ) (p : Chart) :
    cvec (flatGrad u p) = UnforcedLeray.Short.PartIIa.cgrad 0 u p := by
  ext i
  fin_cases i
  · simp only [UnforcedLeray.Short.PartIIa.cgrad, UnforcedLeray.B0226.Deps_zero]
    simp [cvec, flatGrad]
  · simp only [UnforcedLeray.Short.PartIIa.cgrad]
    simp [cvec, flatGrad]

theorem isProfileTest_cutFn {c N : ℝ} {u : Chart → ℝ} (hN : 0 < N)
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hper : ∀ s q η, u (s, (q + c, η)) = u (s, (q, η)))
    {s0 s1 : ℝ} (hs0 : 0 < s0) (hsupp : ∀ p : Chart, u p ≠ 0 → p.1 ∈ Icc s0 s1) :
    UnforcedLeray.B0226.IsProfileTest c (cutFn N u) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (contDiff_chi.comp (contDiff_const.mul (contDiff_snd.comp contDiff_snd))).mul hu
  · intro p
    simp only [cutFn]
    rw [hper p.1 p.2.1 p.2.2]
  · refine ⟨s0, s1, 2 * N, hs0, fun p hp => ?_⟩
    have hu0 : u p ≠ 0 := by
      intro h
      apply hp
      simp [cutFn, h]
    refine ⟨hsupp p hu0, ?_⟩
    by_contra hcon
    push_neg at hcon
    have h3 : 3 ≤ (N⁻¹ * p.2.2) ^ 2 := by
      have hNN : N ^ 2 * (N⁻¹) ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hN.ne', one_pow]
      have hsq : 4 * N ^ 2 < p.2.2 ^ 2 := by
        nlinarith [sq_abs p.2.2, abs_nonneg p.2.2]
      have e1 : (N⁻¹ * p.2.2) ^ 2 = p.2.2 ^ 2 * (N⁻¹) ^ 2 := by ring
      rw [e1]
      nlinarith [sq_nonneg (N⁻¹)]
    apply hp
    simp [cutFn, chi_zero h3]

theorem eventually_cut_eq {N η : ℝ} (hN : 0 < N) (h : |η| < N) :
    chi (N⁻¹ * η) = 1 ∧ deriv chi (N⁻¹ * η) = 0 := by
  have habs : |N⁻¹ * η| < 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hN), inv_mul_lt_iff₀ hN]
    linarith
  have hsq : (N⁻¹ * η) ^ 2 < 1 := by
    nlinarith [sq_abs (N⁻¹ * η), abs_nonneg (N⁻¹ * η)]
  exact ⟨chi_one (by linarith), deriv_chi_of_lt (by linarith)⟩

theorem enorm_rpow_two_eq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

theorem smoothGradPerp : SmoothGradPerp := by
  intro c hc u hu hper hband hbd _hdecay hV
  obtain ⟨s0, s1, hs0, hsupp⟩ := hband
  obtain ⟨C, hC⟩ := hbd
  obtain ⟨B, hB⟩ := exists_bound_deriv_chi
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (0, 0, 0))
  have hu' : Differentiable ℝ u := hu.differentiable (by simp)
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hΦ : ∀ n : ℕ, UnforcedLeray.B0226.IsProfileTest c (cutFn ((n : ℝ) + 1) u) :=
    fun n => isProfileTest_cutFn (hNpos n) hu hper hs0 hsupp
  -- the approximants give generators of `(solenoidalHC 0 c)ᗮ`
  have hgen : ∀ n : ℕ,
      (UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad (ε := 0) (hΦ n)).toLp
        (UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u)) ∈
        (UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)ᗮ := fun n =>
    UnforcedLeray.Short.PartIIa.NearGradMemberAux.gen_mem_orth (hΦ n)
      (UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad (ε := 0) (hΦ n))
  -- pointwise domination of the gradients of the approximants
  have hnorm_le : ∀ (n : ℕ) (p : Chart),
      ‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p‖ ≤
        ‖cvec (flatGrad u p)‖ + errFn s0 s1 (3 * C * B) p := by
    intro n p
    have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hflat : cvec (flatGrad u p) = cvec ![UnforcedLeray.Axi.dQ u p, UnforcedLeray.Axi.dEta u p] :=
      rfl
    rw [cgrad_cutFn hu' p]
    rw [hflat]
    have h1 := norm_cvec_pair_le (χ := chi (((n : ℝ) + 1)⁻¹ * p.2.2)) (chi_nonneg _) (chi_le_one _)
      (a := UnforcedLeray.Axi.dQ u p) (b := UnforcedLeray.Axi.dEta u p)
      (e := u p * (deriv chi (((n : ℝ) + 1)⁻¹ * p.2.2) * ((n : ℝ) + 1)⁻¹))
    have h2 := abs_e_le_errFn (s0 := s0) (s1 := s1) (C := C) (B := B) (N := (n : ℝ) + 1) hN1
      hC0 hB0 hB p (hC p) (fun hne => (hsupp p hne))
    linarith
  -- eventual equality of the approximants with `u` at every point
  have hev : ∀ p : Chart, ∀ᶠ n : ℕ in atTop,
      UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p = cvec (flatGrad u p) := by
    intro p
    filter_upwards [Filter.eventually_ge_atTop ⌈|p.2.2|⌉₊] with n hn
    have hnr : (⌈|p.2.2|⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlt : |p.2.2| < (n : ℝ) + 1 := by
      have := Nat.le_ceil |p.2.2|
      linarith
    obtain ⟨hc1, hd0⟩ := eventually_cut_eq (hNpos n) hlt
    rw [cgrad_cutFn hu' p, hc1, hd0]
    simp [flatGrad]
  -- continuity and measurability
  have hcontF : Continuous (fun p : Chart => cvec (flatGrad u p)) := by
    have hfe : (fun p : Chart => cvec (flatGrad u p)) = UnforcedLeray.Short.PartIIa.cgrad 0 u :=
      funext (cvec_flatGrad_eq_cgrad u)
    rw [hfe]
    exact UnforcedLeray.Short.PartIIa.NearGradMemberAux.continuous_cgrad 0 hu
  -- integrability of the majorant
  have hR2 : Integrable (fun p : Chart => ‖cvec (flatGrad u p)‖ ^ 2)
      (UnforcedLeray.B0220.measureH c) :=
    (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).1 hV
  have herr2 : Integrable (fun p : Chart => errFn s0 s1 (3 * C * B) p ^ 2)
      (UnforcedLeray.B0220.measureH c) :=
    errFn_sq_integrable (c := c) hs0
  have hH : Integrable (fun p : Chart =>
      8 * ‖cvec (flatGrad u p)‖ ^ 2 + 2 * errFn s0 s1 (3 * C * B) p ^ 2)
      (UnforcedLeray.B0220.measureH c) :=
    (hR2.const_mul 8).add (herr2.const_mul 2)
  have hmeasF : ∀ n : ℕ, Measurable fun p : Chart =>
      ENNReal.ofReal (‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p -
        cvec (flatGrad u p)‖ ^ 2) := by
    intro n
    apply ENNReal.measurable_ofReal.comp
    exact (((UnforcedLeray.Short.PartIIa.NearGradMemberAux.continuous_cgrad 0 (hΦ n).smooth).sub
      hcontF).norm.pow 2).measurable
  -- domination by the integrable majorant
  have hbound : ∀ n : ℕ, (fun p : Chart =>
      ENNReal.ofReal (‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p -
        cvec (flatGrad u p)‖ ^ 2)) ≤ᵐ[UnforcedLeray.B0220.measureH c]
      fun p : Chart => ENNReal.ofReal (8 * ‖cvec (flatGrad u p)‖ ^ 2 +
        2 * errFn s0 s1 (3 * C * B) p ^ 2) := by
    intro n
    refine Filter.Eventually.of_forall fun p => ?_
    have hD : ‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p -
        cvec (flatGrad u p)‖ ≤ 2 * ‖cvec (flatGrad u p)‖ + errFn s0 s1 (3 * C * B) p := by
      calc ‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p -
            cvec (flatGrad u p)‖
          ≤ ‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p‖ +
            ‖cvec (flatGrad u p)‖ := norm_sub_le _ _
        _ ≤ (‖cvec (flatGrad u p)‖ + errFn s0 s1 (3 * C * B) p) + ‖cvec (flatGrad u p)‖ := by
            linarith [hnorm_le n p]
        _ = 2 * ‖cvec (flatGrad u p)‖ + errFn s0 s1 (3 * C * B) p := by ring
    have hnn : 0 ≤ ‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p -
        cvec (flatGrad u p)‖ := norm_nonneg _
    have hK : 0 ≤ 3 * C * B := mul_nonneg (mul_nonneg (by norm_num) hC0) hB0
    have he0 : 0 ≤ errFn s0 s1 (3 * C * B) p := errFn_nonneg hK p
    have hsq := pow_le_pow_left₀ hnn hD 2
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (2 * ‖cvec (flatGrad u p)‖ - errFn s0 s1 (3 * C * B) p)]
  -- pointwise convergence to zero
  have hpt : ∀ p : Chart, Tendsto (fun n : ℕ => ENNReal.ofReal
      (‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p -
        cvec (flatGrad u p)‖ ^ 2)) atTop (𝓝 0) := by
    intro p
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev p] with n hn
    rw [hn, sub_self, norm_zero]
    simp
  -- dominated convergence of the squared distances
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := UnforcedLeray.B0220.measureH c)
    (f := fun _ => (0 : ℝ≥0∞))
    (fun p : Chart => ENNReal.ofReal (8 * ‖cvec (flatGrad u p)‖ ^ 2 +
        2 * errFn s0 s1 (3 * C * B) p ^ 2))
    hmeasF hbound hH.lintegral_lt_top.ne (Filter.Eventually.of_forall hpt)
  simp only [lintegral_zero] at hdct
  -- conversion to `eLpNorm`
  have hEL : ∀ n : ℕ, eLpNorm (fun p : Chart =>
      UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p - cvec (flatGrad u p)) 2
      (UnforcedLeray.B0220.measureH c) =
      (∫⁻ p, ENNReal.ofReal (‖UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p -
        cvec (flatGrad u p)‖ ^ 2) ∂(UnforcedLeray.B0220.measureH c)) ^ (1 / 2 : ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr fun p => ?_
    exact enorm_rpow_two_eq _
  have hEL2 : Tendsto (fun n : ℕ => eLpNorm (fun p : Chart =>
      UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u) p - cvec (flatGrad u p)) 2
      (UnforcedLeray.B0220.measureH c)) atTop (𝓝 0) := by
    simp only [hEL]
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0).comp hdct
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h
  -- convergence in `L²`
  have hLp : Tendsto (fun n : ℕ =>
      (UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad (ε := 0) (hΦ n)).toLp
        (UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u))) atTop
      (𝓝 (hV.toLp (fun p : Chart => cvec (flatGrad u p)))) :=
    (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n : ℕ => UnforcedLeray.Short.PartIIa.cgrad 0 (cutFn ((n : ℝ) + 1) u))
      (fun n => UnforcedLeray.Short.PartIIa.NearGradMemberAux.memLp_cgrad (ε := 0) (hΦ n))
      (fun p : Chart => cvec (flatGrad u p)) hV).2 hEL2
  have hclosed := Submodule.isClosed_orthogonal (UnforcedLeray.Short.PartIIa.solenoidalHC 0 c)
  exact hclosed.mem_of_tendsto hLp (Filter.Eventually.of_forall hgen)

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
