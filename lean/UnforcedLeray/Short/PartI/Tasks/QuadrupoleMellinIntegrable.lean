import UnforcedLeray.Short.PartI.StatementsCanonical
import UnforcedLeray.Units.B0011
import UnforcedLeray.Units.B0012

/-!
# Part I, task `PartI:C12`: the quadrupole on `X_G` and integrability of the Mellin integrand

Source of record: `the November 2 reference manuscript`, lines 1155-1170
(Corollary `cor:short-mellin`; the weighted Cauchy-Schwarz bound on `X_G` is the first display
of its proof, and the asymptotics at zero and infinity are stated in its second display).

Proof outline.
* (i) `𝔐(f) = ∫₀^∞ r³ f₂(r) dr` is the `X_G` pairing with the fixed element
  `quadElt := (r ↦ r² G(r))` (`QMI.quadrupole_eq_inner`), hence `|𝔐(f)| ≤ ‖quadElt‖ ‖f‖`.
  Integrability of `r³ f₂` on `(0, ∞)` comes from the pointwise bound
  `r³|f₂| ≤ ½|f₂|² G⁻¹ r + ½ r⁵ G`, which is `½ r G⁻¹ (|f₂| - r² G)² ≥ 0`.
* (ii) Split `(0, ∞) = (0, 1] ∪ (1, B] ∪ (B, ∞)` with `B ≥ max(b, 1)` from the asymptotic.
  On `(0, 1]` the integrand is at most `θ^{Re μ + 1/2} · const`, integrable as `Re μ + 1/2 > -1`.
  On `(1, B]` it is continuous on a compact interval. On `(B, ∞)` the asymptotic gives
  `‖V θ‖ ≤ D e^{-Re λ θ} θ^{-Re κ}`, and `θ^n e^{-Re λ θ}` is integrable on `(B, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ComplexConjugate

namespace UnforcedLeray.Short.PartI.QMI

/-- The real profile `r ↦ r² G(r)`, viewed as a complex profile. -/
def quadWeight (r : ℝ) : ℂ := ((r ^ 2 * B0010.radialGaussianWeight r : ℝ) : ℂ)

theorem quadWeight_continuous : Continuous quadWeight :=
  Complex.continuous_ofReal.comp ((continuous_id.pow 2).mul B0012.continuous_radialGaussianWeight)

theorem quadWeight_memLp : MemLp quadWeight 2 B0010.xGMeasure := by
  have hr5 : IntegrableOn (fun r : ℝ => r ^ 5 * B0010.radialGaussianWeight r) (Ioi 0) :=
    B0011.integrableOn_pow_five_mul_gaussG
  have hint : IntegrableOn
      (fun r : ℝ => ‖quadWeight r‖ ^ 2 * ((B0010.radialGaussianWeight r)⁻¹ * r)) (Ioi 0) := by
    refine hr5.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hG : B0010.radialGaussianWeight r * (B0010.radialGaussianWeight r)⁻¹ = 1 :=
      mul_inv_cancel₀ (B0010.radialGaussianWeight_pos r).ne'
    have hnn : 0 ≤ r ^ 2 * B0010.radialGaussianWeight r :=
      mul_nonneg (sq_nonneg r) (B0010.radialGaussianWeight_pos r).le
    simp only [quadWeight]
    rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    linear_combination (-(r ^ 5 * B0010.radialGaussianWeight r)) * hG
  exact (B0010.memLp_iff_integrableOn (f₂ := quadWeight)
    quadWeight_continuous.aestronglyMeasurable).2 hint

/-- The fixed element of `X_G` representing the quadrupole. -/
def quadElt : B0010.XG := quadWeight_memLp.toLp quadWeight

/-- Elements of `X_G` are measurable on `(0, ∞)` with respect to Lebesgue measure. -/
theorem xg_aesm (f : B0010.XG) : AEStronglyMeasurable (f : ℝ → ℂ) (volume.restrict (Ioi 0)) := by
  have h1 : AEStronglyMeasurable (fun x : ℝ => ((B0010.xGDensity x : ℝ)) • (f : ℝ → ℂ) x)
      (volume.restrict (Ioi 0)) := by
    have hf : AEStronglyMeasurable (f : ℝ → ℂ)
        ((volume.restrict (Ioi 0)).withDensity fun x => (B0010.xGDensity x : ℝ≥0∞)) :=
      (Lp.memLp f).aestronglyMeasurable
    exact (aestronglyMeasurable_withDensity_iff B0010.measurable_xGDensity).1 hf
  have hinv : Measurable fun x : ℝ => ((B0010.xGDensity x : ℝ))⁻¹ :=
    B0010.measurable_xGDensity.coe_nnreal_real.inv
  have h2 : AEStronglyMeasurable
      (fun x : ℝ => ((B0010.xGDensity x : ℝ))⁻¹ • ((B0010.xGDensity x : ℝ) • (f : ℝ → ℂ) x))
      (volume.restrict (Ioi 0)) :=
    (hinv.aestronglyMeasurable (μ := volume.restrict (Ioi 0))).smul h1
  refine h2.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hd : (B0010.xGDensity x : ℝ) ≠ 0 := by
    rw [B0010.coe_xGDensity hx0]
    exact (mul_pos (inv_pos.2 (B0010.radialGaussianWeight_pos x)) hx0).ne'
  simp only [smul_smul, inv_mul_cancel₀ hd, one_smul]

/-- `r ↦ r³ f₂(r)` is integrable on `(0, ∞)` for every `f ∈ X_G` (weighted Cauchy-Schwarz). -/
theorem moment_integrable (f : B0010.XG) :
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ 3 * (f : ℝ → ℂ) r) (Ioi 0) := by
  have hm := xg_aesm f
  have hint : IntegrableOn
      (fun r : ℝ => ‖(f : ℝ → ℂ) r‖ ^ 2 * ((B0010.radialGaussianWeight r)⁻¹ * r)) (Ioi 0) :=
    (B0010.memLp_iff_integrableOn (f₂ := (f : ℝ → ℂ)) hm).1 (Lp.memLp f)
  have hr5 : IntegrableOn (fun r : ℝ => r ^ 5 * B0010.radialGaussianWeight r) (Ioi 0) :=
    B0011.integrableOn_pow_five_mul_gaussG
  have hg : Integrable (fun r : ℝ =>
      (1 / 2 : ℝ) * (‖(f : ℝ → ℂ) r‖ ^ 2 * ((B0010.radialGaussianWeight r)⁻¹ * r))
        + (1 / 2 : ℝ) * (r ^ 5 * B0010.radialGaussianWeight r)) (volume.restrict (Ioi 0)) :=
    (Integrable.const_mul hint (1 / 2 : ℝ)).add (Integrable.const_mul hr5 (1 / 2 : ℝ))
  refine Integrable.mono' hg ?_ ?_
  · exact (Continuous.aestronglyMeasurable
      (by fun_prop : Continuous fun r : ℝ => (r : ℂ) ^ 3)).mul hm
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr0 : (0 : ℝ) < r := hr
    have hG : 0 < B0010.radialGaussianWeight r := B0010.radialGaussianWeight_pos r
    have hu : B0010.radialGaussianWeight r * (B0010.radialGaussianWeight r)⁻¹ = 1 :=
      mul_inv_cancel₀ hG.ne'
    have hu0 : 0 < (B0010.radialGaussianWeight r)⁻¹ := inv_pos.2 hG
    have hnorm : ‖(r : ℂ) ^ 3 * (f : ℝ → ℂ) r‖ = r ^ 3 * ‖(f : ℝ → ℂ) r‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    have key : ‖(f : ℝ → ℂ) r‖ ^ 2 * ((B0010.radialGaussianWeight r)⁻¹ * r)
        - 2 * (r ^ 3 * ‖(f : ℝ → ℂ) r‖) + r ^ 5 * B0010.radialGaussianWeight r
        = r * (B0010.radialGaussianWeight r)⁻¹
          * (‖(f : ℝ → ℂ) r‖ - r ^ 2 * B0010.radialGaussianWeight r) ^ 2 := by
      linear_combination (2 * r ^ 3 * ‖(f : ℝ → ℂ) r‖ - r ^ 5 * B0010.radialGaussianWeight r) * hu
    have hnn : 0 ≤ r * (B0010.radialGaussianWeight r)⁻¹
        * (‖(f : ℝ → ℂ) r‖ - r ^ 2 * B0010.radialGaussianWeight r) ^ 2 :=
      mul_nonneg (mul_nonneg hr0.le hu0.le) (sq_nonneg _)
    show ‖(r : ℂ) ^ 3 * (f : ℝ → ℂ) r‖ ≤
      (1 / 2 : ℝ) * (‖(f : ℝ → ℂ) r‖ ^ 2 * ((B0010.radialGaussianWeight r)⁻¹ * r))
        + (1 / 2 : ℝ) * (r ^ 5 * B0010.radialGaussianWeight r)
    rw [hnorm]
    linarith [key, hnn]

/-- The quadrupole is the pairing with `quadElt` (`X_G` pairing, tex line 678). -/
theorem quadrupole_eq_pairing (f : B0010.XG) :
    Blueprint.Planar.quadrupole (f : ℝ → ℂ) = B0010.pairing f quadElt := by
  have key := B0010.pairing_toLp (f₂ := (f : ℝ → ℂ)) (g₂ := quadWeight) (Lp.memLp f)
    quadWeight_memLp
  rw [Lp.toLp_coeFn f (Lp.memLp f)] at key
  unfold quadElt
  rw [key]
  unfold Blueprint.Planar.quadrupole
  refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
  have hr0 : (0 : ℝ) < r := hr
  have hGc : ((B0010.radialGaussianWeight r : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (B0010.radialGaussianWeight_pos r).ne'
  have hGinv : ((B0010.radialGaussianWeight r : ℝ) : ℂ)
      * ((B0010.radialGaussianWeight r : ℝ) : ℂ)⁻¹ = 1 :=
    mul_inv_cancel₀ hGc
  simp only [quadWeight, Complex.conj_ofReal]
  push_cast
  linear_combination (-((r : ℂ) ^ 3 * (f : ℝ → ℂ) r)) * hGinv

/-- The quadrupole is an inner product with `quadElt`. -/
theorem quadrupole_eq_inner (f : B0010.XG) :
    Blueprint.Planar.quadrupole (f : ℝ → ℂ) = inner ℂ quadElt f := by
  rw [quadrupole_eq_pairing, B0010.pairing_eq_inner]

end UnforcedLeray.Short.PartI.QMI

namespace UnforcedLeray.Short.PartI

open QMI

/-- **(i)** The quadrupole is bounded on `X_G`, and `r ↦ r³ f₂(r)` is integrable on `(0, ∞)`. -/
theorem quadrupole_bounded : ∃ C, ∀ f : B0010.XG,
    IntegrableOn (fun r : ℝ => (r : ℂ) ^ 3 * (f : ℝ → ℂ) r) (Set.Ioi 0) ∧
      ‖Blueprint.Planar.quadrupole (f : ℝ → ℂ)‖ ≤ C * ‖f‖ := by
  refine ⟨‖QMI.quadElt‖, fun f => ⟨QMI.moment_integrable f, ?_⟩⟩
  rw [QMI.quadrupole_eq_inner]
  exact norm_inner_le_norm QMI.quadElt f

/-- **(ii)** Under the canonical solution and asymptotic hypotheses, the Mellin integrand
`θ ↦ θ^{μ+1/2} 𝔐(V_can(θ))` is integrable on `(0, ∞)` for `Re μ > -3/2`. -/
theorem mellin_integrable {lam kappa : ℂ} {q : B0010.XG} {V : ℝ → B0010.XG}
    (hV : IsCanonicalSolution V) (hA : HasCanonicalAsymptotic lam kappa q V)
    (hb : ∃ C, ∀ θ ∈ Set.Ioc (0 : ℝ) 1, ‖V θ‖ ≤ C)
    (hMq : Blueprint.Planar.quadrupole (q : ℝ → ℂ) ≠ 0) (hre : 0 < lam.re) :
    ∀ μ : ℂ, -(3 / 2) < μ.re → IntegrableOn
      (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2) * Blueprint.Planar.quadrupole (V θ : ℝ → ℂ))
      (Set.Ioi 0) := by
  intro μ hμ
  obtain ⟨Cb, hCb⟩ := hb
  obtain ⟨Ca, b, _hb0, hasym⟩ := hA
  have hVc : ContinuousOn V (Set.Ioi 0) := hV.smooth.continuousOn
  have hpow : ContinuousOn (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2)) (Set.Ioi 0) :=
    ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
      (fun θ hθ => Complex.mem_slitPlane_iff.2 (Or.inl (by simpa using hθ)))
  have hQc : ContinuousOn (fun θ : ℝ => Blueprint.Planar.quadrupole (V θ : ℝ → ℂ))
      (Set.Ioi 0) := by
    have hc : Continuous (fun x : B0010.XG => inner ℂ QMI.quadElt x) :=
      continuous_const.inner continuous_id
    have h1 : ContinuousOn (fun θ : ℝ => inner ℂ QMI.quadElt (V θ)) (Set.Ioi 0) :=
      hc.comp_continuousOn hVc
    exact h1.congr (fun θ _ => QMI.quadrupole_eq_inner (V θ))
  have hF : ContinuousOn
      (fun θ : ℝ => (θ : ℂ) ^ (μ + 1 / 2) * Blueprint.Planar.quadrupole (V θ : ℝ → ℂ))
      (Set.Ioi 0) := hpow.mul hQc
  obtain ⟨B, hB1, hBb⟩ : ∃ B : ℝ, 1 ≤ B ∧ b ≤ B :=
    ⟨max b 1, le_max_right _ _, le_max_left _ _⟩
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hdec : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ (Set.Ioc 1 B ∪ Set.Ioi B) := by
    rw [Ioc_union_Ioi_eq_Ioi hB1, Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [hdec]
  refine IntegrableOn.union ?_ (IntegrableOn.union ?_ ?_)
  · -- (0, 1]: the hypothesis `hb` bounds `V`, and `θ^{Re μ + 1/2}` is integrable
    have hs : (μ + 1 / 2).re = μ.re + 1 / 2 := by simp
    have hpowint : IntegrableOn (fun θ : ℝ => θ ^ (μ.re + 1 / 2)) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine Integrable.mono' (Integrable.mul_const hpowint (‖QMI.quadElt‖ * Cb)) ?_ ?_
    · exact (hF.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
      have hθ0 : (0 : ℝ) < θ := hθ.1
      have hQ : ‖Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)‖ ≤ ‖QMI.quadElt‖ * Cb := by
        rw [QMI.quadrupole_eq_inner]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hCb θ hθ) (norm_nonneg _))
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ0, hs]
      exact mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg hθ0.le _)
  · -- (1, B]: continuity on a compact interval
    have hsub : Set.Icc (1 : ℝ) B ⊆ Set.Ioi 0 :=
      fun θ hθ => lt_of_lt_of_le zero_lt_one (Set.mem_Icc.1 hθ).1
    exact ((hF.mono hsub).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · -- (B, ∞): the canonical asymptotic beats any power
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (μ.re + 1 / 2) - kappa.re ≤ (n : ℝ) :=
      ⟨⌈(μ.re + 1 / 2) - kappa.re⌉₊, Nat.le_ceil _⟩
    have hint : IntegrableOn (fun θ : ℝ => θ ^ (n : ℝ) * Real.exp (-lam.re * θ)) (Set.Ioi B) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n : ℝ)) (b := lam.re)
        (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n)) one_pos hre
      simp only [Real.rpow_one] at h
      exact h.mono_set (Set.Ioi_subset_Ioi hB0.le)
    have hbnd : ∀ θ : ℝ, B < θ →
        ‖(θ : ℂ) ^ (μ + 1 / 2) * Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)‖ ≤
          (‖QMI.quadElt‖ * (‖q‖ + |Ca|)) * (θ ^ (n : ℝ) * Real.exp (-lam.re * θ)) := by
      intro θ hθB
      have hθ0 : (0 : ℝ) < θ := lt_of_lt_of_le hB0 hθB.le
      have hθ1 : 1 ≤ θ := le_trans hB1 hθB.le
      have hθb : b ≤ θ := le_trans hBb hθB.le
      have hexpn : ‖Complex.exp (lam * θ)‖ = Real.exp (lam.re * θ) := by
        rw [Complex.norm_exp]
        congr 1
        simp
      have hWn : ‖Complex.exp (lam * θ) • ((θ : ℂ) ^ kappa • V θ)‖
          = Real.exp (lam.re * θ) * (θ ^ kappa.re * ‖V θ‖) := by
        rw [norm_smul, norm_smul, hexpn, Complex.norm_cpow_eq_rpow_re_of_pos hθ0]
      have hCa : Ca / θ ≤ |Ca| := by
        calc Ca / θ ≤ |Ca / θ| := le_abs_self _
          _ = |Ca| / θ := by rw [abs_div, abs_of_pos hθ0]
          _ ≤ |Ca| := div_le_self (abs_nonneg _) hθ1
      have hW := hasym θ hθb
      have hWle : ‖Complex.exp (lam * θ) • ((θ : ℂ) ^ kappa • V θ)‖ ≤ ‖q‖ + |Ca| := by
        have h1 := norm_sub_norm_le (Complex.exp (lam * θ) • ((θ : ℂ) ^ kappa • V θ)) q
        linarith
      have hWD : Real.exp (lam.re * θ) * (θ ^ kappa.re * ‖V θ‖) ≤ ‖q‖ + |Ca| := by
        rw [← hWn]
        exact hWle
      have hE : Real.exp (lam.re * θ) * Real.exp (-lam.re * θ) = 1 := by
        rw [← Real.exp_add, show lam.re * θ + -lam.re * θ = 0 by ring, Real.exp_zero]
      have hP : θ ^ kappa.re * (θ ^ kappa.re)⁻¹ = 1 :=
        mul_inv_cancel₀ (Real.rpow_pos_of_pos hθ0 _).ne'
      have hnonneg : 0 ≤ Real.exp (-lam.re * θ) * (θ ^ kappa.re)⁻¹ :=
        mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 (Real.rpow_nonneg hθ0.le _))
      have hVb : ‖V θ‖ ≤ (‖q‖ + |Ca|) * (Real.exp (-lam.re * θ) * (θ ^ kappa.re)⁻¹) := by
        have hid : (Real.exp (lam.re * θ) * Real.exp (-lam.re * θ))
            * (θ ^ kappa.re * (θ ^ kappa.re)⁻¹) = 1 := by
          rw [hE, hP, mul_one]
        calc ‖V θ‖ = (Real.exp (lam.re * θ) * (θ ^ kappa.re * ‖V θ‖))
              * (Real.exp (-lam.re * θ) * (θ ^ kappa.re)⁻¹) := by
              linear_combination (-‖V θ‖) * hid
          _ ≤ (‖q‖ + |Ca|) * (Real.exp (-lam.re * θ) * (θ ^ kappa.re)⁻¹) :=
              mul_le_mul_of_nonneg_right hWD hnonneg
      have hsP : θ ^ (μ.re + 1 / 2) ≤ θ ^ (n : ℝ) * θ ^ kappa.re := by
        rw [← Real.rpow_add hθ0]
        exact Real.rpow_le_rpow_of_exponent_le hθ1 (by linarith [hn])
      have hsPi : θ ^ (μ.re + 1 / 2) * (θ ^ kappa.re)⁻¹ ≤ θ ^ (n : ℝ) := by
        rw [← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hθ0 _)]
        exact hsP
      have hQ : ‖Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)‖ ≤ ‖QMI.quadElt‖ * ‖V θ‖ := by
        rw [QMI.quadrupole_eq_inner]
        exact norm_inner_le_norm _ _
      have hs : (μ + 1 / 2).re = μ.re + 1 / 2 := by simp
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ0, hs]
      calc θ ^ (μ.re + 1 / 2) * ‖Blueprint.Planar.quadrupole (V θ : ℝ → ℂ)‖
          ≤ θ ^ (μ.re + 1 / 2) * (‖QMI.quadElt‖ * ‖V θ‖) :=
            mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg hθ0.le _)
        _ ≤ θ ^ (μ.re + 1 / 2) * (‖QMI.quadElt‖
              * ((‖q‖ + |Ca|) * (Real.exp (-lam.re * θ) * (θ ^ kappa.re)⁻¹))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hVb (norm_nonneg _)) (Real.rpow_nonneg hθ0.le _)
        _ = (‖QMI.quadElt‖ * (‖q‖ + |Ca|))
              * ((θ ^ (μ.re + 1 / 2) * (θ ^ kappa.re)⁻¹) * Real.exp (-lam.re * θ)) := by ring
        _ ≤ (‖QMI.quadElt‖ * (‖q‖ + |Ca|)) * (θ ^ (n : ℝ) * Real.exp (-lam.re * θ)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsPi (Real.exp_pos _).le)
              (mul_nonneg (norm_nonneg _) (by positivity))
    refine Integrable.mono'
      (Integrable.const_mul hint (‖QMI.quadElt‖ * (‖q‖ + |Ca|))) ?_ ?_
    · exact (hF.mono (fun θ hθ => lt_of_lt_of_le hB0 (le_of_lt (Set.mem_Ioi.1 hθ)))).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with θ hθ
      exact hbnd θ (Set.mem_Ioi.1 hθ)

end UnforcedLeray.Short.PartI
