import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_2
import UnforcedLeray.Short.PartIIb.Sub.T22.CylDecayBridge
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.TransportIBP
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.DiffusionBound.Common
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.Slice
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.WeakEqClassical.N1p.TimeDeriv

/-!
# Part II-b, task `PartII-b:T22/2/2/6`: differentiation of the pairing (`RtdHasDeriv`)

Source of record: `the November 2 reference manuscript`, lines 2074-2105.
For `r ∈ (s, t₁)` the pairing `F(r) = ∫_cell ω(r) φ(r)` is differentiated under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the open neighbourhood `Ioo s t₁`). The
pointwise derivative is `(νΔω - v·∇ω) φ + ω ∂_r φ`, from the `pde` field of `IsRegularCylFlow` and
the `r`-derivative of the test (`RtdTimeDeriv`). Domination on `Ioo s t₁` uses the uniform decay of
`ω` on the strip `|q| ≤ c/2` (`cell_decay 4`), the decay of `φ` (`decay 0`), the bound on `∂_r φ`
(hypothesis with weight `0`) and the bound on `v`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace UnforcedLeray.Short.IIb

/-- A term bounded by a sum `S` with `S J^4 ≤ C` is bounded by `C J^{-4}`. -/
theorem rtdHD_le_cell_inv {a S J C : ℝ} (hJ : 0 < J) (ha : a ≤ S) (hS : S * J ^ (4 : ℝ) ≤ C) :
    a ≤ C * J ^ (-4 : ℝ) := by
  have hJ4 : 0 < J ^ (4 : ℝ) := Real.rpow_pos_of_pos hJ _
  have hneg : J ^ (-4 : ℝ) = (J ^ (4 : ℝ))⁻¹ := Real.rpow_neg hJ.le 4
  have h1 : a * J ^ (4 : ℝ) ≤ C := le_trans (mul_le_mul_of_nonneg_right ha hJ4.le) hS
  rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hJ4]
  exact h1

theorem rtdHD_absmul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

/-- Pure real estimate for the integrand of the derivative of the pairing. -/
theorem rtdHD_pointwise (w0 p0 p1 L v0 v1 nu M phi dphi D C2 C3 : ℝ)
    (hw0 : |w0| ≤ D) (hp0 : |p0| ≤ D) (hp1 : |p1| ≤ D) (hL : |L| ≤ D)
    (hv0 : |v0| ≤ M) (hv1 : |v1| ≤ M) (hphi : |phi| ≤ C2) (hdphi : |dphi| ≤ C3) :
    |(nu * L - (v0 * p0 + v1 * p1)) * phi + w0 * dphi| ≤ ((|nu| + 2 * M) * C2 + C3) * D := by
  have hD : 0 ≤ D := le_trans (abs_nonneg w0) hw0
  have hM : 0 ≤ M := le_trans (abs_nonneg v0) hv0
  have hC2 : 0 ≤ C2 := le_trans (abs_nonneg phi) hphi
  have hC3 : 0 ≤ C3 := le_trans (abs_nonneg dphi) hdphi
  have e1 : |nu * L| ≤ |nu| * D := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hL (abs_nonneg nu)
  have e2 : |v0 * p0| ≤ M * D := by
    rw [abs_mul]; exact mul_le_mul hv0 hp0 (abs_nonneg _) hM
  have e3 : |v1 * p1| ≤ M * D := by
    rw [abs_mul]; exact mul_le_mul hv1 hp1 (abs_nonneg _) hM
  have h1 : |nu * L - (v0 * p0 + v1 * p1)| ≤ |nu * L| + |v0 * p0 + v1 * p1| := by
    have := abs_add_le (nu * L) (-(v0 * p0 + v1 * p1))
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have h2 := abs_add_le (v0 * p0) (v1 * p1)
  have hA : |nu * L - (v0 * p0 + v1 * p1)| ≤ (|nu| + 2 * M) * D := by
    have eq : (|nu| + 2 * M) * D = |nu| * D + 2 * (M * D) := by ring
    rw [eq]; linarith
  have k1 : |nu * L - (v0 * p0 + v1 * p1)| * |phi| ≤ ((|nu| + 2 * M) * D) * C2 :=
    mul_le_mul hA hphi (abs_nonneg _) (mul_nonneg (by linarith [abs_nonneg nu]) hD)
  have k2 : |w0| * |dphi| ≤ D * C3 := mul_le_mul hw0 hdphi (abs_nonneg _) hD
  have hsplit := abs_add_le ((nu * L - (v0 * p0 + v1 * p1)) * phi) (w0 * dphi)
  rw [abs_mul, abs_mul] at hsplit
  have eq2 : ((|nu| + 2 * M) * D) * C2 + D * C3 = ((|nu| + 2 * M) * C2 + C3) * D := by ring
  linarith [hsplit, k1, k2, eq2]

/-- **Task `PartII-b:T22/2/2/6` (`RtdHasDeriv`).** Differentiation of the pairing
`r ↦ ∫_cell ω(r) φ(r)` on `(s, t₁)`, and integrability of `ω ∂_r φ`. -/
theorem rtdHasDeriv : UnforcedLeray.Short.IIb.RtdHasDeriv := by
  intro ν c tr s T t₁ ω φ hc hs hst ht₁ hω hφ hφr hM r hr
  obtain ⟨M, hMb⟩ := hM
  obtain ⟨C1, hC1⟩ := hω.cell_decay 4
  obtain ⟨C2, hC2⟩ := hφ.decay 0
  obtain ⟨C3, hC3⟩ := hφr 0
  have hsub : ∀ q ∈ Ioo s t₁, q ∈ Icc s T :=
    fun q hq => ⟨hq.1.le, (hq.2.trans_le ht₁).le⟩
  -- decay of ω and its first and second derivatives on the strip
  have hωD : ∀ σ ∈ Icc s T, ∀ x : B0579.Plane, |x.1| ≤ c / 2 →
      |ω σ x| ≤ C1 * B0579.jb x ^ (-4 : ℝ) ∧
      |B0579.pd 0 (ω σ) x| ≤ C1 * B0579.jb x ^ (-4 : ℝ) ∧
      |B0579.pd 1 (ω σ) x| ≤ C1 * B0579.jb x ^ (-4 : ℝ) ∧
      |lapP (ω σ) x| ≤ C1 * B0579.jb x ^ (-4 : ℝ) := by
    intro σ hσ x hx
    have h := hC1 σ hσ x hx
    have hJ := B0579.jb_pos x
    have a1 : |ω σ x| ≤ |ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x|
        + |lapP (ω σ) x| := by
      linarith [abs_nonneg (B0579.pd 0 (ω σ) x), abs_nonneg (B0579.pd 1 (ω σ) x),
        abs_nonneg (lapP (ω σ) x)]
    have a2 : |B0579.pd 0 (ω σ) x| ≤ |ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x|
        + |lapP (ω σ) x| := by
      linarith [abs_nonneg (ω σ x), abs_nonneg (B0579.pd 1 (ω σ) x),
        abs_nonneg (lapP (ω σ) x)]
    have a3 : |B0579.pd 1 (ω σ) x| ≤ |ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x|
        + |lapP (ω σ) x| := by
      linarith [abs_nonneg (ω σ x), abs_nonneg (B0579.pd 0 (ω σ) x),
        abs_nonneg (lapP (ω σ) x)]
    have a4 : |lapP (ω σ) x| ≤ |ω σ x| + |B0579.pd 0 (ω σ) x| + |B0579.pd 1 (ω σ) x|
        + |lapP (ω σ) x| := by
      linarith [abs_nonneg (ω σ x), abs_nonneg (B0579.pd 0 (ω σ) x),
        abs_nonneg (B0579.pd 1 (ω σ) x)]
    exact ⟨rtdHD_le_cell_inv hJ a1 h, rtdHD_le_cell_inv hJ a2 h,
      rtdHD_le_cell_inv hJ a3 h, rtdHD_le_cell_inv hJ a4 h⟩
  -- bounds on the test and on its age derivative
  have hφb : ∀ q ∈ Icc s t₁, ∀ x : B0579.Plane, |φ q x| ≤ C2 := by
    intro q hq x
    have h := hC2 q hq x
    rw [Real.rpow_zero, mul_one] at h
    linarith [abs_nonneg (B0579.pd 0 (φ q) x), abs_nonneg (B0579.pd 1 (φ q) x),
      abs_nonneg (lapP (φ q) x)]
  have hdφb : ∀ q ∈ Ioo s t₁, ∀ x : B0579.Plane, |deriv (fun q' => φ q' x) q| ≤ C3 := by
    intro q hq x
    have h := hC3 q hq x
    rw [Real.rpow_zero, mul_one] at h
    exact h
  -- regularity and derivatives
  have hωc : ∀ σ ∈ Icc s T, Continuous (ω σ) :=
    fun σ hσ => (hω.slice σ hσ).smooth.continuous
  have hφc : ∀ q ∈ Ioo s t₁, Continuous (φ q) :=
    fun q hq => (rtdSlice c s t₁ φ hφ q ⟨hq.1.le, hq.2.le⟩).smooth.continuous
  have hdφ_at : ∀ q ∈ Ioo s t₁, ∀ x : B0579.Plane,
      HasDerivAt (fun q' => φ q' x) (deriv (fun q' => φ q' x) q) q :=
    fun q hq x => (rtdTimeDeriv c s t₁ φ hφ q hq).1 x
  have hdφ_cont : ∀ q ∈ Ioo s t₁,
      Continuous (fun x : B0579.Plane => deriv (fun q' => φ q' x) q) :=
    fun q hq => (rtdTimeDeriv c s t₁ φ hφ q hq).2
  have hωd : ∀ σ ∈ Ioo s t₁, ∀ x : B0579.Plane,
      HasDerivAt (fun q => ω q x)
        (ν * lapP (ω σ) x - (tr.v σ x 0 * B0579.pd 0 (ω σ) x + tr.v σ x 1 * B0579.pd 1 (ω σ) x))
        σ := by
    intro σ hσ x
    exact (hω.pde σ (hsub σ hσ) x).hasDerivAt (Icc_mem_nhds hσ.1 (hσ.2.trans_le ht₁))
  have hcontG : ∀ q ∈ Ioo s t₁, Continuous (fun x : B0579.Plane =>
      (ν * lapP (ω q) x - (tr.v q x 0 * B0579.pd 0 (ω q) x + tr.v q x 1 * B0579.pd 1 (ω q) x))
        * φ q x + ω q x * deriv (fun q' => φ q' x) q) := by
    intro q hq
    have hq0 : 0 ≤ q := le_trans hs hq.1.le
    have hv : ContDiff ℝ 1 (tr.v q) :=
      TransportIBP.contDiff_one_of_top (TransportIBP.contDiff_slice tr hq0)
    have hv0 : Continuous (fun x : B0579.Plane => tr.v q x 0) :=
      ((EuclideanSpace.proj (0 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
    have hv1 : Continuous (fun x : B0579.Plane => tr.v q x 1) :=
      ((EuclideanSpace.proj (1 : Fin 2) : UnforcedLeray.Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hv).continuous
    have hg := hω.slice q (hsub q hq)
    have hL : Continuous (lapP (ω q)) := DbCommon.continuous_lapP hg.smooth
    have hp0 : Continuous (B0579.pd 0 (ω q)) := DbCommon.continuous_pd_of_c2 hg.smooth 0
    have hp1 : Continuous (B0579.pd 1 (ω q)) := DbCommon.continuous_pd_of_c2 hg.smooth 1
    have hA : Continuous (fun x : B0579.Plane =>
        ν * lapP (ω q) x - (tr.v q x 0 * B0579.pd 0 (ω q) x + tr.v q x 1 * B0579.pd 1 (ω q) x)) :=
      (continuous_const.mul hL).sub ((hv0.mul hp0).add (hv1.mul hp1))
    exact (hA.mul (hφc q hq)).add ((hωc q (hsub q hq)).mul (hdφ_cont q hq))
  -- the four hypotheses of the differentiation lemma
  have hF_meas : ∀ᶠ q in 𝓝 r,
      AEStronglyMeasurable (fun x => ω q x * φ q x) (volume.restrict (B0579.cell c)) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with q hq
    exact ((hωc q (hsub q hq)).mul (hφc q hq)).aestronglyMeasurable
  have hF_int : Integrable (fun x => ω r x * φ r x) (volume.restrict (B0579.cell c)) := by
    refine DbCommon.cell_integrable_of_bound (Q := fun x => (C1 * C2) * B0579.jb x ^ (-4 : ℝ))
      (DbCommon.integrable_jb_neg4.const_mul (C1 * C2)).integrableOn
      ((hωc r (hsub r hr)).mul (hφc r hr)) (fun x hx => ?_)
    show ‖ω r x * φ r x‖ ≤ (C1 * C2) * B0579.jb x ^ (-4 : ℝ)
    rw [Real.norm_eq_abs]
    have h := rtdHD_absmul_le (hωD r (hsub r hr) x hx).1 (hφb r ⟨hr.1.le, hr.2.le⟩ x)
    exact le_trans h (le_of_eq (by ring))
  have hF'_meas : AEStronglyMeasurable (fun x : B0579.Plane =>
      (ν * lapP (ω r) x - (tr.v r x 0 * B0579.pd 0 (ω r) x + tr.v r x 1 * B0579.pd 1 (ω r) x))
        * φ r x + ω r x * deriv (fun q' => φ q' x) r) (volume.restrict (B0579.cell c)) :=
    (hcontG r hr).aestronglyMeasurable
  have h_bound : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ q ∈ Ioo s t₁,
      ‖(ν * lapP (ω q) a - (tr.v q a 0 * B0579.pd 0 (ω q) a + tr.v q a 1 * B0579.pd 1 (ω q) a))
          * φ q a + ω q a * deriv (fun q' => φ q' a) q‖
        ≤ (((|ν| + 2 * M) * C2 + C3) * C1) * B0579.jb a ^ (-4 : ℝ) := by
    refine (ae_restrict_iff' (B0579.measurableSet_cell c)).2 (ae_of_all _ fun a ha => ?_)
    intro q hq
    have hx := abs_fst_le_of_mem_cell ha
    have hqs := hsub q hq
    obtain ⟨h1, h2, h3, h4⟩ := hωD q hqs a hx
    have hv0 : |tr.v q a 0| ≤ M := by linarith [hMb q hqs a, abs_nonneg (tr.v q a 1)]
    have hv1 : |tr.v q a 1| ≤ M := by linarith [hMb q hqs a, abs_nonneg (tr.v q a 0)]
    have hpt := rtdHD_pointwise (ω q a) (B0579.pd 0 (ω q) a) (B0579.pd 1 (ω q) a)
      (lapP (ω q) a) (tr.v q a 0) (tr.v q a 1) ν M (φ q a) (deriv (fun q' => φ q' a) q)
      (C1 * B0579.jb a ^ (-4 : ℝ)) C2 C3 h1 h2 h3 h4 hv0 hv1
      (hφb q ⟨hq.1.le, hq.2.le⟩ a) (hdφb q hq a)
    rw [Real.norm_eq_abs]
    calc _ ≤ ((|ν| + 2 * M) * C2 + C3) * (C1 * B0579.jb a ^ (-4 : ℝ)) := hpt
      _ = (((|ν| + 2 * M) * C2 + C3) * C1) * B0579.jb a ^ (-4 : ℝ) := by ring
  have hbI : Integrable (fun x : B0579.Plane =>
      (((|ν| + 2 * M) * C2 + C3) * C1) * B0579.jb x ^ (-4 : ℝ))
      (volume.restrict (B0579.cell c)) :=
    (DbCommon.integrable_jb_neg4.const_mul _).integrableOn
  have h_diff : ∀ᵐ a ∂(volume.restrict (B0579.cell c)), ∀ q ∈ Ioo s t₁,
      HasDerivAt (fun q' => ω q' a * φ q' a)
        ((ν * lapP (ω q) a - (tr.v q a 0 * B0579.pd 0 (ω q) a + tr.v q a 1 * B0579.pd 1 (ω q) a))
          * φ q a + ω q a * deriv (fun q' => φ q' a) q) q :=
    ae_of_all _ fun a q hq => (hωd q hq a).mul (hdφ_at q hq a)
  have hlem := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (B0579.cell c))
    (F := fun q x => ω q x * φ q x)
    (F' := fun q x => (ν * lapP (ω q) x - (tr.v q x 0 * B0579.pd 0 (ω q) x
        + tr.v q x 1 * B0579.pd 1 (ω q) x)) * φ q x + ω q x * deriv (fun q' => φ q' x) q)
    (bound := fun x => (((|ν| + 2 * M) * C2 + C3) * C1) * B0579.jb x ^ (-4 : ℝ))
    (Ioo_mem_nhds hr.1 hr.2) hF_meas hF_int hF'_meas h_bound hbI h_diff
  refine ⟨?_, hlem.2⟩
  -- integrability of the first conjunct `ω ∂_r φ`
  refine DbCommon.cell_integrable_of_bound (Q := fun x => (C1 * C3) * B0579.jb x ^ (-4 : ℝ))
    (DbCommon.integrable_jb_neg4.const_mul (C1 * C3)).integrableOn
    ((hωc r (hsub r hr)).mul (hdφ_cont r hr)) (fun x hx => ?_)
  show ‖ω r x * deriv (fun q' => φ q' x) r‖ ≤ (C1 * C3) * B0579.jb x ^ (-4 : ℝ)
  rw [Real.norm_eq_abs]
  have h := rtdHD_absmul_le (hωD r (hsub r hr) x hx).1 (hdφb r hr x)
  exact le_trans h (le_of_eq (by ring))

end UnforcedLeray.Short.IIb
