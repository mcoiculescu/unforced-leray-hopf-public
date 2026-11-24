import UnforcedLeray.Short.PartIIIa.Clock.FrameAmplitudeProof.DirectError.EulerSubBound.SubBound.PlanarDual

/-!
# Planar seed duality: assembly (helper for `PartIII-a:T21/c5/2/2/2`)

Source of record: `the November 2 reference manuscript` (SP), lines 593-610,
662-670, 788-803, 2891-2918.

* `planar_dual_zero`: `v₀·∇λ₀ - K_∞^T(λ₀∇ω₀) = lam λ₀` from the transport part
  (`transCx_v0_seedDual`), the adjoint part (`kerAdjPl_seedDual`), the sector identity
  `y·(K q̃) = 2i Δ₂⁻¹h(|y|) e^{-2iϑ}` (`dot_biotSavart_ofProfile_lim`, `q̃ = h(|y|)e^{-2iϑ}`) and
  `Δ₂⁻¹h = (Ω - i lam/2) G`.
* `planar_dual_one`: the conjugate row `λ₁ = \bar λ₀`.
* `seedPlanarDualEigen`: `DirectEulerSub.SeedPlanarDualEigen κ` for every `κ`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa

namespace PlanarDualSub

open UnforcedLeray UnforcedLeray.Planar.NUE

theorem planar_dual_zero {lam : ℂ} {h : ℝ → ℂ} (hre : 0 < lam.re)
    (hsm : ContDiff ℝ ∞ (PartI.seedPlanar h)) (hon : ContDiffOn ℝ ∞ h (Ioi 0))
    {C : ℝ} {N : ℕ}
    (hC : ∀ y : ℂ, ‖PartI.seedPlanar h y‖ ≤ C * (1 + ‖y‖) ^ N * Real.exp (-(‖y‖ ^ 2) / 4))
    (hkG : ∀ r : ℝ, 0 < r →
      (GaussianVortex.radialK r : ℂ) * CutFTCGradPerSum.seedDualRadialG lam h r = h r)
    (hdiff : Differentiable ℝ (CutFTCGradPerSum.seedDualExplicit lam h 0)) (y : ℝ × ℝ) :
    E0.transCx (fun z l => Train.v0 z l) (CutFTCGradPerSum.seedDualExplicit lam h 0) y -
      EulerSubCore.kerAdjPl (fun l x => CutFTCGradPerSum.seedDualExplicit lam h 0 x *
        ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ)) y =
    lam * CutFTCGradPerSum.seedDualExplicit lam h 0 y := by
  set A : ℝ := |C| * Real.exp (2 * (N : ℝ) ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hq : Ang.ofProfile (-2) h = fun z => PartI.seedPlanar h (conj z) := by
    funext z; exact ofProfile_neg_eq_conj 2 h z
  have hqc : Continuous (Ang.ofProfile (-2) h) := by
    rw [hq]; exact hsm.continuous.comp Complex.continuous_conj
  have hqb : ∀ z, ‖Ang.ofProfile (-2) h z‖ ≤ A * Real.exp (-(‖z‖ ^ 2) / 8) := by
    intro z
    rw [hq]
    have := hC (conj z)
    rw [Complex.norm_conj] at this
    exact PartI.BiotSavartCurlAux.gauss_dominated z this
  have hK : ∀ z, ‖Ang.ofProfile (-2) h z‖ ≤ A := by
    intro z
    refine (hqb z).trans ?_
    have h1 : Real.exp (-(‖z‖ ^ 2) / 8) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := sq_nonneg ‖z‖; linarith)
    exact mul_le_of_le_one_right hA0 h1
  have hint : Integrable (Ang.ofProfile (-2) h) :=
    Integrable.mono' (PartI.BiotSavartCurlAux.integrable_exp_neg_sq_div_eight.const_mul A)
      hqc.aestronglyMeasurable (Eventually.of_forall hqb)
  have hi : IntegrableOn (fun ρ => ‖h ρ‖ * ρ) (Ioi 0) := by
    have hg := ((integrable_mul_exp_neg_mul_sq (b := 1 / 8) (by norm_num)).const_mul A).integrableOn
      (s := Ioi (0 : ℝ))
    refine Integrable.mono' hg ?_ ?_
    · exact (hon.continuousOn.norm.mul continuousOn_id).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
      have hρ' : (0 : ℝ) < ρ := hρ
      have hb := hqb (ρ : ℂ)
      have hsp : Ang.ofProfile 2 h (ρ : ℂ) = h ρ := seedPlanar_ofReal_eq h ρ hρ'
      rw [ofProfile_neg_eq_conj, Complex.conj_ofReal, hsp,
        Complex.norm_real, Real.norm_of_nonneg hρ'.le] at hb
      have hb' : ‖h ρ‖ ≤ A * Real.exp (-(1 / 8) * ρ ^ 2) := by
        refine hb.trans (le_of_eq ?_)
        congr 2; ring
      rw [norm_mul, norm_norm, Real.norm_of_nonneg hρ'.le]
      calc ‖h ρ‖ * ρ ≤ A * Real.exp (-(1 / 8) * ρ ^ 2) * ρ :=
            mul_le_mul_of_nonneg_right hb' hρ'.le
        _ = A * (ρ * Real.exp (-(1 / 8) * ρ ^ 2)) := by ring
  have hlim := dot_biotSavart_ofProfile_lim (m := -2) (by norm_num) hon hqc hK hint hi (planeToC y)
  have hre' : (planeToC y).re = y.1 := rfl
  have him' : (planeToC y).im = y.2 := rfl
  rw [hre', him'] at hlim
  rw [transCx_v0_seedDual hdiff y, kerAdjPl_seedDual hkG hqc hK hint y, hlim,
    seedDualExplicit_zero_eq_comp]
  simp only [Ang.ofProfile]
  rw [gauss0_eq_radialOmega]
  have hnat : Int.natAbs (-2) = 2 := rfl
  rw [hnat]
  by_cases hy : planeToC y = 0
  · have hphase : Ang.angPhase (-2) (planeToC y) = 0 := by rw [hy]; simp [Ang.angPhase]
    rw [hphase]; simp
  · have hr : 0 < ‖planeToC y‖ := norm_pos_iff.2 hy
    have hD := PartI.adjEig_den_ne hre (GaussianVortex.radialOmega ‖planeToC y‖)
    have hgr : Planar.greenN 2 h ‖planeToC y‖ =
        ((GaussianVortex.radialOmega ‖planeToC y‖ : ℂ) - Complex.I * lam / 2) *
          CutFTCGradPerSum.seedDualRadialG lam h ‖planeToC y‖ := by
      unfold CutFTCGradPerSum.seedDualRadialG
      rw [if_pos hr, mul_div_assoc', eq_div_iff hD]
      ring
    rw [hgr]
    push_cast
    linear_combination (-(lam * ((PartI.seedJ h)⁻¹ / (2 * Real.pi : ℂ)) *
      CutFTCGradPerSum.seedDualRadialG lam h ‖planeToC y‖ * Ang.angPhase (-2) (planeToC y))) *
      Complex.I_sq

theorem pdCx_conj {f : ℝ × ℝ → ℂ} (l : Fin 2) (y : ℝ × ℝ) :
    pdCx l (fun x => conj (f x)) y = conj (pdCx l f y) := by
  unfold pdCx
  have hfun : (fun x => conj (f x)) = fun x => star (f x) := rfl
  rw [hfun, fderiv_star]
  simp

theorem planar_dual_one {lam : ℂ} {h : ℝ → ℂ}
    (h0 : ∀ y : ℝ × ℝ,
      E0.transCx (fun z l => Train.v0 z l) (CutFTCGradPerSum.seedDualExplicit lam h 0) y -
        EulerSubCore.kerAdjPl (fun l x => CutFTCGradPerSum.seedDualExplicit lam h 0 x *
          ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ)) y =
      lam * CutFTCGradPerSum.seedDualExplicit lam h 0 y) (y : ℝ × ℝ) :
    E0.transCx (fun z l => Train.v0 z l) (CutFTCGradPerSum.seedDualExplicit lam h 1) y -
      EulerSubCore.kerAdjPl (fun l x => CutFTCGradPerSum.seedDualExplicit lam h 1 x *
        ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ)) y =
    conj lam * CutFTCGradPerSum.seedDualExplicit lam h 1 y := by
  rw [SeedJet2Aux.seedDualExplicit_one_eq_conj lam h]
  set Λ := CutFTCGradPerSum.seedDualExplicit lam h 0 with hΛ
  have htr : E0.transCx (fun z l => Train.v0 z l) (fun x => conj (Λ x)) y =
      conj (E0.transCx (fun z l => Train.v0 z l) Λ y) := by
    unfold E0.transCx
    rw [pdCx_conj 0 y, pdCx_conj 1 y]
    simp only [map_add, map_mul, Complex.conj_ofReal]
  have hker : EulerSubCore.kerAdjPl (fun l x => conj (Λ x) *
        ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ)) y =
      conj (EulerSubCore.kerAdjPl (fun l x => Λ x *
        ((B0579.pd l (Cyl.curl Train.v0) x : ℝ) : ℂ)) y) := by
    unfold EulerSubCore.kerAdjPl
    rw [← integral_conj]
    congr 1
    funext x
    simp only [map_sum, map_mul, Complex.conj_ofReal]
  rw [htr, hker, ← map_sub, h0 y, map_mul]

/-- **Planar seed duality** `v₀·∇λ_k - K_∞^T(λ_k ∇ω₀) = λ_k λ_k` for the seed triple
realizing `κ` (SP 593-610, 2891-2918). -/
theorem seedPlanarDualEigen (κ : PlanarFrameKernels) : DirectEulerSub.SeedPlanarDualEigen κ := by
  intro hκ lam h hh ℓ hIS he0 _he1 hpair k y
  obtain ⟨hsm, hon, C, N, hC⟩ := seed_smooth_given hIS he0
  obtain ⟨hcont_exp, _, hpair_exp⟩ :=
    CutFTCGradPerSum.seedDualExplicit_cont_and_pairing lam h hh ℓ hIS hsm hon
  have hl0 : κ.lamP 0 = CutFTCGradPerSum.seedDualExplicit lam h 0 :=
    CutFTCGradPerSum.eq_of_integral_planeToC_eq (κ.lamP_cont 0) (hcont_exp 0)
      (fun f hf hfc => (hpair f hf hfc).1.trans (hpair_exp f hf hfc).1.symm)
  have hl1 : κ.lamP 1 = CutFTCGradPerSum.seedDualExplicit lam h 1 :=
    CutFTCGradPerSum.eq_of_integral_planeToC_eq (κ.lamP_cont 1) (hcont_exp 1)
      (fun f hf hfc => (hpair f hf hfc).2.trans (hpair_exp f hf hfc).2.symm)
  have hdiff0 : Differentiable ℝ (CutFTCGradPerSum.seedDualExplicit lam h 0) :=
    hl0 ▸ (EulerSubCore.lamP_jets hκ).1 0
  have hkG := kG_eq_h hIS hon
  have h0 := planar_dual_zero hIS.re_pos hsm hon hC hkG hdiff0
  fin_cases k
  · simp only [Fin.zero_eta, seedModeEigen, if_true]
    rw [hl0]
    exact h0 y
  · simp only [Fin.mk_one, seedModeEigen, one_ne_zero, if_false]
    rw [hl1]
    exact planar_dual_one h0 y

end PlanarDualSub

end UnforcedLeray.Short.IIIa
