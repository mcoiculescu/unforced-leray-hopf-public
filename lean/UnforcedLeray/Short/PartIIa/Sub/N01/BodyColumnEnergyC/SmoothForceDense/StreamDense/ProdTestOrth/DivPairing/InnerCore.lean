import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3_2
import UnforcedLeray.Lib.Cylinder.Basic

/-!
# Core pairing identity for `DivPairing` / `CurlPairing` (`PartII-a:N01/9/1/1/3/2/3-4`)

For `V p = (θ(s) b₀(q,η), θ(s) b₁(q,η))` (`b₀,b₁` `c`-periodic in `q`) and `h ∈ 𝓗`,
`⟪V, h⟫_{L²(measureH c)} = ∫_s θ(s) s^{-3/2} ∫_{cell} (h₀ b₀ + h₁ b₁) ds`, where the inner integral
is over the centred cell (the `q`-periodic extension `sliceFn h s` is used).  Proof: `L2.inner_def`,
`withDensity`, Fubini on the product cell `Ioi 0 ×ˢ (Ioc 0 c ×ˢ univ)`, and the `q`-period shift
`Cyl.integral_strip_eq_cell`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace UnforcedLeray.Short.PartIIa.N01.Sub.InnerCore

open UnforcedLeray.B0220 (Profile HSpace measureH weightH reduceIoc)
open UnforcedLeray.B0223 (MeridC)

theorem sBump_zero_of_nmem {θ : ℝ → ℝ} (hθ : IsSBump θ) {s : ℝ} (hs : s ∉ Ioi (0 : ℝ)) :
    θ s = 0 := by
  by_contra hne
  exact hs (hθ.2.2 (subset_tsupport θ hne))

theorem isPeriodic_of_cylTest {c : ℝ} {φ : ℝ × ℝ → ℝ} (hφ : UnforcedLeray.Sob.IsCylTest c φ) :
    UnforcedLeray.Cyl.IsPeriodic c φ := by
  intro z
  have e : ((z.1 + c, z.2) : ℝ × ℝ) = z + (c, 0) := by ext <;> simp
  rw [e]
  exact hφ.periodic z

/-- Partial derivatives of the product `θ(s) ψ(q,η)`. -/
theorem fderiv_prodFn_apply {θ : ℝ → ℝ} {ψ : ℝ × ℝ → ℝ} (hθ : Differentiable ℝ θ)
    (hψ : Differentiable ℝ ψ) (p v : Profile) :
    fderiv ℝ (fun y : Profile => θ y.1 * ψ y.2) p v =
      θ p.1 * fderiv ℝ ψ p.2 v.2 + ψ p.2 * (deriv θ p.1 * v.1) := by
  have h1 : HasDerivAt θ (deriv θ p.1) p.1 := (hθ p.1).hasDerivAt
  have h1' : HasFDerivAt (fun y : Profile => θ y.1)
      ((deriv θ p.1) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
    h1.comp_hasFDerivAt p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun y : Profile => ψ y.2)
      ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
    (hψ p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h3 : HasFDerivAt (fun y : Profile => θ y.1 * ψ y.2)
      (θ p.1 • (fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) +
        ψ p.2 • (deriv θ p.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))) p :=
    h1'.mul h2
  rw [h3.fderiv]
  simp [smul_eq_mul]

/-- Complex cast of a real differentiable function: the derivative is the cast of the derivative. -/
theorem fderiv_ofReal_apply {Φ : Profile → ℝ} (hΦ : Differentiable ℝ Φ) (p v : Profile) :
    fderiv ℝ (fun y : Profile => ((Φ y : ℝ) : ℂ)) p v = ((fderiv ℝ Φ p v : ℝ) : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt).comp p (hΦ p).hasFDerivAt
  have e : (fun y : Profile => ((Φ y : ℝ) : ℂ)) = (Complex.ofRealCLM ∘ Φ) := rfl
  rw [e, h.fderiv]
  simp

theorem sliceFn_periodic {c : ℝ} (hc : 0 < c) (h : HSpace c MeridC) (s : ℝ)
    {b0 b1 : ℝ × ℝ → ℝ} (hb0 : UnforcedLeray.Cyl.IsPeriodic c b0)
    (hb1 : UnforcedLeray.Cyl.IsPeriodic c b1) :
    UnforcedLeray.Cyl.IsPeriodic c
      (fun z => sliceFn h s z 0 * ((b0 z : ℝ) : ℂ) + sliceFn h s z 1 * ((b1 z : ℝ) : ℂ)) := by
  intro z
  simp only [sliceFn, UnforcedLeray.B0220.reduceIoc_add hc, hb0 z, hb1 z]

/-- Periodic integrands over the strip `Ioc 0 c ×ˢ ℝ` and over the centred cell agree. -/
theorem integral_ioc_eq_cell {c : ℝ} (hc : 0 < c) {F : ℝ × ℝ → ℂ}
    (hF : UnforcedLeray.Cyl.IsPeriodic c F) :
    ∫ z in Ioc 0 c ×ˢ (univ : Set ℝ), F z = ∫ z in UnforcedLeray.Cyl.cell c, F z := by
  have hae : Ioc (0 : ℝ) c ×ˢ (univ : Set ℝ) =ᵐ[volume] Ico (0 : ℝ) (0 + c) ×ˢ (univ : Set ℝ) := by
    refine Measure.set_prod_ae_eq ?_ (EventuallyEq.refl _ _)
    rw [zero_add]
    exact Ioc_ae_eq_Icc.trans Ico_ae_eq_Icc.symm
  rw [setIntegral_congr_set hae, UnforcedLeray.Cyl.integral_strip_eq_cell hc hF 0]

theorem innerCore {c : ℝ} (hc : 0 < c) {θ : ℝ → ℝ} (hθ : IsSBump θ)
    {b0 b1 : ℝ × ℝ → ℝ} (hb0 : UnforcedLeray.Cyl.IsPeriodic c b0)
    (hb1 : UnforcedLeray.Cyl.IsPeriodic c b1)
    {V : Profile → MeridC}
    (hVdef : ∀ p : Profile, V p = !₂[((θ p.1 * b0 p.2 : ℝ) : ℂ), ((θ p.1 * b1 p.2 : ℝ) : ℂ)])
    (hV : MemLp V 2 (measureH c)) (h : HSpace c MeridC) :
    inner ℂ (hV.toLp V) h = ∫ s : ℝ, ((θ s * s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      ∫ z in UnforcedLeray.Cyl.cell c,
        (sliceFn h s z 0 * ((b0 z : ℝ) : ℂ) + sliceFn h s z 1 * ((b1 z : ℝ) : ℂ)) := by
  have hpt : ∀ p : Profile, inner ℂ (V p) (h p) =
      ((θ p.1 * b0 p.2 : ℝ) : ℂ) * h p 0 + ((θ p.1 * b1 p.2 : ℝ) : ℂ) * h p 1 := by
    intro p
    rw [hVdef p]
    simp [PiLp.inner_apply, Fin.sum_univ_two] <;> ring
  have hFint : Integrable (fun p : Profile => inner ℂ (V p) (h p)) (measureH c) := by
    refine (L2.integrable_inner (hV.toLp V) h).congr ?_
    filter_upwards [hV.coeFn_toLp] with p hp
    simp only [hp]
  have hinner : inner ℂ (hV.toLp V) h = ∫ p : Profile, inner ℂ (V p) (h p) ∂(measureH c) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hV.coeFn_toLp] with p hp
    simp only [hp]
  have hmH : measureH c = (volume.restrict (UnforcedLeray.B0220.cell c)).withDensity weightH :=
    rfl
  have hwm : Measurable weightH := by
    unfold weightH
    exact Measurable.ennreal_ofReal (measurable_fst.pow_const _)
  have hconv : ∫ p : Profile, inner ℂ (V p) (h p) ∂(measureH c) =
      ∫ p : Profile, (weightH p).toReal • inner ℂ (V p) (h p)
        ∂(volume.restrict (UnforcedLeray.B0220.cell c)) := by
    exact integral_withDensity_eq_integral_toReal_smul
      (μ := volume.restrict (UnforcedLeray.B0220.cell c)) hwm
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) _
  have hGint : IntegrableOn (fun p : Profile => (weightH p).toReal • inner ℂ (V p) (h p))
      (UnforcedLeray.B0220.cell c) := by
    have hfin : ∀ᵐ p ∂(volume.restrict (UnforcedLeray.B0220.cell c)), weightH p < ⊤ :=
      ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
    have h1 : Integrable (fun p : Profile => inner ℂ (V p) (h p))
        ((volume.restrict (UnforcedLeray.B0220.cell c)).withDensity weightH) := hFint
    exact (integrable_withDensity_iff_integrable_smul' hwm hfin).1 h1
  have hsplit : ∫ p : Profile, (weightH p).toReal • inner ℂ (V p) (h p)
        ∂(volume.restrict (UnforcedLeray.B0220.cell c)) =
      ∫ s in Ioi (0 : ℝ), ∫ z in Ioc 0 c ×ˢ (univ : Set ℝ),
        (weightH (s, z)).toReal • inner ℂ (V (s, z)) (h (s, z)) := by
    have hfi : IntegrableOn (fun p : Profile => (weightH p).toReal • inner ℂ (V p) (h p))
        (Ioi (0 : ℝ) ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ)))
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := hGint
    have hrw : (volume.restrict (UnforcedLeray.B0220.cell c) : Measure Profile) =
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))).restrict
          (Ioi (0 : ℝ) ×ˢ (Ioc 0 c ×ˢ (univ : Set ℝ))) := rfl
    rw [hrw]
    exact setIntegral_prod _ hfi
  have hslice : ∀ s ∈ Ioi (0 : ℝ),
      ∫ z in Ioc 0 c ×ˢ (univ : Set ℝ), (weightH (s, z)).toReal • inner ℂ (V (s, z)) (h (s, z))
        = ((θ s * s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ∫ z in UnforcedLeray.Cyl.cell c,
          (sliceFn h s z 0 * ((b0 z : ℝ) : ℂ) + sliceFn h s z 1 * ((b1 z : ℝ) : ℂ)) := by
    intro s hs
    have hs' : (0 : ℝ) < s := hs
    have hEq : EqOn (fun z : ℝ × ℝ => (weightH (s, z)).toReal • inner ℂ (V (s, z)) (h (s, z)))
        (fun z : ℝ × ℝ => ((θ s * s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
          (sliceFn h s z 0 * ((b0 z : ℝ) : ℂ) + sliceFn h s z 1 * ((b1 z : ℝ) : ℂ)))
        (Ioc 0 c ×ˢ (univ : Set ℝ)) := by
      rintro z ⟨hz1, -⟩
      have hzr : reduceIoc c z.1 = z.1 := UnforcedLeray.B0220.reduceIoc_of_mem hc hz1
      have hw : (weightH (s, z)).toReal = s ^ (-(3 / 2 : ℝ)) := by
        unfold weightH
        exact ENNReal.toReal_ofReal (Real.rpow_nonneg hs'.le _)
      simp only [sliceFn, hzr, Prod.mk.eta]
      rw [hpt (s, z), hw, Complex.real_smul]
      dsimp only
      push_cast
      ring
    rw [setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ) hEq, integral_const_mul,
      integral_ioc_eq_cell hc (sliceFn_periodic hc h s hb0 hb1)]
  calc inner ℂ (hV.toLp V) h = ∫ p : Profile, inner ℂ (V p) (h p) ∂(measureH c) := hinner
    _ = ∫ p : Profile, (weightH p).toReal • inner ℂ (V p) (h p)
        ∂(volume.restrict (UnforcedLeray.B0220.cell c)) := hconv
    _ = ∫ s in Ioi (0 : ℝ), ∫ z in Ioc 0 c ×ˢ (univ : Set ℝ),
        (weightH (s, z)).toReal • inner ℂ (V (s, z)) (h (s, z)) := hsplit
    _ = ∫ s in Ioi (0 : ℝ), ((θ s * s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ∫ z in UnforcedLeray.Cyl.cell c,
          (sliceFn h s z 0 * ((b0 z : ℝ) : ℂ) + sliceFn h s z 1 * ((b1 z : ℝ) : ℂ)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun s hs => hslice s hs)
    _ = ∫ s : ℝ, ((θ s * s ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ∫ z in UnforcedLeray.Cyl.cell c,
          (sliceFn h s z 0 * ((b0 z : ℝ) : ℂ) + sliceFn h s z 1 * ((b1 z : ℝ) : ℂ)) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro s hs
        simp [sBump_zero_of_nmem hθ hs]

end UnforcedLeray.Short.PartIIa.N01.Sub.InnerCore
