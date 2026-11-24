import UnforcedLeray.Cons.L2.CanonicalBranch.DysonEnergy
import UnforcedLeray.Lib.BudgetsGronwall.Uniform

/-!
# Strong convergence of the Hermite diffusion approximants

This downstream leaf identifies the bounded Hermite Dyson family on basis vectors and prepares
uniform strong convergence to the concrete Gaussian diffusion family.
-/

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate RealInnerProductSpace Topology

namespace UnforcedLeray.Cons.G3b

open UnforcedLeray.B0010 UnforcedLeray.B0094 UnforcedLeray.B0123 UnforcedLeray.Evolution

private theorem tendstoUniformlyOn_yosida_exp_multiplier (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    TendstoUniformlyOn
      (fun N : ℕ => fun ρ : ℝ => Real.exp (-(((k : ℝ) * N / (N + k)) * ρ)))
      (fun ρ : ℝ => Real.exp (-((k : ℝ) * ρ))) atTop (Icc 0 R) := by
  let κ : ℝ := k
  let gap : ℕ → ℝ := fun N => κ - κ * N / (N + k)
  let f : ℝ → ℝ → ℝ := fun ν ρ => Real.exp (-((κ - ν) * ρ))
  have hNadd : Tendsto (fun N : ℕ => (N : ℝ) + κ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + κ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hNadd
  by_cases hk : k = 0
  · subst k
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with N ρ hρ
    simpa using hε
  · have hkpos : 0 < κ := by
      have hk' : 0 < k := Nat.pos_of_ne_zero hk
      change (0 : ℝ) < (k : ℝ)
      exact_mod_cast hk'
    have hgap_eq : ∀ N, gap N = κ ^ 2 * ((N : ℝ) + κ)⁻¹ := by
      intro N
      have hden : (N : ℝ) + κ ≠ 0 := ne_of_gt (by positivity)
      change κ - κ * N / (N + k) = _
      field_simp
      ring
    have hgap0 : Tendsto gap atTop (𝓝 0) := by
      have h := hinv.const_mul (κ ^ 2)
      have h' : Tendsto (fun N : ℕ => κ ^ 2 * ((N : ℝ) + κ)⁻¹) atTop (𝓝 0) := by
        simpa using h
      have hg : gap = fun N : ℕ => κ ^ 2 * ((N : ℝ) + κ)⁻¹ := funext hgap_eq
      rw [hg]
      exact h'
    have hgap : Tendsto gap atTop (𝓝[>] (0 : ℝ)) := by
      have hpos : ∀ᶠ N : ℕ in atTop, 0 < gap N := by
        filter_upwards [] with N
        rw [hgap_eq N]
        positivity
      refine tendsto_nhdsWithin_iff.2 ⟨hgap0, hpos⟩
    have hν₀ : 0 < κ + 1 := by linarith
    have hu := UnforcedLeray.Budget.tendstoUniformlyOn_of_continuousOn_Icc_prod
      (K := Icc 0 R) isCompact_Icc hν₀ (by fun_prop :
        ContinuousOn (Function.uncurry f) (Icc 0 (κ + 1) ×ˢ Icc 0 R))
    rw [Metric.tendstoUniformlyOn_iff] at hu
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev := hu ε hε
    filter_upwards [hgap.eventually hev] with N hN ρ hρ
    have hparam : κ - gap N = κ * N / (N + k) := by
      simp only [gap]
      ring
    simpa [f, hparam, κ] using hN ρ hρ

private def convergenceIdentityFamily {a b : ℝ} : EvolutionFamily XG a b where
  U _ _ := 1
  U_diag _ _ := rfl
  U_comp _ _ _ _ _ _ _ := by ext x; rfl
  U_cont _ := continuousOn_const
  U_bdd := ⟨1, fun _ _ _ _ _ => ContinuousLinearMap.norm_id_le⟩

private theorem convergenceIdentity_hasWeakGenerator {a b : ℝ} :
    (convergenceIdentityFamily (a := a) (b := b)).HasWeakGenerator Set.univ
      (fun _ _ => 0) := by
  intro (ℓ : XG →L[ℂ] ℂ) hℓ s x hs t ht
  change HasDerivWithinAt (fun _ : ℝ => ℓ x) 0 (Icc s b) t
  exact hasDerivWithinAt_const (c := ℓ x) (s := Icc s b) (x := t)

private theorem diffusionGenerator_continuous {a b : ℝ}
    (β : ℝ → ℝ) (N : ℕ) (hβ : ContinuousOn β (Icc a b)) :
    ∀ (ℓ : XG →L[ℂ] ℂ), ℓ ∈ Set.univ →
      ContinuousOn (fun r => ℓ.comp (boundedYosidaDiffusionCoefficient β N r))
        (Icc a b) := by
  intro ℓ hℓ
  have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn.comp hβ
      (fun r hr => Set.mem_univ (β r))
  have hEq : (fun r => ℓ.comp (boundedYosidaDiffusionCoefficient β N r)) =
      (fun r => ((β r : ℝ) : ℂ) • (ℓ.comp (PlanarSpectral.Dyosida N))) := by
    funext r
    ext x
    simp only [boundedYosidaDiffusionCoefficient, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [hEq]
  exact hβc.smul continuousOn_const

private def unitYosidaDiffusionFamily (R : ℝ) (N : ℕ) : EvolutionFamily XG 0 R :=
  let hC : ContinuousOn (boundedYosidaDiffusionCoefficient (fun _ : ℝ => 1) N) (Icc 0 R) := by
    change ContinuousOn (fun _ : ℝ => (1 : ℂ) • PlanarSpectral.Dyosida N) (Icc 0 R)
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℂ)) (Icc 0 R) := continuousOn_const
    have hD : ContinuousOn (fun _ : ℝ => PlanarSpectral.Dyosida N) (Icc 0 R) := continuousOn_const
    exact h1.smul hD
  Evolution.dyson (convergenceIdentityFamily (a := 0) (b := R))
    (boundedPertOfContinuous (boundedYosidaDiffusionCoefficient (fun _ : ℝ => 1) N) hC)

private theorem unitYosidaDiffusionFamily_norm_le {R ρ : ℝ} {N : ℕ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) (x : XG) :
    ‖(unitYosidaDiffusionFamily R N).U ρ 0 x‖ ≤ ‖x‖ := by
  let C := boundedYosidaDiffusionCoefficient (fun _ : ℝ => 1) N
  have hC : ContinuousOn C (Icc 0 R) := by
    change ContinuousOn (fun _ : ℝ => (1 : ℂ) • PlanarSpectral.Dyosida N) (Icc 0 R)
    have h1 : ContinuousOn (fun _ : ℝ => (1 : ℂ)) (Icc 0 R) := continuousOn_const
    have hD : ContinuousOn (fun _ : ℝ => PlanarSpectral.Dyosida N) (Icc 0 R) := continuousOn_const
    exact h1.smul hD
  let A := boundedPertOfContinuous C hC
  have hA : ContinuousOn A.A (Icc 0 R) := hC
  have hDiss : ∀ r ∈ Icc 0 R, ∀ z : XG,
      (⟪z, A.A r z⟫_ℂ).re ≤ 0 * ‖z‖ ^ 2 := by
    intro r hr z
    change (⟪z, ((1 : ℝ) : ℂ) • (PlanarSpectral.Dyosida N z)⟫_ℂ).re ≤ _
    rw [inner_smul_right]
    simpa using dyosida_inner_nonpos N z
  let E := Evolution.dyson (convergenceIdentityFamily (a := 0) (b := R)) A
  have huR : ContinuousOn (fun r => E.U r 0 x) (Icc 0 R) := E.continuousOn_fst le_rfl x
  have hInt : ContinuousOn (fun r => A.A r (E.U r 0 x)) (Icc 0 R) := hA.clm_apply huR
  have hstar : ∀ u ∈ Icc 0 R,
      E.U u 0 x = x + ∫ r in 0..u, A.A r (E.U r 0 x) := by
    intro u hu
    change (Evolution.dyson (convergenceIdentityFamily (a := 0) (b := R)) A).U u 0 x = _
    rw [Evolution.dyson_left (convergenceIdentityFamily (a := 0) (b := R)) A
      ⟨le_rfl, hu.1, hu.2⟩ x]
    simp [convergenceIdentityFamily]
    rfl
  have hODE : ∀ τ ∈ Ico 0 ρ,
      HasDerivWithinAt (fun r => E.U r 0 x) (A.A τ (E.U τ 0 x)) (Icc 0 ρ) τ := by
    intro τ hτ
    have hder := Evolution.hasDerivWithinAt_integral_Icc hInt
      ⟨hτ.1, (le_of_lt hτ.2).trans hρR⟩
    have hder' := hder.const_add x
    have hder'' := hder'.congr_of_mem hstar
      ⟨hτ.1, (le_of_lt hτ.2).trans hρR⟩
    exact hder''.mono (Icc_subset_Icc le_rfl hρR)
  have hu : ContinuousOn (fun r => E.U r 0 x) (Icc 0 ρ) :=
    huR.mono (Icc_subset_Icc le_rfl hρR)
  have hDiss' : ∀ τ ∈ Ico 0 ρ,
      (⟪E.U τ 0 x, A.A τ (E.U τ 0 x)⟫_ℂ).re ≤ 0 * ‖E.U τ 0 x‖ ^ 2 := by
    intro τ hτ
    exact hDiss τ ⟨hτ.1, (le_of_lt hτ.2).trans hρR⟩ _
  have hnorm := continuousODE_norm_le_exp (fun r => E.U r 0 x) A.A hu hODE hDiss'
    ⟨hρ, le_rfl⟩
  have hnorm' :
      ‖(unitYosidaDiffusionFamily R N).U ρ 0 x‖ ≤
        ‖(unitYosidaDiffusionFamily R N).U 0 0 x‖ := by
    simpa [E, unitYosidaDiffusionFamily, C, A, convergenceIdentityFamily] using hnorm
  calc
    ‖(unitYosidaDiffusionFamily R N).U ρ 0 x‖ ≤
        ‖(unitYosidaDiffusionFamily R N).U 0 0 x‖ := hnorm'
    _ = ‖x‖ := by
      rw [(unitYosidaDiffusionFamily R N).apply_diag ⟨le_rfl, hρ.trans hρR⟩ x]

/-- The bounded Yosida diffusion Dyson family acts diagonally on each oscillator basis vector. -/
theorem boundedYosidaDiffusionFamily_basis_action {a b s t : ℝ}
    (β : ℝ → ℝ) (N k : ℕ) (hβ : ContinuousOn β (Icc a b))
    (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
    (Evolution.dyson (convergenceIdentityFamily (a := a) (b := b))
      (boundedPertOfContinuous (boundedYosidaDiffusionCoefficient β N)
        (by
          have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
            Complex.continuous_ofReal.continuousOn.comp hβ
              (fun r hr => Set.mem_univ (β r))
          exact hβc.smul continuousOn_const))).U t s (B0094.oscBasis k) =
      ((Real.exp ((-((k : ℝ) * N / (N + k))) * (∫ r in s..t, β r)) : ℝ) : ℂ) •
        B0094.oscBasis k := by
  let e : XG := B0094.oscBasis k
  let c : ℝ := -((k : ℝ) * N / (N + k))
  let C : ℝ → XG →L[ℂ] XG := boundedYosidaDiffusionCoefficient β N
  let A := boundedPertOfContinuous C (by
    change ContinuousOn (boundedYosidaDiffusionCoefficient β N) (Icc a b)
    have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.continuousOn.comp hβ
        (fun r hr => Set.mem_univ (β r))
    exact hβc.smul continuousOn_const)
  let E := Evolution.dyson (convergenceIdentityFamily (a := a) (b := b)) A
  have hc : PlanarSpectral.yosidaMult N k = (c : ℂ) := by
    simp [c, PlanarSpectral.yosidaMult]
  have hmode : PlanarSpectral.Dyosida N e = (c : ℂ) • e := by
    apply B0094.ext_inner_basis
    intro j
    rw [PlanarSpectral.inner_Dyosida, inner_smul_right]
    by_cases hj : j = k
    · subst j
      simp [e, hc, B0094.inner_basis_basis]
    · simp [e, hj, B0094.inner_basis_basis]
  have hbase := convergenceIdentity_hasWeakGenerator (a := a) (b := b)
  have hG : ∀ (ℓ : XG →L[ℂ] ℂ), ℓ ∈ Set.univ →
      ContinuousOn (fun _ : ℝ => (0 : XG →L[ℂ] ℂ)) (Icc a b) := by
    intro ℓ hℓ
    exact continuousOn_const
  have hA : ContinuousOn A.A (Icc a b) := by
    change ContinuousOn C (Icc a b)
    exact by
      change ContinuousOn (boundedYosidaDiffusionCoefficient β N) (Icc a b)
      have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
        Complex.continuous_ofReal.continuousOn.comp hβ
          (fun r hr => Set.mem_univ (β r))
      exact hβc.smul continuousOn_const
  have hU : E.HasWeakGenerator Set.univ
      (fun r ℓ => ℓ.comp (C r)) := by
    have h := Evolution.dyson_hasWeakGenerator
      (convergenceIdentityFamily (a := a) (b := b)) A hbase hG hA
    intro ℓ hℓ s x hs t ht
    simpa [E, A, boundedPertOfContinuous, zero_add, C] using h ℓ hℓ s x hs t ht
  have hC : ContinuousOn C (Icc a b) := by
    change ContinuousOn (boundedYosidaDiffusionCoefficient β N) (Icc a b)
    have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.continuousOn.comp hβ
        (fun r hr => Set.mem_univ (β r))
    exact hβc.smul continuousOn_const
  have hβs : ContinuousOn β (Icc s b) := hβ.mono (Icc_subset_Icc has le_rfl)
  let ρ : ℝ → ℝ := fun u => ∫ r in s..u, β r
  let v : ℝ → XG := fun u => Real.exp (c * ρ u) • e
  let u : ℝ → XG := fun r => E.U r s e
  have hu : ContinuousOn u (Icc s t) :=
    (E.continuousOn_fst has e).mono (Icc_subset_Icc le_rfl ht)
  have hρc : ContinuousOn ρ (Icc s t) := by
    intro r hr
    change ContinuousWithinAt (fun y => ∫ q in s..y, β q) (Icc s t) r
    have hder := Evolution.hasDerivWithinAt_integral_Icc hβs
      ⟨hr.1, hr.2.trans ht⟩
    exact hder.continuousWithinAt.mono (Icc_subset_Icc le_rfl ht)
  have hargc : ContinuousOn (fun y => c * ρ y) (Icc s t) := continuousOn_const.mul hρc
  have hscalar : ContinuousOn (fun y => Real.exp (c * ρ y)) (Icc s t) :=
    Real.continuous_exp.comp_continuousOn hargc
  have hv : ContinuousOn v (Icc s t) := hscalar.smul continuousOn_const
  have hODE : ∀ τ ∈ Ico s t,
      HasDerivWithinAt u (C τ (u τ)) (Icc s t) τ := by
    intro τ hτ
    have hder := weakGenerator_path_hasDerivWithinAt E C hU
      (diffusionGenerator_continuous β N hβ) hC has e
      ⟨hτ.1, (le_of_lt hτ.2).trans ht⟩
    exact hder.mono (Icc_subset_Icc le_rfl ht)
  have hV : ∀ τ ∈ Ico s t,
      HasDerivWithinAt v (C τ (v τ)) (Icc s t) τ := by
    intro τ hτ
    have hρwide := Evolution.hasDerivWithinAt_integral_Icc hβs
      ⟨hτ.1, (le_of_lt hτ.2).trans ht⟩
    have hρ := hρwide.mono (Icc_subset_Icc le_rfl ht)
    have harg := hρ.const_mul c
    have hexp := harg.exp
    have hexp' := hexp.smul_const e
    have hderivEq :
        (Real.exp (c * ρ τ) * (c * β τ)) • e = C τ (v τ) := by
      change (Real.exp (c * ρ τ) * (c * β τ)) • e =
        (((β τ : ℝ) : ℂ) • PlanarSpectral.Dyosida N) ((Real.exp (c * ρ τ) : ℝ) • e)
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (Real.exp (c * ρ τ)) e]
      rw [ContinuousLinearMap.smul_apply, map_smul, hmode]
      simp only [smul_smul]
      apply congrArg (fun z : ℂ => z • e)
      change ((Real.exp (c * ρ τ) * (c * β τ) : ℝ) : ℂ) =
        (β τ : ℂ) * (((Real.exp (c * ρ τ) : ℝ) : ℂ) * (c : ℂ))
      push_cast
      ring
    rw [hderivEq] at hexp'
    simpa [v] using hexp'
  let w : ℝ → XG := fun τ => u τ - v τ
  have hwcont : ContinuousOn w (Icc s t) := hu.sub hv
  have hODEw : ∀ τ ∈ Ico s t,
      HasDerivWithinAt w (C τ (w τ)) (Icc s t) τ := by
    intro τ hτ
    have hd := (hODE τ hτ).sub (hV τ hτ)
    change HasDerivWithinAt (fun r => u r - v r)
      (C τ (u τ - v τ)) (Icc s t) τ
    rw [map_sub]
    exact hd
  have hDiss : ∀ τ ∈ Ico s t,
      (⟪w τ, C τ (w τ)⟫_ℂ).re ≤ 0 * ‖w τ‖ ^ 2 := by
    intro τ hτ
    have hβτ : 0 ≤ β τ := hβ0 τ ⟨has.trans hτ.1, (le_of_lt hτ.2).trans ht⟩
    have hD := dyosida_inner_nonpos N (w τ)
    change (⟪w τ, (((β τ : ℝ) : ℂ) • (PlanarSpectral.Dyosida N (w τ)))⟫_ℂ).re ≤ _
    rw [inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
    have hmul := mul_nonpos_of_nonneg_of_nonpos hβτ hD
    nlinarith
  have hu0 : u s = e := by
    simpa [u, E] using E.apply_diag ⟨has, hst.trans ht⟩ e
  have hv0 : v s = e := by simp [v, ρ]
  have hws : w s = 0 := by simp [w, hu0, hv0]
  have hnorm := continuousODE_norm_le_exp w C hwcont hODEw hDiss ⟨hst, le_rfl⟩
  have hwt : w t = 0 := by
    have hzero : ‖w t‖ = 0 := by simpa [hws] using hnorm
    exact norm_eq_zero.mp hzero
  have heq := sub_eq_zero.mp hwt
  have hscalar : ((Real.exp (c * (∫ r in s..t, β r)) : ℝ) : ℂ) =
      Complex.exp (((-((k : ℝ) * N / (N + k)) : ℝ) : ℂ) *
        ((∫ r in s..t, β r : ℝ) : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
  have heq' : u t = ((Real.exp (c * (∫ r in s..t, β r)) : ℝ) : ℂ) • e := by
    simpa [v, ρ, RCLike.real_smul_eq_coe_smul (K := ℂ)] using heq
  rw [hscalar] at heq'
  simpa [u, e, c, E, A, C, PlanarSpectral.yosidaMult,
    Complex.ofReal_mul] using heq'

private theorem expD_oscBasis_apply {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) :
    B0123.expD ρ (B0094.oscBasis k) =
      ((Real.exp (-((k : ℝ) * ρ)) : ℝ) : ℂ) • B0094.oscBasis k := by
  obtain ⟨hk, hDk⟩ := B0094.D_oscBasis k
  have hDk' : B0094.D ⟨B0094.oscBasis k, hk⟩ =
      ((-(k : ℝ) : ℝ) : ℂ) • (B0094.oscBasis k : XG) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast, Subtype.coe_mk] using hDk
  have hEig := B0123.expD_eigen hρ ⟨B0094.oscBasis k, hk⟩ (-(k : ℝ)) hDk'
  have hexp : Complex.exp (-((ρ : ℂ) * (k : ℂ))) =
      ((Real.exp (-((k : ℝ) * ρ)) : ℝ) : ℂ) := by
    rw [show -((ρ : ℂ) * (k : ℂ)) = ((-((k : ℝ) * ρ) : ℝ) : ℂ) by
      push_cast
      ring,
      Complex.ofReal_exp]
  simpa [hexp] using hEig

private theorem unitYosidaDiffusionFamily_oscBasis {R ρ : ℝ} {N k : ℕ}
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    (unitYosidaDiffusionFamily R N).U ρ 0 (B0094.oscBasis k) =
      ((Real.exp (-(((k : ℝ) * N / (N + k)) * ρ)) : ℝ) : ℂ) • B0094.oscBasis k := by
  have h := boundedYosidaDiffusionFamily_basis_action
    (a := 0) (b := R) (s := 0) (t := ρ) (fun _ : ℝ => 1) N k
    continuousOn_const (fun _ _ => by norm_num) (le_rfl) hρ hρR
  simpa [unitYosidaDiffusionFamily, intervalIntegral.integral_const] using h

private theorem tendstoUniformlyOn_add_vec {ι P : Type*} {l : Filter ι} {K : Set P}
    {f g : ι → P → XG} {f₀ g₀ : P → XG}
    (hf : TendstoUniformlyOn f f₀ l K) (hg : TendstoUniformlyOn g g₀ l K) :
    TendstoUniformlyOn (fun i p => f i p + g i p) (fun p => f₀ p + g₀ p) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hf' := Metric.tendstoUniformlyOn_iff.1 hf (ε / 2) hhalf
  have hg' := Metric.tendstoUniformlyOn_iff.1 hg (ε / 2) hhalf
  filter_upwards [hf', hg'] with i hfi hgi p hp
  calc
    dist (f₀ p + g₀ p) (f i p + g i p) ≤ dist (f₀ p) (f i p) + dist (g₀ p) (g i p) :=
      dist_add_add_le _ _ _ _
    _ < ε := by linarith [hfi p hp, hgi p hp]

private theorem tendstoUniformlyOn_smul_vec {ι P : Type*} {l : Filter ι} {K : Set P}
    (c : ℂ) {f : ι → P → XG} {f₀ : P → XG}
    (hf : TendstoUniformlyOn f f₀ l K) :
    TendstoUniformlyOn (fun i p => c • f i p) (fun p => c • f₀ p) l K := by
  by_cases hc : c = 0
  · subst c
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [] with i p hp
    simpa using hε
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hε' : 0 < ε / ‖c‖ := div_pos hε (norm_pos_iff.mpr hc)
    have hev := Metric.tendstoUniformlyOn_iff.1 hf (ε / ‖c‖) hε'
    filter_upwards [hev] with i hi p hp
    have hdist : dist (c • f₀ p) (c • f i p) = ‖c‖ * dist (f₀ p) (f i p) := by
      rw [dist_eq_norm, ← smul_sub, norm_smul, dist_eq_norm]
    rw [hdist]
    calc ‖c‖ * dist (f₀ p) (f i p) < ‖c‖ * (ε / ‖c‖) :=
        mul_lt_mul_of_pos_left (hi p hp) (norm_pos_iff.mpr hc)
      _ = ε := by field_simp

private theorem tendstoUniformlyOn_apply_of_dense {ι P : Type*} {l : Filter ι}
    {K : Set P} {R : ι → P → XG →L[ℂ] XG} {R₀ : P → XG →L[ℂ] XG}
    (hR : ∃ C, ∀ i p, p ∈ K → ‖R i p‖ ≤ C)
    (hR₀ : ∃ C₀, ∀ p ∈ K, ‖R₀ p‖ ≤ C₀)
    {D : Set XG} (hD : Dense D)
    (hconv : ∀ x ∈ D, TendstoUniformlyOn (fun i p => R i p x)
      (fun p => R₀ p x) l K) (x : XG) :
    TendstoUniformlyOn (fun i p => R i p x) (fun p => R₀ p x) l K := by
  obtain ⟨C, hC⟩ := hR
  obtain ⟨C₀, hC₀⟩ := hR₀
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let C' : ℝ := max C 0 + max C₀ 0 + 1
  have hC' : 0 < C' := by positivity
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.1 hD x (ε / (2 * C')) (by positivity)
  rw [Metric.mem_ball, dist_eq_norm] at hd
  rw [norm_sub_rev d x] at hd
  have hev := Metric.tendstoUniformlyOn_iff.1 (hconv d hdD) (ε / 2) (by positivity)
  filter_upwards [hev] with i hi p hp
  have hdec : R i p x - R₀ p x =
      R i p (x - d) + (R i p d - R₀ p d) + R₀ p (d - x) := by
    simp only [map_sub]
    abel
  rw [dist_comm, dist_eq_norm]
  have h1 : ‖R i p (x - d)‖ ≤ max C 0 * ‖x - d‖ := by
    exact ((R i p).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((hC i p hp).trans (le_max_left _ _)) (norm_nonneg _))
  have h3 : ‖R₀ p (d - x)‖ ≤ max C₀ 0 * ‖x - d‖ := by
    rw [norm_sub_rev x d]
    exact (R₀ p).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_right ((hC₀ p hp).trans (le_max_left _ _)) (norm_nonneg _))
  have h4 : (max C 0 + max C₀ 0) * ‖x - d‖ ≤ ε / 2 := by
    have hle : (max C 0 + max C₀ 0) * ‖x - d‖ ≤ C' * (ε / (2 * C')) :=
      mul_le_mul (by dsimp [C']; linarith) hd.le (norm_nonneg _) hC'.le
    calc _ ≤ C' * (ε / (2 * C')) := hle
      _ = ε / 2 := by field_simp
  have hmid : ‖R i p d - R₀ p d‖ < ε / 2 := by
    have hh := hi p hp
    rw [dist_eq_norm] at hh
    simpa [norm_sub_rev] using hh
  calc
    ‖R i p x - R₀ p x‖ =
        ‖R i p (x - d) + (R i p d - R₀ p d) + R₀ p (d - x)‖ := by rw [hdec]
    _ ≤
        ‖R i p (x - d)‖ + ‖R i p d - R₀ p d‖ + ‖R₀ p (d - x)‖ := norm_add₃_le
    _ < max C 0 * ‖x - d‖ + ε / 2 + max C₀ 0 * ‖x - d‖ := by
      linarith [hmid]
    _ ≤ ε := by nlinarith

/-- The bounded Hermite diffusion base converges strongly to the concrete Gaussian semigroup,
uniformly over every compact interval of nonnegative diffusion times. -/
theorem unitYosidaDiffusionFamily_tendstoUniformlyOn_expD (R : ℝ) (hR : 0 ≤ R)
    (x : XG) :
    TendstoUniformlyOn
      (fun N : ℕ => fun ρ : ℝ => (unitYosidaDiffusionFamily R N).U ρ 0 x)
      (fun ρ : ℝ => B0123.expD ρ x) atTop (Icc 0 R) := by
  let F : ℕ → ℝ → XG →L[ℂ] XG := fun N ρ => (unitYosidaDiffusionFamily R N).U ρ 0
  let F₀ : ℝ → XG →L[ℂ] XG := fun ρ => B0123.expD ρ
  have hF : ∃ C : ℝ, ∀ N ρ, ρ ∈ Icc 0 R → ‖F N ρ‖ ≤ C := by
    refine ⟨1, fun N ρ hρ => ?_⟩
    exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun x => by
      simpa using unitYosidaDiffusionFamily_norm_le hρ.1 hρ.2 x
  have hF₀ : ∃ C₀ : ℝ, ∀ ρ ∈ Icc 0 R, ‖F₀ ρ‖ ≤ C₀ := by
    refine ⟨1, fun ρ hρ => ?_⟩
    exact B0123.norm_expD_le ρ
  let D : Submodule ℂ XG := Submodule.span ℂ (Set.range B0094.oscBasis)
  have hD : Dense (D : Set XG) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2 B0094.oscBasis.dense_span
  have hBasis : ∀ k : ℕ,
      TendstoUniformlyOn (fun N ρ => F N ρ (B0094.oscBasis k))
        (fun ρ => F₀ ρ (B0094.oscBasis k)) atTop (Icc 0 R) := by
    intro k
    have hs := tendstoUniformlyOn_yosida_exp_multiplier k hR
    rw [Metric.tendstoUniformlyOn_iff] at hs ⊢
    intro ε hε
    have hev := hs ε hε
    filter_upwards [hev] with N hN ρ hρ
    have hYN := unitYosidaDiffusionFamily_oscBasis
      (R := R) (ρ := ρ) (N := N) (k := k) hρ.1 hρ.2
    have hE := expD_oscBasis_apply hρ.1 k
    have hnorm : ‖B0094.oscBasis k‖ = 1 := B0094.oscBasis.orthonormal.norm_eq_one k
    rw [hYN, hE, dist_eq_norm, ← sub_smul, norm_smul, hnorm, mul_one,
      ← Complex.ofReal_sub, Complex.norm_real]
    simpa [Real.dist_eq, Real.norm_eq_abs] using hN ρ hρ
  have hspan : ∀ y ∈ (D : Set XG),
      TendstoUniformlyOn (fun N ρ => F N ρ y) (fun ρ => F₀ ρ y) atTop (Icc 0 R) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨k, rfl⟩ := hv
        exact hBasis k
    | zero =>
        rw [Metric.tendstoUniformlyOn_iff]
        intro ε hε
        filter_upwards [] with N ρ hρ
        simpa [F, F₀] using hε
    | add y z hy hz ihy ihz =>
        simpa only [map_add] using tendstoUniformlyOn_add_vec ihy ihz
    | smul c y hy ih =>
        simpa only [map_smul] using tendstoUniformlyOn_smul_vec c ih
  exact tendstoUniformlyOn_apply_of_dense hF hF₀ hD hspan x

/-- Uniform strong convergence of the Hermite diffusion truncations on a compact set of vectors
and a compact interval of diffusion times. This finite-net consequence is what lets the
transport-Dyson limit use the compact orbit of its fixed limiting evolution. -/
theorem unitYosidaDiffusionFamily_tendstoUniformlyOn_expD_compact (R : ℝ) (hR : 0 ≤ R)
    {K : Set XG} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : XG × ℝ => (unitYosidaDiffusionFamily R N).U p.2 0 p.1)
      (fun p : XG × ℝ => B0123.expD p.2 p.1) atTop (K ×ˢ Icc 0 R) := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_cases hKn : K.Nonempty
  · obtain ⟨Nnet, hNnet, hNfinite, hcover⟩ :=
      Metric.finite_approx_of_totallyBounded hK.totallyBounded (ε / 8) (by positivity)
    let centers : Finset XG := hNfinite.toFinset
    have hcenter : ∀ y ∈ centers, ∀ᶠ N : ℕ in atTop,
        ∀ ρ ∈ Icc (0 : ℝ) R,
          dist ((unitYosidaDiffusionFamily R N).U ρ 0 y) (B0123.expD ρ y) < ε / 2 := by
      intro y hy
      have hy' : y ∈ Nnet := (Set.Finite.mem_toFinset hNfinite).mp hy
      have hconv := Metric.tendstoUniformlyOn_iff.1
        (unitYosidaDiffusionFamily_tendstoUniformlyOn_expD R hR y) (ε / 2) (by linarith)
      filter_upwards [hconv] with N hN ρ hρ
      simpa [dist_comm] using hN ρ hρ
    have hfinite : ∀ S : Finset XG,
        (∀ y ∈ S, ∀ᶠ N : ℕ in atTop,
          ∀ ρ ∈ Icc (0 : ℝ) R,
            dist ((unitYosidaDiffusionFamily R N).U ρ 0 y) (B0123.expD ρ y) < ε / 2) →
        ∀ᶠ N : ℕ in atTop, ∀ y ∈ S, ∀ ρ ∈ Icc (0 : ℝ) R,
          dist ((unitYosidaDiffusionFamily R N).U ρ 0 y) (B0123.expD ρ y) < ε / 2 := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
          intro _
          filter_upwards [] with N y hy
          simp at hy
      | @insert y S hy ih =>
          intro hpt
          have hy' := hpt y (Finset.mem_insert_self y S)
          have hrest : ∀ z ∈ S, ∀ᶠ N : ℕ in atTop,
              ∀ ρ ∈ Icc (0 : ℝ) R,
                dist ((unitYosidaDiffusionFamily R N).U ρ 0 z) (B0123.expD ρ z) < ε / 2 := by
            intro z hz
            exact hpt z (Finset.mem_insert_of_mem hz)
          have hrest' := ih hrest
          filter_upwards [hy', hrest'] with N hyN hN z hz ρ hρ
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hyN ρ hρ
          · exact hN z hz ρ hρ
    have hall : ∀ᶠ N : ℕ in atTop, ∀ y ∈ centers, ∀ ρ ∈ Icc (0 : ℝ) R,
        dist ((unitYosidaDiffusionFamily R N).U ρ 0 y) (B0123.expD ρ y) < ε / 2 := by
      exact hfinite centers hcenter
    filter_upwards [hall] with N hN p hp
    rcases hp with ⟨hpK, hpρ⟩
    obtain ⟨y, hyN, hpy⟩ := Set.mem_iUnion₂.mp (hcover hpK)
    have hy : y ∈ centers := (Set.Finite.mem_toFinset hNfinite).mpr hyN
    have hdist : dist p.1 y < ε / 8 := by
      simpa [Metric.mem_ball, dist_comm] using hpy
    have hcenter' := hN y hy p.2 hpρ
    have hcontract₁ : ‖(unitYosidaDiffusionFamily R N).U p.2 0 (p.1 - y)‖ ≤ ‖p.1 - y‖ := by
      exact unitYosidaDiffusionFamily_norm_le hpρ.1 hpρ.2 _
    have hcontract₂ : ‖B0123.expD p.2 (y - p.1)‖ ≤ ‖y - p.1‖ := by
      calc
        ‖B0123.expD p.2 (y - p.1)‖ ≤ ‖B0123.expD p.2‖ * ‖y - p.1‖ :=
          (B0123.expD p.2).le_opNorm _
        _ ≤ 1 * ‖y - p.1‖ := mul_le_mul_of_nonneg_right
          (B0123.norm_expD_le p.2) (norm_nonneg _)
        _ = ‖y - p.1‖ := one_mul _
    have hsplit : (unitYosidaDiffusionFamily R N).U p.2 0 p.1 - B0123.expD p.2 p.1 =
        (unitYosidaDiffusionFamily R N).U p.2 0 (p.1 - y) +
          ((unitYosidaDiffusionFamily R N).U p.2 0 y - B0123.expD p.2 y) +
          B0123.expD p.2 (y - p.1) := by
      simp only [map_sub]
      abel
    have hsplit' : B0123.expD p.2 p.1 -
        (unitYosidaDiffusionFamily R N).U p.2 0 p.1 =
        -((unitYosidaDiffusionFamily R N).U p.2 0 p.1 - B0123.expD p.2 p.1) := by abel
    rw [dist_eq_norm, hsplit', norm_neg, hsplit]
    have hcenterNorm :
        ‖(unitYosidaDiffusionFamily R N).U p.2 0 y - B0123.expD p.2 y‖ < ε / 2 := by
      simpa [dist_eq_norm] using hcenter'
    have hpyNorm : ‖p.1 - y‖ < ε / 8 := by simpa [dist_eq_norm] using hdist
    calc
      ‖(unitYosidaDiffusionFamily R N).U p.2 0 (p.1 - y) +
          ((unitYosidaDiffusionFamily R N).U p.2 0 y - B0123.expD p.2 y) +
          B0123.expD p.2 (y - p.1)‖ ≤
        ‖(unitYosidaDiffusionFamily R N).U p.2 0 (p.1 - y)‖ +
          ‖(unitYosidaDiffusionFamily R N).U p.2 0 y - B0123.expD p.2 y‖ +
          ‖B0123.expD p.2 (y - p.1)‖ := norm_add₃_le
      _ < ε := by
        have hsymm : ‖y - p.1‖ = ‖p.1 - y‖ := norm_sub_rev _ _
        linarith
  · filter_upwards [] with N p hp
    have hempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKn
    simpa [hempty] using hp.1

/-- The actual bounded Yosida approximation to the nonautonomous Gaussian diffusion base. -/
def canonicalYosidaDiffusionFamily {a b : ℝ} (β : ℝ → ℝ) (N : ℕ)
    (hβ : ContinuousOn β (Icc a b)) : EvolutionFamily XG a b :=
  Evolution.dyson (convergenceIdentityFamily (a := a) (b := b))
    (boundedPertOfContinuous (boundedYosidaDiffusionCoefficient β N) (by
      have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
        Complex.continuous_ofReal.continuousOn.comp hβ (fun r hr => Set.mem_univ (β r))
      exact hβc.smul continuousOn_const))

/-- Weak generator of the locally defined nonautonomous bounded diffusion family. -/
theorem canonicalYosidaDiffusionFamily_hasWeakGenerator {a b : ℝ}
    (β : ℝ → ℝ) (N : ℕ) (hβ : ContinuousOn β (Icc a b)) :
    (canonicalYosidaDiffusionFamily β N hβ).HasWeakGenerator Set.univ
      (fun r ℓ => ℓ.comp (boundedYosidaDiffusionCoefficient β N r)) := by
  let C := boundedYosidaDiffusionCoefficient β N
  let A := boundedPertOfContinuous C (by
    have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.continuousOn.comp hβ (fun r hr => Set.mem_univ (β r))
    exact hβc.smul continuousOn_const)
  have hA : ContinuousOn A.A (Icc a b) := by
    change ContinuousOn C (Icc a b)
    have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.continuousOn.comp hβ (fun r hr => Set.mem_univ (β r))
    change ContinuousOn (fun r => ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N) (Icc a b)
    exact hβc.smul continuousOn_const
  have h := Evolution.dyson_hasWeakGenerator
    (convergenceIdentityFamily (a := a) (b := b)) A
    (convergenceIdentity_hasWeakGenerator (a := a) (b := b))
    (by
      intro ℓ hℓ
      exact continuousOn_const) hA
  intro ℓ hℓ s x hs t ht
  simpa [canonicalYosidaDiffusionFamily, A, C, boundedPertOfContinuous] using
    h ℓ hℓ s x hs t ht

/-- Identify the action of the general-coefficient bounded diffusion family with the constant
coefficient family at its integrated diffusion time. The proof is by the genuine Hermite basis
expansion, with both families having the same scalar multiplier on each mode. -/
theorem canonicalYosidaDiffusionFamily_eq_unit {a b s t R : ℝ} (β : ℝ → ℝ)
    (N : ℕ) (hβ : ContinuousOn β (Icc a b)) (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    (hρ : 0 ≤ (∫ r in s..t, β r)) (hρR : (∫ r in s..t, β r) ≤ R) (x : XG) :
    (canonicalYosidaDiffusionFamily β N hβ).U t s x =
      (unitYosidaDiffusionFamily R N).U (∫ r in s..t, β r) 0 x := by
  let ρ : ℝ := ∫ r in s..t, β r
  let U := canonicalYosidaDiffusionFamily β N hβ
  let V := unitYosidaDiffusionFamily R N
  have hterms : ∀ k : ℕ,
      U.U t s (B0094.oscBasis k) = V.U ρ 0 (B0094.oscBasis k) := by
    intro k
    have hU := boundedYosidaDiffusionFamily_basis_action β N k hβ hβ0 has hst ht
    have hV := unitYosidaDiffusionFamily_oscBasis (R := R) (ρ := ρ) (N := N) (k := k)
      hρ hρR
    have hU' : U.U t s (B0094.oscBasis k) =
        ((Real.exp (-(((k : ℝ) * N / (N + k)) * ρ)) : ℝ) : ℂ) • B0094.oscBasis k := by
      simpa [U, canonicalYosidaDiffusionFamily, ρ, mul_comm] using hU
    exact hU'.trans hV.symm
  have hsumU := (B0094.hasSum_components x).mapL (U.U t s)
  have hsumV := (B0094.hasSum_components x).mapL (V.U ρ 0)
  have hEq : U.U t s x = V.U ρ 0 x := by
    apply B0094.ext_inner_basis
    intro j
    change (innerSL ℂ (B0094.oscBasis j)) (U.U t s x) =
      (innerSL ℂ (B0094.oscBasis j)) (V.U ρ 0 x)
    have hu := hsumU.mapL (innerSL ℂ (B0094.oscBasis j))
    have hv := hsumV.mapL (innerSL ℂ (B0094.oscBasis j))
    have hterm : ∀ k : ℕ,
        U.U t s (⟪B0094.oscBasis k, x⟫_ℂ • B0094.oscBasis k) =
          V.U ρ 0 (⟪B0094.oscBasis k, x⟫_ℂ • B0094.oscBasis k) := by
      intro k
      rw [map_smul, map_smul, hterms k]
    have hscalar :
        (innerSL ℂ (B0094.oscBasis j)) (U.U t s x) =
          (innerSL ℂ (B0094.oscBasis j)) (V.U ρ 0 x) := by
      rw [← hu.tsum_eq, ← hv.tsum_eq]
      congr 1
      funext k
      exact congrArg (innerSL ℂ (B0094.oscBasis j)) (hterm k)
    simpa only [innerSL_apply_apply] using hscalar
  simpa [U, V, ρ] using hEq

/-- Uniform convergence of the nonautonomous bounded diffusion family to the concrete Gaussian
base, on compact vector sets and all intermediate endpoints in a fixed interval. The coefficient
enters only through its actual integrated diffusion time. -/
theorem canonicalYosidaDiffusionFamily_tendstoUniformlyOn_freeDiffusion
    {a b s t R : ℝ} (β : ℝ → ℝ) (hβ : ContinuousOn β (Icc a b))
    (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r) (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    (hR : 0 ≤ R)
    (hρ : ∀ r ∈ Icc s t, 0 ≤ (∫ q in r..t, β q) ∧ (∫ q in r..t, β q) ≤ R)
    {K : Set XG} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : XG × ℝ =>
        (canonicalYosidaDiffusionFamily β N hβ).U t p.2 p.1)
      (fun p : XG × ℝ => freeDiffusion β t p.2 p.1) atTop (K ×ˢ Icc s t) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hconv := Metric.tendstoUniformlyOn_iff.1
    (unitYosidaDiffusionFamily_tendstoUniformlyOn_expD_compact R hR hK) ε hε
  filter_upwards [hconv] with N hN p hp
  have htime := hρ p.2 hp.2
  have heq := canonicalYosidaDiffusionFamily_eq_unit β N hβ hβ0
    (le_trans has hp.2.1) hp.2.2 ht htime.1 htime.2 p.1
  rw [heq]
  exact hN (p.1, ∫ q in p.2..t, β q) ⟨hp.1, htime.1, htime.2⟩

/-- Uniform convergence of the nonautonomous bounded diffusion base on the full time triangle.
This supplies one approximation threshold for every intermediate time in a Volterra equation. -/
theorem canonicalYosidaDiffusionFamily_tendstoUniformlyOn_freeDiffusion_triangle
    {a b s t R : ℝ} (β : ℝ → ℝ) (hβ : ContinuousOn β (Icc a b))
    (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r) (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
    (hR : 0 ≤ R)
    (hρ : ∀ p ∈ Evolution.triangle s t,
      0 ≤ (∫ q in p.1..p.2, β q) ∧ (∫ q in p.1..p.2, β q) ≤ R)
    {K : Set XG} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : XG × (ℝ × ℝ) =>
        (canonicalYosidaDiffusionFamily β N hβ).U p.2.2 p.2.1 p.1)
      (fun p : XG × (ℝ × ℝ) => freeDiffusion β p.2.2 p.2.1 p.1)
      atTop (K ×ˢ Evolution.triangle s t) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hconv := Metric.tendstoUniformlyOn_iff.1
    (unitYosidaDiffusionFamily_tendstoUniformlyOn_expD_compact R hR hK) ε hε
  filter_upwards [hconv] with N hN p hp
  rcases hp with ⟨hpK, hpTri⟩
  rcases Evolution.mem_triangle.mp hpTri with ⟨hsp, hpu, hut⟩
  have htime := hρ p.2 hpTri
  have heq := canonicalYosidaDiffusionFamily_eq_unit β N hβ hβ0
    (le_trans has hsp) hpu (le_trans hut ht) htime.1 htime.2 p.1
  rw [heq]
  exact hN (p.1, ∫ q in p.2.1..p.2.2, β q) ⟨hpK, htime.1, htime.2⟩

/-- Every nonnegative bounded-coefficient Hermite diffusion propagator is a contraction. This
follows from its exact identification with the scalar-time Yosida semigroup. -/
theorem canonicalYosidaDiffusionFamily_norm_le {a b r u δ : ℝ} (β : ℝ → ℝ)
    (N : ℕ) (hβ : ContinuousOn β (Icc a b))
    (hβ0 : ∀ q ∈ Icc a b, 0 ≤ β q) (hβδ : ∀ q ∈ Icc a b, β q ≤ δ)
    (hδ : 0 ≤ δ) (har : a ≤ r) (hru : r ≤ u) (hub : u ≤ b) (x : XG) :
    ‖(canonicalYosidaDiffusionFamily β N hβ).U u r x‖ ≤ ‖x‖ := by
  have hβi : IntervalIntegrable β volume r u :=
    (hβ.mono (Icc_subset_Icc har hub)).intervalIntegrable_of_Icc hru
  have hρ0 : 0 ≤ (∫ q in r..u, β q) := intervalIntegral.integral_nonneg hru
    (fun q hq => hβ0 q ⟨har.trans hq.1, hq.2.trans hub⟩)
  have hmono := intervalIntegral.integral_mono_on hru hβi intervalIntegrable_const
    (fun q hq => hβδ q ⟨har.trans hq.1, hq.2.trans hub⟩)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hρR : (∫ q in r..u, β q) ≤ δ * (u-r) := by
    calc
      (∫ q in r..u, β q) ≤ (u-r) * δ := hmono
      _ = δ * (u-r) := by ring
  have hident := canonicalYosidaDiffusionFamily_eq_unit β N hβ hβ0 har hru hub
    hρ0 hρR x
  rw [hident]
  exact unitYosidaDiffusionFamily_norm_le hρ0 hρR x

/-- The two-stage bounded Yosida approximation to the actual first transport-diffusion family. -/
private theorem canonicalYosidaTransportCoefficient_continuous {a b : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (hβ : ContinuousOn β (Icc a b)) :
    ContinuousOn (boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β)
      (Icc a b) := by
  have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.continuousOn.comp hβ (fun r hr => Set.mem_univ (β r))
  have hβκ : ContinuousOn (fun r => ((β r : ℝ) : ℂ) * κ) (Icc a b) :=
    hβc.mul continuousOn_const
  have hβκI : ContinuousOn
      (fun r => (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG)) (Icc a b) :=
    hβκ.smul continuousOn_const
  change ContinuousOn (fun r => UnforcedLeray.B0087.imMulOp -
      lam • (1 : XG →L[ℂ] XG) - (((β r : ℝ) : ℂ) * κ) • (1 : XG →L[ℂ] XG))
    (Icc a b)
  exact (continuousOn_const.sub continuousOn_const).sub hβκI

def canonicalYosidaTransportFamily {a b : ℝ} (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ)
    (hβ : ContinuousOn β (Icc a b)) : EvolutionFamily XG a b :=
  Evolution.dyson (canonicalYosidaDiffusionFamily β N hβ)
    (boundedPertOfContinuous (boundedYosidaTransportCoefficient
      UnforcedLeray.B0087.imMulOp lam κ β)
      (canonicalYosidaTransportCoefficient_continuous lam κ β hβ))

/-- The actual bounded Yosida first-stage evolution obeys the sharp energy estimate uniformly in
the truncation N. Its definition is the two-stage Dyson family used by the signed Hilbert energy
argument. -/
theorem canonicalYosidaTransportFamily_norm_le {a b s t δ : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ) (hβ : ContinuousOn β (Icc a b))
    (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r) (hβδ : ∀ r ∈ Icc a b, β r ≤ δ)
    (hδ : 0 ≤ δ) (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    ‖(canonicalYosidaTransportFamily lam κ β N hβ).U t s x‖ ≤
      Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ := by
  let C := fun r => boundedYosidaDiffusionCoefficient β N r +
    boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β r
  have hUraw := Evolution.dyson_hasWeakGenerator
    (canonicalYosidaDiffusionFamily β N hβ)
    (boundedPertOfContinuous
      (boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β)
      (canonicalYosidaTransportCoefficient_continuous lam κ β hβ))
    (canonicalYosidaDiffusionFamily_hasWeakGenerator β N hβ)
    (diffusionGenerator_continuous β N hβ)
    (canonicalYosidaTransportCoefficient_continuous lam κ β hβ)
  have hU : (canonicalYosidaTransportFamily lam κ β N hβ).HasWeakGenerator Set.univ
      (fun r ℓ => ℓ.comp (C r)) := by
    intro ℓ hℓ s y hs u hu
    have hh := hUraw ℓ hℓ s y hs u hu
    simpa [canonicalYosidaTransportFamily, boundedPertOfContinuous, C,
      ContinuousLinearMap.comp_apply, map_add] using hh
  have hC : ContinuousOn C (Icc a b) := by
    dsimp [C]
    have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.continuousOn.comp hβ (fun r hr => Set.mem_univ (β r))
    have hDiff : ContinuousOn (boundedYosidaDiffusionCoefficient β N) (Icc a b) := by
      change ContinuousOn (fun r => ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N) (Icc a b)
      exact hβc.smul continuousOn_const
    exact hDiff.add
      (canonicalYosidaTransportCoefficient_continuous lam κ β hβ)
  have hDiss : ∀ r ∈ Icc a b, ∀ z : XG,
      (⟪z, C r z⟫_ℂ).re ≤ (-lam.re + δ * |κ.re|) * ‖z‖ ^ 2 := by
    have hcoeff := boundedYosidaCoefficient_quadratic_bound
      UnforcedLeray.B0087.imMulOp UnforcedLeray.B0087.adjoint_imMulOp
      lam κ β N hβ0 hβδ hδ rfl
    intro r hr z
    change (⟪z, (boundedYosidaDiffusionCoefficient β N r +
      boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β r) z⟫_ℂ).re ≤ _
    rw [boundedYosidaCoefficient_eq_sum
      UnforcedLeray.B0087.imMulOp lam κ β N r]
    exact hcoeff r hr z
  exact weakGenerator_norm_le_exp _ C hU
    (boundedYosidaTransportDyson_generator_continuous
      UnforcedLeray.B0087.imMulOp lam κ β N hβ)
    hC has hst ht hDiss x

/-- The bounded-Yosida first-stage family with the exact measurable perturbation wrapper used by
the actual transport-Dyson evolution. Its coefficient is pointwise the same as in
`canonicalYosidaTransportFamily`; this form makes the varying-base mild subtraction literal. -/
def canonicalYosidaTransportFamily_actualPert {a b : ℝ} (lam κ : ℂ) (β : ℝ → ℝ)
    (N : ℕ) (hβ : ContinuousOn β (Icc a b))
    (hβsm : AEStronglyMeasurable β (volume.restrict (Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Icc a b, |β r| ≤ C) : EvolutionFamily XG a b :=
  Evolution.dyson (canonicalYosidaDiffusionFamily β N hβ)
    (transportDysonPert UnforcedLeray.B0087.imMulOp lam κ β a b hβsm hβblock)

/-- The actual-wrapper bounded Yosida family retains the same sharp energy estimate. -/
theorem canonicalYosidaTransportFamily_actualPert_norm_le {a b s t δ : ℝ}
    (lam κ : ℂ) (β : ℝ → ℝ) (N : ℕ) (hβ : ContinuousOn β (Icc a b))
    (hβ0 : ∀ r ∈ Icc a b, 0 ≤ β r) (hβδ : ∀ r ∈ Icc a b, β r ≤ δ)
    (hδ : 0 ≤ δ) (hβsm : AEStronglyMeasurable β (volume.restrict (Icc a b)))
    (hβblock : ∃ C : ℝ, ∀ r ∈ Icc a b, |β r| ≤ C)
    (has : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) (x : XG) :
    ‖(canonicalYosidaTransportFamily_actualPert lam κ β N hβ hβsm hβblock).U t s x‖ ≤
      Real.exp ((-lam.re + δ * |κ.re|) * (t - s)) * ‖x‖ := by
  let C := fun r => boundedYosidaDiffusionCoefficient β N r +
    boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β r
  have hAcont : ContinuousOn
      (fun r => (transportDysonPert UnforcedLeray.B0087.imMulOp lam κ β a b hβsm hβblock).A r)
      (Icc a b) := by
    change ContinuousOn (fun r => boundedYosidaTransportCoefficient
      UnforcedLeray.B0087.imMulOp lam κ β r) (Icc a b)
    exact canonicalYosidaTransportCoefficient_continuous lam κ β hβ
  have hUraw := Evolution.dyson_hasWeakGenerator
    (canonicalYosidaDiffusionFamily β N hβ)
    (transportDysonPert UnforcedLeray.B0087.imMulOp lam κ β a b hβsm hβblock)
    (canonicalYosidaDiffusionFamily_hasWeakGenerator β N hβ)
    (diffusionGenerator_continuous β N hβ) hAcont
  have hU : (canonicalYosidaTransportFamily_actualPert lam κ β N hβ hβsm hβblock).HasWeakGenerator
      Set.univ (fun r ℓ => ℓ.comp (C r)) := by
    intro ℓ hℓ s y hs u hu
    have hh := hUraw ℓ hℓ s y hs u hu
    simpa [canonicalYosidaTransportFamily_actualPert, transportDysonPert,
      boundedYosidaTransportCoefficient, boundedYosidaDiffusionCoefficient,
      UnforcedLeray.B0087.imMulOp, C, ContinuousLinearMap.comp_apply, map_add,
      ContinuousLinearMap.one_apply, smul_eq_mul] using hh
  have hC : ContinuousOn C (Icc a b) := by
    dsimp [C]
    have hβc : ContinuousOn (fun r => ((β r : ℝ) : ℂ)) (Icc a b) :=
      Complex.continuous_ofReal.continuousOn.comp hβ (fun r hr => Set.mem_univ (β r))
    have hDiff : ContinuousOn (boundedYosidaDiffusionCoefficient β N) (Icc a b) := by
      change ContinuousOn (fun r => ((β r : ℝ) : ℂ) • PlanarSpectral.Dyosida N) (Icc a b)
      exact hβc.smul continuousOn_const
    exact hDiff.add (canonicalYosidaTransportCoefficient_continuous lam κ β hβ)
  have hDiss : ∀ r ∈ Icc a b, ∀ z : XG,
      (⟪z, C r z⟫_ℂ).re ≤ (-lam.re + δ * |κ.re|) * ‖z‖ ^ 2 := by
    have hcoeff := boundedYosidaCoefficient_quadratic_bound
      UnforcedLeray.B0087.imMulOp UnforcedLeray.B0087.adjoint_imMulOp
      lam κ β N hβ0 hβδ hδ rfl
    intro r hr z
    change (⟪z, (boundedYosidaDiffusionCoefficient β N r +
      boundedYosidaTransportCoefficient UnforcedLeray.B0087.imMulOp lam κ β r) z⟫_ℂ).re ≤ _
    rw [boundedYosidaCoefficient_eq_sum UnforcedLeray.B0087.imMulOp lam κ β N r]
    exact hcoeff r hr z
  exact weakGenerator_norm_le_exp _ C hU
    (boundedYosidaTransportDyson_generator_continuous
      UnforcedLeray.B0087.imMulOp lam κ β N hβ) hC has hst ht hDiss x

end UnforcedLeray.Cons.G3b
