import UnforcedLeray.Cons.L2.CanonicalBranch.Bridge
import UnforcedLeray.Short.PartI.Tasks.AdjointKernelOneDim
import UnforcedLeray.Short.PartI.Tasks.SeedFunctionalProof
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c5_2_2
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4.EllSelf

/-!
# `PartIII-a:T21/c5/2/1/2`, helper: the drift exponent `κ = ℓ(Dq)` of a planar reference

Source: `the November 2 reference manuscript` (SP), lines 593-610 (the seed
`(λ, q, ℓ)` and `ℓ(f) = J_q⁻¹ ∫ h f₂ / k r dr`) and 2991-2995 (the amplitude diagonal
`λ_i + κ_i/θ`).

For a Part I seed triple `(λ, q = h e^{2iϑ}, ℓ)` and a planar reference `P` (`IsPlanarReference P`),
`P.kappa = ⟨D q_P, q_P†⟩ = seedEll h (D h)`:

* `L₀` has a unique growing eigenline (`Planar.L0_eigen_unique`), so `q_P = μ q`;
* the left eigenfunctional `ψ = ⟨·, q_P†⟩` annihilates `ker ℓ = range (λ - L₀)`
  (`PartI.seed_kernel_mem_range`), so `ψ = ψ(q) ℓ`, and `ψ(q_P) = 1` gives `μ ψ(q) = 1`;
* `D q_P = μ D h` on `(0, ∞)` (the profiles agree pointwise there by continuity), and
  `ℓ = seedEll h` on `X_G` (`PartI.seedFunctional_proof`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff ComplexConjugate

namespace UnforcedLeray.Short.IIIa.OscGramKappa

/-- `oscillatorD` respects a pointwise scalar identity on `(0, ∞)`. -/
theorem oscillatorD_eq_smul_of_eqOn {f g : ℝ → ℂ} {μ : ℂ}
    (hfg : ∀ r : ℝ, 0 < r → f r = μ * g r) {r : ℝ} (hr : 0 < r) :
    oscillatorD f r = μ * oscillatorD g r := by
  have hev : f =ᶠ[𝓝 r] fun s => μ * g s :=
    Filter.eventually_of_mem (Ioi_mem_nhds hr) fun s hs => hfg s hs
  have h1 : deriv f r = μ * deriv g r := by
    rw [hev.deriv_eq, deriv_const_mul_field']
  have h2 : deriv (deriv f) r = μ * deriv (deriv g) r := by
    rw [hev.deriv.deriv_eq, deriv_const_mul_field', deriv_const_mul_field']
  unfold oscillatorD
  rw [h1, h2, hfg r hr]
  ring

/-- `seedEll h` is homogeneous. -/
theorem seedEll_const_mul (h f : ℝ → ℂ) (μ : ℂ) :
    PartI.seedEll h (fun r => μ * f r) = μ * PartI.seedEll h f := by
  unfold PartI.seedEll
  have e : (fun r : ℝ => h r * (μ * f r) / (strainK r : ℂ) * (r : ℂ)) =
      fun r : ℝ => μ * (h r * f r / (strainK r : ℂ) * (r : ℂ)) := by
    funext r
    ring
  rw [e, integral_const_mul]
  ring

/-- Representatives of `X_G` elements are `X_G` profiles. -/
theorem memXG_coeFn (y : B0010.XG) : MemXG (y : ℝ → ℂ) :=
  Cons.G3b.memXG_of_memLp ((Lp.aestronglyMeasurable y).mono_ac B0012.restrict_ac) (Lp.memLp y)

/-- **`κ = ℓ(Dq)`** (SP 593-610, 2991-2995): for a seed triple `(λ, hh.toLp h, ℓ)` with smooth
profile `h` on `(0, ∞)` and a planar reference `P`, `P.kappa = seedEll h (oscillatorD h)`. -/
theorem kappa_eq_seedEll {lam : ℂ} {h : ℝ → ℂ} {hh : MemLp h 2 B0010.xGMeasure}
    {ℓ : B0010.XG →L[ℂ] ℂ} (hIS : PartI.IsSeedXG lam (hh.toLp h) ℓ)
    (hsm : ContDiffOn ℝ ∞ h (Ioi 0)) (P : PlanarData) (hP : IsPlanarReference P) :
    P.kappa = PartI.seedEll h (oscillatorD h) := by
  have hPL : (Planar.L0 : B0010.XG →L[ℂ] B0010.XG) = B0012.L0 := rfl
  -- the eigenvector of `P` as an element of `X_G`
  set hmP := Cons.G3b.memLp_of_memXG hP.eigenpair.memXG with hmP_def
  set qP : B0010.XG := hmP.toLp P.mode with hqP_def
  set q : B0010.XG := hh.toLp h with hq_def
  have hqP_eigen : Planar.L0 qP = P.eigenvalue • qP := by
    rw [hPL]
    change B0012.L0 (hmP.toLp P.mode) = P.eigenvalue • qP
    rw [B0012.L0_toLp hmP]
    apply Lp.ext
    filter_upwards [B0012.ae_xG_pos, (B0012.memLp_L0Fun hmP).coeFn_toLp,
      hmP.coeFn_toLp, Lp.coeFn_smul P.eigenvalue qP] with r hr hL hq' hsmul
    have hq'' : ((qP : B0010.XG) : ℝ → ℂ) r = P.mode r := hq'
    rw [hL]
    change B0012.L0Fun P.mode r = ((P.eigenvalue • qP : B0010.XG) : ℝ → ℂ) r
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hq'', ← DirectEulerSub.generatorL0_eq_L0Fun P.mode r,
      hP.eigenpair.eigen r hr]
  have hqP_ne : qP ≠ 0 := by
    intro h0
    apply hP.eigenpair.nonzero
    have hzeroX : P.mode =ᵐ[B0010.xGMeasure] (0 : ℝ → ℂ) := by
      filter_upwards [hmP.coeFn_toLp,
        (show (⇑qP : ℝ → ℂ) =ᵐ[B0010.xGMeasure] 0 from by
          rw [h0]; exact Lp.coeFn_zero ℂ 2 B0010.xGMeasure)] with r h1 h2
      rw [← h1, h2]
    exact B0012.restrict_ac.ae_le hzeroX
  obtain ⟨hlam, μ, hμ⟩ := Planar.L0_eigen_unique hIS.re_pos hP.eigenpair.re_pos
    hIS.eigen hqP_eigen hIS.ne_zero hqP_ne
  -- the left eigenfunctional `ψ = ⟪q_P†, ·⟫`
  set qdag : B0010.XG := (Cons.G3b.memLp_of_memXG hP.adjoint.memXG).toLp P.adjointMode
    with hqdag_def
  have hpair : ∀ {f : Profile} (hf : MemXG f),
      gaussianPairing f P.adjointMode =
        inner ℂ qdag ((Cons.G3b.memLp_of_memXG hf).toLp f) :=
    fun hf => Cons.G3b.gaussianPairing_eq_inner hf hP.adjoint.memXG
  have hL0 : ∀ y : B0010.XG, inner ℂ qdag (Planar.L0 y) = lam * inner ℂ qdag y := by
    intro y
    have hmy : MemLp (y : ℝ → ℂ) 2 B0010.xGMeasure := Lp.memLp y
    have heq : generatorL0 (y : ℝ → ℂ) = B0012.L0Fun (y : ℝ → ℂ) :=
      funext (DirectEulerSub.generatorL0_eq_L0Fun _)
    have hgen : MemXG (generatorL0 (y : ℝ → ℂ)) := by
      rw [heq]
      exact Cons.G3b.memXG_of_memLp
        ((B0012.memLp_L0Fun hmy).aestronglyMeasurable.mono_ac B0012.restrict_ac)
        (B0012.memLp_L0Fun hmy)
    have h1 := hP.adjoint.left_eigen _ (memXG_coeFn y)
    rw [hpair hgen, hpair (memXG_coeFn y)] at h1
    have e1 : (Cons.G3b.memLp_of_memXG (memXG_coeFn y)).toLp (y : ℝ → ℂ) = y :=
      Lp.toLp_coeFn y _
    have e2 : (Cons.G3b.memLp_of_memXG hgen).toLp (generatorL0 (y : ℝ → ℂ)) = Planar.L0 y := by
      apply Lp.ext
      refine (MemLp.coeFn_toLp _).trans ?_
      rw [hPL]
      filter_upwards [B0012.coeFn_L0 y] with r hr
      rw [hr, heq]
    rw [e1, e2, hlam] at h1
    exact h1
  -- `ψ` vanishes on `ker ℓ`, hence `ψ = ψ(q) ℓ`
  have hker : ∀ x : B0010.XG, ℓ x = 0 → inner ℂ qdag x = 0 := by
    intro x hx
    obtain ⟨y, hy⟩ := PartI.seed_kernel_mem_range hIS hx
    rw [hy, inner_sub_right, inner_smul_right, hL0 y, sub_self]
  have hfac : ∀ f : B0010.XG, inner ℂ qdag f = ℓ f * inner ℂ qdag q := by
    intro f
    have hx : ℓ (f - ℓ f • q) = 0 := by
      rw [map_sub, map_smul, hIS.ell_q, smul_eq_mul, mul_one, sub_self]
    have h0 := hker _ hx
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at h0
    exact h0
  -- normalization: `μ ψ(q) = 1`
  have hnorm : μ * inner ℂ qdag q = 1 := by
    have h1 := hP.adjoint.normalized
    rw [hpair hP.eigenpair.memXG] at h1
    change inner ℂ qdag qP = 1 at h1
    rw [hμ, inner_smul_right] at h1
    exact h1
  -- the profiles: `P.mode = μ h` on `(0, ∞)`
  have hae : P.mode =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => μ * h r := by
    have hX : P.mode =ᵐ[B0010.xGMeasure] fun r => μ * h r := by
      filter_upwards [hmP.coeFn_toLp, hh.coeFn_toLp, Lp.coeFn_smul μ q,
        (show (⇑qP : ℝ → ℂ) =ᵐ[B0010.xGMeasure] ⇑(μ • q) from by rw [hμ])] with r h1 h2 h3 h4
      have h1' : (qP : ℝ → ℂ) r = P.mode r := h1
      have h2' : (q : ℝ → ℂ) r = h r := h2
      rw [← h1', h4, h3, Pi.smul_apply, smul_eq_mul, h2']
    exact B0012.restrict_ac.ae_le hX
  have hEq : EqOn P.mode (fun r => μ * h r) (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hP.eigenpair.smooth.continuousOn
      (continuousOn_const.mul hsm.continuousOn)
  have hD : ∀ r : ℝ, 0 < r → oscillatorD P.mode r = μ * oscillatorD h r :=
    fun r hr => oscillatorD_eq_smul_of_eqOn (fun s hs => hEq hs) hr
  -- `κ = ψ(D q_P) = ℓ(D q_P) ψ(q) = μ seedEll h (D h) ψ(q)`
  have hSF := (PartI.seedFunctional_proof lam h hh ℓ hIS).2.2.2.1
  have hmD := Cons.G3b.memLp_of_memXG hP.oscillator_memXG
  have hk : P.kappa = inner ℂ qdag (hmD.toLp (oscillatorD P.mode)) := hpair hP.oscillator_memXG
  rw [hk, hfac, hSF]
  have hrep : PartI.seedEll h ((hmD.toLp (oscillatorD P.mode) : B0010.XG) : ℝ → ℂ) =
      PartI.seedEll h (oscillatorD P.mode) := by
    unfold PartI.seedEll
    congr 1
    apply integral_congr_ae
    filter_upwards [SeedEllSelfAux.ae_toLp_eq _ hmD] with r hr
    rw [hr]
  rw [hrep, IIIa.seedEll_congr h _ _ hD, seedEll_const_mul]
  linear_combination (PartI.seedEll h (oscillatorD h)) * hnorm

end UnforcedLeray.Short.IIIa.OscGramKappa
