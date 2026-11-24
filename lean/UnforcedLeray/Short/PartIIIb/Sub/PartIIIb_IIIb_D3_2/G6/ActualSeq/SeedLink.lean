import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G6Org
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G2.g2ModeBounds
import UnforcedLeray.Short.PartIIIa.Clock.FrameKernels
import UnforcedLeray.Short.PartIIIa.Sub.T21_c1_a_4

/-!
# `PartIII-b:IIIb-D3/2/G6/5/org`: existence of planar seed kernels with `SeedLink`

Source of record: `the November 2 reference manuscript` (73 pages):
Proposition `short-gaussian-seed` lines 593-610 (`ℓ(H) = M_q / J_q ≠ 0`), moving frame
2891-2897, Gaussian sources 4565-4570 (`H₀ = r E₀'(r) e^{2iϑ} = r² k(r) e^{2iϑ}`),
limiting amplitude and direct/dual comparison 4614-4618, 4650-4654 (`∫ λ₀ H₀ = ℓ₊(H₀)`).

Rescaling the seed eigenvector gauge by `t ≠ 0` (`q ↦ t q`, `ℓ ↦ t⁻¹ ℓ`, `e₀ ↦ t e₀`,
`e₁ ↦ t̄ e₁`, `λ₀ ↦ t⁻¹ λ₀`, `λ₁ ↦ t̄⁻¹ λ₁`) preserves `IIIa.IsSeedKernels` and scales
`∫ λ₀ H₀` by `t⁻¹`. Since the unscaled seed kernel satisfies `∫ λ₀ H₀ = ℓ(H) ≠ 0` and
`D.Pl.strainCoupling ≠ 0` (`D.strainCoupling_ne`), choosing `t = (∫ λ₀ H₀) / D.Pl.strainCoupling`
yields `SeedLink D κ'`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory UnforcedLeray.Blueprint.Planar
open scoped ComplexConjugate ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6.ActualSeqAux

open FlatSettingInst

private lemma norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private lemma planeToC_eq (y : ℝ × ℝ) :
    IIIa.planeToC y = (y.1 : ℂ) + (y.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [IIIa.planeToC]

private lemma norm_planeToC (y : ℝ × ℝ) : ‖IIIa.planeToC y‖ = planeR y := by
  have h1 : ‖IIIa.planeToC y‖ ^ 2 = y.1 ^ 2 + y.2 ^ 2 := by
    rw [norm_sq_eq]; rfl
  have h2 : 0 ≤ ‖IIIa.planeToC y‖ := norm_nonneg _
  unfold planeR
  rw [← h1, Real.sqrt_sq h2]

private lemma seedPlanar_strainProfile_eq (z : ℂ) :
    PartI.seedPlanar strainProfile z = ((strainK ‖z‖ : ℝ) : ℂ) * z ^ 2 := by
  unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile Planar.NUE.Ang.angPhase strainProfile
  by_cases hz : z = 0
  · subst hz; simp
  · have hnorm : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hz)
    push_cast
    rw [zpow_ofNat, div_pow]
    field_simp [hnorm]

private lemma contDiff_seedPlanar_strainProfile :
    ContDiff ℝ ∞ (PartI.seedPlanar strainProfile) := by
  have heq : PartI.seedPlanar strainProfile = fun z : ℂ =>
      ((((z.re ^ 2 + z.im ^ 2) / 4 - 2) * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 4) : ℝ) : ℂ) *
        z ^ 2 := by
    ext z
    rw [seedPlanar_strainProfile_eq]
    unfold strainK
    rw [norm_sq_eq]
  rw [heq]
  have hre : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hsq : ContDiff ℝ ∞ (fun z : ℂ => z.re ^ 2 + z.im ^ 2) :=
    (hre.pow 2).add (him.pow 2)
  have hreal : ContDiff ℝ ∞ (fun z : ℂ =>
      ((z.re ^ 2 + z.im ^ 2) / 4 - 2) * Real.exp (-(z.re ^ 2 + z.im ^ 2) / 4)) :=
    ((hsq.div_const 4).sub contDiff_const).mul (Real.contDiff_exp.comp (hsq.neg.div_const 4))
  exact (Complex.ofRealCLM.contDiff.comp hreal).mul (contDiff_id.pow 2)

private lemma gaussRdE_one_eq_strainProfile (r : ℝ) :
    gaussRdE 1 r = r ^ 2 * strainK r := by
  rw [G2.g2mb_gaussRdE_one]
  unfold strainK
  ring

private lemma seedPlanar_strainProfile_planeToC (y : ℝ × ℝ) :
    PartI.seedPlanar strainProfile (IIIa.planeToC y) = hMode 1 y := by
  rw [seedPlanar_strainProfile_eq, norm_planeToC]
  unfold hMode IIIa.angTwo
  rw [gaussRdE_one_eq_strainProfile, ← planeToC_eq]
  by_cases hy : y.1 ^ 2 + y.2 ^ 2 = 0
  · have hr0 : planeR y ^ 2 = 0 := by rw [G2.g2mb_planeR_sq, hy]
    have hz : IIIa.planeToC y = 0 := by
      have h1 : y.1 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      have h2 : y.2 = 0 := by nlinarith [sq_nonneg y.1, sq_nonneg y.2]
      apply Complex.ext <;> simp [IIIa.planeToC, h1, h2]
    rw [hz, hy]
    simp [hr0]
  · have hyC : ((y.1 : ℂ) ^ 2 + (y.2 : ℂ) ^ 2) ≠ 0 := by
      exact_mod_cast hy
    have hr2 : (planeR y : ℂ) ^ 2 = (y.1 : ℂ) ^ 2 + (y.2 : ℂ) ^ 2 := by
      exact_mod_cast G2.g2mb_planeR_sq y
    push_cast
    rw [hr2]
    field_simp [hyC]

/-- There exists a planar seed kernel `κ₀` whose `λ₀` pairing with `hMode 1` is nonzero. -/
theorem exists_seedKernels_pairing_ne_zero :
    ∃ κ₀ : IIIa.PlanarFrameKernels, IIIa.IsSeedKernels κ₀ ∧
      (∫ y, κ₀.lamP 0 y * hMode 1 y) ≠ 0 := by
  obtain ⟨lam, h, hh, ℓ, hS, hsm, hon, hdec⟩ :=
    seedSmoothRep_proof PartI.seedModeRegularity_proof PartI.seedXGExists
  obtain ⟨CG, hCG⟩ := seedGaussHalf_proof h hdec
  obtain ⟨lamP, hc, hd, hcl⟩ :=
    seedDualKernel_proof PartI.seedFunctional_proof lam h hh ℓ hS hsm hon
  have hb := seedBiorth_proof PartI.seedFunctional_proof lam h hh ℓ hS hsm ⟨CG, hCG⟩ lamP hc hd hcl
  let e : Fin 2 → ℝ × ℝ → ℂ := fun j y =>
    if j = 0 then PartI.seedPlanar h (IIIa.planeToC y)
    else conj (PartI.seedPlanar h (IIIa.planeToC y))
  have hcont : Continuous fun y : ℝ × ℝ => PartI.seedPlanar h (IIIa.planeToC y) := by
    refine hsm.continuous.comp ?_
    exact Complex.equivRealProdCLM.symm.continuous.comp continuous_id |>.congr (fun _ => rfl)
  let κ₀ : IIIa.PlanarFrameKernels :=
    { e := e
      lamP := lamP
      e_cont := fun i => by
        by_cases hi : i = 0
        · simp only [e, hi, if_true]; exact hcont
        · simp only [e, hi, if_false]; exact Complex.continuous_conj.comp hcont
      lamP_cont := hc
      e_decay := ⟨CG, fun i y => by
        by_cases hi : i = 0
        · simp only [e, hi, if_true]; exact hCG y
        · simp only [e, hi, if_false, Complex.norm_conj]; exact hCG y⟩
      lamP_decay := hd
      biorth := fun i j => by simpa [e] using hb i j }
  have hκ₀ : IIIa.IsSeedKernels κ₀ := ⟨lam, h, hh, ℓ, hS, fun _ => rfl, fun _ => rfl, hcl⟩
  refine ⟨κ₀, hκ₀, ?_⟩
  obtain ⟨_, _, Kh, hKh⟩ := G2.g2ModeBounds
  have hfG : ∃ C : ℝ, ∀ y : ℝ × ℝ,
      ‖PartI.seedPlanar strainProfile (IIIa.planeToC y)‖ ≤
        C * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) :=
    ⟨Kh, fun y => by rw [seedPlanar_strainProfile_planeToC]; exact (hKh y).1⟩
  have hext := (seedBiorthExt_proof PartI.seedFunctional_proof lam h hh ℓ hS hsm ⟨CG, hCG⟩
    lamP hc hd hcl (PartI.seedPlanar strainProfile) contDiff_seedPlanar_strainProfile hfG).1
  have hint : (∫ y, κ₀.lamP 0 y * hMode 1 y) =
      ∫ y, lamP 0 y * PartI.seedPlanar strainProfile (IIIa.planeToC y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [seedPlanar_strainProfile_planeToC]
  rw [hint, hext, IIIa.seedEll_congr h _ strainProfile
    (fun r hr => (seedSectors_proof strainProfile r hr).1)]
  exact (PartI.seedStrainCoupling_of PartI.seedModeRegularity_proof
    PartI.seedFunctional_proof lam h hh ℓ hS).2

/-- Rescaling planar seed kernels by `t ≠ 0` preserves `IsSeedKernels` and scales the `λ₀`
integral by `t⁻¹`. -/
theorem rescale_seedKernels (κ : IIIa.PlanarFrameKernels) (hκ : IIIa.IsSeedKernels κ)
    {t : ℂ} (ht : t ≠ 0) :
    ∃ κ' : IIIa.PlanarFrameKernels, IIIa.IsSeedKernels κ' ∧
      ∀ g : ℝ × ℝ → ℂ, (∫ y, κ'.lamP 0 y * g y) = t⁻¹ * (∫ y, κ.lamP 0 y * g y) := by
  have htc : conj t ≠ 0 := star_ne_zero.2 ht
  obtain ⟨Ce, hCe⟩ := κ.e_decay
  obtain ⟨Cl, hCl⟩ := κ.lamP_decay
  let e' : Fin 2 → ℝ × ℝ → ℂ := fun i y =>
    if i = 0 then t * κ.e 0 y else conj t * κ.e 1 y
  let lamP' : Fin 2 → ℝ × ℝ → ℂ := fun i y =>
    if i = 0 then t⁻¹ * κ.lamP 0 y else (conj t)⁻¹ * κ.lamP 1 y
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  let κ' : IIIa.PlanarFrameKernels :=
    { e := e'
      lamP := lamP'
      e_cont := fun i => by
        fin_cases i <;> simp only [e', Fin.zero_eta, Fin.mk_one, if_pos rfl, if_neg h10] <;>
          exact continuous_const.mul (κ.e_cont _)
      lamP_cont := fun i => by
        fin_cases i <;> simp only [lamP', Fin.zero_eta, Fin.mk_one, if_pos rfl, if_neg h10] <;>
          exact continuous_const.mul (κ.lamP_cont _)
      e_decay := ⟨‖t‖ * |Ce|, fun i y => by
        have h1 : ‖e' i y‖ ≤ ‖t‖ * ‖κ.e i y‖ := by
          fin_cases i <;> simp [e']
        calc ‖e' i y‖ ≤ ‖t‖ * ‖κ.e i y‖ := h1
          _ ≤ ‖t‖ * (Ce * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
            mul_le_mul_of_nonneg_left (hCe i y) (norm_nonneg t)
          _ ≤ ‖t‖ * (|Ce| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (le_abs_self Ce) (Real.exp_pos _).le) (norm_nonneg t)
          _ = ‖t‖ * |Ce| * Real.exp (-(y.1 ^ 2 + y.2 ^ 2) / 8) := by ring⟩
      lamP_decay := ⟨‖t⁻¹‖ * |Cl|, fun i y => by
        have h1 : ‖lamP' i y‖ ≤ ‖t⁻¹‖ * ‖κ.lamP i y‖ := by
          fin_cases i <;> simp [lamP']
        have hpos : 0 ≤ (1 + |y.1| + |y.2|)⁻¹ ^ 2 := by positivity
        calc ‖lamP' i y‖ ≤ ‖t⁻¹‖ * ‖κ.lamP i y‖ := h1
          _ ≤ ‖t⁻¹‖ * (Cl * (1 + |y.1| + |y.2|)⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (hCl i y) (norm_nonneg _)
          _ ≤ ‖t⁻¹‖ * (|Cl| * (1 + |y.1| + |y.2|)⁻¹ ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self Cl) hpos)
              (norm_nonneg _)
          _ = ‖t⁻¹‖ * |Cl| * (1 + |y.1| + |y.2|)⁻¹ ^ 2 := by ring⟩
      biorth := fun i j => by
        fin_cases i <;> fin_cases j <;>
          simp only [lamP', e', Fin.zero_eta, Fin.mk_one, if_pos rfl, if_neg h10, if_neg h01]
        · have heq : (fun y => t⁻¹ * κ.lamP 0 y * (t * κ.e 0 y)) =
              fun y => κ.lamP 0 y * κ.e 0 y := by
            ext y; calc t⁻¹ * κ.lamP 0 y * (t * κ.e 0 y)
                = (t⁻¹ * t) * (κ.lamP 0 y * κ.e 0 y) := by ring
              _ = κ.lamP 0 y * κ.e 0 y := by rw [inv_mul_cancel₀ ht, one_mul]
          rw [heq]; simpa using κ.biorth 0 0
        · have heq : (fun y => t⁻¹ * κ.lamP 0 y * (conj t * κ.e 1 y)) =
              fun y => (t⁻¹ * conj t) * (κ.lamP 0 y * κ.e 1 y) := by ext y; ring
          have hb01 : (∫ y, κ.lamP 0 y * κ.e 1 y) = 0 := by simpa [h01] using κ.biorth 0 1
          rw [heq, integral_const_mul, hb01, mul_zero]
        · have heq : (fun y => (conj t)⁻¹ * κ.lamP 1 y * (t * κ.e 0 y)) =
              fun y => ((conj t)⁻¹ * t) * (κ.lamP 1 y * κ.e 0 y) := by ext y; ring
          have hb10 : (∫ y, κ.lamP 1 y * κ.e 0 y) = 0 := by simpa [h10] using κ.biorth 1 0
          rw [heq, integral_const_mul, hb10, mul_zero]
        · have heq : (fun y => (conj t)⁻¹ * κ.lamP 1 y * (conj t * κ.e 1 y)) =
              fun y => κ.lamP 1 y * κ.e 1 y := by
            ext y; calc (conj t)⁻¹ * κ.lamP 1 y * (conj t * κ.e 1 y)
                = ((conj t)⁻¹ * conj t) * (κ.lamP 1 y * κ.e 1 y) := by ring
              _ = κ.lamP 1 y * κ.e 1 y := by rw [inv_mul_cancel₀ htc, one_mul]
          rw [heq]; simpa using κ.biorth 1 1 }
  obtain ⟨lam, h, hh, ℓ, hS, he0, he1, hcl⟩ := hκ
  let h' : ℝ → ℂ := t • h
  have hh' : MemLp h' 2 B0010.xGMeasure := hh.const_smul t
  let ℓ' : B0010.XG →L[ℂ] ℂ := t⁻¹ • ℓ
  have htoLp : hh'.toLp h' = t • hh.toLp h := MemLp.toLp_const_smul t hh
  have hrp : UnforcedLeray.Infra.Dunford.rankOneProj ℓ' (hh'.toLp h') =
      UnforcedLeray.Infra.Dunford.rankOneProj ℓ (hh.toLp h) := by
    ext1 x
    rw [htoLp, UnforcedLeray.Infra.Dunford.rankOneProj_apply,
      UnforcedLeray.Infra.Dunford.rankOneProj_apply]
    change ((t⁻¹ * ℓ x) • (t • hh.toLp h)) = (ℓ x • hh.toLp h)
    rw [smul_smul, mul_comm (t⁻¹), mul_assoc, inv_mul_cancel₀ ht, mul_one]
  have hS' : PartI.IsSeedXG lam (hh'.toLp h') ℓ' :=
    { re_pos := hS.re_pos
      ne_zero := by rw [htoLp]; exact smul_ne_zero ht hS.ne_zero
      eigen := by rw [htoLp, map_smul, hS.eigen, smul_comm]
      ell_q := by
        rw [htoLp]
        change t⁻¹ * ℓ (t • hh.toLp h) = 1
        rw [map_smul, smul_eq_mul, hS.ell_q, mul_one, inv_mul_cancel₀ ht]
      proj := by rw [hrp]; exact hS.proj }
  have hsp : ∀ z : ℂ, PartI.seedPlanar h' z = t * PartI.seedPlanar h z := by
    intro z
    unfold PartI.seedPlanar Planar.NUE.Ang.ofProfile
    simp only [h', Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hJ : PartI.seedJ h' = t ^ 2 * PartI.seedJ h := by
    unfold PartI.seedJ
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp only [h', Pi.smul_apply, smul_eq_mul]
    ring
  have hEll : ∀ g : ℝ → ℂ, PartI.seedEll h' g = t⁻¹ * PartI.seedEll h g := by
    intro g
    unfold PartI.seedEll
    rw [hJ]
    have h1 : (∫ r in Ioi (0 : ℝ), h' r * g r / (strainK r : ℂ) * (r : ℂ)) =
        t * ∫ r in Ioi (0 : ℝ), h r * g r / (strainK r : ℂ) * (r : ℂ) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      simp only [h', Pi.smul_apply, smul_eq_mul]
      ring
    rw [h1, mul_inv]
    have ht2 : (t ^ 2)⁻¹ * t = t⁻¹ := by
      rw [sq, mul_inv, mul_assoc, inv_mul_cancel₀ ht, mul_one]
    calc (t ^ 2)⁻¹ * (PartI.seedJ h)⁻¹ *
          (t * ∫ r in Ioi (0 : ℝ), h r * g r / (strainK r : ℂ) * (r : ℂ))
        = ((t ^ 2)⁻¹ * t) *
          ((PartI.seedJ h)⁻¹ * ∫ r in Ioi (0 : ℝ), h r * g r / (strainK r : ℂ) * (r : ℂ)) := by ring
      _ = t⁻¹ *
          ((PartI.seedJ h)⁻¹ * ∫ r in Ioi (0 : ℝ), h r * g r / (strainK r : ℂ) * (r : ℂ)) := by
        rw [ht2]
  refine ⟨κ', ⟨lam, h', hh', ℓ', hS', ?_, ?_, ?_⟩, ?_⟩
  · intro y
    change e' 0 y = PartI.seedPlanar h' (IIIa.planeToC y)
    simp only [e', if_pos rfl, he0 y, hsp]
  · intro y
    change e' 1 y = conj (PartI.seedPlanar h' (IIIa.planeToC y))
    simp only [e', if_neg h10, he1 y, hsp, map_mul]
  · intro f hf hfc
    obtain ⟨h0, h1⟩ := hcl f hf hfc
    constructor
    · change (∫ y, lamP' 0 y * f (IIIa.planeToC y)) = _
      have heq : (fun y => lamP' 0 y * f (IIIa.planeToC y)) =
          fun y => t⁻¹ * (κ.lamP 0 y * f (IIIa.planeToC y)) := by
        ext y; simp only [lamP', if_pos rfl, mul_assoc]
      rw [heq, integral_const_mul, h0, hEll]
    · change (∫ y, lamP' 1 y * f (IIIa.planeToC y)) = _
      have heq : (fun y => lamP' 1 y * f (IIIa.planeToC y)) =
          fun y => (conj t)⁻¹ * (κ.lamP 1 y * f (IIIa.planeToC y)) := by
        ext y
        simp only [lamP', if_neg h10, mul_assoc]
      rw [heq, integral_const_mul, h1, hEll, map_mul, map_inv₀]
  · intro g
    change (∫ y, lamP' 0 y * g y) = _
    have heq : (fun y => lamP' 0 y * g y) = fun y => t⁻¹ * (κ.lamP 0 y * g y) := by
      ext y; simp only [lamP', if_pos rfl, mul_assoc]
    rw [heq, integral_const_mul]

/-- Every `D : SeqData` admits planar seed kernels `κ` satisfying `SeedLink D κ`. -/
theorem seedLink_exists (D : SeqData) : ∃ κ : IIIa.PlanarFrameKernels, SeedLink D κ := by
  obtain ⟨κ₀, hκ₀, hI⟩ := exists_seedKernels_pairing_ne_zero
  have hsc : D.Pl.strainCoupling ≠ 0 := D.strainCoupling_ne
  set I0 : ℂ := ∫ y, κ₀.lamP 0 y * hMode 1 y
  have ht : I0 / D.Pl.strainCoupling ≠ 0 := div_ne_zero hI hsc
  obtain ⟨κ, hκ, hscale⟩ := rescale_seedKernels κ₀ hκ₀ ht
  refine ⟨κ, hκ, ?_⟩
  rw [hscale (hMode 1), inv_div, div_mul_cancel₀ _ hI]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G6.ActualSeqAux
