import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T22
import UnforcedLeray.Lib.CylinderB.Periodize
import UnforcedLeray.Lib.Gaussian.PeriodizationCell
import UnforcedLeray.Lib.PlanarSectorsB.LaterIdentities

/-!
# Part III-a, task `PartIII-a:T22/2/1`: prepared datum and periodized canonical branch properties

Source of record: `the November 2 reference manuscript`, lines 3121-3128,
3223-3225, and 3300-3302 (`CTCanonicalBranchProps` in `Sub/PartIII-a_T22.lean`).

## Proved results (`0 sorry`)
* General Gaussian periodization package on `X_{m,d}` (`1 ≤ d`, `0 < m`) for any radial profile
  `f : Profile` with `MemXG f` and `ContinuousOn f (Ioi 0)`:
  - `MemLp (periodizeC d (planarMode f)) 2 (B0579.cellMeasure d m)`,
  - `HasZeroCirculation d (periodizeC d (planarMode f))`,
  - `IsCentrallyEven (periodizeC d (planarMode f))`,
  - `quadQ d (periodizeC d (planarMode f)) = quadrupole f`,
  - uniform `X_{m,d}` bound `xNorm d m (periodizeC d (planarMode f)) ≤ ENNReal.ofReal (K_m * gaussianNorm f)`.
* `PreparedDatumAux.ctCanonicalBranchProps_one_two_three`: Clauses 1, 2, and 3 of
  `CTCanonicalBranchProps` proved unconditionally for every `IsPlanarReference P`.
* `PreparedDatumAux.isXGContinuous_of_canonicalSolution`: any profile curve `W` representing a
  `PartI.IsCanonicalSolution V` satisfies `Cons.C01.IsXGContinuous W`.
* `ctCanonicalBranchProps_at`: all four clauses of `CTCanonicalBranchProps` at any
  `P : PlanarData` satisfying `IsPlanarReference P` and `Cons.C01.IsXGContinuous P.canonical`
  (needed for Clause 4 on `(1, min b θ₁)` when `1 < b` and `1 < θ₁`, since
  `Blueprint.Planar.IsCanonicalBranch` only bounds `(0, 1]` and `[θ₁, ∞)`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Blueprint.Planar
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa.T22Sub

open UnforcedLeray.Short.IIIa

/-! ## 1. Cell, angular-two mode, and `X_G` norm bridges -/

private theorem b0579_cell_eq_cyl_cell (d : ℝ) :
    B0579.cell d = UnforcedLeray.Cyl.cell d := by
  simp only [B0579.cell, UnforcedLeray.Cyl.cell, neg_div]

private theorem symm_equiv_eq (x : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm x = (x.1 : ℂ) + (x.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

private theorem norm_symm_equiv (x : ℝ × ℝ) :
    ‖Complex.measurableEquivRealProd.symm x‖ = Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := by
  rw [symm_equiv_eq, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply, sq]

private theorem planarMode_eq_ofProfile (f : Profile) (x : ℝ × ℝ) :
    planarMode f x =
      UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f (Complex.measurableEquivRealProd.symm x) := by
  unfold planarMode angTwo UnforcedLeray.Planar.NUE.Ang.ofProfile
    UnforcedLeray.Planar.NUE.Ang.angPhase
  rw [norm_symm_equiv, symm_equiv_eq, zpow_ofNat, div_pow]
  have hsq : ((Real.sqrt (x.1 ^ 2 + x.2 ^ 2) : ℂ)) ^ 2 = ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  rw [hsq]

private theorem angTwo_neg (x : ℝ × ℝ) : angTwo (-x) = angTwo x := by
  unfold angTwo
  simp only [Prod.fst_neg, Prod.snd_neg, Complex.ofReal_neg, neg_sq]
  congr 1
  ring

private theorem planarMode_neg (f : Profile) (x : ℝ × ℝ) :
    planarMode f (-x) = planarMode f x := by
  unfold planarMode
  simp only [Prod.fst_neg, Prod.snd_neg, neg_sq, angTwo_neg]

private theorem isCentrallyEven_periodizeC_planarMode (d : ℝ) (f : Profile) :
    IsCentrallyEven (periodizeC d (planarMode f)) := by
  intro x
  unfold periodizeC
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext n
  have hcoord : ((-x).1 - ((-n : ℤ) : ℝ) * d, (-x).2) = -(x.1 - (n : ℝ) * d, x.2) := by
    apply Prod.ext
    · simp; ring
    · simp
  simp only [Equiv.neg_apply, hcoord, planarMode_neg]

private theorem measurable_planarMode {f : Profile} (hf : ContinuousOn f (Ioi 0)) :
    Measurable (planarMode f) := by
  refine measurable_of_isOpen fun V hV => ?_
  have hcont : ContinuousOn (planarMode f) ({(0, 0)}ᶜ : Set (ℝ × ℝ)) := by
    intro x hx
    have hpos : 0 < x.1 ^ 2 + x.2 ^ 2 := by
      by_contra hle
      have hle' : x.1 ^ 2 + x.2 ^ 2 ≤ 0 := le_of_not_gt hle
      have hx1 : x.1 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      have hx2 : x.2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
      exact hx (Prod.ext hx1 hx2)
    have hr : 0 < Real.sqrt (x.1 ^ 2 + x.2 ^ 2) := Real.sqrt_pos.2 hpos
    have hrad : ContinuousAt (fun y : ℝ × ℝ => Real.sqrt (y.1 ^ 2 + y.2 ^ 2)) x := by
      fun_prop
    have hf_at : ContinuousAt (fun y : ℝ × ℝ => f (Real.sqrt (y.1 ^ 2 + y.2 ^ 2))) x :=
      ContinuousAt.comp (f := fun y : ℝ × ℝ => Real.sqrt (y.1 ^ 2 + y.2 ^ 2))
        (hf.continuousAt (isOpen_Ioi.mem_nhds hr)) hrad
    have hden_ne : ((x.1 ^ 2 + x.2 ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
    have hang_at : ContinuousAt angTwo x := by
      unfold angTwo
      exact ContinuousAt.div (by fun_prop) (by fun_prop) hden_ne
    exact (hf_at.mul hang_at).continuousWithinAt
  have hopen : IsOpen (({(0, 0)}ᶜ : Set (ℝ × ℝ)) ∩ planarMode f ⁻¹' V) :=
    hcont.isOpen_inter_preimage isOpen_compl_singleton hV
  have hsing : MeasurableSet (({(0, 0)} : Set (ℝ × ℝ)) ∩ planarMode f ⁻¹' V) := by
    by_cases h0 : (0, 0) ∈ planarMode f ⁻¹' V
    · have heq : ({(0, 0)} : Set (ℝ × ℝ)) ∩ planarMode f ⁻¹' V = {(0, 0)} := by
        ext y; simp [h0]
      rw [heq]; exact measurableSet_singleton _
    · have heq : ({(0, 0)} : Set (ℝ × ℝ)) ∩ planarMode f ⁻¹' V = ∅ := by
        ext y; simp [h0]
      rw [heq]; exact MeasurableSet.empty
  have hunion : planarMode f ⁻¹' V =
      (({(0, 0)}ᶜ : Set (ℝ × ℝ)) ∩ planarMode f ⁻¹' V) ∪
        (({(0, 0)} : Set (ℝ × ℝ)) ∩ planarMode f ⁻¹' V) := by
    ext y
    by_cases hy : y = (0, 0) <;> simp [hy]
  rw [hunion]
  exact hopen.measurableSet.union hsing

private theorem memLp_of_memXG {f : Profile} (hf : MemXG f) : MemLp f 2 B0010.xGMeasure := by
  rw [B0010.memLp_iff_integrableOn hf.measurable]
  refine hf.integrable.congr_fun (fun r _ => ?_) measurableSet_Ioi
  rw [B0010.radialGaussianWeight_inv]
  unfold gaussianWeightInv
  ring

private theorem gaussianNorm_eq_norm_toLp {f : Profile} (hf : MemXG f) :
    gaussianNorm f = ‖(memLp_of_memXG hf).toLp f‖ := by
  have hsq : ‖(memLp_of_memXG hf).toLp f‖ ^ 2 =
      ∫ r in Ioi (0 : ℝ), ‖f r‖ ^ 2 * gaussianWeightInv r * r := by
    rw [B0010.norm_sq_toLp (memLp_of_memXG hf)]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [B0010.radialGaussianWeight_inv]
    unfold gaussianWeightInv
    ring
  unfold gaussianNorm
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

private theorem memXG_const_mul (c : ℂ) {f : Profile} (hf : MemXG f) :
    MemXG (fun r => c * f r) := by
  refine ⟨hf.measurable.const_mul c, ?_⟩
  have heq : (fun r : ℝ => ‖c * f r‖ ^ 2 * gaussianWeightInv r * r) =
      fun r : ℝ => ‖c‖ ^ 2 * (‖f r‖ ^ 2 * gaussianWeightInv r * r) := by
    funext r; rw [norm_mul, mul_pow]; ring
  rw [heq]
  exact hf.integrable.const_mul (‖c‖ ^ 2)

private theorem memXG_add {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    MemXG (fun r => f r + g r) := by
  have hL := (memLp_of_memXG hf).add (memLp_of_memXG hg)
  refine ⟨hf.measurable.add hg.measurable, ?_⟩
  have hint := (B0010.memLp_iff_integrableOn (hf.measurable.add hg.measurable)).1 hL
  refine hint.congr_fun (fun r _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [B0010.radialGaussianWeight_inv]
  unfold gaussianWeightInv
  ring

private theorem memXG_sub {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    MemXG (fun r => f r - g r) := by
  have h := memXG_add hf (memXG_const_mul (-1) hg)
  refine ⟨h.1.congr (Eventually.of_forall fun r => by simp [sub_eq_add_neg]),
    h.2.congr_fun (fun r _ => by simp [sub_eq_add_neg]) measurableSet_Ioi⟩

private theorem gaussianNorm_add_le {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    gaussianNorm (fun r => f r + g r) ≤ gaussianNorm f + gaussianNorm g := by
  rw [gaussianNorm_eq_norm_toLp (memXG_add hf hg), gaussianNorm_eq_norm_toLp hf,
    gaussianNorm_eq_norm_toLp hg]
  have hEq : (memLp_of_memXG (memXG_add hf hg)).toLp (fun r => f r + g r) =
      (memLp_of_memXG hf).toLp f + (memLp_of_memXG hg).toLp g := by
    symm
    exact MemLp.toLp_add (memLp_of_memXG hf) (memLp_of_memXG hg)
  rw [hEq]
  exact norm_add_le _ _

private theorem abs_gaussianNorm_sub_le {f g : Profile} (hf : MemXG f) (hg : MemXG g) :
    |gaussianNorm f - gaussianNorm g| ≤ gaussianNorm (fun r => f r - g r) := by
  rw [gaussianNorm_eq_norm_toLp hf, gaussianNorm_eq_norm_toLp hg,
    gaussianNorm_eq_norm_toLp (memXG_sub hf hg)]
  have hEq : (memLp_of_memXG (memXG_sub hf hg)).toLp (fun r => f r - g r) =
      (memLp_of_memXG hf).toLp f - (memLp_of_memXG hg).toLp g := by
    symm
    exact MemLp.toLp_sub (memLp_of_memXG hf) (memLp_of_memXG hg)
  rw [hEq]
  exact abs_norm_sub_norm_le _ _

/-! ## 2. Planar Gaussian `L²` identity and `L¹` moment integrability -/

private theorem lintegral_planarMode_gauss {f : Profile} (hf : MemXG f)
    (hfc : ContinuousOn f (Ioi 0)) :
    ∫⁻ x : ℝ × ℝ, ‖planarMode f x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 4)) =
      ENNReal.ofReal ((1 / 2) * gaussianNorm f ^ 2) := by
  set G : ℝ × ℝ → ℝ≥0∞ := fun x =>
    ‖planarMode f x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 4))
  have hGm : Measurable G := by
    refine ((measurable_planarMode hfc).enorm.pow_const 2).mul ?_
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).div_const 4))
  have hcomp : ∫⁻ x : ℝ × ℝ, G x = ∫⁻ z : ℂ, G (Complex.measurableEquivRealProd z) := by
    symm
    exact Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
      Complex.measurableEquivRealProd.measurableEmbedding G
  have hpolar := UnforcedLeray.Planar.NUE.Polar.lintegral_eq_lintegral_Ioi_circle
    (f := G ∘ Complex.measurableEquivRealProd)
    (hGm.comp Complex.measurableEquivRealProd.measurable)
  dsimp only [Function.comp_def] at hpolar
  rw [hcomp, hpolar]
  have hinner : ∀ r ∈ Ioi (0 : ℝ),
      ENNReal.ofReal r *
        (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), G (Complex.measurableEquivRealProd (circleMap 0 r θ))) =
        ENNReal.ofReal ((1 / 2) * (‖f r‖ ^ 2 * gaussianWeightInv r * r)) := by
    intro r hr
    have hr' : 0 < r := hr
    have hpt : ∀ θ : ℝ, G (Complex.measurableEquivRealProd (circleMap 0 r θ)) =
        ENNReal.ofReal (‖f r‖ ^ 2 * Real.exp (r ^ 2 / 4)) := by
      intro θ
      dsimp only [G]
      have hpm : planarMode f (Complex.measurableEquivRealProd (circleMap 0 r θ)) =
          UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f (circleMap 0 r θ) := by
        rw [planarMode_eq_ofProfile, MeasurableEquiv.symm_apply_apply]
      have hsq_c : (Complex.measurableEquivRealProd (circleMap 0 r θ)).1 ^ 2 +
          (Complex.measurableEquivRealProd (circleMap 0 r θ)).2 ^ 2 = r ^ 2 := by
        have hn := norm_symm_equiv (Complex.measurableEquivRealProd (circleMap 0 r θ))
        rw [MeasurableEquiv.symm_apply_apply, norm_circleMap_zero, abs_of_pos hr'] at hn
        have hnn : 0 ≤ (Complex.measurableEquivRealProd (circleMap 0 r θ)).1 ^ 2 +
            (Complex.measurableEquivRealProd (circleMap 0 r θ)).2 ^ 2 := by positivity
        nlinarith [Real.sq_sqrt hnn]
      rw [hpm, hsq_c]
      unfold UnforcedLeray.Planar.NUE.Ang.ofProfile
      rw [norm_circleMap_zero, abs_of_pos hr', UnforcedLeray.Planar.angPhase_circleMap hr' 2 θ]
      have hexp_norm : ‖Complex.exp (((2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ = 1 := by
        have hre : (((2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I).re = 0 := by simp
        rw [Complex.norm_exp, hre, Real.exp_zero]
      have hnorm : ‖f r * Complex.exp (((2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I)‖ = ‖f r‖ := by
        rw [norm_mul, hexp_norm, mul_one]
      rw [← ofReal_norm, hnorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (sq_nonneg _)]
    simp_rw [hpt]
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hr'.le]
    congr 1
    unfold gaussianWeightInv
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  have hint : IntegrableOn (fun r : ℝ => (1 / 2) * (‖f r‖ ^ 2 * gaussianWeightInv r * r)) (Ioi 0) :=
    hf.integrable.const_mul (1 / 2)
  have hae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r : ℝ => (1 / 2) * (‖f r‖ ^ 2 * gaussianWeightInv r * r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : 0 < r := hr
    unfold gaussianWeightInv
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hae]
  unfold gaussianNorm
  rw [integral_const_mul, Real.sq_sqrt (setIntegral_nonneg measurableSet_Ioi fun r hr => by
    have hr' : 0 < r := hr
    unfold gaussianWeightInv
    positivity)]

private theorem integrable_planarMode {f : Profile} (hf : MemXG f)
    (hfc : ContinuousOn f (Ioi 0)) : Integrable (planarMode f) := by
  refine ⟨(measurable_planarMode hfc).stronglyMeasurable.aestronglyMeasurable, ?_⟩
  have hpt : ∀ x : ℝ × ℝ, ‖planarMode f x‖ₑ ≤
      ENNReal.ofReal (1 / 2) *
          (‖planarMode f x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 4))) +
        ENNReal.ofReal ((1 / 2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 1))) := by
    intro x
    set s : ℝ := x.1 ^ 2 + x.2 ^ 2
    set A : ℝ := ‖planarMode f x‖ * Real.exp (s / 8)
    set B : ℝ := Real.exp (-s / 8)
    have hAB : ‖planarMode f x‖ = A * B := by
      dsimp only [A, B]
      rw [mul_assoc, ← Real.exp_add]
      have : s / 8 + -s / 8 = 0 := by ring
      rw [this, Real.exp_zero, mul_one]
    have hA2 : A ^ 2 = ‖planarMode f x‖ ^ 2 * Real.exp (s / 4) := by
      dsimp only [A]
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2; ring
    have hB2 : B ^ 2 = Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 1)) := by
      dsimp only [B, s]
      rw [← Real.exp_nat_mul]
      congr 1; ring
    have hreal : ‖planarMode f x‖ ≤
        (1 / 2) * (‖planarMode f x‖ ^ 2 * Real.exp (s / 4)) +
          (1 / 2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 1)) := by
      nlinarith [sq_nonneg (A - B), hAB, hA2, hB2]
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  have h1 : Measurable (fun x : ℝ × ℝ =>
      ENNReal.ofReal (1 / 2) *
        (‖planarMode f x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 4)))) := by
    refine measurable_const.mul (((measurable_planarMode hfc).enorm.pow_const 2).mul ?_)
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).div_const 4))
  have hg_int := (UnforcedLeray.Gaussian.integrable_gauss_plane (a := 1) one_pos).const_mul (1 / 2)
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_add_left h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_planarMode_gauss hf hfc]
  have hg_lt : ∫⁻ x : ℝ × ℝ,
      ENNReal.ofReal ((1 / 2) * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 1))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hg_int.2
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top, hg_lt⟩

private theorem integrable_eta_sq_planarMode {f : Profile} (hf : MemXG f)
    (hfc : ContinuousOn f (Ioi 0)) :
    Integrable (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * planarMode f x) := by
  have hm : Measurable (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ) * planarMode f x) :=
    (Complex.continuous_ofReal.measurable.comp (measurable_snd.pow_const 2)).mul
      (measurable_planarMode hfc)
  refine ⟨hm.stronglyMeasurable.aestronglyMeasurable, ?_⟩
  have hpt : ∀ x : ℝ × ℝ, ‖((x.2 ^ 2 : ℝ) : ℂ) * planarMode f x‖ₑ ≤
      ENNReal.ofReal (1 / 2) *
          (‖planarMode f x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 4))) +
        ENNReal.ofReal (128 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 2))) := by
    intro x
    set s : ℝ := x.1 ^ 2 + x.2 ^ 2
    have hs0 : 0 ≤ s := by dsimp only [s]; positivity
    have hx2_le : x.2 ^ 2 ≤ 16 * Real.exp (s / 16) := by
      have h1 : x.2 ^ 2 ≤ s := by dsimp only [s]; nlinarith [sq_nonneg x.1]
      have h2 : s / 16 + 1 ≤ Real.exp (s / 16) := Real.add_one_le_exp (s / 16)
      linarith
    have hx2_exp : x.2 ^ 2 * Real.exp (-s / 8) ≤ 16 * Real.exp (-s / 16) := by
      calc x.2 ^ 2 * Real.exp (-s / 8)
          ≤ (16 * Real.exp (s / 16)) * Real.exp (-s / 8) := by gcongr
        _ = 16 * (Real.exp (s / 16) * Real.exp (-s / 8)) := by ring
        _ = 16 * Real.exp (-s / 16) := by
            rw [← Real.exp_add]; congr 2; ring
    set A : ℝ := ‖planarMode f x‖ * Real.exp (s / 8)
    set B : ℝ := 16 * Real.exp (-s / 16)
    have hnorm : ‖((x.2 ^ 2 : ℝ) : ℂ) * planarMode f x‖ ≤ A * B := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      have hEq : x.2 ^ 2 * ‖planarMode f x‖ = A * (x.2 ^ 2 * Real.exp (-s / 8)) := by
        dsimp only [A]
        calc x.2 ^ 2 * ‖planarMode f x‖
            = x.2 ^ 2 * ‖planarMode f x‖ * (Real.exp (s / 8) * Real.exp (-s / 8)) := by
                rw [← Real.exp_add]
                have : s / 8 + -s / 8 = 0 := by ring
                rw [this, Real.exp_zero, mul_one]
          _ = ‖planarMode f x‖ * Real.exp (s / 8) * (x.2 ^ 2 * Real.exp (-s / 8)) := by ring
      rw [hEq]
      exact mul_le_mul_of_nonneg_left hx2_exp (by dsimp only [A]; positivity)
    have hA2 : A ^ 2 = ‖planarMode f x‖ ^ 2 * Real.exp (s / 4) := by
      dsimp only [A]
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2; ring
    have hB2 : (1 / 2) * B ^ 2 = 128 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 2)) := by
      dsimp only [B, s]
      rw [mul_pow, ← Real.exp_nat_mul]
      have : (2 : ℕ) * (- (x.1 ^ 2 + x.2 ^ 2) / 16) = -(x.1 ^ 2 + x.2 ^ 2) / (4 * 2) := by
        push_cast; ring
      rw [this]; ring
    have hreal : ‖((x.2 ^ 2 : ℝ) : ℂ) * planarMode f x‖ ≤
        (1 / 2) * (‖planarMode f x‖ ^ 2 * Real.exp (s / 4)) +
          128 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 2)) := by
      nlinarith [sq_nonneg (A - B), hnorm, hA2, hB2]
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg (planarMode f x)),
      ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  have h1 : Measurable (fun x : ℝ × ℝ =>
      ENNReal.ofReal (1 / 2) *
        (‖planarMode f x‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 4)))) := by
    refine measurable_const.mul (((measurable_planarMode hfc).enorm.pow_const 2).mul ?_)
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).div_const 4))
  have hg_int := (UnforcedLeray.Gaussian.integrable_gauss_plane (a := 2) two_pos).const_mul 128
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  rw [lintegral_add_left h1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_planarMode_gauss hf hfc]
  have hg_lt : ∫⁻ x : ℝ × ℝ,
      ENNReal.ofReal (128 * Real.exp (-(x.1 ^ 2 + x.2 ^ 2) / (4 * 2))) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hg_int.2
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top, hg_lt⟩

/-! ## 3. Measurability, zero circulation, and quadrupole identity for `periodizeC` -/

private theorem enorm_tsum_int_le (u : ℤ → ℂ) :
    ‖∑' n : ℤ, u n‖ₑ ≤ ∑' n : ℤ, ‖u n‖ₑ := by
  by_cases hsum : Summable (fun n : ℤ => ‖u n‖)
  · have hu : Summable u := Summable.of_norm hsum
    have hle : ‖∑' n : ℤ, u n‖ ≤ ∑' n : ℤ, ‖u n‖ := norm_tsum_le_tsum_norm hsum
    rw [← ofReal_norm]
    have h_eq : ∑' n : ℤ, ‖u n‖ₑ = ENNReal.ofReal (∑' n : ℤ, ‖u n‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) hsum]
      congr 1; funext n; exact (ofReal_norm _).symm
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal hle
  · have htop : ∑' n : ℤ, ‖u n‖ₑ = ⊤ := by
      by_contra hne
      apply hsum
      refine summable_of_sum_le (fun n => norm_nonneg _) (c := (∑' n : ℤ, ‖u n‖ₑ).toReal) ?_
      intro s
      have hs_le : ∑ n ∈ s, ‖u n‖ₑ ≤ ∑' n : ℤ, ‖u n‖ₑ := ENNReal.sum_le_tsum s
      have hs_eq : ∑ n ∈ s, ‖u n‖ₑ = ENNReal.ofReal (∑ n ∈ s, ‖u n‖) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun n _ => norm_nonneg _]
        congr 1; funext n; exact (ofReal_norm _).symm
      rw [hs_eq] at hs_le
      have hnn : 0 ≤ ∑ n ∈ s, ‖u n‖ := Finset.sum_nonneg fun n _ => norm_nonneg _
      have := ENNReal.toReal_mono hne hs_le
      rwa [ENNReal.toReal_ofReal hnn] at this
    rw [htop]
    exact le_top

private theorem tendsto_finset_Icc_int :
    Tendsto (fun k : ℕ => Finset.Icc (-(k : ℤ)) (k : ℤ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro t
  refine ⟨t.sup Int.natAbs, fun k hk n hn => Finset.mem_Icc.2 ?_⟩
  have habs : n.natAbs ≤ k := le_trans (Finset.le_sup hn) hk
  have h1 : (n.natAbs : ℤ) ≤ (k : ℤ) := Int.ofNat_le.2 habs
  omega

private theorem aestronglyMeasurable_periodizeC {d : ℝ} (hd : 0 < d) {g : ℝ × ℝ → ℂ}
    (hgm : Measurable g) (hg_int : Integrable g) :
    AEStronglyMeasurable (periodizeC d g) (volume.restrict (B0579.cell d)) := by
  set F : ℝ × ℝ → ℝ≥0∞ := fun x => ∑' n : ℤ, ‖g (x.1 - n * d, x.2)‖ₑ
  have hFm : Measurable F :=
    Measurable.tsum fun n => (hgm.comp (UnforcedLeray.Cyl.measurable_shift d n)).enorm
  have hFl : ∫⁻ x in B0579.cell d, F x = ∫⁻ x, ‖g x‖ₑ := by
    rw [b0579_cell_eq_cyl_cell]
    exact UnforcedLeray.Cyl.lintegral_cell_periodize hd hgm.enorm
  have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell d)), F x < ⊤ :=
    ae_lt_top hFm (by rw [hFl]; exact hg_int.2.ne)
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun (k : ℕ) (x : ℝ × ℝ) =>
      ∑ n ∈ Finset.Icc (-(k : ℤ)) (k : ℤ), g (x.1 - n * d, x.2)) ?_ ?_
  · intro k
    exact (Finset.measurable_sum _ fun n _ =>
      hgm.comp (UnforcedLeray.Cyl.measurable_shift d n)).stronglyMeasurable.aestronglyMeasurable
  · filter_upwards [hae] with x hx
    have hsn : Summable (fun n : ℤ => ‖g (x.1 - n * d, x.2)‖) := by
      refine summable_of_sum_le (fun n => norm_nonneg _) (c := (F x).toReal) fun s => ?_
      have hs_le : ∑ n ∈ s, ‖g (x.1 - n * d, x.2)‖ₑ ≤ F x := ENNReal.sum_le_tsum s
      have hs_eq : ∑ n ∈ s, ‖g (x.1 - n * d, x.2)‖ₑ =
          ENNReal.ofReal (∑ n ∈ s, ‖g (x.1 - n * d, x.2)‖) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun n _ => norm_nonneg _]
        congr 1; funext n; exact (ofReal_norm _).symm
      rw [hs_eq] at hs_le
      have hnn : 0 ≤ ∑ n ∈ s, ‖g (x.1 - n * d, x.2)‖ := Finset.sum_nonneg fun n _ => norm_nonneg _
      have := ENNReal.toReal_mono hx.ne hs_le
      rwa [ENNReal.toReal_ofReal hnn] at this
    exact (Summable.of_norm hsn).hasSum.comp tendsto_finset_Icc_int

private theorem hasZeroCirculation_periodizeC_planarMode {d : ℝ} (hd : 0 < d) {f : Profile}
    (hf : MemXG f) (hfc : ContinuousOn f (Ioi 0)) :
    HasZeroCirculation d (periodizeC d (planarMode f)) := by
  have hgm := measurable_planarMode hfc
  have hg_int := integrable_planarMode hf hfc
  refine ⟨⟨aestronglyMeasurable_periodizeC hd hgm hg_int, ?_⟩, ?_⟩
  · have hle : ∫⁻ x in B0579.cell d, ‖periodizeC d (planarMode f) x‖ₑ ≤
        ∫⁻ x in B0579.cell d,
          UnforcedLeray.Cyl.periodize d (fun w => ‖planarMode f w‖ₑ) x :=
      lintegral_mono fun x => enorm_tsum_int_le _
    rw [b0579_cell_eq_cyl_cell, UnforcedLeray.Cyl.lintegral_cell_periodize hd hgm.enorm] at hle
    rw [HasFiniteIntegral, b0579_cell_eq_cyl_cell]
    exact lt_of_le_of_lt hle hg_int.2
  · rw [b0579_cell_eq_cyl_cell]
    have hmul : (fun x : ℝ × ℝ => periodizeC d (planarMode f) x) =
        fun x => UnforcedLeray.Cyl.periodize d (planarMode f) x * (1 : ℂ) := by
      funext x; simp [periodizeC, UnforcedLeray.Cyl.periodize]
    rw [hmul, UnforcedLeray.Cyl.integral_cell_periodize_mul hd hgm.stronglyMeasurable
      stronglyMeasurable_const (fun _ => rfl) (by simpa using hg_int)]
    simp only [mul_one]
    have heq_of : ∫ x : ℝ × ℝ, planarMode f x =
        ∫ z : ℂ, UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f z := by
      simp_rw [planarMode_eq_ofProfile]
      exact Complex.volume_preserving_equiv_real_prod.symm.integral_comp
        Complex.measurableEquivRealProd.symm.measurableEmbedding
        (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f)
    have hint_of : Integrable (UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f) := by
      have := (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
        Complex.measurableEquivRealProd.symm.measurableEmbedding
        (g := UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f)).1
      refine this ?_
      exact hg_int.congr (Eventually.of_forall fun x => planarMode_eq_ofProfile f x)
    rw [heq_of, UnforcedLeray.Planar.NUE.Polar.integral_eq_integral_Ioi_intervalIntegral hint_of]
    have hzero : ∀ r ∈ Ioi (0 : ℝ),
        r • (∫ θ in (0 : ℝ)..2 * Real.pi,
          UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f (circleMap 0 r θ)) = 0 := by
      intro r hr
      have hr' : 0 < r := hr
      have hpt : ∀ θ : ℝ, UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f (circleMap 0 r θ) =
          f r * Complex.exp (((2 : ℤ) : ℂ) * (θ : ℂ) * Complex.I) := by
        intro θ
        unfold UnforcedLeray.Planar.NUE.Ang.ofProfile
        rw [norm_circleMap_zero, abs_of_pos hr', UnforcedLeray.Planar.angPhase_circleMap hr' 2 θ]
      simp_rw [hpt]
      rw [intervalIntegral.integral_const_mul,
        UnforcedLeray.Planar.integral_exp_int_mul_I (by norm_num : (2 : ℤ) ≠ 0), mul_zero,
        smul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero]

private theorem quadQ_periodizeC_planarMode {d : ℝ} (hd : 0 < d) {f : Profile}
    (hf : MemXG f) (hfc : ContinuousOn f (Ioi 0)) :
    quadQ d (periodizeC d (planarMode f)) = quadrupole f := by
  have hgm := measurable_planarMode hfc
  have hgw : StronglyMeasurable (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.measurable.comp (measurable_snd.pow_const 2)).stronglyMeasurable
  have hper : UnforcedLeray.Cyl.IsPeriodic d (fun x : ℝ × ℝ => ((x.2 ^ 2 : ℝ) : ℂ)) :=
    fun _ => rfl
  have hint_prod : Integrable (fun x : ℝ × ℝ => planarMode f x * ((x.2 ^ 2 : ℝ) : ℂ)) := by
    refine (integrable_eta_sq_planarMode hf hfc).congr (Eventually.of_forall fun x => ?_)
    ring
  unfold quadQ quadrupole
  rw [b0579_cell_eq_cyl_cell]
  have hcomm : (∫ x in UnforcedLeray.Cyl.cell d,
      ((x.2 ^ 2 : ℝ) : ℂ) * periodizeC d (planarMode f) x) =
      ∫ x in UnforcedLeray.Cyl.cell d,
        UnforcedLeray.Cyl.periodize d (planarMode f) x * ((x.2 ^ 2 : ℝ) : ℂ) := by
    refine setIntegral_congr_fun (UnforcedLeray.Cyl.measurableSet_cell d) fun x _ => ?_
    simp only [periodizeC, UnforcedLeray.Cyl.periodize]
    ring
  rw [hcomm, UnforcedLeray.Cyl.integral_cell_periodize_mul hd hgm.stronglyMeasurable hgw hper
    hint_prod]
  set H : ℂ → ℂ := fun z => ((z.im : ℝ) : ℂ) ^ 2 * UnforcedLeray.Planar.NUE.Ang.ofProfile 2 f z
  have hH_comp : (fun x : ℝ × ℝ => planarMode f x * ((x.2 ^ 2 : ℝ) : ℂ)) =
      fun x : ℝ × ℝ => H (Complex.measurableEquivRealProd.symm x) := by
    funext x
    dsimp only [H]
    rw [planarMode_eq_ofProfile]
    have him : (Complex.measurableEquivRealProd.symm x).im = x.2 := by
      rw [symm_equiv_eq]; simp
    rw [him, ← Complex.ofReal_pow]
    ring
  have hH_int : Integrable H := by
    refine (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding (g := H)).1 ?_
    exact hint_prod.congr (Eventually.of_forall fun x => congrFun hH_comp x)
  have hInt_eq : ∫ x : ℝ × ℝ, planarMode f x * ((x.2 ^ 2 : ℝ) : ℂ) = ∫ z : ℂ, H z := by
    rw [hH_comp]
    exact Complex.volume_preserving_equiv_real_prod.symm.integral_comp
      Complex.measurableEquivRealProd.symm.measurableEmbedding H
  rw [hInt_eq]
  have hpre : -((2 / Real.pi : ℝ) : ℂ) = -(2 / (Real.pi : ℂ)) := by push_cast; ring
  rw [hpre]
  exact UnforcedLeray.Planar.quadrupole_ofProfile_two hH_int

/-! ## 4. Uniform `X_{m,d}` bound on `1 ≤ d` via lattice Cauchy-Schwarz -/

private theorem cell_shift_quad_ge {d : ℝ} (hd : 1 ≤ d) {x : ℝ × ℝ} (hx : x ∈ B0579.cell d)
    (n : ℤ) :
    4 * x.1 ^ 2 + (n : ℝ) ^ 2 ≤ 8 * (x.1 - (n : ℝ) * d) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp; nlinarith [sq_nonneg x.1]
  · have hx1 : -(d / 2) ≤ x.1 ∧ x.1 < d / 2 := hx.1
    have hq_abs : |x.1| ≤ d / 2 := abs_le.2 ⟨hx1.1, hx1.2.le⟩
    have hn_abs : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
      exact_mod_cast this
    have hd0 : 0 ≤ d := by linarith
    have hkd : d / 2 ≤ |(n : ℝ)| * d / 2 := by nlinarith
    have hrev : |(n : ℝ)| * d / 2 ≤ |x.1 - (n : ℝ) * d| := by
      have htri : |(n : ℝ) * d| - |x.1| ≤ |x.1 - (n : ℝ) * d| := by
        have := abs_sub_abs_le_abs_sub ((n : ℝ) * d) x.1
        rwa [abs_sub_comm] at this
      have hmul : |(n : ℝ) * d| = |(n : ℝ)| * d := by rw [abs_mul, abs_of_nonneg hd0]
      linarith
    have hsq1 : (|(n : ℝ)| * d / 2) ^ 2 ≤ (x.1 - (n : ℝ) * d) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hrev 2
      rwa [sq_abs] at h
    have hsq_n : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
    have h8 : 2 * (n : ℝ) ^ 2 * d ^ 2 ≤ 8 * (x.1 - (n : ℝ) * d) ^ 2 := by
      nlinarith [hsq1, hsq_n]
    have hd2 : 1 ≤ d ^ 2 := by nlinarith
    have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hn_abs, hsq_n]
    have hq2 : x.1 ^ 2 ≤ (d / 2) ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg x.1) hq_abs 2
      rwa [sq_abs] at h
    have hpart1 : 4 * x.1 ^ 2 ≤ (n : ℝ) ^ 2 * d ^ 2 := by
      calc 4 * x.1 ^ 2 ≤ 4 * (d / 2) ^ 2 := by nlinarith
        _ = 1 * d ^ 2 := by ring
        _ ≤ (n : ℝ) ^ 2 * d ^ 2 := by gcongr
    have hpart2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * d ^ 2 := by
      calc (n : ℝ) ^ 2 = (n : ℝ) ^ 2 * 1 := by ring
        _ ≤ (n : ℝ) ^ 2 * d ^ 2 := by gcongr
    linarith

private theorem jb_rpow_le_exp_div_eight {m : ℝ} (hm : 0 < m) (x : ℝ × ℝ) :
    B0579.jb x ^ m ≤ (8 * (Nat.ceil m : ℝ)) ^ (Nat.ceil m) *
      Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8) := by
  set k : ℕ := Nat.ceil m
  have hk_pos : 0 < k := Nat.ceil_pos.2 hm
  have hk_real : 0 < (k : ℝ) := Nat.cast_pos.2 hk_pos
  have hm_le : m ≤ (k : ℝ) := Nat.le_ceil m
  have hjb1 : 1 ≤ B0579.jb x := by unfold B0579.jb; nlinarith [sq_nonneg x.1, sq_nonneg x.2]
  have hrpow : B0579.jb x ^ m ≤ B0579.jb x ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hjb1 hm_le
  rw [Real.rpow_natCast] at hrpow
  set s : ℝ := x.1 ^ 2 + x.2 ^ 2
  have hs0 : 0 ≤ s := by dsimp only [s]; positivity
  have hbase : B0579.jb x ≤ (8 * (k : ℝ)) * Real.exp (s / (8 * (k : ℝ))) := by
    have h1 : 1 ≤ 8 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      linarith
    have h2 : s / (8 * (k : ℝ)) + 1 ≤ Real.exp (s / (8 * (k : ℝ))) :=
      Real.add_one_le_exp _
    have h3 : s + 8 * (k : ℝ) ≤ (8 * (k : ℝ)) * Real.exp (s / (8 * (k : ℝ))) := by
      have hmul := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8 * (k : ℝ))
      have hdiv : (8 * (k : ℝ)) * (s / (8 * (k : ℝ)) + 1) = s + 8 * (k : ℝ) := by
        field_simp [hk_real.ne']
      linarith
    unfold B0579.jb
    have hs_eq : s = x.1 ^ 2 + x.2 ^ 2 := rfl
    linarith
  have hpow : B0579.jb x ^ k ≤ ((8 * (k : ℝ)) * Real.exp (s / (8 * (k : ℝ)))) ^ k :=
    pow_le_pow_left₀ (by unfold B0579.jb; positivity) hbase k
  rw [mul_pow, ← Real.exp_nat_mul] at hpow
  have hexp_arg : (k : ℝ) * (s / (8 * (k : ℝ))) = s / 8 := by
    field_simp [hk_real.ne']
  rw [hexp_arg] at hpow
  exact hrpow.trans hpow

private theorem summable_exp_sq_div_32 :
    Summable (fun n : ℤ => Real.exp (-(n : ℝ) ^ 2 / 32)) := by
  have hg := UnforcedLeray.Gaussian.summable_exp_neg_mul_nat (β := 1 / 32) (by norm_num)
  refine (UnforcedLeray.Gaussian.tsum_int_le_of_le_two_sides
    (f := fun n : ℤ => Real.exp (-(n : ℝ) ^ 2 / 32))
    (g := fun m : ℕ => Real.exp (-(1 / 32 : ℝ) * m))
    (fun _ => (Real.exp_pos _).le) hg ?_ ?_).1
  · intro m
    apply Real.exp_le_exp.2
    have hm : (m : ℝ) ≤ (((m : ℤ) : ℝ)) ^ 2 := by
      rcases m with _ | m
      · simp
      · push_cast; nlinarith
    linarith
  · intro m
    apply Real.exp_le_exp.2
    have hm : (m : ℝ) ≤ (((-((m : ℤ) + 1) : ℤ) : ℝ)) ^ 2 := by
      push_cast; nlinarith
    linarith

private theorem ennreal_tsum_sq_le_cauchy (u : ℤ → ℝ≥0∞) :
    (∑' n : ℤ, u n) ^ 2 ≤
      ENNReal.ofReal (∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2 / 32)) *
        ∑' n : ℤ, u n ^ 2 * ENNReal.ofReal (Real.exp ((n : ℝ) ^ 2 / 32)) := by
  set S₀ : ℝ := ∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2 / 32)
  have hS0_pos : 0 < S₀ := by
    refine lt_of_lt_of_le (Real.exp_pos (-(((0 : ℤ) : ℝ)) ^ 2 / 32)) ?_
    exact summable_exp_sq_div_32.le_tsum 0 fun n _ => (Real.exp_pos _).le
  by_cases htop : ∃ n : ℤ, u n = ⊤
  · obtain ⟨n₀, hn₀⟩ := htop
    have hterm_top : u n₀ ^ 2 * ENNReal.ofReal (Real.exp ((n₀ : ℝ) ^ 2 / 32)) = ⊤ := by
      rw [hn₀, sq, ENNReal.top_mul_top, ENNReal.top_mul]
      simp [ENNReal.ofReal_eq_zero, not_le_of_gt (Real.exp_pos _)]
    have htsum_top : ∑' n : ℤ, u n ^ 2 * ENNReal.ofReal (Real.exp ((n : ℝ) ^ 2 / 32)) = ⊤ :=
      top_unique (hterm_top ▸ ENNReal.le_tsum n₀)
    rw [htsum_top, ENNReal.mul_top]
    · exact le_top
    · simp [ENNReal.ofReal_eq_zero, not_le_of_gt hS0_pos]
  · have htop' : ∀ n : ℤ, u n ≠ ⊤ := fun n hn => htop ⟨n, hn⟩
    set R : ℝ≥0∞ := ENNReal.ofReal S₀ *
      ∑' n : ℤ, u n ^ 2 * ENNReal.ofReal (Real.exp ((n : ℝ) ^ 2 / 32))
    have hfin : ∀ H : Finset ℤ, (∑ n ∈ H, u n) ^ 2 ≤ R := by
      intro H
      set v : ℤ → ℝ := fun n => (u n).toReal
      set a : ℤ → ℝ := fun n => Real.exp (-(n : ℝ) ^ 2 / 64)
      have hv_eq : ∀ n : ℤ, u n = ENNReal.ofReal (v n) :=
        fun n => (ENNReal.ofReal_toReal (htop' n)).symm
      have ha2 : ∀ n : ℤ, a n ^ 2 = Real.exp (-(n : ℝ) ^ 2 / 32) := by
        intro n; dsimp only [a]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      have hainv : ∀ n : ℤ, a n * (v n * Real.exp ((n : ℝ) ^ 2 / 64)) = v n := by
        intro n; dsimp only [a]
        calc Real.exp (-(n : ℝ) ^ 2 / 64) * (v n * Real.exp ((n : ℝ) ^ 2 / 64))
            = v n * (Real.exp (-(n : ℝ) ^ 2 / 64) * Real.exp ((n : ℝ) ^ 2 / 64)) := by ring
          _ = v n := by
              rw [← Real.exp_add]
              have : -(n : ℝ) ^ 2 / 64 + (n : ℝ) ^ 2 / 64 = 0 := by ring
              rw [this, Real.exp_zero, mul_one]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq H a (fun n => v n * Real.exp ((n : ℝ) ^ 2 / 64))
      simp_rw [hainv, ha2] at hcs
      have hsum_a : ∑ n ∈ H, Real.exp (-(n : ℝ) ^ 2 / 32) ≤ S₀ :=
        summable_exp_sq_div_32.sum_le_tsum H fun n _ => (Real.exp_pos _).le
      have hb2 : ∀ n : ℤ, (v n * Real.exp ((n : ℝ) ^ 2 / 64)) ^ 2 =
          v n ^ 2 * Real.exp ((n : ℝ) ^ 2 / 32) := by
        intro n; rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
      simp_rw [hb2] at hcs
      have hreal : (∑ n ∈ H, v n) ^ 2 ≤ S₀ * ∑ n ∈ H, v n ^ 2 * Real.exp ((n : ℝ) ^ 2 / 32) :=
        hcs.trans (mul_le_mul_of_nonneg_right hsum_a
          (Finset.sum_nonneg fun n _ => by positivity))
      have hLHS : (∑ n ∈ H, u n) ^ 2 = ENNReal.ofReal ((∑ n ∈ H, v n) ^ 2) := by
        have hs : ∑ n ∈ H, u n = ENNReal.ofReal (∑ n ∈ H, v n) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun n _ => ENNReal.toReal_nonneg]
          exact Finset.sum_congr rfl fun n _ => hv_eq n
        rw [hs, ← ENNReal.ofReal_pow (Finset.sum_nonneg fun n _ => ENNReal.toReal_nonneg)]
      rw [hLHS]
      refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
      rw [ENNReal.ofReal_mul hS0_pos.le,
        ENNReal.ofReal_sum_of_nonneg fun n _ => by positivity]
      dsimp only [R]
      gcongr
      refine le_trans (le_of_eq ?_)
        (ENNReal.sum_le_tsum H (f := fun n => u n ^ 2 * ENNReal.ofReal (Real.exp ((n : ℝ) ^ 2 / 32))))
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow ENNReal.toReal_nonneg, ← hv_eq n]
    rw [sq, ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_mul]
    refine iSup_le fun F => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun G => ?_
    classical
    have hF : ∑ n ∈ F, u n ≤ ∑ n ∈ F ∪ G, u n :=
      Finset.sum_le_sum_of_subset Finset.subset_union_left
    have hG : ∑ n ∈ G, u n ≤ ∑ n ∈ F ∪ G, u n :=
      Finset.sum_le_sum_of_subset Finset.subset_union_right
    exact (mul_le_mul' hF hG).trans (by rw [← sq]; exact hfin (F ∪ G))

private def periodizeConst (m : ℝ) : ℝ :=
  Real.sqrt ((8 * (Nat.ceil m : ℝ)) ^ (Nat.ceil m) *
    (∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2 / 32)) * (1 / 2) + 1)

private theorem periodizeConst_pos (m : ℝ) : 0 < periodizeConst m := by
  unfold periodizeConst
  apply Real.sqrt_pos.2
  have hS0 : 0 ≤ ∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2 / 32) :=
    tsum_nonneg fun _ => (Real.exp_pos _).le
  positivity

private theorem memLp_and_xNorm_periodizeC_planarMode {d m : ℝ} (hd : 1 ≤ d) (hm : 0 < m)
    {f : Profile} (hf : MemXG f) (hfc : ContinuousOn f (Ioi 0)) :
    MemLp (periodizeC d (planarMode f)) 2 (B0579.cellMeasure d m) ∧
      xNorm d m (periodizeC d (planarMode f)) ≤
        ENNReal.ofReal (periodizeConst m * gaussianNorm f) := by
  have hd_pos : 0 < d := by linarith
  have hgm := measurable_planarMode hfc
  have hg_int := integrable_planarMode hf hfc
  set Kk : ℝ := (8 * (Nat.ceil m : ℝ)) ^ (Nat.ceil m)
  set S₀ : ℝ := ∑' n : ℤ, Real.exp (-(n : ℝ) ^ 2 / 32)
  have hKk_pos : 0 < Kk := by
    dsimp only [Kk]
    have : 0 < Nat.ceil m := Nat.ceil_pos.2 hm
    positivity
  have hS0_nonneg : 0 ≤ S₀ := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hlint_eq : ∫⁻ x, ‖periodizeC d (planarMode f) x‖ₑ ^ 2 ∂(B0579.cellMeasure d m) =
      ∫⁻ x in B0579.cell d,
        ENNReal.ofReal (B0579.jb x ^ m) * ‖periodizeC d (planarMode f) x‖ₑ ^ 2 := by
    rw [B0579.cellMeasure,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _
        (B0579.measurable_density m).coe_nnreal_ennreal
        (Eventually.of_forall fun _ => ENNReal.coe_lt_top)]
    refine lintegral_congr fun x => ?_
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_coe_nnreal, B0579.coe_density]
  have hpt : ∀ x ∈ B0579.cell d,
      ENNReal.ofReal (B0579.jb x ^ m) * ‖periodizeC d (planarMode f) x‖ₑ ^ 2 ≤
        ENNReal.ofReal (Kk * S₀) *
          ∑' n : ℤ, ‖planarMode f (x.1 - n * d, x.2)‖ₑ ^ 2 *
            ENNReal.ofReal (Real.exp (((x.1 - n * d) ^ 2 + x.2 ^ 2) / 4)) := by
    intro x hx
    have hjb := ENNReal.ofReal_le_ofReal (jb_rpow_le_exp_div_eight hm x)
    have hts : ‖periodizeC d (planarMode f) x‖ₑ ^ 2 ≤
        (∑' n : ℤ, ‖planarMode f (x.1 - n * d, x.2)‖ₑ) ^ 2 :=
      pow_le_pow_left' (enorm_tsum_int_le _) 2
    have hcs := ennreal_tsum_sq_le_cauchy (fun n : ℤ => ‖planarMode f (x.1 - n * d, x.2)‖ₑ)
    calc ENNReal.ofReal (B0579.jb x ^ m) * ‖periodizeC d (planarMode f) x‖ₑ ^ 2
        ≤ ENNReal.ofReal (Kk * Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8)) *
            (ENNReal.ofReal S₀ *
              ∑' n : ℤ, ‖planarMode f (x.1 - n * d, x.2)‖ₑ ^ 2 *
                ENNReal.ofReal (Real.exp ((n : ℝ) ^ 2 / 32))) :=
          mul_le_mul' hjb (hts.trans hcs)
      _ = ENNReal.ofReal (Kk * S₀) *
            (ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8)) *
              ∑' n : ℤ, ‖planarMode f (x.1 - n * d, x.2)‖ₑ ^ 2 *
                ENNReal.ofReal (Real.exp ((n : ℝ) ^ 2 / 32))) := by
          rw [ENNReal.ofReal_mul hKk_pos.le, ENNReal.ofReal_mul hKk_pos.le]
          ring
      _ = ENNReal.ofReal (Kk * S₀) *
            ∑' n : ℤ, ‖planarMode f (x.1 - n * d, x.2)‖ₑ ^ 2 *
              (ENNReal.ofReal (Real.exp ((x.1 ^ 2 + x.2 ^ 2) / 8)) *
                ENNReal.ofReal (Real.exp ((n : ℝ) ^ 2 / 32))) := by
          rw [← ENNReal.tsum_mul_left]
          congr 1
          exact tsum_congr fun n => by ring
      _ ≤ ENNReal.ofReal (Kk * S₀) *
            ∑' n : ℤ, ‖planarMode f (x.1 - n * d, x.2)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (((x.1 - n * d) ^ 2 + x.2 ^ 2) / 4)) := by
          gcongr with n
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.2
          have hq := cell_shift_quad_ge hd hx n
          linarith [sq_nonneg x.2]
  have hG_meas : Measurable (fun w : ℝ × ℝ =>
      ‖planarMode f w‖ₑ ^ 2 * ENNReal.ofReal (Real.exp ((w.1 ^ 2 + w.2 ^ 2) / 4))) := by
    refine (hgm.enorm.pow_const 2).mul ?_
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).div_const 4))
  have hlint_le : ∫⁻ x, ‖periodizeC d (planarMode f) x‖ₑ ^ 2 ∂(B0579.cellMeasure d m) ≤
      ENNReal.ofReal (periodizeConst m ^ 2 * gaussianNorm f ^ 2) := by
    rw [hlint_eq]
    calc ∫⁻ x in B0579.cell d,
            ENNReal.ofReal (B0579.jb x ^ m) * ‖periodizeC d (planarMode f) x‖ₑ ^ 2
        ≤ ∫⁻ x in B0579.cell d, ENNReal.ofReal (Kk * S₀) *
            ∑' n : ℤ, ‖planarMode f (x.1 - n * d, x.2)‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (((x.1 - n * d) ^ 2 + x.2 ^ 2) / 4)) :=
          setLIntegral_mono' (B0579.measurableSet_cell d) hpt
      _ = ENNReal.ofReal (Kk * S₀) *
            ∫⁻ x in UnforcedLeray.Cyl.cell d,
              UnforcedLeray.Cyl.periodize d
                (fun w : ℝ × ℝ => ‖planarMode f w‖ₑ ^ 2 *
                  ENNReal.ofReal (Real.exp ((w.1 ^ 2 + w.2 ^ 2) / 4))) x := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, b0579_cell_eq_cyl_cell]
          rfl
      _ = ENNReal.ofReal (Kk * S₀) *
            ENNReal.ofReal ((1 / 2) * gaussianNorm f ^ 2) := by
          rw [UnforcedLeray.Cyl.lintegral_cell_periodize hd_pos hG_meas,
            lintegral_planarMode_gauss hf hfc]
      _ = ENNReal.ofReal ((Kk * S₀ * (1 / 2)) * gaussianNorm f ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (periodizeConst m ^ 2 * gaussianNorm f ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hpc : periodizeConst m ^ 2 = Kk * S₀ * (1 / 2) + 1 := by
            unfold periodizeConst
            exact Real.sq_sqrt (by positivity)
          rw [hpc]
          nlinarith [sq_nonneg (gaussianNorm f)]
  have hxNorm_le : xNorm d m (periodizeC d (planarMode f)) ≤
      ENNReal.ofReal (periodizeConst m * gaussianNorm f) := by
    unfold xNorm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, one_div]
    calc (∫⁻ x, ‖periodizeC d (planarMode f) x‖ₑ ^ 2 ∂B0579.cellMeasure d m) ^ (2⁻¹ : ℝ)
        ≤ (ENNReal.ofReal (periodizeConst m ^ 2 * gaussianNorm f ^ 2)) ^ (2⁻¹ : ℝ) :=
          ENNReal.rpow_le_rpow hlint_le (by positivity)
      _ = ENNReal.ofReal ((periodizeConst m ^ 2 * gaussianNorm f ^ 2) ^ (2⁻¹ : ℝ)) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
      _ = ENNReal.ofReal (periodizeConst m * gaussianNorm f) := by
          congr 1
          have h12 : (2⁻¹ : ℝ) = 1 / 2 := by ring
          rw [h12, ← Real.sqrt_eq_rpow,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (periodizeConst_pos m).le,
            Real.sqrt_sq (by unfold gaussianNorm; exact Real.sqrt_nonneg _)]
  refine ⟨⟨(aestronglyMeasurable_periodizeC hd_pos hgm hg_int).mono_ac
    (B0579.cellMeasure_ac d m), ?_⟩, hxNorm_le⟩
  exact lt_of_le_of_lt hxNorm_le ENNReal.ofReal_lt_top

/-! ## 5. Scalar scaling of `periodizeC (planarMode ...)` and continuity of `gaussianNorm` -/

private theorem periodizeC_planarMode_const_mul (d : ℝ) (c : ℂ) (f : Profile) :
    periodizeC d (planarMode (fun r => c * f r)) =
      fun x => c * periodizeC d (planarMode f) x := by
  funext x
  unfold periodizeC planarMode
  simp_rw [mul_assoc]
  exact tsum_mul_left

private theorem continuousOn_canonical_slice {P : PlanarData} (hP : IsPlanarReference P)
    {θ : ℝ} (hθ : 0 < θ) : ContinuousOn (P.canonical θ) (Ioi 0) := by
  have hsm := hP.canonical.smooth.continuousOn
  have hmap : ContinuousOn (fun r : ℝ => (θ, r)) (Ioi 0) :=
    continuousOn_const.prodMk continuousOn_id
  exact hsm.comp hmap fun r hr => ⟨hθ, hr⟩

namespace PreparedDatumAux

/-- Any profile curve `W` representing a `PartI.IsCanonicalSolution V` satisfies
`Cons.C01.IsXGContinuous W`. -/
theorem isXGContinuous_of_canonicalSolution {W : ℝ → Profile} {V : ℝ → B0010.XG}
    (hW : ∀ θ : ℝ, 0 < θ → MemXG (W θ))
    (hV : UnforcedLeray.Short.PartI.IsCanonicalSolution V)
    (hWV : ∀ θ : ℝ, 0 < θ → W θ =ᵐ[B0010.xGMeasure] (V θ : ℝ → ℂ)) :
    UnforcedLeray.Cons.C01.IsXGContinuous W := by
  intro θ₀ hθ₀
  have hcont : ContinuousAt V θ₀ :=
    hV.smooth.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hθ₀)
  have hcont_norm : ContinuousAt (fun θ => ‖V θ - V θ₀‖) θ₀ :=
    (hcont.sub (continuousAt_const (y := V θ₀))).norm
  have hlim : Tendsto (fun θ => ‖V θ - V θ₀‖) (𝓝 θ₀) (𝓝 0) := by
    simpa [sub_self] using hcont_norm.tendsto
  refine hlim.congr' ?_
  filter_upwards [isOpen_Ioi.mem_nhds hθ₀] with θ hθ
  have hsub := memXG_sub (hW θ hθ) (hW θ₀ hθ₀)
  rw [gaussianNorm_eq_norm_toLp hsub]
  congr 1
  apply Lp.ext
  filter_upwards [(memLp_of_memXG hsub).coeFn_toLp, Lp.coeFn_sub (V θ) (V θ₀),
    hWV θ hθ, hWV θ₀ hθ₀] with r h1 h2 h3 h4
  rw [h2, Pi.sub_apply, h1, ← h3, ← h4]

/-- Clauses 1, 2, and 3 of `CTCanonicalBranchProps`, proved unconditionally for every
`P : PlanarData` satisfying `IsPlanarReference P`. -/
theorem ctCanonicalBranchProps_one_two_three (P : PlanarData) (hP : IsPlanarReference P)
    (m : ℝ) (hm : 8 < m) :
    (∀ ν ∈ Ioc (0 : ℝ) 1,
      MemLp (preparedDatum P ν) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (preparedDatum P ν) ∧
      IsCentrallyEven (preparedDatum P ν)) ∧
    (∀ ν θ : ℝ, 0 < ν → 0 < θ → 1 ≤ dOfTheta ν θ →
      MemLp (canonicalPeriodized P ν θ) 2 (B0579.cellMeasure (dOfTheta ν θ) m) ∧
      HasZeroCirculation (dOfTheta ν θ) (canonicalPeriodized P ν θ) ∧
      IsCentrallyEven (canonicalPeriodized P ν θ) ∧
      quadQ (dOfTheta ν θ) (canonicalPeriodized P ν θ) = quadrupole (P.canonical θ)) ∧
    (∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ C : ℝ, 0 < C ∧
      ∀ ν ∈ Ioc (0 : ℝ) 1, ∀ θ : ℝ, b ≤ θ → 1 ≤ dOfTheta ν θ →
        ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re) *
            xNorm (dOfTheta ν θ) m (canonicalPeriodized P ν θ) ≤ ENNReal.ofReal C) := by
  have hm0 : 0 < m := by linarith
  refine ⟨?_, ?_, ?_⟩
  · -- Clause 1: preparedDatum
    intro ν hν
    have hν0 : 0 < ν := hν.1
    have hν1 : ν ≤ 1 := hν.2
    have hinv_pos : 0 < ν⁻¹ := inv_pos.2 hν0
    have hc_ge : 1 ≤ ν ^ (-2 : ℝ) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hν0 hν1 (by norm_num)
    have hc_pos : 0 < ν ^ (-2 : ℝ) := by linarith
    set α : ℂ := Complex.exp (P.eigenvalue * ((ν⁻¹ : ℝ) : ℂ)) * ((ν⁻¹ : ℝ) : ℂ) ^ P.kappa
    have hf_xg : MemXG (fun r => α * P.canonical ν⁻¹ r) :=
      memXG_const_mul α (hP.canonical.memXG ν⁻¹ hinv_pos)
    have hf_cont : ContinuousOn (fun r => α * P.canonical ν⁻¹ r) (Ioi 0) :=
      continuousOn_const.mul (continuousOn_canonical_slice hP hinv_pos)
    unfold preparedDatum
    exact ⟨(memLp_and_xNorm_periodizeC_planarMode hc_ge hm0 hf_xg hf_cont).1,
      hasZeroCirculation_periodizeC_planarMode hc_pos hf_xg hf_cont,
      isCentrallyEven_periodizeC_planarMode _ _⟩
  · -- Clause 2: canonicalPeriodized
    intro ν θ _hν hθ hd
    have hd_pos : 0 < dOfTheta ν θ := by linarith
    have hf_xg : MemXG (P.canonical θ) := hP.canonical.memXG θ hθ
    have hf_cont : ContinuousOn (P.canonical θ) (Ioi 0) := continuousOn_canonical_slice hP hθ
    unfold canonicalPeriodized
    exact ⟨(memLp_and_xNorm_periodizeC_planarMode hd hm0 hf_xg hf_cont).1,
      hasZeroCirculation_periodizeC_planarMode hd_pos hf_xg hf_cont,
      isCentrallyEven_periodizeC_planarMode _ _,
      quadQ_periodizeC_planarMode hd_pos hf_xg hf_cont⟩
  · -- Clause 3: uniform weighted bound on θ ≥ b ≥ b₀
    obtain ⟨C₁, θ₁, hθ₁, hasym⟩ := hP.canonical.asymptotic
    refine ⟨max θ₁ 1, lt_of_lt_of_le hθ₁ (le_max_left _ _), fun b hb => ?_⟩
    set M : ℝ := max C₁ 0 + gaussianNorm P.mode + 1
    have hM_pos : 0 < M := by
      dsimp only [M]
      have hgn : 0 ≤ gaussianNorm P.mode := by unfold gaussianNorm; exact Real.sqrt_nonneg _
      linarith [le_max_right C₁ 0]
    refine ⟨periodizeConst m * M, mul_pos (periodizeConst_pos m) hM_pos, ?_⟩
    intro ν _hν θ hθb hd
    have hθ_ge_θ1 : θ₁ ≤ θ := le_trans (le_trans (le_max_left _ _) hb) hθb
    have hθ_ge_1 : 1 ≤ θ := le_trans (le_trans (le_max_right _ _) hb) hθb
    have hθ_pos : 0 < θ := by linarith
    set α : ℂ := Complex.exp (P.eigenvalue * (θ : ℂ)) * (θ : ℂ) ^ P.kappa
    have hα_norm : ‖α‖ = Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re := by
      dsimp only [α]
      rw [norm_mul, Complex.norm_exp, Complex.norm_cpow_eq_rpow_re_of_pos hθ_pos]
      have hre : (P.eigenvalue * (θ : ℂ)).re = P.eigenvalue.re * θ := by simp
      rw [hre]
    have hsmul_xNorm :
        ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re) *
          xNorm (dOfTheta ν θ) m (canonicalPeriodized P ν θ) =
        xNorm (dOfTheta ν θ) m
          (periodizeC (dOfTheta ν θ) (planarMode (fun r => α * P.canonical θ r))) := by
      unfold canonicalPeriodized xNorm
      rw [periodizeC_planarMode_const_mul]
      change _ = eLpNorm (α • periodizeC (dOfTheta ν θ) (planarMode (P.canonical θ))) 2 _
      rw [eLpNorm_const_smul, ← ofReal_norm, hα_norm]
    rw [hsmul_xNorm]
    have hf_xg : MemXG (fun r => α * P.canonical θ r) :=
      memXG_const_mul α (hP.canonical.memXG θ hθ_pos)
    have hf_cont : ContinuousOn (fun r => α * P.canonical θ r) (Ioi 0) :=
      continuousOn_const.mul (continuousOn_canonical_slice hP hθ_pos)
    refine (memLp_and_xNorm_periodizeC_planarMode hd hm0 hf_xg hf_cont).2.trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (periodizeConst_pos m).le
    have hsplit_xg : MemXG (fun r => α * P.canonical θ r - P.mode r) :=
      memXG_sub hf_xg hP.eigenpair.memXG
    have hsum_eq : (fun r => α * P.canonical θ r) =
        fun r => (α * P.canonical θ r - P.mode r) + P.mode r := by
      funext r; ring
    rw [hsum_eq]
    have htri := gaussianNorm_add_le hsplit_xg hP.eigenpair.memXG
    have hrem := hasym θ hθ_ge_θ1
    have hdiv : C₁ / θ ≤ max C₁ 0 := by
      calc C₁ / θ ≤ max C₁ 0 / θ := div_le_div_of_nonneg_right (le_max_left _ _) hθ_pos.le
        _ ≤ max C₁ 0 / 1 := div_le_div_of_nonneg_left (le_max_right _ _) one_pos hθ_ge_1
        _ = max C₁ 0 := div_one _
    dsimp only [M]
    linarith

end PreparedDatumAux

/-- All four clauses of `CTCanonicalBranchProps` at any planar reference `P` whose canonical
branch satisfies `Cons.C01.IsXGContinuous P.canonical`. -/
theorem ctCanonicalBranchProps_at (P : PlanarData) (hP : IsPlanarReference P)
    (hCont : UnforcedLeray.Cons.C01.IsXGContinuous P.canonical) (m : ℝ) (hm : 8 < m) :
    (∀ ν ∈ Ioc (0 : ℝ) 1,
      MemLp (preparedDatum P ν) 2 (B0579.cellMeasure (ν ^ (-2 : ℝ)) m) ∧
      HasZeroCirculation (ν ^ (-2 : ℝ)) (preparedDatum P ν) ∧
      IsCentrallyEven (preparedDatum P ν)) ∧
    (∀ ν θ : ℝ, 0 < ν → 0 < θ → 1 ≤ dOfTheta ν θ →
      MemLp (canonicalPeriodized P ν θ) 2 (B0579.cellMeasure (dOfTheta ν θ) m) ∧
      HasZeroCirculation (dOfTheta ν θ) (canonicalPeriodized P ν θ) ∧
      IsCentrallyEven (canonicalPeriodized P ν θ) ∧
      quadQ (dOfTheta ν θ) (canonicalPeriodized P ν θ) = quadrupole (P.canonical θ)) ∧
    (∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, b₀ ≤ b → ∃ C : ℝ, 0 < C ∧
      ∀ ν ∈ Ioc (0 : ℝ) 1, ∀ θ : ℝ, b ≤ θ → 1 ≤ dOfTheta ν θ →
        ENNReal.ofReal (Real.exp (P.eigenvalue.re * θ) * θ ^ P.kappa.re) *
            xNorm (dOfTheta ν θ) m (canonicalPeriodized P ν θ) ≤ ENNReal.ofReal C) ∧
    (∀ b : ℝ, 0 < b → ∃ C : ℝ, 0 < C ∧
      ∀ ν ∈ Ioc (0 : ℝ) 1, ∀ θ ∈ Ioc (0 : ℝ) b, 1 ≤ dOfTheta ν θ →
        xNorm (dOfTheta ν θ) m (canonicalPeriodized P ν θ) ≤ ENNReal.ofReal C) := by
  obtain ⟨h1, h2, h3⟩ := PreparedDatumAux.ctCanonicalBranchProps_one_two_three P hP m hm
  refine ⟨h1, h2, h3, fun b hb => ?_⟩
  have hm0 : 0 < m := by linarith
  obtain ⟨C₀, hC₀⟩ := hP.canonical.bounded_near_zero
  -- ContinuousOn of θ ↦ gaussianNorm (P.canonical θ) on (0, ∞) from hCont
  have hgn_cont : ContinuousOn (fun θ : ℝ => gaussianNorm (P.canonical θ)) (Ioi 0) := by
    intro θ₀ hθ₀
    have hθ₀' : 0 < θ₀ := hθ₀
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    have htend := (Metric.tendsto_nhds.1 (hCont θ₀ hθ₀')) ε hε
    filter_upwards [htend, isOpen_Ioi.mem_nhds hθ₀'] with θ hdist hθ
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by unfold gaussianNorm; exact Real.sqrt_nonneg _)]
      at hdist
    rw [Real.dist_eq]
    exact lt_of_le_of_lt
      (abs_gaussianNorm_sub_le (hP.canonical.memXG θ hθ) (hP.canonical.memXG θ₀ hθ₀')) hdist
  have hcomp_bdd : ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ θ ∈ Icc (1 : ℝ) (max b 1), gaussianNorm (P.canonical θ) ≤ C₂ := by
    have hK : IsCompact (Icc (1 : ℝ) (max b 1)) := isCompact_Icc
    have hne : (Icc (1 : ℝ) (max b 1)).Nonempty := ⟨1, le_rfl, le_max_right _ _⟩
    have hsub : Icc (1 : ℝ) (max b 1) ⊆ Ioi 0 := fun θ hθ => lt_of_lt_of_le one_pos hθ.1
    obtain ⟨θ_max, _, hmax⟩ := hK.exists_isMaxOn hne (hgn_cont.mono hsub)
    refine ⟨max (gaussianNorm (P.canonical θ_max)) 0, le_max_right _ _, fun θ hθ => ?_⟩
    exact (hmax hθ).trans (le_max_left _ _)
  obtain ⟨C₂, hC₂0, hC₂⟩ := hcomp_bdd
  set M : ℝ := max C₀ 0 + C₂ + 1
  have hM_pos : 0 < M := by dsimp only [M]; linarith [le_max_right C₀ 0]
  refine ⟨periodizeConst m * M, mul_pos (periodizeConst_pos m) hM_pos, ?_⟩
  intro ν _hν θ hθ hd
  have hθ_pos : 0 < θ := hθ.1
  have hf_xg : MemXG (P.canonical θ) := hP.canonical.memXG θ hθ_pos
  have hf_cont : ContinuousOn (P.canonical θ) (Ioi 0) := continuousOn_canonical_slice hP hθ_pos
  refine (memLp_and_xNorm_periodizeC_planarMode hd hm0 hf_xg hf_cont).2.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (periodizeConst_pos m).le
  by_cases hθ1 : θ ≤ 1
  · have hbd := hC₀ θ hθ_pos hθ1
    dsimp only [M]
    linarith [le_max_left C₀ 0]
  · have hθ1' : 1 < θ := lt_of_not_ge hθ1
    have hbd := hC₂ θ ⟨hθ1'.le, hθ.2.trans (le_max_left _ _)⟩
    dsimp only [M]
    linarith [le_max_right C₀ 0]

/-- **`PartIII-a:T22/2/1/1`**: compact-interval `X_G`-norm boundedness (SP 1076-1093, 3121-3128)
of `P.canonical` on `[1, B]` (`1 ≤ B`) for every planar reference `IsPlanarReference P`.

Proved by comparing `P.canonical` against the smooth representative `W` of the unique `X_G`-valued
canonical solution `V` from `PartI.CanonicalBranch` (`T22Sub.canonicalBranch_unconditional`) and
`Spine.classicalRegularityHyp`: `Z = P.canonical - W` solves `-∂_θ Z = (L₀ + θ⁻¹ D) Z` on
`(0, ∞) × (0, ∞)` with `MemXG (Z θ)` for all `θ > 0` and `O(e^{-Re λ θ} θ^{-Re κ - 1})` decay in
`X_G` as `θ → ∞`. Composed in `PartIII-a:T22/2/1` (`PreparedDatum.lean`). -/
def CanonicalCompactXGBound : Prop :=
  ∀ (P : PlanarData), IsPlanarReference P → ∀ B : ℝ, 1 ≤ B →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ θ ∈ Icc (1 : ℝ) B, gaussianNorm (P.canonical θ) ≤ C₂

/-- Conditional assembly of `CTCanonicalBranchProps` (`PartIII-a:T22/2/1`, composed in
`PreparedDatum.lean`) from `CanonicalCompactXGBound` (`PartIII-a:T22/2/1/1`). -/
theorem ctCanonicalBranchProps_of (hComp : CanonicalCompactXGBound) :
    CTCanonicalBranchProps := by
  intro P hP m hm
  obtain ⟨h1, h2, h3⟩ := PreparedDatumAux.ctCanonicalBranchProps_one_two_three P hP m hm
  refine ⟨h1, h2, h3, fun b hb => ?_⟩
  have hm0 : 0 < m := by linarith
  obtain ⟨C₀, hC₀⟩ := hP.canonical.bounded_near_zero
  obtain ⟨C₂, hC₂0, hC₂⟩ := hComp P hP (max b 1) (le_max_right _ _)
  set M : ℝ := max C₀ 0 + C₂ + 1
  have hM_pos : 0 < M := by dsimp only [M]; linarith [le_max_right C₀ 0]
  refine ⟨periodizeConst m * M, mul_pos (periodizeConst_pos m) hM_pos, ?_⟩
  intro ν _hν θ hθ hd
  have hθ_pos : 0 < θ := hθ.1
  have hf_xg : MemXG (P.canonical θ) := hP.canonical.memXG θ hθ_pos
  have hf_cont : ContinuousOn (P.canonical θ) (Ioi 0) := continuousOn_canonical_slice hP hθ_pos
  refine (memLp_and_xNorm_periodizeC_planarMode hd hm0 hf_xg hf_cont).2.trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (periodizeConst_pos m).le
  by_cases hθ1 : θ ≤ 1
  · have hbd := hC₀ θ hθ_pos hθ1
    dsimp only [M]
    linarith [le_max_left C₀ 0]
  · have hθ1' : 1 < θ := lt_of_not_ge hθ1
    have hbd := hC₂ θ ⟨hθ1'.le, hθ.2.trans (le_max_left _ _)⟩
    dsimp only [M]
    linarith [le_max_right C₀ 0]

end UnforcedLeray.Short.IIIa.T22Sub
