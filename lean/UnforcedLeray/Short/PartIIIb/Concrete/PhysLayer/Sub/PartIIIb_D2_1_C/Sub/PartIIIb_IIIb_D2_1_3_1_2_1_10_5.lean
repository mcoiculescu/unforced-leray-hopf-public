import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_10_4
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.CutBounds
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIb.Tasks.BodyLift.Norm

/-!
# `truncGCurl`: the curl of the truncated potential `hₙ` is `gₙ`

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`hₙ = χₙ w + c₂ ψ - 2ν ∑ₖ ∂ₖχₙ ∂ₖψ` with `c₂ = ½ radS χₙ - ν lapS χₙ`. Each summand is a weak
product or derivative rule for the curl (`weakCurlMul`, `weakCurlDeriv`); the sum and real multiple
are handled by `weakCurlLin`. Every field involved lies in `Y_2`, so the local `L²` side conditions
are discharged by the `Y_2` branch of `LocL2`. The compact `y`-support of the cutoff gives the
`Y_2` membership of the Hardy-type products `χₙ w` and `c₂ ψ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Pointwise `sd` of a real linear combination of two differentiable functions. -/
theorem tgc_sd_lin {f g : Space → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a b : ℝ) (j : Fin 3) (y : Space) :
    sd j (fun z => a * f z - b * g z) y = a * sd j f y - b * sd j g y := by
  simp only [sd]
  have h1 : DifferentiableAt ℝ (fun z => a * f z) y := (hf y).const_mul a
  have h2 : DifferentiableAt ℝ (fun z => b * g z) y := (hg y).const_mul b
  have e : fderiv ℝ (fun z => a * f z - b * g z) y
      = fderiv ℝ (fun z => a * f z) y - fderiv ℝ (fun z => b * g z) y := fderiv_sub h1 h2
  rw [e, fderiv_const_mul (hf y) a, fderiv_const_mul (hg y) b]
  simp [smul_eq_mul]

/-- `gradC` of a real linear combination. -/
theorem tgc_gradC_lin {f g : Space → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a b : ℝ) (y : Space) :
    gradC (fun z => a * f z - b * g z) y = a • gradC f y - b • gradC g y := by
  ext j
  simp [gradC, tgc_sd_lin hf hg a b j y, Complex.real_smul]

/-- The cross product with a `gradC` of a real linear combination. -/
theorem tgc_crossC_c2 {f g : Space → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (a b : ℝ) (y : Space) (v : CVec3) :
    crossC (gradC (fun z => a * f z - b * g z) y) v
      = a • crossC (gradC f y) v - b • crossC (gradC g y) v := by
  rw [tgc_gradC_lin hf hg a b y]
  ext i
  fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring

/-- Hardy-type product with a bounded, compactly `y`-supported scalar: `α(y) f` is in `Y_2`
when `f/|y| ∈ Y_2`. The bound is only needed off the null set `{y = 0}`. -/
theorem tgc_hardy_cs {P : ℝ} (hP : 0 < P) {α : Space → ℝ} (hα : Continuous α) {M R : ℝ}
    (hM0 : 0 ≤ M) (hR0 : 0 ≤ R) (hMb : ∀ y : Space, |α y| ≤ M)
    (hR : ∀ y : Space, R < ‖y‖ → α y = 0)
    {f : ℝ × Space → CVec3} (hfper : ∀ᵐ x : ℝ × Space, f (x.1 + P, x.2) = f x)
    (hfm : AEStronglyMeasurable f volume)
    (hH : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => (‖x.2‖⁻¹ : ℝ) • f x)) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => α x.2 • f x) := by
  have key : ∀ y : Space, |α y * ‖y‖| ≤ M * R := by
    intro y
    rw [abs_mul, abs_of_nonneg (norm_nonneg y)]
    by_cases h : ‖y‖ ≤ R
    · exact mul_le_mul (hMb y) h (norm_nonneg y) hM0
    · rw [hR y (not_le.1 h), abs_zero, zero_mul]
      exact mul_nonneg hM0 hR0
  have hae : ∀ᵐ x : ℝ × Space, α x.2 • f x
      = (α x.2 * ‖x.2‖) • ((‖x.2‖⁻¹ : ℝ) • f x) := by
    filter_upwards [wcm_null] with x hx
    rw [smul_smul, mul_inv_cancel_right₀ (norm_ne_zero_iff.mpr hx)]
  have hmeasG : AEStronglyMeasurable
      (fun x : ℝ × Space => (α x.2 * ‖x.2‖) • ((‖x.2‖⁻¹ : ℝ) • f x)) volume :=
    ((((hα.comp continuous_snd).mul (continuous_norm.comp continuous_snd)).aestronglyMeasurable)
      ).smul hH.meas
  have hfin : UnforcedLeray.Short.IIb.phaseLpNorm P 2
      (fun x : ℝ × Space => (α x.2 * ‖x.2‖) • ((‖x.2‖⁻¹ : ℝ) • f x)) < ⊤ :=
    phaseLpNorm_lt_top_of_enorm_le hP (K := ENNReal.ofReal (M * R)) ENNReal.ofReal_ne_top
      hmeasG hH.meas hH.finite (fun x => by
        show ‖(α x.2 * ‖x.2‖) • ((‖x.2‖⁻¹ : ℝ) • f x)‖ₑ
          ≤ ENNReal.ofReal (M * R) * ‖(‖x.2‖⁻¹ : ℝ) • f x‖ₑ
        rw [enorm_smul, Real.enorm_eq_ofReal_abs]
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (key x.2)) le_rfl)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hfper] with x hx
    show α x.2 • f (x.1 + P, x.2) = α x.2 • f x
    rw [hx]
  · exact (hα.comp continuous_snd).aestronglyMeasurable.smul hfm
  · rw [UnforcedLeray.Short.IIb.phaseLpNorm_congr_ae' hae]
    exact hfin

/-- The `y`-function `½ radS χ - ν lapS χ` whose gradient enters `hₙ`. -/
def tgcC2 (n : ℕ) (ν : ℝ) : Space → ℝ :=
  fun y => (1 / 2 : ℝ) * radS (cutχ n) y - ν * lapS (cutχ n) y

/-- **TruncGCurl** (source 1334-1337, 1351-1362, 1470-1480): the curl of `hₙ` is `gₙ` weakly. -/
theorem truncGCurl : TruncGCurl := by
  intro P ν μ hP hP1 hν hμ D hD n
  have hCut : CutBounds := cutBounds
  unfold CutBounds at hCut
  obtain ⟨C, hC0, hb⟩ := hCut
  have hG1 : ∀ y : Space, ‖gradC (cutχ n) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).1) (hb n y).2.1
  have hG2 : ∀ y : Space, ‖gradC (radS (cutχ n)) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).2.1) (hb n y).2.2.1
  have hG3 : ∀ y : Space, ‖gradC (lapS (cutχ n)) y‖ ≤ 2 * C * ‖y‖⁻¹ := fun y =>
    gradC_le_inv hC0 n _ y (fun h => ((hb n y).1 h).2.2.1) (hb n y).2.2.2.1
  have hR : ∀ y : Space, |radS (cutχ n) y| ≤ C := fun y => (hb n y).2.2.2.2.1
  have hL : ∀ y : Space, |lapS (cutχ n) y| ≤ C := fun y => (hb n y).2.2.2.2.2.1
  have hKa : ∀ (k : Fin 3) (y : Space), |sd k (cutχ n) y| ≤ C :=
    fun k y => ((hb n y).2.2.2.2.2.2 k).1
  have hKg : ∀ (k : Fin 3) (y : Space), ‖gradC (sd k (cutχ n)) y‖ ≤ C :=
    fun k y => ((hb n y).2.2.2.2.2.2 k).2
  have hcb : ∀ y : Space, |cutχ n y| ≤ 1 := fun y => by
    have h0 : (0 : ℝ) ≤ unitBump (cutC n • y) := unitBump.nonneg
    have h1 : unitBump (cutC n • y) ≤ 1 := unitBump.le_one
    unfold cutχ
    exact abs_le.2 ⟨by linarith, h1⟩
  have hc2b : ∀ y : Space, |tgcC2 n ν y| ≤ (1 / 2 + |ν|) * C := fun y => by
    have h1 := hR y
    have h2 := hL y
    unfold tgcC2
    calc |(1 / 2 : ℝ) * radS (cutχ n) y - ν * lapS (cutχ n) y|
        ≤ |(1 / 2 : ℝ) * radS (cutχ n) y| + |ν * lapS (cutχ n) y| := abs_sub _ _
      _ = (1 / 2) * |radS (cutχ n) y| + |ν| * |lapS (cutχ n) y| := by
          rw [abs_mul, abs_mul]; norm_num
      _ ≤ (1 / 2) * C + |ν| * C := by gcongr
      _ = (1 / 2 + |ν|) * C := by ring
  have hcut : ContDiff ℝ ∞ (cutχ n) := contDiff_cutχ n
  have hradC : ContDiff ℝ ∞ (radS (cutχ n)) := contDiff_radS' hcut
  have hlapC : ContDiff ℝ ∞ (lapS (cutχ n)) := contDiff_lapS' hcut
  have hc2C : ContDiff ℝ ∞ (tgcC2 n ν) :=
    (contDiff_const.mul hradC).sub (contDiff_const.mul hlapC)
  have hdR : Differentiable ℝ (radS (cutχ n)) := hradC.differentiable (by simp)
  have hdL : Differentiable ℝ (lapS (cutχ n)) := hlapC.differentiable (by simp)
  have hcont_c : Continuous (cutχ n) := hcut.continuous
  have hcont_c2 : Continuous (tgcC2 n ν) := hc2C.continuous
  have hcont_gC : Continuous (gradC (cutχ n)) :=
    continuous_gradC' fun j => (contDiff_sd hcut j).continuous
  have hcont_gR : Continuous (gradC (radS (cutχ n))) :=
    continuous_gradC' fun j => (contDiff_sd hradC j).continuous
  have hcont_gL : Continuous (gradC (lapS (cutχ n))) :=
    continuous_gradC' fun j => (contDiff_sd hlapC j).continuous
  have hcont_gK : ∀ k : Fin 3, Continuous (gradC (sd k (cutχ n))) := fun k =>
    continuous_gradC' fun j => (contDiff_sd (contDiff_sd hcut k) j).continuous
  have hcont_K : ∀ k : Fin 3, Continuous (sd k (cutχ n)) := fun k =>
    (contDiff_sd hcut k).continuous
  have hRsupp : ∀ y : Space, 2 * ((n : ℝ) + 1) < ‖y‖ → cutχ n y = 0 := fun y hy =>
    cutχ_eq_zero n hy.le
  have hc2supp : ∀ y : Space, 2 * ((n : ℝ) + 1) < ‖y‖ → tgcC2 n ν y = 0 := fun y hy => by
    have h := (hb n y).1 (Or.inr hy)
    unfold tgcC2
    simp [h.2.2.2.1, h.2.2.2.2.1]
  have hgc2 : ∀ (y : Space) (v : CVec3), crossC (gradC (tgcC2 n ν) y) v
      = (1 / 2 : ℝ) • crossC (gradC (radS (cutχ n)) y) v
        - ν • crossC (gradC (lapS (cutχ n)) y) v :=
    fun y v => tgc_crossC_c2 hdR hdL (1 / 2) ν y v
  -- Y_2 membership of the pieces
  have hMc : 0 ≤ (1 / 2 + |ν|) * C := mul_nonneg (by linarith [abs_nonneg ν]) hC0
  have hX : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => cutχ n x.2 • D.w x) :=
    tgc_hardy_cs hP hcont_c (by norm_num) (by positivity) hcb hRsupp
      hD.spg.periodic hD.spg.meas hD.spg.hardy
  have hY : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => tgcC2 n ν x.2 • D.ψ x) :=
    tgc_hardy_cs hP hcont_c2 hMc (by positivity) hc2b hc2supp
      hD.spΦ.periodic hD.spΦ.meas hD.spΦ.hardy
  have hXg : UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => cutχ n x.2 • D.g x) :=
    isInYr_smul_of_bdd hP (M := 1) (a := fun x : ℝ × Space => cutχ n x.2)
      ((hcont_c.comp continuous_snd).aestronglyMeasurable) (fun x => hcb x.2)
      (Filter.Eventually.of_forall fun x => rfl) hD.dom.mem_g
  have hΦc2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => tgcC2 n ν x.2 • D.Φ x) :=
    isInYr_smul_of_bdd hP (M := (1 / 2 + |ν|) * C) (a := fun x : ℝ × Space => tgcC2 n ν x.2)
      ((hcont_c2.comp continuous_snd).aestronglyMeasurable) (fun x => hc2b x.2)
      (Filter.Eventually.of_forall fun x => rfl) hD.dom.mem
  have hcross2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => crossC (gradC (tgcC2 n ν) x.2) (D.ψ x)) := by
    have hu := isInYr_smul_of_bdd hP (M := 1 / 2) (a := fun _ : ℝ × Space => (1 / 2 : ℝ))
      aestronglyMeasurable_const (fun x => by norm_num) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG2 hcont_gR
        hD.spΦ.periodic hD.spΦ.meas hD.spΦ.hardy)
    have hv := isInYr_smul_of_bdd hP (M := |ν|) (a := fun _ : ℝ × Space => -ν)
      aestronglyMeasurable_const (fun x => by simp) (Filter.Eventually.of_forall fun x => rfl)
      (isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG3 hcont_gL
        hD.spΦ.periodic hD.spΦ.meas hD.spΦ.hardy)
    exact isInYr_add2 hP (F := fun x : ℝ × Space => crossC (gradC (tgcC2 n ν) x.2) (D.ψ x))
      (fun x => by simp only [hgc2, neg_smul, sub_eq_add_neg]) hu hv
  have hVX : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x)) :=
    isInYr_add2 hP (fun x => rfl) hXg
      (isInYr_cross_hardy hP (M := 2 * C) (by linarith) hG1 hcont_gC
        hD.spg.periodic hD.spg.meas hD.spg.hardy)
  have hVY : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => tgcC2 n ν x.2 • D.Φ x + crossC (gradC (tgcC2 n ν) x.2) (D.ψ x)) :=
    isInYr_add2 hP (fun x => rfl) hΦc2 hcross2
  have hZ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => sd k (cutχ n) x.2 • D.Dψ k x) := fun k =>
    isInYr_smul_of_bdd hP (M := C) (a := fun x : ℝ × Space => sd k (cutχ n) x.2)
      ((hcont_K k).comp continuous_snd).aestronglyMeasurable (fun x => hKa k x.2)
      (Filter.Eventually.of_forall fun x => rfl) (hD.spΦ.grad k).1
  have hDΦZ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => sd k (cutχ n) x.2 • D.DΦ k x) := fun k =>
    isInYr_smul_of_bdd hP (M := C) (a := fun x : ℝ × Space => sd k (cutχ n) x.2)
      ((hcont_K k).comp continuous_snd).aestronglyMeasurable (fun x => hKa k x.2)
      (Filter.Eventually.of_forall fun x => rfl) (hD.dΦ k).1
  have hVZ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => sd k (cutχ n) x.2 • D.DΦ k x
        + crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) := fun k =>
    isInYr_add2 hP (fun x => rfl) (hDΦZ k)
      (isInYr_cross_bdd hP (M := C) (by linarith) (fun y => hKg k y) (hcont_gK k)
        (hD.spΦ.grad k).1)
  -- the weak curl pairs
  have pA := weakCurlMul P hP (cutχ n) hcut D.w D.g (Or.inr hD.spg.hardy)
    (Or.inl hD.dom.mem_g) hD.spg.curl
  have pB := weakCurlMul P hP (tgcC2 n ν) hc2C D.ψ D.Φ (Or.inr hD.spΦ.hardy)
    (Or.inl hD.dom.mem) hD.spΦ.curl
  have pZ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.HasPtwOp P curlT
      (fun x : ℝ × Space => sd k (cutχ n) x.2 • D.Dψ k x)
      (fun x : ℝ × Space => sd k (cutχ n) x.2 • D.DΦ k x
        + crossC (gradC (sd k (cutχ n)) x.2) (D.Dψ k x)) := fun k =>
    weakCurlMul P hP (sd k (cutχ n)) (contDiff_sd hcut k) (D.Dψ k) (D.DΦ k)
      (Or.inl (hD.spΦ.grad k).1) (Or.inl (hD.dΦ k).1) (weakCurlDeriv P ν μ D hD k)
  -- sums
  have s1 := weakCurlLin P hP (fun x : ℝ × Space => cutχ n x.2 • D.w x)
    (fun x : ℝ × Space => tgcC2 n ν x.2 • D.ψ x)
    (fun x : ℝ × Space => cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x))
    (fun x : ℝ × Space => tgcC2 n ν x.2 • D.Φ x + crossC (gradC (tgcC2 n ν) x.2) (D.ψ x))
    (Or.inl hX) (Or.inl hY) (Or.inl hVX) (Or.inl hVY) pA pB
  have hS2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => sd 0 (cutχ n) x.2 • D.Dψ 0 x + sd 1 (cutχ n) x.2 • D.Dψ 1 x) :=
    isInYr_add2 hP (fun x => rfl) (hZ 0) (hZ 1)
  have hVS2 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (sd 0 (cutχ n) x.2 • D.DΦ 0 x
          + crossC (gradC (sd 0 (cutχ n)) x.2) (D.Dψ 0 x))
        + (sd 1 (cutχ n) x.2 • D.DΦ 1 x + crossC (gradC (sd 1 (cutχ n)) x.2) (D.Dψ 1 x))) :=
    isInYr_add2 hP (fun x => rfl) (hVZ 0) (hVZ 1)
  have s2 := weakCurlLin P hP _ _ _ _ (Or.inl (hZ 0)) (Or.inl (hZ 1))
    (Or.inl (hVZ 0)) (Or.inl (hVZ 1)) (pZ 0) (pZ 1)
  have hS3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => sd 0 (cutχ n) x.2 • D.Dψ 0 x + sd 1 (cutχ n) x.2 • D.Dψ 1 x
        + sd 2 (cutχ n) x.2 • D.Dψ 2 x) :=
    isInYr_add2 hP (fun x => rfl) hS2 (hZ 2)
  have hVS3 : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (sd 0 (cutχ n) x.2 • D.DΦ 0 x
          + crossC (gradC (sd 0 (cutχ n)) x.2) (D.Dψ 0 x))
        + (sd 1 (cutχ n) x.2 • D.DΦ 1 x + crossC (gradC (sd 1 (cutχ n)) x.2) (D.Dψ 1 x))
        + (sd 2 (cutχ n) x.2 • D.DΦ 2 x + crossC (gradC (sd 2 (cutχ n)) x.2) (D.Dψ 2 x))) :=
    isInYr_add2 hP (fun x => rfl) hVS2 (hVZ 2)
  have s3 := weakCurlLin P hP _ _ _ _ (Or.inl hS2) (Or.inl (hZ 2))
    (Or.inl hVS2) (Or.inl (hVZ 2)) s2.1 (pZ 2)
  have scal := (weakCurlLin P hP _ _ _ _ (Or.inl hS3) (Or.inl hS3)
    (Or.inl hVS3) (Or.inl hVS3) s3.1 s3.1).2 (-(2 * ν))
  have hSc : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-(2 * ν)) • (sd 0 (cutχ n) x.2 • D.Dψ 0 x
        + sd 1 (cutχ n) x.2 • D.Dψ 1 x + sd 2 (cutχ n) x.2 • D.Dψ 2 x)) :=
    isInYr_smul_of_bdd hP (M := |2 * ν|) (a := fun _ : ℝ × Space => -(2 * ν))
      aestronglyMeasurable_const (fun x => by simp) (Filter.Eventually.of_forall fun x => rfl) hS3
  have hVSc : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (-(2 * ν)) • ((sd 0 (cutχ n) x.2 • D.DΦ 0 x
          + crossC (gradC (sd 0 (cutχ n)) x.2) (D.Dψ 0 x))
        + (sd 1 (cutχ n) x.2 • D.DΦ 1 x + crossC (gradC (sd 1 (cutχ n)) x.2) (D.Dψ 1 x))
        + (sd 2 (cutχ n) x.2 • D.DΦ 2 x + crossC (gradC (sd 2 (cutχ n)) x.2) (D.Dψ 2 x)))) :=
    isInYr_smul_of_bdd hP (M := |2 * ν|) (a := fun _ : ℝ × Space => -(2 * ν))
      aestronglyMeasurable_const (fun x => by simp) (Filter.Eventually.of_forall fun x => rfl) hVS3
  have hXY : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => cutχ n x.2 • D.w x + tgcC2 n ν x.2 • D.ψ x) :=
    isInYr_add2 hP (fun x => rfl) hX hY
  have hVXY : UnforcedLeray.Short.IIb.IsInYr P 2
      (fun x : ℝ × Space => (cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x))
        + (tgcC2 n ν x.2 • D.Φ x + crossC (gradC (tgcC2 n ν) x.2) (D.ψ x))) :=
    isInYr_add2 hP (fun x => rfl) hVX hVY
  have hfin := (weakCurlLin P hP _ _ _ _ (Or.inl hXY) (Or.inl hSc)
    (Or.inl hVXY) (Or.inl hVSc) s1.1 scal).1
  have hTH : truncH n ν D = fun x : ℝ × Space =>
      (cutχ n x.2 • D.w x + tgcC2 n ν x.2 • D.ψ x)
        + (-(2 * ν)) • (sd 0 (cutχ n) x.2 • D.Dψ 0 x + sd 1 (cutχ n) x.2 • D.Dψ 1 x
          + sd 2 (cutχ n) x.2 • D.Dψ 2 x) := by
    funext x
    simp only [truncH, tgcC2, Fin.sum_univ_three]
    module
  have hTG : truncG n ν D = fun x : ℝ × Space =>
      (cutχ n x.2 • D.g x + crossC (gradC (cutχ n) x.2) (D.w x))
        + (tgcC2 n ν x.2 • D.Φ x + crossC (gradC (tgcC2 n ν) x.2) (D.ψ x))
        + (-(2 * ν)) • ((sd 0 (cutχ n) x.2 • D.DΦ 0 x
          + crossC (gradC (sd 0 (cutχ n)) x.2) (D.Dψ 0 x))
          + (sd 1 (cutχ n) x.2 • D.DΦ 1 x + crossC (gradC (sd 1 (cutχ n)) x.2) (D.Dψ 1 x))
          + (sd 2 (cutχ n) x.2 • D.DΦ 2 x + crossC (gradC (sd 2 (cutχ n)) x.2) (D.Dψ 2 x))) := by
    funext x
    rw [hgc2 x.2 (D.ψ x)]
    simp only [truncG, EHardy, EBdd, tgcC2, Fin.sum_univ_three]
    module
  rw [hTH, hTG]
  exact hfin

end UnforcedLeray.Short.PartIIIb.Concrete
