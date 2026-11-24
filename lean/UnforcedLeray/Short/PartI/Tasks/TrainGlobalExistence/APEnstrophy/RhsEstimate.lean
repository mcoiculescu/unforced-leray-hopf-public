import UnforcedLeray.Short.PartI.Sub.PartI_T04_6_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.Integrable
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts
import UnforcedLeray.Short.PartI.Tasks.VorticityFirstMoment.CurlRegularity

/-!
# `PartI:T04/6/1/4`: `APEnstrophyRhsEstimate` (source lines 285-287)

For `R ≥ 1` and `s ∈ (0,T)`, with `φ = etaCutoff R`, `|φ'| ≤ a √φ` where `a = C₀/R`
(`etaCutoffFacts`), the integrand of `apEnstrophyRhs` is bounded pointwise by
`(ν a² + M a) ω²`, where `M` bounds `|v₁|`. The dissipation part and the transverse-derivative
term are absorbed by Cauchy-Schwarz (`apRE_key`), and `∫_cell ω² ≤ 4 velJet(1) ≤ 4K`.
Hence the right-hand side is `≤ C/√R` (`R ≥ 1` gives `√R ≤ R`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Pointwise estimate `-2ν d ω p ≤ ν (f p² + a² ω²)` when `|d| ≤ a √f`. -/
lemma apRE_key (ν a d f om p : ℝ) (hν : 0 ≤ ν) (ha : 0 ≤ a) (hf : 0 ≤ f)
    (hd : |d| ≤ a * Real.sqrt f) :
    -2 * ν * (d * om * p) ≤ ν * (f * p ^ 2 + a ^ 2 * om ^ 2) := by
  have hsq : Real.sqrt f ^ 2 = f := Real.sq_sqrt hf
  have h1 : |d * om * p| ≤ a * Real.sqrt f * |om| * |p| := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (abs_nonneg om)) (abs_nonneg p)
  have h2 : -(d * om * p) ≤ a * Real.sqrt f * |om| * |p| := (neg_le_abs _).trans h1
  have hsp : (Real.sqrt f * |p|) ^ 2 = f * p ^ 2 := by rw [mul_pow, hsq, sq_abs]
  have hab : (a * |om|) ^ 2 = a ^ 2 * om ^ 2 := by rw [mul_pow, sq_abs]
  have h3 : 2 * (a * Real.sqrt f * |om| * |p|) ≤ f * p ^ 2 + a ^ 2 * om ^ 2 := by
    rw [← hsp, ← hab]
    nlinarith [sq_nonneg (Real.sqrt f * |p| - a * |om|)]
  calc -2 * ν * (d * om * p) = 2 * ν * (-(d * om * p)) := by ring
    _ ≤ 2 * ν * (a * Real.sqrt f * |om| * |p|) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ν * (2 * (a * Real.sqrt f * |om| * |p|)) := by ring
    _ ≤ ν * (f * p ^ 2 + a ^ 2 * om ^ 2) := mul_le_mul_of_nonneg_left h3 hν

/-- **`PartI:T04/6/1/4`**: the right-hand side of the cutoff enstrophy identity is `O(R^{-1/2})`. -/
theorem apEnstrophyRhsEstimate : UnforcedLeray.Short.PartI.APEnstrophyRhsEstimate := by
  intro ν c T v p hν hc hcls
  obtain ⟨C0, hC0, hφall⟩ := etaCutoffFacts
  obtain ⟨K, hK⟩ := hcls.jet_l2 1
  obtain ⟨M0, hM0⟩ := hcls.bounded 0
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  have hK' : 0 ≤ 4 * max K 0 := by positivity
  have hCnn : 0 ≤ (ν * C0 + max M0 0) * C0 * (4 * max K 0) :=
    mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg hν.le hC0) hM) hC0) hK'
  refine ⟨(ν * C0 + max M0 0) * C0 * (4 * max K 0), hCnn, fun R hR s hs => ?_⟩
  have hR0 : 0 < R := by linarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hs1 : 1 ≤ Real.sqrt R := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hR
  have hRs : Real.sqrt R ≤ R := by
    nlinarith [Real.sq_sqrt hR0.le, mul_nonneg (Real.sqrt_nonneg R) (sub_nonneg.2 hs1)]
  obtain ⟨hφsm, hφbd, -, hφz, hder⟩ := hφall R hR
  have hφv : ∀ x : ℝ, (2 * R) < |x| → etaCutoff R x = 0 := fun x hx => hφz x hx.le
  have hφ2 : ContDiff ℝ 2 (etaCutoff R) := hφsm.of_le (by simp)
  have hφcont : Continuous (fun z : Plane => etaCutoff R z.2) :=
    hφsm.continuous.comp continuous_snd
  have hφ'cont : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    (hφsm.continuous_deriv (by simp)).comp continuous_snd
  have hsq1 : ∀ x : ℝ, Real.sqrt (etaCutoff R x) ≤ 1 := fun x => by
    have := Real.sqrt_le_sqrt (hφbd x).2
    rwa [Real.sqrt_one] at this
  set a : ℝ := C0 / R with ha_def
  have ha0 : 0 ≤ a := div_nonneg hC0 hR0.le
  have hder' : ∀ x : ℝ, |deriv (etaCutoff R) x| ≤ a * Real.sqrt (etaCutoff R x) := fun x => hder x
  have hφ'bd : ∀ x : ℝ, |deriv (etaCutoff R) x| ≤ a := fun x =>
    (hder' x).trans (mul_le_of_le_one_right ha0 (hsq1 x))
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  -- smoothness of the slice and of its vorticity
  have hW : ContDiffOn ℝ 2 (fun x : ℝ × Plane => Cyl.curl (v x.1) x.2)
      (Ioo 0 T ×ˢ (univ : Set Plane)) :=
    crSmooth hcls.classical.smooth_v
  have hvs : ContDiff ℝ 2 (v s) := by
    have h1 : ContDiffOn ℝ ∞ (fun z : Plane => v s z) univ :=
      hcls.classical.smooth_v.comp ((contDiff_const (c := s)).prodMk contDiff_id).contDiffOn
        (fun z _ => ⟨⟨hs.1.le, hs.2.le⟩, mem_univ z⟩)
    exact (contDiffOn_univ.mp h1).of_le (by simp)
  have hω2 : ContDiff ℝ 2 (fun z : Plane => Cyl.curl (v s) z) := by
    have h1 : ContDiffOn ℝ 2 (fun z : Plane => Cyl.curl (v s) z) univ :=
      hW.comp ((contDiff_const (c := s)).prodMk contDiff_id).contDiffOn
        (fun z _ => Set.mk_mem_prod ⟨hs.1, hs.2⟩ (mem_univ z))
    exact contDiffOn_univ.mp h1
  have hw2 : ContDiff ℝ 2 (fun z : Plane => v s z 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hvs
  have hω2c : Continuous (fun z : Plane => Cyl.curl (v s) z) := hω2.continuous
  have hw2c : Continuous (fun z : Plane => v s z 1) := hw2.continuous
  have hpqc : Continuous (Cyl.partialQ (fun z : Plane => Cyl.curl (v s) z)) :=
    apHD_pq_cont hω2
  have hpec : Continuous (Cyl.partialEta (fun z : Plane => Cyl.curl (v s) z)) :=
    apHD_pe_cont hω2
  -- pointwise bounds
  have hwb : ∀ z : Plane, |v s z 1| ≤ max M0 0 := by
    intro z
    have h1 := hM0 s hsI z
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 : |v s z 1| ≤ ‖v s z‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (v s z) 1
    exact h2.trans (h1.trans (le_max_left _ _))
  have hdiffv : Differentiable ℝ (v s) := hvs.differentiable (by norm_num)
  have hωsq : ∀ z : Plane, Cyl.curl (v s) z ^ 2 ≤ 4 * ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2 := by
    intro z
    have h := apCurl_abs_le_fderiv hdiffv z
    rw [norm_iteratedFDeriv_one]
    nlinarith [sq_abs (Cyl.curl (v s) z), norm_nonneg (fderiv ℝ (v s) z), abs_nonneg (Cyl.curl (v s) z)]
  -- the cell integral of the squared vorticity
  have hΩ : ∫ z in Cyl.cell c, Cyl.curl (v s) z ^ 2 ≤ 4 * max K 0 := by
    have hI := apEnstrophyIntegrable ν c T v p hν hc hcls s hsI
    have hJ := (hK s hsI).1
    have hmono : ∫ z in Cyl.cell c, Cyl.curl (v s) z ^ 2
        ≤ ∫ z in Cyl.cell c, 4 * ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2 :=
      integral_mono hI (Integrable.const_mul hJ 4) (fun z => hωsq z)
    have hval : ∫ z in Cyl.cell c, 4 * ‖iteratedFDeriv ℝ 1 (v s) z‖ ^ 2
        = 4 * velJet c 1 v s := by
      unfold velJet
      rw [integral_const_mul]
    have hvK := (hK s hsI).2
    have hK'' : K ≤ max K 0 := le_max_left _ _
    linarith
  -- integrability of the three pieces of the right-hand side
  have hA1 : Integrable (fun z : Plane => -2 * ν * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
      + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))) (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := 2 * R)
      (((hφcont.mul ((hpqc.pow 2).add (hpec.pow 2))).const_mul (-2 * ν)))
      (fun z hz => by simp [hφv z.2 hz])
  have hA2 : Integrable (fun z : Plane => -2 * ν * (deriv (etaCutoff R) z.2 * Cyl.curl (v s) z
      * Cyl.partialEta (Cyl.curl (v s)) z)) (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := 2 * R)
      ((((hφ'cont.mul hω2c)).mul hpec).const_mul (-2 * ν))
      (fun z hz => by simp [apHD_deriv_zero hφv hz])
  have hA3 : Integrable (fun z : Plane => Cyl.curl (v s) z ^ 2 * v s z 1 * deriv (etaCutoff R) z.2)
      (volume.restrict (Cyl.cell c)) :=
    apHD_integ (c := c) (R0 := 2 * R)
      ((((hω2c.pow 2)).mul hw2c).mul hφ'cont)
      (fun z hz => by simp [apHD_deriv_zero hφv hz])
  have hS12 : Integrable (fun z : Plane => -2 * ν * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
      + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
      + -2 * ν * (deriv (etaCutoff R) z.2 * Cyl.curl (v s) z * Cyl.partialEta (Cyl.curl (v s)) z))
      (volume.restrict (Cyl.cell c)) := hA1.add hA2
  have hS123 : Integrable (fun z : Plane => (-2 * ν * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
      + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
      + -2 * ν * (deriv (etaCutoff R) z.2 * Cyl.curl (v s) z * Cyl.partialEta (Cyl.curl (v s)) z))
      + Cyl.curl (v s) z ^ 2 * v s z 1 * deriv (etaCutoff R) z.2)
      (volume.restrict (Cyl.cell c)) := hS12.add hA3
  -- the right-hand side is the integral of the sum of the three pieces
  have hrhs : apEnstrophyRhs ν c v R s = ∫ z in Cyl.cell c,
      ((-2 * ν * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
        + -2 * ν * (deriv (etaCutoff R) z.2 * Cyl.curl (v s) z * Cyl.partialEta (Cyl.curl (v s)) z))
        + Cyl.curl (v s) z ^ 2 * v s z 1 * deriv (etaCutoff R) z.2) := by
    rw [integral_add hS12 hA3, integral_add hA1 hA2, integral_const_mul, integral_const_mul]
    unfold apEnstrophyRhs
    ring
  -- the pointwise bound
  set A : ℝ := ν * a ^ 2 + max M0 0 * a with hA_def
  have hA0 : 0 ≤ A := add_nonneg (mul_nonneg hν.le (sq_nonneg _)) (mul_nonneg hM ha0)
  have hpt : ∀ z : Plane,
      (-2 * ν * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
        + -2 * ν * (deriv (etaCutoff R) z.2 * Cyl.curl (v s) z * Cyl.partialEta (Cyl.curl (v s)) z))
        + Cyl.curl (v s) z ^ 2 * v s z 1 * deriv (etaCutoff R) z.2
      ≤ A * Cyl.curl (v s) z ^ 2 := by
    intro z
    have k1 := apRE_key ν a (deriv (etaCutoff R) z.2) (etaCutoff R z.2) (Cyl.curl (v s) z)
      (Cyl.partialEta (Cyl.curl (v s)) z) hν.le ha0 (hφbd z.2).1 (hder' z.2)
    have k2 : v s z 1 * deriv (etaCutoff R) z.2 ≤ max M0 0 * a := by
      have h : |v s z 1 * deriv (etaCutoff R) z.2| ≤ max M0 0 * a := by
        rw [abs_mul]
        exact mul_le_mul (hwb z) (hφ'bd z.2) (abs_nonneg _) (le_max_right _ _)
      exact (le_abs_self _).trans h
    have k3 : Cyl.curl (v s) z ^ 2 * (v s z 1 * deriv (etaCutoff R) z.2)
        ≤ Cyl.curl (v s) z ^ 2 * (max M0 0 * a) :=
      mul_le_mul_of_nonneg_left k2 (sq_nonneg _)
    have k4 : 0 ≤ ν * (etaCutoff R z.2 * Cyl.partialQ (Cyl.curl (v s)) z ^ 2) :=
      mul_nonneg hν.le (mul_nonneg (hφbd z.2).1 (sq_nonneg _))
    have k5 : 0 ≤ ν * (etaCutoff R z.2 * Cyl.partialEta (Cyl.curl (v s)) z ^ 2) :=
      mul_nonneg hν.le (mul_nonneg (hφbd z.2).1 (sq_nonneg _))
    rw [hA_def]
    nlinarith [k1, k3, k4, k5]
  -- the bound by `C/√R`
  have ha_le_C0 : a ≤ C0 := div_le_self hC0 hR
  have ha_le_sq : a ≤ C0 / Real.sqrt R := div_le_div_of_nonneg_left hC0 hsR hRs
  have hsq2 : a ^ 2 ≤ C0 * (C0 / Real.sqrt R) := by
    rw [sq]
    calc a * a ≤ (C0 / Real.sqrt R) * C0 :=
          mul_le_mul ha_le_sq ha_le_C0 ha0 (div_nonneg hC0 hsR.le)
      _ = C0 * (C0 / Real.sqrt R) := mul_comm _ _
  have hA_le : A ≤ (ν * C0 + max M0 0) * (C0 / Real.sqrt R) := by
    have h2 : max M0 0 * a ≤ max M0 0 * (C0 / Real.sqrt R) :=
      mul_le_mul_of_nonneg_left ha_le_sq hM
    have h3 : ν * a ^ 2 ≤ ν * (C0 * (C0 / Real.sqrt R)) :=
      mul_le_mul_of_nonneg_left hsq2 hν.le
    rw [hA_def]
    nlinarith [h2, h3]
  have hmono : ∫ z in Cyl.cell c, ((-2 * ν * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
        + -2 * ν * (deriv (etaCutoff R) z.2 * Cyl.curl (v s) z * Cyl.partialEta (Cyl.curl (v s)) z))
        + Cyl.curl (v s) z ^ 2 * v s z 1 * deriv (etaCutoff R) z.2)
      ≤ ∫ z in Cyl.cell c, A * Cyl.curl (v s) z ^ 2 :=
    integral_mono hS123 ((apEnstrophyIntegrable ν c T v p hν hc hcls s hsI).const_mul A)
      (fun z => hpt z)
  calc apEnstrophyRhs ν c v R s
      = ∫ z in Cyl.cell c, ((-2 * ν * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
        + -2 * ν * (deriv (etaCutoff R) z.2 * Cyl.curl (v s) z * Cyl.partialEta (Cyl.curl (v s)) z))
        + Cyl.curl (v s) z ^ 2 * v s z 1 * deriv (etaCutoff R) z.2) := hrhs
    _ ≤ ∫ z in Cyl.cell c, A * Cyl.curl (v s) z ^ 2 := hmono
    _ = A * ∫ z in Cyl.cell c, Cyl.curl (v s) z ^ 2 := integral_const_mul _ _
    _ ≤ A * (4 * max K 0) := mul_le_mul_of_nonneg_left hΩ hA0
    _ ≤ ((ν * C0 + max M0 0) * (C0 / Real.sqrt R)) * (4 * max K 0) :=
        mul_le_mul_of_nonneg_right hA_le hK'
    _ = (ν * C0 + max M0 0) * C0 * (4 * max K 0) / Real.sqrt R := by ring

end UnforcedLeray.Short.PartI
