import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC
import UnforcedLeray.Short.PartI.Tasks.ClassicalOdd.EtaCutoffFacts

/-!
# Part I, `PartI:T04/9/1/2/2/4`: the strip error `E_R ≤ C R^{-1/2}` (`APL2StripBound`)

Source lines 285-288.  `|χ_R'| ≤ a := C₀/R` everywhere, and the two cell integrals of `apL2E` are
bounded pointwise by `a` times second and third jets of `v` (`|∂ω| ≤ ‖D²v‖`, `|∂²ω| ≤ ‖D³v‖`,
`iteratedFDeriv_curl_le`), hence by `a` times the cell `L²` norms `velJet c 2`, `velJet c 3`,
which are uniformly bounded (`jet_l2`).  Finally `a = C₀/R ≤ C₀/√R`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff Interval

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Bound of a directional derivative by the first jet. -/
theorem sb_bound_one (f : Plane → ℝ) (x y : Plane) :
    |fderiv ℝ f x y| ≤ ‖iteratedFDeriv ℝ 1 f x‖ * ‖y‖ := by
  have h := (iteratedFDeriv ℝ 1 f x).le_opNorm (fun _ : Fin 1 => y)
  rw [iteratedFDeriv_one_apply] at h
  simpa [Real.norm_eq_abs] using h

theorem sb_fderiv_fderiv {f : Plane → ℝ} {x : Plane} (hf : ContDiffAt ℝ ∞ f x) (a m : Plane) :
    fderiv ℝ (fun y => fderiv ℝ f y m) x a = iteratedFDeriv ℝ 2 f x ![a, m] := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : Plane => m) hd (differentiableAt_const m)
  have h0 : fderiv ℝ (fun _ : Plane => m) x = 0 := by rw [fderiv_fun_const]; rfl
  rw [this, h0]
  simp

/-- Bound of a second directional derivative by the second jet. -/
theorem sb_bound_two {f : Plane → ℝ} (x : Plane) (hf : ContDiffAt ℝ ∞ f x) (a m : Plane) :
    |fderiv ℝ (fun y => fderiv ℝ f y m) x a| ≤ ‖iteratedFDeriv ℝ 2 f x‖ * ‖a‖ * ‖m‖ := by
  rw [sb_fderiv_fderiv hf a m]
  have h := (iteratedFDeriv ℝ 2 f x).le_opNorm ![a, m]
  simpa [Real.norm_eq_abs, Fin.prod_univ_two, mul_assoc] using h

/-- `∂_η ∂_q f = ∂_η (∂_q f)` as a second directional derivative. -/
theorem sb_pe_pq {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    Cyl.partialEta (Cyl.partialQ f) z = fderiv ℝ (fun y => fderiv ℝ f y eQ) z eE := by
  have hfun : Cyl.partialQ f = fun y => fderiv ℝ f y eQ :=
    funext fun y => UnforcedLeray.Short.PartI.partialQ_eq_fderiv (hf.differentiable (by simp) y)
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y eQ) z :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) z).clm_apply
      (differentiableAt_const eQ)
  rw [hfun, UnforcedLeray.Short.PartI.partialEta_eq_fderiv hd]

/-- `∂_η ∂_η f = ∂_η (∂_η f)` as a second directional derivative. -/
theorem sb_pe_pe {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (z : Plane) :
    Cyl.partialEta (Cyl.partialEta f) z = fderiv ℝ (fun y => fderiv ℝ f y eE) z eE := by
  have hfun : Cyl.partialEta f = fun y => fderiv ℝ f y eE :=
    funext fun y => UnforcedLeray.Short.PartI.partialEta_eq_fderiv (hf.differentiable (by simp) y)
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ f y eE) z :=
    ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) z).clm_apply
      (differentiableAt_const eE)
  rw [hfun, UnforcedLeray.Short.PartI.partialEta_eq_fderiv hd]

theorem sb_sq_le (x X : ℝ) (hX : 0 ≤ X) (h : |x| ≤ X) : x ^ 2 ≤ X ^ 2 := by
  nlinarith [abs_nonneg x, sq_abs x, mul_nonneg (sub_nonneg.2 h) (add_nonneg hX (abs_nonneg x))]

/-- **`PartI:T04/9/1/2/2/4`**: the strip error is `O(R^{-1/2})`. -/
theorem aPL2StripBound : APL2StripBound := by
  intro ν c T v p hν hc hcls
  obtain ⟨C0, hC0, hφall⟩ := etaCutoffFacts
  obtain ⟨M0, hM0⟩ := hcls.bounded 0
  obtain ⟨K2, hK2⟩ := hcls.jet_l2 2
  obtain ⟨K3, hK3⟩ := hcls.jet_l2 3
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M0 0 := ⟨_, rfl⟩
  have hM : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
  obtain ⟨Kq, hKqdef⟩ : ∃ K : ℝ, K = max K2 0 := ⟨_, rfl⟩
  have hKq : 0 ≤ Kq := by rw [hKqdef]; exact le_max_right _ _
  have hKq' : K2 ≤ Kq := by rw [hKqdef]; exact le_max_left _ _
  obtain ⟨Kt, hKtdef⟩ : ∃ K : ℝ, K = max K3 0 := ⟨_, rfl⟩
  have hKt : 0 ≤ Kt := by rw [hKtdef]; exact le_max_right _ _
  have hKt' : K3 ≤ Kt := by rw [hKtdef]; exact le_max_left _ _
  have hL : 0 ≤ ‖APEllipticCaux.lam‖ := by positivity
  have hCc0 : 0 ≤ 2 * M * ‖APEllipticCaux.lam‖ ^ 2 * Kq
      + 2 * ν * (‖APEllipticCaux.lam‖ ^ 2 * Kq + ‖APEllipticCaux.lam‖ ^ 2 * Kt) := by
    have h1 : 0 ≤ 2 * M * ‖APEllipticCaux.lam‖ ^ 2 * Kq :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) (sq_nonneg _)) hKq
    have h2 : 0 ≤ 2 * ν * (‖APEllipticCaux.lam‖ ^ 2 * Kq + ‖APEllipticCaux.lam‖ ^ 2 * Kt) :=
      mul_nonneg (mul_nonneg (by norm_num) hν.le)
        (add_nonneg (mul_nonneg (sq_nonneg _) hKq) (mul_nonneg (sq_nonneg _) hKt))
    linarith
  refine ⟨C0 * (2 * M * ‖APEllipticCaux.lam‖ ^ 2 * Kq
      + 2 * ν * (‖APEllipticCaux.lam‖ ^ 2 * Kq + ‖APEllipticCaux.lam‖ ^ 2 * Kt)),
    mul_nonneg hC0 hCc0, fun R hR s hs => ?_⟩
  have hR0 : 0 < R := by linarith
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR0
  have hs1 : 1 ≤ Real.sqrt R := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hR
  have hRs : Real.sqrt R ≤ R := by
    nlinarith [Real.sq_sqrt hR0.le, mul_nonneg (Real.sqrt_nonneg R) (sub_nonneg.2 hs1)]
  obtain ⟨hφsm, hφbd, -, hφz, hder⟩ := hφall R hR
  have hsq1 : ∀ x : ℝ, Real.sqrt (etaCutoff R x) ≤ 1 := fun x => by
    have := Real.sqrt_le_sqrt (hφbd x).2
    rwa [Real.sqrt_one] at this
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = C0 / R := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha_def]; exact div_nonneg hC0 hR0.le
  have hφ'bd : ∀ x : ℝ, |deriv (etaCutoff R) x| ≤ a := fun x => by
    have h := hder x
    rw [← ha_def] at h
    exact h.trans (mul_le_of_le_one_right ha0 (hsq1 x))
  have ha_le_sq : a ≤ C0 / Real.sqrt R := by
    rw [ha_def]; exact div_le_div_of_nonneg_left hC0 hsR hRs
  have hsI : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
  have hv := hcls.classical.smooth_v
  have hvs : ContDiff ℝ ∞ (v s) := by
    have h := hv.comp_contDiff
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => s)).prodMk contDiff_id :
        ContDiff ℝ ∞ (fun z : Plane => ((s, z) : ℝ × Plane)))
      (fun z => (⟨hsI, mem_univ z⟩ : ((s, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    exact h
  have hω : ContDiff ℝ ∞ (Cyl.curl (v s)) := APEllipticCaux.curl_contDiff hvs
  have hωd : Differentiable ℝ (Cyl.curl (v s)) := hω.differentiable (by simp)
  have hwb : ∀ z : Plane, |v s z 1| ≤ M := by
    intro z
    have h1 := hM0 s hsI z
    rw [norm_iteratedFDeriv_zero] at h1
    have h2 : |v s z 1| ≤ ‖v s z‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (v s z) 1
    rw [hMdef]
    exact h2.trans (h1.trans (le_max_left _ _))
  -- pointwise jet bounds for the vorticity `ω = curl v(s)`
  have hN1 : ∀ z : Plane, ‖iteratedFDeriv ℝ 1 (Cyl.curl (v s)) z‖
      ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖ :=
    fun z => APEllipticCaux.iteratedFDeriv_curl_le hvs 1 z
  have hN2 : ∀ z : Plane, ‖iteratedFDeriv ℝ 2 (Cyl.curl (v s)) z‖
      ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖ :=
    fun z => APEllipticCaux.iteratedFDeriv_curl_le hvs 2 z
  have hP1 : ∀ z : Plane, |Cyl.partialQ (Cyl.curl (v s)) z|
      ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖ := by
    intro z
    rw [UnforcedLeray.Short.PartI.partialQ_eq_fderiv (hωd z)]
    have h := sb_bound_one (Cyl.curl (v s)) z eQ
    rw [norm_eQ, mul_one] at h
    exact h.trans (hN1 z)
  have hP2 : ∀ z : Plane, |Cyl.partialEta (Cyl.curl (v s)) z|
      ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖ := by
    intro z
    rw [UnforcedLeray.Short.PartI.partialEta_eq_fderiv (hωd z)]
    have h := sb_bound_one (Cyl.curl (v s)) z eE
    rw [norm_eE, mul_one] at h
    exact h.trans (hN1 z)
  have hPE : ∀ z : Plane, |Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z|
      ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖ := by
    intro z
    rw [sb_pe_pq hω z]
    have h := sb_bound_two z (hω.contDiffAt) eE eQ
    simp only [norm_eE, norm_eQ, mul_one] at h
    exact h.trans (hN2 z)
  have hQE : ∀ z : Plane, |Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z|
      ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖ := by
    intro z
    rw [sb_pe_pe hω z]
    have h := sb_bound_two z (hω.contDiffAt) eE eE
    simp only [norm_eE, mul_one] at h
    exact h.trans (hN2 z)
  -- the integrands and their majorants
  have hA_bound : ∀ z : Plane,
      ‖deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2)‖
      ≤ (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2)) * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2 := by
    intro z
    have hS0 : 0 ≤ Cyl.partialQ (Cyl.curl (v s)) z ^ 2 + Cyl.partialEta (Cyl.curl (v s)) z ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hSb : Cyl.partialQ (Cyl.curl (v s)) z ^ 2 + Cyl.partialEta (Cyl.curl (v s)) z ^ 2
        ≤ 2 * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖) ^ 2 := by
      have h1 := sb_sq_le _ _ (mul_nonneg hL (norm_nonneg _)) (hP1 z)
      have h2 := sb_sq_le _ _ (mul_nonneg hL (norm_nonneg _)) (hP2 z)
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hS0]
    calc |deriv (etaCutoff R) z.2| * |v s z 1| *
          (Cyl.partialQ (Cyl.curl (v s)) z ^ 2 + Cyl.partialEta (Cyl.curl (v s)) z ^ 2)
        ≤ a * M * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2 + Cyl.partialEta (Cyl.curl (v s)) z ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (hφ'bd z.2) (hwb z) (abs_nonneg _) ha0) hS0
      _ ≤ a * M * (2 * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hSb (mul_nonneg ha0 hM)
      _ = (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2)) * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2 := by ring
  have hB_bound : ∀ z : Plane,
      ‖deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
        + Cyl.partialEta (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z)‖
      ≤ (a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2
        + (a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2 := by
    intro z
    have hLN2 : 0 ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖ :=
      mul_nonneg hL (norm_nonneg _)
    have hLN3 : 0 ≤ ‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖ :=
      mul_nonneg hL (norm_nonneg _)
    have h1 : |Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
          + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z|
        ≤ (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖)
            * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖)
          + (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖)
            * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖) := by
      calc |Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
            + Cyl.partialEta (Cyl.curl (v s)) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z|
          ≤ |Cyl.partialQ (Cyl.curl (v s)) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z|
            + |Cyl.partialEta (Cyl.curl (v s)) z
              * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z| := abs_add_le _ _
        _ = |Cyl.partialQ (Cyl.curl (v s)) z| * |Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z|
            + |Cyl.partialEta (Cyl.curl (v s)) z|
              * |Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z| := by
          rw [abs_mul, abs_mul]
        _ ≤ _ := add_le_add (mul_le_mul (hP1 z) (hPE z) (abs_nonneg _) hLN2)
            (mul_le_mul (hP2 z) (hQE z) (abs_nonneg _) hLN2)
    have h2 : (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖)
            * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖)
          + (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖)
            * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖)
        ≤ ‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2
          + ‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg ‖APEllipticCaux.lam‖)
        (sq_nonneg (‖iteratedFDeriv ℝ 2 (v s) z‖ - ‖iteratedFDeriv ℝ 3 (v s) z‖))]
    rw [Real.norm_eq_abs, abs_mul]
    calc |deriv (etaCutoff R) z.2| * |Cyl.partialQ (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
        + Cyl.partialEta (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z|
        ≤ a * ((‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖)
            * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖)
          + (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 2 (v s) z‖)
            * (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ 3 (v s) z‖)) :=
          mul_le_mul (hφ'bd z.2) h1 (abs_nonneg _) ha0
      _ ≤ a * (‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2
          + ‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 ha0
      _ = (a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2
          + (a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2 := by ring
  -- integrability of the majorants
  have hI2 := (hK2 s hsI).1
  have hI3 := (hK3 s hsI).1
  have hgA : Integrable (fun z : Plane => (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2))
      * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    hI2.const_mul _
  have hgB : Integrable (fun z : Plane => (a * ‖APEllipticCaux.lam‖ ^ 2)
      * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2 + (a * ‖APEllipticCaux.lam‖ ^ 2)
      * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    (hI2.const_mul _).add (hI3.const_mul _)
  have hgB2 : Integrable (fun z : Plane => (a * ‖APEllipticCaux.lam‖ ^ 2)
      * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    hI2.const_mul _
  have hgB3 : Integrable (fun z : Plane => (a * ‖APEllipticCaux.lam‖ ^ 2)
      * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
    hI3.const_mul _
  -- the two cell integrals
  have hIA : ‖∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
      + Cyl.partialEta (Cyl.curl (v s)) z ^ 2)‖
      ≤ ∫ z in Cyl.cell c, (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2))
        * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2 :=
    norm_integral_le_of_norm_le hgA (ae_of_all _ hA_bound)
  have hIB : ‖∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
      * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
        + Cyl.partialEta (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z)‖
      ≤ ∫ z in Cyl.cell c, ((a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2
        + (a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2) :=
    norm_integral_le_of_norm_le (hgB) (ae_of_all _ hB_bound)
  have hvA : ∫ z in Cyl.cell c, (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2))
      * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2 = (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2)) * velJet c 2 v s := by
    unfold velJet
    rw [integral_const_mul]
  have hvB : ∫ z in Cyl.cell c, ((a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 2 (v s) z‖ ^ 2
        + (a * ‖APEllipticCaux.lam‖ ^ 2) * ‖iteratedFDeriv ℝ 3 (v s) z‖ ^ 2)
      = (a * ‖APEllipticCaux.lam‖ ^ 2) * velJet c 2 v s + (a * ‖APEllipticCaux.lam‖ ^ 2) * velJet c 3 v s := by
    rw [integral_add hgB2 hgB3, integral_const_mul, integral_const_mul]
    rfl
  have hposA : 0 ≤ a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2) :=
    mul_nonneg (mul_nonneg ha0 hM) (by positivity)
  have hposB : 0 ≤ a * ‖APEllipticCaux.lam‖ ^ 2 := mul_nonneg ha0 (sq_nonneg _)
  have hvelA : velJet c 2 v s ≤ Kq := (hK2 s hsI).2.trans hKq'
  have hvelB2 : velJet c 2 v s ≤ Kq := (hK2 s hsI).2.trans hKq'
  have hvelB3 : velJet c 3 v s ≤ Kt := (hK3 s hsI).2.trans hKt'
  have hXa : ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
      + Cyl.partialEta (Cyl.curl (v s)) z ^ 2) ≤ a * (M * (2 * ‖APEllipticCaux.lam‖ ^ 2) * Kq) := by
    have h1 : |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2)|
        ≤ (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2)) * velJet c 2 v s := by
      rw [← Real.norm_eq_abs]; exact hIA.trans_eq hvA
    have h2 : (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2)) * velJet c 2 v s
        ≤ (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2)) * Kq :=
      mul_le_mul_of_nonneg_left hvelA hposA
    have h3 := le_abs_self (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
    have : a * (M * (2 * ‖APEllipticCaux.lam‖ ^ 2) * Kq)
        = (a * M * (2 * ‖APEllipticCaux.lam‖ ^ 2)) * Kq := by ring
    rw [this]
    linarith
  have hYneg : -(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
      * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
        + Cyl.partialEta (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z))
      ≤ a * ‖APEllipticCaux.lam‖ ^ 2 * Kq + a * ‖APEllipticCaux.lam‖ ^ 2 * Kt := by
    have h1 : |∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
        * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
          + Cyl.partialEta (Cyl.curl (v s)) z
            * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z)|
        ≤ (a * ‖APEllipticCaux.lam‖ ^ 2) * velJet c 2 v s
          + (a * ‖APEllipticCaux.lam‖ ^ 2) * velJet c 3 v s := by
      rw [← Real.norm_eq_abs]; exact hIB.trans_eq hvB
    have h0 := neg_le_abs (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
        * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
          + Cyl.partialEta (Cyl.curl (v s)) z
            * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z))
    have h2 : (a * ‖APEllipticCaux.lam‖ ^ 2) * velJet c 2 v s
        ≤ (a * ‖APEllipticCaux.lam‖ ^ 2) * Kq := mul_le_mul_of_nonneg_left hvelB2 hposB
    have h3 : (a * ‖APEllipticCaux.lam‖ ^ 2) * velJet c 3 v s
        ≤ (a * ‖APEllipticCaux.lam‖ ^ 2) * Kt := mul_le_mul_of_nonneg_left hvelB3 hposB
    have e1 : a * ‖APEllipticCaux.lam‖ ^ 2 * Kq = (a * ‖APEllipticCaux.lam‖ ^ 2) * Kq := by ring
    have e2 : a * ‖APEllipticCaux.lam‖ ^ 2 * Kt = (a * ‖APEllipticCaux.lam‖ ^ 2) * Kt := by ring
    rw [e1, e2]
    linarith
  -- assemble
  have hmain : (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
        + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
      - 2 * ν * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
        + Cyl.partialEta (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z))
      ≤ C0 * (2 * M * ‖APEllipticCaux.lam‖ ^ 2 * Kq
          + 2 * ν * (‖APEllipticCaux.lam‖ ^ 2 * Kq + ‖APEllipticCaux.lam‖ ^ 2 * Kt)) / Real.sqrt R := by
    have hν2 : 0 ≤ 2 * ν := by linarith
    calc (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
          + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
        - 2 * ν * (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
        + Cyl.partialEta (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z))
        = (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * v s z 1 * (Cyl.partialQ (Cyl.curl (v s)) z ^ 2
          + Cyl.partialEta (Cyl.curl (v s)) z ^ 2))
          + 2 * ν * (-(∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (Cyl.partialQ (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialQ (Cyl.curl (v s))) z
        + Cyl.partialEta (Cyl.curl (v s)) z
          * Cyl.partialEta (Cyl.partialEta (Cyl.curl (v s))) z))) := by ring
      _ ≤ a * (M * (2 * ‖APEllipticCaux.lam‖ ^ 2) * Kq)
          + 2 * ν * (a * ‖APEllipticCaux.lam‖ ^ 2 * Kq + a * ‖APEllipticCaux.lam‖ ^ 2 * Kt) :=
          add_le_add hXa (mul_le_mul_of_nonneg_left hYneg hν2)
      _ = a * (2 * M * ‖APEllipticCaux.lam‖ ^ 2 * Kq
          + 2 * ν * (‖APEllipticCaux.lam‖ ^ 2 * Kq + ‖APEllipticCaux.lam‖ ^ 2 * Kt)) := by ring
      _ ≤ (C0 / Real.sqrt R) * (2 * M * ‖APEllipticCaux.lam‖ ^ 2 * Kq
          + 2 * ν * (‖APEllipticCaux.lam‖ ^ 2 * Kq + ‖APEllipticCaux.lam‖ ^ 2 * Kt)) :=
          mul_le_mul_of_nonneg_right (le_trans (ha_def ▸ le_refl a) ha_le_sq) hCc0
      _ = C0 * (2 * M * ‖APEllipticCaux.lam‖ ^ 2 * Kq
          + 2 * ν * (‖APEllipticCaux.lam‖ ^ 2 * Kq + ‖APEllipticCaux.lam‖ ^ 2 * Kt)) / Real.sqrt R := by
          ring
  unfold apL2E
  exact hmain

end UnforcedLeray.Short.PartI
