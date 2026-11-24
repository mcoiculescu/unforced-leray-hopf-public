import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayBoundedDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayKerWindow
import UnforcedLeray.Lib.Kernels.ParamIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Smoothness of the flat potential (`LerayPotSmooth`)

Source `the November 2 reference manuscript` 1676: `u = Σ_i K_i ⊛ F_i` with the
derivatives falling on `F`.  The `i`-th summand `lpsU c F i p = ∫_{cell} K_i(y) F_i(p.1, p.2 - y)`
is a parametric integral (`Lib/Kernels/ParamIntegral.lean`) over the centred cell, whose integrand
at `y` is `p ↦ K_i(y) F_i(p - (0, y))`.  Its iterated derivatives are bounded by
`|K_i(y)| · sup|D^n F_i|` on the window `|y.2 - p.2.2| ≤ L` (the band of `F`), which is integrable by
`CylKerWindow`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The integrand of the `i`-th summand of `lerayPot`, at the evaluation point `p`. -/
def lpsPhi (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2) (y : ℝ × ℝ) (p : Chart) : ℝ :=
  cylKer c i y * F (p.1, p.2 - y) i

/-- The `i`-th summand of `lerayPot` as a function of the point `p`. -/
def lpsU (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2) (p : Chart) : ℝ :=
  ∫ y in cellC c, lpsPhi c F i y p

lemma lps_shift (p : Chart) (y : ℝ × ℝ) : (p.1, p.2 - y) = p + (0, -y) := by
  ext <;> simp [sub_eq_add_neg]

lemma lps_eq_smul (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2) (y : ℝ × ℝ) :
    lpsPhi c F i y = cylKer c i y • (fun z : Chart => F (z + (0, -y)) i) := by
  funext p
  simp only [lpsPhi, Pi.smul_apply, smul_eq_mul, lps_shift]

lemma lps_contDiff (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2)
    (hFi : ContDiff ℝ ∞ (fun q => F q i)) (y : ℝ × ℝ) : ContDiff ℝ ∞ (lpsPhi c F i y) := by
  show ContDiff ℝ ∞ (fun p : Chart => cylKer c i y * F (p.1, p.2 - y) i)
  exact contDiff_const.mul (hFi.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)))

lemma lps_iter (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2)
    (hFi : ContDiff ℝ ∞ (fun q => F q i)) (n : ℕ) (y : ℝ × ℝ) (x : Chart) :
    iteratedFDeriv ℝ n (lpsPhi c F i y) x =
      cylKer c i y • iteratedFDeriv ℝ n (fun q => F q i) (x + (0, -y)) := by
  have hFn : ContDiffAt ℝ n (fun z : Chart => F (z + (0, -y)) i) x :=
    ((hFi.comp (contDiff_id.add contDiff_const)).of_le (by simp)).contDiffAt
  have hcomp : iteratedFDeriv ℝ n (fun z : Chart => F (z + (0, -y)) i) x =
      iteratedFDeriv ℝ n (fun q => F q i) (x + (0, -y)) :=
    iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun q => F q i) n (0, -y) x
  rw [lps_eq_smul, iteratedFDeriv_const_smul_apply hFn, hcomp]

lemma lps_iter_zero (F : Chart → Fin 2 → ℝ) (i : Fin 2) (LF : ℝ)
    (hLF : ∀ q : Chart, LF < |q.2.2| → F q i = 0) (n : ℕ) (q : Chart) (hq : LF < |q.2.2|) :
    iteratedFDeriv ℝ n (fun q => F q i) q = 0 := by
  have hopen : IsOpen {x : Chart | LF < |x.2.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp (continuous_snd.comp continuous_snd))
  have hzero : (fun q => F q i) =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
    filter_upwards [hopen.mem_nhds (show q ∈ {x : Chart | LF < |x.2.2|} from hq)] with w hw
      using hLF w hw
  have hz := (hzero.iteratedFDeriv ℝ n).eq_of_nhds
  rw [hz]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hn)]
    simp

lemma lps_pointwise (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2) (LF : ℝ)
    (hLF : ∀ q : Chart, LF < |q.2.2| → F q i = 0)
    (hFi : ContDiff ℝ ∞ (fun q => F q i)) (M : ℝ) (n : ℕ)
    (hM : ∀ q : Chart, ‖iteratedFDeriv ℝ n (fun q => F q i) q‖ ≤ M)
    (y : ℝ × ℝ) (hy : y ∈ cellC c) (p : Chart) :
    ‖iteratedFDeriv ℝ n (lpsPhi c F i y) p‖ ≤
      (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LF) (p.2.2 + LF)).indicator
        (fun a => M * |cylKer c i a|) y := by
  rw [lps_iter c F i hFi n y p, norm_smul, Real.norm_eq_abs]
  by_cases hyW : y ∈ Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LF) (p.2.2 + LF)
  · rw [Set.indicator_of_mem hyW]
    calc |cylKer c i y| * ‖iteratedFDeriv ℝ n (fun q => F q i) (p + (0, -y))‖
        ≤ |cylKer c i y| * M := mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
      _ = M * |cylKer c i y| := mul_comm _ _
  · rw [Set.indicator_of_notMem hyW]
    have hyL : LF < |p.2.2 - y.2| := by
      by_contra hcon
      push_neg at hcon
      apply hyW
      obtain ⟨ha, hb⟩ := abs_le.1 hcon
      exact ⟨hy.1, ⟨by linarith, by linarith⟩⟩
    have hq : LF < |(p + (0, -y)).2.2| := by
      have e : (p + (0, -y)).2.2 = p.2.2 - y.2 := by simp [sub_eq_add_neg]
      rw [e]
      exact hyL
    simp [lps_iter_zero F i LF hLF n (p + (0, -y)) hq]

lemma lps_meas (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2)
    (hFi : ContDiff ℝ ∞ (fun q => F q i)) :
    ∀ (n : ℕ) (x : Chart),
      AEStronglyMeasurable (fun y => iteratedFDeriv ℝ n (lpsPhi c F i y) x)
        (volume.restrict (cellC c)) := by
  intro n x
  have hfun : (fun y => iteratedFDeriv ℝ n (lpsPhi c F i y) x) =
      fun y => cylKer c i y • iteratedFDeriv ℝ n (fun q => F q i) (x + (0, -y)) :=
    funext (fun y => lps_iter c F i hFi n y x)
  rw [hfun]
  have hcont : Continuous (fun y : ℝ × ℝ => iteratedFDeriv ℝ n (fun q => F q i) (x + (0, -y))) :=
    (hFi.continuous_iteratedFDeriv (m := n) (by simp)).comp
      (continuous_const.add (continuous_const.prodMk continuous_neg))
  exact (cylKW_meas c i).aestronglyMeasurable.smul hcont.aestronglyMeasurable

lemma lps_ind_int (c : ℝ) (hc : 0 < c) (i : Fin 2) (t L M : ℝ) :
    Integrable ((Ioc (-(c / 2)) (c / 2) ×ˢ Icc (t - L) (t + L)).indicator
      (fun a => M * |cylKer c i a|)) (volume.restrict (cellC c)) := by
  obtain ⟨C, hC⟩ := cylKerWindow c hc L
  have hW : MeasurableSet (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (t - L) (t + L)) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hsub : Ioc (-(c / 2)) (c / 2) ×ˢ Icc (t - L) (t + L) ⊆ cellC c :=
    fun y hy => ⟨hy.1, Set.mem_univ _⟩
  rw [integrable_indicator_iff hW]
  show Integrable _ ((volume.restrict (cellC c)).restrict _)
  rw [Measure.restrict_restrict hW, inter_eq_left.2 hsub]
  exact ((hC i t).1.abs).const_mul M

lemma lps_locDom (c : ℝ) (hc : 0 < c) (F : Chart → Fin 2 → ℝ) (i : Fin 2) (LF : ℝ)
    (hLF : ∀ q : Chart, LF < |q.2.2| → F q i = 0)
    (hFi : ContDiff ℝ ∞ (fun q => F q i))
    (hbdd : ∀ n : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (fun q => F q i) p‖ ≤ C) :
    UnforcedLeray.Kernels.LocDominated (volume.restrict (cellC c))
      (fun a p => lpsPhi c F i a p) univ := by
  unfold UnforcedLeray.Kernels.LocDominated
  intro n x _
  obtain ⟨Mn, hMn⟩ := hbdd n
  have hM0 : 0 ≤ max Mn 0 := le_max_right _ _
  have hM : ∀ q : Chart, ‖iteratedFDeriv ℝ n (fun q => F q i) q‖ ≤ max Mn 0 :=
    fun q => (hMn q).trans (le_max_left _ _)
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos,
    (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2.2 - (LF + 1)) (x.2.2 + (LF + 1))).indicator
      (fun a => max Mn 0 * |cylKer c i a|),
    lps_ind_int c hc i x.2.2 (LF + 1) (max Mn 0), ?_⟩
  refine ae_restrict_of_forall_mem (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)
    (fun a ha y hy => ?_)
  have hd : dist y x < 1 := Metric.mem_ball.1 hy
  have hdt : dist y.2.2 x.2.2 ≤ dist y x := by
    rw [Prod.dist_eq, Prod.dist_eq]
    exact le_max_of_le_right (le_max_of_le_right le_rfl)
  rw [Real.dist_eq] at hdt
  have hyt := abs_lt.1 (lt_of_le_of_lt hdt hd)
  have hsubW : Ioc (-(c / 2)) (c / 2) ×ˢ Icc (y.2.2 - LF) (y.2.2 + LF) ⊆
      Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2.2 - (LF + 1)) (x.2.2 + (LF + 1)) :=
    Set.prod_mono subset_rfl
      (Icc_subset_Icc (by linarith [hyt.1, hyt.2]) (by linarith [hyt.1, hyt.2]))
  calc ‖iteratedFDeriv ℝ n (lpsPhi c F i a) y‖
      ≤ (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (y.2.2 - LF) (y.2.2 + LF)).indicator
          (fun a => max Mn 0 * |cylKer c i a|) a :=
        lps_pointwise c F i LF hLF hFi (max Mn 0) n hM a ha y
    _ ≤ _ := Set.indicator_le_indicator_of_subset hsubW
        (fun b => mul_nonneg hM0 (abs_nonneg _)) a

lemma lps_uniform (c : ℝ) (hc : 0 < c) (F : Chart → Fin 2 → ℝ) (i : Fin 2) (LF : ℝ)
    (hLF : ∀ q : Chart, LF < |q.2.2| → F q i = 0)
    (hFi : ContDiff ℝ ∞ (fun q => F q i))
    (hbdd : ∀ n : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (fun q => F q i) p‖ ≤ C) (n : ℕ) :
    ∃ C : ℝ, ∀ x : Chart, ‖iteratedFDeriv ℝ n (lpsU c F i) x‖ ≤ C := by
  obtain ⟨Mn, hMn⟩ := hbdd n
  obtain ⟨Cw, hCw⟩ := cylKerWindow c hc LF
  refine ⟨max Mn 0 * Cw, fun x => ?_⟩
  have hM0 : 0 ≤ max Mn 0 := le_max_right _ _
  have hM : ∀ q : Chart, ‖iteratedFDeriv ℝ n (fun q => F q i) q‖ ≤ max Mn 0 :=
    fun q => (hMn q).trans (le_max_left _ _)
  have hcellm : MeasurableSet (cellC c) :=
    MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ
  have hsub : Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2.2 - LF) (x.2.2 + LF) ⊆ cellC c :=
    fun y hy => ⟨hy.1, Set.mem_univ _⟩
  have hW : MeasurableSet (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2.2 - LF) (x.2.2 + LF)) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hdom := lps_locDom c hc F i LF hLF hFi hbdd
  have hmeas := lps_meas c F i hFi
  have hsmooth : ∀ᵐ a ∂(volume.restrict (cellC c)), ContDiff ℝ ∞ (lpsPhi c F i a) :=
    ae_of_all _ (fun a => lps_contDiff c F i hFi a)
  have hnorm := UnforcedLeray.Kernels.norm_iteratedFDeriv_integral_le (F := fun a p => lpsPhi c F i a p)
    isOpen_univ hsmooth hmeas hdom n (Set.mem_univ x)
  have hintf : Integrable (fun a => ‖iteratedFDeriv ℝ n (lpsPhi c F i a) x‖)
      (volume.restrict (cellC c)) :=
    (hdom.integrable hmeas n (Set.mem_univ x)).norm
  refine le_trans hnorm ?_
  calc ∫ a, ‖iteratedFDeriv ℝ n (lpsPhi c F i a) x‖ ∂(volume.restrict (cellC c))
      ≤ ∫ a, ((Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2.2 - LF) (x.2.2 + LF)).indicator
          (fun a => max Mn 0 * |cylKer c i a|)) a ∂(volume.restrict (cellC c)) := by
        refine integral_mono_ae hintf (lps_ind_int c hc i x.2.2 LF (max Mn 0)) ?_
        exact ae_restrict_of_forall_mem hcellm
          (fun a ha => lps_pointwise c F i LF hLF hFi (max Mn 0) n hM a ha x)
    _ = ∫ a in (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2.2 - LF) (x.2.2 + LF)),
          max Mn 0 * |cylKer c i a| := by
        rw [setIntegral_indicator hW, Set.inter_eq_right.2 hsub]
    _ = max Mn 0 * ∫ a in (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (x.2.2 - LF) (x.2.2 + LF)),
          |cylKer c i a| := integral_const_mul _ _
    _ ≤ max Mn 0 * Cw := mul_le_mul_of_nonneg_left (hCw i x.2.2).2 hM0

lemma lps_fderiv_pt (c : ℝ) (F : Chart → Fin 2 → ℝ) (i : Fin 2)
    (hFi : ContDiff ℝ ∞ (fun q => F q i)) (y : ℝ × ℝ) (x v : Chart) :
    fderiv ℝ (lpsPhi c F i y) x v =
      cylKer c i y * fderiv ℝ (fun q => F q i) (x.1, x.2 - y) v := by
  have hFd : DifferentiableAt ℝ (fun q => F q i) (x + (0, -y)) :=
    (hFi.differentiable (by simp)).differentiableAt
  have hd : HasFDerivAt (fun z : Chart => F (z + (0, -y)) i)
      (fderiv ℝ (fun q => F q i) (x + (0, -y))) x :=
    (hasFDerivAt_comp_add_right (f := fun q => F q i) (0, -y)).2 hFd.hasFDerivAt
  have hfun : lpsPhi c F i y = fun z : Chart => cylKer c i y * F (z + (0, -y)) i := by
    rw [lps_eq_smul]
    rfl
  rw [hfun, (hd.const_mul (cylKer c i y)).fderiv, smul_apply, smul_eq_mul,
    show (x.1, x.2 - y) = x + (0, -y) from lps_shift x y]

lemma lps_fderiv_int (c : ℝ) (hc : 0 < c) (F : Chart → Fin 2 → ℝ) (i : Fin 2) (LF : ℝ)
    (hLF : ∀ q : Chart, LF < |q.2.2| → F q i = 0)
    (hFi : ContDiff ℝ ∞ (fun q => F q i))
    (hbdd : ∀ n : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (fun q => F q i) p‖ ≤ C)
    (x v : Chart) :
    fderiv ℝ (lpsU c F i) x v = ∫ a in cellC c, fderiv ℝ (lpsPhi c F i a) x v := by
  have hdom := lps_locDom c hc F i LF hLF hFi hbdd
  have hmeas := lps_meas c F i hFi
  have hsmooth : ∀ᵐ a ∂(volume.restrict (cellC c)), ContDiff ℝ ∞ (lpsPhi c F i a) :=
    ae_of_all _ (fun a => lps_contDiff c F i hFi a)
  have hI : iteratedFDeriv ℝ 1 (lpsU c F i) x =
      ∫ a, iteratedFDeriv ℝ 1 (lpsPhi c F i a) x ∂(volume.restrict (cellC c)) :=
    UnforcedLeray.Kernels.iteratedFDeriv_integral_eq (F := fun a p => lpsPhi c F i a p)
      isOpen_univ hsmooth hmeas hdom 1 (Set.mem_univ x)
  have hint1 : Integrable (fun a => iteratedFDeriv ℝ 1 (lpsPhi c F i a) x)
      (volume.restrict (cellC c)) :=
    hdom.integrable hmeas 1 (Set.mem_univ x)
  calc fderiv ℝ (lpsU c F i) x v = iteratedFDeriv ℝ 1 (lpsU c F i) x (fun _ => v) := by simp
    _ = (∫ a, iteratedFDeriv ℝ 1 (lpsPhi c F i a) x ∂(volume.restrict (cellC c))) (fun _ => v) := by
        rw [hI]
    _ = ∫ a, iteratedFDeriv ℝ 1 (lpsPhi c F i a) x (fun _ => v) ∂(volume.restrict (cellC c)) :=
        ContinuousMultilinearMap.integral_apply hint1 _
    _ = ∫ a in cellC c, fderiv ℝ (lpsPhi c F i a) x v := by simp

lemma lps_component (c : ℝ) (hc : 0 < c) (F : Chart → Fin 2 → ℝ) (hF : IsForceField c F)
    (i : Fin 2) :
    ContDiff ℝ ∞ (lpsU c F i) ∧ (∀ n : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (lpsU c F i) p‖ ≤ C) ∧
      ∀ p v : Chart, fderiv ℝ (lpsU c F i) p v =
        ∫ y in cellC c, cylKer c i y * fderiv ℝ (fun q => F q i) (p.1, p.2 - y) v := by
  obtain ⟨hFall, hperF, s0, s1, LF, hs0, hsuppF⟩ := hF
  have hFi : ContDiff ℝ ∞ (fun q => F q i) := hFall i
  have hperi : ∀ s q η, (fun q => F q i) (s, (q + c, η)) = (fun q => F q i) (s, (q, η)) :=
    fun s q η => congrFun (hperF s q η) i
  have hLF : ∀ q : Chart, LF < |q.2.2| → F q i = 0 := by
    intro q hq
    by_contra hne
    have hF0 : F q ≠ 0 := fun h0 => hne (by simp [h0])
    exact absurd (hsuppF q hF0).2 (not_le.2 hq)
  have hbdd : ∀ n : ℕ, ∃ C : ℝ, ∀ p, ‖iteratedFDeriv ℝ n (fun q => F q i) p‖ ≤ C := by
    intro n
    refine boundedDerivBand c hc (fun q => F q i) hFi hperi ?_ n
    refine ⟨s0, s1, LF, fun p hp => ?_⟩
    have hF0 : F p ≠ 0 := fun h0 => hp (by simp [h0])
    exact hsuppF p hF0
  refine ⟨?_, fun n => lps_uniform c hc F i LF hLF hFi hbdd n, fun p v => ?_⟩
  · exact contDiffOn_univ.1
      (UnforcedLeray.Kernels.contDiffOn_integral (F := fun a p => lpsPhi c F i a p) isOpen_univ
        (ae_of_all _ (fun a => lps_contDiff c F i hFi a)) (lps_meas c F i hFi)
        (lps_locDom c hc F i LF hLF hFi hbdd))
  · rw [lps_fderiv_int c hc F i LF hLF hFi hbdd p v]
    exact integral_congr_ae (ae_of_all _ (fun a => lps_fderiv_pt c F i hFi a p v))

theorem lerayPotSmooth : LerayPotSmooth := by
  intro c hc F hF
  have hsum : lerayPot c F = fun p => lpsU c F 0 p + lpsU c F 1 p := by
    funext p
    simp only [lerayPot, lpsU, lpsPhi, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum]
    exact (lps_component c hc F hF 0).1.add (lps_component c hc F hF 1).1
  · intro n
    obtain ⟨C0, hC0⟩ := (lps_component c hc F hF 0).2.1 n
    obtain ⟨C1, hC1⟩ := (lps_component c hc F hF 1).2.1 n
    refine ⟨C0 + C1, fun p => ?_⟩
    rw [hsum]
    have h0 : ContDiffAt ℝ n (lpsU c F 0) p :=
      (((lps_component c hc F hF 0).1).of_le (by simp)).contDiffAt
    have h1 : ContDiffAt ℝ n (lpsU c F 1) p :=
      (((lps_component c hc F hF 1).1).of_le (by simp)).contDiffAt
    have hadd := iteratedFDeriv_add_apply h0 h1
    show ‖iteratedFDeriv ℝ n (lpsU c F 0 + lpsU c F 1) p‖ ≤ C0 + C1
    rw [hadd]
    exact (norm_add_le _ _).trans (add_le_add (hC0 p) (hC1 p))
  · intro p v
    rw [hsum]
    have d0 : DifferentiableAt ℝ (lpsU c F 0) p :=
      ((lps_component c hc F hF 0).1.differentiable (by simp)) p
    have d1 : DifferentiableAt ℝ (lpsU c F 1) p :=
      ((lps_component c hc F hF 1).1.differentiable (by simp)) p
    show fderiv ℝ (lpsU c F 0 + lpsU c F 1) p v = _
    rw [fderiv_add d0 d1, ContinuousLinearMap.add_apply, (lps_component c hc F hF 0).2.2 p v,
      (lps_component c hc F hF 1).2.2 p v]
    simp only [lerayPot, Fin.sum_univ_two]

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
