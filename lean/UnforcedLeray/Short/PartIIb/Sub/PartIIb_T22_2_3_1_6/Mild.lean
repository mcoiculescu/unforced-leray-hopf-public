import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T22_2_3_1_6.Gains
import UnforcedLeray.Short.PartIIb.Tasks.CylEnergy.ClassicalExists.HeatLapTransfer

/-!


Source: `the November 2 reference manuscript`, lines 2100-2105.  For a classical
`C²_b` solution of `Y_σ = νΔY + F`, the function `r ↦ e^{ν(s-r)Δ} Y(r)(x)` is continuous on `[0, s]`
and has the derivative `e^{ν(s-r)Δ} F(r)(x)` on `(0, s)` (differentiation under the integral with the
Gaussian majorant of `heatTimeDeriv`, and `heatLapTransfer`).  The fundamental theorem of calculus
gives Duhamel's formula.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open UnforcedLeray.Cons.C03.Concrete

namespace UnforcedLeray.Short.IIb.BwdRoute

namespace LS

open CylPDE

variable {T : ℝ}

/-- `heatSG` is bounded by the sup norm for every `a`. -/
theorem heatSG_abs_le' {a M : ℝ} {g : Pl → ℝ} (hg : ∀ y, |g y| ≤ M) (x : Pl) :
    |heatSG a g x| ≤ M := by
  by_cases ha : 0 < a
  · exact heatSG_abs_le ha hg x
  · have : heatSG a g x = g x := by
      unfold heatSG
      rw [ite_cond_eq_true _ _ (eq_true (not_lt.1 ha))]
    rw [this]
    exact hg x

/-- The heat semigroup is linear on bounded continuous functions. -/
theorem heatSG_sub {a M M' : ℝ} {g h : Pl → ℝ} (hgc : Continuous g) (hhc : Continuous h)
    (hg : ∀ y, |g y| ≤ M) (hh : ∀ y, |h y| ≤ M') (x : Pl) :
    heatSG a (fun y => g y - h y) x = heatSG a g x - heatSG a h x := by
  by_cases ha : 0 < a
  · unfold heatSG
    rw [ite_cond_eq_false _ _ (eq_false (not_le.2 ha)), ite_cond_eq_false _ _ (eq_false (not_le.2 ha)),
      ite_cond_eq_false _ _ (eq_false (not_le.2 ha)),
      ← integral_sub (k_int ha hgc hg x) (k_int ha hhc hh x)]
    congr 1
    funext y
    ring
  · unfold heatSG
    rw [ite_cond_eq_true _ _ (eq_true (not_lt.1 ha)), ite_cond_eq_true _ _ (eq_true (not_lt.1 ha)),
      ite_cond_eq_true _ _ (eq_true (not_lt.1 ha))]

/-- The integral of the Gaussian majorant of `heatTimeDeriv`. -/
theorem exp_majorant_int {a : ℝ} (ha : 0 < a) (x : Pl) :
    Integrable (fun y : Pl => Real.exp (-((x - y).1 ^ 2 + (x - y).2 ^ 2) / (12 * a))) := by
  have h3 := (heatK_sub_int (by linarith : 0 < 3 * a) x).const_mul (4 * Real.pi * (3 * a))
  refine h3.congr (ae_of_all _ fun y => ?_)
  show (4 * Real.pi * (3 * a)) * heatK (3 * a) (x - y) = _
  unfold heatK
  have h12 : (4 : ℝ) * (3 * a) = 12 * a := by ring
  have hne : (4 * Real.pi * (3 * a)) ≠ 0 := by positivity
  rw [h12]
  field_simp

/-- The derivative of `r ↦ e^{ν(s-r)Δ} Y(r)(x)`. -/
theorem heat_time_deriv {ν R M MF s : ℝ} {Y F : ℝ → Pl → ℝ} (hν : 0 < ν) (hY : CB T 2 Y)
    (hYs : EtaS T R Y) (hF : CB T 0 F) (hYM : CBle T 2 Y (fun _ => M)) (hFM : CBle T 0 F (fun _ => MF))
    (hpde : ∀ σ ∈ Icc 0 T, ∀ x : Pl,
      HasDerivWithinAt (fun r => Y r x) (ν * lapP (Y σ) x + F σ x) (Icc 0 T) σ)
    (hsT : s ≤ T) {r₀ : ℝ} (hr₀ : r₀ ∈ Ioo 0 s) (x : Pl) :
    HasDerivAt (fun r => heatSG (ν * (s - r)) (Y r) x) (heatSG (ν * (s - r₀)) (F r₀) x) r₀ := by
  set a := ν * (s - r₀) with ha_def
  have hsr : 0 < s - r₀ := by linarith [hr₀.2]
  have ha : 0 < a := mul_pos hν hsr
  have hM : 0 ≤ M := (abs_nonneg _).trans (CBle.top hYM r₀ ⟨hr₀.1.le, hr₀.2.le.trans hsT⟩ 0)
  have hMF : 0 ≤ MF := (abs_nonneg _).trans (hFM r₀ ⟨hr₀.1.le, hr₀.2.le.trans hsT⟩ 0)
  set δ := min r₀ ((s - r₀) / 2) with hδ
  have hδ0 : 0 < δ := lt_min hr₀.1 (by linarith)
  have hδ1 : δ ≤ r₀ := min_le_left _ _
  have hδ2 : δ ≤ (s - r₀) / 2 := min_le_right _ _
  -- facts on the neighbourhood
  have hball : ∀ r ∈ ball r₀ δ, r ∈ Ioo 0 s ∧ r ∈ Ioo 0 T ∧ a / 2 < ν * (s - r) ∧
      ν * (s - r) < 3 * a / 2 := by
    intro r hr
    rw [Real.ball_eq_Ioo] at hr
    have h1 : 0 < r := by linarith [hr.1]
    have h2 : r < s := by linarith [hr.2]
    refine ⟨⟨h1, h2⟩, ⟨h1, h2.trans_le hsT⟩, ?_, ?_⟩
    · have : (s - r₀) / 2 < s - r := by linarith [hr.2]
      rw [ha_def]
      nlinarith
    · have : s - r < 3 * (s - r₀) / 2 := by linarith [hr.1]
      rw [ha_def]
      nlinarith
  have hIcc : ∀ r ∈ ball r₀ δ, r ∈ Icc 0 T := fun r hr =>
    Ioo_subset_Icc_self (hball r hr).2.1
  -- bounds of the slices
  have hlap : ∀ r ∈ Icc 0 T, ∀ y : Pl, |lapP (Y r) y| ≤ M + M := by
    intro r hr y
    have h0 := CBle.top ((hYM.2 0).2 0) r hr y
    have h1 := CBle.top ((hYM.2 1).2 1) r hr y
    unfold lapP
    exact (abs_add_le _ _).trans (add_le_add h0 h1)
  have hYb : ∀ r ∈ Icc 0 T, ∀ y : Pl, |Y r y| ≤ M := fun r hr y => CBle.top hYM r hr y
  have hY0 : ∀ r ∈ Icc 0 T, Continuous (Y r) := fun r hr => DiffC.cont_slice (CB.cb0 hY).1 hr
  have hF0 : ∀ r ∈ Icc 0 T, Continuous (F r) := fun r hr => DiffC.cont_slice hF.1 hr
  have hlapc : ∀ r ∈ Icc 0 T, Continuous (lapP (Y r)) := by
    intro r hr
    have h0 : Continuous (B0579.pd 0 (B0579.pd 0 (Y r))) :=
      DiffC.cont_slice (g := fun σ => B0579.pd 0 (B0579.pd 0 (Y σ))) (CB.cb0 ((hY.2.2 0).2.2 0)).1 hr
    have h1 : Continuous (B0579.pd 1 (B0579.pd 1 (Y r))) :=
      DiffC.cont_slice (g := fun σ => B0579.pd 1 (B0579.pd 1 (Y σ))) (CB.cb0 ((hY.2.2 1).2.2 1)).1 hr
    exact h0.add h1
  -- the integrands
  let Qf : Pl → ℝ := fun z => z.1 ^ 2 + z.2 ^ 2
  let f : ℝ → Pl → ℝ := fun r y => heatK (ν * (s - r)) (x - y) * Y r y
  let cK : ℝ → Pl → ℝ := fun b z => (-1 / b + Qf z / (4 * b ^ 2)) * heatK b z
  let f' : ℝ → Pl → ℝ := fun r y =>
    (-ν) * cK (ν * (s - r)) (x - y) * Y r y +
      heatK (ν * (s - r)) (x - y) * (ν * lapP (Y r) y + F r y)
  have hcKcont : ∀ b : ℝ, Continuous (cK b) := fun b => by
    simp only [cK, Qf]
    exact Continuous.mul (by fun_prop) (heatK_cont' b)
  have hsub : Continuous (fun y : Pl => x - y) := continuous_const.sub continuous_id
  have hr₀I : r₀ ∈ Icc 0 T := ⟨hr₀.1.le, hr₀.2.le.trans hsT⟩
  -- the majorant
  let Cb : ℝ := ν * ((12 / a) * (1 / (2 * Real.pi * a))) * M +
    (1 / (2 * Real.pi * a)) * (ν * (M + M) + MF)
  have hCb : 0 ≤ Cb := by positivity
  have hmaj : ∀ r ∈ ball r₀ δ, ∀ y : Pl,
      ‖f' r y‖ ≤ Cb * Real.exp (-((x - y).1 ^ 2 + (x - y).2 ^ 2) / (12 * a)) := by
    intro r hr y
    obtain ⟨-, -, hb1, hb2⟩ := hball r hr
    have hrI := hIcc r hr
    set b := ν * (s - r) with hb
    set z := x - y with hz
    have hb0 : 0 < b := lt_trans (half_pos ha) hb1
    have hQ : 0 ≤ Qf z := by
      simp only [Qf]
      positivity
    have hK0 : 0 < heatK b z := heatK_pos' hb0 z
    have hc := HTD.coef_bound ha hb1 hb2 hQ
    have hk := HTD.heatK_upper ha hb1 hb2 z
    have hkey := HTD.bound_key ha hQ
    set E := Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (12 * a)) with hE
    have hE0 : 0 < E := Real.exp_pos _
    have hA : |cK b z| ≤ (12 / a) * (1 / (2 * Real.pi * a)) * E := by
      simp only [cK]
      rw [abs_mul, abs_of_pos hK0]
      calc |(-1 / b + Qf z / (4 * b ^ 2))| * heatK b z
          ≤ (2 / a + Qf z / a ^ 2) *
              ((1 / (2 * Real.pi * a)) * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / (6 * a))) :=
            mul_le_mul hc hk hK0.le (by positivity)
        _ ≤ (12 / a) * ((1 / (2 * Real.pi * a)) * E) := hkey
        _ = _ := by ring
    have hK1 : heatK b z ≤ (1 / (2 * Real.pi * a)) * E := by
      refine hk.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
      rw [neg_div, neg_div]
      have hQ' : 0 ≤ z.1 ^ 2 + z.2 ^ 2 := by positivity
      have : (z.1 ^ 2 + z.2 ^ 2) / (12 * a) ≤ (z.1 ^ 2 + z.2 ^ 2) / (6 * a) :=
        div_le_div_of_nonneg_left hQ' (by positivity) (by linarith)
      linarith
    have hB : |ν * lapP (Y r) y + F r y| ≤ ν * (M + M) + MF := by
      refine (abs_add_le _ _).trans (add_le_add ?_ (hFM r hrI y))
      rw [abs_mul, abs_of_pos hν]
      exact mul_le_mul_of_nonneg_left (hlap r hrI y) hν.le
    show ‖(-ν) * cK b z * Y r y + heatK b z * (ν * lapP (Y r) y + F r y)‖ ≤ _
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    have h1 : ν * |cK b z| * |Y r y| ≤ ν * ((12 / a) * (1 / (2 * Real.pi * a)) * E) * M :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA hν.le) (hYb r hrI y) (abs_nonneg _)
        (by positivity)
    have h2 : heatK b z * |ν * lapP (Y r) y + F r y| ≤
        (1 / (2 * Real.pi * a)) * E * (ν * (M + M) + MF) :=
      mul_le_mul hK1 hB (abs_nonneg _) (by positivity)
    have t1 : |(-ν) * cK b z * Y r y| = ν * |cK b z| * |Y r y| := by
      rw [abs_mul ((-ν) * cK b z), abs_mul (-ν), abs_neg, abs_of_pos hν]
    have t2 : |heatK b z * (ν * lapP (Y r) y + F r y)| =
        heatK b z * |ν * lapP (Y r) y + F r y| := by
      rw [abs_mul, abs_of_pos hK0]
    rw [t1, t2]
    have e : Cb * E = ν * ((12 / a) * (1 / (2 * Real.pi * a)) * E) * M +
        (1 / (2 * Real.pi * a)) * E * (ν * (M + M) + MF) := by
      simp only [Cb]
      ring
    rw [e]
    exact add_le_add h1 h2
  have hderiv : ∀ r ∈ ball r₀ δ, ∀ y : Pl, HasDerivAt (fun r' => f r' y) (f' r y) r := by
    intro r hr y
    obtain ⟨hrs, hrT, hb1, -⟩ := hball r hr
    have hb0 : 0 < ν * (s - r) := lt_trans (half_pos ha) hb1
    have h1 := HTD.heatK_hasDerivAt_b hb0 (x - y)
    have h2 : HasDerivAt (fun r' : ℝ => ν * (s - r')) (-ν) r := by
      have := ((hasDerivAt_id' r).const_sub s).const_mul ν
      simpa using this
    have h3 := HasDerivAt.comp r h1 h2
    have h4 := (hpde r (Ioo_subset_Icc_self hrT) y).hasDerivAt (Icc_mem_nhds hrT.1 hrT.2)
    have h5 := h3.mul h4
    refine h5.congr_deriv ?_
    simp only [f', cK, Qf, Function.comp]
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := r₀)
    (F := f) (F' := f') (s := ball r₀ δ)
    (bound := fun y => Cb * Real.exp (-((x - y).1 ^ 2 + (x - y).2 ^ 2) / (12 * a)))
    (ball_mem_nhds r₀ hδ0)
    (Filter.eventually_of_mem (ball_mem_nhds r₀ hδ0) fun r hr =>
      ((heatK_cont' _).comp hsub |>.mul (hY0 r (hIcc r hr))).aestronglyMeasurable)
    (k_int ha (hY0 r₀ hr₀I) (hYb r₀ hr₀I) x)
    (by
      refine Continuous.aestronglyMeasurable ?_
      exact ((continuous_const.mul ((hcKcont _).comp hsub)).mul (hY0 r₀ hr₀I)).add
        (((heatK_cont' _).comp hsub).mul ((continuous_const.mul (hlapc r₀ hr₀I)).add (hF0 r₀ hr₀I))))
    (ae_of_all _ fun y r hr => hmaj r hr y)
    ((exp_majorant_int ha x).const_mul Cb)
    (ae_of_all _ fun y r hr => hderiv r hr y)
  -- the value of the derivative
  have hg := hY0 r₀ hr₀I
  have hval : (∫ y : Pl, f' r₀ y) = heatSG a (F r₀) x := by
    have hC2 : ContDiff ℝ 2 (Y r₀) := by
      have := CB.contDiff hY r₀ hr₀I
      exact_mod_cast this
    have hW0 := wb_of (hYb r₀ hr₀I) (hYs r₀ hr₀I)
    have hW1 : ∀ j : Fin 2, WB (M * Real.cosh R) (B0579.pd j (Y r₀)) := fun j =>
      wb_of (CBle.top (hYM.2 j) r₀ hr₀I) ((hYs.pd j) r₀ hr₀I)
    have hW2 : ∀ i j : Fin 2, WB (M * Real.cosh R) (B0579.pd i (B0579.pd j (Y r₀))) := fun i j =>
      wb_of (CBle.top ((hYM.2 j).2 i) r₀ hr₀I) (((hYs.pd j).pd i) r₀ hr₀I)
    have htr := HLT.heatLapTransfer _ (Y r₀) hC2 hW0 hW1 hW2 a ha x
    have hLc : ∀ z : Pl, cK a z = lapP (heatK a) z := fun z => (HTD.lapP_heatK ha z).symm
    have hi1 := k_int ha (hlapc r₀ hr₀I) (hlap r₀ hr₀I) x
    have hi2 := k_int ha (hF0 r₀ hr₀I) (hFM r₀ hr₀I) x
    have hi3 : Integrable (fun y : Pl => heatK a (x - y) * (ν * lapP (Y r₀) y + F r₀ y)) := by
      refine (hi1.const_mul ν |>.add hi2).congr (ae_of_all _ fun y => ?_)
      simp only [Pi.add_apply]
      ring
    have hi4 : Integrable (fun y : Pl => (-ν) * cK a (x - y) * Y r₀ y) := by
      have h := hmain.1.sub hi3
      refine h.congr (ae_of_all _ fun y => ?_)
      simp only [Pi.sub_apply, f', ha_def.symm]
      ring
    have e1 : (∫ y : Pl, (-ν) * cK a (x - y) * Y r₀ y) = (-ν) * heatSG a (lapP (Y r₀)) x := by
      rw [htr, ← integral_const_mul]
      congr 1
      funext y
      rw [hLc]
      ring
    have e2 : (∫ y : Pl, heatK a (x - y) * (ν * lapP (Y r₀) y + F r₀ y)) =
        ν * heatSG a (lapP (Y r₀)) x + heatSG a (F r₀) x := by
      have e3 : ∀ g : Pl → ℝ, heatSG a g x = ∫ y : Pl, heatK a (x - y) * g y := fun g => by
        unfold heatSG
        rw [ite_cond_eq_false _ _ (eq_false (not_le.2 ha))]
      rw [e3, e3, ← integral_const_mul, ← integral_add (hi1.const_mul ν) hi2]
      congr 1
      funext y
      ring
    have e4 : (∫ y : Pl, f' r₀ y) = (∫ y : Pl, (-ν) * cK a (x - y) * Y r₀ y) +
        ∫ y : Pl, heatK a (x - y) * (ν * lapP (Y r₀) y + F r₀ y) :=
      integral_add hi4 hi3
    rw [e4, e1, e2]
    ring
  have hfin := hmain.2
  rw [hval] at hfin
  refine hfin.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds r₀ hδ0] with r hr
  obtain ⟨-, -, hb1, -⟩ := hball r hr
  have hb0 : 0 < ν * (s - r) := lt_trans (half_pos ha) hb1
  show heatSG (ν * (s - r)) (Y r) x = ∫ y : Pl, heatK (ν * (s - r)) (x - y) * Y r y
  unfold heatSG
  rw [ite_cond_eq_false _ _ (eq_false (not_le.2 hb0))]

/-- **Leaf `/7`.** -/
theorem classicalToMild : ClassicalToMild := by
  intro ν T R Y F hν hT hY hYs hF hFs hpde s hs x
  obtain ⟨M, hM, hYM⟩ := CB.exists_le hY
  obtain ⟨MF, hMF, hFM⟩ := CB.exists_le hF
  have hYb : ∀ r ∈ Icc 0 T, ∀ y : Pl, |Y r y| ≤ M := fun r hr y => CBle.top hYM r hr y
  have hY0 : ∀ r ∈ Icc 0 T, Continuous (Y r) := fun r hr => DiffC.cont_slice (CB.cb0 hY).1 hr
  have hIcc : ∀ r ∈ Icc 0 s, r ∈ Icc 0 T := fun r hr => ⟨hr.1, hr.2.trans hs.2⟩
  -- the time Lipschitz bound
  set Mt : ℝ := ν * (M + M) + MF with hMt
  have hMt0 : 0 ≤ Mt := by positivity
  have hLip : ∀ r ∈ Icc 0 T, ∀ r' ∈ Icc 0 T, ∀ y : Pl, |Y r y - Y r' y| ≤ Mt * |r - r'| := by
    intro r hr r' hr' y
    have h := (convex_Icc (0 : ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => Y r y) (f' := fun σ => ν * lapP (Y σ) y + F σ y) (C := Mt) (x := r') (y := r)
      (fun σ hσ => hpde σ hσ y)
      (fun σ hσ => by
        have h0 := CBle.top ((hYM.2 0).2 0) σ hσ y
        have h1 := CBle.top ((hYM.2 1).2 1) σ hσ y
        have hl : |lapP (Y σ) y| ≤ M + M := by
          unfold lapP
          exact (abs_add_le _ _).trans (add_le_add h0 h1)
        rw [Real.norm_eq_abs]
        refine (abs_add_le _ _).trans (add_le_add ?_ (hFM σ hσ y))
        rw [abs_mul, abs_of_pos hν]
        exact mul_le_mul_of_nonneg_left hl hν.le) hr' hr
    simpa [Real.norm_eq_abs] using h
  -- continuity of `r ↦ e^{ν(s-r)Δ} Y(r)(x)`
  have hcont : ContinuousOn (fun r => heatSG (ν * (s - r)) (Y r) x) (Icc 0 s) := by
    intro r₀ hr₀
    have hr₀T := hIcc r₀ hr₀
    have hW := wb_of (hYb r₀ hr₀T) (hYs r₀ hr₀T)
    have hc := heatCont _ (Y r₀) (hY0 r₀ hr₀T) hW
    have hmap : ContinuousWithinAt (fun r : ℝ => ((ν * (s - r), x) : ℝ × Pl)) (Icc 0 s) r₀ := by
      apply Continuous.continuousWithinAt
      fun_prop
    have h1 : ContinuousWithinAt (fun r => heatSG (ν * (s - r)) (Y r₀) x) (Icc 0 s) r₀ :=
      ContinuousWithinAt.comp (g := fun z : ℝ × Pl => heatSG z.1 (Y r₀) z.2)
        (f := fun r : ℝ => ((ν * (s - r), x) : ℝ × Pl))
        (hc (ν * (s - r₀), x) ⟨mul_nonneg hν.le (by linarith [hr₀.2]), mem_univ _⟩) hmap
        (fun r hr => ⟨mul_nonneg hν.le (by linarith [hr.2]), mem_univ _⟩)
    have hdiff : ∀ r ∈ Icc 0 s, |heatSG (ν * (s - r)) (Y r) x - heatSG (ν * (s - r)) (Y r₀) x| ≤
        Mt * |r - r₀| := by
      intro r hr
      have hrT := hIcc r hr
      rw [← heatSG_sub (hY0 r hrT) (hY0 r₀ hr₀T) (hYb r hrT) (hYb r₀ hr₀T) x]
      exact heatSG_abs_le' (fun y => hLip r hrT r₀ hr₀T y) x
    have h2 : Tendsto (fun r => heatSG (ν * (s - r)) (Y r) x - heatSG (ν * (s - r)) (Y r₀) x)
        (𝓝[Icc 0 s] r₀) (𝓝 0) := by
      have h3 : Tendsto (fun r : ℝ => Mt * |r - r₀|) (𝓝[Icc 0 s] r₀) (𝓝 0) := by
        have : Continuous (fun r : ℝ => Mt * |r - r₀|) := by fun_prop
        have h4 := (this.tendsto r₀).mono_left (nhdsWithin_le_nhds (s := Icc 0 s))
        simpa using h4
      refine squeeze_zero_norm' ?_ h3
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [Real.norm_eq_abs]
      exact hdiff r hr
    have h5 := h2.add h1.tendsto
    simp only [zero_add, sub_add_cancel] at h5
    exact h5
  -- the fundamental theorem of calculus
  have hA := admH (T := T) hF hFM (fun _ _ => hMF)
  have hint := dConv_int hν zero_le_one continuousOn_const (fun _ _ => hMF) hA hs x
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs.1 hcont
    (fun r hr => heat_time_deriv hν hY hYs hF hYM hFM hpde hs.2 hr x) hint
  have he1 : heatSG (ν * (s - s)) (Y s) x = Y s x := by
    simp [heatSG]
  have he2 : heatSG (ν * (s - 0)) (Y 0) x = heatSG (ν * s) (Y 0) x := by
    rw [sub_zero]
  rw [he1, he2] at hftc
  show Y s x = heatSG (ν * s) (Y 0) x + ∫ r in (0 : ℝ)..s, heatSG (ν * (s - r)) (F r) x
  rw [hftc]
  ring

end LS

end UnforcedLeray.Short.IIb.BwdRoute
