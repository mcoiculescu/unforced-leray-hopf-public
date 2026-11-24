import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Defs
import UnforcedLeray.Short.PartIIIa.Sub.T15
import UnforcedLeray.Short.PartIIIa.T15_SepKernelBounds.HeatTailIterated

/-!


Joint measurability of `wardX0` in `(τ, y)` for a measurable chart tensor `g` (source 4171-4174).

Route. `sepW` is an iterated integral over `(l, z)` of the kernel derivative
`fderiv (heatLerayK (ν (1 - l²)) i j) (y - l z)` times `T(τ + 2 log l, z)`.
The kernel is `K_t = δ G_t + part2 (heatTail t)`; for `t ≤ 0` the heat kernel vanishes, so
`K_t` is constant in `t ≤ 0`, and for `t ≥ 0`, `heatTail t` is `C^∞` off the origin
(`HeatTailIterated`). Joint measurability of the kernel and of its `x`-derivatives follows from
difference quotients (as in `T8_3`), off the origin, with the value `0` at the origin
(the origin is a single point of the `z`-integral, hence irrelevant).
-/

set_option autoImplicit false

noncomputable section

open scoped Classical ContDiff
open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

namespace T8_1

/-! ## 1. Heat kernel facts -/

lemma heatG_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : Space) : IIIa.heatG t x = 0 := by
  unfold IIIa.heatG
  rcases lt_or_eq_of_le ht with h | h
  · have hneg : 4 * Real.pi * t < 0 := by nlinarith [Real.pi_pos]
    rw [Real.rpow_def_of_neg hneg]
    have hc : Real.cos ((-3 / 2 : ℝ) * Real.pi) = 0 := by
      have e : (-3 / 2 : ℝ) * Real.pi = -(Real.pi / 2) - Real.pi := by ring
      rw [e, Real.cos_sub_pi, Real.cos_neg, Real.cos_pi_div_two, neg_zero]
    rw [hc, mul_zero, zero_mul]
  · subst h
    rw [show 4 * Real.pi * (0:ℝ) = 0 by ring, Real.zero_rpow (by norm_num), zero_mul]

lemma heatTail_eq_of_nonpos {t : ℝ} (ht : t ≤ 0) : IIIa.heatTail t = IIIa.heatTail 0 := by
  funext x
  unfold IIIa.heatTail
  have h1 : ∫ a in Ioi t, IIIa.heatG a x = ∫ a, (Ioi t).indicator (fun a => IIIa.heatG a x) a :=
    (integral_indicator (measurableSet_Ioi (a := t))).symm
  have h2 : ∫ a in Ioi (0:ℝ), IIIa.heatG a x =
      ∫ a, (Ioi (0:ℝ)).indicator (fun a => IIIa.heatG a x) a :=
    (integral_indicator (measurableSet_Ioi (a := (0:ℝ)))).symm
  rw [h1, h2]
  congr 1
  funext a
  by_cases ha : 0 < a
  · rw [indicator_of_mem (show a ∈ Ioi t from lt_of_le_of_lt ht ha),
      indicator_of_mem (show a ∈ Ioi (0:ℝ) from ha)]
  · rw [indicator_of_notMem (show a ∉ Ioi (0:ℝ) from ha)]
    by_cases hb : a ∈ Ioi t
    · rw [indicator_of_mem hb, heatG_eq_zero_of_nonpos (not_lt.1 ha)]
    · rw [indicator_of_notMem hb]

lemma heatTail_contDiffAt (t : ℝ) {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (IIIa.heatTail t) x := by
  rcases le_or_gt t 0 with ht | ht
  · rw [heatTail_eq_of_nonpos ht]
    exact IIIa.heatTailIterated 0 le_rfl x hx |>.1
  · exact IIIa.heatTailIterated t ht.le x hx |>.1

lemma measurable_heatG : Measurable fun q : ℝ × Space => IIIa.heatG q.1 q.2 := by
  unfold IIIa.heatG
  fun_prop

lemma measurable_heatTail : Measurable fun q : ℝ × Space => IIIa.heatTail q.1 q.2 := by
  let Φ : (ℝ × Space) × ℝ → ℝ := fun p => if p.1.1 < p.2 then IIIa.heatG p.2 p.1.2 else 0
  have hΦ : Measurable Φ := by
    refine Measurable.ite (measurableSet_lt (measurable_fst.fst) measurable_snd) ?_ measurable_const
    exact measurable_heatG.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have hS := (StronglyMeasurable.integral_prod_right' (ν := volume)
    (f := fun p : (ℝ × Space) × ℝ => Φ p) hΦ.stronglyMeasurable).measurable
  have key : (fun q : ℝ × Space => IIIa.heatTail q.1 q.2) =
      fun q : ℝ × Space => ∫ a, Φ (q, a) := by
    funext q
    unfold IIIa.heatTail
    rw [← integral_indicator (measurableSet_Ioi (a := q.1))]
    congr 1
  rw [key]
  exact hS

/-! ## 2. Differentiability facts -/

lemma ev_ne {x : Space} (hx : x ≠ 0) : ∀ᶠ y in 𝓝 x, y ≠ 0 := isOpen_ne.mem_nhds hx

lemma diffAt_fderiv_apply {f : Space → ℝ} {x : Space} (h : ContDiffAt ℝ 2 f x) (v : Space) :
    DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := h.fderiv_right (m := 1) (by norm_num)
  exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const v)

lemma diffAt_part2 {f : Space → ℝ} {x : Space} (h : ContDiffAt ℝ 3 f x) (i j : Fin 3) :
    DifferentiableAt ℝ (fun y => IIIa.part2 f i j y) x := by
  unfold IIIa.part2
  have hg : ContDiffAt ℝ 2 (fun y => fderiv ℝ f y (coordinateVector j)) x := by
    have h1 : ContDiffAt ℝ 2 (fderiv ℝ f) x := h.fderiv_right (m := 2) (by norm_num)
    exact h1.clm_apply contDiffAt_const
  exact diffAt_fderiv_apply hg (coordinateVector i)

lemma diffAt_heatLerayK (t : ℝ) (i j : Fin 3) {x : Space} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y => IIIa.heatLerayK t i j y) x := by
  have h1 : DifferentiableAt ℝ (fun y => if i = j then IIIa.heatG t y else 0) x :=
    (IIIa.contDiffAt_delta t i j x).differentiableAt (by norm_num)
  have h3 : ContDiffAt ℝ 3 (IIIa.heatTail t) x :=
    IIIa.contDiffAt_nat (heatTail_contDiffAt t hx) 3
  have h2 : DifferentiableAt ℝ (fun y => IIIa.part2 (IIIa.heatTail t) i j y) x :=
    diffAt_part2 h3 i j
  have e : (fun y => IIIa.heatLerayK t i j y) =
      fun y => (if i = j then IIIa.heatG t y else 0) + IIIa.part2 (IIIa.heatTail t) i j y := rfl
  rw [e]
  exact h1.add h2

/-! ## 3. Generic measurability of a parametric derivative off the origin -/

lemma measurable_fderiv_offzero {X : Type*} [MeasurableSpace X] (F : X → Space → ℝ)
    (hF : Measurable fun q : X × Space => F q.1 q.2)
    (hd : ∀ p : X, ∀ x : Space, x ≠ 0 → DifferentiableAt ℝ (F p) x) (v : Space) :
    Measurable fun q : X × Space => if q.2 = 0 then (0:ℝ) else fderiv ℝ (F q.1) q.2 v := by
  have hS : MeasurableSet {q : X × Space | q.2 = 0} :=
    (measurableSet_singleton (0 : Space)).preimage measurable_snd
  have hq : ∀ n : ℕ, Measurable fun q : X × Space =>
      if q.2 = 0 then (0:ℝ) else ((n:ℝ) + 1) • (F q.1 (q.2 + ((n:ℝ) + 1)⁻¹ • v) - F q.1 q.2) := by
    intro n
    have hA : Measurable fun q : X × Space => F q.1 (q.2 + ((n:ℝ) + 1)⁻¹ • v) :=
      hF.comp (measurable_fst.prodMk (measurable_snd.add measurable_const))
    simp only [smul_eq_mul]
    exact Measurable.ite hS measurable_const (measurable_const.mul (hA.sub hF))
  refine measurable_of_tendsto_metrizable hq ?_
  refine tendsto_pi_nhds.2 fun q => ?_
  by_cases hq0 : q.2 = 0
  · simp only [if_pos hq0]
    exact tendsto_const_nhds
  · simp only [if_neg hq0]
    have h1 : Tendsto (fun n : ℕ => (n:ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hc : Tendsto (fun n : ℕ => ‖((n:ℝ) + 1)‖) atTop atTop :=
      h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
    exact (hd q.1 q.2 hq0).hasFDerivAt.lim (c := fun n : ℕ => (n:ℝ) + 1) v hc

/-! ## 4. The kernel `K` and its derivative as jointly measurable functions -/

/-- `∂_j heatTail` (off the origin). -/
def D1bar (j : Fin 3) (q : ℝ × Space) : ℝ :=
  if q.2 = 0 then 0 else fderiv ℝ (IIIa.heatTail q.1) q.2 (coordinateVector j)

/-- `∂_i ∂_j heatTail` (off the origin). -/
def D2bar (i j : Fin 3) (q : ℝ × Space) : ℝ :=
  if q.2 = 0 then 0 else fderiv ℝ (fun y => D1bar j (q.1, y)) q.2 (coordinateVector i)

/-- A jointly measurable version of `(t, x) ↦ heatLerayK t i j x`. -/
def Kbar (i j : Fin 3) (q : ℝ × Space) : ℝ :=
  (if i = j then IIIa.heatG q.1 q.2 else 0) + D2bar i j q

/-- A jointly measurable version of `(t, x) ↦ fderiv (heatLerayK t i j) x (e_k)`. -/
def Gm (k i j : Fin 3) (q : ℝ × Space) : ℝ :=
  if q.2 = 0 then 0 else fderiv ℝ (fun y => Kbar i j (q.1, y)) q.2 (coordinateVector k)

lemma measurable_D1bar (j : Fin 3) : Measurable (D1bar j) :=
  measurable_fderiv_offzero (fun t y => IIIa.heatTail t y) measurable_heatTail
    (fun t x hx => (heatTail_contDiffAt t hx).differentiableAt (by norm_num)) (coordinateVector j)

lemma D1bar_eq_of_ne {t : ℝ} {x : Space} (j : Fin 3) (hx : x ≠ 0) :
    (fun y => D1bar j (t, y)) =ᶠ[𝓝 x] (fun y => fderiv ℝ (IIIa.heatTail t) y (coordinateVector j)) := by
  filter_upwards [ev_ne hx] with y hy
  simp [D1bar, hy]

lemma measurable_D2bar (i j : Fin 3) : Measurable (D2bar i j) := by
  refine measurable_fderiv_offzero (fun t y => D1bar j (t, y)) (measurable_D1bar j)
    (fun t x hx => ?_) (coordinateVector i)
  have hd := diffAt_fderiv_apply (IIIa.contDiffAt_nat (heatTail_contDiffAt t hx) 2) (coordinateVector j)
  exact hd.congr_of_eventuallyEq (D1bar_eq_of_ne j hx)

lemma measurable_Kbar (i j : Fin 3) : Measurable (Kbar i j) := by
  have hδ : Measurable fun q : ℝ × Space => if i = j then IIIa.heatG q.1 q.2 else 0 := by
    split_ifs
    · exact measurable_heatG
    · exact measurable_const
  unfold Kbar
  exact hδ.add (measurable_D2bar i j)

lemma Kbar_eq_K (t : ℝ) (i j : Fin 3) {x : Space} (hx : x ≠ 0) :
    Kbar i j (t, x) = IIIa.heatLerayK t i j x := by
  have hfd : fderiv ℝ (fun y => D1bar j (t, y)) x =
      fderiv ℝ (fun y => fderiv ℝ (IIIa.heatTail t) y (coordinateVector j)) x :=
    (D1bar_eq_of_ne j hx).fderiv_eq
  dsimp only [Kbar, D2bar, IIIa.heatLerayK, IIIa.part2]
  rw [if_neg hx, hfd]

lemma Gm_eq (k i j : Fin 3) (t : ℝ) {x : Space} (hx : x ≠ 0) :
    Gm k i j (t, x) = fderiv ℝ (fun y => IIIa.heatLerayK t i j y) x (coordinateVector k) := by
  have hev : (fun y => Kbar i j (t, y)) =ᶠ[𝓝 x] (fun y => IIIa.heatLerayK t i j y) := by
    filter_upwards [ev_ne hx] with y hy
    exact Kbar_eq_K t i j hy
  dsimp only [Gm]
  rw [if_neg hx, hev.fderiv_eq]

lemma measurable_Gm (k i j : Fin 3) : Measurable (Gm k i j) := by
  refine measurable_fderiv_offzero (fun t y => Kbar i j (t, y)) (measurable_Kbar i j)
    (fun t x hx => ?_) (coordinateVector k)
  have hev : (fun y => Kbar i j (t, y)) =ᶠ[𝓝 x] (fun y => IIIa.heatLerayK t i j y) := by
    filter_upwards [ev_ne hx] with y hy
    exact Kbar_eq_K t i j hy
  exact (diffAt_heatLerayK t i j hx).congr_of_eventuallyEq hev

/-! ## 5. The separated integrand -/

/-- The jointly measurable `z`-integrand of `sepW`, at `p = ((τ, y), l)`. -/
def PsiM (ν : ℝ) (i : Fin 3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (p : (ℝ × Space) × ℝ) (z : Space) : ℂ :=
  ∑ j : Fin 3, ∑ k : Fin 3,
    ((Gm k i j (ν * (1 - p.2 ^ 2), p.1.2 - p.2 • z) : ℝ) : ℂ) *
      ((T (p.1.1 + 2 * Real.log p.2) z j k : ℝ) : ℂ)

lemma sepW_eq_PsiM (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (q : ℝ × Space) :
    IIIa.sepW ν μ T q.2 q.1 i =
      -2 * ∫ l in Ioo (0:ℝ) 1, (l : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiM ν i T (q, l) z := by
  unfold IIIa.sepW
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo (fun l hl => ?_)
  congr 1
  refine integral_congr_ae ?_
  have hz : ∀ᵐ z ∂(volume : Measure Space), z ∈ ({l⁻¹ • q.2} : Set Space)ᶜ :=
    compl_mem_ae_iff.2 (measure_singleton _)
  filter_upwards [hz] with z hz'
  have hne : z ≠ l⁻¹ • q.2 := hz'
  have hx : q.2 - l • z ≠ 0 := by
    intro h
    apply hne
    have h' : l • z = q.2 := (sub_eq_zero.1 h).symm
    rw [← h', smul_smul, inv_mul_cancel₀ hl.1.ne', one_smul]
  dsimp only [PsiM]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [Gm_eq k i j _ hx]

/-! ## 6. Measurability of the chart data -/

@[fun_prop]
lemma measurable_coord (a : Fin 3) : Measurable fun z : Space => z a :=
  (measurable_pi_apply a).comp (PiLp.continuous_ofLp 2 _).measurable

@[fun_prop]
lemma measurable_coordTen (ab : Fin 3 × Fin 3) : Measurable fun T : Ten3 => T ab :=
  (measurable_pi_apply ab).comp (PiLp.continuous_ofLp 2 _).measurable

lemma measurable_nsSym_entry (a b : Fin 3) : Measurable fun T : Ten3 => NearInst.nsSym T a b := by
  fin_cases a <;> fin_cases b <;> simp [NearInst.nsSym, NearInst.symRZ] <;> fun_prop

lemma measurable_cylFrame_entry (i k : Fin 3) :
    Measurable fun z : Space => NearInst.cylFrame z i k := by
  fin_cases i <;> fin_cases k <;> simp [NearInst.cylFrame, NearInst.hRad] <;> fun_prop

lemma measurable_chartOf (R c : ℝ) :
    Measurable fun s : ℝ × Space => NearInst.chartOf R c s.2 s.1 := by
  unfold NearInst.chartOf NearInst.hRad
  have hh : Measurable fun s : ℝ × Space =>
      Real.sqrt (s.2 0 ^ 2 + s.2 1 ^ 2) := by fun_prop
  have hL : Measurable fun s : ℝ × Space =>
      R * Real.log (Real.sqrt (s.2 0 ^ 2 + s.2 1 ^ 2) / R) + R * s.1 / 2 := by
    fun_prop
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · fun_prop
  · have hfl : Measurable fun s : ℝ × Space =>
        ⌊(R * Real.log (Real.sqrt (s.2 0 ^ 2 + s.2 1 ^ 2) / R) + R * s.1 / 2) / c + 1 / 2⌋ :=
      Measurable.floor ((hL.div_const c).add_const _)
    exact hL.sub (measurable_const.mul ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp hfl))
  · fun_prop

lemma measurable_cartLift_entry (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) (j k : Fin 3) :
    Measurable fun s : ℝ × Space => NearInst.cartLift R c g s.1 s.2 j k := by
  unfold NearInst.cartLift
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ (fun x _ => ?_)
  refine Measurable.mul (Finset.measurable_sum _ (fun y _ => ?_)) ?_
  · refine Measurable.mul ?_ ?_
    · exact (measurable_cylFrame_entry j y).comp measurable_snd
    · exact (measurable_chartOf R c).fst.mul
        ((measurable_nsSym_entry y x).comp (hg.comp (measurable_chartOf R c)))
  · exact (measurable_cylFrame_entry k x).comp measurable_snd

lemma measurable_oldPhys_entry (R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) (j k : Fin 3) :
    Measurable fun s : ℝ × Space => oldPhys R c g s.1 s.2 j k :=
  measurable_cartLift_entry R c g hg j k

/-! ## 7. Measurability of `PsiM` and `sepW` -/

lemma measurable_PsiM (ν : ℝ) (i : Fin 3) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => T s.1 s.2 j k) :
    Measurable fun p : ((ℝ × Space) × ℝ) × Space => PsiM ν i T p.1 p.2 := by
  have hl : Measurable fun p : ((ℝ × Space) × ℝ) × Space => p.1.2 := measurable_snd.comp measurable_fst
  have hy : Measurable fun p : ((ℝ × Space) × ℝ) × Space => p.1.1.2 :=
    measurable_snd.comp (measurable_fst.comp measurable_fst)
  have hτ : Measurable fun p : ((ℝ × Space) × ℝ) × Space => p.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have ht : Measurable fun p : ((ℝ × Space) × ℝ) × Space => ν * (1 - p.1.2 ^ 2) :=
    measurable_const.mul (measurable_const.sub (hl.pow_const 2))
  have hx : Measurable fun p : ((ℝ × Space) × ℝ) × Space => p.1.1.2 - p.1.2 • p.2 :=
    hy.sub (hl.smul measurable_snd)
  have hlog : Measurable fun p : ((ℝ × Space) × ℝ) × Space =>
      p.1.1.1 + 2 * Real.log p.1.2 :=
    hτ.add (measurable_const.mul (hl.log))
  unfold PsiM
  refine Finset.measurable_sum _ (fun j _ => ?_)
  refine Finset.measurable_sum _ (fun k _ => ?_)
  refine Measurable.mul (Complex.measurable_ofReal.comp ?_) (Complex.measurable_ofReal.comp ?_)
  · exact (measurable_Gm k i j).comp (ht.prodMk hx)
  · exact (hT j k).comp (hlog.prodMk measurable_snd)

lemma measurable_sepW_comp (ν : ℝ) (μ : ℂ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3)
    (hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => T s.1 s.2 j k) :
    Measurable fun q : ℝ × Space => IIIa.sepW ν μ T q.2 q.1 i := by
  have e : (fun q : ℝ × Space => IIIa.sepW ν μ T q.2 q.1 i) =
      fun q : ℝ × Space => -2 * ∫ l in Ioo (0:ℝ) 1,
        (l : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiM ν i T (q, l) z := by
    funext q
    exact sepW_eq_PsiM ν μ T i q
  rw [e]
  have hP := measurable_PsiM ν i T hT
  have hI : StronglyMeasurable fun r : (ℝ × Space) × ℝ => ∫ z : Space, PsiM ν i T r z :=
    StronglyMeasurable.integral_prod_right' (ν := volume)
      (f := fun p : ((ℝ × Space) × ℝ) × Space => PsiM ν i T p.1 p.2) hP.stronglyMeasurable
  have hO : Measurable fun r : (ℝ × Space) × ℝ =>
      (r.2 : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiM ν i T r z :=
    ((Complex.measurable_ofReal.comp measurable_snd).pow_const _).mul hI.measurable
  have hOS : StronglyMeasurable fun q : ℝ × Space =>
      ∫ l in Ioo (0:ℝ) 1, (l : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiM ν i T (q, l) z :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioo (0:ℝ) 1))
      (f := fun p : (ℝ × Space) × ℝ => (p.2 : ℂ) ^ (2 * μ + 2) * ∫ z : Space, PsiM ν i T p z)
      hO.stronglyMeasurable
  exact hOS.measurable.const_mul (-2)

end T8_1

open T8_1 in
/-- **`PartIII-b:IIIb-D2/3/1/8/1`** (`wardX0_measurable_of_measurable`): `wardX0` is jointly
measurable in `(τ, y)` for a measurable chart representative `g` (source 4171-4174). -/
theorem wardX0_measurable_of_measurable (ν μ R c : ℝ) (g : Chart → Ten3) (hg : Measurable g) :
    Measurable fun p : ℝ × Space => wardX0 ν μ R c g p.1 p.2 := by
  have hT : ∀ j k : Fin 3, Measurable fun s : ℝ × Space => oldPhys R c g s.1 s.2 j k :=
    fun j k => measurable_oldPhys_entry R c g hg j k
  have h1 : ∀ i : Fin 3, Measurable fun q : ℝ × Space =>
      IIIa.sepW ν (μ : ℂ) (oldPhys R c g) q.2 q.1 i :=
    fun i => measurable_sepW_comp ν (μ : ℂ) (oldPhys R c g) i hT
  have h2 : ∀ i : Fin 3, Measurable fun q : ℝ × Space =>
      IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) q.2 q.1 i :=
    fun i => measurable_sepW_comp ν ((μ : ℂ) + 1) (oldPhys R c g) i hT
  have hcomp : ∀ i : Fin 3, Measurable fun q : ℝ × Space =>
      (IIIa.sepW ν (μ : ℂ) (oldPhys R c g) q.2 q.1 i -
        IIIa.sepW ν ((μ : ℂ) + 1) (oldPhys R c g) q.2 q.1 i).re :=
    fun i => Complex.measurable_re.comp ((h1 i).sub (h2 i))
  unfold wardX0
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp (measurable_pi_iff.2 hcomp)

end UnforcedLeray.Short.PartIIIb.Concrete
