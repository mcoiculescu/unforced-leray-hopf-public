import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_10_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_1_3
import UnforcedLeray.Short.PartIIIa.Tasks16.DomPointwise.Kernel

/-!
# Helpers for `wardDXYoungSup_proved` (1): pointwise sup bound for `w2Dom`

Source of record: `the November 2 reference manuscript` (73 pages), 3603-3629,
3687-3713, 3838-3845, 5238-5244.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- Spatial `L²` norm of the dilated kernel `z ↦ k (y - l • z)`. -/
theorem w114_lintegral_k_dilate {k : Space → ℝ≥0∞} (hk : Measurable k) (y : Space)
    {l : ℝ} (hl : 0 < l) :
    (∫⁻ z : Space, k (y - l • z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (l ^ (-(3 / 2 : ℝ))) * (∫⁻ x : Space, k x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  have hm : Measurable fun x : Space => k (y - x) ^ (2 : ℝ) :=
    (hk.comp (measurable_const.sub measurable_id)).pow_const 2
  have hd : ∫⁻ z : Space, k (y - l • z) ^ (2 : ℝ) =
      ENNReal.ofReal ((l ^ 3)⁻¹) * ∫⁻ x : Space, k x ^ (2 : ℝ) := by
    refine (IIIa.lintegral_smul_space l hl hm).trans ?_
    congr 1
    exact lintegral_sub_left_eq_self (fun x => k x ^ (2 : ℝ)) y
  rw [hd, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  congr 2
  rw [← Real.rpow_natCast l 3, ← Real.rpow_neg hl.le, ← Real.rpow_mul hl.le]
  congr 1
  norm_num

/-- Dilation integral bound over `(0, 1)` for any period `P > 0` and exponent `c > -1`. -/
theorem w114_dilation_sum {c P : ℝ} (hc : -1 < c) (hP : 0 < P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : ℝ → ℝ≥0∞, Measurable G → (∀ s, G (s + P) = G s) → ∀ τ : ℝ,
      ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l) ≤
        ENNReal.ofReal C * IIIa.ltauAt P G := by
  set κ : ℝ := (c + 1) / 2
  have hκ : 0 < κ := by simp only [κ]; linarith
  set e : ℝ := Real.exp (-κ * P)
  have he_pos : 0 < e := Real.exp_pos _
  have he_lt : e < 1 := by
    have h := Real.exp_lt_exp.mpr (show -κ * P < 0 by nlinarith)
    rwa [Real.exp_zero] at h
  have h1e : 0 < 1 - e := by linarith
  set C : ℝ := 1 / 2 * ((1 - e)⁻¹ * P)
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, fun G hGm hper τ => ?_⟩
  have hpt : ∀ l ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal |(-2 * l⁻¹)|
          * (ENNReal.ofReal (Real.exp (-κ * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) := by
    intro l hl
    have hl0 : 0 < l := hl.1
    have habs : |(-2 * l⁻¹)| = 2 * l⁻¹ := by
      rw [show (-2 * l⁻¹) = -(2 * l⁻¹) by ring, abs_neg,
        abs_of_pos (mul_pos two_pos (inv_pos.mpr hl0))]
    have e1 : Real.exp (-κ * (-2 * Real.log l)) = l ^ c * l := by
      rw [← Real.rpow_add_one hl0.ne' c, Real.rpow_def_of_pos hl0]
      congr 1
      simp only [κ]; ring
    have e2 : τ - (-2 * Real.log l) = τ + 2 * Real.log l := by ring
    have hL : ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (2 * l ^ c) * G (τ + 2 * Real.log l) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), mul_assoc]
    have hR : ENNReal.ofReal (2 * l⁻¹) * (ENNReal.ofReal (l ^ c * l) * G (τ + 2 * Real.log l))
        = ENNReal.ofReal (2 * l ^ c) * G (τ + 2 * Real.log l) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (inv_nonneg.mpr hl0.le))]
      have hal : 2 * l⁻¹ * (l ^ c * l) = 2 * l ^ c := by field_simp
      rw [hal]
    rw [habs, e1, e2, hL, hR]
  have hJ1 : ∫⁻ l in Ioo (0 : ℝ) 1,
        ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l))
      = ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal |(-2 * l⁻¹)|
          * (ENNReal.ofReal (Real.exp (-κ * (-2 * Real.log l)))
              * G (τ - (-2 * Real.log l))) :=
    setLIntegral_congr_fun measurableSet_Ioo fun l hl => hpt l hl
  have hf' : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun l : ℝ => -2 * Real.log l) (-2 * x⁻¹) (Ioo (0 : ℝ) 1) x :=
    fun x hx => ((Real.hasDerivAt_log hx.1.ne').const_mul (-2)).hasDerivWithinAt
  have hinj : InjOn (fun l : ℝ => -2 * Real.log l) (Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    have h1 : Real.log a = Real.log b := by
      have hab' : -2 * Real.log a = -2 * Real.log b := hab
      linarith
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr ha.1) (Set.mem_Ioi.mpr hb.1) h1
  have hJ2 := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hf' hinj
    (fun x => ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x))
  have hsub : (fun l : ℝ => -2 * Real.log l) '' Ioo (0 : ℝ) 1 ⊆ Ioi 0 := by
    rintro _ ⟨l, hl, rfl⟩
    have := Real.log_neg hl.1 hl.2
    show 0 < -2 * Real.log l
    linarith
  have hfac : (1 - ENNReal.ofReal e)⁻¹ * ENNReal.ofReal P =
      ENNReal.ofReal ((1 - e)⁻¹ * P) := by
    have hsub1 : (1 : ℝ≥0∞) - ENNReal.ofReal e = ENNReal.ofReal (1 - e) := by
      rw [ENNReal.ofReal_sub 1 he_pos.le, ENNReal.ofReal_one]
    rw [hsub1, ← ENNReal.ofReal_inv_of_pos h1e, ← ENNReal.ofReal_mul (inv_nonneg.2 h1e.le)]
  have hL : ENNReal.ofReal 2 * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
      ≤ ENNReal.ofReal ((1 - e)⁻¹ * P) * IIIa.ltauAt P G := by
    calc ENNReal.ofReal 2 * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
        = ∫⁻ l in Ioo (0 : ℝ) 1,
            ENNReal.ofReal 2 * (ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ x in (fun l : ℝ => -2 * Real.log l) '' Ioo (0 : ℝ) 1,
            ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x) := hJ1.trans hJ2.symm
      _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal (Real.exp (-κ * x)) * G (τ - x) := lintegral_mono_set hsub
      _ ≤ (1 - ENNReal.ofReal e)⁻¹ * (∫⁻ u in Ioc 0 P, G u) := pds_sum hκ hP hGm hper τ
      _ ≤ (1 - ENNReal.ofReal e)⁻¹ * (ENNReal.ofReal P * IIIa.ltauAt P G) :=
          mul_le_mul' le_rfl (pds_cs hP hGm)
      _ = ENNReal.ofReal ((1 - e)⁻¹ * P) * IIIa.ltauAt P G := by
          rw [← mul_assoc, hfac]
  have hhalf : ENNReal.ofReal (1 / 2) * ENNReal.ofReal 2 = 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)
      = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal 2
          * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ c) * G (τ + 2 * Real.log l)) := by
        rw [← mul_assoc, hhalf, one_mul]
    _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal ((1 - e)⁻¹ * P) * IIIa.ltauAt P G) :=
        mul_le_mul' le_rfl hL
    _ = ENNReal.ofReal C * IIIa.ltauAt P G := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- Pointwise `L^∞_{τ,y}` bound on `w2Dom k a g` for any `L²` kernel `k`. -/
theorem w114_w2Dom_sup {k : Space → ℝ≥0∞} (hk : Measurable k)
    (hk2 : ∫⁻ x : Space, k x ^ (2 : ℝ) ≠ ⊤) {a P : ℝ} (ha : 1 / 2 < a) (hP : 0 < P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ → Space → ℝ≥0∞, Measurable (Function.uncurry g) →
      (∀ τ z, g (τ + P) z = g τ z) → ∀ (τ : ℝ) (y : Space),
        w2Dom k a g τ y ≤ ENNReal.ofReal C * IIIa.ltauLq P 2 g := by
  obtain ⟨Cpds, hCpds0, hpds⟩ := w114_dilation_sum (c := a - 3 / 2) (by linarith) hP
  set Ik : ℝ≥0∞ := (∫⁻ x : Space, k x ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
  have hIktop : Ik ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hk2
  refine ⟨Ik.toReal * Cpds, by positivity, fun g hgm hper τ y => ?_⟩
  set G : ℝ → ℝ≥0∞ := fun s => (∫⁻ z : Space, g s z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) with hG
  have hGm : Measurable G := by
    have h1 : Measurable fun q : ℝ × Space => g q.1 q.2 ^ (2 : ℝ) := hgm.pow_const 2
    exact h1.lintegral_prod_right'.pow_const (1 / 2 : ℝ)
  have hGper : ∀ s, G (s + P) = G s := fun s => by
    simp only [hG, hper]
  have hGL : IIIa.ltauAt P G = IIIa.ltauLq P 2 g := by
    unfold IIIa.ltauAt IIIa.ltauLq
    have hsq : ∀ s, G s ^ (2 : ℝ) = (∫⁻ z : Space, g s z ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) := fun s => by
      simp only [hG, ← ENNReal.rpow_mul]
      congr 1; ring
    simp_rw [hsq]
  have hinner : ∀ l ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, k (y - l • z) * g (τ + 2 * Real.log l) z ≤
        Ik * (ENNReal.ofReal (l ^ (a - 3 / 2)) * G (τ + 2 * Real.log l)) := by
    intro l hl
    have hf : AEMeasurable (fun z : Space => k (y - l • z)) volume :=
      (hk.comp (measurable_const.sub (measurable_const_smul l))).aemeasurable
    have hgτ : AEMeasurable (g (τ + 2 * Real.log l)) volume :=
      (hgm.comp (measurable_prodMk_left (x := τ + 2 * Real.log l))).aemeasurable
    have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hf hgτ
    have hdil := w114_lintegral_k_dilate hk y hl.1
    calc ENNReal.ofReal (l ^ a) * ∫⁻ z : Space, k (y - l • z) * g (τ + 2 * Real.log l) z
        ≤ ENNReal.ofReal (l ^ a) *
            ((∫⁻ z : Space, k (y - l • z) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * G (τ + 2 * Real.log l)) :=
          mul_le_mul' le_rfl hcs
      _ = ENNReal.ofReal (l ^ a) *
            ((ENNReal.ofReal (l ^ (-(3 / 2 : ℝ))) * Ik) * G (τ + 2 * Real.log l)) := by
          rw [hdil]
      _ = Ik * (ENNReal.ofReal (l ^ (a - 3 / 2)) * G (τ + 2 * Real.log l)) := by
          have hpow : l ^ (a - 3 / 2) = l ^ a * l ^ (-(3 / 2 : ℝ)) := by
            rw [sub_eq_add_neg, Real.rpow_add hl.1]
          rw [hpow, ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
          ring
  calc w2Dom k a g τ y
      ≤ ∫⁻ l in Ioo (0 : ℝ) 1,
          Ik * (ENNReal.ofReal (l ^ (a - 3 / 2)) * G (τ + 2 * Real.log l)) :=
        setLIntegral_mono' measurableSet_Ioo hinner
    _ = Ik * ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a - 3 / 2)) * G (τ + 2 * Real.log l) :=
        lintegral_const_mul' _ _ hIktop
    _ ≤ Ik * (ENNReal.ofReal Cpds * IIIa.ltauAt P G) :=
        mul_le_mul' le_rfl (hpds G hGm hGper τ)
    _ = ENNReal.ofReal (Ik.toReal * Cpds) * IIIa.ltauLq P 2 g := by
        rw [hGL, ← mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hIktop]

/-- `IIIa.sepKd j D` is square-integrable on `Space` for `D > 0`. -/
theorem w114_sepKd_sq_ne_top (j : ℕ) {D : ℝ} (hD : 0 < D) :
    ∫⁻ x : Space, IIIa.sepKd j D x ^ (2 : ℝ) ≠ ⊤ := by
  rw [IIIa.lintegral_sepKd_rpow j D 2 hD two_pos]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (IIIa.lintegral_sepKd_rpow_one_ne_top j 2 one_lt_two)

/-- `w2k r0 D A` is square-integrable on `Space` for `r0 ≥ 0`, `D > 0`. -/
theorem w114_w2k_sq_ne_top {r0 D : ℝ} (hr0 : 0 ≤ r0) (hD : 0 < D) (A : ℝ) :
    ∫⁻ x : Space, w2k r0 D A x ^ (2 : ℝ) ≠ ⊤ := by
  set M₀ : ℝ := (r0 + D) / D / 2 * (D ^ 2)⁻¹
  have hM₀ : 0 ≤ M₀ := by positivity
  have hle : ∀ x : Space, w2k r0 D A x ≤ ENNReal.ofReal M₀ := fun x => by
    unfold w2k
    split_ifs with h
    · refine ENNReal.ofReal_le_ofReal ?_
      unfold w2M M₀
      gcongr
      linarith [sq_nonneg (x 2)]
    · exact zero_le
  have hsq : ∀ x : Space, w2k r0 D A x ^ (2 : ℝ) ≤ ENNReal.ofReal M₀ * w2k r0 D A x := fun x => by
    rw [show (2 : ℝ) = (2 : ℕ) by norm_num, ENNReal.rpow_natCast, sq]
    exact mul_le_mul' (hle x) le_rfl
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal M₀ * ∫⁻ x : Space, w2k r0 D A x) ?_ ?_
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (w2k_lintegral_ne_top hD A)
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono hsq

/-- `ltauLq` of the cut old source bounded by `eLpNorm g 2 (ageμ c (-1/2))`. -/
theorem w114_src_ltauLq_le {R c : ℝ} (r : ℝ) (hR : 0 < R) (hc : 0 < c)
    {g : Chart → Ten3} (hg : Measurable g) :
    IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c r g)) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * R ^ 2)) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
  have hsq := w10_src_sq R c r g hR hc hg
  have h1 := ENNReal.rpow_le_rpow hsq (show (0 : ℝ) ≤ 1 / 2 by positivity)
  have hL : (IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c r g)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      IIIa.ltauLq (2 * c / R) 2 (IIIa.srcNorm (oldCutSrc R c r g)) := by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hR' : (ENNReal.ofReal (Real.pi * R ^ 2) * ∫⁻ p, ‖g p‖ₑ ^ 2 ∂(ageμ c (-1 / 2))) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (Real.pi * R ^ 2)) * eLpNorm g 2 (ageμ c (-1 / 2)) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.sqrt_eq_rpow]
    congr 1
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
    simp
  rwa [hL, hR'] at h1

end UnforcedLeray.Short.PartIIIb.Concrete
end
