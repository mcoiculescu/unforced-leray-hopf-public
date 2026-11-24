import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G4Org

/-!
# `PartIII-b:IIIb-D3/2/G4/2`: pointwise bound on the vorticity source `g_B`

Source 4605-4608: `g_B = -1/2(d-ie)H - 1/2(d+ie)conj H - beta R`, with `|d|,|e|,|beta| <= |B|`
(entrywise `l^1` norm `matNorm`), and the bounded sources `‖H‖, ‖conj H‖, ‖R‖ <= C` on `[0,T]`.
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4

open ConcreteYF

lemma matNorm_entry_le (B : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    |B i j| ≤ UnforcedLeray.Short.PartIIIb.matNorm B := by
  unfold UnforcedLeray.Short.PartIIIb.matNorm
  have h1 : |B i j| ≤ ∑ j', |B i j'| :=
    Finset.single_le_sum (f := fun j' => |B i j'|) (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', |B i j'| ≤ ∑ i', ∑ j', |B i' j'| :=
    Finset.single_le_sum (f := fun i' => ∑ j', |B i' j'|)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
  linarith

lemma coef_minus_le (x y m : ℝ) (hx : |x| ≤ m) (hy : |y| ≤ m) :
    ‖(-(1 / 2 : ℂ)) * (((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ))‖ ≤ m := by
  have hc : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by norm_num
  have hn : ‖((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)‖ ≤ |x| + |y| := by
    calc ‖((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ)‖
        ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * ((y : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = |x| + |y| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  rw [norm_mul, hc]
  have hxy : |x| + |y| ≤ 2 * m := by linarith
  nlinarith [norm_nonneg (((x : ℝ) : ℂ) - Complex.I * ((y : ℝ) : ℂ))]

lemma coef_plus_le (x y m : ℝ) (hx : |x| ≤ m) (hy : |y| ≤ m) :
    ‖(-(1 / 2 : ℂ)) * (((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ))‖ ≤ m := by
  have hc : ‖(-(1 / 2 : ℂ))‖ = 1 / 2 := by norm_num
  have hn : ‖((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)‖ ≤ |x| + |y| := by
    calc ‖((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ)‖
        ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * ((y : ℝ) : ℂ)‖ := norm_add_le _ _
      _ = |x| + |y| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  rw [norm_mul, hc]
  have hxy : |x| + |y| ≤ 2 * m := by linarith
  nlinarith [norm_nonneg (((x : ℝ) : ℂ) + Complex.I * ((y : ℝ) : ℂ))]

theorem gBPointwise (S : FlatSetting) (T C : ℝ) (hC : ∀ t ∈ Set.Icc (0:ℝ) T, ‖S.Hper t‖ ≤ C ∧ ‖S.conjX (S.Hper t)‖ ≤ C ∧ ‖S.Rper t‖ ≤ C) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) T) : ‖S.gB B t‖ ≤ 3 * C * matNorm (B t) := by
  obtain ⟨h1, h2, h3⟩ := hC t ht
  set m := matNorm (B t) with hm_def
  have hm0 : 0 ≤ m := by
    rw [hm_def]; unfold UnforcedLeray.Short.PartIIIb.matNorm
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) h1
  have e00 := abs_le.mp (matNorm_entry_le (B t) 0 0)
  have e22 := abs_le.mp (matNorm_entry_le (B t) 2 2)
  have e02 := abs_le.mp (matNorm_entry_le (B t) 0 2)
  have e20 := abs_le.mp (matNorm_entry_le (B t) 2 0)
  have hd : |UnforcedLeray.Short.PartIIIb.Bd (B t)| ≤ m := by
    rw [abs_le]; unfold UnforcedLeray.Short.PartIIIb.Bd
    constructor <;> linarith [e00.1, e00.2, e22.1, e22.2]
  have he : |UnforcedLeray.Short.PartIIIb.Be (B t)| ≤ m := by
    rw [abs_le]; unfold UnforcedLeray.Short.PartIIIb.Be
    constructor <;> linarith [e02.1, e02.2, e20.1, e20.2]
  have hb : |Bbeta (B t)| ≤ m := by
    rw [abs_le]; unfold Bbeta
    constructor <;> linarith [e00.1, e00.2, e22.1, e22.2]
  have ha := coef_minus_le _ _ m hd he
  have hb' := coef_plus_le _ _ m hd he
  have hR : ‖((Bbeta (B t) : ℝ) : ℂ)‖ ≤ m := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hb
  unfold FlatSetting.gB
  have t1 : ‖(-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ)
        - Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ))) • S.Hper t‖ ≤ m * C := by
    rw [norm_smul]
    exact mul_le_mul ha h1 (norm_nonneg _) hm0
  have t2 : ‖(-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ)
        + Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ))) • S.conjX (S.Hper t)‖ ≤ m * C := by
    rw [norm_smul]
    exact mul_le_mul hb' h2 (norm_nonneg _) hm0
  have t3 : ‖((Bbeta (B t) : ℝ) : ℂ) • S.Rper t‖ ≤ m * C := by
    rw [norm_smul]
    exact mul_le_mul hR h3 (norm_nonneg _) hm0
  calc _ ≤ ‖(-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ)
        - Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ))) • S.Hper t‖
        + ‖(-(1 / 2 : ℂ) * (((UnforcedLeray.Short.PartIIIb.Bd (B t) : ℝ) : ℂ)
        + Complex.I * ((UnforcedLeray.Short.PartIIIb.Be (B t) : ℝ) : ℂ))) • S.conjX (S.Hper t)‖
        + ‖((Bbeta (B t) : ℝ) : ℂ) • S.Rper t‖ := by
          refine le_trans (norm_sub_le _ _) ?_
          gcongr
          exact norm_add_le _ _
    _ ≤ m * C + m * C + m * C := by linarith
    _ = 3 * C * m := by ring

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G4
