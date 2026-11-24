import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_2_4
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.InletProfileJets.RingStreamJets.Generic

/-!
# Part II-b, task `PartII-b:G4/5/2/2/4` (`ringStreamJetsFix`)

Source of record: `the November 2 reference manuscript`, lines 2360-2366 (the
normalized ring stream `(-φ_η, φ_q + R⁻¹(φ - 2sφ_s - ηφ_η))`), 2386-2387 (`W^{j,∞}` bound).

The profile `φ` is bounded with the transverse decay `E(m) = exp(-κ|η|/c')`. The `s`-factor
`2s φ_s` is handled by the Leibniz rule with the coordinate `2s`: `φ_s` vanishes near every point
with `|s| > S` (by `φ = 0` for `s > S` and the new clause for `s < -S`), so the factor is bounded by
`2S` on the rest. The `η`-factor uses `|η| E ≤ c'/κ`.
Constant: `C = 3(j+1)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb.RingJ

theorem addV_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g : ℝ × (ℝ × ℝ) → V) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖ := by
  have h : iteratedFDeriv ℝ l (f + g) x = iteratedFDeriv ℝ l f x + iteratedFDeriv ℝ l g x :=
    iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  show ‖iteratedFDeriv ℝ l (f + g) x‖ ≤ _
  rw [h]
  exact norm_add_le _ _

theorem subV_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f g : ℝ × (ℝ × ℝ) → V) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (l : ℕ)
    (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => f y - g y) x‖ ≤
      ‖iteratedFDeriv ℝ l f x‖ + ‖iteratedFDeriv ℝ l g x‖ := by
  have h : iteratedFDeriv ℝ l (f - g) x = iteratedFDeriv ℝ l f x - iteratedFDeriv ℝ l g x :=
    iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast le_top)).contDiffAt
      (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  show ‖iteratedFDeriv ℝ l (f - g) x‖ ≤ _
  rw [h]
  exact norm_sub_le _ _

theorem expLe_one (κ c' : ℝ) (hκ : 0 < κ) (hc : 0 < c') (η : ℝ) :
    Real.exp (-(κ * |η| / c')) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact neg_nonpos.mpr (div_nonneg (mul_nonneg hκ.le (abs_nonneg η)) hc.le)

theorem expBound (κ c' : ℝ) (hκ : 0 < κ) (hc : 0 < c') (η : ℝ) :
    |η| * Real.exp (-(κ * |η| / c')) ≤ c' / κ := by
  have hk : κ * |η| / c' = (κ / c') * |η| := by ring
  have hη : |η| = c' / κ * (κ * |η| / c') := by
    field_simp
  set t := κ * |η| / c' with ht
  have hk1 : t * Real.exp (-t) ≤ 1 := by
    have h1 : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    rw [Real.exp_neg]
    calc t * (Real.exp t)⁻¹ ≤ Real.exp t * (Real.exp t)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Real.exp_pos t).le)
      _ = 1 := mul_inv_cancel₀ (Real.exp_pos t).ne'
  have hc' : 0 ≤ c' / κ := div_nonneg hc.le hκ.le
  calc |η| * Real.exp (-t) = c' / κ * (t * Real.exp (-t)) := by rw [hη]; ring
    _ ≤ c' / κ * 1 := mul_le_mul_of_nonneg_left hk1 hc'
    _ = c' / κ := mul_one _

/-- Pointwise bound of a directional profile derivative with the transverse decay. -/
theorem dirE_bound (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (M κ c' : ℝ) (j : ℕ)
    (hder : ∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c')))
    (v : ℝ × (ℝ × ℝ)) (hv : ‖v‖ ≤ 1) (l : ℕ) (hl : l ≤ j) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => fderiv ℝ φ y v) x‖ ≤
      M * Real.exp (-(κ * |x.2.2| / c')) := by
  refine (dir_norm φ hφ v l x).trans ?_
  have h1 := hder (l + 1) (by omega) x
  calc ‖v‖ * ‖iteratedFDeriv ℝ (l + 1) φ x‖ ≤ 1 * (M * Real.exp (-(κ * |x.2.2| / c'))) :=
        mul_le_mul hv h1 (norm_nonneg _) zero_le_one
    _ = M * Real.exp (-(κ * |x.2.2| / c')) := one_mul _

theorem dir_le_M (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (M κ c' : ℝ) (hκ : 0 < κ)
    (hc : 0 < c') (hM : 0 ≤ M) (j : ℕ)
    (hder : ∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c')))
    (v : ℝ × (ℝ × ℝ)) (hv : ‖v‖ ≤ 1) (l : ℕ) (hl : l ≤ j) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => fderiv ℝ φ y v) x‖ ≤ M :=
  (dirE_bound φ hφ M κ c' j hder v hv l hl x).trans
    (mul_le_of_le_one_right hM (expLe_one κ c' hκ hc _))

theorem phi_le_M (φ : ℝ × (ℝ × ℝ) → ℝ) (M κ c' : ℝ) (hκ : 0 < κ) (hc : 0 < c') (hM : 0 ≤ M)
    (j : ℕ)
    (hder : ∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c')))
    (l : ℕ) (hl : l ≤ j) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l φ x‖ ≤ M :=
  (hder l (by omega) x).trans (mul_le_of_le_one_right hM (expLe_one κ c' hκ hc _))

theorem dS_zero_of_gt (φ : ℝ × (ℝ × ℝ) → ℝ) (S : ℝ)
    (hvan : ∀ x : ℝ × (ℝ × ℝ), S < x.1 → φ x = 0) (y : ℝ × (ℝ × ℝ)) (hy : S < y.1) :
    Axi.dS φ y = 0 := by
  have hev : φ =ᶠ[𝓝 y] (fun _ : ℝ × (ℝ × ℝ) => (0 : ℝ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hy] with z hz
    exact hvan z hz
  have h1 := hev.fderiv_eq (𝕜 := ℝ)
  unfold Axi.dS
  rw [h1]
  simp

theorem dC_cd (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (Axi.dS φ) ∧ ContDiff ℝ ∞ (Axi.dEta φ) ∧ ContDiff ℝ ∞ (Axi.dQ φ) :=
  ⟨dir_cd φ hφ (1, (0, 0)), dir_cd φ hφ (0, (0, 1)), dir_cd φ hφ (0, (1, 0))⟩

theorem norm_basis_s : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
  simp [Prod.norm_def]

theorem norm_basis_q : ‖((0 : ℝ), ((1 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
  simp [Prod.norm_def]

theorem norm_basis_e : ‖((0 : ℝ), ((0 : ℝ), (1 : ℝ)))‖ ≤ 1 := by
  simp [Prod.norm_def]

/-- The `s`-term `2 s φ_s`. -/
theorem s_term (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (S c' κ M : ℝ) (hS : 0 < S)
    (hc : 0 < c') (hκ : 0 < κ) (hM : 0 ≤ M) (j : ℕ)
    (hvan : ∀ x : ℝ × (ℝ × ℝ), S < x.1 → φ x = 0)
    (hfd : ∀ x : ℝ × (ℝ × ℝ), x.1 < -S → fderiv ℝ φ x (1, (0, 0)) = 0)
    (hder : ∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c')))
    (l : ℕ) (hl : l ≤ j) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => 2 * y.1 * Axi.dS φ y) x‖ ≤ 2 * (S + l) * M := by
  have hdS : ContDiff ℝ ∞ (Axi.dS φ) := (dC_cd φ hφ).1
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  have hnn : 0 ≤ 2 * (S + (l : ℝ)) * M := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hM
  by_cases h1 : S < x.1
  · have hz : ∀ᶠ y in 𝓝 x, 2 * y.1 * Axi.dS φ y = 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds h1] with y hy
      rw [dS_zero_of_gt φ S hvan y hy]
      simp
    rw [vanish_norm _ x hz l]
    exact hnn
  by_cases h2 : x.1 < -S
  · have hz : ∀ᶠ y in 𝓝 x, 2 * y.1 * Axi.dS φ y = 0 := by
      filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds h2] with y hy
      have hy0 : Axi.dS φ y = 0 := hfd y hy
      rw [hy0]
      simp
    rw [vanish_norm _ x hz l]
    exact hnn
  push Not at h1 h2
  set L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ) with hLdef
  have hLx : ∀ y : ℝ × (ℝ × ℝ), L y = 2 * y.1 := fun y => by
    simp [hLdef]
  have hLn : ‖L‖ ≤ 2 := by
    rw [hLdef]
    refine (norm_smul_le (2 : ℝ) (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))).trans ?_
    have h3 := ContinuousLinearMap.norm_fst_le ℝ ℝ (ℝ × ℝ)
    have h2n : ‖(2 : ℝ)‖ = 2 := by norm_num
    rw [h2n]
    nlinarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))]
  have e : (fun y : ℝ × (ℝ × ℝ) => 2 * y.1 * Axi.dS φ y) = fun y => L y * Axi.dS φ y := by
    funext y
    rw [hLx]
  rw [e]
  refine (coord_mul_norm L (Axi.dS φ) hdS l x).trans ?_
  have hLs : |L x| ≤ 2 * S := by
    rw [hLx, abs_mul, abs_two]
    have : |x.1| ≤ S := abs_le.2 ⟨by linarith, h1⟩
    linarith
  have hD0 : ‖iteratedFDeriv ℝ l (Axi.dS φ) x‖ ≤ M :=
    dir_le_M φ hφ M κ c' hκ hc hM j hder (1, (0, 0)) norm_basis_s l hl x
  have hD1 : ‖iteratedFDeriv ℝ (l - 1) (Axi.dS φ) x‖ ≤ M :=
    dir_le_M φ hφ M κ c' hκ hc hM j hder (1, (0, 0)) norm_basis_s (l - 1) (by omega) x
  have t1 : |L x| * ‖iteratedFDeriv ℝ l (Axi.dS φ) x‖ ≤ 2 * S * M :=
    mul_le_mul hLs hD0 (norm_nonneg _) (by linarith)
  have t2 : (l : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (l - 1) (Axi.dS φ) x‖ ≤ (l : ℝ) * (2 * M) := by
    have h := mul_le_mul hLn hD1 (norm_nonneg _) (by norm_num)
    calc (l : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (l - 1) (Axi.dS φ) x‖
        = (l : ℝ) * (‖L‖ * ‖iteratedFDeriv ℝ (l - 1) (Axi.dS φ) x‖) := by ring
      _ ≤ (l : ℝ) * (2 * M) := mul_le_mul_of_nonneg_left h hl0
  have e2 : 2 * (S + (l : ℝ)) * M = 2 * S * M + (l : ℝ) * (2 * M) := by ring
  rw [e2]
  linarith [t1, t2]

/-- The `η`-term `η φ_η`. -/
theorem eta_term (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (c' κ M : ℝ)
    (hc : 0 < c') (hκ : 0 < κ) (hM : 0 ≤ M) (j : ℕ)
    (hder : ∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c')))
    (l : ℕ) (hl : l ≤ j) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun y => y.2.2 * Axi.dEta φ y) x‖ ≤ (c' / κ + l) * M := by
  have hdE : ContDiff ℝ ∞ (Axi.dEta φ) := (dC_cd φ hφ).2.1
  have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
  set L : ℝ × (ℝ × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)) with hLdef
  have hLy : ∀ y : ℝ × (ℝ × ℝ), L y = y.2.2 := fun y => rfl
  have hLn : ‖L‖ ≤ 1 := by
    rw [hLdef]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    have h2 := ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ × ℝ)
    have h3 : ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ * ‖ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)‖ ≤ 1 * 1 :=
      mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    linarith
  have e : (fun y : ℝ × (ℝ × ℝ) => y.2.2 * Axi.dEta φ y) = fun y => L y * Axi.dEta φ y := rfl
  rw [e]
  refine (coord_mul_norm L (Axi.dEta φ) hdE l x).trans ?_
  have hD0 : ‖iteratedFDeriv ℝ l (Axi.dEta φ) x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c')) :=
    dirE_bound φ hφ M κ c' j hder (0, (0, 1)) norm_basis_e l hl x
  have hD1 : ‖iteratedFDeriv ℝ (l - 1) (Axi.dEta φ) x‖ ≤ M :=
    dir_le_M φ hφ M κ c' hκ hc hM j hder (0, (0, 1)) norm_basis_e (l - 1) (by omega) x
  have hEx := expBound κ c' hκ hc x.2.2
  have hLabs : |L x| = |x.2.2| := by rw [hLy]
  have t1 : |L x| * ‖iteratedFDeriv ℝ l (Axi.dEta φ) x‖ ≤ c' / κ * M := by
    calc |L x| * ‖iteratedFDeriv ℝ l (Axi.dEta φ) x‖
        ≤ |x.2.2| * (M * Real.exp (-(κ * |x.2.2| / c'))) :=
          mul_le_mul hLabs.le hD0 (norm_nonneg _) (abs_nonneg _)
      _ = M * (|x.2.2| * Real.exp (-(κ * |x.2.2| / c'))) := by ring
      _ ≤ M * (c' / κ) := mul_le_mul_of_nonneg_left hEx hM
      _ = c' / κ * M := by ring
  have t2 : (l : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (l - 1) (Axi.dEta φ) x‖ ≤ (l : ℝ) * M := by
    have h := mul_le_mul hLn hD1 (norm_nonneg _) zero_le_one
    calc (l : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ (l - 1) (Axi.dEta φ) x‖
        = (l : ℝ) * (‖L‖ * ‖iteratedFDeriv ℝ (l - 1) (Axi.dEta φ) x‖) := by ring
      _ ≤ (l : ℝ) * (1 * M) := mul_le_mul_of_nonneg_left h hl0
      _ = (l : ℝ) * M := by ring
  have e2 : (c' / κ + (l : ℝ)) * M = c' / κ * M + (l : ℝ) * M := by ring
  rw [e2]
  linarith [t1, t2]

theorem B_cd (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (R : ℝ) :
    ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) =>
      Axi.dQ φ m + R⁻¹ * (φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m)) := by
  obtain ⟨hdS, hdE, hdQ⟩ := dC_cd φ hφ
  have hc2 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => 2 * m.1 * Axi.dS φ m) :=
    (contDiff_const.mul contDiff_fst).mul hdS
  have hc3 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => m.2.2 * Axi.dEta φ m) :=
    (contDiff_snd.comp contDiff_snd).mul hdE
  have hc0 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) =>
      φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m) :=
    (hφ.sub hc2).sub hc3
  exact hdQ.add (contDiff_const.mul hc0)

theorem B_bound (φ : ℝ × (ℝ × ℝ) → ℝ) (hφ : ContDiff ℝ ∞ φ) (R S c' κ M : ℝ) (hR : 1 ≤ R)
    (hS : 0 < S) (hc : 0 < c') (hκ : 0 < κ) (hM : 0 ≤ M) (j : ℕ)
    (hvan : ∀ x : ℝ × (ℝ × ℝ), S < x.1 → φ x = 0)
    (hfd : ∀ x : ℝ × (ℝ × ℝ), x.1 < -S → fderiv ℝ φ x (1, (0, 0)) = 0)
    (hder : ∀ l ≤ j + 1, ∀ x : ℝ × (ℝ × ℝ),
      ‖iteratedFDeriv ℝ l φ x‖ ≤ M * Real.exp (-(κ * |x.2.2| / c')))
    (l : ℕ) (hl : l ≤ j) (x : ℝ × (ℝ × ℝ)) :
    ‖iteratedFDeriv ℝ l (fun m : ℝ × (ℝ × ℝ) =>
      Axi.dQ φ m + R⁻¹ * (φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m)) x‖ ≤
      M * (2 + 2 * S + 3 * l + c' / κ) := by
  obtain ⟨hdS, hdE, hdQ⟩ := dC_cd φ hφ
  have hc2 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => 2 * m.1 * Axi.dS φ m) :=
    (contDiff_const.mul contDiff_fst).mul hdS
  have hc3 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => m.2.2 * Axi.dEta φ m) :=
    (contDiff_snd.comp contDiff_snd).mul hdE
  have hc1 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) => φ m - 2 * m.1 * Axi.dS φ m) := hφ.sub hc2
  have hc0 : ContDiff ℝ ∞ (fun m : ℝ × (ℝ × ℝ) =>
      φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m) := hc1.sub hc3
  have hin1 : ‖iteratedFDeriv ℝ l (fun m : ℝ × (ℝ × ℝ) => φ m - 2 * m.1 * Axi.dS φ m) x‖ ≤
      M + 2 * (S + l) * M :=
    (subV_norm φ (fun m : ℝ × (ℝ × ℝ) => 2 * m.1 * Axi.dS φ m) hφ hc2 l x).trans
      (add_le_add (phi_le_M φ M κ c' hκ hc hM j hder l hl x)
        (s_term φ hφ S c' κ M hS hc hκ hM j hvan hfd hder l hl x))
  have hin : ‖iteratedFDeriv ℝ l (fun m : ℝ × (ℝ × ℝ) =>
      φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m) x‖ ≤
      M + 2 * (S + l) * M + (c' / κ + l) * M :=
    (subV_norm _ _ hc1 hc3 l x).trans
      (add_le_add hin1 (eta_term φ hφ c' κ M hc hκ hM j hder l hl x))
  have hR0 : 0 ≤ R⁻¹ := inv_nonneg.2 (by linarith)
  have hR1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hRn : ‖R⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hR0]
    exact hR1
  have hR' : ‖iteratedFDeriv ℝ l (fun m : ℝ × (ℝ × ℝ) =>
      R⁻¹ * (φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m)) x‖ ≤
      ‖iteratedFDeriv ℝ l (fun m : ℝ × (ℝ × ℝ) =>
      φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m) x‖ := by
    refine (const_mul_norm R⁻¹ _ hc0 l x).trans ?_
    have h1 : |R⁻¹| ≤ 1 := by
      rw [← Real.norm_eq_abs]
      exact hRn
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  have hdQb : ‖iteratedFDeriv ℝ l (Axi.dQ φ) x‖ ≤ M :=
    dir_le_M φ hφ M κ c' hκ hc hM j hder (0, (1, 0)) norm_basis_q l hl x
  refine (addV_norm (Axi.dQ φ) (fun m : ℝ × (ℝ × ℝ) =>
      R⁻¹ * (φ m - 2 * m.1 * Axi.dS φ m - m.2.2 * Axi.dEta φ m)) hdQ
      (contDiff_const.mul hc0) l x).trans ?_
  have e : M * (2 + 2 * S + 3 * l + c' / κ) = M + (M + 2 * (S + l) * M + (c' / κ + l) * M) := by
    ring
  rw [e]
  linarith [hdQb, hR', hin]

end UnforcedLeray.Short.IIb.RingJ

namespace UnforcedLeray.Short.IIb

open RingJ

theorem ringStreamJetsFix : UnforcedLeray.Short.IIb.RingStreamJetsFix := by
  intro j
  refine ⟨3 * ((j : ℝ) + 1), by positivity, ?_⟩
  intro R S c' κ M φ hR hS hc hκ hM hφ hvan hfd hder l hl m
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hl' : (l : ℝ) ≤ j := by exact_mod_cast hl
  have hK : 0 ≤ c' / κ := div_nonneg hc.le hκ.le
  have hm0 : ‖Axi.m0‖ = 1 := by
    unfold Axi.m0
    simp
  have hm1 : ‖Axi.m1‖ = 1 := by
    unfold Axi.m1
    simp
  have hAcd : ContDiff ℝ ∞ (fun y => -(Axi.dEta φ y)) := ((dC_cd φ hφ).2.1).neg
  have hBcd := B_cd φ hφ R
  show ‖iteratedFDeriv ℝ l (fun y =>
      (-(Axi.dEta φ y)) • Axi.m0 +
        (Axi.dQ φ y + R⁻¹ * (φ y - 2 * y.1 * Axi.dS φ y - y.2.2 * Axi.dEta φ y)) • Axi.m1) m‖ ≤
      3 * ((j : ℝ) + 1) * (1 + S) * (1 + c' / κ) * M
  have hXcd : ContDiff ℝ ∞ (fun y => (-(Axi.dEta φ y)) • Axi.m0) :=
    hAcd.smul contDiff_const
  have hYcd : ContDiff ℝ ∞ (fun y =>
      (Axi.dQ φ y + R⁻¹ * (φ y - 2 * y.1 * Axi.dS φ y - y.2.2 * Axi.dEta φ y)) • Axi.m1) :=
    hBcd.smul contDiff_const
  have hX : ‖iteratedFDeriv ℝ l (fun y => (-(Axi.dEta φ y)) • Axi.m0) m‖ ≤
      ‖iteratedFDeriv ℝ l (fun y => -(Axi.dEta φ y)) m‖ := by
    have h := smulVec_norm (fun y => -(Axi.dEta φ y)) hAcd Axi.m0 l m
    rw [hm0, one_mul] at h
    exact h
  have hY : ‖iteratedFDeriv ℝ l (fun y =>
      (Axi.dQ φ y + R⁻¹ * (φ y - 2 * y.1 * Axi.dS φ y - y.2.2 * Axi.dEta φ y)) • Axi.m1) m‖ ≤
      ‖iteratedFDeriv ℝ l (fun y =>
      Axi.dQ φ y + R⁻¹ * (φ y - 2 * y.1 * Axi.dS φ y - y.2.2 * Axi.dEta φ y)) m‖ := by
    have h := smulVec_norm (fun y =>
      Axi.dQ φ y + R⁻¹ * (φ y - 2 * y.1 * Axi.dS φ y - y.2.2 * Axi.dEta φ y)) hBcd Axi.m1 l m
    rw [hm1, one_mul] at h
    exact h
  have hA : ‖iteratedFDeriv ℝ l (fun y => -(Axi.dEta φ y)) m‖ ≤ M := by
    have e : (fun y => -(Axi.dEta φ y)) = -(Axi.dEta φ) := rfl
    rw [e, iteratedFDeriv_neg_apply, norm_neg]
    exact dir_le_M φ hφ M κ c' hκ hc hM j hder (0, (0, 1)) norm_basis_e l hl m
  have hB := B_bound φ hφ R S c' κ M hR hS hc hκ hM j hvan hfd hder l hl m
  have hsplit := addV_norm (fun y => (-(Axi.dEta φ y)) • Axi.m0) (fun y =>
      (Axi.dQ φ y + R⁻¹ * (φ y - 2 * y.1 * Axi.dS φ y - y.2.2 * Axi.dEta φ y)) • Axi.m1)
      hXcd hYcd l m
  have hpoly : 3 + 2 * S + 3 * (l : ℝ) + c' / κ ≤ 3 * ((j : ℝ) + 1) * (1 + S) * (1 + c' / κ) := by
    nlinarith [mul_nonneg hS.le hK, mul_nonneg hj0 hS.le, mul_nonneg hj0 hK,
      mul_nonneg (mul_nonneg hj0 hS.le) hK]
  have hfin : M + M * (2 + 2 * S + 3 * l + c' / κ) ≤
      3 * ((j : ℝ) + 1) * (1 + S) * (1 + c' / κ) * M := by
    have e : M + M * (2 + 2 * S + 3 * l + c' / κ) = M * (3 + 2 * S + 3 * l + c' / κ) := by ring
    have e2 : 3 * ((j : ℝ) + 1) * (1 + S) * (1 + c' / κ) * M =
        M * (3 * ((j : ℝ) + 1) * (1 + S) * (1 + c' / κ)) := by ring
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left hpoly hM
  have hbig := hsplit.trans (add_le_add hX (le_refl _))
  linarith [hsplit, hX, hY, hA, hB, hfin]

end UnforcedLeray.Short.IIb
