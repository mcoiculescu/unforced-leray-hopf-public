import UnforcedLeray.Short.PartIIa.Sub.N02_4_7_B
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Commute
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Decay
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.Band
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.IntegrableWeight
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.NonzeroMode.ModeBounds.WeightedEnergy

/-!
# Part II-a, task `PartII-a:N02/4/7/8`: the `j = 0` moment bound `NzmbJ0`

Source: `the November 2 reference manuscript`, lines 1722-1727.
Energy identity `nzmbWeightedEnergy` applied to `(S^α φ, S^α ψ)` with data `(S^α a, S^α b)`,
then the moment bookkeeping (`√` of integrals, `√(x+y) ≤ √x + √y`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

/-! ### Support and vanishing lemmas -/

theorem j0_S_band (g : ℝ × ℝ → ℂ) (s0 s1 : ℝ) (h : ∀ x, g x ≠ 0 → x.1 ∈ Icc s0 s1) :
    ∀ x, nzS2 g x ≠ 0 → x.1 ∈ Icc s0 s1 := by
  intro x hx
  by_contra h1
  apply hx
  refine nzS2_eq_zero_of_open_zero g {y : ℝ × ℝ | y.1 ∉ Icc s0 s1}
    ((isClosed_Icc.isOpen_compl).preimage continuous_fst) ?_ x h1
  intro y hy
  by_contra hgy
  exact hy (h y hgy)

theorem j0_iter_band (g : ℝ × ℝ → ℂ) (s0 s1 : ℝ) (h : ∀ x, g x ≠ 0 → x.1 ∈ Icc s0 s1)
    (n : ℕ) : ∀ x, (nzS2^[n] g) x ≠ 0 → x.1 ∈ Icc s0 s1 := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact j0_S_band _ s0 s1 ih

theorem j0_fderiv_zero (g : ℝ × ℝ → ℂ) (s0 s1 : ℝ) (h : ∀ x, g x ≠ 0 → x.1 ∈ Icc s0 s1)
    (x : ℝ × ℝ) (hx : x.1 ∉ Icc s0 s1) : fderiv ℝ g x = 0 := by
  have hU : IsOpen {y : ℝ × ℝ | y.1 ∉ Icc s0 s1} :=
    (isClosed_Icc.isOpen_compl).preimage continuous_fst
  have hxU : x ∈ {y : ℝ × ℝ | y.1 ∉ Icc s0 s1} := hx
  have hev : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) :=
    Filter.eventually_of_mem (hU.mem_nhds hxU) (fun y hy => by
      by_contra hgy
      exact hy (h y hgy))
  rw [hev.fderiv_eq]
  simp

theorem j0_deriv_band (g : ℝ × ℝ → ℂ) (s0 s1 : ℝ) (h : ∀ x, g x ≠ 0 → x.1 ∈ Icc s0 s1) :
    ∀ x, fderiv ℝ g x (0, 1) ≠ 0 → x.1 ∈ Icc s0 s1 := by
  intro x hx
  by_contra h1
  apply hx
  rw [j0_fderiv_zero g s0 s1 h x h1]
  simp

theorem j0_weaken {g : ℝ × ℝ → ℂ} {a b a' b' : ℝ} (h : ∀ x, g x ≠ 0 → x.1 ∈ Icc a b)
    (ha : a' ≤ a) (hb : b ≤ b') : ∀ x, g x ≠ 0 → x.1 ∈ Icc a' b' :=
  fun x hx => ⟨le_trans ha (h x hx).1, le_trans (h x hx).2 hb⟩

theorem j0_abs_le_Icc {s0 s1 t : ℝ} (ht : t ∈ Icc s0 s1) : |t| ≤ |s0| + |s1| :=
  abs_le.mpr ⟨by linarith [ht.1, neg_abs_le s0, abs_nonneg s1],
    by linarith [ht.2, le_abs_self s1, abs_nonneg s0]⟩

theorem j0_iter_NzBand2 (n : ℕ) : ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g → NzBand2 g →
    NzBand2 (nzS2^[n] g) := by
  have hNB : NzmbBand := nzmbBand
  induction n with
  | zero => intro g _ hg; simpa using hg
  | succ n ih =>
    intro g hg hB
    rw [Function.iterate_succ_apply']
    exact hNB.1 _ (nzmb_iter_contDiff n g hg) (ih g hg hB)

/-! ### Decay lemmas -/

theorem j0_decay_S (φ : ℝ × ℝ → ℂ) (hφ : NzDecay2 φ) (s0 s1 : ℝ)
    (hb : ∀ x, φ x ≠ 0 → x.1 ∈ Icc s0 s1) (α : ℕ) (hα : α < 2) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖nzS2^[α] φ x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ (nzS2^[α] φ) x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|) := by
  obtain ⟨κ, C, hκ, hd⟩ := nzmb_decay_norms φ hφ
  have hsm : ContDiff ℝ ∞ φ := hφ.1
  have h01 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := (nzmb_norm_one_le_prod).2
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg (fderiv ℝ φ 0)).trans (hd 0).2.1
    simpa using h
  interval_cases α
  · refine ⟨κ, C, hκ, fun x => ⟨?_, ?_⟩⟩
    · simpa using (hd x).1
    · simp only [Function.iterate_zero, id_eq]
      exact ((fderiv ℝ φ x).le_opNorm _).trans
        ((mul_le_of_le_one_right (norm_nonneg _) h01).trans (hd x).2.1)
  · have hD : 0 ≤ |s0| + |s1| := by positivity
    have hDC : 0 ≤ (|s0| + |s1|) * C := mul_nonneg hD hC0
    refine ⟨κ, (|s0| + |s1|) * C, hκ, fun x => ⟨?_, ?_⟩⟩
    · simp only [Function.iterate_one]
      by_cases hx : x.1 ∈ Icc s0 s1
      · have hCe : 0 ≤ C * Real.exp (-κ * |x.2|) :=
          (norm_nonneg (fderiv ℝ φ x)).trans (hd x).2.1
        calc ‖nzS2 φ x‖ ≤ |x.1| * (C * Real.exp (-κ * |x.2|)) :=
              nzmb_norm_nzS2_le φ x _ (hd x).2.1
          _ ≤ (|s0| + |s1|) * (C * Real.exp (-κ * |x.2|)) :=
              mul_le_mul_of_nonneg_right (j0_abs_le_Icc hx) hCe
          _ = (|s0| + |s1|) * C * Real.exp (-κ * |x.2|) := by ring
      · have h0 : nzS2 φ x = 0 := by
          by_contra hne
          exact hx (j0_S_band φ s0 s1 hb x hne)
        rw [h0, norm_zero]
        exact mul_nonneg hDC (Real.exp_pos _).le
    · simp only [Function.iterate_one]
      by_cases hx : x.1 ∈ Icc s0 s1
      · have hCe : 0 ≤ C * Real.exp (-κ * |x.2|) :=
          (norm_nonneg (fderiv ℝ φ x)).trans (hd x).2.1
        calc ‖fderiv ℝ (nzS2 φ) x (0, 1)‖ ≤ |x.1| * (C * Real.exp (-κ * |x.2|)) :=
              nzmb_norm_fderiv_snd_nzS2_le φ hsm x _ (hd x).2.2
          _ ≤ (|s0| + |s1|) * (C * Real.exp (-κ * |x.2|)) :=
              mul_le_mul_of_nonneg_right (j0_abs_le_Icc hx) hCe
          _ = (|s0| + |s1|) * C * Real.exp (-κ * |x.2|) := by ring
      · rw [j0_fderiv_zero (nzS2 φ) s0 s1 (j0_S_band φ s0 s1 hb) x hx]
        simp only [zero_apply, norm_zero]
        exact mul_nonneg hDC (Real.exp_pos _).le

theorem j0_pair (G1 G2 : ℝ × ℝ → ℂ) (κ1 C1 κ2 C2 : ℝ) (hκ1 : 0 < κ1) (hκ2 : 0 < κ2)
    (h1 : ∀ x : ℝ × ℝ, ‖G1 x‖ ≤ C1 * Real.exp (-κ1 * |x.2|) ∧
      ‖fderiv ℝ G1 x (0, 1)‖ ≤ C1 * Real.exp (-κ1 * |x.2|))
    (h2 : ∀ x : ℝ × ℝ, ‖G2 x‖ ≤ C2 * Real.exp (-κ2 * |x.2|) ∧
      ‖fderiv ℝ G2 x (0, 1)‖ ≤ C2 * Real.exp (-κ2 * |x.2|)) :
    ∃ κ C : ℝ, 0 < κ ∧ ∀ x : ℝ × ℝ,
      ‖G1 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ G1 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖G2 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ G2 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|) := by
  have hD1 : |C1| ≤ |C1| + |C2| := le_add_of_nonneg_right (abs_nonneg C2)
  have hD2 : |C2| ≤ |C1| + |C2| := le_add_of_nonneg_left (abs_nonneg C1)
  refine ⟨min κ1 κ2, |C1| + |C2|, lt_min hκ1 hκ2, fun x => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact nzmb_upgrade (min_le_left _ _) hD1 (h1 x).1
  · exact nzmb_upgrade (min_le_left _ _) hD1 (h1 x).2
  · exact nzmb_upgrade (min_le_right _ _) hD2 (h2 x).1
  · exact nzmb_upgrade (min_le_right _ _) hD2 (h2 x).2

theorem j0_data_decay (A : ℝ × ℝ → ℂ) (hA : ContDiff ℝ ∞ A) (hB : NzBand2 A) :
    ∃ s0 s1 κ C : ℝ, 0 < s0 ∧ 0 < κ ∧ (∀ x, A x ≠ 0 → x.1 ∈ Icc s0 s1) ∧
      ∀ x, ‖A x‖ ≤ C * Real.exp (-κ * |x.2|) := by
  obtain ⟨s0, s1, L, hs0, hsupp⟩ := hB
  have hK : IsCompact (Icc s0 s1 ×ˢ Icc (-L) L) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hA.continuous.continuousOn
  refine ⟨s0, s1, 1, max M 0 * Real.exp L, hs0, one_pos, fun x hx => (hsupp x hx).1, fun x => ?_⟩
  by_cases hxK : x ∈ Icc s0 s1 ×ˢ Icc (-L) L
  · have hxL : |x.2| ≤ L := abs_le.mpr ⟨hxK.2.1, hxK.2.2⟩
    have hex : 1 ≤ Real.exp L * Real.exp (-1 * |x.2|) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖A x‖ ≤ M := hM x hxK
      _ ≤ max M 0 := le_max_left _ _
      _ = max M 0 * 1 := (mul_one _).symm
      _ ≤ max M 0 * (Real.exp L * Real.exp (-1 * |x.2|)) :=
          mul_le_mul_of_nonneg_left hex (le_max_right _ _)
      _ = max M 0 * Real.exp L * Real.exp (-1 * |x.2|) := by ring
  · have h0 : A x = 0 := by
      by_contra hne
      exact hxK ⟨(hsupp x hne).1, abs_le.mp (hsupp x hne).2⟩
    rw [h0, norm_zero]
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (Real.exp_pos _).le) (Real.exp_pos _).le

/-! ### Integrability and nonnegativity -/

theorem j0_int (g : ℝ × ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (s0 s1 κ C : ℝ) (hs0 : 0 < s0)
    (hκ : 0 < κ) (hsupp : ∀ x, g x ≠ 0 → x.1 ∈ Icc s0 s1)
    (hdec : ∀ x, ‖g x‖ ≤ C * Real.exp (-κ * |x.2|)) :
    Integrable (fun x : ℝ × ℝ => ‖g x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) := by
  have h := nzmbIntegrableWeight g hg s0 s1 κ C hs0 hκ hsupp hdec 0
  refine h.congr (ae_of_all _ fun x => ?_)
  simp

theorem j0_int_nonneg (f : ℝ × ℝ → ℂ) :
    0 ≤ ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖f x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
  apply setIntegral_nonneg (measurableSet_Ioi.prod MeasurableSet.univ)
  intro x hx
  have h1 : 0 < x.1 := hx.1
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg h1.le _)

theorem j0_pt (a1 a2 a3 a4 w : ℝ) (h1 : 0 ≤ a1) (h2 : 0 ≤ a2) (h3 : 0 ≤ a3) (h4 : 0 ≤ a4)
    (hw : 0 ≤ w) :
    a1 * w ≤ (a1 + a2 + a3 + a4) * w ∧ a2 * w ≤ (a1 + a2 + a3 + a4) * w ∧
      a3 * w ≤ (a1 + a2 + a3 + a4) * w ∧ a4 * w ≤ (a1 + a2 + a3 + a4) * w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right (by linarith) hw
  · exact mul_le_mul_of_nonneg_right (by linarith) hw
  · exact mul_le_mul_of_nonneg_right (by linarith) hw
  · exact mul_le_mul_of_nonneg_right (by linarith) hw

/-! ### Iterates of `S` and constants -/

theorem j0_iter_fderiv_fun (α : ℕ) (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    nzS2^[α] (fun x => fderiv ℝ φ x (0, 1)) = fun x => fderiv ℝ (nzS2^[α] φ) x (0, 1) :=
  funext fun x => (nzmb_iter_fderiv α φ hφ x).symm

theorem j0_iter_const (c : ℂ) (n : ℕ) : ∀ g : ℝ × ℝ → ℂ, ContDiff ℝ ∞ g →
    nzS2^[n] (fun x => c * g x) = fun x => c * (nzS2^[n] g) x := by
  induction n with
  | zero => intro g _; rfl
  | succ n ih =>
    intro g hg
    rw [Function.iterate_succ_apply', ih g hg, Function.iterate_succ_apply']
    funext x
    exact nzmb_nzS2_const_mul c (nzS2^[n] g) (nzmb_iter_contDiff n g hg) x

/-! ### Moment bookkeeping -/

theorem j0_mom0 (α : ℕ) (g : ℝ × ℝ → ℂ) :
    nzMom2 0 α g = Real.sqrt (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
      ‖(nzS2^[α] g) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) := by
  unfold nzMom2
  rw [Real.sqrt_eq_rpow]
  simp

theorem j0_mom0_const (k : ℝ) (α : ℕ) (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) :
    nzMom2 0 α (fun x => (k : ℂ) * φ x) = Real.sqrt (k ^ 2 *
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖(nzS2^[α] φ) x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) := by
  rw [j0_mom0, j0_iter_const (k : ℂ) α φ hφ]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem j0_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

theorem j0_sqrt_le (X IA IB : ℝ) (_hX : 0 ≤ X) (hIA : 0 ≤ IA) (hIB : 0 ≤ IB)
    (h : X ≤ IA + IB) : Real.sqrt X ≤ Real.sqrt IA + Real.sqrt IB :=
  (Real.sqrt_le_sqrt h).trans (j0_sqrt_add_le IA IB hIA hIB)

theorem j0_sqrt_bound (k X IA IB : ℝ) (hX : 0 ≤ X) (hIA : 0 ≤ IA) (hIB : 0 ≤ IB)
    (h : X ≤ IA + IB) : Real.sqrt X ≤ (1 + |k|⁻¹) * (Real.sqrt IA + Real.sqrt IB) := by
  have hv : 0 ≤ Real.sqrt IA + Real.sqrt IB := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine (j0_sqrt_le X IA IB hX hIA hIB h).trans ?_
  have : 0 ≤ |k|⁻¹ := inv_nonneg.mpr (abs_nonneg k)
  nlinarith

theorem j0_real (k X IA IB : ℝ) (hk : k ≠ 0) (hX : 0 ≤ X) (hIA : 0 ≤ IA) (hIB : 0 ≤ IB)
    (h : k ^ 2 * X ≤ IA + IB) : Real.sqrt X ≤ (1 + |k|⁻¹) * (Real.sqrt IA + Real.sqrt IB) := by
  have hk0 : 0 < |k| := abs_pos.mpr hk
  have hv : 0 ≤ Real.sqrt IA + Real.sqrt IB := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have e1 : (Real.sqrt X * |k|) ^ 2 = k ^ 2 * X := by
    rw [mul_pow, Real.sq_sqrt hX, sq_abs]
    ring
  have hsq : (Real.sqrt X * |k|) ^ 2 ≤ (Real.sqrt IA + Real.sqrt IB) ^ 2 := by
    rw [e1]
    nlinarith [Real.sq_sqrt hIA, Real.sq_sqrt hIB, mul_nonneg (Real.sqrt_nonneg IA) (Real.sqrt_nonneg IB)]
  have h1 : Real.sqrt X * |k| ≤ Real.sqrt IA + Real.sqrt IB :=
    (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hk0.le) hv).mp hsq
  have h2 : Real.sqrt X = (Real.sqrt X * |k|) * |k|⁻¹ := by
    rw [mul_assoc, mul_inv_cancel₀ hk0.ne', mul_one]
  have hinv : 0 ≤ |k|⁻¹ := inv_nonneg.mpr hk0.le
  calc Real.sqrt X = (Real.sqrt X * |k|) * |k|⁻¹ := h2
    _ ≤ (Real.sqrt IA + Real.sqrt IB) * |k|⁻¹ := mul_le_mul_of_nonneg_right h1 hinv
    _ ≤ (1 + |k|⁻¹) * (Real.sqrt IA + Real.sqrt IB) := by nlinarith

/-! ### Core energy step -/

theorem j0_core (k : ℝ) (A B G1 G2 : ℝ × ℝ → ℂ)
    (hG1 : ContDiff ℝ ∞ G1) (hG2 : ContDiff ℝ ∞ G2) (hAB : NzModeEq k A B G1 G2)
    (s0 s1 κ C : ℝ) (hs0 : 0 < s0) (hκ : 0 < κ)
    (hb1 : ∀ x, G1 x ≠ 0 → x.1 ∈ Icc s0 s1) (hb2 : ∀ x, G2 x ≠ 0 → x.1 ∈ Icc s0 s1)
    (hdec : ∀ x : ℝ × ℝ, ‖G1 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ G1 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖G2 x‖ ≤ C * Real.exp (-κ * |x.2|) ∧
      ‖fderiv ℝ G2 x (0, 1)‖ ≤ C * Real.exp (-κ * |x.2|))
    (hA : Integrable (fun x : ℝ × ℝ => ‖A x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)))
    (hB : Integrable (fun x : ℝ × ℝ => ‖B x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ))) :
    k ^ 2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖A x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
          (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖B x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ∧
    (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖A x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
          (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖B x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ∧
    k ^ 2 * (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖A x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
          (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖B x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ∧
    (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G2 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) ≤
        (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖A x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
          (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖B x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) := by
  have hEn := nzmbWeightedEnergy k A B G1 G2 hG1 hG2 hAB
    ⟨s0, s1, hs0, fun x hx => hx.elim (hb1 x) (hb2 x)⟩ ⟨κ, C, hκ, hdec⟩
  have i1 : Integrable (fun x : ℝ × ℝ => ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int G1 hG1 s0 s1 κ C hs0 hκ hb1 (fun x => (hdec x).1)
  have i2 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int (fun x => fderiv ℝ G1 x (0, 1)) (nzmb_contDiff_snd G1 hG1 (0, 1)) s0 s1 κ C hs0 hκ
      (j0_deriv_band G1 s0 s1 hb1) (fun x => (hdec x).2.1)
  have i3 : Integrable (fun x : ℝ × ℝ => ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int G2 hG2 s0 s1 κ C hs0 hκ hb2 (fun x => (hdec x).2.2.1)
  have i4 : Integrable (fun x : ℝ × ℝ => ‖fderiv ℝ G2 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) :=
    j0_int (fun x => fderiv ℝ G2 x (0, 1)) (nzmb_contDiff_snd G2 hG2 (0, 1)) s0 s1 κ C hs0 hκ
      (j0_deriv_band G2 s0 s1 hb2) (fun x => (hdec x).2.2.2)
  have iF : Integrable (fun x : ℝ × ℝ => (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
      k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) := by
    have e := (((i1.const_mul (k ^ 2)).add i2).add (i3.const_mul (k ^ 2))).add i4
    refine e.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hw : ∀ᵐ x ∂(volume.restrict (Ioi 0 ×ˢ univ) : Measure (ℝ × ℝ)), 0 < x.1 := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with x hx
    exact hx.1
  have hR : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (‖A x‖ ^ 2 + ‖B x‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) =
      (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖A x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) +
        (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖B x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) := by
    rw [← integral_add hA hB]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  -- pointwise comparison with the energy integrand
  have E1' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).1
  have E2' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).2.1
  have E3' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).2.2.1
  have E4' : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖fderiv ℝ G2 x (0, 1)‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) ≤
      ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, (k ^ 2 * ‖G1 x‖ ^ 2 + ‖fderiv ℝ G1 x (0, 1)‖ ^ 2 +
        k ^ 2 * ‖G2 x‖ ^ 2 + ‖fderiv ℝ G2 x (0, 1)‖ ^ 2) * x.1 ^ (-(3 / 2 : ℝ)) := by
    refine integral_mono_of_nonneg ?_ iF ?_
    · filter_upwards [hw] with x hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.le _)
    · filter_upwards [hw] with x hx
      exact (j0_pt (k ^ 2 * ‖G1 x‖ ^ 2) (‖fderiv ℝ G1 x (0, 1)‖ ^ 2) (k ^ 2 * ‖G2 x‖ ^ 2)
        (‖fderiv ℝ G2 x (0, 1)‖ ^ 2) (x.1 ^ (-(3 / 2 : ℝ)))
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (mul_nonneg (sq_nonneg k) (sq_nonneg _)) (sq_nonneg _)
        (Real.rpow_nonneg hx.le _)).2.2.2
  -- pull out the constant `k^2`
  have q1 : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) =
      k ^ 2 * ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G1 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have q3 : ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, k ^ 2 * ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) =
      k ^ 2 * ∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖G2 x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← q1]; linarith
  · linarith
  · rw [← q3]; linarith
  · linarith

/-! ### Main theorem -/

theorem nzmbJ0 : UnforcedLeray.Short.PartIIa.NzmbJ0 := by
  intro k hk a b φ ψ ha hb hBa hBb hφ hψ hE α hα g hg
  have hα2 : α < 2 := Finset.mem_range.mp hα
  have hφs : ContDiff ℝ ∞ φ := hφ.1
  have hψs : ContDiff ℝ ∞ ψ := hψ.1
  have hAB := nzmb_modeEq_iter k α a b φ ψ ha hb hφs hψs hE
  obtain ⟨s0φ, s1φ, hs0φ, hbφ⟩ := hφ.2.1
  obtain ⟨s0ψ, s1ψ, hs0ψ, hbψ⟩ := hψ.2.1
  obtain ⟨s0, s1, hs0, hb1, hb2⟩ : ∃ s0 s1 : ℝ, 0 < s0 ∧ (∀ x, φ x ≠ 0 → x.1 ∈ Icc s0 s1) ∧
      (∀ x, ψ x ≠ 0 → x.1 ∈ Icc s0 s1) :=
    ⟨min s0φ s0ψ, max s1φ s1ψ, lt_min hs0φ hs0ψ,
      j0_weaken hbφ (min_le_left _ _) (le_max_left _ _),
      j0_weaken hbψ (min_le_right _ _) (le_max_right _ _)⟩
  obtain ⟨κ1, C1, hκ1, hd1⟩ := j0_decay_S φ hφ s0 s1 hb1 α hα2
  obtain ⟨κ2, C2, hκ2, hd2⟩ := j0_decay_S ψ hψ s0 s1 hb2 α hα2
  obtain ⟨κ, C, hκ, hdec⟩ := j0_pair _ _ κ1 C1 κ2 C2 hκ1 hκ2 hd1 hd2
  have hG1b := j0_iter_band φ s0 s1 hb1 α
  have hG2b := j0_iter_band ψ s0 s1 hb2 α
  have hIA : Integrable (fun x : ℝ × ℝ => ‖nzS2^[α] a x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) := by
    obtain ⟨sa0, sa1, κa, Ca, hsa0, hκa, hbA, hdA⟩ :=
      j0_data_decay (nzS2^[α] a) (nzmb_iter_contDiff α a ha) (j0_iter_NzBand2 α a ha hBa)
    exact j0_int _ (nzmb_iter_contDiff α a ha) sa0 sa1 κa Ca hsa0 hκa hbA hdA
  have hIB : Integrable (fun x : ℝ × ℝ => ‖nzS2^[α] b x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ)))
      (volume.restrict (Ioi 0 ×ˢ univ)) := by
    obtain ⟨sb0, sb1, κb, Cb, hsb0, hκb, hbB, hdB⟩ :=
      j0_data_decay (nzS2^[α] b) (nzmb_iter_contDiff α b hb) (j0_iter_NzBand2 α b hb hBb)
    exact j0_int _ (nzmb_iter_contDiff α b hb) sb0 sb1 κb Cb hsb0 hκb hbB hdB
  obtain ⟨E1, E2, E3, E4⟩ := j0_core k _ _ _ _ (nzmb_iter_contDiff α φ hφs)
    (nzmb_iter_contDiff α ψ hψs) hAB s0 s1 κ C hs0 hκ hG1b hG2b hdec hIA hIB
  have hv : 0 ≤ Real.sqrt (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ, ‖nzS2^[α] a x‖ ^ 2 *
      x.1 ^ (-(3 / 2 : ℝ))) + Real.sqrt (∫ x : ℝ × ℝ in Ioi 0 ×ˢ univ,
      ‖nzS2^[α] b x‖ ^ 2 * x.1 ^ (-(3 / 2 : ℝ))) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [j0_mom0 α a, j0_mom0 α b]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h | h | h | h
  · rw [h, j0_mom0 α φ]
    exact j0_real k _ _ _ hk (j0_int_nonneg _) (j0_int_nonneg _) (j0_int_nonneg _) E1
  · rw [h, j0_mom0 α (fun x => fderiv ℝ φ x (0, 1)), j0_iter_fderiv_fun α φ hφs]
    exact j0_sqrt_bound k _ _ _ (j0_int_nonneg _) (j0_int_nonneg _) (j0_int_nonneg _) E2
  · rw [h, j0_mom0_const k α φ hφs]
    exact j0_sqrt_bound k _ _ _ (mul_nonneg (sq_nonneg k) (j0_int_nonneg _))
      (j0_int_nonneg _) (j0_int_nonneg _) E1
  · rw [h, j0_mom0 α ψ]
    exact j0_real k _ _ _ hk (j0_int_nonneg _) (j0_int_nonneg _) (j0_int_nonneg _) E3
  · rw [h, j0_mom0 α (fun x => fderiv ℝ ψ x (0, 1)), j0_iter_fderiv_fun α ψ hψs]
    exact j0_sqrt_bound k _ _ _ (j0_int_nonneg _) (j0_int_nonneg _) (j0_int_nonneg _) E4
  · rw [h, j0_mom0_const k α ψ hψs]
    exact j0_sqrt_bound k _ _ _ (mul_nonneg (sq_nonneg k) (j0_int_nonneg _))
      (j0_int_nonneg _) (j0_int_nonneg _) E3

end UnforcedLeray.Short.PartIIa
