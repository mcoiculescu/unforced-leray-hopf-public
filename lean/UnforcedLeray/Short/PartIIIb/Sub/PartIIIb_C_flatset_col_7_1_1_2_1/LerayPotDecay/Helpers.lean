import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayKerAsym
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayRegKerIBP
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayForceDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayBoundedDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayKerWindow

/-!
# Helpers for `LerayPotDecay`

Source `the November 2 reference manuscript` 1676: the constant part `±a/4π` of
`K₁` integrates a derivative `∂_j F₁` over a cell to `0` (`dd_int_zero`, from `CellIBP` with `A = 1`),
and the far-field estimate of `lerayPot` is a window estimate with `CylKerAsym`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The `v`-derivative of each component of a field. -/
def dfDv (F : Chart → Fin 2 → ℝ) (v : Chart) : Chart → Fin 2 → ℝ :=
  fun p i => fderiv ℝ (fun p' => F p' i) p v

lemma dd_freq_pos (c : ℝ) (hc : 0 < c) : 0 < cylFreq c := by
  unfold cylFreq
  exact div_pos (mul_pos two_pos Real.pi_pos) hc

lemma dd_hasFDerivAt_shift (p : Chart) (y : ℝ × ℝ) :
    HasFDerivAt (fun y' : ℝ × ℝ => p + ((0 : ℝ), -y'))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (-ContinuousLinearMap.id ℝ (ℝ × ℝ))) y := by
  have h1 : HasFDerivAt (fun y' : ℝ × ℝ => -y') (-ContinuousLinearMap.id ℝ (ℝ × ℝ)) y :=
    (hasFDerivAt_id y).neg
  have h2 : HasFDerivAt (fun y' : ℝ × ℝ => ((0 : ℝ), -y'))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (-ContinuousLinearMap.id ℝ (ℝ × ℝ))) y :=
    (hasFDerivAt_const (0 : ℝ) y).prodMk h1
  exact h2.const_add p

lemma dd_chain1 (g : Chart → ℝ) (hg : ContDiff ℝ ∞ g) (p : Chart) (y v : ℝ × ℝ) :
    fderiv ℝ (fun y' => g (p + ((0 : ℝ), -y'))) y v =
      -fderiv ℝ g (p + ((0 : ℝ), -y)) ((0 : ℝ), v) := by
  have hgd : HasFDerivAt g (fderiv ℝ g (p + ((0 : ℝ), -y))) (p + ((0 : ℝ), -y)) :=
    ((hg.differentiable (by simp)) _).hasFDerivAt
  have hc := hgd.comp y (dd_hasFDerivAt_shift p y)
  rw [show (fun y' => g (p + ((0 : ℝ), -y'))) = g ∘ (fun y' => p + ((0 : ℝ), -y')) from rfl,
    hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
  rw [show ((0 : ℝ), -v) = -((0 : ℝ), v) by simp, map_neg]

lemma dd_zero (c : ℝ) (F : Chart → Fin 2 → ℝ) (hF : IsForceField c F) :
    ∃ LF : ℝ, ∀ q : Chart, LF < |q.2.2| → F q = 0 := by
  obtain ⟨_, _, _, _, LF, _, hsupp⟩ := hF
  refine ⟨LF, fun q hq => ?_⟩
  by_contra hne
  exact absurd (hsupp q hne).2 (not_le.2 hq)

lemma dd_test (c : ℝ) (hc : 0 < c) (F : Chart → Fin 2 → ℝ) (hF : IsForceField c F)
    (p : Chart) (i : Fin 2) : IsCylTest2 c (fun y => F (p + ((0 : ℝ), -y)) i) := by
  obtain ⟨LF, hLF⟩ := dd_zero c F hF
  refine ⟨?_, ?_, ?_⟩
  · exact (hF.1 i).comp (contDiff_const.add (contDiff_const.prodMk contDiff_id.neg))
  · intro y
    obtain ⟨s, q, η⟩ := p
    have e1 : ((s, (q, η)) + ((0 : ℝ), -((y.1 + c), y.2))) =
        (s, (q + -y.1 + -c, η + -y.2)) := by
      ext <;> simp <;> ring
    have e2 : ((s, (q, η)) + ((0 : ℝ), -y)) = (s, (q + -y.1, η + -y.2)) := by
      ext <;> simp
    show F ((s, (q, η)) + ((0 : ℝ), -((y.1 + c), y.2))) i = F ((s, (q, η)) + ((0 : ℝ), -y)) i
    rw [e1, e2]
    have h := congrFun (hF.2.1 s (q + -y.1 + -c) (η + -y.2)) i
    rw [show q + -y.1 + -c + c = q + -y.1 by ring] at h
    exact h.symm
  · refine ⟨LF + |p.2.2|, fun y hy => ?_⟩
    have hz : LF < |(p + ((0 : ℝ), -y)).2.2| := by
      have e : (p + ((0 : ℝ), -y)).2.2 = p.2.2 - y.2 := by simp [sub_eq_add_neg]
      rw [e]
      rcases abs_cases p.2.2 with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
        rcases abs_cases y.2 with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
        rcases abs_cases (p.2.2 - y.2) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> linarith
    exact congrFun (hLF _ hz) i

/-- Integrability of `y ↦ K_i(y) G_i(p.1, p.2 - y)` on the cell for a force field `G`. -/
lemma dd_integrable (c : ℝ) (hc : 0 < c) (G : Chart → Fin 2 → ℝ) (hG : IsForceField c G)
    (i : Fin 2) (p : Chart) :
    Integrable (fun y : ℝ × ℝ => cylKer c i y * G (p.1, p.2 - y) i)
      (volume.restrict (cellC c)) := by
  obtain ⟨hGs, hGper, s0, s1, LG, hs0, hsupp⟩ := hG
  have hFi : ContDiff ℝ ∞ (fun q => G q i) := hGs i
  have hperi : ∀ s q η, (fun q => G q i) (s, (q + c, η)) = (fun q => G q i) (s, (q, η)) :=
    fun s q η => congrFun (hGper s q η) i
  have hLF : ∀ q : Chart, LG < |q.2.2| → G q i = 0 := by
    intro q hq
    by_contra hne
    have hG0 : G q ≠ 0 := fun h0 => hne (by simp [h0])
    exact absurd (hsupp q hG0).2 (not_le.2 hq)
  obtain ⟨M, hM⟩ := boundedDerivBand c hc (fun q => G q i) hFi hperi
    ⟨s0, s1, LG, fun q hq => hsupp q (fun h0 => hq (by simp [h0]))⟩ 0
  have hMM : ∀ q : Chart, ‖iteratedFDeriv ℝ 0 (fun q => G q i) q‖ ≤ max M 0 :=
    fun q => (hM q).trans (le_max_left _ _)
  have hcont : Continuous (fun y : ℝ × ℝ => G (p.1, p.2 - y) i) :=
    hFi.continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hmeas : AEStronglyMeasurable (fun y : ℝ × ℝ => cylKer c i y * G (p.1, p.2 - y) i)
      (volume.restrict (cellC c)) :=
    (cylKW_meas c i).aestronglyMeasurable.mul hcont.aestronglyMeasurable
  refine Integrable.mono' (lps_ind_int c hc i p.2.2 LG (max M 0)) hmeas ?_
  refine ae_restrict_of_forall_mem (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)
    (fun y hy => ?_)
  have h := lps_pointwise c G i LG hLF hFi (max M 0) 0 hMM y hy p
  rw [norm_iteratedFDeriv_zero] at h
  exact h

/-- Each component of a force field is bounded by a common constant. -/
lemma dd_compBound (c : ℝ) (hc : 0 < c) (G : Chart → Fin 2 → ℝ) (hG : IsForceField c G) :
    ∃ M : ℝ, ∀ (z : Chart) (i : Fin 2), |G z i| ≤ M := by
  obtain ⟨hGs, hGper, s0, s1, LG, hs0, hsupp⟩ := hG
  have hcomp : ∀ i : Fin 2, ∃ M : ℝ, ∀ z : Chart, |G z i| ≤ M := by
    intro i
    have hperi : ∀ s q η, (fun q => G q i) (s, (q + c, η)) = (fun q => G q i) (s, (q, η)) :=
      fun s q η => congrFun (hGper s q η) i
    obtain ⟨M, hM⟩ := boundedDerivBand c hc (fun q => G q i) (hGs i) hperi
      ⟨s0, s1, LG, fun q hq => hsupp q (fun h0 => hq (by simp [h0]))⟩ 0
    refine ⟨M, fun z => ?_⟩
    have h := hM z
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
    exact h
  obtain ⟨M0, h0⟩ := hcomp 0
  obtain ⟨M1, h1⟩ := hcomp 1
  refine ⟨max M0 M1, fun z i => ?_⟩
  fin_cases i
  · exact (h0 z).trans (le_max_left _ _)
  · exact (h1 z).trans (le_max_right _ _)

/-- The window volume: `vol(Ioc × Icc) = c · 2L` (for `L ≥ 0`), finite. -/
lemma dd_vol_real (c : ℝ) (hc : 0 < c) (η LG : ℝ) (hLG : 0 ≤ LG) :
    (volume (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (η - LG) (η + LG))).toReal = c * (2 * LG) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

lemma dd_vol_ne (c η LG : ℝ) :
    volume (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (η - LG) (η + LG)) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioc, Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- **Zero mean of the constant part**: `∫_cell ∂_j F₁(s, x - y) dy = 0` for `j = q, η`
(`CellIBP` with `A = 1`: `∂_j` of a test function integrates to zero over the cell). -/
lemma dd_int_zero (c : ℝ) (hc : 0 < c) (F : Chart → Fin 2 → ℝ) (hF : IsForceField c F)
    (p : Chart) (i : Fin 2) :
    ∫ y in cellC c, dfDv F ((0 : ℝ), dir2 i) (p.1, p.2 - y) 1 = 0 := by
  have hgs : ContDiff ℝ ∞ (fun z => F z 1) := hF.1 1
  have hpt : ∀ y : ℝ × ℝ, dfDv F ((0 : ℝ), dir2 i) (p.1, p.2 - y) 1 =
      -pd2 i (fun y' => F (p + ((0 : ℝ), -y')) 1) y := by
    intro y
    have h := dd_chain1 (fun z => F z 1) hgs p y (dir2 i)
    have hpd : pd2 i (fun y' => F (p + ((0 : ℝ), -y')) 1) y =
        -fderiv ℝ (fun z => F z 1) (p + ((0 : ℝ), -y)) ((0 : ℝ), dir2 i) := h
    rw [hpd, neg_neg, lps_shift]
    rfl
  have hint : ∫ y in cellC c, dfDv F ((0 : ℝ), dir2 i) (p.1, p.2 - y) 1 =
      -∫ y in cellC c, pd2 i (fun y' => F (p + ((0 : ℝ), -y')) 1) y := by
    rw [← integral_neg]
    congr 1
    funext y
    exact hpt y
  rw [hint]
  obtain ⟨hHs, hHper, L, hL⟩ := dd_test c hc F hF p 1
  have hC := cellIBP c hc (-(c / 2)) (fun _ => (1 : ℝ)) (fun y => F (p + ((0 : ℝ), -y)) 1)
    contDiff_const (hHs.of_le (by simp)) (fun _ => rfl) hHper ⟨L, hL⟩ i
  have h0 : pd2 i (fun _ => (1 : ℝ)) = fun _ => (0 : ℝ) := by
    funext y
    simp [pd2]
  rw [h0] at hC
  rw [rki_cellC_eq c]
  simpa using hC


/-- **Far-field estimate**: for `|η| ≥ L + 1`, the constant part is removed by `dd_int_zero`, and
`K₀`, `K₁ - (a/4π) sign η` are `O(e^{-a|y.2|})` on the window, which has length `2L` in `η`. -/
lemma dd_far (c : ℝ) (hc : 0 < c) (G : Chart → Fin 2 → ℝ) (hG : IsForceField c G)
    (hG0 : ∀ p : Chart, ∫ y in cellC c, G (p.1, p.2 - y) 1 = 0)
    (LG : ℝ) (hLG0 : 0 ≤ LG) (hLG : ∀ q : Chart, LG < |q.2.2| → G q = 0)
    (M : ℝ) (hM : ∀ (z : Chart) (i : Fin 2), |G z i| ≤ M)
    (CA : ℝ) (hCA0 : 0 ≤ CA)
    (hCA : ∀ y : ℝ × ℝ, 1 ≤ |y.2| →
      |cylKer c 0 y| ≤ CA * Real.exp (-(cylFreq c * |y.2|)) ∧
      |cylKer c 1 y - cylFreq c / (4 * Real.pi) * Real.sign y.2| ≤
        CA * Real.exp (-(cylFreq c * |y.2|)))
    (p : Chart) (hp : LG + 1 ≤ |p.2.2|) :
    |lerayPot c G p| ≤
      2 * CA * M * (c * (2 * LG)) * Real.exp (-(cylFreq c * (|p.2.2| - LG))) := by
  have ha : 0 < cylFreq c := dd_freq_pos c hc
  obtain ⟨k1, hk1⟩ : ∃ k1 : ℝ, k1 = cylFreq c / (4 * Real.pi) * Real.sign p.2.2 := ⟨_, rfl⟩
  have hint0 := dd_integrable c hc G hG 0 p
  have hint1 := dd_integrable c hc G hG 1 p
  have hcont : Continuous (fun y : ℝ × ℝ => G (p.1, p.2 - y) 1) :=
    (hG.1 1).continuous.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
  have hzero : ∀ y : ℝ × ℝ, (LG + |p.2.2|) < |y.2| → G (p.1, p.2 - y) 1 = 0 := by
    intro y hy
    have h1 := abs_sub_abs_le_abs_sub y.2 p.2.2
    have h2 : LG < |(p.1, p.2 - y).2.2| := by
      show LG < |p.2.2 - y.2|
      rw [abs_sub_comm]
      linarith
    exact congrFun (hLG _ h2) 1
  have hintk : Integrable (fun y : ℝ × ℝ => k1 * G (p.1, p.2 - y) 1)
      (volume.restrict (cellC c)) :=
    (rki_integrableOn_cellC _ hcont c (LG + |p.2.2|) hzero).const_mul k1
  have hf : Integrable (fun y : ℝ × ℝ => cylKer c 0 y * G (p.1, p.2 - y) 0 +
      (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1))
      (volume.restrict (cellC c)) :=
    hint0.add (hint1.sub hintk)
  have hk1zero : ∫ y in cellC c, k1 * G (p.1, p.2 - y) 1 = 0 := by
    rw [integral_const_mul, hG0 p, mul_zero]
  have hsplit : lerayPot c G p = ∫ y in cellC c, (cylKer c 0 y * G (p.1, p.2 - y) 0 +
      (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)) := by
    unfold lerayPot
    rw [Fin.sum_univ_two, ← integral_add hint0 hint1]
    have h2 : ∫ y in cellC c, (cylKer c 0 y * G (p.1, p.2 - y) 0 +
        cylKer c 1 y * G (p.1, p.2 - y) 1) =
        ∫ y in cellC c, ((cylKer c 0 y * G (p.1, p.2 - y) 0 +
          (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)) +
          k1 * G (p.1, p.2 - y) 1) := by
      congr 1
      funext y
      ring
    rw [h2, integral_add hf hintk, hk1zero, add_zero]
  have hWsub : Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LG) (p.2.2 + LG) ⊆ cellC c :=
    fun y hy => ⟨hy.1, mem_univ _⟩
  have hW : MeasurableSet (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LG) (p.2.2 + LG)) :=
    measurableSet_Ioc.prod measurableSet_Icc
  have hWfin : (volume.restrict (cellC c)) (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LG) (p.2.2 + LG))
      ≠ ⊤ := by
    rw [Measure.restrict_apply hW, inter_eq_left.2 hWsub]
    exact dd_vol_ne c p.2.2 LG
  have hbound : ∀ᵐ y ∂(volume.restrict (cellC c)),
      ‖cylKer c 0 y * G (p.1, p.2 - y) 0 +
        (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)‖ ≤
      (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LG) (p.2.2 + LG)).indicator
        (fun _ => 2 * CA * M * Real.exp (-(cylFreq c * (|p.2.2| - LG)))) y := by
    refine ae_restrict_of_forall_mem (MeasurableSet.prod measurableSet_Ioc MeasurableSet.univ)
      (fun y hy => ?_)
    by_cases hyW : y ∈ Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LG) (p.2.2 + LG)
    · rw [Set.indicator_of_mem hyW]
      have hy2 : |p.2.2 - y.2| ≤ LG := abs_le.2 ⟨by linarith [hyW.2.2], by linarith [hyW.2.1]⟩
      have hyabs : |p.2.2| - LG ≤ |y.2| := by
        have h1 := abs_sub_abs_le_abs_sub p.2.2 y.2
        linarith
      have hy1 : 1 ≤ |y.2| := by linarith
      have hsign : Real.sign y.2 = Real.sign p.2.2 := by
        rcases le_total 0 p.2.2 with h0 | h0
        · rw [abs_of_nonneg h0] at hp
          have hyp : 0 < y.2 := by linarith [hyW.2.1]
          rw [Real.sign_of_pos hyp, Real.sign_of_pos (by linarith)]
        · rw [abs_of_nonpos h0] at hp
          have hyn : y.2 < 0 := by linarith [hyW.2.2]
          rw [Real.sign_of_neg hyn, Real.sign_of_neg (by linarith)]
      have hA := hCA y hy1
      rw [hsign, ← hk1] at hA
      have hexp : Real.exp (-(cylFreq c * |y.2|)) ≤
          Real.exp (-(cylFreq c * (|p.2.2| - LG))) :=
        Real.exp_le_exp.2 (by have := mul_le_mul_of_nonneg_left hyabs ha.le; linarith)
      have hK0 : |cylKer c 0 y| ≤ CA * Real.exp (-(cylFreq c * (|p.2.2| - LG))) :=
        hA.1.trans (mul_le_mul_of_nonneg_left hexp hCA0)
      have hK1 : |cylKer c 1 y - k1| ≤ CA * Real.exp (-(cylFreq c * (|p.2.2| - LG))) :=
        hA.2.trans (mul_le_mul_of_nonneg_left hexp hCA0)
      have hE0 : 0 ≤ CA * Real.exp (-(cylFreq c * (|p.2.2| - LG))) :=
        mul_nonneg hCA0 (Real.exp_nonneg _)
      have hG0b := hM (p.1, p.2 - y) 0
      have hG1b := hM (p.1, p.2 - y) 1
      calc ‖cylKer c 0 y * G (p.1, p.2 - y) 0 +
            (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1)‖
          = |cylKer c 0 y * G (p.1, p.2 - y) 0 +
            (cylKer c 1 y - k1) * G (p.1, p.2 - y) 1| := by
            rw [Real.norm_eq_abs]
            congr 1
            ring
        _ ≤ |cylKer c 0 y * G (p.1, p.2 - y) 0| +
            |(cylKer c 1 y - k1) * G (p.1, p.2 - y) 1| := abs_add_le _ _
        _ = |cylKer c 0 y| * |G (p.1, p.2 - y) 0| +
            |cylKer c 1 y - k1| * |G (p.1, p.2 - y) 1| := by
            rw [abs_mul, abs_mul]
        _ ≤ (CA * Real.exp (-(cylFreq c * (|p.2.2| - LG)))) * M +
            (CA * Real.exp (-(cylFreq c * (|p.2.2| - LG)))) * M :=
            add_le_add (mul_le_mul hK0 hG0b (abs_nonneg _) hE0)
              (mul_le_mul hK1 hG1b (abs_nonneg _) hE0)
        _ = 2 * CA * M * Real.exp (-(cylFreq c * (|p.2.2| - LG))) := by ring
    · rw [Set.indicator_of_notMem hyW]
      have hyS : LG < |p.2.2 - y.2| := by
        by_contra hcon
        push_neg at hcon
        apply hyW
        exact ⟨hy.1, ⟨by linarith [(abs_le.1 hcon).2], by linarith [(abs_le.1 hcon).1]⟩⟩
      have hz : G (p.1, p.2 - y) = 0 := hLG _ hyS
      rw [hz]
      simp
  have hgint : Integrable ((Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LG) (p.2.2 + LG)).indicator
      (fun _ => 2 * CA * M * Real.exp (-(cylFreq c * (|p.2.2| - LG)))))
      (volume.restrict (cellC c)) :=
    (integrable_indicator_iff hW).2 (integrableOn_const hWfin)
  have hle := norm_integral_le_of_norm_le hgint hbound
  have hval : ∫ y in cellC c, (Ioc (-(c / 2)) (c / 2) ×ˢ Icc (p.2.2 - LG) (p.2.2 + LG)).indicator
      (fun _ => 2 * CA * M * Real.exp (-(cylFreq c * (|p.2.2| - LG)))) y =
      (c * (2 * LG)) * (2 * CA * M * Real.exp (-(cylFreq c * (|p.2.2| - LG)))) := by
    rw [integral_indicator_const _ hW, smul_eq_mul, Measure.real, Measure.restrict_apply hW,
      inter_eq_left.2 hWsub, dd_vol_real c hc _ LG hLG0]
  rw [hsplit, ← Real.norm_eq_abs]
  calc ‖∫ y in cellC c, (cylKer c 0 y * G (p.1, p.2 - y) 0 +
        (cylKer c 1 y * G (p.1, p.2 - y) 1 - k1 * G (p.1, p.2 - y) 1))‖
      ≤ _ := hle
    _ = (c * (2 * LG)) * (2 * CA * M * Real.exp (-(cylFreq c * (|p.2.2| - LG)))) := hval
    _ = 2 * CA * M * (c * (2 * LG)) * Real.exp (-(cylFreq c * (|p.2.2| - LG))) := by ring

/-- **General decay of `lerayPot`** for a force field whose constant component integrates to zero:
`|u(p)| ≤ C e^{-a|η|}`, `a = cylFreq c`. -/
lemma dd_decay_gen (c : ℝ) (hc : 0 < c) (G : Chart → Fin 2 → ℝ) (hG : IsForceField c G)
    (hG0 : ∀ p : Chart, ∫ y in cellC c, G (p.1, p.2 - y) 1 = 0) :
    ∃ C : ℝ, ∀ p : Chart, |lerayPot c G p| ≤ C * Real.exp (-(cylFreq c * |p.2.2|)) := by
  have ha : 0 < cylFreq c := dd_freq_pos c hc
  obtain ⟨LG0, hLG0'⟩ := dd_zero c G hG
  obtain ⟨LG, hLGnn, hLG⟩ : ∃ LG : ℝ, 0 ≤ LG ∧ ∀ q : Chart, LG < |q.2.2| → G q = 0 :=
    ⟨|LG0|, abs_nonneg _, fun q hq => hLG0' q (lt_of_le_of_lt (le_abs_self _) hq)⟩
  obtain ⟨M, hM⟩ := dd_compBound c hc G hG
  obtain ⟨CA, hCA0, hCA⟩ : ∃ CA : ℝ, 0 ≤ CA ∧ ∀ y : ℝ × ℝ, 1 ≤ |y.2| →
      |cylKer c 0 y| ≤ CA * Real.exp (-(cylFreq c * |y.2|)) ∧
      |cylKer c 1 y - cylFreq c / (4 * Real.pi) * Real.sign y.2| ≤
        CA * Real.exp (-(cylFreq c * |y.2|)) := by
    obtain ⟨C, hC⟩ := cylKerAsym c hc
    refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
    obtain ⟨h1, h2⟩ := hC y hy
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)),
      h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _))⟩
  obtain ⟨U, hU⟩ := (lerayPotSmooth c hc G hG).2.1 0
  refine ⟨max (2 * CA * M * (c * (2 * LG)) * Real.exp (cylFreq c * LG))
    (U * Real.exp (cylFreq c * (LG + 1))), fun p => ?_⟩
  have hE : 0 ≤ Real.exp (-(cylFreq c * |p.2.2|)) := (Real.exp_pos _).le
  by_cases hp : LG + 1 ≤ |p.2.2|
  · have h1 := dd_far c hc G hG hG0 LG hLGnn hLG M (fun z i => hM z i) CA hCA0 hCA p hp
    have h2 : Real.exp (-(cylFreq c * (|p.2.2| - LG))) =
        Real.exp (cylFreq c * LG) * Real.exp (-(cylFreq c * |p.2.2|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h2] at h1
    calc |lerayPot c G p|
        ≤ 2 * CA * M * (c * (2 * LG)) *
          (Real.exp (cylFreq c * LG) * Real.exp (-(cylFreq c * |p.2.2|))) := h1
      _ = (2 * CA * M * (c * (2 * LG)) * Real.exp (cylFreq c * LG)) *
          Real.exp (-(cylFreq c * |p.2.2|)) := by ring
      _ ≤ max (2 * CA * M * (c * (2 * LG)) * Real.exp (cylFreq c * LG))
          (U * Real.exp (cylFreq c * (LG + 1))) * Real.exp (-(cylFreq c * |p.2.2|)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hE
  · push_neg at hp
    have h1 : |lerayPot c G p| ≤ U := by
      have h := hU p
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
      exact h
    have hU0 : 0 ≤ U := (abs_nonneg _).trans h1
    have hE1 : 1 ≤ Real.exp (cylFreq c * (LG + 1)) * Real.exp (-(cylFreq c * |p.2.2|)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hp.le ha.le
      linarith
    calc |lerayPot c G p| ≤ U := h1
      _ ≤ U * (Real.exp (cylFreq c * (LG + 1)) * Real.exp (-(cylFreq c * |p.2.2|))) :=
        le_mul_of_one_le_right hU0 hE1
      _ = (U * Real.exp (cylFreq c * (LG + 1))) * Real.exp (-(cylFreq c * |p.2.2|)) := by ring
      _ ≤ max (2 * CA * M * (c * (2 * LG)) * Real.exp (cylFreq c * LG))
          (U * Real.exp (cylFreq c * (LG + 1))) * Real.exp (-(cylFreq c * |p.2.2|)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hE

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
