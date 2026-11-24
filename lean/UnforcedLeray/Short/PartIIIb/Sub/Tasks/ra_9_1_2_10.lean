import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.GeoDTasks
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_5
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_8
import UnforcedLeray.Short.PartIIIb.Sub.Tasks.ra_9_1_2_9
import Mathlib.Algebra.Order.Chebyshev

/-!
# `PartIII-b:C/asrc/ra/9/1/2/10` : `geoGCellL2`

Source of record: `the November 2 reference manuscript`,
lines 5034-5039, 4979-4980, 5063-5079.
Combines `latSmooth` (`ra_9_1_2_5`), `geoGPointwise` (`ra_9_1_2_8`), and `latCellBound` (`ra_9_1_2_9`)
to establish `GeoGCellL2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (Params)

private lemma cont_word_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Chart → E} (hF : ContDiffOn ℝ 4 F (Ioi 0 ×ˢ univ))
    {w : List (Fin 3)} (hw : w ∈ budgetWords) {s : ℝ} (hs : 0 < s) :
    Continuous (fun x : ℝ × ℝ => wordW w F (s, x)) := by
  have hlen : w.length ≤ 4 := mem_wordsLE.1 (by rwa [← budgetWords_eq])
  have hF0 : ContDiffOn ℝ ((4 : ℕ) : WithTop ℕ∞) F UC := hF
  have hF' : ContDiffOn ℝ ((0 + w.length : ℕ) : WithTop ℕ∞) F UC :=
    cd_mono (by omega) hF0
  have hcw : ContinuousOn (wordW w F) UC := (cd_wordW w 0 hF').continuousOn
  exact hcw.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hs, trivial⟩)

private lemma meas_word_term {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Chart → E} (hF : ContDiffOn ℝ 4 F (Ioi 0 ×ˢ univ))
    {w : List (Fin 3)} (hw : w ∈ budgetWords) {s : ℝ} (hs : 0 < s) :
    Measurable (fun x : ℝ × ℝ => ENNReal.ofReal (((1 + |x.2|) ^ 3 * ‖wordW w F (s, x)‖) ^ 2)) := by
  have hc1 : Continuous (fun x : ℝ × ℝ => (1 + |x.2|) ^ 3) :=
    (continuous_const.add (continuous_snd.abs)).pow 3
  have hc2 : Continuous (fun x : ℝ × ℝ => ‖wordW w F (s, x)‖) :=
    (cont_word_slice hF hw hs).norm
  exact ENNReal.measurable_ofReal.comp (((hc1.mul hc2).pow 2).measurable)

private lemma pt_sq_sum_bound (S : Finset (List (Fin 3))) (K : ℝ) (a b : List (Fin 3) → ℝ)
    {g : ℝ} (hg : 0 ≤ g) (hpt : g ≤ K * ∑ w ∈ S, (a w + b w)) :
    g ^ 2 ≤ K ^ 2 * (2 * (S.card : ℝ)) *
      ∑ w ∈ S, (a w ^ 2 + b w ^ 2) := by
  have h1 : g ^ 2 ≤ (K * ∑ w ∈ S, (a w + b w)) ^ 2 :=
    pow_le_pow_left₀ hg hpt 2
  have h2 : (∑ w ∈ S, (a w + b w)) ^ 2
      ≤ (S.card : ℝ) * ∑ w ∈ S, (a w + b w) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : ∑ w ∈ S, (a w + b w) ^ 2
      ≤ ∑ w ∈ S, 2 * (a w ^ 2 + b w ^ 2) := by
    refine Finset.sum_le_sum fun w _ => ?_
    nlinarith [sq_nonneg (a w - b w)]
  rw [← Finset.mul_sum] at h3
  have h4 : (K * ∑ w ∈ S, (a w + b w)) ^ 2
      = K ^ 2 * (∑ w ∈ S, (a w + b w)) ^ 2 := mul_pow _ _ 2
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have hcard : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  calc g ^ 2 ≤ K ^ 2 * (∑ w ∈ S, (a w + b w)) ^ 2 := by linarith
    _ ≤ K ^ 2 * ((S.card : ℝ) * ∑ w ∈ S, (a w + b w) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 hK2
    _ ≤ K ^ 2 * ((S.card : ℝ) * (2 * ∑ w ∈ S, (a w ^ 2 + b w ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hcard) hK2
    _ = K ^ 2 * (2 * (S.card : ℝ)) * ∑ w ∈ S, (a w ^ 2 + b w ^ 2) := by ring

private lemma cell_sum_bound (S : Finset (List (Fin 3))) (μc : Measure (ℝ × ℝ))
    (G : ℝ × ℝ → Merid) (F1 : Chart → Merid) (F2 : Chart → ℝ)
    (C1 C2 νk M s : ℝ) (hs : 0 < s)
    (hF1 : ∀ w ∈ S, Measurable (fun x : ℝ × ℝ =>
      ENNReal.ofReal (((1 + |x.2|) ^ 3 * ‖wordW w F1 (s, x)‖) ^ 2)))
    (hF2 : ∀ w ∈ S, Measurable (fun x : ℝ × ℝ =>
      ENNReal.ofReal (((1 + |x.2|) ^ 3 * |wordW w F2 (s, x)|) ^ 2)))
    (hpt : ∀ x : ℝ × ℝ, ‖G x‖ ≤ C1 * (1 + s⁻¹) * (1 + |x.2|) ^ 3 *
      ∑ w ∈ S, (‖wordW w F1 (s, x)‖ + |wordW w F2 (s, x)|))
    (hcell : ∀ w ∈ S,
      (∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * ‖wordW w F1 (s, x)‖) ^ 2) ∂μc
        ≤ ENNReal.ofReal ((C2 * νk * M * s ^ (5 / 2 : ℝ)) ^ 2)) ∧
      (∫⁻ x, ENNReal.ofReal (((1 + |x.2|) ^ 3 * |wordW w F2 (s, x)|) ^ 2) ∂μc
        ≤ ENNReal.ofReal ((C2 * νk * M * s ^ (5 / 2 : ℝ)) ^ 2))) :
    ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μc ≤
      ENNReal.ofReal ((2 * C1 * (S.card : ℝ) * C2 * νk * M *
        (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) ^ 2) := by
  let N : ℝ := S.card
  set a : List (Fin 3) → ℝ × ℝ → ℝ :=
    fun w x => (1 + |x.2|) ^ 3 * ‖wordW w F1 (s, x)‖ with ha_def
  set b : List (Fin 3) → ℝ × ℝ → ℝ :=
    fun w x => (1 + |x.2|) ^ 3 * |wordW w F2 (s, x)| with hb_def
  set B : ℝ := C2 * νk * M * s ^ (5 / 2 : ℝ) with hB_def
  set K0 : ℝ := C1 * (1 + s⁻¹) with hK0_def
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hpt_enn : ∀ x : ℝ × ℝ,
      ENNReal.ofReal (‖G x‖ ^ 2) ≤
        ENNReal.ofReal (K0 ^ 2 * (2 * N)) *
          ∑ w ∈ S, (ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) := by
    intro x
    have hq := hpt x
    have hsum_eq : C1 * (1 + s⁻¹) * (1 + |x.2|) ^ 3 *
        ∑ w ∈ S, (‖wordW w F1 (s, x)‖ + |wordW w F2 (s, x)|)
        = K0 * ∑ w ∈ S, (a w x + b w x) := by
      rw [hK0_def, mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [ha_def, hb_def]; ring
    have hq' : ‖G x‖ ≤ K0 * ∑ w ∈ S, (a w x + b w x) := hsum_eq ▸ hq
    have hsq := pt_sq_sum_bound S K0 (fun w => a w x) (fun w => b w x) (norm_nonneg _) hq'
    calc ENNReal.ofReal (‖G x‖ ^ 2)
        ≤ ENNReal.ofReal (K0 ^ 2 * (2 * N) * ∑ w ∈ S, (a w x ^ 2 + b w x ^ 2)) :=
          ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (K0 ^ 2 * (2 * N)) *
            ENNReal.ofReal (∑ w ∈ S, (a w x ^ 2 + b w x ^ 2)) :=
          ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (K0 ^ 2 * (2 * N)) *
            ∑ w ∈ S, (ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) := by
          congr 1
          rw [ENNReal.ofReal_sum_of_nonneg (fun w _ => by positivity)]
          refine Finset.sum_congr rfl fun w _ => ?_
          exact ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)
  have hmeas_ab : ∀ w ∈ S,
      Measurable (fun x => ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) :=
    fun w hw => (hF1 w hw).add (hF2 w hw)
  have hint_sum : ∫⁻ x, ∑ w ∈ S,
        (ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) ∂μc
      ≤ ENNReal.ofReal (N * (2 * B ^ 2)) := by
    rw [lintegral_finsetSum S hmeas_ab]
    have hle : ∀ w ∈ S,
        ∫⁻ x, (ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) ∂μc
          ≤ ENNReal.ofReal (2 * B ^ 2) := by
      intro w hw
      rw [lintegral_add_left (hF1 w hw)]
      obtain ⟨ha_cell, hb_cell⟩ := hcell w hw
      calc ∫⁻ x, ENNReal.ofReal (a w x ^ 2) ∂μc + ∫⁻ x, ENNReal.ofReal (b w x ^ 2) ∂μc
          ≤ ENNReal.ofReal (B ^ 2) + ENNReal.ofReal (B ^ 2) := add_le_add ha_cell hb_cell
        _ = ENNReal.ofReal (2 * B ^ 2) := by
            rw [← ENNReal.ofReal_add (sq_nonneg B) (sq_nonneg B), two_mul]
    calc ∑ w ∈ S, ∫⁻ x, (ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) ∂μc
        ≤ ∑ _w ∈ S, ENNReal.ofReal (2 * B ^ 2) := Finset.sum_le_sum hle
      _ = S.card • ENNReal.ofReal (2 * B ^ 2) := Finset.sum_const _
      _ = ENNReal.ofReal (N * (2 * B ^ 2)) := by
          rw [nsmul_eq_mul, ENNReal.ofReal_mul hN, ENNReal.ofReal_natCast]
  have hs_pow : (1 + s⁻¹) * s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ) := by
    have e1 : s ^ (5 / 2 : ℝ) = s * s ^ (3 / 2 : ℝ) := by
      rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hs, Real.rpow_one]
    have e2 : s⁻¹ * s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) := by
      rw [e1, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    calc (1 + s⁻¹) * s ^ (5 / 2 : ℝ) = s ^ (5 / 2 : ℝ) + s⁻¹ * s ^ (5 / 2 : ℝ) := by ring
      _ = s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ) := by rw [e2, add_comm]
  calc ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μc
      ≤ ∫⁻ x, ENNReal.ofReal (K0 ^ 2 * (2 * N)) *
          ∑ w ∈ S, (ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) ∂μc :=
        lintegral_mono hpt_enn
    _ = ENNReal.ofReal (K0 ^ 2 * (2 * N)) *
          ∫⁻ x, ∑ w ∈ S, (ENNReal.ofReal (a w x ^ 2) + ENNReal.ofReal (b w x ^ 2)) ∂μc :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K0 ^ 2 * (2 * N)) * ENNReal.ofReal (N * (2 * B ^ 2)) := by gcongr
    _ = ENNReal.ofReal ((2 * C1 * N * C2 * νk * M *
          (s ^ (3 / 2 : ℝ) + s ^ (5 / 2 : ℝ))) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← hs_pow, hK0_def, hB_def]
        ring

/-- **Gaussian-summation cell bound** (source 5034-5039, 4979-4980, 5063-5079). -/
theorem geoGCellL2 (as : ℝ) (χf : ℝ → ℝ) : GeoGCellL2 as χf := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨C1, _hC1, Hpt⟩ := geoGPointwise as χf
  obtain ⟨C2, k, ν₀, hν₀, Hcell⟩ := latCellBound as χf hχ
  refine ⟨2 * C1 * (budgetWords.card : ℝ) * C2, k, min ν₀ 1, lt_min hν₀ one_pos, ?_⟩
  intro p d hreg hν μ hμ A hA s hs hs1
  have hν_pos : 0 < p.ν := p.ν_pos
  have hν_le_ν₀ : p.ν ≤ ν₀ := hν.trans (min_le_left _ _)
  have hν_le_1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hμ_Ioo : μ ∈ Ioo (0 : ℝ) (1 / 4) := hKs hμ
  have hμ_abs : |μ| ≤ 1 := abs_le.2 ⟨by linarith [hμ_Ioo.1], by linarith [hμ_Ioo.2]⟩
  have hε_pos : 0 < p.ε := p.ε_pos
  have hε_le_1 : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    have hd : 0 < d := hreg.dm_pos.trans_le hreg.dm_le
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hν_pos.le
  obtain ⟨hh, hp⟩ := latSmooth as χf hχ p.ν hν_pos A hA
  have hpt_all := Hpt hχ p.ν μ p.ε hν_pos hν_le_1 hμ_abs hε_pos hε_le_1 A hA hh hp
  have hcell_all := Hcell p.ν hν_pos hν_le_ν₀ A hA s hs hs1
  rw [hreg.c_eq]
  refine cell_sum_bound budgetWords (UnforcedLeray.Cyl.avgμ (cOf p.ν))
    (fun x => geoDG p.ν μ p.ε χf A (s, x)) (hpM p.ν χf A) (psiM p.ν χf A)
    C1 C2 (p.ν⁻¹ ^ k) (affM p.ν χf A) s hs
    (fun w hw => meas_word_term hh hw hs)
    (fun w hw => ?_)
    (fun x => hpt_all (s, x) hs)
    hcell_all
  have hm := meas_word_term hp hw hs
  simpa only [Real.norm_eq_abs] using hm

end UnforcedLeray.Short.PartIIIb.Concrete
