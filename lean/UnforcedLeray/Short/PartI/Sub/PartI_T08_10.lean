import UnforcedLeray.Short.PartI.Sub.PartI_T08_1
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.CellBridge

/-!
# Part I, task `PartI:T08/10` (`VcStressJetBound`): reduction to smoothness and periodicity of `Q_c`

Source: `the November 2 reference manuscript` lines 331-335 (`‖D^jQ‖₂ ≤ C_j a^{-(5+j)/2}
e^{-b_j c²/a}`). From `Train.Vc_bounds j 0` and the cell bridge, `VcStressJetBound` follows from the
leaves `QcSmooth` and `QcPeriodic` (tasks `PartI:T08/1/2`, `PartI:T08/1/3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

theorem qcT08_per_word (c : ℝ) (w : List Bool) :
    ∀ F : Plane → ℝ, Cyl.IsPeriodic c F → Cyl.IsPeriodic c (B0151.derivWord w F) := by
  induction w with
  | nil => intro F hF; exact hF
  | cons b w ih =>
    intro F hF
    cases b with
    | false => exact (ih F hF).partialEta
    | true => exact (ih F hF).partialQ

theorem qcT08_mem_words {j : ℕ} {w : List Bool} :
    w ∈ wordsOfLength j ↔ w.length = j := by
  unfold wordsOfLength
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 h
    exact List.length_ofFn
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem qcT08_card_words (l : ℕ) : (wordsOfLength l).card ≤ 2 ^ l := by
  unfold wordsOfLength
  exact Finset.card_image_le.trans (by simp)

theorem qcT08_int_sq_le {μ : Measure Plane} {g : Plane → ℝ} (hg : MemLp g 2 μ) {K : ℝ}
    (hK : 0 ≤ K) (h : eLpNorm g 2 μ ≤ ENNReal.ofReal K) : ∫ z, g z ^ 2 ∂μ ≤ K ^ 2 := by
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff hK).1 h
  simp only [ENNReal.toReal_ofNat] at h2
  have hX : 0 ≤ ∫ z, ‖g z‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun z => by positivity
  have h3 : (∫ z, ‖g z‖ ^ (2 : ℝ) ∂μ) ≤ K ^ 2 := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hX _) h2 (show (0:ℝ) ≤ 2 by norm_num)
    rw [← Real.rpow_mul hX] at this
    norm_num at this
    simpa using this
  refine le_trans (le_of_eq ?_) h3
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp [Real.norm_eq_abs, sq_abs]

theorem vcStressJetBound_of (hS : QcSmooth) (hP : QcPeriodic) : VcStressJetBound := by
  intro N
  choose C bb hC hbb hall using fun j : ℕ => Train.Vc_bounds j 0
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  let b : ℝ := (Finset.range (N + 1)).inf' hne (fun j => 2 * bb j)
  have hb : 0 < b := by
    show 0 < (Finset.range (N + 1)).inf' hne (fun j => 2 * bb j)
    rw [Finset.lt_inf'_iff]
    intro j _; linarith [hbb j]
  have hble : ∀ j ∈ Finset.range (N + 1), b ≤ 2 * bb j := fun j hj =>
    Finset.inf'_le (fun j => 2 * bb j) hj
  refine ⟨∑ j ∈ Finset.range (N + 1), 4 * 2 ^ j * C j ^ 2, b,
    Finset.sum_nonneg fun j _ => by positivity, hb, ?_⟩
  intro ν c s hν hc hs hac
  have hc0 : 0 < c := by linarith
  have ha1 : 1 ≤ width ν s := by simp only [Train.width]; nlinarith
  have ha0 : 0 < width ν s := by linarith
  -- per-word data
  have key : ∀ j : ℕ, ∀ (w : List Bool), w.length = j → ∀ k l : Fin 2,
      MemLp (B0151.derivWord w (fun z => Qc ν c s z k l)) 2 (Cyl.cellμ c) ∧
      ∫ z, B0151.derivWord w (fun x => Qc ν c s x k l) z ^ 2 ∂(Cyl.cellμ c) ≤
        C j ^ 2 / width ν s ^ (5 + j) * Real.exp (-(2 * bb j * c ^ 2 / width ν s)) := by
    intro j w hw k l
    obtain ⟨-, -, h3⟩ := hall j ν c s hc0 ha1 hac
    obtain ⟨hm, hn⟩ := h3 w hw k l
    simp only [pow_zero, one_mul] at hm hn
    have hsm : ContDiff ℝ ∞ (fun z => Qc ν c s z k l) := hS ν c s hν hc0 hs.le k l
    have hg : ContDiff ℝ ∞ (B0151.derivWord w (fun z => Qc ν c s z k l)) :=
      B0151.contDiff_derivWord hsm w
    have hmeas : Measurable (B0151.derivWord w (fun z => Qc ν c s z k l)) := hg.continuous.measurable
    have hper : Cyl.IsPeriodic c (B0151.derivWord w (fun z => Qc ν c s z k l)) :=
      qcT08_per_word c w _ (hP ν c s k l)
    have hm' := (memLp_cellMeasure_iff hc0 hmeas hper 2).1 hm
    refine ⟨hm', ?_⟩
    have hn' : eLpNorm (B0151.derivWord w (fun z => Qc ν c s z k l)) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal (C j * width ν s ^ (-(5 + (j : ℝ)) / 2) *
          Real.exp (-(bb j * c ^ 2 / width ν s))) := by
      rw [← eLpNorm_cellMeasure_eq hc0 hmeas hper]; exact hn
    have hK : 0 ≤ C j * width ν s ^ (-(5 + (j : ℝ)) / 2) * Real.exp (-(bb j * c ^ 2 / width ν s)) :=
      by have := hC j; positivity
    refine (qcT08_int_sq_le hm' hK hn').trans (le_of_eq ?_)
    rw [mul_pow, mul_pow]
    have e1 : (width ν s ^ (-(5 + (j : ℝ)) / 2)) ^ 2 = 1 / width ν s ^ (5 + j) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
      have : -(5 + (j : ℝ)) / 2 * ((2 : ℕ) : ℝ) = -((5 + j : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_neg ha0.le, Real.rpow_natCast, one_div]
    have e2 : Real.exp (-(bb j * c ^ 2 / width ν s)) ^ 2 =
        Real.exp (-(2 * bb j * c ^ 2 / width ν s)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e1, e2]; ring
  refine ⟨fun w k l => (key w.length w rfl k l).1, ?_⟩
  intro j hj
  have hjm : j ∈ Finset.range (N + 1) := Finset.mem_range.2 (by omega)
  have hint : ∀ w ∈ wordsOfLength j, ∀ k l : Fin 2,
      Integrable (fun z => B0151.derivWord w (fun x => Qc ν c s x k l) z ^ 2) (Cyl.cellμ c) :=
    fun w hw k l => (key j w (qcT08_mem_words.1 hw) k l).1.integrable_sq
  have hexp : Real.exp (-(2 * bb j * c ^ 2 / width ν s)) ≤ Real.exp (-(b * c ^ 2 / width ν s)) := by
    apply Real.exp_le_exp.2
    have : b * c ^ 2 / width ν s ≤ 2 * bb j * c ^ 2 / width ν s :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hble j hjm) (by positivity)) ha0.le
    linarith
  have hterm : ∀ w ∈ wordsOfLength j, ∀ k ∈ (Finset.univ : Finset (Fin 2)), ∀ l ∈ (Finset.univ : Finset (Fin 2)),
      ∫ z, B0151.derivWord w (fun x => Qc ν c s x k l) z ^ 2 ∂(Cyl.cellμ c) ≤
        C j ^ 2 / width ν s ^ (5 + j) * Real.exp (-(b * c ^ 2 / width ν s)) := by
    intro w hw k _ l _
    refine (key j w (qcT08_mem_words.1 hw) k l).2.trans ?_
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  have hmat : matEnergy c j (Qc ν c s) =
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∑ l : Fin 2,
        ∫ z, B0151.derivWord w (fun x => Qc ν c s x k l) z ^ 2 ∂(Cyl.cellμ c) := by
    unfold matEnergy
    change ∫ z, _ ∂(Cyl.cellμ c) = _
    rw [integral_finset_sum _ (fun w hw => ?_)]
    · refine Finset.sum_congr rfl fun w hw => ?_
      rw [integral_finset_sum _ (fun k _ => ?_)]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finset_sum _ (fun l _ => hint w hw k l)]
      · exact integrable_finset_sum _ fun l _ => hint w hw k l
    · exact integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ => hint w hw k l
  rw [hmat]
  have hsum : ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∑ l : Fin 2,
        ∫ z, B0151.derivWord w (fun x => Qc ν c s x k l) z ^ 2 ∂(Cyl.cellμ c) ≤
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2, ∑ l : Fin 2,
        C j ^ 2 / width ν s ^ (5 + j) * Real.exp (-(b * c ^ 2 / width ν s)) :=
    Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl =>
      hterm w hw k hk l hl
  refine hsum.trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcard : ((wordsOfLength j).card : ℝ) ≤ 2 ^ j := by exact_mod_cast qcT08_card_words j
  have hE := Real.exp_pos (-(b * c ^ 2 / width ν s))
  have hbig : 4 * 2 ^ j * C j ^ 2 ≤ ∑ i ∈ Finset.range (N + 1), 4 * 2 ^ i * C i ^ 2 :=
    Finset.single_le_sum (f := fun i => 4 * 2 ^ i * C i ^ 2) (fun i _ => by positivity) hjm
  have hP0 : 0 < width ν s ^ (5 + j) := by positivity
  calc (wordsOfLength j).card * ((2:ℕ) * ((2:ℕ) * (C j ^ 2 / width ν s ^ (5 + j) *
        Real.exp (-(b * c ^ 2 / width ν s)))))
      = ((wordsOfLength j).card : ℝ) * 4 * C j ^ 2 / width ν s ^ (5 + j) *
        Real.exp (-(b * c ^ 2 / width ν s)) := by push_cast; ring
    _ ≤ (4 * 2 ^ j * C j ^ 2) / width ν s ^ (5 + j) * Real.exp (-(b * c ^ 2 / width ν s)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        apply div_le_div_of_nonneg_right _ hP0.le
        nlinarith [sq_nonneg (C j)]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        exact div_le_div_of_nonneg_right hbig hP0.le

end UnforcedLeray.Short.PartI
