import UnforcedLeray.Short.PartI.Sub.PartI_T08_7_3_1_3
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.GN
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.JetWord
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.DerivFinite

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

/-- Pointwise jet bound by the sum of the coordinate words of length `j`. -/
lemma gnw_jet_le {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) (j : ℕ) (z : Plane) :
    ‖Train.jet j g z‖ ≤ ∑ w ∈ wordsOfLength j, ‖B0151.derivWord w g z‖ := by
  have h := (cylJetWord_proof g hg j z).2
  simpa [Real.norm_eq_abs] using h

/-- Squares of real numbers in the `rpow` form used by the `L²` integral. -/
lemma gnw_norm_rpow_two (x : ℝ) : ‖x‖ ^ (2:ℝ) = x * x := by
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs, sq]

/-- All jets lie in `L²(μ)` once all coordinate words do. -/
lemma gnw_jet_memLp {c : ℝ} {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g)
    (hL : ∀ w : List Bool, MemLp (B0151.derivWord w g) 2 (Cyl.cellμ c)) (j : ℕ) :
    MemLp (Train.jet j g) 2 (Cyl.cellμ c) := by
  have hF : MemLp (fun z => ∑ w ∈ wordsOfLength j, ‖B0151.derivWord w g z‖) 2 (Cyl.cellμ c) :=
    memLp_finsetSum (wordsOfLength j) (f := fun w z => ‖B0151.derivWord w g z‖)
      (fun w _ => (hL w).norm)
  refine MemLp.of_le hF ?_ ?_
  · exact (hg.continuous_iteratedFDeriv (m := j) (by simp)).aestronglyMeasurable
  · refine ae_of_all _ fun z => ?_
    have h0 : 0 ≤ ∑ w ∈ wordsOfLength j, ‖B0151.derivWord w g z‖ :=
      Finset.sum_nonneg fun w _ => norm_nonneg _
    show ‖Train.jet j g z‖ ≤ ‖∑ w ∈ wordsOfLength j, ‖B0151.derivWord w g z‖‖
    rw [Real.norm_of_nonneg h0]
    exact gnw_jet_le hg j z

/-- The cell `L²` norm of the `n`-jet, bounded by `2^n J^{1/2}` (Minkowski over the words). -/
lemma gnw_cellL2_le {c : ℝ} {g : Plane → ℝ} {J : ℝ} (n : ℕ) (hg : ContDiff ℝ ∞ g)
    (hA : ∀ w : List Bool, MemLp (B0151.derivWord w g) 2 (Cyl.cellμ c))
    (hJ : ∀ v : List Bool, v.length = n →
      ∫ z in Cyl.cell c, B0151.derivWord v g z * B0151.derivWord v g z ≤ J)
    (hJ0 : 0 ≤ J) :
    Train.cellL2 c (Train.jet n g) ≤ ENNReal.ofReal (2 ^ n * J ^ ((2:ℝ)⁻¹)) := by
  unfold Train.cellL2
  have hterm : ∀ w ∈ wordsOfLength n,
      eLpNorm (fun z => ‖B0151.derivWord w g z‖) 2 (Cyl.cellμ c) ≤
        ENNReal.ofReal (J ^ ((2:ℝ)⁻¹)) := by
    intro w hw
    rw [eLpNorm_norm]
    rw [(hA w).eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat]
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow (integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _) _
      (by norm_num)
    have hwl : w.length = n := mem_wordsOfLength_length hw
    calc ∫ z, ‖B0151.derivWord w g z‖ ^ (2:ℝ) ∂(Cyl.cellμ c)
        = ∫ z in Cyl.cell c, B0151.derivWord w g z * B0151.derivWord w g z :=
          integral_congr_ae (ae_of_all _ fun z => gnw_norm_rpow_two _)
      _ ≤ J := hJ w hwl
  calc eLpNorm (Train.jet n g) 2 (Cyl.cellμ c)
      ≤ eLpNorm (fun z => ∑ w ∈ wordsOfLength n, ‖B0151.derivWord w g z‖) 2 (Cyl.cellμ c) :=
        eLpNorm_mono_real (fun z => gnw_jet_le hg n z)
    _ = eLpNorm (∑ w ∈ wordsOfLength n, fun z => ‖B0151.derivWord w g z‖) 2 (Cyl.cellμ c) := by
        congr 1
        funext z
        simp [Finset.sum_apply]
    _ ≤ ∑ w ∈ wordsOfLength n, eLpNorm (fun z => ‖B0151.derivWord w g z‖) 2 (Cyl.cellμ c) :=
        eLpNorm_sum_le (fun w _ => (hA w).1.norm) one_le_two
    _ ≤ ∑ w ∈ wordsOfLength n, ENNReal.ofReal (J ^ ((2:ℝ)⁻¹)) :=
        Finset.sum_le_sum hterm
    _ = (wordsOfLength n).card • ENNReal.ofReal (J ^ ((2:ℝ)⁻¹)) := Finset.sum_const _
    _ = ((wordsOfLength n).card : ℝ≥0∞) * ENNReal.ofReal (J ^ ((2:ℝ)⁻¹)) := nsmul_eq_mul _ _
    _ ≤ ((2 ^ n : ℕ) : ℝ≥0∞) * ENNReal.ofReal (J ^ ((2:ℝ)⁻¹)) :=
        by gcongr; exact_mod_cast cgn_card_wordsOfLength n
    _ = ENNReal.ofReal (2 ^ n * J ^ ((2:ℝ)⁻¹)) := by
        rw [ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast]
        congr 1
        · norm_num
        
/-- **Target `MidGNWord`** (lines 355-357): the word form of the Gagliardo-Nirenberg inequality. -/
theorem midGNWord_proof : UnforcedLeray.Short.PartI.MidGNWord := by
  intro n hn
  have hG := cylGN_proof
  unfold CylGN at hG
  obtain ⟨Cn, hCn0, hCn⟩ := hG n hn
  have hD := cylDerivFinite_proof
  unfold CylDerivFinite at hD
  refine ⟨Cn * 2 ^ n, mul_nonneg hCn0 (by positivity), ?_⟩
  intro c hc g S J hS hJ0 hMA l hl1 hln u hu
  unfold MidAdm at hMA
  obtain ⟨hg, hper, hL, hGb, hJb⟩ := hMA
  have hMem : ∀ j : ℕ, MemLp (Train.jet j g) 2 (Cyl.cellμ c) := fun j => gnw_jet_memLp hg hL j
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl0 : (0:ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hlnR : (l:ℝ) ≤ n := by exact_mod_cast hln
  have hp0 : 0 < 2 * (n:ℝ) / l := by positivity
  have hp2 : (2:ℝ) ≤ 2 * (n:ℝ) / l := by
    rw [le_div_iff₀ hl0]
    linarith
  have hp2E : (2:ℝ≥0∞) ≤ ENNReal.ofReal (2 * (n:ℝ) / l) := by
    calc (2:ℝ≥0∞) = ENNReal.ofReal 2 := (ENNReal.ofReal_ofNat 2).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hp2
  have hDu : MemLp (B0151.derivWord u g) (ENNReal.ofReal (2 * (n:ℝ) / l)) (Cyl.cellμ c) :=
    (hD c hc g hg hper hMem u).2 _ hp2E
  have hLHS : eLpNorm (B0151.derivWord u g) (ENNReal.ofReal (2 * (n:ℝ) / l)) (Cyl.cellμ c) =
      ENNReal.ofReal ((∫ z, |B0151.derivWord u g z| ^ (2 * (n:ℝ) / l) ∂(Cyl.cellμ c)) ^
        ((l:ℝ) / (2 * n))) := by
    rw [hDu.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.2 hp0).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp0.le, inv_div]
    simp only [Real.norm_eq_abs]
  have hcell := gnw_cellL2_le (c := c) (g := g) (J := J) n hg hL hJb hJ0
  have hsup : (⨆ z, ‖g z‖ₑ) ≤ ENNReal.ofReal S := by
    refine iSup_le fun z => ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hGb z)
  have hGN := hCn c hc g hg hper hMem l hl1 hln
  have hx0 : 0 ≤ 1 - (l:ℝ) / n := by
    rw [sub_nonneg, div_le_one hn0]
    exact hlnR
  have hx1 : 0 ≤ (l:ℝ) / n := by positivity
  have hx1' : (l:ℝ) / n ≤ 1 := (div_le_one hn0).2 hlnR
  have hsupP : (⨆ z, ‖g z‖ₑ) ^ (1 - (l:ℝ) / n) ≤ ENNReal.ofReal (S ^ (1 - (l:ℝ) / n)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hS hx0]
    exact ENNReal.rpow_le_rpow hsup hx0
  have hJp : 0 ≤ 2 ^ n * J ^ ((2:ℝ)⁻¹) := mul_nonneg (by positivity) (Real.rpow_nonneg hJ0 _)
  have hcellP : Train.cellL2 c (Train.jet n g) ^ ((l:ℝ) / n) ≤
      ENNReal.ofReal ((2 ^ n * J ^ ((2:ℝ)⁻¹)) ^ ((l:ℝ) / n)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hJp hx1]
    exact ENNReal.rpow_le_rpow hcell hx1
  have hreal : Cn * S ^ (1 - (l:ℝ) / n) * ((2 ^ n * J ^ ((2:ℝ)⁻¹)) ^ ((l:ℝ) / n)) ≤
      Cn * 2 ^ n * (S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n))) := by
    have hsplit : (2 ^ n * J ^ ((2:ℝ)⁻¹)) ^ ((l:ℝ) / n) =
        ((2:ℝ) ^ n) ^ ((l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n)) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hJ0 _), ← Real.rpow_mul hJ0]
      congr 2
      ring
    have hpow : ((2:ℝ) ^ n) ^ ((l:ℝ) / n) ≤ 2 ^ n := by
      calc ((2:ℝ) ^ n) ^ ((l:ℝ) / n) ≤ ((2:ℝ) ^ n) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) hx1'
        _ = 2 ^ n := Real.rpow_one _
    rw [hsplit]
    have hA0 : 0 ≤ S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n)) :=
      mul_nonneg (Real.rpow_nonneg hS _) (Real.rpow_nonneg hJ0 _)
    calc Cn * S ^ (1 - (l:ℝ) / n) * (((2:ℝ) ^ n) ^ ((l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n)))
        = (Cn * ((2:ℝ) ^ n) ^ ((l:ℝ) / n)) * (S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n))) := by
          ring
      _ ≤ (Cn * 2 ^ n) * (S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCn0) hA0
      _ = Cn * 2 ^ n * (S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n))) := rfl
  have hY0 : 0 ≤ Cn * 2 ^ n * (S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n))) :=
    mul_nonneg (mul_nonneg hCn0 (by positivity))
      (mul_nonneg (Real.rpow_nonneg hS _) (Real.rpow_nonneg hJ0 _))
  have key : eLpNorm (B0151.derivWord u g) (ENNReal.ofReal (2 * (n:ℝ) / l)) (Cyl.cellμ c) ≤
      ENNReal.ofReal (Cn * 2 ^ n * (S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n)))) := by
    calc eLpNorm (B0151.derivWord u g) (ENNReal.ofReal (2 * (n:ℝ) / l)) (Cyl.cellμ c)
        ≤ eLpNorm (Train.jet l g) (ENNReal.ofReal (2 * (n:ℝ) / l)) (Cyl.cellμ c) :=
          eLpNorm_mono (fun z => by
            rw [Real.norm_eq_abs]
            exact (cylJetWord_proof g hg l z).1 u hu)
      _ ≤ ENNReal.ofReal Cn * (⨆ z, ‖g z‖ₑ) ^ (1 - (l:ℝ) / n) *
            Train.cellL2 c (Train.jet n g) ^ ((l:ℝ) / n) := hGN
      _ ≤ ENNReal.ofReal Cn * ENNReal.ofReal (S ^ (1 - (l:ℝ) / n)) *
            ENNReal.ofReal ((2 ^ n * J ^ ((2:ℝ)⁻¹)) ^ ((l:ℝ) / n)) :=
          by gcongr
      _ = ENNReal.ofReal (Cn * S ^ (1 - (l:ℝ) / n) * ((2 ^ n * J ^ ((2:ℝ)⁻¹)) ^ ((l:ℝ) / n))) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hCn0 (Real.rpow_nonneg hS _)),
            ENNReal.ofReal_mul hCn0]
      _ ≤ ENNReal.ofReal (Cn * 2 ^ n * (S ^ (1 - (l:ℝ) / n) * J ^ ((l:ℝ) / (2 * n)))) :=
          ENNReal.ofReal_le_ofReal hreal
  rw [hLHS] at key
  exact (ENNReal.ofReal_le_ofReal_iff hY0).1 key

end UnforcedLeray.Short.PartI
