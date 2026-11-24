import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9_1_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.PairCont
import UnforcedLeray.Units.B0610

/-!
# Circulation repair for the test approximants (`LadDensCircFix`)

Source: `the November 2 reference manuscript` lines 3230-3240 and 3052-3058.

Replaces the stale leaf `PartIII-a:T21/2/3/1/9/1/2` (`LadCircFix`, not defined on disk): the content
of that leaf is `LadDensCircFix` of `Sub/PartIII-a_T21_2_3_1_9_1_1.lean`, proved here.

Proof. `β = χ / ∫_cell χ` for the fixed cylinder bump `χ = ladCut 1`; `a' = a - (∫a) β`,
`b' = b - (∫b) β`. As `w` has zero circulation, `∫a + i ∫b = ∫ (a + i b - w)`, and by weighted
Cauchy-Schwarz against `1 ∈ X_{-m}` (`m > 1`) its modulus is at most `K ‖a + i b - w‖_{X_m}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CircFixAux

lemma isCylTest_sub_smul {c : ℝ} {φ χ : ℝ × ℝ → ℝ} (hφ : B0579.IsCylTest c φ)
    (hχ : B0579.IsCylTest c χ) (k : ℝ) :
    B0579.IsCylTest c (fun x => φ x - k * χ x) where
  smooth := hφ.smooth.sub (contDiff_const.mul hχ.smooth)
  periodic x := by simp only [hφ.periodic x, hχ.periodic x]
  band := by
    obtain ⟨R, hR⟩ := hφ.band
    obtain ⟨R', hR'⟩ := hχ.band
    refine ⟨max R R', fun x hx => ?_⟩
    rw [hR x (lt_of_le_of_lt (le_max_left _ _) hx), hR' x (lt_of_le_of_lt (le_max_right _ _) hx)]
    simp

lemma isCylTest_const_mul {c : ℝ} {χ : ℝ × ℝ → ℝ} (hχ : B0579.IsCylTest c χ) (k : ℝ) :
    B0579.IsCylTest c (fun x => k * χ x) where
  smooth := contDiff_const.mul hχ.smooth
  periodic x := by simp only [hχ.periodic x]
  band := by
    obtain ⟨R', hR'⟩ := hχ.band
    exact ⟨R', fun x hx => by rw [hR' x hx]; simp⟩

lemma cut_integral_pos (c : ℝ) (hc : 0 < c) :
    0 < ∫ x in B0579.cell c, ladCut 1 x := by
  obtain ⟨K, -, hK⟩ := ladCutProps
  obtain ⟨hT, h01, h1, -⟩ := hK 1 one_pos
  have hint : IntegrableOn (ladCut 1) (B0579.cell c) := (hT c).integrableOn
  set S : Set (ℝ × ℝ) := Ico (-(c / 2)) (c / 2) ×ˢ Icc (-1) 1 with hS
  have hSsub : S ⊆ B0579.cell c := fun x hx => ⟨hx.1, mem_univ _⟩
  have hSm : MeasurableSet S := measurableSet_Ico.prod measurableSet_Icc
  have h1' : ∫ x in S, ladCut 1 x = ∫ x in S, (1 : ℝ) := by
    refine setIntegral_congr_fun hSm (fun x hx => ?_)
    apply h1
    have := hx.2
    nlinarith [this.1, this.2]
  have hvol : ∫ x in S, (1 : ℝ) = c * 2 := by
    rw [setIntegral_const, hS, Measure.real, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Ico, Real.volume_Icc, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by norm_num)]
    simp only [smul_eq_mul, mul_one]
    ring
  have hmono : ∫ x in S, ladCut 1 x ≤ ∫ x in B0579.cell c, ladCut 1 x :=
    setIntegral_mono_set hint (Eventually.of_forall (fun x => (h01 x).1))
      (Eventually.of_forall hSsub)
  linarith

end CircFixAux

open CircFixAux in
theorem ladDensCircFix (m : ℝ) (hm : 8 < m) : LadDensCircFix m := by
  intro c hc
  have hm' : 1 / 2 < m := by linarith
  have hc0 : 0 < c := by linarith
  obtain ⟨K0, -, hK0⟩ := ladCutProps
  obtain ⟨hχT, -, -, -⟩ := hK0 1 one_pos
  set χ := ladCut 1 with hχdef
  have hχ : B0579.IsCylTest c χ := hχT c
  set I := ∫ x in B0579.cell c, χ x with hIdef
  have hI : 0 < I := cut_integral_pos c hc0
  set β : ℝ × ℝ → ℝ := fun x => I⁻¹ * χ x with hβdef
  have hβ : B0579.IsCylTest c β := isCylTest_const_mul hχ _
  have hβ1 : ∫ x in B0579.cell c, β x = 1 := by
    rw [hβdef]; simp only
    rw [integral_const_mul, ← hIdef]; field_simp
  have hβC : MemLp (fun x => ((β x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := (hβ.memLp m).ofReal
  have hone : MemLp (fun _ : ℝ × ℝ => ((1 : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m)) :=
    (B0610.memLp_one_neg (c := c) (m := m) hm').ofReal
  set K : ℝ := (eLpNorm (fun _ : ℝ × ℝ => ((1 : ℝ) : ℂ)) 2 (B0579.cellMeasure c (-m))).toReal
    with hKdef
  have hK : 0 ≤ K := ENNReal.toReal_nonneg
  set B : ℝ := (eLpNorm (fun x => ((β x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m)).toReal with hBdef
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  refine ⟨1 + K * B, fun w hw hz a b ha hb => ?_⟩
  set ea : ℝ := ∫ x in B0579.cell c, a x with hea
  set eb : ℝ := ∫ x in B0579.cell c, b x with heb
  refine ⟨fun x => a x - ea * β x, fun x => b x - eb * β x,
    isCylTest_sub_smul ha hβ _, isCylTest_sub_smul hb hβ _,
    (isCylTest_sub_smul ha hβ _).integrableOn, (isCylTest_sub_smul hb hβ _).integrableOn,
    ?_, ?_, ?_⟩
  · rw [integral_sub ha.integrableOn (hβ.integrableOn.const_mul _), integral_const_mul, hβ1]
    simp [hea]
  · rw [integral_sub hb.integrableOn (hβ.integrableOn.const_mul _), integral_const_mul, hβ1]
    simp [heb]
  -- norm estimate
  set g1 : ℝ × ℝ → ℂ := fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ) - w x with hg1
  set z : ℂ := (ea : ℂ) + Complex.I * (eb : ℂ) with hz'
  have hg1m : MemLp g1 2 (B0579.cellMeasure c m) :=
    (TranspApproxAux.memLp_comb ha hb).sub hw
  have hfun : (fun x => ((a x - ea * β x : ℝ) : ℂ) + Complex.I * ((b x - eb * β x : ℝ) : ℂ) -
      w x) = fun x => g1 x - z * ((β x : ℝ) : ℂ) := by
    funext x; simp only [hg1, hz']; push_cast; ring
  -- the complex number `z` is the circulation of `g1`
  have hia : IntegrableOn (fun x => ((a x : ℝ) : ℂ)) (B0579.cell c) := ha.integrableOn.ofReal
  have hib : IntegrableOn (fun x => ((b x : ℝ) : ℂ)) (B0579.cell c) := hb.integrableOn.ofReal
  have hab : IntegrableOn (fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ)) (B0579.cell c) :=
    hia.add (hib.const_mul Complex.I)
  have hzint : ∫ x in B0579.cell c, g1 x = z := by
    have : ∫ x in B0579.cell c, (((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ) - w x) =
        (∫ x in B0579.cell c, (((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ))) -
          ∫ x in B0579.cell c, w x := integral_sub hab hz.1
    simp only [hg1]
    rw [this, hz.2, sub_zero, integral_add hia (hib.const_mul Complex.I), integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal]
  have hhold := PairContAux.holder hg1m hone
  have hzbd : ‖z‖ ≤ K * (xNorm c m g1).toReal := by
    have := hhold.2
    simp only [Complex.ofReal_one, mul_one] at this
    rw [hzint] at this
    rw [hKdef, mul_comm]
    simpa [xNorm] using this
  have hN : xNorm c m g1 ≠ ⊤ := hg1m.2.ne
  have hBtop : eLpNorm (fun x => ((β x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) ≠ ⊤ := hβC.2.ne
  have hstep : xNorm c m (fun x => ((a x - ea * β x : ℝ) : ℂ) +
      Complex.I * ((b x - eb * β x : ℝ) : ℂ) - w x) ≤
      xNorm c m g1 + ‖z‖ₑ * eLpNorm (fun x => ((β x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := by
    unfold xNorm
    rw [hfun]
    refine (eLpNorm_sub_le hg1m.1 ((hβC.1).const_mul z) (by norm_num)).trans ?_
    refine add_le_add le_rfl (le_of_eq ?_)
    have : (fun x => z * ((β x : ℝ) : ℂ)) = z • (fun x => ((β x : ℝ) : ℂ)) := by
      funext x; simp
    rw [this, eLpNorm_const_smul]
  refine hstep.trans ?_
  have hzE : ‖z‖ₑ ≤ ENNReal.ofReal K * xNorm c m g1 := by
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖z‖ ≤ ENNReal.ofReal (K * (xNorm c m g1).toReal) :=
          ENNReal.ofReal_le_ofReal hzbd
      _ = ENNReal.ofReal K * xNorm c m g1 := by
          rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_toReal hN]
  have hBE : eLpNorm (fun x => ((β x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) = ENNReal.ofReal B := by
    rw [hBdef, ENNReal.ofReal_toReal hBtop]
  rw [hBE]
  calc xNorm c m g1 + ‖z‖ₑ * ENNReal.ofReal B
      ≤ xNorm c m g1 + (ENNReal.ofReal K * xNorm c m g1) * ENNReal.ofReal B :=
        add_le_add le_rfl (mul_le_mul_left hzE _)
    _ = ENNReal.ofReal (1 + K * B) * xNorm c m g1 := by
        rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hK hB), ENNReal.ofReal_mul hK,
          ENNReal.ofReal_one]
        ring

/-- The (stale) leaf predicate `LadCircFix` is the circulation-repair leaf `LadDensCircFix`. -/
abbrev LadCircFix (m : ℝ) : Prop := LadDensCircFix m

theorem ladCircFix (m : ℝ) (hm : 8 < m) : LadCircFix m := ladDensCircFix m hm

end UnforcedLeray.Short.IIIa
