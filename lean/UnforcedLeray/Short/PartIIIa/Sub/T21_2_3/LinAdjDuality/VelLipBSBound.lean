import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_4
import UnforcedLeray.Short.PartIIIa.T20_6_RealBiotSavartUniform
import UnforcedLeray.Short.PartIIIa.T20_2_BiotSavartUnique
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutLimit
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLipBSSub

/-!
# `PartIII-a:T21/2/3/1/4`, leaf 3: the Biot-Savart velocity of zero-circulation data

Source: `the November 2 reference manuscript` 3230-3240 (`eq:ct-embeddings`) and
2819-2830. For a zero-circulation `Ω ∈ X_{m,c}` (complex valued, `c ≥ 1`, `m > 8`) and any
Biot-Savart velocity `U` of `Ω`, `‖U_j‖₂ ≤ C ‖Ω‖_{X_{m,c}}` with `C` uniform in `c`.

Proof. Split `Ω = Re Ω + i Im Ω`; both parts are real zero-circulation `X_{m,c}` data, so
`CTE.realBiotSavartUniform` gives real Biot-Savart velocities `U_r, U_i` with
`velNorm ≤ C ‖·‖_{X_m}`. The combination `U_r + i U_i` is a Biot-Savart velocity of `Ω`
(`isBiotSavart_comb`), and by `CTE.isBiotSavart_unique` it agrees a.e. with `U`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- A.e. modification of the vorticity keeps the Biot-Savart relation. -/
lemma isBiotSavart_congr_ae {c : ℝ} {ωa ωb : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ}
    (h : IsBiotSavart c ωa u) (he : ωa =ᵐ[volume.restrict (B0579.cell c)] ωb) :
    IsBiotSavart c ωb u := by
  unfold IsBiotSavart at h ⊢
  refine ⟨h.1, h.2.1, fun ψ hψ => ?_⟩
  rw [← h.2.2 ψ hψ]
  refine integral_congr_ae ?_
  filter_upwards [he] with x hx
  rw [hx]

/-- Complex linear combinations of Biot-Savart pairs are Biot-Savart pairs. -/
lemma isBiotSavart_comb {c m : ℝ} {ω₁ ω₂ : ℝ × ℝ → ℂ} {u₁ u₂ : ℝ × ℝ → Fin 2 → ℂ}
    (h₁ : IsBiotSavart c ω₁ u₁) (h₂ : IsBiotSavart c ω₂ u₂)
    (hω₁ : MemLp ω₁ 2 (B0579.cellMeasure c m)) (hω₂ : MemLp ω₂ 2 (B0579.cellMeasure c m))
    (k : ℂ) :
    IsBiotSavart c (fun x => ω₁ x + k * ω₂ x) (fun x j => u₁ x j + k * u₂ x j) := by
  unfold IsBiotSavart at h₁ h₂ ⊢
  refine ⟨fun j => (h₁.1 j).add ((h₂.1 j).const_mul k), ?_, ?_⟩
  · intro ψ hψ
    have K1 := BSSubAux.integrable_u_pd h₁.1 hψ 0 0
    have K1' := BSSubAux.integrable_u_pd h₁.1 hψ 1 1
    have K2 := BSSubAux.integrable_u_pd h₂.1 hψ 0 0
    have K2' := BSSubAux.integrable_u_pd h₂.1 hψ 1 1
    have hA : Integrable (fun x => u₁ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        u₁ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := K1.add K1'
    have hB : Integrable (fun x => u₂ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        u₂ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := K2.add K2'
    have key : ∀ x, (u₁ x 0 + k * u₂ x 0) * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        (u₁ x 1 + k * u₂ x 1) * ((B0579.pd 1 ψ x : ℝ) : ℂ) =
        (u₁ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) + u₁ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) +
        k * (u₂ x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) + u₂ x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) := by
      intro x
      ring
    show ∫ x in B0579.cell c, ((u₁ x 0 + k * u₂ x 0) * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        (u₁ x 1 + k * u₂ x 1) * ((B0579.pd 1 ψ x : ℝ) : ℂ)) = 0
    simp only [key]
    rw [integral_add hA (hB.const_mul k), integral_const_mul, h₁.2.1 ψ hψ, h₂.2.1 ψ hψ]
    simp
  · intro ψ hψ
    have I1 := CutLimitAux.integrable_complex hω₁ (hψ.memLp (-m)).ofReal
    have I2 := CutLimitAux.integrable_complex hω₂ (hψ.memLp (-m)).ofReal
    have K1 := BSSubAux.integrable_u_pd h₁.1 hψ 0 1
    have K1' := BSSubAux.integrable_u_pd h₁.1 hψ 1 0
    have K2 := BSSubAux.integrable_u_pd h₂.1 hψ 0 1
    have K2' := BSSubAux.integrable_u_pd h₂.1 hψ 1 0
    have hA : Integrable (fun x => u₁ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₁ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := K1.sub K1'
    have hB : Integrable (fun x => u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) (volume.restrict (B0579.cell c)) := K2.sub K2'
    have hL : ∀ x, (ω₁ x + k * ω₂ x) * ((ψ x : ℝ) : ℂ) =
        ω₁ x * ((ψ x : ℝ) : ℂ) + k * (ω₂ x * ((ψ x : ℝ) : ℂ)) := fun x => by ring
    have hR : ∀ x, (u₁ x 0 + k * u₂ x 0) * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        (u₁ x 1 + k * u₂ x 1) * ((B0579.pd 0 ψ x : ℝ) : ℂ) =
        (u₁ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) - u₁ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) +
        k * (u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) - u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) :=
      fun x => by ring
    show ∫ x in B0579.cell c, (ω₁ x + k * ω₂ x) * ((ψ x : ℝ) : ℂ) =
      ∫ x in B0579.cell c, ((u₁ x 0 + k * u₂ x 0) * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        (u₁ x 1 + k * u₂ x 1) * ((B0579.pd 0 ψ x : ℝ) : ℂ))
    simp only [hL, hR]
    have I2k : Integrable (fun x => k * (ω₂ x * ((ψ x : ℝ) : ℂ))) (volume.restrict (B0579.cell c)) :=
      I2.const_mul k
    have hBk : Integrable (fun x => k * (u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ))) (volume.restrict (B0579.cell c)) := hB.const_mul k
    have e1 : ∫ x in B0579.cell c, (ω₁ x * ((ψ x : ℝ) : ℂ) + k * (ω₂ x * ((ψ x : ℝ) : ℂ))) =
        (∫ x in B0579.cell c, ω₁ x * ((ψ x : ℝ) : ℂ)) +
          ∫ x in B0579.cell c, k * (ω₂ x * ((ψ x : ℝ) : ℂ)) := integral_add I1 I2k
    have e2 : ∫ x in B0579.cell c, k * (ω₂ x * ((ψ x : ℝ) : ℂ)) =
        k * ∫ x in B0579.cell c, ω₂ x * ((ψ x : ℝ) : ℂ) := integral_const_mul k _
    have e3 : ∫ x in B0579.cell c, ((u₁ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₁ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) + k * (u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ))) =
        (∫ x in B0579.cell c, (u₁ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
          u₁ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ))) +
        ∫ x in B0579.cell c, k * (u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
          u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) := integral_add hA hBk
    have e4 : ∫ x in B0579.cell c, k * (u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) =
        k * ∫ x in B0579.cell c, (u₂ x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
          u₂ x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) := integral_const_mul k _
    rw [e1, e2, h₁.2.2 ψ hψ, h₂.2.2 ψ hψ, e3, e4]

/-- Components of a complex `L²` velocity are bounded by its `velNorm`. -/
lemma comp_le_velNorm (d : ℝ) (u : ℝ × ℝ → Fin 2 → ℂ) (j : Fin 2) :
    eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ≤ velNorm d u := by
  unfold velNorm
  have h1 : eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ^ 2 ≤
      ∑ i : Fin 2, eLpNorm (fun x => u x i) 2 (volume.restrict (B0579.cell d)) ^ 2 :=
    Finset.single_le_sum (f := fun i : Fin 2 =>
      eLpNorm (fun x => u x i) 2 (volume.restrict (B0579.cell d)) ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ j)
  calc eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d))
      = (eLpNorm (fun x => u x j) 2 (volume.restrict (B0579.cell d)) ^ 2) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow h1 (by norm_num)

/-- **Leaf 3** (SP 3230-3240): the Biot-Savart velocity of zero-circulation data is controlled by
its weighted norm, uniformly in the period (`m > 8`). -/
theorem ladBSBound (m : ℝ) (hm : 8 < m) : LadBSBound m := by
  obtain ⟨C, hC0, hC⟩ := CTE.realBiotSavartUniform m (by linarith)
  refine ⟨2 * C, fun c hc Ω hΩ hcirc U hU j => ?_⟩
  have hc0 : (0 : ℝ) < c := by linarith
  haveI : Fact (0 < c) := ⟨hc0⟩
  obtain ⟨hint, hz⟩ := hcirc
  have hre : MemLp (fun x => (Ω x).re) 2 (B0579.cellMeasure c m) := hΩ.re
  have him : MemLp (fun x => (Ω x).im) 2 (B0579.cellMeasure c m) := hΩ.im
  have hzre : ∫ x in B0579.cell c, (Ω x).re = 0 := by
    have h := integral_re hint
    simpa [hz] using h
  have hzim : ∫ x in B0579.cell c, (Ω x).im = 0 := by
    have h := integral_im hint
    simpa [hz] using h
  set ωr : B0579.X c m := hre.toLp (fun x => (Ω x).re) with hωr
  set ωi : B0579.X c m := him.toLp (fun x => (Ω x).im) with hωi
  have hωr_int : ∫ x in B0579.cell c, ωr x = 0 := by
    rw [integral_congr_ae ((B0579.ac_cellMeasure c m).ae_le hre.coeFn_toLp)]
    exact hzre
  have hωi_int : ∫ x in B0579.cell c, ωi x = 0 := by
    rw [integral_congr_ae ((B0579.ac_cellMeasure c m).ae_le him.coeFn_toLp)]
    exact hzim
  obtain ⟨Ur, hUr, hUr_v⟩ := hC c hc ωr hωr_int
  obtain ⟨Ui, hUi, hUi_v⟩ := hC c hc ωi hωi_int
  have hUr' : IsBiotSavart c (fun x => (((Ω x).re : ℝ) : ℂ)) Ur := by
    refine isBiotSavart_congr_ae hUr ?_
    filter_upwards [(B0579.ac_cellMeasure c m).ae_le hre.coeFn_toLp] with x hx
    show ((ωr x : ℝ) : ℂ) = (((Ω x).re : ℝ) : ℂ)
    rw [hx]
  have hUi' : IsBiotSavart c (fun x => (((Ω x).im : ℝ) : ℂ)) Ui := by
    refine isBiotSavart_congr_ae hUi ?_
    filter_upwards [(B0579.ac_cellMeasure c m).ae_le him.coeFn_toLp] with x hx
    show ((ωi x : ℝ) : ℂ) = (((Ω x).im : ℝ) : ℂ)
    rw [hx]
  have hcomb := isBiotSavart_comb hUr' hUi' hre.ofReal him.ofReal Complex.I
  have hΩeq : (fun x => (((Ω x).re : ℝ) : ℂ) + Complex.I * (((Ω x).im : ℝ) : ℂ)) = Ω := by
    funext x
    apply Complex.ext <;> simp
  rw [hΩeq] at hcomb
  have huniq := CTE.isBiotSavart_unique c hc0 Ω U _ hU hcomb
  have hU_eq : eLpNorm (fun x => U x j) 2 (volume.restrict (B0579.cell c)) =
      eLpNorm (fun x => Ur x j + Complex.I * Ui x j) 2 (volume.restrict (B0579.cell c)) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [huniq] with x hx
    simp only [hx]
  have hmin : eLpNorm (fun x => Ur x j + Complex.I * Ui x j) 2 (volume.restrict (B0579.cell c)) ≤
      eLpNorm (fun x => Ur x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => Ui x j) 2 (volume.restrict (B0579.cell c)) := by
    have h := eLpNorm_add_le ((hUr.1 j).aestronglyMeasurable)
      ((hUi.1 j).aestronglyMeasurable.const_mul Complex.I) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have h2 : eLpNorm (fun x => Complex.I * Ui x j) 2 (volume.restrict (B0579.cell c)) ≤
        eLpNorm (fun x => Ui x j) 2 (volume.restrict (B0579.cell c)) :=
      eLpNorm_mono fun x => by simp
    exact h.trans (add_le_add_right h2 _)
  have hfin : xNorm c m Ω ≠ ⊤ := hΩ.eLpNorm_lt_top.ne
  have hnorm_re : ‖ωr‖ ≤ (xNorm c m Ω).toReal := by
    have hle' : eLpNorm (fun x => (Ω x).re) 2 (B0579.cellMeasure c m) ≤ xNorm c m Ω :=
      eLpNorm_mono fun x => by simpa using Complex.abs_re_le_norm (Ω x)
    rw [Lp.norm_def, eLpNorm_congr_ae hre.coeFn_toLp]
    exact ENNReal.toReal_mono hfin hle'
  have hnorm_im : ‖ωi‖ ≤ (xNorm c m Ω).toReal := by
    have hle' : eLpNorm (fun x => (Ω x).im) 2 (B0579.cellMeasure c m) ≤ xNorm c m Ω :=
      eLpNorm_mono fun x => by simpa using Complex.abs_im_le_norm (Ω x)
    rw [Lp.norm_def, eLpNorm_congr_ae him.coeFn_toLp]
    exact ENNReal.toReal_mono hfin hle'
  have hnr : ENNReal.ofReal (C * ‖ωr‖) ≤ ENNReal.ofReal C * xNorm c m Ω := by
    rw [ENNReal.ofReal_mul hC0]
    gcongr
    exact (ENNReal.ofReal_le_ofReal hnorm_re).trans_eq (ENNReal.ofReal_toReal hfin)
  have hni : ENNReal.ofReal (C * ‖ωi‖) ≤ ENNReal.ofReal C * xNorm c m Ω := by
    rw [ENNReal.ofReal_mul hC0]
    gcongr
    exact (ENNReal.ofReal_le_ofReal hnorm_im).trans_eq (ENNReal.ofReal_toReal hfin)
  rw [hU_eq]
  calc eLpNorm (fun x => Ur x j + Complex.I * Ui x j) 2 (volume.restrict (B0579.cell c))
      ≤ eLpNorm (fun x => Ur x j) 2 (volume.restrict (B0579.cell c)) +
        eLpNorm (fun x => Ui x j) 2 (volume.restrict (B0579.cell c)) := hmin
    _ ≤ velNorm c Ur + velNorm c Ui := add_le_add (comp_le_velNorm c Ur j) (comp_le_velNorm c Ui j)
    _ ≤ ENNReal.ofReal (C * ‖ωr‖) + ENNReal.ofReal (C * ‖ωi‖) := add_le_add hUr_v hUi_v
    _ ≤ ENNReal.ofReal C * xNorm c m Ω + ENNReal.ofReal C * xNorm c m Ω := add_le_add hnr hni
    _ = ENNReal.ofReal (2 * C) * xNorm c m Ω := by
        rw [← add_mul, ← ENNReal.ofReal_add hC0 hC0]
        congr 2
        ring

end UnforcedLeray.Short.IIIa
