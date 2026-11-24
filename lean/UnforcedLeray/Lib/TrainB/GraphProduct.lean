import UnforcedLeray.Lib.TrainB.SmoothProduct

/-!
# Smooth scalar H³ product bound on the periodic cylinder

The wordwise Leibniz estimate is assembled into the actual Sobolev graph norm, retaining the
ordered-word indexing of `Sob.Idx`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)

/-- Smooth scalar cylinder fields form an algebra in the actual order-three graph norm. The
coefficient is expressed through the exact eightfold component bound from `SmoothProduct`. -/
theorem smooth_h3_scalar_mul_norm {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1])
      (fun z => f z * g z) (IsCylSmooth.mul hf hg)‖ ≤
      4 * ((smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg).toReal) := by
  let hc : 0 < c := by linarith [hc1]
  let x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf
  let y := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg
  let z := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc (fun z => f z * g z) (IsCylSmooth.mul hf hg)
  let E : ℝ≥0∞ := smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg +
        smoothH3ProductFactor hc1 hf hg + smoothH3ProductFactor hc1 hf hg
  have hKtop : smoothH3ProductFactor hc1 hf hg ≠ ⊤ := by
    unfold smoothH3ProductFactor
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hEtop : E ≠ ⊤ := by
    simp [E, ENNReal.add_ne_top, hKtop]
  have hcomponent : ∀ α : UnforcedLeray.Sob.Idx 2 3,
      ‖UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
        (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 α z‖ ≤ E.toReal := by
    intro α
    let w := UnforcedLeray.Sob.Idx.toList α
    have hw : w.length ≤ 3 := by
      simp only [w, UnforcedLeray.Sob.Idx.length_toList]
      omega
    have hword : (UnforcedLeray.Sob.cylinder c).word α =
        w.map UnforcedLeray.Sob.cylDir := by
      rw [UnforcedLeray.Sob.TestDomain.word_eq_map]
      rfl
    have hdir := smooth_h3_iterD_mul_eLp_bound hc1 hf hg w hw
    rw [← UnforcedLeray.TrainB.scalarH2_measure_eq_cell c] at hdir
    have hAE := UnforcedLeray.Sob.W.deriv_ofCylSmooth
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      hc (fun z => f z * g z) (IsCylSmooth.mul hf hg) α
    let v := UnforcedLeray.Sob.W.deriv (UnforcedLeray.Sob.cylinder c)
      (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) ℝ ℝ 3 2 α z
    rw [UnforcedLeray.Sob.W.deriv_apply] at hAE
    have hAE' : (v : Plane → ℝ) =ᵐ[UnforcedLeray.Sob.wμ
        (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))]
        UnforcedLeray.Sob.iterD (w.map UnforcedLeray.Sob.cylDir) (fun z => f z * g z) := by
      dsimp [v, z]
      simpa [hword] using hAE
    have hvbound : eLpNorm (v : Plane → ℝ) 2
        (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) ≤ E := by
      calc
        _ = eLpNorm (UnforcedLeray.Sob.iterD (w.map UnforcedLeray.Sob.cylDir)
            (fun z => f z * g z)) 2 (UnforcedLeray.Sob.wμ
              (UnforcedLeray.Sob.cylinder c).μ (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) :=
          eLpNorm_congr_ae hAE'
        _ ≤ E := by simpa [E] using hdir
    have hvfin := (Lp.memLp v).eLpNorm_ne_top
    have hveq : eLpNorm (v : Plane → ℝ) 2
        (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder c).μ
          (UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ))) = ENNReal.ofReal ‖v‖ := by
      rw [← ENNReal.ofReal_toReal hvfin, Lp.norm_def]
    have hnorm := ENNReal.toReal_mono hEtop hvbound
    rw [hveq] at hnorm
    rw [UnforcedLeray.Sob.W.deriv_apply]
    have hnorm' := hnorm
    rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hnorm'
    simpa [v, UnforcedLeray.Sob.W.deriv_apply] using hnorm'
  have hEreal : 0 ≤ E.toReal := ENNReal.toReal_nonneg
  have hsum : ‖z‖ ^ 2 ≤ 16 * E.toReal ^ 2 := by
    rw [UnforcedLeray.Sob.W.norm_sq]
    calc
      _ ≤ ∑ _α : UnforcedLeray.Sob.Idx 2 3, E.toReal ^ 2 := by
        refine Finset.sum_le_sum fun α _ => ?_
        have hsquare := mul_le_mul (hcomponent α) (hcomponent α)
          (norm_nonneg _) hEreal
        simpa [pow_two] using hsquare
      _ = (Fintype.card (UnforcedLeray.Sob.Idx 2 3) : ℝ) * E.toReal ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ 16 * E.toReal ^ 2 := by
        have hcard : Fintype.card (UnforcedLeray.Sob.Idx 2 3) ≤ 16 := by
          norm_num [UnforcedLeray.Sob.Idx, Fintype.card_sigma, Fintype.card_fun,
            Fin.sum_univ_succ]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg E.toReal)
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have hnorm : ‖z‖ ≤ 4 * E.toReal := by nlinarith [sq_nonneg (‖z‖ - 4 * E.toReal)]
  simpa [z, E] using hnorm

#print axioms UnforcedLeray.TrainB.smooth_h3_scalar_mul_norm

end UnforcedLeray.TrainB

namespace UnforcedLeray.TrainB

open UnforcedLeray.GaussianVortex (Plane)

/-- Explicit form of the smooth scalar H³ algebra estimate. -/
theorem smooth_h3_scalar_mul_norm_explicit {c : ℝ} (hc1 : 1 ≤ c) {f g : Plane → ℝ}
    (hf : UnforcedLeray.Sob.IsCylSmooth c f) (hg : UnforcedLeray.Sob.IsCylSmooth c g) :
    ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
      (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1])
      (fun z => f z * g z) (IsCylSmooth.mul hf hg)‖ ≤
      384 * ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
        (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) f hf‖ *
        ‖UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
          (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) (by linarith [hc1]) g hg‖ := by
  let hc : 0 < c := by linarith [hc1]
  let x := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc f hf
  let y := UnforcedLeray.Sob.W.ofCylSmooth (𝕜 := ℝ) (F := ℝ) (k := 3) (p := 2)
    (ρ := UnforcedLeray.Cyl.ρwW c ^ (0 : ℝ)) hc g hg
  let K := smoothH3ProductFactor hc1 hf hg
  let E : ℝ≥0∞ := K + K + K + K + K + K + K + K
  have hbound := smooth_h3_scalar_mul_norm hc1 hf hg
  have hKtop : K ≠ ⊤ := by
    dsimp [K, smoothH3ProductFactor]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h2top : K + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hKtop, hKtop⟩
  have h3top : K + K + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h2top, hKtop⟩
  have h4top : K + K + K + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h3top, hKtop⟩
  have h5top : K + K + K + K + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h4top, hKtop⟩
  have h6top : K + K + K + K + K + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h5top, hKtop⟩
  have h7top : K + K + K + K + K + K + K ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨h6top, hKtop⟩
  have hEreal : E.toReal = 8 * K.toReal := by
    dsimp [E]
    rw [ENNReal.toReal_add h7top hKtop, ENNReal.toReal_add h6top hKtop,
      ENNReal.toReal_add h5top hKtop, ENNReal.toReal_add h4top hKtop,
      ENNReal.toReal_add h3top hKtop, ENNReal.toReal_add h2top hKtop,
      ENNReal.toReal_add hKtop hKtop]
    ring
  have hKreal : K.toReal = 12 * ‖x‖ * ‖y‖ := by
    dsimp [K, smoothH3ProductFactor]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (norm_nonneg _)]
  have hcoeff : 4 * E.toReal = 384 * ‖x‖ * ‖y‖ := by
    rw [hEreal, hKreal]
    ring
  calc
    _ ≤ 4 * E.toReal := by simpa [E] using hbound
    _ = 384 * ‖x‖ * ‖y‖ := hcoeff

#print axioms UnforcedLeray.TrainB.smooth_h3_scalar_mul_norm_explicit

end UnforcedLeray.TrainB
