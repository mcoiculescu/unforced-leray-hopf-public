import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_3_1_1_org.Leaf2Duality.Assembly
import UnforcedLeray.Lib.SobolevC.CylDensity

/-!
# Leaf (`PartIII-a:T21/c3/3/1/1/2/2/2/3`): `CylDataDense`

Source of record: `the November 2 reference manuscript` (SP), lines 2937–2958,
3036–3060.

Proves `CylDataDense`: for `c > 0`, `a ≥ 1`, `m ≥ 0`, complex cylinder data
`movCx a f₁ f₂ = J_a⁻¹ f₁ + i J_a⁻¹ f₂` with `f₁, f₂` smooth `c`-periodic band-limited real
cylinder tests (`B0579.IsCylTest c`) are dense in `X_{m, c/√a}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

namespace ComplFreeRateSub

namespace Leaf2DualityNeeded

namespace CylDataDenseAux

private def jbWeight (m : ℝ) : UnforcedLeray.Sob.Weight (ℝ × ℝ) :=
  UnforcedLeray.Sob.Weight.ofContinuous (fun x => B0579.jb x ^ m)
    (B0579.continuous_jb_rpow m)
    (fun x => Real.rpow_pos_of_pos (B0579.jb_pos x) m)

private theorem wμ_jbWeight_eq (d m : ℝ) :
    UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder d).μ (jbWeight m) = B0579.cellMeasure d m := by
  simp [UnforcedLeray.Sob.wμ, UnforcedLeray.Sob.cylinder, UnforcedLeray.Sob.cylCell,
    jbWeight, B0579.cellMeasure, B0579.cell, B0579.density, ENNReal.ofReal]

private theorem idx20_eq_zero (α : UnforcedLeray.Sob.Idx 2 0) :
    α = UnforcedLeray.Sob.Idx.zero := by
  rcases α with ⟨j, w⟩
  have hj : j = 0 := by omega
  subst j
  have hw : w = fun i => Fin.elim0 i := by
    funext i
    exact Fin.elim0 i
  subst w
  rfl

private theorem word_zero_eq (d : ℝ) :
    (UnforcedLeray.Sob.cylinder d).word
      (UnforcedLeray.Sob.Idx.zero : UnforcedLeray.Sob.Idx 2 0) = [] := by
  simp [UnforcedLeray.Sob.TestDomain.word, UnforcedLeray.Sob.Idx.zero]

private theorem isCylTest_of_isCylSmooth {d : ℝ} {h : B0579.Plane → ℝ}
    (hh : UnforcedLeray.Sob.IsCylSmooth d h) : B0579.IsCylTest d h where
  smooth := hh.smooth
  periodic x := by
    have hx : (x.1 + d, x.2) = x + (d, 0) := by ext <;> simp
    rw [hx]
    exact hh.periodic x
  band := hh.bounded

private theorem real_cylData_dense {d m : ℝ} (hd : 0 < d) {u : B0579.Plane → ℝ}
    (hu : MemLp u 2 (B0579.cellMeasure d m)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : B0579.Plane → ℝ, B0579.IsCylTest d h ∧
      eLpNorm (u - h) 2 (B0579.cellMeasure d m) < ENNReal.ofReal δ := by
  have huW : MemLp u 2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder d).μ (jbWeight m)) := by
    rwa [wμ_jbWeight_eq]
  have hweak : ∀ α : UnforcedLeray.Sob.Idx 2 0,
      UnforcedLeray.Sob.HasWeakDeriv (UnforcedLeray.Sob.cylinder d)
        ((UnforcedLeray.Sob.cylinder d).word α) u u := by
    intro α
    rw [idx20_eq_zero α, word_zero_eq d]
    exact UnforcedLeray.Sob.HasWeakDeriv.nil fun φ hφ =>
      UnforcedLeray.Sob.integrable_smul_of_memLp
        (UnforcedLeray.Sob.CompactlyBounded.of_adm hφ) huW
  let x0 : UnforcedLeray.Sob.W (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 :=
    UnforcedLeray.Sob.W.ofFields (fun _ => u) (fun _ => huW) hweak
  obtain ⟨y, hy, hlim⟩ := UnforcedLeray.Sob.W.exists_seq_cylSmooth
    (c := d) (ρ := jbWeight m) (𝕜 := ℝ) (F := ℝ) (k := 0) (p := 2) hd (by norm_num) x0
  choose h hh hrep using hy
  have hval : Tendsto
      (fun n => UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 (y n))
      atTop
      (𝓝 (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 x0)) :=
    ((UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2).continuous.tendsto
      x0).comp hlim
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at hval
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := ENNReal.ofReal_pos.mpr (half_pos hδ)
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp hval _ hpos).exists
  have hy_ae :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 (y n) :
        ℝ × ℝ → ℝ) =ᵐ[UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder d).μ (jbWeight m)] h n :=
    (UnforcedLeray.Sob.ae_eq_wμ_iff (UnforcedLeray.Sob.cylinder d).μ (jbWeight m)).mpr (hrep n)
  have hx0_ae :
      (UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 x0 :
        ℝ × ℝ → ℝ) =ᵐ[UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder d).μ (jbWeight m)] u := by
    change (huW.toLp u : ℝ × ℝ → ℝ) =ᵐ[_] u
    exact huW.coeFn_toLp
  have hsub_ae :
      (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 (y n)) -
        ⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 x0)) =ᵐ[
          UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder d).μ (jbWeight m)] (h n - u) :=
    hy_ae.sub hx0_ae
  have hneg : h n - u = -(u - h n) := by
    funext z
    simp [neg_sub]
  have hnorm_eq :
      eLpNorm (u - h n) 2 (B0579.cellMeasure d m) =
        eLpNorm
          (⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 (y n)) -
            ⇑(UnforcedLeray.Sob.W.value (UnforcedLeray.Sob.cylinder d) (jbWeight m) ℝ ℝ 0 2 x0))
          2 (UnforcedLeray.Sob.wμ (UnforcedLeray.Sob.cylinder d).μ (jbWeight m)) := by
    rw [eLpNorm_congr_ae hsub_ae, wμ_jbWeight_eq, hneg, eLpNorm_neg]
  refine ⟨h n, isCylTest_of_isCylSmooth (hh n), ?_⟩
  rw [hnorm_eq]
  exact lt_of_le_of_lt hn ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (half_lt_self hδ))

private def unscaleTest (a : ℝ) (h : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  (a ^ 2)⁻¹ * h (x.1 / Real.sqrt a, x.2 / Real.sqrt a)

private theorem isCylTest_unscaleTest {c a : ℝ} (ha : 0 < a) {h : B0579.Plane → ℝ}
    (hh : B0579.IsCylTest (cellLen c a) h) : B0579.IsCylTest c (unscaleTest a h) where
  smooth := by
    unfold unscaleTest
    exact contDiff_const.mul (hh.smooth.comp
      ((contDiff_fst.div_const (Real.sqrt a)).prodMk (contDiff_snd.div_const (Real.sqrt a))))
  periodic x := by
    unfold unscaleTest cellLen at *
    rw [add_div]
    rw [hh.periodic (x.1 / Real.sqrt a, x.2 / Real.sqrt a)]
  band := by
    have hsq : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
    obtain ⟨R, hR⟩ := hh.band
    refine ⟨max R 0 * Real.sqrt a, fun x hx => ?_⟩
    unfold unscaleTest
    have hx' : R < |(x.1 / Real.sqrt a, x.2 / Real.sqrt a).2| := by
      simp only [abs_div, abs_of_pos hsq]
      exact (le_max_left R 0).trans_lt ((lt_div_iff₀ hsq).mpr hx)
    rw [hR _ hx', mul_zero]

private theorem movCx_unscaleTest {a : ℝ} (ha : 0 < a) (h₁ h₂ : B0579.Plane → ℝ) (y : ℝ × ℝ) :
    movCx a (unscaleTest a h₁) (unscaleTest a h₂) y =
      ((h₁ y : ℝ) : ℂ) + Complex.I * ((h₂ y : ℝ) : ℂ) := by
  have hsq : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  have h1 : unscaleTest a h₁ (Real.sqrt a * y.1, Real.sqrt a * y.2) = (a ^ 2)⁻¹ * h₁ y := by
    unfold unscaleTest
    rw [mul_div_cancel_left₀ _ hsq, mul_div_cancel_left₀ _ hsq]
  have h2 : unscaleTest a h₂ (Real.sqrt a * y.1, Real.sqrt a * y.2) = (a ^ 2)⁻¹ * h₂ y := by
    unfold unscaleTest
    rw [mul_div_cancel_left₀ _ hsq, mul_div_cancel_left₀ _ hsq]
  have hmov := congrFun (movCx_eq_JscaleInv a (unscaleTest a h₁) (unscaleTest a h₂)) y
  rw [hmov]
  unfold JscaleInv
  dsimp only
  rw [h1, h2, Complex.ofReal_mul, Complex.ofReal_mul]
  have ha2C : ((a ^ 2 : ℝ) : ℂ) * (((a ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ ha2, Complex.ofReal_one]
  linear_combination (((h₁ y : ℝ) : ℂ) + Complex.I * ((h₂ y : ℝ) : ℂ)) * ha2C

private theorem eLpNorm_complex_ofReal {μ : Measure B0579.Plane} (w : B0579.Plane → ℝ) :
    eLpNorm (fun y => ((w y : ℝ) : ℂ)) 2 μ = eLpNorm w 2 μ := by
  rw [← eLpNorm_norm (fun y => ((w y : ℝ) : ℂ)), ← eLpNorm_norm w]
  congr 1
  funext y
  exact Complex.norm_real (w y)

private theorem eLpNorm_I_mul_ofReal {μ : Measure B0579.Plane} (w : B0579.Plane → ℝ) :
    eLpNorm (fun y => Complex.I * ((w y : ℝ) : ℂ)) 2 μ = eLpNorm w 2 μ := by
  rw [← eLpNorm_norm (fun y => Complex.I * ((w y : ℝ) : ℂ)), ← eLpNorm_norm w]
  congr 1
  funext y
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]

end CylDataDenseAux

theorem cylDataDense : UnforcedLeray.Short.IIIa.ComplFreeRateSub.Leaf2DualityNeeded.CylDataDense := by
  intro c a m hc ha1 _hm g hg ε hε
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hsq : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hd : 0 < cellLen c a := div_pos hc hsq
  set d := cellLen c a
  let u₁ : B0579.Plane → ℝ := fun y => (g y).re
  let u₂ : B0579.Plane → ℝ := fun y => (g y).im
  have hu₁ : MemLp u₁ 2 (B0579.cellMeasure d m) := Complex.reCLM.comp_memLp' hg
  have hu₂ : MemLp u₂ 2 (B0579.cellMeasure d m) := Complex.imCLM.comp_memLp' hg
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨h₁, hh₁, he₁⟩ := CylDataDenseAux.real_cylData_dense hd hu₁ hε3
  obtain ⟨h₂, hh₂, he₂⟩ := CylDataDenseAux.real_cylData_dense hd hu₂ hε3
  let f₁ : B0579.Plane → ℝ := CylDataDenseAux.unscaleTest a h₁
  let f₂ : B0579.Plane → ℝ := CylDataDenseAux.unscaleTest a h₂
  refine ⟨f₁, f₂, CylDataDenseAux.isCylTest_unscaleTest ha hh₁,
    CylDataDenseAux.isCylTest_unscaleTest ha hh₂, ?_⟩
  let A₁ : B0579.Plane → ℂ := fun y => ((u₁ y - h₁ y : ℝ) : ℂ)
  let A₂ : B0579.Plane → ℂ := fun y => Complex.I * ((u₂ y - h₂ y : ℝ) : ℂ)
  have hsplit : g - movCx a f₁ f₂ = A₁ + A₂ := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, A₁, A₂, f₁, f₂]
    rw [CylDataDenseAux.movCx_unscaleTest ha h₁ h₂ y]
    have hg_re_im : ((u₁ y : ℝ) : ℂ) + ((u₂ y : ℝ) : ℂ) * Complex.I = g y :=
      Complex.re_add_im (g y)
    rw [← hg_re_im, Complex.ofReal_sub, Complex.ofReal_sub]
    ring
  have hA₁_meas : AEStronglyMeasurable A₁ (B0579.cellMeasure d m) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hu₁.aestronglyMeasurable.sub hh₁.continuous.aestronglyMeasurable)
  have hA₂_meas : AEStronglyMeasurable A₂ (B0579.cellMeasure d m) :=
    aestronglyMeasurable_const.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hu₂.aestronglyMeasurable.sub hh₂.continuous.aestronglyMeasurable))
  unfold xNorm
  change eLpNorm (g - movCx a f₁ f₂) 2 (B0579.cellMeasure d m) < ENNReal.ofReal ε
  rw [hsplit]
  have htri : eLpNorm (A₁ + A₂) 2 (B0579.cellMeasure d m) ≤
      eLpNorm A₁ 2 (B0579.cellMeasure d m) + eLpNorm A₂ 2 (B0579.cellMeasure d m) :=
    eLpNorm_add_le hA₁_meas hA₂_meas (by norm_num)
  have hA₁_eq : eLpNorm A₁ 2 (B0579.cellMeasure d m) =
      eLpNorm (u₁ - h₁) 2 (B0579.cellMeasure d m) :=
    CylDataDenseAux.eLpNorm_complex_ofReal (u₁ - h₁)
  have hA₂_eq : eLpNorm A₂ 2 (B0579.cellMeasure d m) =
      eLpNorm (u₂ - h₂) 2 (B0579.cellMeasure d m) :=
    CylDataDenseAux.eLpNorm_I_mul_ofReal (u₂ - h₂)
  calc eLpNorm (A₁ + A₂) 2 (B0579.cellMeasure d m)
      ≤ eLpNorm (u₁ - h₁) 2 (B0579.cellMeasure d m) +
          eLpNorm (u₂ - h₂) 2 (B0579.cellMeasure d m) := by
        rwa [hA₁_eq, hA₂_eq] at htri
    _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := add_le_add he₁.le he₂.le
    _ = ENNReal.ofReal (ε / 3 + ε / 3) := (ENNReal.ofReal_add hε3.le hε3.le).symm
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

end Leaf2DualityNeeded

end ComplFreeRateSub

end UnforcedLeray.Short.IIIa

end
