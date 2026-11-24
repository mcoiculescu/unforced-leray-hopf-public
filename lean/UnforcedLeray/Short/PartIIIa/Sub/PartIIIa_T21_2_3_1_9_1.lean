import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_3_1_9
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.VelLip

/-!
# `PartIII-a:T21/2/3/1/9/1` (`LadTranspApprox`), decomposition

Source: `the November 2 reference manuscript` (SP) lines 3230-3240
(`eq:ct-embeddings`: `‖K_c f‖₂ ≤ C‖f‖_{X_m}` for zero circulation) and 3052-3058.

`LadTranspApprox m` follows from
* `LadTestDensity` : a zero-circulation `w ∈ X_{m,c}` is the `X_m`-limit of `a_n + i b_n`, `a_n, b_n`
  real cylinder tests with zero circulation (mollify and cut off, then restore the circulation with
  a fixed bump);
* `LadKernelVel` : a real zero-circulation cylinder test has a kernel velocity (`IsKernelBiotSavart`,
  `meanShear` vanishes) which is also the `IsBiotSavart` velocity of its complexification
  (`CTE.RealBiotSavartUniform` and real parts);
* `ladBSSub` (linearity, `VelLipBSSub.lean`) and `ladBSBound` (`VelLipBSBound.lean`), which turn the
  `X_m`-convergence into the `L²(cell)` convergence of the velocities.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

/-- **Leaf D** (density, SP 3230-3240): a zero-circulation `w ∈ X_{m,c}` is the `X_{m,c}`-limit of
`a_n + i b_n` with `a_n, b_n` real cylinder tests of zero circulation. -/
def LadTestDensity (m : ℝ) : Prop :=
  ∀ (c : ℝ) (w : ℝ × ℝ → ℂ), 1 ≤ c → MemLp w 2 (B0579.cellMeasure c m) →
    HasZeroCirculation c w →
    ∃ a b : ℕ → ℝ × ℝ → ℝ,
      (∀ n, B0579.IsCylTest c (a n) ∧ B0579.IsCylTest c (b n) ∧
        IntegrableOn (a n) (B0579.cell c) ∧ IntegrableOn (b n) (B0579.cell c) ∧
        ∫ x in B0579.cell c, a n x = 0 ∧ ∫ x in B0579.cell c, b n x = 0) ∧
      Tendsto (fun n => xNorm c m
        (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x)) atTop (𝓝 0)

/-- **Leaf K** (kernel velocity of a zero-circulation test, SP 3236-3240): a real cylinder test `ψ`
with `∫_{cell} ψ = 0` has a real velocity `u` with `IsKernelBiotSavart c ψ u` that is also the
Biot-Savart velocity (`IsBiotSavart`) of the complexification of `ψ`. -/
def LadKernelVel : Prop :=
  ∀ (c : ℝ) (ψ : ℝ × ℝ → ℝ), 1 ≤ c → B0579.IsCylTest c ψ → ∫ x in B0579.cell c, ψ x = 0 →
    ∃ u : ℝ × ℝ → Fin 2 → ℝ, IsKernelBiotSavart c ψ u ∧
      IsBiotSavart c (fun x => ((ψ x : ℝ) : ℂ)) (fun x j => ((u x j : ℝ) : ℂ))

namespace TranspApproxAux

/-- Scalar multiples of Biot-Savart pairs are Biot-Savart pairs. -/
lemma isBiotSavart_smul {c : ℝ} {om : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Fin 2 → ℂ} (k : ℂ)
    (h : IsBiotSavart c om u) :
    IsBiotSavart c (fun x => k * om x) (fun x j => k * u x j) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun j => (h1 j).const_mul k, fun ψ hψ => ?_, fun ψ hψ => ?_⟩
  · have e : (fun x => k * u x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        k * u x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) = fun x => k * (u x 0 * ((B0579.pd 0 ψ x : ℝ) : ℂ) +
        u x 1 * ((B0579.pd 1 ψ x : ℝ) : ℂ)) := by funext x; ring
    simp only [e]
    rw [integral_const_mul, h2 ψ hψ, mul_zero]
  · have e1 : (fun x => k * om x * ((ψ x : ℝ) : ℂ)) = fun x => k * (om x * ((ψ x : ℝ) : ℂ)) := by
      funext x; ring
    have e2 : (fun x => k * u x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        k * u x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) = fun x => k * (u x 0 * ((B0579.pd 1 ψ x : ℝ) : ℂ) -
        u x 1 * ((B0579.pd 0 ψ x : ℝ) : ℂ)) := by funext x; ring
    simp only [e1, e2]
    rw [integral_const_mul, integral_const_mul, h3 ψ hψ]

lemma memLp_comb {c m : ℝ} {a b : ℝ × ℝ → ℝ} (ha : B0579.IsCylTest c a)
    (hb : B0579.IsCylTest c b) :
    MemLp (fun x => ((a x : ℝ) : ℂ) + Complex.I * ((b x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := by
  have a1 : MemLp (fun x => ((a x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := (ha.memLp m).ofReal
  have a2 : MemLp (fun x => ((b x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) := (hb.memLp m).ofReal
  have a3 : MemLp (fun x => Complex.I * ((b x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
    a2.const_mul Complex.I
  exact a1.add a3

end TranspApproxAux

set_option maxHeartbeats 1600000 in
open TranspApproxAux in
/-- Assembly of `LadTranspApprox` from density, kernel velocities, linearity and the Biot-Savart
bound. -/
theorem ladTranspApprox_of (m : ℝ) (hm : 8 < m) (hD : LadTestDensity m) (hK : LadKernelVel) :
    LadTranspApprox m := by
  intro c w u hc hw hz hbs
  obtain ⟨a, b, hab, hX⟩ := hD c w hc hw hz
  have hKex : ∀ n, ∃ ua ub : ℝ × ℝ → Fin 2 → ℝ,
      IsKernelBiotSavart c (a n) ua ∧ IsKernelBiotSavart c (b n) ub ∧
      IsBiotSavart c (fun x => ((a n x : ℝ) : ℂ)) (fun x j => ((ua x j : ℝ) : ℂ)) ∧
      IsBiotSavart c (fun x => ((b n x : ℝ) : ℂ)) (fun x j => ((ub x j : ℝ) : ℂ)) := by
    intro n
    obtain ⟨ua, h1, h2⟩ := hK c (a n) hc (hab n).1 (hab n).2.2.2.2.1
    obtain ⟨ub, h3, h4⟩ := hK c (b n) hc (hab n).2.1 (hab n).2.2.2.2.2
    exact ⟨ua, ub, h1, h3, h2, h4⟩
  choose ua ub hka hkb hba hbb using hKex
  refine ⟨a, b, ua, ub, fun n => ⟨(hab n).1, (hab n).2.1, hka n, hkb n⟩, hX, ?_⟩
  obtain ⟨C, hC⟩ := ladBSBound m hm
  have hm1 : 1 < m := by linarith
  -- biot-savart pair of `a_n + i b_n`
  have hBS : ∀ n, IsBiotSavart c
      ((fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ)) - w)
      ((fun x j => ((ua n x j : ℝ) : ℂ) + Complex.I * ((ub n x j : ℝ) : ℂ)) - u) := by
    intro n
    have hAm : MemLp (fun x => ((a n x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
      ((hab n).1.memLp m).ofReal
    have hBm : MemLp (fun x => (-Complex.I) * ((b n x : ℝ) : ℂ)) 2 (B0579.cellMeasure c m) :=
      (((hab n).2.1.memLp m).ofReal).const_mul _
    have h1 := ladBSSub m c _ _ _ _ hm1 hAm hBm (hba n) (isBiotSavart_smul (-Complex.I) (hbb n))
    have hWm : MemLp ((fun x => ((a n x : ℝ) : ℂ)) - fun x => (-Complex.I) * ((b n x : ℝ) : ℂ))
        2 (B0579.cellMeasure c m) := hAm.sub hBm
    have h2 := ladBSSub m c _ _ _ _ hm1 hWm hw h1 hbs
    convert h2 using 2
    · funext x; simp
    · funext x j; simp
  have hZ : ∀ n, HasZeroCirculation c
      ((fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ)) - w) := by
    intro n
    have ia : IntegrableOn (fun x => ((a n x : ℝ) : ℂ)) (B0579.cell c) := (hab n).2.2.1.ofReal
    have ib : IntegrableOn (fun x => ((b n x : ℝ) : ℂ)) (B0579.cell c) := (hab n).2.2.2.1.ofReal
    have iW : IntegrableOn (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ))
        (B0579.cell c) := ia.add (ib.const_mul Complex.I)
    refine ⟨iW.sub hz.1, ?_⟩
    have e : ∫ x in B0579.cell c, (((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ)) = 0 := by
      rw [integral_add ia (ib.const_mul Complex.I), integral_const_mul, integral_complex_ofReal,
        integral_complex_ofReal, (hab n).2.2.2.2.1, (hab n).2.2.2.2.2]
      simp
    have := integral_sub iW hz.1
    simp only [Pi.sub_apply]
    rw [this, e, hz.2, sub_zero]
  intro j
  have hbd : ∀ n, eLpNorm (fun x => ((ua n x j : ℝ) : ℂ) + Complex.I * ((ub n x j : ℝ) : ℂ) - u x j)
      2 (volume.restrict (B0579.cell c)) ≤
      ENNReal.ofReal C * xNorm c m
        (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x) := by
    intro n
    have hWm : MemLp ((fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ)) - w) 2
        (B0579.cellMeasure c m) :=
      (memLp_comb (hab n).1 (hab n).2.1).sub hw
    exact hC c hc _ hWm (hZ n) _ (hBS n) j
  have hlim : Tendsto (fun n => ENNReal.ofReal C * xNorm c m
      (fun x => ((a n x : ℝ) : ℂ) + Complex.I * ((b n x : ℝ) : ℂ) - w x)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hX (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbd

end UnforcedLeray.Short.IIIa
