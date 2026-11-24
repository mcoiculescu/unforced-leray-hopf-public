import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6.Pointwise
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6.ChartPhase
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6.AgeCell
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6.SlabLintegral
import UnforcedLeray.Short.PartIIa.Sub.N01.CartLiftRows
import UnforcedLeray.Short.PartIIa.Sub.F13

/-!
# `PartII-a:N01/6/5`: the slab-Frobenius identity `SlabFrobIdentity`

Assembly of the leaves `/1` (`slabFrobPointwise`), `/2` (`chartPhaseFrob`), `/3`
(`ageCellTransfer`), `/4` (`slabToLintegral`) and the phase-test rows `N01.cartLiftRows`.
Source of record: `the November 2 reference manuscript` lines 1644-1648, 2666-2687.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.PhaseSpace
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift nsSym symRZ chartOf)

/-- `frob2` is nonnegative. -/
theorem slabId_frob2_nonneg (T : Ten3) : 0 ≤ frob2 T :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `frob2` depends only on the components `tv4 T`: `|nsSym T|_F² = ‖tv4 T‖² + |tv4 T 1|²`. -/
theorem slabId_frob2_eq (T : Ten3) : frob2 T = ‖tv4 T‖ ^ 2 + ‖tv4 T 1‖ ^ 2 := by
  have hn : ‖tv4 T‖ ^ 2 = T (0, 0) ^ 2 + symRZ T ^ 2 + T (2, 2) ^ 2 + T (1, 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [tv4, Fin.sum_univ_four]
  have h1 : ‖tv4 T 1‖ ^ 2 = symRZ T ^ 2 := by
    simp [tv4, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hf : frob2 T = T (0, 0) ^ 2 + T (1, 1) ^ 2 + T (2, 2) ^ 2 + 2 * symRZ T ^ 2 := by
    simp [frob2, nsSym, Fin.sum_univ_three]
    ring
  rw [hf, hn, h1]
  ring

theorem slabFrobIdentity : UnforcedLeray.Short.PartIIa.N01.SlabFrobIdentity := by
  intro ε c P _ hε hc hP m hm
  have hεinv : 0 < ε⁻¹ := inv_pos.2 hε
  have hPpos : 0 < P := by rw [hP]; positivity
  have hph : ∀ i, IsPhaseTest P (cartRowsC (cartLift ε⁻¹ c m) i) :=
    (cartLiftRows ε c P hε hc hP m hm).1
  -- the scalar profile `p ↦ frob2 (m p)` is continuous and `q`-periodic
  have hsm : Continuous (fun p : Chart => tv4 (m p)) := hm.smooth.continuous
  have hsm1 : Continuous (fun p : Chart => tv4 (m p) 1) :=
    (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 4 => ℂ) 1).comp hsm
  have hcont : Continuous (fun p : Chart => frob2 (m p)) := by
    have e : (fun p : Chart => frob2 (m p)) =
        fun p => ‖tv4 (m p)‖ ^ 2 + ‖tv4 (m p) 1‖ ^ 2 :=
      funext fun p => slabId_frob2_eq (m p)
    rw [e]
    exact (hsm.norm.pow 2).add (hsm1.norm.pow 2)
  obtain ⟨G, hGdef⟩ : ∃ G : Chart → ℝ≥0∞, G = fun p => ENNReal.ofReal (frob2 (m p)) :=
    ⟨_, rfl⟩
  have hGm : Measurable G := by
    rw [hGdef]
    exact hcont.measurable.ennreal_ofReal
  have hper : ∀ p : Chart, G (p.1, p.2.1 + c, p.2.2) = G p := by
    intro p
    have hq : tv4 (m (p.1, p.2.1 + c, p.2.2)) = tv4 (m p) := hm.periodic p
    have hf : frob2 (m (p.1, p.2.1 + c, p.2.2)) = frob2 (m p) := by
      rw [slabId_frob2_eq, slabId_frob2_eq, hq]
    rw [hGdef]
    simp only [hf]
  -- the leaves
  have hPR : 2 * c / ε⁻¹ = P := by
    rw [hP, div_inv_eq_mul]; ring
  have hL1 : ∫⁻ τ in Ioc 0 P, ∫⁻ z : UnforcedLeray.Space,
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, (cartLift ε⁻¹ c m τ z i j) ^ 2) =
      ∫⁻ τ in Ioc 0 (2 * c / ε⁻¹), ∫⁻ z : UnforcedLeray.Space,
        ENNReal.ofReal ((chartOf ε⁻¹ c z τ).1 ^ 2) * G (chartOf ε⁻¹ c z τ) := by
    rw [hPR]
    refine lintegral_congr fun τ => lintegral_congr fun z => ?_
    rw [slabFrobPointwise ε⁻¹ c m τ z, ENNReal.ofReal_mul (sq_nonneg _)]
    simp only [hGdef]
  have hL2 := chartPhaseFrob ε⁻¹ c hεinv hc G hGm
  have hL3 := ageCellTransfer c hc G hGm hper
  have hmain := slabToLintegral P (cartLift ε⁻¹ c m) hph
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ∑ i : Fin 3,
      (slabInner P (cartRowsC (cartLift ε⁻¹ c m) i) (cartRowsC (cartLift ε⁻¹ c m) i)).re :=
    ⟨_, rfl⟩
  rw [← hX] at hmain
  -- the lift norm in terms of `X`
  have hnorm : ‖smoothTensor P (cartRowsC (cartLift ε⁻¹ c m))‖ ^ 2 = P⁻¹ * X := by
    rw [PiLp.norm_sq_eq_of_L2, hX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smoothTensor, PiLp.toLp_apply]
    rw [normSq_testElem (hph i)]
  have hXnn : 0 ≤ X := by
    have h1 : X = P * ‖smoothTensor P (cartRowsC (cartLift ε⁻¹ c m))‖ ^ 2 := by
      rw [hnorm, ← mul_assoc, mul_inv_cancel₀ hPpos.ne', one_mul]
    rw [h1]
    positivity
  -- the chain of lintegrals
  have hchain : ENNReal.ofReal X = (ENNReal.ofReal (2 * c / ε⁻¹) *
      ENNReal.ofReal (Real.pi * ε⁻¹ ^ 2) * ENNReal.ofReal c⁻¹) *
      ∫⁻ p, G p ∂(UnforcedLeray.Short.PartIIa.measureHT c) := by
    rw [hmain, hL1, hL2, hL3]
    ring
  -- the Bochner integral of `frob2 ∘ m` is the real part of the lintegral
  have hA : ∫ p, frob2 (m p) ∂(UnforcedLeray.Short.PartIIa.measureHT c) =
      (∫⁻ p, G p ∂(UnforcedLeray.Short.PartIIa.measureHT c)).toReal := by
    rw [← integral_toReal hGm.aemeasurable (ae_of_all _ fun p => by
      rw [hGdef]; exact ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    rw [hGdef]
    simp only [ENNReal.toReal_ofReal (slabId_frob2_nonneg (m p))]
  have h2 : 0 ≤ 2 * c / ε⁻¹ := by positivity
  have h3 : 0 ≤ Real.pi * ε⁻¹ ^ 2 := by positivity
  have h4 : 0 ≤ c⁻¹ := by positivity
  have hXA : X = (2 * c / ε⁻¹ * (Real.pi * ε⁻¹ ^ 2) * c⁻¹) *
      ∫ p, frob2 (m p) ∂(UnforcedLeray.Short.PartIIa.measureHT c) := by
    have e1 : X = (ENNReal.ofReal X).toReal := (ENNReal.toReal_ofReal hXnn).symm
    rw [e1, hchain, hA]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal h2, ENNReal.toReal_ofReal h3,
      ENNReal.toReal_ofReal h4]
  rw [hnorm, hXA, hP]
  field_simp

end UnforcedLeray.Short.PartIIa.N01
