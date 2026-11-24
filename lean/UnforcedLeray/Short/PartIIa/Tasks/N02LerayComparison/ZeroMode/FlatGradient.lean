import UnforcedLeray.Short.PartIIa.Sub.N02_3
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.GradMember
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.CutTest
import UnforcedLeray.Short.PartIIa.Tasks.N02LerayComparison.ZeroMode.GradCutError

/-!


Source of record: `the November 2 reference manuscript`, lines 1728-1735 ("the axial
component is a gradient"). Specification: `ZeroFlatGradient` in `Short/PartII-a/Sub/N02_3.lean`.

Proof outline. For a `q`-independent smooth meridional test `f`, the field `(0, f_z)` is continuous and
supported in the band, so it lies in `L²(measureH c)`; call its class `v`. For `L > 0` the cut-off
primitive `zCut L (zPrimC f_z)` is a complex band potential (`zeroCutTest`), so its `0`-gradient
`cgradC 0 (...)` has class in `(solenoidalHC 0 c)ᗮ` (`nearGradMember_proof`). By `zeroGradCutError`
with `ε = 0`, the distance from `v` to that class is at most `C (L⁻¹ + L^{-1/2}) zMomSum`. Taking
`L = n + 1` gives a sequence in the closed subspace `(solenoidalHC 0 c)ᗮ` converging to `v`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0226

namespace ZeroFlatGradientAux

/-- The axial component `(0, f_z)` of a meridional test is in `L²(measureH c)`. -/
theorem memLp_flat {c : ℝ} {f : Profile → MeridC} (hf : IsMeridTest c f) :
    MemLp (fun p : Profile => (!₂[0, f p 1] : MeridC)) 2 (measureH c) := by
  obtain ⟨s0, s1, Lb, hs0, hb⟩ := hf.band
  have hF1 : Continuous (fun p : Profile => f p 1) :=
    (ZeroCutTestAux.comp_isCTest hf 1).smooth.continuous
  have hcont : Continuous (fun p : Profile => (!₂[0, f p 1] : MeridC)) :=
    NearGradMemberAux.continuous_mk continuous_const hF1
  have hz : ∀ p : Profile, ¬(p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ Lb) →
      (fun p : Profile => (!₂[0, f p 1] : MeridC)) p = 0 := by
    intro p hp
    have h0 : f p 1 = 0 := by
      by_contra h
      exact hp (hb p (fun h' => h (by simp [h'])))
    ext i
    fin_cases i <;> simp [h0]
  exact NearGradMemberAux.memLp_of_band hcont hs0 hz

/-- Approximation: for every `L > 0` there is a member of `(solenoidalHC 0 c)ᗮ` at `H`-distance
at most `C (L⁻¹ + L^{-1/2}) zMomSum` from the class of `(0, f_z)`. -/
theorem approx_of_L {c : ℝ} {f : Profile → MeridC} {C : ℝ} (hc : 0 < c) (hf : IsMeridTest c f)
    (_hQ : QInvariant c f)
    (hCb : ∀ L : ℝ, 0 < L →
      (∫ p, ‖(!₂[0, f p 1] : MeridC) - cgradC 0 (zCut L (zPrimC (fun r => f r 1))) p‖ ^ 2
          ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        C * (L⁻¹ + L ^ (-(1 / 2 : ℝ))) * zMomSum c f)
    {L : ℝ} (hL : 0 < L) :
    ∃ g : HSpace c MeridC, g ∈ (solenoidalHC 0 c)ᗮ ∧
      ‖(memLp_flat hf).toLp _ - g‖ ≤ C * (L⁻¹ + L ^ (-(1 / 2 : ℝ))) * zMomSum c f := by
  have hm := memLp_flat hf
  have hΦ : IsCTest c (zCut L (zPrimC (fun r => f r 1))) := (zeroCutTest c L f hc hL hf 1).1
  obtain ⟨hmn, hgmem⟩ := nearGradMember_proof 0 c _ hΦ
  refine ⟨hmn.toLp _, hgmem, ?_⟩
  have hD : (((hm.toLp _ - hmn.toLp _ : HSpace c MeridC)) : Profile → MeridC) =ᵐ[measureH c]
      fun p => (!₂[0, f p 1] : MeridC) - cgradC 0 (zCut L (zPrimC (fun r => f r 1))) p := by
    filter_upwards [Lp.coeFn_sub (hm.toLp _) (hmn.toLp _), hm.coeFn_toLp, hmn.coeFn_toLp]
      with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  rw [zLpNorm_eq _ _ hD]
  exact hCb L hL

end ZeroFlatGradientAux

/-- **L3b (the axial component is a flat gradient), proved.** Target `zeroFlatGradient` for the Prop
`ZeroFlatGradient` (`Sub/N02_3.lean`, tex lines 1728-1735). -/
theorem zeroFlatGradient : UnforcedLeray.Short.PartIIa.ZeroFlatGradient := by
  intro c f hc hf hQ
  have hm := ZeroFlatGradientAux.memLp_flat hf
  refine ⟨hm, ?_⟩
  obtain ⟨C, _hC0, hC1⟩ := zeroGradCutError
  have hCb : ∀ L : ℝ, 0 < L →
      (∫ p, ‖(!₂[0, f p 1] : MeridC) - cgradC 0 (zCut L (zPrimC (fun r => f r 1))) p‖ ^ 2
          ∂(measureH c)) ^ (1 / 2 : ℝ) ≤
        C * (L⁻¹ + L ^ (-(1 / 2 : ℝ))) * zMomSum c f := by
    intro L hL
    have h := hC1 c 0 L f hc le_rfl hL hf hQ
    simp only [zero_mul, add_zero] at h
    exact h
  choose g hgmem hgb using fun n : ℕ =>
    ZeroFlatGradientAux.approx_of_L (C := C) hc hf hQ hCb (L := (n : ℝ) + 1)
      (by positivity)
  have hLtop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hLtop
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hLtop
  have hT : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1)⁻¹ + ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)))
      * zMomSum c f) atTop (𝓝 (C * (0 + 0) * zMomSum c f)) :=
    ((h1.add h2).const_mul C).mul_const (zMomSum c f)
  rw [show C * ((0 : ℝ) + 0) * zMomSum c f = 0 by ring] at hT
  have hlim : Tendsto (fun n : ℕ => ‖(ZeroFlatGradientAux.memLp_flat hf).toLp _ - g n‖) atTop
      (𝓝 0) := squeeze_zero (fun n => norm_nonneg _) hgb hT
  have hconv : Tendsto g atTop (𝓝 ((ZeroFlatGradientAux.memLp_flat hf).toLp _)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (hlim.congr fun n => norm_sub_rev _ _)
  exact (Submodule.isClosed_orthogonal _).mem_of_tendsto hconv (Eventually.of_forall hgmem)

end UnforcedLeray.Short.PartIIa
