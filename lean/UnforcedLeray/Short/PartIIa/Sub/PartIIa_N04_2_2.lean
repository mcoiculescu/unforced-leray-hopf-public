import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_2
import UnforcedLeray.Units.B0224
import UnforcedLeray.Units.B0225

/-!
# Sub `PartII-a_N04_2_2`: Causal Flat Adjoint Representative & Elementary Bounds (`FlatAdjointElementaryBound`)

Source of record: `the November 2 reference manuscript`,
lines 1803–1836 (Lemma `near:adjoint-polynomial`, step 2).

For a smooth flat-Leray representative `h` satisfying `IsFlatLerayRep c σ H1 h` with
`(PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] h`, we construct the concrete backward causal
integral representative `flatAdjointRep ν μ h : Profile → MeridC`:
`v(s, q, η) = ∫_{t > 0} e^{-(μ̄ + 1/2) t} (e^{ν s (e^t - 1) Δ_{q,η}} (h(e^t s, ·)))(q, η) dt`
for `s > 0` (and `0` for `s ≤ 0`).

This file proves unconditionally:
1. `planeHeat_zero`: `B0224.planeHeat θ (fun _ => 0) x = 0`.
2. `planeHeat_periodic`: translation invariance of `B0224.planeHeat θ` under `q ↦ q + c` for
   `c`-periodic planar profiles.
3. `flatAdjointRep_periodic`: `QPeriodic c (flatAdjointRep ν μ h)` from `hh.periodic`.
4. `flatAdjointRep_support_H1`: `flatAdjointRep ν μ h p = 0` for `H1 < p.1`, since `e^t > 1` for
   `t > 0` forces `e^t p.1 > H1` where `h` vanishes by `hh.support_s`.
5. `flatProjMomentNorm_nonneg`: `0 ≤ flatProjMomentNorm c h`.
6. Reduction `flatAdjointElementaryBound_of` of `FlatAdjointElementaryBound` to three
   self-contained analytical leaf propositions on `flatAdjointRep ν μ h`:
   - `FlatAdjointSmoothAe` (`PartII-a:N04/2/2/1`): smoothness on `{p : Profile | 0 < p.1}` and
     a.e. identification with `ContinuousLinearMap.adjoint (T0flat hc ν μ) Z`.
   - `FlatAdjointGen1Bound` (`PartII-a:N04/2/2/2`): `L²` membership and polynomial `GammaBox`
     bound for the first-order generator difference `genDiff1 ν (flatAdjointRep ν μ h)` and tensor
     gradient `gradDiff1 (flatAdjointRep ν μ h)`.
   - `FlatAdjointGen2Bound` (`PartII-a:N04/2/2/3`): `L²` membership and polynomial `GammaBox`
     bound for the six elementary terms `genDiff2Term1..6 ν (flatAdjointRep ν μ h)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223 UnforcedLeray.B0224 UnforcedLeray.B0226

/-! ### 1. Concrete backward causal integral representative `flatAdjointRep` -/

/-- Integrand slice at age-time `t > 0` of the backward causal flat adjoint integral
(source line 1803):
`e^{-(μ̄ + 1/2) t} e^{ν s (e^t - 1) Δ_{q,η}} (h(e^t s, ·))(q, η)`. -/
def flatAdjointSlice (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) (t : ℝ) (p : Profile) : MeridC :=
  Complex.exp (-((starRingEnd ℂ μ + (1 / 2 : ℂ)) * (t : ℂ))) •
    B0224.planeHeat (ν * p.1 * (Real.exp t - 1)) (fun y => h (Real.exp t * p.1, y)) p.2

/-- Concrete backward causal integral representative `v` of `(T0flat hc ν μ).adjoint Z`
for a flat Leray representative `h` of `PepsC 0 c Z` (source lines 1803–1808). -/
def flatAdjointRep (ν : ℝ) (μ : ℂ) (h : Profile → MeridC) (p : Profile) : MeridC :=
  if 0 < p.1 then ∫ t : ℝ in Ioi (0 : ℝ), flatAdjointSlice ν μ h t p else 0

/-! ### 2. Unconditional properties of `planeHeat` and `flatAdjointRep` -/

/-- The planar Gaussian heat convolution of the zero field is zero. -/
theorem planeHeat_zero (θ : ℝ) (x : ℝ × ℝ) :
    B0224.planeHeat θ (fun _ : ℝ × ℝ => (0 : MeridC)) x = 0 := by
  by_cases hθ : 0 < θ
  · simp [B0224.planeHeat_of_pos hθ]
  · simp [B0224.planeHeat_of_nonpos (not_lt.1 hθ)]

/-- The planar Gaussian heat convolution preserves `c`-periodicity in the first coordinate `q`. -/
theorem planeHeat_periodic {c : ℝ} (θ : ℝ) {u : ℝ × ℝ → MeridC}
    (hu : ∀ z : ℝ × ℝ, u (z.1 + c, z.2) = u z) (x : ℝ × ℝ) :
    B0224.planeHeat θ u (x.1 + c, x.2) = B0224.planeHeat θ u x := by
  by_cases hθ : 0 < θ
  · rw [B0224.planeHeat_of_pos hθ, B0224.planeHeat_of_pos hθ]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    have hshift : (x.1 + c, x.2) - B0224.planeι y =
        ((x - B0224.planeι y).1 + c, (x - B0224.planeι y).2) := by
      ext <;> simp only [Prod.fst_sub, Prod.snd_sub]; ring
    rw [hshift, hu]
  · rw [B0224.planeHeat_of_nonpos (not_lt.1 hθ), hu]

/-- Each time slice `flatAdjointSlice ν μ h t` is `c`-periodic in `q` when `h` is `c`-periodic. -/
theorem flatAdjointSlice_periodic {c : ℝ} (ν : ℝ) (μ : ℂ) {h : Profile → MeridC}
    (hh : QPeriodic c h) (t : ℝ) : QPeriodic c (flatAdjointSlice ν μ h t) := by
  intro p
  simp only [flatAdjointSlice]
  congr 1
  exact planeHeat_periodic (ν * p.1 * (Real.exp t - 1))
    (fun z => hh (Real.exp t * p.1, z.1, z.2)) p.2

/-- The backward causal integral representative `flatAdjointRep ν μ h` is `c`-periodic in `q`
whenever `h` is `c`-periodic in `q`. -/
theorem flatAdjointRep_periodic {c : ℝ} (ν : ℝ) (μ : ℂ) {h : Profile → MeridC}
    (hh : QPeriodic c h) : QPeriodic c (flatAdjointRep ν μ h) := by
  intro p
  simp only [flatAdjointRep]
  split_ifs with hp
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact flatAdjointSlice_periodic ν μ hh t p
  · rfl

/-- For `H1 < p.1` and `t > 0`, `Real.exp t * p.1 > H1`, so `flatAdjointSlice ν μ h t p = 0`. -/
theorem flatAdjointSlice_eq_zero_of_H1_lt {c σ H1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (ν : ℝ) (μ : ℂ) {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    {p : Profile} (hp : H1 < p.1) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    flatAdjointSlice ν μ h t p = 0 := by
  have hp_pos : 0 < p.1 := (hσ.trans_le hσH1).trans hp
  have hexp : 1 < Real.exp t := Real.one_lt_exp_iff.mpr ht
  have hlt : H1 < Real.exp t * p.1 := by
    calc H1 < p.1 := hp
      _ = 1 * p.1 := (one_mul p.1).symm
      _ < Real.exp t * p.1 := mul_lt_mul_of_pos_right hexp hp_pos
  have hzero : (fun y : ℝ × ℝ => h (Real.exp t * p.1, y)) = fun _ => 0 := by
    funext y
    exact hh.support_s (Real.exp t * p.1, y) (Or.inr hlt)
  simp only [flatAdjointSlice, hzero, planeHeat_zero, smul_zero]

/-- The backward causal integral representative `flatAdjointRep ν μ h` vanishes for `s > H₁`
(source line 1805: "Because `h` is supported in `s ≤ H₁` and `e^t ≥ 1`, we have `v(s, ·) = 0` for
`s > H₁`"). -/
theorem flatAdjointRep_support_H1 {c σ H1 : ℝ} (hσ : 0 < σ) (hσH1 : σ ≤ H1)
    (ν : ℝ) (μ : ℂ) {h : Profile → MeridC} (hh : IsFlatLerayRep c σ H1 h)
    (p : Profile) (hp : H1 < p.1) :
    flatAdjointRep ν μ h p = 0 := by
  simp only [flatAdjointRep]
  split_ifs with hp_pos
  · have hcongr : EqOn (fun t => flatAdjointSlice ν μ h t p) (fun _ => (0 : MeridC)) (Ioi 0) :=
      fun t ht => flatAdjointSlice_eq_zero_of_H1_lt hσ hσH1 ν μ hh hp ht
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, setIntegral_const, smul_zero]
  · rfl

/-- Nonnegativity of the combined weighted `L²(measureH c)` norm `flatProjMomentNorm c h`. -/
theorem flatProjMomentNorm_nonneg (c : ℝ) (h : Profile → MeridC) :
    0 ≤ flatProjMomentNorm c h := by
  unfold flatProjMomentNorm
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun m _ => ?_
  exact Real.rpow_nonneg (integral_nonneg fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _

/-! ### 3. Leaf propositions and assembly of `FlatAdjointElementaryBound` -/

/-- **Leaf 1 (`FlatAdjointSmoothAe`, task `PartII-a:N04/2/2/1`)**: for any flat-Leray
representative `h` satisfying `IsFlatLerayRep c σ H1 h` with `PepsC 0 c Z =ᵐ[measureH c] h`,
the backward causal integral `flatAdjointRep ν μ h` is smooth on `{p : Profile | 0 < p.1}` and
represents `ContinuousLinearMap.adjoint (T0flat hc ν μ) Z` almost everywhere with respect to
`measureH c` (source: `the November 2 reference manuscript` lines 1803–1808). -/
def FlatAdjointSmoothAe : Prop :=
  ∀ (ν c σ H1 γs : ℝ) (hc : 0 < c), 0 < ν → 0 < σ → σ ≤ H1 → 0 < γs →
    ∀ μ : ℂ, γs ≤ μ.re + 1 / 4 →
      ∀ (Z : HSpace c MeridC) (h : Profile → MeridC),
        IsFlatLerayRep c σ H1 h →
        (PepsC 0 c Z : Profile → MeridC) =ᵐ[measureH c] h →
        ContDiffOn ℝ ∞ (flatAdjointRep ν μ h) {p : Profile | 0 < p.1} ∧
        ((ContinuousLinearMap.adjoint (T0flat hc ν μ) Z : HSpace c MeridC) :
          Profile → MeridC) =ᵐ[measureH c] flatAdjointRep ν μ h

/-- **Leaf 2 (`FlatAdjointGen1Bound`, task `PartII-a:N04/2/2/2`)**: `L²` membership and
polynomial `GammaBox` bound for the first-order generator difference
`genDiff1 ν (flatAdjointRep ν μ h)` in `L²(measureH c)` and the tensor gradient term
`gradDiff1 (flatAdjointRep ν μ h)` in `L²(measureHT c)` (source: `the November 2 reference manuscript`
lines 1809–1835). -/
def FlatAdjointGen1Bound : Prop :=
  ∃ (k1 : ℕ) (C1 : ℝ), 0 ≤ C1 ∧
    ∀ (ν c σ H1 L1 M γs : ℝ), 0 < c → 0 < ν → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ h : Profile → MeridC, IsFlatLerayRep c σ H1 h →
          ∃ (h1 : MemLp (genDiff1 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (hgd : MemLp (gradDiff1 (flatAdjointRep ν μ h)) 2 (measureHT c)),
            ‖h1.toLp (genDiff1 ν (flatAdjointRep ν μ h))‖ +
              ‖hgd.toLp (gradDiff1 (flatAdjointRep ν μ h))‖ ≤
                C1 * GammaBox ν c σ H1 L1 M γs ^ k1 * flatProjMomentNorm c h

/-- **Leaf 3 (`FlatAdjointGen2Bound`, task `PartII-a:N04/2/2/3`)**: `L²(measureH c)` membership
and polynomial `GammaBox` bound for the six elementary second-order terms
`genDiff2Term1..6 ν (flatAdjointRep ν μ h)` (source: `the November 2 reference manuscript`
lines 1814–1835). -/
def FlatAdjointGen2Bound : Prop :=
  ∃ (k2 : ℕ) (C2 : ℝ), 0 ≤ C2 ∧
    ∀ (ν c σ H1 L1 M γs : ℝ), 0 < c → 0 < ν → 0 < σ → σ ≤ H1 → 0 ≤ L1 → 0 < γs →
      ∀ μ : ℂ, ‖μ‖ ≤ M → γs ≤ μ.re + 1 / 4 →
        ∀ h : Profile → MeridC, IsFlatLerayRep c σ H1 h →
          ∃ (ht1 : MemLp (genDiff2Term1 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht2 : MemLp (genDiff2Term2 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht3 : MemLp (genDiff2Term3 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht4 : MemLp (genDiff2Term4 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht5 : MemLp (genDiff2Term5 ν (flatAdjointRep ν μ h)) 2 (measureH c))
            (ht6 : MemLp (genDiff2Term6 ν (flatAdjointRep ν μ h)) 2 (measureH c)),
            4 * ‖ht1.toLp (genDiff2Term1 ν (flatAdjointRep ν μ h))‖ +
              4 * ‖ht2.toLp (genDiff2Term2 ν (flatAdjointRep ν μ h))‖ +
              4 * ‖ht3.toLp (genDiff2Term3 ν (flatAdjointRep ν μ h))‖ +
              ‖ht4.toLp (genDiff2Term4 ν (flatAdjointRep ν μ h))‖ +
              3 * ‖ht5.toLp (genDiff2Term5 ν (flatAdjointRep ν μ h))‖ +
              ‖ht6.toLp (genDiff2Term6 ν (flatAdjointRep ν μ h))‖ ≤
                C2 * GammaBox ν c σ H1 L1 M γs ^ k2 * flatProjMomentNorm c h

/-- Assembly of `FlatAdjointElementaryBound` (`PartII-a:N04/2/2`) from the unconditional
periodicity and upper-age support proofs (`flatAdjointRep_periodic`, `flatAdjointRep_support_H1`)
and the three analytical leaf propositions (`FlatAdjointSmoothAe`, `FlatAdjointGen1Bound`,
`FlatAdjointGen2Bound`). -/
theorem flatAdjointElementaryBound_of
    (hSmoothAe : FlatAdjointSmoothAe)
    (hGen1 : FlatAdjointGen1Bound)
    (hGen2 : FlatAdjointGen2Bound) : FlatAdjointElementaryBound := by
  obtain ⟨k1, C1, hC1, hGen1⟩ := hGen1
  obtain ⟨k2, C2, hC2, hGen2⟩ := hGen2
  refine ⟨k1 + k2, C1 + C2, add_nonneg hC1 hC2, ?_⟩
  intro ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ Z h hh hZ_ae
  obtain ⟨hv_smooth, hv_ae⟩ := hSmoothAe ν c σ H1 γs hc hν hσ hσH1 hγs μ hμγ Z h hh hZ_ae
  obtain ⟨h1, hgd, hbound1⟩ := hGen1 ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  obtain ⟨ht1, ht2, ht3, ht4, ht5, ht6, hbound2⟩ :=
    hGen2 ν c σ H1 L1 M γs hc hν hσ hσH1 hL1 hγs μ hμM hμγ h hh
  refine ⟨flatAdjointRep ν μ h, hv_smooth, flatAdjointRep_periodic ν μ hh.periodic,
    flatAdjointRep_support_H1 hσ hσH1 ν μ hh, hv_ae,
    h1, ht1, ht2, ht3, ht4, ht5, ht6, hgd, ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg μ).trans hμM
  have hG1 : 1 ≤ GammaBox ν c σ H1 L1 M γs :=
    one_le_GammaBox hν hc hσ hσH1 hL1 hM0 hγs
  have hF0 : 0 ≤ flatProjMomentNorm c h := flatProjMomentNorm_nonneg c h
  have hpow1 : GammaBox ν c σ H1 L1 M γs ^ k1 ≤ GammaBox ν c σ H1 L1 M γs ^ (k1 + k2) :=
    pow_le_pow_right₀ hG1 (Nat.le_add_right k1 k2)
  have hpow2 : GammaBox ν c σ H1 L1 M γs ^ k2 ≤ GammaBox ν c σ H1 L1 M γs ^ (k1 + k2) :=
    pow_le_pow_right₀ hG1 (Nat.le_add_left k2 k1)
  have hle1 : C1 * GammaBox ν c σ H1 L1 M γs ^ k1 * flatProjMomentNorm c h ≤
      C1 * GammaBox ν c σ H1 L1 M γs ^ (k1 + k2) * flatProjMomentNorm c h := by
    gcongr
  have hle2 : C2 * GammaBox ν c σ H1 L1 M γs ^ k2 * flatProjMomentNorm c h ≤
      C2 * GammaBox ν c σ H1 L1 M γs ^ (k1 + k2) * flatProjMomentNorm c h := by
    gcongr
  linarith

end UnforcedLeray.Short.PartIIa
