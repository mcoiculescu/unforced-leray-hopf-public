import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04_3_3_Org
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Sub `PartII-a_N04_3_Org`: `AdjointResidualEq` tested against axis-reaching core tests

Source of record: `the November 2 reference manuscript`,
lines 1800–1806 (`h = P_0 z`, `v = T_0^* z`; `v` vanishes for `s > H_1`), 1836–1845 (the
generator difference and `(μ̄ - A_ε^*) w = (P_ε - P_0) z + (A_ε^* - A_0^*) v`), 1456–1480 (the
core of `A_ε^vec` reaches the axis), 1669–1670 and 1724 (`P_0` is the planar cylinder projection,
a Fourier multiplier in `(q, η)` at each age `s`).

## Why the band leaves are kept

The weak characterization of `RepsVec.adjoint` must test against the axis-reaching class
`IsMeridCoreTest ε c` (`RepsVecAdjointOfWeakEqCore`; the band version is false). The flat identity
`FlatAdjointWeakEq` and the integration by parts `GenDiffIBP` do not make sense over that class:
near the axis (`s → ∞`) an axis-reaching test has `u_z ≈ s^{-1/2} V_z(0, εηs^{-1/2}, τ)`, hence
`genDiffC ν ε u ≈ -4ε²ν s^{1/2} ∂_τ²V_z` and `ν s ∂_q² u` have `H`-norm `∫^∞ ds = ∞`; neither
`(μ - A_0) u` nor `genDiffC ν ε u` lies in `H` (only `(μ - A_ε) u` does). The pairing with
`v = T_0^* z` only sees `s ≤ H_1`. So a core test is replaced by a band test that agrees with it on
`0 < s < H_1 + 1` (`MeridCoreTestLocalize`), the accepted band leaves are applied to the
replacement, and the right side `P_0 Z - genDiffC ν ε v` vanishes for `s > H_1`: `genDiffC ν ε v`
because `v = 0` there, `P_0 Z` because `P_0` commutes with functions of `s` (`FlatProjCommSMul`).

## Contents
* Leaves `MeridCoreTestSupport` (task `PartII-a:N04/3/4`), `FlatProjCommSMul`
  (task `PartII-a:N04/3/5`), `ProfileBandCutoff` (task `PartII-a:N04/3/6`);
  `meridCoreTestLocalize_of` composes `MeridCoreTestLocalize` from the first and the last.
* `N04_3_Org.flatProjVanishAbove_of`: `P_0 Z` vanishes above `H` when `Z` does.
* `adjointResidualEq_of_core`: `AdjointResidualEq` from the band leaves `FlatAdjointWeakEq`,
  `GenDiffIBP`, the two new leaves and `RepsVecAdjointOfWeakEqCore` (composed by task
  `PartII-a:N04/3`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.B0220 UnforcedLeray.B0223

/-- **Support of core tests (leaf `PartII-a:N04/3/4`, `MeridCoreTestSupport`)**: an axis-reaching
core test vanishes for `s < R⁻¹` and for `|η| > R √s`. Its lift agrees off the axis with a field
vanishing for `|x| > R₀`; at the chart point `x = (s^{-1/2}, 0, ε s^{-1/2} η)`, `τ = 2εq + log s`
(radius `s^{-1/2} ≠ 0`, `chart ε (x, τ) = p`) one has `|x|² = s⁻¹ (1 + ε² η²)`, `liftA x ≠ 0`, and
`frame x` is isometric, so `u p ≠ 0` forces `|x| ≤ R₀` (source lines 3290–3295 for the lift,
1456–1466 for the bounded spatial support of the core). -/
def MeridCoreTestSupport : Prop :=
  ∀ (ε c : ℝ), 0 < ε → ∀ u : Profile → MeridC, IsMeridCoreTest ε c u →
    ∃ R : ℝ, 0 < R ∧ ∀ p : Profile, 0 < p.1 → u p ≠ 0 → R⁻¹ ≤ p.1 ∧ |p.2.2| ≤ R * Real.sqrt p.1

/-- **Band cutoff below a level (leaf `PartII-a:N04/3/6`, `ProfileBandCutoff`)**: a profile smooth
on `{s > 0}`, `c`-periodic, vanishing for `s < R⁻¹` and for `|η| > R √s`, agrees on `0 < s < S` with
the band test `w = χ(s) u`, `χ` smooth, `χ = 0` for `s ≤ R⁻¹/2` and for `s ≥ S + 1`, `χ = 1` on
`[R⁻¹, S]` (source lines 1464–1466: cutoffs; lines 1800–1806: only `s ≤ H_1` is seen by
`v = T_0^* z`). -/
def ProfileBandCutoff : Prop :=
  ∀ (c R : ℝ), 0 < R → ∀ u : Profile → MeridC, ContDiffOn ℝ ∞ u {p : Profile | 0 < p.1} →
    QPeriodic c u →
    (∀ p : Profile, 0 < p.1 → u p ≠ 0 → R⁻¹ ≤ p.1 ∧ |p.2.2| ≤ R * Real.sqrt p.1) →
    ∀ S : ℝ, ∃ w : Profile → MeridC, IsMeridTest c w ∧
      ∀ p : Profile, 0 < p.1 → p.1 < S → w p = u p

/-- **Localization of core tests (`MeridCoreTestLocalize`)**: below any age level `S`, an
axis-reaching core test agrees with a band test (composed by `meridCoreTestLocalize_of` from
`MeridCoreTestSupport` and `ProfileBandCutoff`). -/
def MeridCoreTestLocalize : Prop :=
  ∀ (ε c : ℝ), 0 < ε → 0 < c → ∀ u : Profile → MeridC, IsMeridCoreTest ε c u →
    ∀ S : ℝ, ∃ w : Profile → MeridC, IsMeridTest c w ∧
      ∀ p : Profile, 0 < p.1 → p.1 < S → w p = u p

/-- `MeridCoreTestLocalize` from the support bound and the band cutoff (applied in task
`PartII-a:N04/3`). -/
theorem meridCoreTestLocalize_of (hSupp : MeridCoreTestSupport) (hCut : ProfileBandCutoff) :
    MeridCoreTestLocalize := by
  intro ε c hε _hc u hu S
  obtain ⟨R, hR, hb⟩ := hSupp ε c hε u hu
  exact hCut c R hR u hu.smooth hu.periodic hb S

/-- **Leaf `PartII-a:N04/3/5` (`FlatProjCommSMul`)**: the flat projection `P_0 = PepsC 0 c`
commutes with multiplication by a smooth bounded function `χ(s)` of the age. `P_0` is the planar
cylinder projection, a Fourier multiplier in `(q, η)` at each `s` (source lines 1669–1670, 1724):
for a profile test `Φ`, `χ(s) Φ` is a profile test and `cgrad 0 (χ Φ) = χ cgrad 0 Φ`
(`Deps 0 = ∂_q`), so multiplication by `χ` (self-adjoint) preserves the gradient span, hence
`solenoidalHC 0 c` and its complement. -/
def FlatProjCommSMul : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → (∃ B : ℝ, ∀ s, |χ s| ≤ B) →
    ∀ Z Y : HSpace c MeridC,
      (Y : Profile → MeridC) =ᵐ[measureH c] (fun p => (χ p.1 : ℂ) • (Z : Profile → MeridC) p) →
      ((PepsC 0 c Y : HSpace c MeridC) : Profile → MeridC) =ᵐ[measureH c]
        (fun p => (χ p.1 : ℂ) • ((PepsC 0 c Z : HSpace c MeridC) : Profile → MeridC) p)

namespace N04_3_Org

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem pdQ_evEq {f g : Profile → E} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    pdQ f =ᶠ[𝓝 p] pdQ g := by
  filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) h] with y hdy
  simp only [pdQ, hdy]

theorem pdEta_evEq {f g : Profile → E} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    pdEta f =ᶠ[𝓝 p] pdEta g := by
  filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) h] with y hdy
  simp only [pdEta, hdy]

theorem opS_evEq {f g : Profile → E} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    opS f =ᶠ[𝓝 p] opS g := by
  filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) h] with y hdy
  simp only [opS, pdS, hdy]

theorem opK_evEq {f g : Profile → E} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    opK f =ᶠ[𝓝 p] opK g := by
  filter_upwards [opS_evEq h, pdEta_evEq h] with y h1 h2
  simp only [opK, h1, h2]

theorem opLam_evEq {f g : Profile → E} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    opLam f =ᶠ[𝓝 p] opLam g := by
  filter_upwards [opK_evEq h, h] with y h1 h2
  simp only [opLam, h1, h2]

theorem opQ_evEq (ε : ℝ) {f g : Profile → E} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    opQ ε f =ᶠ[𝓝 p] opQ ε g := by
  filter_upwards [pdQ_evEq h, opK_evEq h, h] with y h1 h2 h3
  simp only [opQ, h1, h2, h3]

end Local

/-- `A_ε^vec` is a local operator. -/
theorem AepsVecC_congr (ν ε : ℝ) {f g : Profile → MeridC} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    AepsVecC ν ε f p = AepsVecC ν ε g p := by
  simp only [AepsVecC, (opS_evEq h).eq_of_nhds, (opQ_evEq ε (opQ_evEq ε h)).eq_of_nhds,
    (pdEta_evEq (pdEta_evEq h)).eq_of_nhds, opE, h.eq_of_nhds]

/-- The generator difference `genDiffC` is a local operator. -/
theorem genDiffC_congr (ν ε : ℝ) {f g : Profile → MeridC} {p : Profile} (h : f =ᶠ[𝓝 p] g) :
    genDiffC ν ε f p = genDiffC ν ε g p := by
  simp only [genDiffC, genDiff1, genDiff2, (opLam_evEq (pdQ_evEq h)).eq_of_nhds,
    (opLam_evEq (opLam_evEq h)).eq_of_nhds, opE, h.eq_of_nhds]

theorem genDiffC_zero (ν ε : ℝ) (p : Profile) :
    genDiffC ν ε (fun _ => (0 : MeridC)) p = 0 := by
  have hQ : pdQ (fun _ : Profile => (0 : MeridC)) = fun _ => 0 := by
    funext y
    simp [pdQ]
  have hL : opLam (fun _ : Profile => (0 : MeridC)) = fun _ => 0 := by
    funext y
    simp [opLam, opK, opS, pdS, pdEta]
  simp [genDiffC, genDiff1, genDiff2, hQ, hL, opE]

/-- `measureH c` lives on `{s > 0}`. -/
theorem ae_pos_measureH (c : ℝ) : ∀ᵐ p ∂measureH c, 0 < p.1 := by
  have hac : measureH c ≪ cellMeasure c := withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le (ae_restrict_mem (measurableSet_cell c))] with p hp
  exact hp.1

/-- Two elements of `H` with almost everywhere disjoint supports are orthogonal. -/
theorem inner_eq_zero_of_ae_or {c : ℝ} (F G : HSpace c MeridC)
    (h : ∀ᵐ p ∂measureH c, (F : Profile → MeridC) p = 0 ∨ (G : Profile → MeridC) p = 0) :
    inner ℂ F G = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [h] with p hp
  rcases hp with hp | hp <;> simp [hp]

/-- `P_0 Z` vanishes above the age `H` when `Z` does (smooth cutoffs `χ = 1` on `s ≤ H`,
`χ = 0` on `s ≥ H + 1/(n+1)`, and `FlatProjCommSMul`). -/
theorem flatProjVanishAbove_of (hComm : FlatProjCommSMul) {c : ℝ} (hc : 0 < c) (H : ℝ)
    (Z : HSpace c MeridC)
    (hZ : ∀ᵐ p ∂measureH c, H < p.1 → (Z : Profile → MeridC) p = 0) :
    ∀ᵐ p ∂measureH c, H < p.1 → ((PepsC 0 c Z : HSpace c MeridC) : Profile → MeridC) p = 0 := by
  have hn : ∀ n : ℕ, ∀ᵐ p ∂measureH c, H + 1 / ((n : ℝ) + 1) ≤ p.1 →
      ((PepsC 0 c Z : HSpace c MeridC) : Profile → MeridC) p = 0 := by
    intro n
    set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
    have hδpos : 0 < δ := by positivity
    set χ : ℝ → ℝ := fun s => Real.smoothTransition ((H + δ - s) / δ) with hχ
    have hχs : ContDiff ℝ ∞ χ :=
      (Real.smoothTransition.contDiff (n := ⊤)).comp
        ((contDiff_const.sub contDiff_id).div_const δ)
    have hχB : ∃ B : ℝ, ∀ s, |χ s| ≤ B := ⟨1, fun s => by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _⟩
    have hχ1 : ∀ s, s ≤ H → χ s = 1 := fun s hs =>
      Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδpos]; linarith)
    have hχ0 : ∀ s, H + δ ≤ s → χ s = 0 := fun s hs =>
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδpos.le)
    have hZχ : (Z : Profile → MeridC) =ᵐ[measureH c]
        (fun p => (χ p.1 : ℂ) • (Z : Profile → MeridC) p) := by
      filter_upwards [hZ] with p hp
      by_cases h : H < p.1
      · simp [hp h]
      · rw [hχ1 p.1 (not_lt.1 h)]
        simp
    filter_upwards [hComm c hc χ hχs hχB Z Z hZχ] with p hp hle
    rw [hp, hχ0 p.1 hle]
    simp
  filter_upwards [ae_all_iff.2 hn] with p hp hlt
  obtain ⟨n, hn'⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
  exact hp n (by linarith)

/-- The band-tested residual identity: for a smooth meridional (band) test `w`,
`⟨(μ - A_ε) w, T_0^* Z⟩ = ⟨w, P_0 Z - (A_ε - A_0)^* v⟩`, from the accepted band leaves. -/
theorem bandWeakResidual (hFlat : FlatAdjointWeakEq) (hIBP : GenDiffIBP)
    {ν c ε : ℝ} (hν : 0 < ν) (hc : 0 < c) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    (Z : HSpace c MeridC) {v : Profile → MeridC}
    (hv_smooth : ContDiffOn ℝ ∞ v {p : Profile | 0 < p.1}) (hv_per : QPeriodic c v)
    (hV : ((ContinuousLinearMap.adjoint (T0flat hc ν μ) Z : HSpace c MeridC) :
      Profile → MeridC) =ᵐ[measureH c] v)
    (h1 : MemLp (genDiff1 ν v) 2 (measureH c)) (h2 : MemLp (genDiff2 ν v) 2 (measureH c))
    {w : Profile → MeridC} (hw : IsMeridTest c w) (W AWε : HSpace c MeridC)
    (hW : (W : Profile → MeridC) =ᵐ[measureH c] w)
    (hAWε : (AWε : Profile → MeridC) =ᵐ[measureH c] (fun p => μ • w p - AepsVecC ν ε w p)) :
    inner ℂ AWε (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z) =
      inner ℂ W (PepsC 0 c Z - (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v)) := by
  have hAU0_mem : MemLp (fun p => μ • w p - AepsVecC ν 0 w p) 2 (measureH c) :=
    memLp_mu_sub_AepsVecC ν 0 μ hw
  have hDU_mem : MemLp (genDiffC ν ε w) 2 (measureH c) :=
    memLp_genDiffC_isMeridTest ν ε hw
  set AU0 : HSpace c MeridC := hAU0_mem.toLp (fun p => μ • w p - AepsVecC ν 0 w p)
  set DU : HSpace c MeridC := hDU_mem.toLp (genDiffC ν ε w)
  have hdecomp : AWε = AU0 - DU := by
    apply Lp.ext
    filter_upwards [hAWε, Lp.coeFn_sub AU0 DU, hAU0_mem.coeFn_toLp, hDU_mem.coeFn_toLp]
      with p hp1 hp2 hp3 hp4
    rw [hp1, hp2, Pi.sub_apply, hp3, hp4]
    exact mu_sub_AepsVecC_eq ν ε μ (hw.smooth.contDiffAt.of_le (by simp))
  rw [hdecomp, inner_sub_left, inner_sub_right,
    hFlat ν c hc hν μ hγ Z w W AU0 hw hW hAU0_mem.coeFn_toLp,
    hIBP ν c ε hν hc w v W DU (ContinuousLinearMap.adjoint (T0flat hc ν μ) Z)
      hw hW hDU_mem.coeFn_toLp hv_smooth hv_per hV h1 h2]

end N04_3_Org

/-- **Assembly of `AdjointResidualEq` over axis-reaching core tests** (task `PartII-a:N04/3`
composes `adjointResidualEq` from it). With `V = T_0^* Z` and `R = P_0 Z - genDiffC ν ε v`, the
weak identity `⟨(μ - A_ε) u, V⟩ = ⟨u, R⟩` is checked on every core test `u` by replacing `u` with a
band test `w` agreeing with it on `0 < s < H_1 + 1`: both pairings only see `s ≤ H_1`, where `V`
and `R` live (source lines 1800–1806, 1836–1845). -/
theorem adjointResidualEq_of_core (hFlat : FlatAdjointWeakEq) (hIBP : GenDiffIBP)
    (hLoc : MeridCoreTestLocalize) (hComm : FlatProjCommSMul)
    (hWeak : RepsVecAdjointOfWeakEqCore) : AdjointResidualEq := by
  intro ν c σ H1 L1 hν hc _hσ _hσH1 _hL1 ε hε hε1 P _ hP hP1 μ hγ z v Z _hz hsupp hZ
    hv_smooth hv_per hv_supp hV h1 h2
  rw [ContinuousLinearMap.sub_apply, adjoint_Teps_eq hν hε hc hP hγ Z]
  set GD : HSpace c MeridC := (memLp_genDiffC h1 h2 ε).toLp (genDiffC ν ε v) with hGDdef
  suffices hT0 : ContinuousLinearMap.adjoint (T0flat hc ν μ) Z =
      ContinuousLinearMap.adjoint (B0223.RepsVec hν hε hc hP μ) (PepsC 0 c Z - GD) by
    rw [hT0, ← map_sub]
    congr 1
    simp only [ContinuousLinearMap.sub_apply]
    abel
  set V0 : HSpace c MeridC := ContinuousLinearMap.adjoint (T0flat hc ν μ) Z with hV0def
  have hpos := N04_3_Org.ae_pos_measureH c
  have hZv : ∀ᵐ p ∂measureH c, H1 < p.1 → (Z : Profile → MeridC) p = 0 := by
    filter_upwards [hZ] with p hp hlt
    rw [hp]
    by_contra hne
    exact absurd (hsupp p hne).2.1 (not_le.2 hlt)
  have hPv := N04_3_Org.flatProjVanishAbove_of hComm hc H1 Z hZv
  have hGDv : ∀ᵐ p ∂measureH c, H1 < p.1 → (GD : Profile → MeridC) p = 0 := by
    filter_upwards [(memLp_genDiffC h1 h2 ε).coeFn_toLp] with p hp hlt
    rw [hp]
    have hev : v =ᶠ[𝓝 p] (fun _ => (0 : MeridC)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hlt] with q hq
      exact hv_supp q hq
    rw [N04_3_Org.genDiffC_congr ν ε hev, N04_3_Org.genDiffC_zero]
  have hRv : ∀ᵐ p ∂measureH c, H1 < p.1 →
      ((PepsC 0 c Z - GD : HSpace c MeridC) : Profile → MeridC) p = 0 := by
    filter_upwards [hPv, hGDv, Lp.coeFn_sub (PepsC 0 c Z) GD] with p hp1 hp2 hp3 hlt
    rw [hp3, Pi.sub_apply, hp1 hlt, hp2 hlt, sub_zero]
  have hVv : ∀ᵐ p ∂measureH c, H1 < p.1 → (V0 : Profile → MeridC) p = 0 := by
    filter_upwards [hV] with p hp hlt
    rw [hp]
    exact hv_supp p hlt
  refine hWeak ν c ε hν hc hε hε1 P hP hP1 μ hγ V0 (PepsC 0 c Z - GD) ?_
  intro u U AUε hu hU hAUε
  obtain ⟨w, hw, hwu⟩ := hLoc ε c hε hc u hu (H1 + 1)
  have hW_mem : MemLp w 2 (measureH c) := memLp_isMeridTest hw
  have hAW_mem : MemLp (fun p => μ • w p - AepsVecC ν ε w p) 2 (measureH c) :=
    memLp_mu_sub_AepsVecC ν ε μ hw
  have hband := N04_3_Org.bandWeakResidual hFlat hIBP hν hc hγ Z hv_smooth hv_per hV h1 h2 hw
    (hW_mem.toLp w) (hAW_mem.toLp _) hW_mem.coeFn_toLp hAW_mem.coeFn_toLp
  have hopen : IsOpen {q : Profile | 0 < q.1 ∧ q.1 < H1 + 1} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hnear : ∀ p : Profile, 0 < p.1 → p.1 < H1 + 1 → u =ᶠ[𝓝 p] w := by
    intro p hp0 hp1
    filter_upwards [hopen.mem_nhds ⟨hp0, hp1⟩] with q hq
    exact (hwu q hq.1 hq.2).symm
  have hL : inner ℂ AUε V0 = inner ℂ (hAW_mem.toLp _) V0 := by
    rw [← sub_eq_zero, ← inner_sub_left]
    apply N04_3_Org.inner_eq_zero_of_ae_or
    filter_upwards [hpos, hVv, hAUε, hAW_mem.coeFn_toLp, Lp.coeFn_sub AUε (hAW_mem.toLp _)]
      with p hp0 hpV hpA hpW hps
    by_cases hlt : H1 < p.1
    · exact Or.inr (hpV hlt)
    · left
      have hn := hnear p hp0 (by linarith)
      rw [hps, Pi.sub_apply, hpA, hpW, N04_3_Org.AepsVecC_congr ν ε hn, hn.eq_of_nhds, sub_self]
  have hR : inner ℂ (hW_mem.toLp w) (PepsC 0 c Z - GD) = inner ℂ U (PepsC 0 c Z - GD) := by
    rw [← sub_eq_zero, ← inner_sub_left]
    apply N04_3_Org.inner_eq_zero_of_ae_or
    filter_upwards [hpos, hRv, hU, hW_mem.coeFn_toLp, Lp.coeFn_sub (hW_mem.toLp w) U]
      with p hp0 hpR hpU hpW hps
    by_cases hlt : H1 < p.1
    · exact Or.inr (hpR hlt)
    · left
      rw [hps, Pi.sub_apply, hpU, hpW, hwu p hp0 (by linarith), sub_self]
  exact hL.trans (hband.trans hR)

end UnforcedLeray.Short.PartIIa
