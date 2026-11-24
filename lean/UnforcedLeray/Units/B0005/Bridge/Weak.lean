import UnforcedLeray.Units.B0005.Bridge.Partition

/-!
# B0005 bridge, part 4: the distributional identities of the two encodings agree

Blueprint unit B0005 (tex 141–145: `hΔf, 𝒯₀f ∈ 𝒴_q` "in distributions") against
`Blueprint/Package.lean` (`laplacianPairing`, `driftPairing`: two-sided identities against all
smooth compactly supported real spacetime tests, with integrability clauses). For real periodic
fields `b, a ∈ 𝒴₂` (`IsY2`):

* `laplacianPairing_iff`: `∀ ψ, laplacianPairing b a ψ` ⟺ `Δ(toY b) = toY a` in the phase
  model (`HasPhaseOp lapT`);
* `hasHLap_iff`: for `h ≠ 0`, `hΔ(toY b) = h · toY a` ⟺ `Δ(toY b) = toY a`;
* `driftPairing_iff`: `∀ ψ, driftPairing b a ψ` ⟺ `𝒯₀(toY b) = toY a` (`HasT0`).

Direction `⇐` tests a compactly supported real `ψ` through its periodization (a phase test);
direction `⇒` writes a complex phase test as the periodization of a windowed test
(`perT_cutoffTest`) and splits it into real and imaginary parts.

Status: infrastructure for the B0005 bridge. Theorem A is not proved in Lean.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.B0005

open UnforcedLeray.PhaseSpace UnforcedLeray.PhaseTrace

/-! ### Derivatives commute with periodization -/

section PerT

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem dy_congr {Φ Ψ : ℝ × Space → F} {p : ℝ × Space} (h : Φ =ᶠ[𝓝 p] Ψ) (j : Fin 3) :
    dy j Φ p = dy j Ψ p := by
  simp only [dy, h.fderiv_eq]

theorem dy_sum_shift {G : ℝ × Space → F} (hGs : ContDiff ℝ ∞ G) (s : Finset ℤ) (P : ℝ)
    (j : Fin 3) :
    dy j (fun p => ∑ k ∈ s, G (p.1 + k * P, p.2)) =
      fun p => ∑ k ∈ s, dy j G (p.1 + k * P, p.2) := by
  funext p
  have hdiff : ∀ k ∈ s, DifferentiableAt ℝ (fun p : ℝ × Space => G (p.1 + k * P, p.2)) p :=
    fun k _ => ((contDiff_shift hGs _).differentiable (by simp)).differentiableAt
  simp only [dy]
  rw [fderiv_fun_sum hdiff, sum_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [fderiv_shift]

/-- `∂ⱼ` commutes with periodization. -/
theorem dy_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G)
    (hGs : ContDiff ℝ ∞ G) (j : Fin 3) : dy j (perT P G) = perT P (dy j G) := by
  funext p₀
  rw [dy_congr (perT_eventuallyEq hP hG p₀), dy_sum_shift hGs,
    perT_eq_sum (timeSupp_dy hG j) _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)]

/-- `Δ` commutes with periodization. -/
theorem lapT_perT {P : ℝ} (hP : 0 < P) {G : ℝ × Space → F} {A B : ℝ} (hG : TimeSupp A B G)
    (hGs : ContDiff ℝ ∞ G) : lapT (perT P G) = perT P (lapT G) := by
  funext p₀
  have hidx : ∀ {H : ℝ × Space → F}, TimeSupp A B H → perT P H p₀ =
      ∑ k ∈ perIdx P A B (p₀.1 - 1) (p₀.1 + 1), H (p₀.1 + k * P, p₀.2) := fun hH =>
    perT_eq_sum hH _ p₀
      (fun k hk => mem_perIdx (a := p₀.1 - 1) (b := p₀.1 + 1) hP ⟨by linarith, by linarith⟩ hk)
  simp only [lapT]
  simp_rw [dy_perT hP hG hGs, dy_perT hP (timeSupp_dy hG _) (contDiff_dy' hGs _),
    hidx (timeSupp_dy (timeSupp_dy hG _) _)]
  rw [hidx (timeSupp_lapT hG), Finset.sum_comm]
  rfl

end PerT

/-! ### Real tests -/

theorem exists_window_of_hasCompactSupport {F : Type*} [NormedAddCommGroup F]
    {χ : ℝ × Space → F} (hχ : HasCompactSupport χ) :
    ∃ R, 0 ≤ R ∧ TimeSupp (-R) R χ ∧ ∀ t y, R < ‖y‖ → χ (t, y) = 0 := by
  obtain ⟨R, hR⟩ := hχ.isCompact.isBounded.subset_closedBall 0
  have hz : ∀ t y, R < ‖((t, y) : ℝ × Space)‖ → χ (t, y) = 0 := fun t y h =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
  refine ⟨|R|, abs_nonneg R, fun t y ht => hz t y ?_, fun t y hy => hz t y ?_⟩
  · rw [Prod.norm_def]
    refine lt_max_of_lt_left ?_
    rw [Real.norm_eq_abs]
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · linarith [neg_le_abs t, le_abs_self R]
    · linarith [le_abs_self t, le_abs_self R]
  · rw [Prod.norm_def]
    exact lt_max_of_lt_right (by linarith [le_abs_self R])

theorem IsSimilarityTest.isPhaseTest {ψ : ℝ × Space → Space} (hψ : Blueprint.IsSimilarityTest ψ) :
    IsPhaseTest 0 ψ where
  smooth := hψ.smooth
  periodic := fun τ y => by simp
  bounded_support := by
    obtain ⟨R, -, -, hR⟩ := exists_window_of_hasCompactSupport hψ.compact
    exact ⟨R, hR⟩

theorem isSimilarityTest_of {ψ : ℝ × Space → Space} (hψ : IsPhaseTest 0 ψ) {A B : ℝ}
    (hT : TimeSupp A B ψ) : Blueprint.IsSimilarityTest ψ where
  smooth := hψ.smooth
  compact := by
    obtain ⟨R, hR⟩ := hψ.bounded_support
    refine HasCompactSupport.intro (K := Icc A B ×ˢ Metric.closedBall (0 : Space) R)
      ((isCompact_Icc (a := A) (b := B)).prod (isCompact_closedBall (0 : Space) R)) ?_
    intro z hz
    obtain ⟨t, y⟩ := z
    simp only [mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le] at hz
    rcases hz with h | h
    · exact hT t y h
    · exact hR t y h

/-- The real part of a complex test, `reL ∘ G`. -/
def reT (G : ℝ × Space → CVec3) : ℝ × Space → Space := fun p => reL (G p)

/-- The imaginary part of a complex test, `imL ∘ G`. -/
def imT (G : ℝ × Space → CVec3) : ℝ × Space → Space := fun p => imL (G p)

theorem timeSupp_clm {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] (L : F →L[ℝ] F') {G : ℝ × Space → F} {A B : ℝ}
    (hG : TimeSupp A B G) : TimeSupp A B (fun p => L (G p)) := fun t y ht => by
  simp [hG t y ht]

/-! ### Splitting the unfolded pairing into real and imaginary parts -/

section Split

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {f : ℝ → SpatialField}

theorem IsY2.phasePair_perT_split (hf : IsY2 𝒯 f) {G : ℝ × Space → CVec3}
    (hG0 : IsPhaseTest 0 G) {A B : ℝ} (hAB : A ≤ B) (hG : TimeSupp A B G) :
    phasePair 𝒯 2 (perT 𝒯 G) (toY 𝒯 f) =
      ((𝒯⁻¹ * ∫ z, Blueprint.pairTerm f (reT G) z : ℝ) : ℂ) +
        Complex.I * ((𝒯⁻¹ * ∫ z, Blueprint.pairTerm f (imT G) z : ℝ) : ℂ) := by
  have h1 := hf.pairTerm_unfold (hG0.clm_comp reL) hAB (timeSupp_clm reL hG)
  have h2 := hf.pairTerm_unfold (hG0.clm_comp imL) hAB (timeSupp_clm imL hG)
  rw [hf.phasePair_perT hG0 hAB hG]
  have hpt : ∀ z, dotL (G z) (jointC f z) = ((Blueprint.pairTerm f (reT G) z : ℝ) : ℂ) +
      Complex.I * ((Blueprint.pairTerm f (imT G) z : ℝ) : ℂ) := by
    intro z
    conv_lhs => rw [← cplxL_re_add_im (G z)]
    rw [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, jointC, dotL_cplxL, dotL_cplxL]
    rfl
  simp_rw [hpt]
  have hi1 : Integrable (fun z => ((Blueprint.pairTerm f (reT G) z : ℝ) : ℂ)) := h1.1.ofReal
  have hi2 : Integrable (fun z => Complex.I * ((Blueprint.pairTerm f (imT G) z : ℝ) : ℂ)) :=
    h2.1.ofReal.const_mul _
  rw [integral_add hi1 hi2, integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, Complex.real_smul]
  push_cast
  ring

theorem ofReal_mul_inj {x y : ℝ} (h : ((𝒯⁻¹ * x : ℝ) : ℂ) = ((𝒯⁻¹ * y : ℝ) : ℂ)) : x = y := by
  have h' := Complex.ofReal_injective h
  exact mul_left_cancel₀ (inv_ne_zero hT.out.ne') h'

end Split

/-! ### The Laplacian -/

section Lap

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {b a : ℝ → SpatialField}

theorem IsY2.laplacianPairing_of_phase (hb : IsY2 𝒯 b) (ha : IsY2 𝒯 a)
    (h : HasPhaseOp lapT (toY 𝒯 b) (toY 𝒯 a)) {ψ : ℝ × Space → Space}
    (hψ : Blueprint.IsSimilarityTest ψ) : Blueprint.laplacianPairing b a ψ := by
  obtain ⟨R, hR0, hRT, -⟩ := exists_window_of_hasCompactSupport hψ.compact
  have hAB : -R ≤ R := by linarith
  have hψ0 := IsSimilarityTest.isPhaseTest hψ
  have hc : IsPhaseTest 0 (cplxT ψ) := hψ0.clm_comp cplxL
  have hcs : TimeSupp (-R) R (cplxT ψ) := timeSupp_clm cplxL hRT
  have key := h _ (isPhaseTest_perT hT.out hcs hc)
  rw [lapT_perT hT.out hcs hc.smooth, lapT_cplxT hψ.smooth] at key
  have u1 := hb.pairTerm_unfold hψ0.lapT hAB (timeSupp_lapT hRT)
  have u2 := ha.pairTerm_unfold hψ0 hAB hRT
  rw [u1.2, u2.2] at key
  refine ⟨?_, u2.1, ?_⟩
  · rw [diffusionTerm_eq b hψ.smooth]; exact u1.1
  · rw [diffusionTerm_eq b hψ.smooth]; exact ofReal_mul_inj key

theorem IsY2.phase_of_laplacianPairing (hb : IsY2 𝒯 b) (ha : IsY2 𝒯 a)
    (h : ∀ ψ, Blueprint.IsSimilarityTest ψ → Blueprint.laplacianPairing b a ψ) :
    HasPhaseOp lapT (toY 𝒯 b) (toY 𝒯 a) := by
  intro Φ hΦ
  set G := cutoffTest 𝒯 Φ with hGdef
  have hG0 : IsPhaseTest 0 G := isPhaseTest_cutoffTest hΦ
  have hGT : TimeSupp (winA 𝒯) (winB 𝒯) G := timeSupp_cutoffTest Φ
  have hAB := winA_le_winB 𝒯
  have hperG : perT 𝒯 G = Φ := perT_cutoffTest hΦ
  have hL0 : IsPhaseTest 0 (lapT G) := hG0.lapT
  have hLT : TimeSupp (winA 𝒯) (winB 𝒯) (lapT G) := timeSupp_lapT hGT
  have hre : reT (lapT G) = lapT (reT G) := (lapT_clm reL hG0.smooth).symm
  have him : imT (lapT G) = lapT (imT G) := (lapT_clm imL hG0.smooth).symm
  have hreS : Blueprint.IsSimilarityTest (reT G) :=
    isSimilarityTest_of (hG0.clm_comp reL) (timeSupp_clm reL hGT)
  have himS : Blueprint.IsSimilarityTest (imT G) :=
    isSimilarityTest_of (hG0.clm_comp imL) (timeSupp_clm imL hGT)
  have e1 := (h _ hreS).eq
  have e2 := (h _ himS).eq
  rw [diffusionTerm_eq b hreS.smooth] at e1
  rw [diffusionTerm_eq b himS.smooth] at e2
  rw [← hperG, lapT_perT hT.out hGT hG0.smooth, hb.phasePair_perT_split hL0 hAB hLT,
    ha.phasePair_perT_split hG0 hAB hGT, hre, him]
  change ((𝒯⁻¹ * ∫ z, Blueprint.pairTerm b (lapT (reT G)) z : ℝ) : ℂ) +
      Complex.I * ((𝒯⁻¹ * ∫ z, Blueprint.pairTerm b (lapT (imT G)) z : ℝ) : ℂ) = _
  rw [e1, e2]

/-- **The Laplacian identities agree**: `∀ ψ, laplacianPairing b a ψ` (interface) iff
`Δ (toY b) = toY a` in distributions (phase model). -/
theorem IsY2.laplacianPairing_iff (hb : IsY2 𝒯 b) (ha : IsY2 𝒯 a) :
    (∀ ψ, Blueprint.IsSimilarityTest ψ → Blueprint.laplacianPairing b a ψ) ↔
      HasPhaseOp lapT (toY 𝒯 b) (toY 𝒯 a) :=
  ⟨hb.phase_of_laplacianPairing ha, fun h _ hψ => hb.laplacianPairing_of_phase ha h hψ⟩

/-- For `h ≠ 0`, `hΔf = h a` iff `Δf = a` (tex 141: `hΔf ∈ 𝒴_q` is `Δf ∈ 𝒴_q`). -/
theorem hasHLap_iff {h : ℝ} (hh : h ≠ 0) {f g : Y 𝒯 2} :
    HasHLap h f ((h : ℂ) • g) ↔ HasPhaseOp lapT f g := by
  have hc : ∀ Φ, IsPhaseTest 𝒯 Φ → phasePair 𝒯 2 (nuLapT h Φ) f = (h : ℂ) * phasePair 𝒯 2 (lapT Φ) f := by
    intro Φ hΦ
    rw [nuLapT, phasePair_real_smul hΦ.lapT]
  constructor
  · intro H Φ hΦ
    have := H Φ hΦ
    rw [hc Φ hΦ, map_smul, smul_eq_mul] at this
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hh) this
  · intro H Φ hΦ
    rw [hc Φ hΦ, map_smul, smul_eq_mul, H Φ hΦ]

end Lap

/-! ### The drift `𝒯₀` -/

section Drift

variable {𝒯 : ℝ} [hT : Fact (0 < 𝒯)] {b d : ℝ → SpatialField}

theorem IsY2.driftPairing_of_phase (hb : IsY2 𝒯 b) (hd : IsY2 𝒯 d)
    (h : HasT0 (toY 𝒯 b) (toY 𝒯 d)) {ψ : ℝ × Space → Space}
    (hψ : Blueprint.IsSimilarityTest ψ) : Blueprint.driftPairing b d ψ := by
  obtain ⟨R, hR0, hRT, -⟩ := exists_window_of_hasCompactSupport hψ.compact
  have hAB : -R ≤ R := by linarith
  have hψ0 := IsSimilarityTest.isPhaseTest hψ
  have hdiff : Differentiable ℝ ψ := hψ.smooth.differentiable (by simp)
  have hc : IsPhaseTest 0 (cplxT ψ) := hψ0.clm_comp cplxL
  have hcs : TimeSupp (-R) R (cplxT ψ) := timeSupp_clm cplxL hRT
  have key := h _ (isPhaseTest_perT hT.out hcs hc)
  rw [driftT_perT hT.out hcs hc.smooth, driftT_cplxT hdiff] at key
  have u1 := hb.pairTerm_unfold hψ0.driftT hAB (timeSupp_driftT hRT)
  have u2 := hd.pairTerm_unfold hψ0 hAB hRT
  rw [u1.2, u2.2] at key
  refine ⟨?_, u2.1, ?_⟩
  · rw [driftAdjointTerm_eq b hdiff]; exact u1.1
  · rw [driftAdjointTerm_eq b hdiff]; exact ofReal_mul_inj key

theorem IsY2.phase_of_driftPairing (hb : IsY2 𝒯 b) (hd : IsY2 𝒯 d)
    (h : ∀ ψ, Blueprint.IsSimilarityTest ψ → Blueprint.driftPairing b d ψ) :
    HasT0 (toY 𝒯 b) (toY 𝒯 d) := by
  intro Φ hΦ
  set G := cutoffTest 𝒯 Φ with hGdef
  have hG0 : IsPhaseTest 0 G := isPhaseTest_cutoffTest hΦ
  have hGT : TimeSupp (winA 𝒯) (winB 𝒯) G := timeSupp_cutoffTest Φ
  have hAB := winA_le_winB 𝒯
  have hperG : perT 𝒯 G = Φ := perT_cutoffTest hΦ
  have hGd : Differentiable ℝ G := hG0.smooth.differentiable (by simp)
  have hL0 : IsPhaseTest 0 (driftT G) := hG0.driftT
  have hLT : TimeSupp (winA 𝒯) (winB 𝒯) (driftT G) := timeSupp_driftT hGT
  have hre : reT (driftT G) = driftT (reT G) := (driftT_clm reL hGd).symm
  have him : imT (driftT G) = driftT (imT G) := (driftT_clm imL hGd).symm
  have hreS : Blueprint.IsSimilarityTest (reT G) :=
    isSimilarityTest_of (hG0.clm_comp reL) (timeSupp_clm reL hGT)
  have himS : Blueprint.IsSimilarityTest (imT G) :=
    isSimilarityTest_of (hG0.clm_comp imL) (timeSupp_clm imL hGT)
  have e1 := (h _ hreS).eq
  have e2 := (h _ himS).eq
  rw [driftAdjointTerm_eq b (hreS.smooth.differentiable (by simp))] at e1
  rw [driftAdjointTerm_eq b (himS.smooth.differentiable (by simp))] at e2
  rw [← hperG, driftT_perT hT.out hGT hG0.smooth, hb.phasePair_perT_split hL0 hAB hLT,
    hd.phasePair_perT_split hG0 hAB hGT, hre, him]
  change ((𝒯⁻¹ * ∫ z, Blueprint.pairTerm b (driftT (reT G)) z : ℝ) : ℂ) +
      Complex.I * ((𝒯⁻¹ * ∫ z, Blueprint.pairTerm b (driftT (imT G)) z : ℝ) : ℂ) = _
  rw [e1, e2]

/-- **The drift identities agree**: `∀ ψ, driftPairing b d ψ` (interface) iff
`𝒯₀ (toY b) = toY d` in distributions (phase model). -/
theorem IsY2.driftPairing_iff (hb : IsY2 𝒯 b) (hd : IsY2 𝒯 d) :
    (∀ ψ, Blueprint.IsSimilarityTest ψ → Blueprint.driftPairing b d ψ) ↔
      HasT0 (toY 𝒯 b) (toY 𝒯 d) :=
  ⟨hb.phase_of_driftPairing hd, fun h _ hψ => hb.driftPairing_of_phase hd h hψ⟩

end Drift

end UnforcedLeray.B0005
