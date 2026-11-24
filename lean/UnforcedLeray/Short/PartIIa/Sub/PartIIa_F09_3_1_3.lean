import UnforcedLeray.Short.PartIIa.Sub.PartIIa_F09_3_1
import UnforcedLeray.Short.PartIIa.Tasks.F03cWindowBackEquation

/-!
# Part II-a, task `PartII-a:F09/3/1/3`: `AdjointWindowBackEquation` from two chart leaves

Source `the November 2 reference manuscript`
lines 1426-1442, 1431-1441 (reversed window, `θ = 1 - e^{-t}`, `x = e^{-t/2} y`). The passage from
the real-test identity to the vector weak Laplacian is the (copied) component/vector argument of
`Tasks/F03cWindowBackEquation.lean`; only the chart computation (`AdjBackRealIdentity`) and the
integrability of the transported side (`AdjBackLambdaInt`) are chart specific.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Parabolic UnforcedLeray.B0424
  UnforcedLeray.Short.PartIIa.Rep UnforcedLeray.Short.PartIIa.WinBack

/-- **Sub-lemma C1 (the real-test identity through the reversed chart).** For a real smooth
compactly supported test `a` with support in the window `(τ₀-1,τ₀+1) × ℝ³` and `D2` the weak second
derivatives (in `L^r`) of `u_c = adjWindowField χ τ₀ W c`:
`∫ W_c · (ν Δa) = ∫ adjWindowLap(Σ_i D2 c i i)_c · a`.  Proof: transfer both sides through
`(t,y) ↦ (1 - e^{-t}, e^{-t/2} y)` (density `e^{-5t/2}`; `χ = 1` on the support), applying the
weak derivative to the test `lapTestAdj τ₀ a (θ,x) = (1-θ) a(τ₀ + log(1-θ), (1-θ)^{-1/2} x)`-type
rescaling of `a` (analogue of `real_identity`, `Tasks/F03cWindowBackEquation.lean`). -/
def AdjBackRealIdentity : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (P : ℝ) [Fact (0 < P)] (w : Yq P r)
    (W : ℝ × Space → CVec3), IsRep w W → ∀ χ : ℝ → ℝ, WindowCutoff χ → ∀ (τ₀ ν : ℝ) (c : Fin 3)
    (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ),
    (∀ i, MemLp (D2 c i i) r volume ∧
      UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (adjWindowField χ τ₀ W c) i i (D2 c i i)) →
    ∀ {a : PS 3 → ℝ}, IsSTTest a →
      tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) →
        ∫ p : ℝ × Space, W p c * ((ν * sLap a p : ℝ) : ℂ) =
          ∫ p : ℝ × Space, adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ((a p : ℝ) : ℂ)

/-- **Sub-lemma C2 (integrability of the transported side).** Analogue of `integrable_lambda_real`
(`Tasks/F03cWindowBackEquation.lean`): for `D2 c i i ∈ L^r` and a real test `a` supported in the
window, `p ↦ adjWindowLap(Σ_i D2 c i i)_c(p) · a(p)` is integrable (change of variables through
`(t,y) ↦ (1 - e^{-t}, e^{-t/2} y)`). -/
def AdjBackLambdaInt : Prop :=
  ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → ∀ (τ₀ ν : ℝ) (c : Fin 3)
    (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ), (∀ i, MemLp (D2 c i i) r volume) →
    ∀ {a : PS 3 → ℝ}, IsSTTest a →
      tsupport a ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) →
        Integrable (fun p : ℝ × Space =>
          adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ((a p : ℝ) : ℂ))

variable {P : ℝ} [Fact (0 < P)]

theorem adj_component_identity (hRI : AdjBackRealIdentity) (hLI : AdjBackLambdaInt)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {w : Yq P r}
    {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ) (τ₀ ν : ℝ)
    (c : Fin 3) (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ)
    (hD2 : ∀ i, MemLp (D2 c i i) r volume ∧
      UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (adjWindowField χ τ₀ W c) i i (D2 c i i))
    {ψc : ℝ × Space → ℂ} (hψc : ContDiff ℝ ∞ ψc) (hψcs : HasCompactSupport ψc)
    (hψw : tsupport ψc ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    Integrable (fun p => W p c * (ν * lapT ψc p)) ∧
      Integrable (fun p => adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p) ∧
      ∫ p, W p c * (ν * lapT ψc p) =
        ∫ p, adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p := by
  have hre : ContDiff ℝ ∞ (fun q => (ψc q).re) := Complex.reCLM.contDiff.comp hψc
  have him : ContDiff ℝ ∞ (fun q => (ψc q).im) := Complex.imCLM.contDiff.comp hψc
  have hcsa : HasCompactSupport (fun q => (ψc q).re) := hψcs.comp_left Complex.zero_re
  have hcsb : HasCompactSupport (fun q => (ψc q).im) := hψcs.comp_left Complex.zero_im
  have hsa : tsupport (fun q => (ψc q).re : PS 3 → ℝ) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
    (tsupport_comp_subset Complex.zero_re ψc).trans hψw
  have hsb : tsupport (fun q => (ψc q).im : PS 3 → ℝ) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
    (tsupport_comp_subset Complex.zero_im ψc).trans hψw
  have ha : IsSTTest (fun q => (ψc q).re : PS 3 → ℝ) := ⟨hre, hcsa⟩
  have hb : IsSTTest (fun q => (ψc q).im : PS 3 → ℝ) := ⟨him, hcsb⟩
  have hIA := hRI r hrt P w W hW χ hχ τ₀ ν c D2 hD2 ha hsa
  have hIB := hRI r hrt P w W hW χ hχ τ₀ ν c D2 hD2 hb hsb
  have hJA := hLI r hrt τ₀ ν c D2 (fun i => (hD2 i).1) ha hsa
  have hJB := hLI r hrt τ₀ ν c D2 (fun i => (hD2 i).1) hb hsb
  have hWA : Integrable (fun p => W p c * ((ν * sLap (fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    have h1 := integrable_W_mul_real hrt hW τ₀ c (UnforcedLeray.Parabolic.isSTTest_sLap ha)
      (fun q hq => sLap_zero_off_window hsa q hq)
    refine (h1.const_mul (ν : ℂ)).congr (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hWB : Integrable (fun p => W p c * ((ν * sLap (fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    have h1 := integrable_W_mul_real hrt hW τ₀ c (UnforcedLeray.Parabolic.isSTTest_sLap hb)
      (fun q hq => sLap_zero_off_window hsb q hq)
    refine (h1.const_mul (ν : ℂ)).congr (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hlapc : ∀ p, lapT ψc p = ((sLap (fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ) +
      ((sLap (fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ) * Complex.I :=
    fun p => lapT_complex hψc p
  have hLHS : ∀ p, W p c * (ν * lapT ψc p) =
      W p c * ((ν * sLap (fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ) +
        Complex.I * (W p c * ((ν * sLap (fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    intro p
    rw [hlapc p]
    push_cast
    ring
  have hdec : ∀ p, ψc p = ((ψc p).re : ℂ) + ((ψc p).im : ℂ) * Complex.I :=
    fun p => (Complex.re_add_im (ψc p)).symm
  have hRHS : ∀ p, adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p =
      adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * (((fun q => (ψc q).re : PS 3 → ℝ) p : ℝ) : ℂ) +
        Complex.I * (adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c *
          (((fun q => (ψc q).im : PS 3 → ℝ) p : ℝ) : ℂ)) := by
    intro p
    conv_lhs => rw [hdec p]
    simp only []
    ring
  have hiLHS : Integrable (fun p => W p c * (ν * lapT ψc p)) :=
    (hWA.add (hWB.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun p => (hLHS p).symm)
  have hiRHS : Integrable (fun p => adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψc p) :=
    (hJA.add (hJB.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun p => (hRHS p).symm)
  refine ⟨hiLHS, hiRHS, ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hLHS),
    integral_congr_ae (Filter.Eventually.of_forall hRHS),
    integral_add hWA (hWB.const_mul Complex.I), integral_add hJA (hJB.const_mul Complex.I),
    integral_const_mul, integral_const_mul, hIA, hIB]

/-! ### The vector statement -/

theorem dotL_lap_eq {ν : ℝ} {W : ℝ × Space → CVec3} {ψ : ℝ × Space → CVec3}
    (hψ : ContDiff ℝ ∞ ψ) (p : ℝ × Space) :
    dotL (W p) (ν • lapT ψ p) = ∑ c : Fin 3, W p c * (ν * lapT (fun q => ψ q c) p) := by
  rw [dotL_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lapT_apply_comp hψ c p]
  simp only [PiLp.smul_apply, Complex.real_smul]


/-- **`PartII-a:F09/3/1/3`, conditional on the two chart leaves.** -/
theorem adjointWindowBackEquation_of (hRI : AdjBackRealIdentity) (hLI : AdjBackLambdaInt) :
    AdjointWindowBackEquation := by
  intro r _ hrt P _ ν w W hW χ hχ τ₀ D2 hD2
  unfold IsWindowLaplacian
  intro ψ hψ hψc hψw
  have hD2' : ∀ c i, MemLp (D2 c i i) r volume ∧
      UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (adjWindowField χ τ₀ W c) i i (D2 c i i) := by
    intro c i
    refine ⟨?_, (hD2 c i i).2⟩
    have h := (hD2 c i i).1
    rwa [ENNReal.ofReal_toReal hrt] at h
  have hψcomp : ∀ c : Fin 3, ContDiff ℝ ∞ (fun q => ψ q c) := fun c =>
    ((EuclideanSpace.proj c : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hψ
  have hcs : ∀ c : Fin 3, HasCompactSupport (fun q => ψ q c) := fun c =>
    hψc.comp_left (g := fun v : CVec3 => v c) (by simp)
  have hsup : ∀ c : Fin 3, tsupport (fun q => ψ q c) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) := fun c =>
    (tsupport_comp_subset (g := fun v : CVec3 => v c) (by simp) ψ).trans hψw
  have hcomp : ∀ c : Fin 3,
      Integrable (fun p => W p c * (ν * lapT (fun q => ψ q c) p)) ∧
      Integrable (fun p => adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψ p c) ∧
      ∫ p, W p c * (ν * lapT (fun q => ψ q c) p) =
        ∫ p, adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψ p c := fun c =>
    adj_component_identity hRI hLI hrt hW hχ τ₀ ν c D2 (hD2' c) (hψcomp c) (hcs c) (hsup c)
  have e1 : (fun p => dotL (W p) (ν • lapT ψ p)) =
      fun p => ∑ c : Fin 3, W p c * (ν * lapT (fun q => ψ q c) p) :=
    funext fun p => dotL_lap_eq hψ p
  have e2 : (fun p => dotL (adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p) (ψ p)) =
      fun p => ∑ c : Fin 3, adjWindowLap ν τ₀ (fun c X => ∑ i, D2 c i i X) p c * ψ p c :=
    funext fun p => dotL_apply _ _
  rw [e1, e2]
  refine ⟨integrable_finsetSum _ fun c _ => (hcomp c).1,
    integrable_finsetSum _ fun c _ => (hcomp c).2.1, ?_⟩
  rw [integral_finsetSum _ fun c _ => (hcomp c).1, integral_finsetSum _ fun c _ => (hcomp c).2.1]
  exact Finset.sum_congr rfl fun c _ => (hcomp c).2.2


end UnforcedLeray.Short.PartIIa
