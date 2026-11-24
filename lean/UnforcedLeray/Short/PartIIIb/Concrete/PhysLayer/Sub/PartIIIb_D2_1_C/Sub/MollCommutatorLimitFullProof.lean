import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.MollCommDefs

/-!
# `MollCommutatorLimitFull` from the Friedrichs ingredients

Source `the November 2 reference manuscript` lines 1351-1362, 1556-1583.
Step 1: the full equation tested against periodised translates of `ρ` gives the exact identity
`(μ + L₀ᵗ)(ρ ⋆ Φ) - ρ ⋆ g = commK ρ Φ`.  Step 2: the commutator is `Y_2`-bounded uniformly in `ρ`,
small on tests, and tests are dense.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- Step 1: the exact commutator identity from the full adjoint equation. -/
theorem moll_identity (hA : MollKernelAdj) (hB1 : ShiftTestPhase) (hB2 : ShiftPairUnfold)
    (hB3 : ShiftTestOpEq) (hB4 : TestKerSmooth) (hF : MollIntegralSplit)
    (hG : NormedBumpSmooth)
    (P ν μ : ℝ) (hP : 0 < P) (Φ g : ℝ × Space → CVec3)
    (hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 Φ) (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g)
    (hEq : ∀ Ψ, IsPhaseTest P Ψ →
      pairF P (fun x => L0 ν Ψ x + (μ : ℂ) • Ψ x) Φ = pairF P Ψ g)
    (ρ : ContDiffBump (0 : ℝ × Space)) (x : ℝ × Space) :
    L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x - mollP ρ g x = commK ρ Φ x := by
  have hall : ∀ e : CVec3, dotL e (L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x - commK ρ Φ x
      - mollP ρ g x) = 0 := by
    intro e
    have h1 := hEq _ (hB1 P hP ρ x e)
    have h2 : (fun y => L0 ν (shiftTest P ρ x e) y + (μ : ℂ) • shiftTest P ρ x e y) =
        shiftKer P (testKer ν μ ρ x) x e := hB3 P ν μ hP ρ x e
    rw [h2, hB2 P hP _ (hB4 ν μ ρ x).1 (hB4 ν μ ρ x).2 Φ hΦ x e,
      show shiftTest P ρ x e = shiftKer P (ρ.normed volume) x e from rfl,
      hB2 P hP _ (hG ρ).1 (hG ρ).2 g hg x e, hF P ν μ hP Φ hΦ ρ x, ← hA P ν μ hP Φ hΦ ρ x] at h1
    have h3 : mollP ρ g x = ∫ z, ρ.normed volume z • g (x - z) := rfl
    rw [← h3] at h1
    have hP0 : (P⁻¹ : ℂ) ≠ 0 := by
      have : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
      exact inv_ne_zero this
    have h4 := mul_left_cancel₀ hP0 h1
    rw [map_sub, h4, sub_self]
  have hV : L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x - commK ρ Φ x - mollP ρ g x = 0 := by
    ext j
    have := hall (EuclideanSpace.single j 1)
    simpa [dotL_apply] using this
  have := hV
  rw [sub_right_comm] at this
  exact sub_eq_zero.mp this

/-- Minkowski for a sum of two measurable fields. -/
theorem commAddLe (P : ℝ) (hP : 0 < P) (u v : ℝ × Space → CVec3)
    (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume) :
    UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun x => u x + v x) ≤
      UnforcedLeray.Short.IIb.phaseLpNorm P 2 u + UnforcedLeray.Short.IIb.phaseLpNorm P 2 v := by
  have h := phaseLpTri2 P (fun x => u x + v x) u (fun _ => 0) hP (hu.add hv) hu
    aestronglyMeasurable_const
  have e1 : (fun x => (u x + v x) - (fun _ : ℝ × Space => (0 : CVec3)) x) = fun x => u x + v x := by
    funext x; simp
  have e2 : (fun x => (u x + v x) - u x) = v := by funext x; simp
  have e3 : (fun x => u x - (fun _ : ℝ × Space => (0 : CVec3)) x) = u := by funext x; simp
  rw [e1, e2, e3] at h
  rw [add_comm] at h
  exact h

/-- **Assembly** of `MollCommutatorLimitFull` from the ingredients. -/
theorem mollCommutatorLimitFull_of (hA : MollKernelAdj) (hB1 : ShiftTestPhase)
    (hB2 : ShiftPairUnfold) (hB3 : ShiftTestOpEq) (hB4 : TestKerSmooth)
    (hF : MollIntegralSplit) (hG : NormedBumpSmooth) (hFr : FriedrichsBound)
    (hT : CommTestLimit) (hDense : PhaseTestDense) (hSub : CommSub) (hM : CommMeas) :
    MollCommutatorLimitFull := by
  intro P ν μ hP hP1 hν hμ Φ g hΦ _hY hEq ε hε
  obtain ⟨C, hC, hCb⟩ := hFr P hP hP1
  obtain ⟨Ψ, hΨ, hD, hDn⟩ := hDense P hP Φ hΦ.mem (ε / (2 * C)) (by positivity)
  obtain ⟨δ, hδ, hδ'⟩ := hT P hP Ψ hΨ (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun ρ hρ hρ2 => ?_⟩
  have hid : (fun x => L0T ν (mollP ρ Φ) x + (μ : ℂ) • mollP ρ Φ x - mollP ρ g x) =
      commK ρ Φ :=
    funext fun x => moll_identity hA hB1 hB2 hB3 hB4 hF hG P ν μ hP Φ g hΦ.mem hΦ.mem_g hEq ρ x
  rw [hid]
  have hsplit : commK ρ Φ = fun x => commK ρ (fun w => Φ w - Ψ w) x + commK ρ Ψ x :=
    funext fun x => hSub P hP Φ Ψ hΦ.mem hΨ ρ x
  rw [hsplit]
  have h1 : UnforcedLeray.Short.IIb.phaseLpNorm P 2 (commK ρ (fun w => Φ w - Ψ w)) <
      ENNReal.ofReal (ε / 2) := by
    calc _ ≤ ENNReal.ofReal C *
          UnforcedLeray.Short.IIb.phaseLpNorm P 2 (fun w => Φ w - Ψ w) := hCb ρ hρ2 _ hD
      _ < ENNReal.ofReal C * ENNReal.ofReal (ε / (2 * C)) := by
          rw [ENNReal.mul_lt_mul_iff_right (by simpa using hC) ENNReal.ofReal_ne_top]
          exact hDn
      _ = ENNReal.ofReal (ε / 2) := by
          rw [← ENNReal.ofReal_mul hC.le]
          congr 1
          field_simp
  have h2 := hδ' ρ hρ
  calc _ ≤ UnforcedLeray.Short.IIb.phaseLpNorm P 2 (commK ρ (fun w => Φ w - Ψ w)) +
        UnforcedLeray.Short.IIb.phaseLpNorm P 2 (commK ρ Ψ) :=
        commAddLe P hP _ _ (hM P hP ρ _ (Or.inl hD)) (hM P hP ρ _ (Or.inr hΨ))
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add h1 h2
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end UnforcedLeray.Short.PartIIIb.Concrete
