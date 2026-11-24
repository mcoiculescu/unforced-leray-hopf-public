import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.HessRealIdentity
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.Hess.HessCalc

/-!
# Transport back of the window Hessian (source 1426-1436)

Task `PartIII-b:C/ward/12/3/1/2/2/5`.  Hessian analogue of `PartII-a:F03/3`
(`windowBackEquation`, template `Tasks/F03cWindowBackEquation.lean`, lines 169-309).

Route: for a smooth compactly supported `ℂ³`-valued test `ψ` in the window, each component
`φ = ψ · c` is split into real and imaginary parts (`dy_dy_complex`), the real parts are handled
by `hess_real_identity`, and the component sum gives the vector statement.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.Short.PartIIa.Rep
open UnforcedLeray.Parabolic (PS IsSTTest sD2)
open UnforcedLeray.Short.PartIIa (WindowCutoff windowField windowLap winSet)

/-- The second derivative `sD2 j k` of a test vanishes off the window. -/
theorem hsWB_sD2_zero_off_window {τ₀ : ℝ} {g : PS 3 → ℝ} (j k : Fin 3)
    (hg : tsupport g ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) (q : ℝ × Space)
    (hq : q ∉ Icc (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) : sD2 j k g q = 0 := by
  by_contra hne
  have hm := hg (UnforcedLeray.Short.PartIIa.WinBack.sD2_tsupport_subset j k g
    (subset_tsupport _ (Function.mem_support.2 hne)))
  exact hq ⟨Ioo_subset_Icc_self hm.1, hm.2⟩

/-- Integrability of `W · g` for a real test `g` of `IsSTTest` type supported in the window. -/
theorem hsWB_integrable_W_mul_real {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {P : ℝ}
    [Fact (0 < P)] {w : Yq P r} {W : ℝ × Space → CVec3} (hW : IsRep w W) (τ₀ : ℝ) (c : Fin 3)
    {g : ℝ × Space → ℝ} (hg : IsSTTest g)
    (hz : ∀ q, q ∉ Icc (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) → g q = 0) :
    Integrable (fun p => W p c * ((g p : ℝ) : ℂ)) :=
  UnforcedLeray.Short.PartIIa.WinBack.integrable_W_mul_real hrt hW τ₀ c hg hz

/-- The component `c` of `dy j (dy k Φ)` is the second derivative of the component `Φ · c`. -/
theorem hsWB_dy_dy_comp {Φ : ℝ × Space → CVec3} (hΦ : ContDiff ℝ ∞ Φ) (j k c : Fin 3)
    (p : ℝ × Space) :
    dy j (dy k Φ) p c = dy j (dy k (fun q => Φ q c)) p := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hdk : Differentiable ℝ (dy k Φ) := (UnforcedLeray.Short.PartIIa.WinBack.contDiff_dy_gen
    hΦ k).differentiable (by simp)
  have h1 : dy k (fun q => Φ q c) = fun q => (EuclideanSpace.proj c : CVec3 →L[ℂ] ℂ) (dy k Φ q) :=
    UnforcedLeray.Short.PartIIa.WinBack.dy_clm (L := EuclideanSpace.proj c) hΦd k
  have h2 := UnforcedLeray.Short.PartIIa.WinBack.dy_clm (L := EuclideanSpace.proj c) hdk j
  rw [h1]
  exact (congrFun h2 p).symm

/-- The Hessian pairing on a vector test, componentwise. -/
theorem hsWB_dotL_nuHess {ν : ℝ} {W ψ : ℝ × Space → CVec3} (hψ : ContDiff ℝ ∞ ψ) (j k : Fin 3)
    (p : ℝ × Space) :
    dotL (W p) (nuHessT ν j k ψ p) =
      ∑ c : Fin 3, W p c * (ν * dy j (dy k (fun q => ψ q c)) p) := by
  rw [dotL_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hsWB_dy_dy_comp hψ j k c p]
  simp only [nuHessT, Pi.smul_apply, PiLp.smul_apply, Complex.real_smul]

/-- Real and imaginary parts of a smooth complex component. -/
theorem hsWB_component {r : ℝ≥0∞} [Fact (1 ≤ r)] (hrt : r ≠ ⊤) {P : ℝ} [Fact (0 < P)]
    {w : Yq P r} {W : ℝ × Space → CVec3} (hW : IsRep w W) {χ : ℝ → ℝ} (hχ : WindowCutoff χ)
    (τ₀ ν : ℝ) (j k c : Fin 3) (D2 : Fin 3 → Fin 3 → Fin 3 → PS 3 → ℂ)
    (hD2 : MemLp (D2 c j k) r volume ∧ UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3)
      (windowField χ τ₀ W c) j k (D2 c j k))
    {φ : ℝ × Space → ℂ} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hφw : tsupport φ ⊆ Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space)) :
    Integrable (fun p => W p c * (ν * dy j (dy k φ) p)) ∧
      Integrable (fun p => windowLap ν τ₀ (fun c X => D2 c j k X) p c * φ p) ∧
      ∫ p, W p c * (ν * dy j (dy k φ) p) =
        ∫ p, windowLap ν τ₀ (fun c X => D2 c j k X) p c * φ p := by
  have hre : ContDiff ℝ ∞ (fun q => (φ q).re) := Complex.reCLM.contDiff.comp hφ
  have him : ContDiff ℝ ∞ (fun q => (φ q).im) := Complex.imCLM.contDiff.comp hφ
  have hcsa : HasCompactSupport (fun q => (φ q).re) := hφs.comp_left Complex.zero_re
  have hcsb : HasCompactSupport (fun q => (φ q).im) := hφs.comp_left Complex.zero_im
  have hsa : tsupport (fun q => (φ q).re : PS 3 → ℝ) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
    (tsupport_comp_subset Complex.zero_re φ).trans hφw
  have hsb : tsupport (fun q => (φ q).im : PS 3 → ℝ) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) :=
    (tsupport_comp_subset Complex.zero_im φ).trans hφw
  have ha : IsSTTest (fun q => (φ q).re : PS 3 → ℝ) := ⟨hre, hcsa⟩
  have hb : IsSTTest (fun q => (φ q).im : PS 3 → ℝ) := ⟨him, hcsb⟩
  have hA := hess_real_identity hrt hW hχ τ₀ ν c j k D2 hD2 ha hsa
  have hB := hess_real_identity hrt hW hχ τ₀ ν c j k D2 hD2 hb hsb
  have hWA : Integrable (fun p => W p c *
      ((ν * sD2 j k (fun q => (φ q).re) p : ℝ) : ℂ)) := by
    have h1 := hsWB_integrable_W_mul_real hrt hW τ₀ c
      (UnforcedLeray.Parabolic.IsSTTest.sD2 ha j k)
      (fun q hq => hsWB_sD2_zero_off_window j k hsa q hq)
    refine (h1.const_mul (ν : ℂ)).congr (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hWB : Integrable (fun p => W p c *
      ((ν * sD2 j k (fun q => (φ q).im) p : ℝ) : ℂ)) := by
    have h1 := hsWB_integrable_W_mul_real hrt hW τ₀ c
      (UnforcedLeray.Parabolic.IsSTTest.sD2 hb j k)
      (fun q hq => hsWB_sD2_zero_off_window j k hsb q hq)
    refine (h1.const_mul (ν : ℂ)).congr (Filter.Eventually.of_forall fun p => ?_)
    push_cast
    ring
  have hLHS : ∀ p, W p c * (ν * dy j (dy k φ) p) =
      W p c * ((ν * sD2 j k (fun q => (φ q).re) p : ℝ) : ℂ) +
        Complex.I * (W p c * ((ν * sD2 j k (fun q => (φ q).im) p : ℝ) : ℂ)) := by
    intro p
    rw [dy_dy_complex hφ j k p]
    push_cast
    ring
  have hRHS : ∀ p, windowLap ν τ₀ (fun c X => D2 c j k X) p c * φ p =
      windowLap ν τ₀ (fun c X => D2 c j k X) p c * (((fun q => (φ q).re) p : ℝ) : ℂ) +
        Complex.I * (windowLap ν τ₀ (fun c X => D2 c j k X) p c *
          (((fun q => (φ q).im) p : ℝ) : ℂ)) := by
    intro p
    have hdec : φ p = (((φ p).re : ℝ) : ℂ) + (((φ p).im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im (φ p)).symm
    conv_lhs => rw [hdec]
    ring
  have hiLHS : Integrable (fun p => W p c * (ν * dy j (dy k φ) p)) :=
    (hWA.add (hWB.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun p => (hLHS p).symm)
  have hiRHS : Integrable (fun p => windowLap ν τ₀ (fun c X => D2 c j k X) p c * φ p) :=
    (hA.1.add (hB.1.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun p => (hRHS p).symm)
  refine ⟨hiLHS, hiRHS, ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hLHS),
    integral_congr_ae (Filter.Eventually.of_forall hRHS),
    integral_add hWA (hWB.const_mul Complex.I), integral_add hA.1 (hB.1.const_mul Complex.I),
    integral_const_mul, integral_const_mul, hA.2, hB.2]

/-- **`PartIII-b:C/ward/12/3/1/2/2/5`.** Transport back of the window Hessian: the components
`windowField` of the cutoff pull-back with weak second derivatives `D2 c i j` give a window
Hessian `windowLap ν τ₀ (D2 · j k)` of `W`. -/
theorem windowBackHess : WindowBackHess := by
  intro r _ hrt P _ ν w W hW χ hχ τ₀ D2 hD2 j k
  unfold IsWindowHess
  intro ψ hψ hψc hψw
  have hD2' : ∀ c : Fin 3, MemLp (D2 c j k) r volume ∧
      UnforcedLeray.B0423.HasWeakSpaceDeriv2C (d := 3) (windowField χ τ₀ W c) j k (D2 c j k) := by
    intro c
    refine ⟨?_, (hD2 c j k).2⟩
    have h := (hD2 c j k).1
    rwa [ENNReal.ofReal_toReal hrt] at h
  have hψcomp : ∀ c : Fin 3, ContDiff ℝ ∞ (fun q => ψ q c) := fun c =>
    ((EuclideanSpace.proj c : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hψ
  have hcs : ∀ c : Fin 3, HasCompactSupport (fun q => ψ q c) := fun c =>
    hψc.comp_left (g := fun v : CVec3 => v c) (by simp)
  have hsup : ∀ c : Fin 3, tsupport (fun q => ψ q c) ⊆
      Ioo (τ₀ - 1) (τ₀ + 1) ×ˢ (univ : Set Space) := fun c =>
    (tsupport_comp_subset (g := fun v : CVec3 => v c) (by simp) ψ).trans hψw
  have hcomp : ∀ c : Fin 3,
      Integrable (fun p => W p c * (ν * dy j (dy k (fun q => ψ q c)) p)) ∧
      Integrable (fun p => windowLap ν τ₀ (fun c X => D2 c j k X) p c * ψ p c) ∧
      ∫ p, W p c * (ν * dy j (dy k (fun q => ψ q c)) p) =
        ∫ p, windowLap ν τ₀ (fun c X => D2 c j k X) p c * ψ p c := fun c =>
    hsWB_component hrt hW hχ τ₀ ν j k c D2 (hD2' c) (hψcomp c) (hcs c) (hsup c)
  have e1 : (fun p => dotL (W p) (nuHessT ν j k ψ p)) =
      fun p => ∑ c : Fin 3, W p c * (ν * dy j (dy k (fun q => ψ q c)) p) :=
    funext fun p => hsWB_dotL_nuHess hψ j k p
  have e2 : (fun p => dotL (windowLap ν τ₀ (fun c X => D2 c j k X) p) (ψ p)) =
      fun p => ∑ c : Fin 3, windowLap ν τ₀ (fun c X => D2 c j k X) p c * ψ p c :=
    funext fun p => dotL_apply _ _
  rw [e1, e2]
  refine ⟨integrable_finsetSum _ fun c _ => (hcomp c).1,
    integrable_finsetSum _ fun c _ => (hcomp c).2.1, ?_⟩
  rw [integral_finsetSum _ fun c _ => (hcomp c).1, integral_finsetSum _ fun c _ => (hcomp c).2.1]
  exact Finset.sum_congr rfl fun c _ => (hcomp c).2.2

end UnforcedLeray.Short.PartIIIb.Concrete
