import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1
import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_1_1_2.Int

/-!
# Decomposition of `wardX0Structure_of` (`PartIII-b:IIIb-D2/3/1/2`)

Source of record: `the November 2 reference manuscript` 3604-3621
(`sep:kernel`, `sep:resolvent`), 4171-4178.

* periodicity of `oldPhys` (`cartLift` through `chartOf`) gives the `2c/R`-periodicity of
  `wardX0` (proved here from `OldPhysPeriodic`);
* `SepWDivFree`: the separated realization is divergence free off the source disk, because
  `K_t = δ G_t + ∂_i∂_j ∫_t^∞ G` is the Leray kernel (`∑_i ∂_i K_{ij} = 0`; 3600-3610);
* `WardX0Axi`: rotation equivariance of `heatLerayK` and of the axisymmetric tensor `cartLift`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- `cartLift R c g` is `2c/R`-periodic in the phase (`chartOf` shifts the cell by one period). -/
def OldPhysPeriodic : Prop :=
  ∀ (R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (z : Space),
    oldPhys R c g (τ + 2 * c / R) z = oldPhys R c g τ z

/-- Leray kernel identity at the level of `sepW` (3600-3610): the divergence of `W_μ(·,τ)` vanishes
off the source disk. -/
def SepWDivFree : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (rOut P : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ),
    0 < ν → -(1 / 4) < μ.re → 0 ≤ rOut → 0 < P → IIIa.IsSepSource P rOut T → SepMoment P T →
    ∀ (τ : ℝ) (y : Space), rOut < ϱ y →
      ∑ j : Fin 3, fderiv ℝ (fun y' => IIIa.sepW ν μ T y' τ j) y (coordinateVector j) = 0

/-- Rotation equivariance (4171-4178): `X₀` is the frame lift of its trace on `φ = 0`, off the
axis.  The Bochner integrals `sepW` are rotation invariant only when the integrand is integrable
(a matrix mixing components does not commute with a componentwise junk value `0`), so the
integrability of the `sepW` integrands of `oldPhys R c g` at the trace point `meridPt y`
(for `μ` and `μ + 1`) is a hypothesis; it holds for the actual old source (`SepIntegrableOfSource`
and `SepIntegrableCongrAE` through `OldSourceReg`). -/
def WardX0Axi : Prop :=
  ∀ (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ) (y : Space), y ∉ axis →
    SepIntegrableAt ν (μ : ℂ) (oldPhys R c g) (meridPt y) τ →
    SepIntegrableAt ν ((μ : ℂ) + 1) (oldPhys R c g) (meridPt y) τ →
    wardX0 ν μ R c g τ y =
      frameL y !₂[wardX0 ν μ R c g τ (meridPt y) 0, wardX0 ν μ R c g τ (meridPt y) 2]

theorem wardX0_periodic (hP : OldPhysPeriodic) (ν μ R c : ℝ) (g : Chart → Ten3) (τ : ℝ)
    (y : Space) :
    wardX0 ν μ R c g (τ + 2 * c / R) y = wardX0 ν μ R c g τ y := by
  have h2 : ∀ (l : ℝ) (z : Space), oldPhys R c g (τ + 2 * c / R + 2 * Real.log l) z =
      oldPhys R c g (τ + 2 * Real.log l) z := by
    intro l z
    have : τ + 2 * c / R + 2 * Real.log l = (τ + 2 * Real.log l) + 2 * c / R := by ring
    rw [this, hP]
  unfold wardX0
  simp only [IIIa.sepW, h2]

theorem fderiv_apply_coord (f : Space → Space) (y v : Space) (j : Fin 3)
    (hf : DifferentiableAt ℝ f y) :
    fderiv ℝ f y v j = fderiv ℝ (fun y' => f y' j) y v := by
  have h := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp y hf.hasFDerivAt
  have := h.fderiv
  rw [show (fun y' => f y' j) = ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) ∘ f) from rfl, this]
  rfl

theorem varrho_meridPt (y : Space) : ϱ (meridPt y) = ϱ y := by
  have h : ϱ y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  unfold ϱ meridPt
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← h]
  simp [ϱ]

theorem wardX0Structure_of (c mZ ρb γ ν ε μ : ℝ) {χo : ℝ → ℝ} (hχo : IsOutwardCutoff χo)
    (hreg : OldSourceReg c mZ ρb γ ν ε hχo) (hW : SepWSmoothOn) (hD : SepWDivFree)
    (hP : OldPhysPeriodic) (hA : WardX0Axi) (hSrc : SepIntegrableOfSource)
    (hCong : SepIntegrableCongrAE) :
    WardX0Structure c mZ ρb γ ν ε μ hχo := by
  intro hc hρ hm hν hε hμ T g₁ g₂ h1 h2
  obtain ⟨P, T', hPp, hS, hM, hEq, hae⟩ := hreg hc hρ hm hν hε T g₁ g₂ h1 h2
  have hr0 : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
  refine ⟨?_, fun τ y => wardX0_periodic hP ν μ ε⁻¹ c _ τ y, fun τ y hy' hy => hA ν μ ε⁻¹ c _ τ y hy
    (hCong ν _ _ T' hae _ τ
      (hSrc ν _ _ P T' hν (by simpa using hμ) hr0 hPp hS hM τ _
        (by rw [varrho_meridPt]; exact hy')))
    (hCong ν _ _ T' hae _ τ
      (hSrc ν _ _ P T' hν (by simp; linarith) hr0 hPp hS hM τ _
        (by rw [varrho_meridPt]; exact hy')))⟩
  intro τ y hy
  have hr : 0 ≤ ε⁻¹ * Real.sqrt (5 * ν / 6) := by positivity
  have hopen : IsOpen {y : Space | ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y} :=
    isOpen_lt continuous_const (by unfold ϱ; fun_prop)
  have hy' : y ∈ {y : Space | ε⁻¹ * Real.sqrt (5 * ν / 6) < ϱ y} := hy
  have hA' := hW ν (μ : ℂ) _ P T' hν (by simpa using hμ) hr hPp hS hM τ
  have hB' := hW ν ((μ : ℂ) + 1) _ P T' hν (by simp; linarith) hr hPp hS hM τ
  have dA : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T' y' τ i) y := fun i =>
    ((hA' i).contDiffAt (hopen.mem_nhds hy')).differentiableAt (by norm_num)
  have dB : ∀ i, DifferentiableAt ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ i) y := fun i =>
    ((hB' i).contDiffAt (hopen.mem_nhds hy')).differentiableAt (by norm_num)
  have hfun : wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ = fun y' => (WithLp.toLp 2 fun i =>
      (IIIa.sepW ν (μ : ℂ) T' y' τ i - IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ i).re : Space) := by
    funext y'
    unfold wardX0
    simp [hEq]
  have hdiff : DifferentiableAt ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y := by
    rw [hfun]
    refine (differentiableAt_piLp 2).2 fun i => ?_
    exact Complex.reCLM.differentiableAt.comp y ((dA i).sub (dB i))
  unfold physPd
  have hc : ∀ j : Fin 3, fderiv ℝ (wardX0 ν μ ε⁻¹ c (g₁ + g₂) τ) y (coordinateVector j) j =
      (fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T' y' τ j) y (coordinateVector j) -
        fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ j) y (coordinateVector j)).re := by
    intro j
    rw [fderiv_apply_coord _ _ _ _ hdiff, hfun]
    simp only
    have hh : HasFDerivAt (fun y' => (IIIa.sepW ν (μ : ℂ) T' y' τ j -
        IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ j).re)
        (Complex.reCLM.comp ((fderiv ℝ (fun y' => IIIa.sepW ν (μ : ℂ) T' y' τ j) y) -
          (fderiv ℝ (fun y' => IIIa.sepW ν ((μ : ℂ) + 1) T' y' τ j) y))) y :=
      Complex.reCLM.hasFDerivAt.comp y (((dA j).hasFDerivAt).sub ((dB j).hasFDerivAt))
    rw [hh.fderiv]
    simp
  simp only [hc]
  have e1 := hD ν (μ : ℂ) _ P T' hν (by simpa using hμ) hr hPp hS hM τ y hy
  have e2 := hD ν ((μ : ℂ) + 1) _ P T' hν (by simp; linarith) hr hPp hS hM τ y hy
  rw [← Complex.re_sum, Finset.sum_sub_distrib, e1, e2]
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
