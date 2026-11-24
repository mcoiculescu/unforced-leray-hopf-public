import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIa.Sub.F14
import UnforcedLeray.Short.PartIIa.Tasks.F07Surjective
import UnforcedLeray.Short.PartIIa.Tasks.F13EnergyIdentity
import UnforcedLeray.Units.B0414.PhaseOrthogonal

/-!
# Part II-a, `PartII-a:F14/1`: `SmoothStressMap` from four analytic lemmas

Source of record: `the November 2 reference manuscript`, lines 1537-1544 and
1488-1500.  `smoothStressMap_of` derives `SmoothStressMap` from

* `SmoothStressEnergyD2` (the Hilbert energy identity on all of `D_2`, lines 1446-1450, 1491-1496),
* `SolenoidalBodySolution` (the solution of `(μ+L)w = 𝐏 f` is solenoidal, lines 1358-1359),
* `TensorDivPairingLe` (`Re ⟨div G, w⟩ ≤ ‖G‖ ‖∇w‖`, line 1497),
* `SmoothDivLinear` (`div` is a well-defined linear map on the smooth symmetric tensors).

The solution is unique by the energy identity; `S₀` is the inverse of `μ+L` applied to the
Leray projection of the divergence; the bounds follow by completing the square.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp

/-- **Energy identity on all of `D_2`** (lines 1446-1450 core-to-graph closure, 1491-1496):
every `w ∈ D_2` has a gradient `g ∈ Y_2³` and
`Re ⟨(μ+L)w, w⟩ = (Re μ + 1/4)‖w‖² + ν ‖∇w‖²`. -/
def SmoothStressEnergyD2 : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ w : D P ν 2, ∃ g : Fin 3 → Yq P 2, HasGrad (w : Yq P 2) g ∧
      (inner ℂ (bodyOp P ν 2 μ w) (w : Yq P 2)).re =
        (μ.re + 1 / 4) * ‖(w : Yq P 2)‖ ^ 2 + ν * ∑ j, ‖g j‖ ^ 2

/-- **Solenoidal solution of the projected body equation at `r = 2`** (lines 1358-1359, 1480-1481:
Leray commutes with heat, dilation and phase translation): for every `f ∈ Y_2` there is
`w ∈ D_2` with `w` a.e. slice-solenoidal and `(μ+L)w = 𝐏 f`. -/
def SolenoidalBodySolution : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 → ∀ ν : ℝ, 0 < ν → ∀ μ : ℂ, 0 < μ.re + 1 / 4 →
    ∀ f : Yq P 2, ∃ w : D P ν 2, (w : Yq P 2) ∈ B0414.solenoidalY P ∧
      bodyOp P ν 2 μ w = lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top f

/-- **Integration by parts against a gradient** (line 1497): for a smooth symmetric tensor `G`
and `w ∈ Y_2` with gradient `g`, `Re ⟨div G, w⟩ ≤ ‖G‖_2 ‖∇w‖_2`. -/
def TensorDivPairingLe : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (G : Fin 3 → ℝ × Space → CVec3), (∀ i, IsPhaseTest P (G i)) →
    IsSymRows G → ∀ (w : Yq P 2) (g : Fin 3 → Yq P 2), HasGrad w g →
      (inner ℂ (testElem P 2 (tensorDiv G)) w).re ≤
        ‖smoothTensor P G‖ * Real.sqrt (∑ j, ‖g j‖ ^ 2)

/-- **The divergence is a well-defined linear map on the smooth symmetric tensors**
(lines 1537-1540). -/
def SmoothDivLinear : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)], P ≤ 1 →
    ∀ M : Submodule ℂ (Y2Sym P), M ≤ symY2 P →
    (∀ X : Y2Sym P, X ∈ M ↔ ∃ G : Fin 3 → ℝ × Space → CVec3,
      (∀ i, IsPhaseTest P (G i)) ∧ IsSymRows G ∧ smoothTensor P G = X) →
    ∃ Dv : M →ₗ[ℂ] Yq P 2, ∀ (X : M) (G : Fin 3 → ℝ × Space → CVec3),
      (∀ i, IsPhaseTest P (G i)) → IsSymRows G → smoothTensor P G = (X : Y2Sym P) →
        Dv X = testElem P 2 (tensorDiv G)

/-- **Smooth core of `D_2`** (source lines 1424-1445): every `w ∈ D_2` is the `Y_2`-limit of phase
tests `G_n` together with their drift and diffusion (`𝒯₀ G_n → 𝒯₀ w`, `νΔ G_n → νΔ w` in `Y_2`),
i.e. the smooth periodic Schwartz class (radial cutoffs of truncated resolvent integrals) is a
core of the maximal graph. -/
def D2CoreDense : Prop :=
  ∀ (P : ℝ) [Fact (0 < P)] (ν : ℝ), 0 < ν → ∀ w : D P ν 2,
    ∃ G : ℕ → ℝ × Space → CVec3, (∀ n, IsPhaseTest P (G n)) ∧
      Tendsto (fun n => testElem P 2 (G n)) atTop (𝓝 (w : Yq P 2)) ∧
      Tendsto (fun n => testElem P 2 (B0005.T0op (G n))) atTop (𝓝 (T0D w)) ∧
      Tendsto (fun n => testElem P 2 (nuLapT ν (G n))) atTop (𝓝 (nuLapD w))

theorem smoothStress_bounds (hE : SmoothStressEnergyD2) (hI : TensorDivPairingLe)
    {P : ℝ} [Fact (0 < P)] (hP : P ≤ 1) {ν : ℝ} (hν : 0 < ν) {μ : ℂ} (hμ : 0 < μ.re + 1 / 4)
    (w : D P ν 2) (hws : (w : Yq P 2) ∈ B0414.solenoidalY P)
    (G : Fin 3 → ℝ × Space → CVec3) (hG : ∀ i, IsPhaseTest P (G i)) (hs : IsSymRows G)
    (g : Fin 3 → Yq P 2) (hg : HasGrad (w : Yq P 2) g)
    (hsol : bodyOp P ν 2 μ w =
      lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G))) :
    Real.sqrt (∑ j, ‖g j‖ ^ 2) ≤ ν⁻¹ * ‖smoothTensor P G‖ ∧
      ‖(w : Yq P 2)‖ ≤ ‖smoothTensor P G‖ / (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) := by
  obtain ⟨g', hg', hid⟩ := hE P hP ν hν μ hμ w
  have hgg : g' = g := funext fun j => hasPhaseOp_unique (hg' j) (hg j)
  subst hgg
  set s := Real.sqrt (∑ j, ‖g' j‖ ^ 2) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ∑ j, ‖g' j‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  set a := μ.re + 1 / 4 with hadef
  set x := ‖(w : Yq P 2)‖ with hxdef
  set T := ‖smoothTensor P G‖ with hTdef
  have hT0 : 0 ≤ T := norm_nonneg _
  have hx0 : 0 ≤ x := norm_nonneg _
  have hinner : (inner ℂ (bodyOp P ν 2 μ w) (w : Yq P 2)).re ≤ T * s := by
    rw [hsol, B0414.inner_lerayY_two_left_eq_right,
      (B0414.lerayY_two_eq_self_iff _).2 hws]
    exact hI P G hG hs _ g' hg
  have hA : a * x ^ 2 + ν * s ^ 2 ≤ T * s := by
    rw [hs2]; linarith
  have hB : s ≤ ν⁻¹ * T := by
    rw [inv_mul_eq_div, le_div_iff₀ hν]
    rcases hs0.eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using hT0
    · have : ν * s * s ≤ T * s := by nlinarith [mul_nonneg hμ.le (sq_nonneg x)]
      nlinarith
  refine ⟨hB, ?_⟩
  have hr : 0 < Real.sqrt (a * ν) := Real.sqrt_pos.2 (mul_pos hμ hν)
  have hr2 : Real.sqrt (a * ν) ^ 2 = a * ν := Real.sq_sqrt (mul_pos hμ hν).le
  rw [le_div_iff₀ (by positivity)]
  by_contra hcon
  rw [not_le] at hcon
  have h1 : T ^ 2 < (x * (2 * Real.sqrt (a * ν))) ^ 2 := by
    nlinarith
  have h2 : (x * (2 * Real.sqrt (a * ν))) ^ 2 = 4 * ν * (a * x ^ 2) := by
    rw [mul_pow, mul_pow, hr2]; ring
  have h3 : a * x ^ 2 ≤ T * s - ν * s ^ 2 := by linarith
  have h4 : 4 * ν * (T * s - ν * s ^ 2) ≤ T ^ 2 := by nlinarith [sq_nonneg (T - 2 * ν * s)]
  nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 4 * ν)]

theorem hasGrad_unique {P : ℝ} [Fact (0 < P)] {w : Yq P 2} {g g' : Fin 3 → Yq P 2}
    (h : HasGrad w g) (h' : HasGrad w g') : g = g' :=
  funext fun j => hasPhaseOp_unique (h j) (h' j)

theorem smoothStressMap_of (hE : SmoothStressEnergyD2) (hS : SolenoidalBodySolution)
    (hI : TensorDivPairingLe) (hL : SmoothDivLinear) : SmoothStressMap := by
  intro P _ hP ν hν μ hμ M hMS hmem
  obtain ⟨Dv, hDv⟩ := hL P hP M hMS hmem
  have hμ2 : 0 < μ.re + gammaR 2 := by
    have : gammaR 2 = 1 / 4 := by
      simp only [gammaR, ENNReal.toReal_ofNat]; norm_num
    rw [this]; exact hμ
  have hsurj : Function.Surjective (bodyOp P ν 2 μ) :=
    commonBodySurjective 2 ENNReal.one_lt_two (by norm_num) P hP ν hν μ hμ2
  have hinj : Function.Injective (bodyOp P ν 2 μ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    obtain ⟨g, -, hg⟩ := hE P hP ν hν μ hμ w
    rw [hw] at hg
    simp only [inner_zero_left, Complex.zero_re] at hg
    have h1 : 0 ≤ ν * ∑ j, ‖g j‖ ^ 2 :=
      mul_nonneg hν.le (Finset.sum_nonneg fun _ _ => by positivity)
    have h2 : (μ.re + 1 / 4) * ‖(w : Yq P 2)‖ ^ 2 = 0 := by
      have := mul_nonneg hμ.le (sq_nonneg ‖(w : Yq P 2)‖)
      linarith
    have h3 : ‖(w : Yq P 2)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h hμ.ne'
      · exact h
    have h4 : (w : Yq P 2) = 0 := norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 h3)
    exact Subtype.ext h4
  let e : D P ν 2 ≃ₗ[ℂ] Yq P 2 := LinearEquiv.ofBijective (bodyOp P ν 2 μ) ⟨hinj, hsurj⟩
  have he : ∀ w, e w = bodyOp P ν 2 μ w := fun w => rfl
  have hex : ∀ w : D P ν 2, ∃ g : Fin 3 → Yq P 2, HasGrad (w : Yq P 2) g := fun w => by
    obtain ⟨g, hg, -⟩ := hE P hP ν hν μ hμ w
    exact ⟨g, hg⟩
  let Grad : D P ν 2 →ₗ[ℂ] PiLp 2 (fun _ : Fin 3 => Yq P 2) :=
    { toFun := fun w => WithLp.toLp 2 (Classical.choose (hex w))
      map_add' := fun w1 w2 => by
        have h1 := Classical.choose_spec (hex w1)
        have h2 := Classical.choose_spec (hex w2)
        have h3 := Classical.choose_spec (hex (w1 + w2))
        have h4 : HasGrad ((w1 + w2 : D P ν 2) : Yq P 2)
            (Classical.choose (hex w1) + Classical.choose (hex w2)) :=
          fun j => (h1 j).add (h2 j)
        have := hasGrad_unique h3 h4
        ext1 j; exact congrFun this j
      map_smul' := fun c w => by
        have h1 := Classical.choose_spec (hex w)
        have h3 := Classical.choose_spec (hex (c • w))
        have h4 : HasGrad ((c • w : D P ν 2) : Yq P 2) (c • Classical.choose (hex w)) :=
          fun j => (h1 j).smul c
        have := hasGrad_unique h3 h4
        ext1 j; exact congrFun this j }
  have hGrad : ∀ w : D P ν 2, HasGrad (w : Yq P 2) (fun j => Grad w j) := fun w =>
    Classical.choose_spec (hex w)
  let Lp : Yq P 2 →ₗ[ℂ] Yq P 2 :=
    (lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).toLinearMap
  let W : M →ₗ[ℂ] D P ν 2 := e.symm.toLinearMap ∘ₗ Lp ∘ₗ Dv
  have hW : ∀ X : M, bodyOp P ν 2 μ (W X) =
      lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (Dv X) := fun X => by
    rw [← he]; exact e.apply_symm_apply _
  refine ⟨(D P ν 2).subtype ∘ₗ W, Grad ∘ₗ W, ?_, ?_⟩
  · intro X G hG hs hGX
    exact ⟨W X, rfl, by rw [hW, hDv X G hG hs hGX]⟩
  · intro X
    obtain ⟨G, hG, hs, hGX⟩ := (hmem _).1 X.2
    have hsol : bodyOp P ν 2 μ (W X) =
        lerayY P 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top (testElem P 2 (tensorDiv G)) := by
      rw [hW, hDv X G hG hs hGX]
    obtain ⟨w0, hw0s, hw0⟩ := hS P hP ν hν μ hμ (testElem P 2 (tensorDiv G))
    have hw0W : w0 = W X := hinj (hw0.trans hsol.symm)
    rw [hw0W] at hw0s
    obtain ⟨hb1, hb2⟩ := smoothStress_bounds hE hI hP hν hμ (W X) hw0s G hG hs _ (hGrad (W X)) hsol
    have hT : ‖smoothTensor P G‖ = ‖(X : Y2Sym P)‖ := by rw [hGX]
    rw [hT] at hb1 hb2
    refine ⟨hb2, hGrad (W X), ?_⟩
    have h2 : Real.sqrt (∑ j, ‖Grad (W X) j‖ ^ 2) = ‖Grad (W X)‖ := by
      rw [PiLp.norm_eq_of_L2]
    show ‖Grad (W X)‖ ≤ _
    rw [← h2]; exact hb1

end UnforcedLeray.Short.PartIIa
