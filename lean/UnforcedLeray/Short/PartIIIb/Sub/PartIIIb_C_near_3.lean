import UnforcedLeray.Short.PartIIIb.NearInst.Targets

/-!
# Sub-lemmas for `PartIII-b:C/near/3` (`NearFlatBoundC`, source 3560-3581, 3881-3887)

`D₀ = I + M₀S₀` is a unit with `‖G⁻¹D₀⁻¹G‖ ≤ Cν^{-k}` as soon as

* `D₀` is injective (`NearD0Inj`; from `PolyCausal` uniqueness: `D₀F = 0` makes `S₀F` a solution of
  the actual equation with zero force, so `S₀F = 0`, hence `F = 0`, source 3560-3581);
* every `F ∈ Z` has a preimage `F' = (F₁ - M₀b, F₂)` with `‖G⁻¹F'‖ ≤ Cν^{-k}‖G⁻¹F‖`
  (`NearD0Surj`; from `PolyStressCorollary` and `FreeCausalExistsUnique`, source 3560-3581), the
  hypothesis of `PolyStressCorollary` being the function-level train multiplier bound
  (`FlatMultFunBound`, from `FlatTrainMultBound` since `|v⊗u+u⊗v| ≤ 2|v||u|`).

The right inverse is linear by injectivity, so no Banach bijection theorem is needed
(`nearFlatBoundC_of_leaves`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- **Function-level train multiplier bound** (feeds the hypothesis of `IIIa.PolyStressCorollary`,
source 3566-3567): for `m_Z > 3/2` there are `C, k, ν₀` with
`‖M₀u‖_{𝒵₁} ≤ C ν^{-k}‖u‖_𝓗` for measurable `u`, every BUC train at `ν ≤ ν₀`. -/
def FlatMultFunBound : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧ ∀ ν ∈ Ioc 0 ν₀,
    ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
      UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ u : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => u p i) →
        UnforcedLeray.Short.IIIa.z1Norm2 (ν ^ (-2 : ℝ)) mZ (UnforcedLeray.Short.IIIa.flatMult tr u) ≤
          ENNReal.ofReal (C * ν ^ (-(k : ℝ))) *
            UnforcedLeray.Short.IIIa.hCalNorm (ν ^ (-2 : ℝ)) u

/-- **Injectivity of `D₀`** (source 3560-3581, from the uniqueness clause of `PolyCausal`). -/
def NearD0Inj : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∃ ν₀ : ℝ, 0 < ν₀ ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ o : NearOps c mZ ρb,
        IsFlatMult o.M0 tr → IsFreeStress o.S0 ν μ → Function.Injective o.D0

/-- **Gained right inverse of `D₀`, elementwise** (source 3560-3581, `D₀⁻¹F := (F₁ - M₀b, F₂)`,
`b = S_lin(F₁+F₂)`; `S₀(D₀⁻¹F) = b` by uniqueness in `FreeCausalExistsUnique` and the pin
`IsFreeStress`): every `F ∈ Z` has `F'` with `D₀F' = F` and `‖G⁻¹F'‖ ≤ Cν^{-k}‖G⁻¹F‖`. -/
def NearD0Surj : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ Kset : Set ℝ, IsCompact Kset →
    Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 3 / 2 < mZ → ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 ≤ C ∧ 0 < ν₀ ∧
      ∀ ν : ℝ, ∀ hν : 0 < ν, ν ≤ ν₀ → ∀ c : ℝ, c = (ν ^ 2)⁻¹ →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset, ∀ o : NearOps c mZ ρb,
        IsFlatMult o.M0 tr → IsFreeStress o.S0 ν μ →
        ∀ F : Zsp c mZ ρb, ∃ F' : Zsp c mZ ρb, o.D0 F' = F ∧
          ‖(gainEquiv c mZ ρb P.eigenvalue.re hν).symm F'‖ ≤
            C * ν⁻¹ ^ k * ‖(gainEquiv c mZ ρb P.eigenvalue.re hν).symm F‖

theorem nearFlatBoundC_of_leaves (h1 : NearD0Inj) (h2 : NearD0Surj) : NearFlatBoundC := by
  intro P hP K hK hKs mZ hmZ dm dp hdm
  obtain ⟨ν1, hν1, e1⟩ := h1 P hP K hK hKs mZ hmZ
  obtain ⟨C, k, ν2, hC, hν2, e2⟩ := h2 P hP K hK hKs mZ hmZ
  refine ⟨C, k, min ν1 ν2, lt_min hν1 hν2, ?_⟩
  intro p d hreg hp ρb hρb hρb1 μ hμ o hM hS
  have hν : 0 < p.ν := p.ν_pos
  have hp1 : p.ν ≤ ν1 := hp.trans (min_le_left _ _)
  have hp2 : p.ν ≤ ν2 := hp.trans (min_le_right _ _)
  have inj : Function.Injective o.D0 :=
    e1 p.ν hν hp1 p.c hreg.c_eq p.trainData hreg.train_buc ρb hρb hρb1 μ hμ o hM hS
  have sur := e2 p.ν hν hp2 p.c hreg.c_eq p.trainData hreg.train_buc ρb hρb hρb1 μ hμ o hM hS
  set G := gainEquiv p.c mZ ρb P.eigenvalue.re hν with hG
  choose Rf hRf using sur
  have hadd : ∀ x y, Rf (x + y) = Rf x + Rf y := fun x y => by
    apply inj
    rw [map_add, (hRf _).1, (hRf x).1, (hRf y).1]
  have hsmul : ∀ (r : ℝ) x, Rf (r • x) = r • Rf x := fun r x => by
    apply inj
    rw [map_smul, (hRf _).1, (hRf x).1]
  let T : Zsp p.c mZ ρb →ₗ[ℝ] Zsp p.c mZ ρb :=
    { toFun := Rf, map_add' := hadd, map_smul' := hsmul }
  set B : ℝ := C * p.ν⁻¹ ^ k with hB
  have hB0 : 0 ≤ B := mul_nonneg hC (pow_nonneg (inv_nonneg.2 hν.le) _)
  let Rc : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb :=
    LinearMap.mkContinuous T (‖(G : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)‖ * B *
      ‖(G.symm : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)‖) (by
      intro x
      have h1 : ‖Rf x‖ ≤ ‖(G : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)‖ * ‖G.symm (Rf x)‖ := by
        have := (G : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb).le_opNorm (G.symm (Rf x))
        simpa using this
      have h2 : ‖G.symm x‖ ≤ ‖(G.symm : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)‖ * ‖x‖ :=
        (G.symm : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb).le_opNorm x
      have h3 := (hRf x).2
      calc ‖T x‖ = ‖Rf x‖ := rfl
        _ ≤ ‖(G : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)‖ * (B * ‖G.symm x‖) :=
            h1.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))
        _ ≤ ‖(G : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)‖ * (B *
              (‖(G.symm : Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)‖ * ‖x‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB0) (norm_nonneg _)
        _ = _ := by ring)
  have hRc : ∀ x, Rc x = Rf x := fun x => rfl
  have h1' : o.D0 * Rc = 1 := by
    ext x; simp only [ContinuousLinearMap.mul_apply, hRc, (hRf _).1]; rfl
  have h2' : Rc * o.D0 = 1 := by
    ext x
    simp only [ContinuousLinearMap.mul_apply]
    apply inj
    rw [hRc, (hRf _).1]; rfl
  let u : (Zsp p.c mZ ρb →L[ℝ] Zsp p.c mZ ρb)ˣ := ⟨o.D0, Rc, h1', h2'⟩
  have hu : Ring.inverse o.D0 = Rc := Ring.inverse_unit u
  refine ⟨⟨u, rfl⟩, ?_⟩
  rw [hu]
  refine ContinuousLinearMap.opNorm_le_bound _ hB0 fun x => ?_
  have := (hRf (G x)).2
  simpa [conjG, hRc] using this

end UnforcedLeray.Short.PartIIIb.NearInst
