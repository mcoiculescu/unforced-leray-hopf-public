import UnforcedLeray.Short.PartIIIb.StatementsB
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2

/-!
# Young response and signed flat return: status of target PartIII-b:IIIb-D3

Status: BLOCKED. Each target is a `Prop` quantifying over an arbitrary `YoungPkg` or `FlatPkg`
(StatementsB.lean). Their fields (`Uev`, `q`, `ell`, `ellMu`, `aNu`, `moment`) are not yet the
concrete objects of Parts I-III-a, so the targets are not provable as stated for arbitrary
packages. No target is proved in this file.

What this file checks: for the degenerate instances below, the stated Props are false, so no
argument can prove them without the concrete objects or without amended hypotheses.

* `not_youngFrozenPair` : `YoungFrozenPair` fails for `Uev = id`, `q = ell = 0`, `ν ≡ 0`.
* `not_flatClassAmplitude` : `FlatClassAmplitude` fails for `aNu ≡ 1`, at `B = 0`.
* `not_flatAllMoments` : `FlatAllMoments` fails for `moment ≡ 1`, at `B = 0`.
* `not_flatScalarEstimate` : `FlatScalarEstimate` fails for `ellMu ≡ 1`, at `B = 0`, when `Re λ > 0`.
* `not_flatCoefficient` : `FlatCoefficient` fails for `ellMu ≡ 1` with `ε3 ≡ 0`.

Not examined here: `YoungDuhamel` (every instance with `ν ≡ 0` has both sides zero, since
`α/ν = 0`), and `FlatLimit` (a `ReturnSeq` Prop from StatementsA.lean).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory

namespace UnforcedLeray.Short.PartIIIb

namespace DeferredYoungFlat

/-- The essential supremum of the zero function is zero. -/
lemma essSup_zero_fun (μ : Measure ℝ) : essSup (fun _ : ℝ => (0 : ENNReal)) μ = 0 :=
  le_antisymm (essSup_le_of_ae_le 0 (ae_of_all μ fun _ => le_refl _)) zero_le

/-- The class norm of the zero matrix function is zero. -/
lemma bNorm_zero (a : ℝ) : bNorm a (fun _ => 0) = 0 := by
  simp [bNorm, matNorm, essSup_zero_fun]

/-- The zero matrix function lies in the class `𝓑_a` for every `a` and `ν`. -/
lemma isBclass_zero (a ν : ℝ) : IsBclass a ν (fun _ => 0) := by
  refine ⟨fun _ _ => measurable_const, fun _ => by simp, fun _ => by simp, fun _ _ => rfl, ?_⟩
  simp [matNorm, essSup_zero_fun]

/-- The limiting amplitude vanishes on the zero matrix function. -/
lemma aZero_zero (lam ell μ : ℂ) : aZero lam ell μ (fun _ => 0) = 0 := by
  simp [aZero, Bd, Be]

/-- The flat package with every functional equal to `1`. -/
def oneFlat : FlatPkg := ⟨fun _ => 1, fun _ => 1, fun _ _ => 1⟩

theorem not_flatClassAmplitude (ν : ℕ → ℝ) (lam ell μ : ℂ) (a : ℝ) :
    ¬ FlatClassAmplitude (fun _ => oneFlat) ν lam ell μ a := by
  intro h
  obtain ⟨C, N, hN⟩ := h
  have := hN N le_rfl (fun _ => 0) (isBclass_zero a (ν N))
  norm_num [oneFlat, aZero_zero, bNorm_zero] at this

theorem not_flatAllMoments (ν : ℕ → ℝ) (lam κ : ℂ) (μ a : ℝ) :
    ¬ FlatAllMoments (fun _ => oneFlat) ν lam κ μ a := by
  intro h
  obtain ⟨C, N, hN⟩ := h
  have := hN N le_rfl 0 (by norm_num) (fun _ => 0) (isBclass_zero a (ν N))
  norm_num [oneFlat, bNorm_zero] at this

theorem not_flatScalarEstimate (ν ε3 : ℕ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ) (μ a : ℝ)
    (hlam : 0 < lam.re) :
    ¬ FlatScalarEstimate (fun _ => oneFlat) ν ε3 lam κ ell J μ a := by
  intro h
  obtain ⟨ωcan, C, k, N, _, hN⟩ := h (lam.re / 2) (by linarith) (by linarith)
  have := hN N le_rfl (fun _ => 0) (isBclass_zero a (ν N))
  norm_num [oneFlat, aZero_zero, bNorm_zero] at this

theorem not_flatCoefficient (ν : ℕ → ℝ) (lam κ ell : ℂ) (J : ℂ → ℂ)
    (chi dchi : ℝ → ℝ) (μ : ℝ) :
    ¬ FlatCoefficient (fun _ => oneFlat) ν (fun _ => 0) lam κ ell J chi dchi μ := by
  intro h
  obtain ⟨ωcan, C, k, b, γ', N, _, _, _, _, hN⟩ := h
  have := hN N le_rfl
  norm_num [oneFlat, unitResp] at this

/-- A scalar multiple of a `smulRight` built from the zero functional vanishes. -/
lemma smul_smulRight_zero {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (c : ℂ) (q : X) :
    c • ((0 : X →L[ℂ] ℂ).smulRight q) = 0 := by
  ext x
  simp

/-- The Young package with `X = ℂ`, `Uev = id`, `q = ell = 0`. -/
def idYoung : YoungPkg where
  X := ℂ
  Uev := fun _ _ => ContinuousLinearMap.id ℂ ℂ
  q := fun _ _ => 0
  ell := fun _ _ => 0

theorem not_youngFrozenPair (lam κ : ℂ) (Sg α : ℝ) :
    ¬ YoungFrozenPair (fun _ => idYoung) (fun _ => 0) lam κ Sg α := by
  intro h
  obtain ⟨C, N, hN⟩ := h
  have hS : (∑ j : Bool, Fpm j lam κ 0 0 0 • ((idYoung.ell j 0).smulRight (idYoung.q j 0))) = 0 :=
    Finset.sum_eq_zero (fun j _ => smul_smulRight_zero _ _)
  have hid : ‖ContinuousLinearMap.id ℂ ℂ‖ = 1 := ContinuousLinearMap.norm_id
  have := hN N le_rfl 0 (by simp)
  dsimp only at this
  rw [div_zero, hS, sub_zero] at this
  change ‖ContinuousLinearMap.id ℂ ℂ‖ ≤ C * 0 * _ at this
  rw [hid] at this
  norm_num at this

end DeferredYoungFlat

end UnforcedLeray.Short.PartIIIb

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem flatLimit_concrete (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (hflat : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      NearInst.Kflat.IsFlatDuhamelColumn (D.flat n)
        (cOf_pos (retNu_pos D.Pl D.σ₀ n)) (D.train n) (D.mu n z) D.K.as D.K.χf)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) :
    FlatLimit (concreteReturnSeq D G) D.Pl.eigenvalue D.Pl.kappa D.Pl.strainCoupling
      (planarJ D.Pl) D.σ₀ D.K.as :=
  flatLimit_of_parts D G (flatLimitKflatPart_of D hst hflat G) (flatLimitCoefPart_of D hst G)

end UnforcedLeray.Short.PartIIIb.Concrete
